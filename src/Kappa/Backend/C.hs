{-# LANGUAGE OverloadedRecordDot #-}

-- | Native backend: lower elaborated KCore ('Kappa.Core.Term') to C that
-- links against the @kappart@ runtime (see @runtime/kappart.h@ and
-- docs/NATIVE_BACKEND.md).
--
-- The lowering is a structural recursion over 'Term' that mirrors
-- 'Kappa.Eval.eval' / 'Kappa.Interp' but emits C rather than stepping an
-- interpreter, so the two stay semantically aligned for the supported
-- subset.  Any 'Term' or do-kernel item the backend does not support is a
-- compile-time 'E_BACKEND_UNSUPPORTED' error naming the construct (and the
-- definition it appears in) — never a silent fallback to interpreter
-- behaviour.
--
-- Representation contract with the runtime:
--
--   * all functions are curried arity-1 closures; application is a chain
--     of @kapp@ (explicit) / @kappi@ (implicit) calls;
--   * implicit arguments are erased for primitives and constructors, and
--     type-level implicit arguments to ordinary functions are passed as an
--     unused @kunit()@ placeholder (types are computationally erased);
--   * the de Bruijn environment is the runtime @KEnv@ linked list, head =
--     index 0; entering a binder conses onto it.
module Kappa.Backend.C
  ( generateC
  , BackendError (..)
  , backendUnsupported
  , backendDiagnostics
  , basePrims
    -- * Shared primitive registry (consumed by "Kappa.Backend.LLVM")
  , PrimEntry (..)
  , primEntries
  , primDirect
  , primRegistryDiagnostics
  , suspenderGlobals
  , suspenderGlobalsWith
  , blockSuspends
  , cpsEligible
    -- * §34.3.3 multi-shot backend legality (shared with "Kappa.Backend.LLVM")
  , multishotLegality
    -- * Shared Q0 spine erasure (consumed by "Kappa.Backend.LLVM")
  , eraseQ0ArgsP
  , resultIsProofP
  ) where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Char (isAscii, isAsciiLower, isAsciiUpper, isDigit, ord)
import Data.List (sort)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Control.Monad (foldM, forM, forM_, unless, void, when)
import Control.Monad.State.Strict
import Kappa.Backend.NativeFfi
  ( ResolvedNativeSymbol (..)
  , externPrototype
  , rnsCollectCtors
  , wrapperCName
  , wrapperDefinition
  )
import Kappa.Build.Types (FfiClass (..))
import qualified Kappa.Backend.Repr as Repr
import qualified Kappa.Builtins as Builtins
import Kappa.Check (CheckState (..), CtorInfo (..))
import Kappa.Core
import Kappa.CoreOps (dropStaticGlobalPrefixArgs, dropStaticPrefixLams, patBindersC, substTopTerm)
import Kappa.Diagnostic
import Kappa.Eval (EvalCtx (..), GlobalDef (..), Globals (..), eval, force, quote)
import Kappa.Ownership
  ( BinderId (..)
  , BinderOwn (..)
  , OwnInfo (..)
  , UseKind (..)
  , UseSite (..)
  )
import qualified Kappa.PathScheme as P
import Kappa.Source (ModuleName (..), Span, noSpan)
import Numeric (showHex, showOct)

-- | One reason the native backend cannot compile a definition: the global
-- it occurred in, the unsupported construct, and a human detail.
data BackendError = BackendError
  { beGlobal :: !GName
  , beSpan :: !Span
  , beCode :: !Text
  , beFamily :: !(Maybe Text)
  , beConstruct :: !Text
  , beDetail :: !Text
  }
  deriving stock (Eq, Show)

backendUnsupported :: GName -> Span -> Text -> Text -> BackendError
backendUnsupported g sp construct detail =
  BackendError g sp "E_BACKEND_UNSUPPORTED" (Just "kappa-hs.backend.unsupported") construct detail

backendFeatureMissing :: GName -> Span -> Text -> Text -> BackendError
backendFeatureMissing g sp construct detail =
  BackendError g sp "E_FEATURE_BACKEND_CAPABILITY_MISSING" (Just "kappa.feature.gated") construct detail

-- | Render backend errors as structured diagnostics (§3.1): one
-- @E_BACKEND_UNSUPPORTED@ per unsupported construct, citing the offending
-- definition's declaration site.
backendDiagnostics :: [BackendError] -> Diagnostics
backendDiagnostics = map one
  where
    one be =
      diag SevError StageElaborate (beCode be) (beFamily be)
        (beSpan be)
        ( "the native backend cannot compile definition '"
            <> gnameText (beGlobal be)
            <> "': " <> beDetail be
            <> " (" <> beConstruct be <> ")"
        )

-- ── Code-generation monad ────────────────────────────────────────────

data GenState = GenState
  { gsFresh :: !Int
  , gsStmts :: ![Text] -- ^ current function body, reversed
  , gsEnv :: !Text -- ^ C expression for the current KEnv*
  , gsParamLvals :: ![Text] -- ^ R2.3: in a FLAT (capture-free) first-order worker, the C lvalue for each de Bruijn index — the params (index @i@ = source param @n-1-i@) plus any @let@/@match@-bound locals prepended at index 0 (R2.3-rest); a 'CVar' reads the C local directly instead of walking @kvar(kw_env,i)@. Empty outside a flat worker body (then 'CVar' uses @kvar@).
  , gsParamBinders :: ![Maybe BinderId] -- ^ Parallel to 'gsParamLvals': the ownership binder identity for each flat local when known. Needed by S2.3d branch-dead drops so codegen drops the already-bound C local for exactly the binder the ownership walk named.
  , gsParamOwns :: ![Bool] -- ^ Parallel to 'gsParamLvals': whether the flat local currently owns a reference. Incoming params are not marked owning until caller-side ownership transfer is normalized; constructor let-locals are owning when their RHS is a proven fresh allocation; pattern locals are owning only on the match cell-drop path that first @kdup@s the field; projection/call-result locals stay non-owning until result ownership is modeled.
  , gsTopFlatFrame :: !Bool -- ^ True only while compiling a top-level flat worker body. S2.3d can treat a missing branch-dead binder mapping as path/metadata drift in this frame; nested flat closures may deliberately omit outer captured binders and therefore keep missing branch-drop locals leak-biased.
  , gsTop :: ![Text] -- ^ completed top-level C functions, reversed
  , gsProtos :: ![Text] -- ^ forward declarations, reversed
  , gsEmitted :: !(Set GName) -- ^ globals already emitted or enqueued
  , gsQueue :: ![GName] -- ^ globals still to emit
  , gsErrs :: ![BackendError] -- ^ unsupported-construct findings
  , gsCur :: !GName -- ^ definition currently being compiled (for diagnostics)
  , gsGlobals :: !(Map GName GlobalDef)
  , gsEvalCtx :: !EvalCtx -- ^ R2.2: a non-runtime EvalCtx (built from the CheckState) used only to 'quote' a global's 'gdType' to a Term so the per-parameter scalar kinds can be read from its Pi telescope.
  , gsBodies :: !(Map GName Term)
  , gsSuspenders :: !(Set GName) -- ^ §3.3: globals that TRANSITIVELY reach a suspending primitive (fork/await/…); computed once from gsBodies. A do-bind whose action's spine head is in here may suspend, so its do-block is CPS-lowered.
  , gsOwnership :: !(Map GName OwnInfo) -- ^ Perceus RC side table (see "Kappa.Ownership"): per-definition binders, per-use last-use facts, and the S2.3b consume/read bit carried from @csOwnership@ beside 'gsSuspenders'. The explicit OFF baseline ignores it and disables runtime RC effects in the generated entry point; the default native path validates and emits RC operations from it.
  , gsCurOwn :: !(Maybe OwnInfo) -- ^ The 'OwnInfo' for the global currently being compiled ('gsCur'), looked up from 'gsOwnership' at body entry ('emitGlobal'/'compileFunctionGlobal') and cleared otherwise. The walk-and-lookup at a 'CVar' consults @oiUses@ and @oiUseConsumes@ here. 'Nothing' when no per-definition table is in scope (a CAF prologue, a lifted helper without its own entry) — then the lookup is skipped.
  , gsPath :: ![Int] -- ^ Perceus RC Stage S2.1: the REVERSED structural child-position path from the current global's body root to the node being compiled, threaded through 'compileTerm'/'compileApp'/'compileCtor'/'consume*' at exactly the child positions "Kappa.Ownership"'s walk records, via the SHARED constants in "Kappa.PathScheme" (so the two schemes can never diverge — risk R-path). @reverse gsPath@ is the 'UseSite'/'BinderId' key. Seeded with the leading-lambda prefix in 'compileFunctionGlobal' (the analysis walks the whole body INCLUDING the leading 'CLam's, which codegen strips off into the worker frame). Empty at a CAF/body root.
  , gsRcEnabled :: !Bool -- ^ Perceus RC maintenance gate. Default ON for native builds; @KAPPA_PERCEUS_RC=0@ is the explicit byte-identical baseline and emits @krc_set_enabled(0)@ so generated @kdup@/@kdrop@ maintenance has no runtime counting/freeing effect. S4 publish marking still emits because shared bits are synchronization metadata for Ref/Array storage. When enabled, every non-erased runtime 'CVar' must resolve in @gsCurOwn@'s @oiUses@ AND @oiUseConsumes@, and the backend emits the currently enabled dup/drop operations.
  , gsRcFindings :: ![Text] -- ^ Perceus RC validation log, populated only when 'gsRcEnabled'. One entry per ownership side-table miss (missing use path, missing consume/read bit for a resolved use, or S2.3d branch-drop binder metadata drift). Converted to a backend error at the end of generation so ON builds fail closed instead of silently suppressing RC decisions.
  , gsRcBranchVisited :: !(Set (GName, [Int])) -- ^ S2.3d branch-drop paths that codegen reached under the current ownership table. Compared with @oiBranchDropSites@ at the end of RC-on generation so a stale path key cannot silently leak.
  , gsCtors :: !(Map GName CtorInfo)
  , gsDatas :: !(Set GName)
  , gsTraits :: !(Set GName)
  , gsDeclSites :: !(Map GName Span)
  , gsPrims :: !(Set Text) -- ^ primitive names the linked runtime implements
  , gsPrimUsed :: !(Set Text) -- ^ §34.5.3: builtin primitives actually referenced; 'assemble' emits an @extern@ decl for each direct entry point (@kp_*@/@kpf_*@) so the optimized output calls it DIRECTLY — never a by-name string dispatch.
  , gsHostSyms :: !(Map GName ResolvedNativeSymbol) -- ^ §27.1.1/§36.28: each provided @host.native.*@ member (an abstract global) ↦ its resolved native symbol (C symbol + ABI signature), built per build from the manifest's native bindings (never a hardcoded catalog). A reference to such a member lowers to a DIRECT typed call ('knative'), not a runtime primitive.
  , gsHostUsed :: !(Set GName) -- ^ §27.1.1: host members actually referenced; 'assemble' emits one extern prototype + marshalling wrapper per used member.
  , gsBounceMemo :: !(Map (GName, Int) (Maybe Bool)) -- ^ Native lowering cache: whether a boxed worker of this arity may return K_BOUNCE. 'Nothing' marks an in-progress analysis; recursive cycles conservatively read as may-bounce. The analysis is pure in the stable codegen environment, so caching prevents large game targets from re-walking the same bodies at every call site.
  , gsLoops :: ![LoopCtx] -- ^ enclosing loops, innermost first (§18.2.5 labels)
  , gsDefer :: ![(Text, Text)] -- ^ §18.7 TAIL-scope defer frames (do-block + tail-if-branch), innermost first; flushed after the tail IO action via kio_finally
  , gsScopeDefers :: ![(Text, Text)] -- ^ §18.7 NESTED-scope defer frames (loop body / non-tail if branch), innermost first; flushed inline at scope exit + break/continue/return crossings
  , gsDeferLabels :: ![(Text, (Text, Text))] -- ^ §18.7 label ↦ (arr,cnt) frame of each enclosing LABELED do-scope (explicit `do`/loop), innermost first; a `defer@L` registers onto the frame of the scope labeled L (which may be outer) instead of the current scope.
  , gsI64Escape :: !Text -- ^ The C statement spliced by scalarArith on int overflow / INT64_MIN in an unboxed scalar worker: @*kovf = 1; return 0;@.
  , gsCollectCtors :: !(Set Text) -- ^ LR2: gKeys of USER constructors referenced (constructed or matched); builtins use the fixed @KCT_*@ ids so they are NOT collected. After codegen, @assemble@ assigns each a @KCT_USER_BASE+i@ id (sorted, deterministic) and emits a @KT_<mangle>@ enum.
  , gsCollectVars :: !(Set Text) -- ^ LR2: §13 variant member-identity tags referenced (injected or matched); @assemble@ emits a 0-based @KVT_<mangle>@ enum (variants are never runtime-built, so no fixed-id constraint).
  }

data FlatLocalScope = FlatLocalScope
  { flsLvals :: ![Text]
  , flsBinders :: ![Maybe BinderId]
  , flsOwns :: ![Bool]
  }

saveFlatLocalScope :: Gen FlatLocalScope
saveFlatLocalScope =
  FlatLocalScope
    <$> gets gsParamLvals
    <*> gets gsParamBinders
    <*> gets gsParamOwns

restoreFlatLocalScope :: FlatLocalScope -> Gen ()
restoreFlatLocalScope saved =
  modify' $ \g ->
    g
      { gsParamLvals = flsLvals saved
      , gsParamBinders = flsBinders saved
      , gsParamOwns = flsOwns saved
      }

-- | A loop's labelled control targets: its source label (if any), the C
-- goto label a @continue@ jumps to, the one a @break@ jumps to, and the
-- 'gsScopeDefers' depth at loop-body entry (so a @break@/@continue@ flushes
-- exactly the defer frames it unwinds, §18.7).
data LoopCtx = LoopCtx
  { lcLabel :: !(Maybe Text)
  , lcContinue :: !Text
  , lcBreak :: !Text
  , lcScopeDepth :: !Int
  }

type Gen = State GenState

freshN :: Text -> Gen Text
freshN base = do
  n <- gets gsFresh
  modify' $ \g -> g {gsFresh = n + 1}
  pure (base <> T.pack (show n))

-- | A fresh name for a generated top-level helper FUNCTION (lambda, closure,
-- do-block, thunk, defer), derived from the enclosing source global so the
-- generated C carries source intent — e.g. @kfn_main_2e_len_9@ for a lambda
-- inside @main.len@ — rather than an opaque @kfn_9@ (QW3, review note §6).
-- The global counter is kept only as a uniqueness suffix.  Temporaries
-- (@pa_@, @env_@, @scrut_@, …) keep the plain 'freshN' form.
freshFn :: Text -> Gen Text
freshFn base = do
  g <- gets gsCur
  n <- gets gsFresh
  modify' $ \st -> st {gsFresh = n + 1}
  pure (base <> mangle (gKey g) <> "_" <> T.pack (show n))

emit :: Text -> Gen ()
emit s = modify' $ \g -> g {gsStmts = s : gsStmts g}

-- ── Perceus RC Stage S2.1: structural-path threading ─────────────────
--
-- 'gsPath' is the REVERSED child-position path from the current global's body
-- root to the node being compiled (see 'GenState'). It mirrors the path
-- "Kappa.Ownership"'s @walk@ records, position-for-position, via the SHARED
-- "Kappa.PathScheme" constants — so the codegen path that LOOKS UP a side-table
-- key matches the analysis path that BUILT it (risk R-path). The whole mechanism
-- is INERT unless 'gsRcEnabled'; at S2.1 it asserts but emits nothing.

-- | Descend into a child at the given shared child position ('Kappa.PathScheme'),
-- running the action with @pos@ pushed onto 'gsPath', then restoring the path.
-- This is the single descent primitive both the path threading and the analysis
-- walk agree on. A no-op on the path when 'gsRcEnabled' is off would still be
-- correct, but we keep the push unconditional (it is a cheap list cons) so the
-- threading is exercised — and immediately validated — under the ON build.
withChild :: Int -> Gen a -> Gen a
withChild pos act = do
  saved <- gets gsPath
  modify' $ \st -> st {gsPath = pos : saved}
  r <- act
  modify' $ \st -> st {gsPath = saved}
  pure r

-- | Descend into the @j@-th argument (0-based, in 'spineOf' order) of a flat
-- application spine of @k@ total arguments, pushing the nested-CApp path the
-- analysis walk would take. 'spineOf' lists args innermost-applied first, so the
-- spine is @CApp (… (CApp hd arg0) …) arg{k-1}@: @arg j@ sits under one
-- 'appArgPos' beneath @(k-1-j)@ 'appHeadPos' steps. The reversed (deepest-first)
-- prefix pushed onto 'gsPath' is therefore @appArgPos : replicate (k-1-j)
-- appHeadPos@. This reproduces, for a spine flattened by 'spineOf', the exact key
-- the analysis built by its structural nested-'CApp' descent. Inert when the path
-- is unread (OFF baseline).
withSpineArg :: Int -> Int -> Gen a -> Gen a
withSpineArg k j act = do
  saved <- gets gsPath
  let prefix = P.appArgPos : replicate (k - 1 - j) P.appHeadPos
  modify' $ \st -> st {gsPath = prefix ++ saved}
  r <- act
  modify' $ \st -> st {gsPath = saved}
  pure r

-- | Run an action with the given current-definition 'OwnInfo' and root path in
-- scope (the body-entry seam), restoring both afterwards. @prefix@ is the
-- reversed path from the global's body root down to the term about to be
-- compiled — for a function global the leading-lambda prefix the worker frame
-- stripped off, for a CAF the empty root. Used by 'emitGlobal' /
-- 'compileFunctionGlobal' so the walk-and-lookup keys land in the right
-- definition's table at the right structural offset.
withBodyOwn :: Maybe OwnInfo -> [Int] -> Gen a -> Gen a
withBodyOwn own prefix act = do
  savedOwn <- gets gsCurOwn
  savedPath <- gets gsPath
  modify' $ \st -> st {gsCurOwn = own, gsPath = prefix}
  r <- act
  modify' $ \st -> st {gsCurOwn = savedOwn, gsPath = savedPath}
  pure r

-- | The per-definition ownership side-table for global @g@, if the analysis
-- recorded one. 'Nothing' for a global with no entry (no recorded core body, or
-- the analysis produced none) — then the walk-and-lookup is skipped for its body.
curOwnInfo :: GName -> Gen (Maybe OwnInfo)
curOwnInfo g = Map.lookup g <$> gets gsOwnership

-- | Fetch the ownership table for a runtime body about to be compiled. In RC
-- validation mode, absence is a hard finding: compiling without the side-table
-- would make every CVar in the body fail open.
requireOwnInfo :: GName -> Gen (Maybe OwnInfo)
requireOwnInfo g = do
  own <- curOwnInfo g
  enabled <- gets gsRcEnabled
  case (enabled, own) of
    (True, Nothing) ->
      rcRecordFinding $
        rcUseSiteMiss
          g
          Nothing
          []
          "no OwnInfo entry for compiled runtime body"
    _ -> pure ()
  pure own

-- | The Perceus RC walk-and-lookup at a 'CVar' occurrence
-- (PERCEUS-S2-PLAN (b.2)/(d)). INERT unless 'gsRcEnabled'. When on: build the
-- 'UseSite' for this occurrence (the current global plus @reverse gsPath@) and
-- require both @oiUses@ and @oiUseConsumes@ entries in 'gsCurOwn'. This is the
-- validation guard for the dup/drop decisions emitted elsewhere in S2.
--
--   * A resolved 'UseSite' with a consume/read bit is the expected case — the
--     path threading reached the same structural node the analysis keyed.
--   * A missing @oiUses@ or @oiUseConsumes@ entry is a hard validation miss.
--     Falling back to "no side-table fact" could silently suppress a required S2
--     ownership action, so the ON build fails closed.
rcRecordFinding :: Text -> Gen ()
rcRecordFinding msg =
  modify' $ \st -> st {gsRcFindings = msg : gsRcFindings st}

rcUseSiteMiss :: GName -> Maybe Int -> [Int] -> Text -> Text
rcUseSiteMiss g mi path detail =
  gKey g
    <> maybe "" (\i -> " CVar#" <> T.pack (show i)) mi
    <> " @" <> T.pack (show (reverse path))
    <> ": "
    <> detail

rcWalkLookupVar :: Int -> Gen ()
rcWalkLookupVar i = do
  enabled <- gets gsRcEnabled
  when enabled $ do
    mown <- gets gsCurOwn
    case mown of
      Nothing -> pure () -- no per-definition table in scope (CAF prologue / lifted helper)
      Just own -> do
        g <- gets gsCur
        path <- gets gsPath
        let us = UseSite g (reverse path)
        case Map.lookup us (oiUses own) of
          Just _
            | Map.member us (oiUseConsumes own) -> pure () -- resolved: the threaded path and consume/read bit match the analysis key
            | otherwise ->
                rcRecordFinding $
                  rcUseSiteMiss
                    g
                    (Just i)
                    path
                    "no oiUseConsumes entry for resolved oiUses key"
          Nothing ->
            rcRecordFinding $
              rcUseSiteMiss
                g
                (Just i)
                path
                "no oiUses entry"

-- | The S2.3b use verdict plus the consume/read bit for THIS occurrence. The
-- consume bit is required whenever a use verdict is present; validation records
-- missing bits as side-table misses, and emission declines to act without both
-- facts.
rcUseInfoHere :: Gen (Maybe (UseKind, Bool))
rcUseInfoHere = do
  enabled <- gets gsRcEnabled
  if not enabled
    then pure Nothing
    else do
      mown <- gets gsCurOwn
      case mown of
        Just own -> do
          g <- gets gsCur
          path <- gets gsPath
          let us = UseSite g (reverse path)
          pure $ do
            k <- Map.lookup us (oiUses own)
            consumes <- Map.lookup us (oiUseConsumes own)
            pure (k, consumes)
        _ -> pure Nothing

-- | Wrap a 'CVar' use-expression in @kdup(...)@ when the analysis classified the
-- occurrence as a consuming 'NonLast' (S2.2 / b.2 plus S2.3b): the value is used
-- again downstream and the current consumer receives its own reference. Read-only
-- 'NonLast' occurrences (projection bases, borrowed call args) leave the bare
-- expression, since no consumer-side drop will balance a dup. 'kdup' skips
-- immediates (its @kis_imm@ guard), so an immediate-valued binder wrap is a
-- runtime no-op.
rcDupVarUse :: Text -> Gen Text
rcDupVarUse e = do
  mi <- rcUseInfoHere
  pure $ case mi of
    Just (NonLast, True) -> "kdup(" <> e <> ")"
    _ -> e

-- | Compile the raw C expression for a variable occurrence after validating the
-- ownership side-table path. This intentionally does not apply a dup/move
-- policy; callers choose that policy according to the value-flow context.
compileVarRef :: Int -> Gen Text
compileVarRef i = do
  rcWalkLookupVar i
  lvals <- gets gsParamLvals
  if not (null lvals) && i >= 0 && i < length lvals
    then pure (lvals !! i)
    else do
      env <- gets gsEnv
      pure ("kvar(" <> env <> ", " <> T.pack (show (i - length lvals)) <> ")")

-- | Compile a variable occurrence whose value flows into a position that
-- requires an owned reference. A consuming NonLast use already needs a dup; a
-- consuming LastUse can move only when the current flat local is known to own
-- the reference. Borrowed/non-owning locals, including values just read from a
-- mutable cell, must be materialized with kdup before the callee/store consumes
-- the argument. Non-flat/unknown locals are treated conservatively: an extra dup
-- is leak-biased, while moving a borrowed cell read becomes a UAF after S3.3
-- drop-old barriers.
compileOwnedVarUse :: Int -> Gen Text
compileOwnedVarUse i = do
  e <- compileVarRef i
  rcOn <- gets gsRcEnabled
  if not rcOn
    then pure e
    else do
      mi <- rcUseInfoHere
      sourceOwns <- flatLocalOwnsAt i
      let needsDup = case mi of
            Just (_, False) -> False
            Just (NonLast, True) -> True
            Just (LastUse, True) -> not sourceOwns
            Just (Borrowed, True) -> True
            Nothing -> not sourceOwns
      pure $ if needsDup then "kdup(" <> e <> ")" else e

-- | A projection such as @p.left@ borrows its field from the owning aggregate
-- @p@. When that projection result is itself going to be returned, stored in an
-- owning local, or transferred to a consuming call, codegen must materialise an
-- owned reference with @kdup@ before any later cleanup can drop @p@. The proof is
-- the structural base term plus the ownership side table for that exact base use:
-- an owned flat local read in a non-consuming position. No field-name recognition.
rcProjectionResultCanOwn :: Term -> Gen Bool
rcProjectionResultCanOwn = \case
  CVar i -> do
    mi <- rcUseInfoHere
    sourceOwns <- flatLocalOwnsAt i
    pure $ sourceOwns && case mi of
      Just (_, False) -> True
      _ -> False
  CSealE _ e -> withChild P.childPos (rcProjectionResultCanOwn e)
  _ -> pure False

rcOwnProjectionResult :: Bool -> Term -> Text -> Gen Text
rcOwnProjectionResult needOwned base raw =
  if not needOwned
    then pure raw
    else do
      canOwn <- withChild P.childPos (rcProjectionResultCanOwn base)
      pure $ if canOwn then "kdup(" <> raw <> ")" else raw

flatLocalOwnsAt :: Int -> Gen Bool
flatLocalOwnsAt i = do
  owns <- gets gsParamOwns
  pure $ case drop i owns of
    own : _ -> own
    [] -> False

withFlatLocalOwnership :: Maybe BinderId -> Bool -> Gen a -> Gen a
withFlatLocalOwnership mbid ownsRef act = do
  lvals <- gets gsParamLvals
  if null lvals
    then act
    else do
      saved <- saveFlatLocalScope
      modify' $ \st ->
        st
          { gsParamLvals = "proof_local" : gsParamLvals st
          , gsParamBinders = mbid : gsParamBinders st
          , gsParamOwns = ownsRef : gsParamOwns st
          }
      r <- act
      restoreFlatLocalScope saved
      pure r

-- | Conservative S2.3b/S2.3d ownership result check for a flat @let@
-- initializer.
-- Scope-close drops are only safe when the local is known to hold an owned
-- reference. Projection results are accepted only when their base-use side-table
-- proves an owned aggregate is read in a non-consuming position and the result
-- site can materialise an owned @kdup@; unproven call/projection shapes stay
-- leak-biased. A saturated eta-expanded constructor application is accepted
-- because this same structural recognizer is what codegen beta-reduces to a
-- direct fresh @kctor@ allocation; this is symbolically tied to the Core shape,
-- not to a source spelling.
rcTermProducesOwnedHere :: Term -> Gen Bool
rcTermProducesOwnedHere t = case t of
  CApp {}
    | Just {} <- etaCtorApp t -> pure True
  CVar i -> do
    mi <- rcUseInfoHere
    sourceOwns <- flatLocalOwnsAt i
    pure $ case mi of
      Just (LastUse, True) -> sourceOwns
      Just (NonLast, True) -> True
      _ -> False
  CCtor {} -> pure True
  CRecordV {} -> pure True
  CInject {} -> pure True
  CThunkE {} -> pure True
  CLazyE {} -> pure True
  CSealE _ e -> withChild P.childPos (rcTermProducesOwnedHere e)
  CProj e _ -> withChild P.childPos (rcProjectionResultCanOwn e)
  CProjAt e _ _ -> withChild P.childPos (rcProjectionResultCanOwn e)
  CIf _ th el ->
    (&&)
      <$> withChild P.ifThenPos (rcTermProducesOwnedHere th)
      <*> withChild P.ifElsePos (rcTermProducesOwnedHere el)
  CLet _ _ _ rhs body -> do
    rhsOwns <- withChild P.letRhsPos (rcTermProducesOwnedHere rhs)
    bid <- currentBinderIdHere
    withFlatLocalOwnership (Just bid) rhsOwns $
      withChild P.letBodyPos (rcTermProducesOwnedHere body)
  CLetRec _ _ _ rhs body -> do
    rhsOwns <- withChild P.letRhsPos (rcTermProducesOwnedHere rhs)
    bid <- currentBinderIdHere
    withFlatLocalOwnership (Just bid) rhsOwns $
      withChild P.letBodyPos (rcTermProducesOwnedHere body)
  CMatch _ _ alts ->
    withChild P.matchArmsPos $
      and
        <$> forM
          (zip [0 ..] alts)
          ( \(ai, CaseAlt _ _ body) ->
              withChild (P.matchArmPos ai) $
                withChild P.altBodyPos (rcTermProducesOwnedHere body)
          )
  _ -> pure False

binderHasConsumingLastUse :: OwnInfo -> BinderId -> Bool
binderHasConsumingLastUse own bid =
  any (== LastUse) (Map.findWithDefault [] bid (oiBinderConsumingUses own))

-- | The S2.3 drop DECISION for a binder introduced at the CURRENT 'gsPath' (its
-- 'BinderId' is @gsCur@ + @reverse gsPath@) — the seam where the binder node is
-- compiled, BEFORE descending into its body/arm. Returns 'True' iff a @kdrop@
-- against the binder's bound C local should be emitted at that scope's close
-- (b.4):
--
--   * the binder is 'boDroppable' (@0@\/@≤1@\/@ω@ — carries no consumption
--     obligation) and NOT 'boBorrowed' (a borrowed value is the caller's; the
--     callee never drops it — §1\/§3); AND
  --   * the binder has NO consuming 'LastUse' occurrence in its scope
  --     ('oiBinderConsumingUses' holds no 'LastUse'). Non-consuming projection
  --     reads may coexist with the close-drop because projection results are now
  --     owned at the result/let/consuming-call sites that can outlive the aggregate.
  --     S2.3d branch-dead drops are handled separately by
--     'rcEmitBranchDeadDropsHere', using explicit path-local drop sites and the
--     current flat-local ownership metadata; this helper remains the ordinary
--     whole-scope close-drop gate.
--
-- Inert under the OFF baseline (returns 'False' without a lookup), so codegen is
-- byte-identical. A missing ownership table yields 'False'.
rcBinderDroppableHere :: Gen Bool
rcBinderDroppableHere = do
  enabled <- gets gsRcEnabled
  if not enabled
    then pure False
    else do
      mown <- gets gsCurOwn
      case mown of
        Just own -> do
          g <- gets gsCur
          path <- gets gsPath
          let bid = BinderId g (reverse path)
          pure $ case Map.lookup bid (oiBinders own) of
            Just bo
              | boDroppable bo
              , not (boBorrowed bo)
              , not (binderHasConsumingLastUse own bid) ->
                  True
            _ -> False
        _ -> pure False

-- | Like 'rcBinderDroppableHere' but for a pattern-slot binder at slot @k@ of the
-- match arm currently being compiled (its 'BinderId' is @gsCur@ +
-- @reverse (patSlotPos k : gsPath)@ — the same key 'Kappa.Ownership.walkAlt'
-- records). Used to decide whether the per-arm @kdrop@ of a destructured field
-- local fires (b.4, per-arm completion path in 'consumeAlt').
rcPatSlotDroppableHere :: Int -> Gen Bool
rcPatSlotDroppableHere k = do
  enabled <- gets gsRcEnabled
  if not enabled
    then pure False
    else do
      mown <- gets gsCurOwn
      case mown of
        Just own -> do
          g <- gets gsCur
          path <- gets gsPath
          let bid = BinderId g (reverse (P.patSlotPos k : path))
          pure $ case Map.lookup bid (oiBinders own) of
            Just bo
              | boDroppable bo
              , not (boBorrowed bo)
              , not (binderHasConsumingLastUse own bid) ->
                  True
            _ -> False
        _ -> pure False

-- | Emit a @kdrop(<lval>)@ statement against a bound C LOCAL (b.4 / R-flat:
-- ALWAYS the bound local, never a fresh @kvar(env,i)@ rvalue re-read). The
-- runtime decrements RC and, in S3/S4, may reclaim strict FREESET values at zero;
-- the @kdrop@ assert remains the primary differential check for underflow.
rcEmitDrop :: Text -> Gen ()
rcEmitDrop lv = emit ("kdrop(" <> lv <> ");")

-- | The binder introduced at the current structural path.
currentBinderIdHere :: Gen BinderId
currentBinderIdHere = do
  g <- gets gsCur
  path <- gets gsPath
  pure (BinderId g (reverse path))

-- | The pattern-slot binder introduced at slot @k@ under the current structural
-- path.
currentPatSlotBinderId :: Int -> Gen BinderId
currentPatSlotBinderId k = do
  g <- gets gsCur
  path <- gets gsPath
  pure (BinderId g (reverse (P.patSlotPos k : path)))

-- | S2.3d branch-dead drop emission. The ownership table names binders that
-- are absent from this selected branch while live in a sibling path; this
-- helper resolves those binder identities to the current flat C locals and
-- emits drops only when the local is known to own a reference and the binder is
-- droppable/non-borrowed. In a top-level flat worker frame, missing
-- binder-to-local metadata for a droppable site is a validation finding.
-- Capture-free nested flat closures may drop their own resolved owned locals;
-- missing outer captured binders and boxed/CPS paths remain conservative
-- no-drops. A resolved local with unproven ownership also remains a
-- conservative no-drop. No guessed @kvar@ reread, no name-based match.
rcEmitBranchDeadDropsHere :: Gen ()
rcEmitBranchDeadDropsHere = do
  enabled <- gets gsRcEnabled
  when enabled $ do
    mown <- gets gsCurOwn
    case mown of
      Nothing -> pure ()
      Just own -> do
        path <- reverse <$> gets gsPath
        g <- gets gsCur
        modify' $ \st -> st {gsRcBranchVisited = Set.insert (g, path) (gsRcBranchVisited st)}
        lvals <- gets gsParamLvals
        bids <- gets gsParamBinders
        owns <- gets gsParamOwns
        topFlat <- gets gsTopFlatFrame
        let siteBids = Map.findWithDefault [] path (oiBranchDropSites own)
            flat = zip3 lvals bids owns
            knownFlatBids = [bid | (_, Just bid, _) <- flat]
            lvalFor bid =
              case [lv | (lv, Just bid', True) <- flat, bid' == bid] of
                lv : _ -> Just lv
                [] -> Nothing
            droppable bid =
              case Map.lookup bid (oiBinders own) of
                Just bo -> boDroppable bo && not (boBorrowed bo)
                Nothing -> False
            targets =
              [ lv
              | bid <- siteBids
              , droppable bid
              , Just lv <- [lvalFor bid]
              ]
            unresolvedDroppable =
              [ bid
              | bid <- siteBids
              , droppable bid
              , bid `notElem` knownFlatBids
              ]
        case unresolvedDroppable of
          _ | not topFlat -> pure ()
          [] -> pure ()
          _ ->
            rcRecordFinding $
              rcUseSiteMiss
                g
                Nothing
                (reverse path)
                ( "branch drop site listed droppable binder(s) with no top-level flat-local metadata: "
                    <> T.intercalate ", " (map (T.pack . show) unresolvedDroppable)
                )
        mapM_ rcEmitDrop targets

-- | Perceus RC S2.3a (§a) — the MATCH-DESTRUCTURE cell-drop DECISION.
--
-- A @match@'s arms read their scrutinee's fields out via BORROWING projections
-- (@kctor_arg@\/@kproj@\/@krec_at@\/@kvariant_payload@ all return the field
-- without an incref), so once the bound fields are dup'd-out the scrutinee CELL
-- itself is leaked unless the match drops it. This decides, from the SCRUTINEE
-- shape and (for a 'CVar' scrutinee) its use verdict plus consume bit at the
-- 'matchScrutPos' seam,
-- whether the match owns a reference to the cell that it must discharge with a
-- @kdrop(sv)@:
--
--   * a __'CVar'__ scrutinee — look up its use verdict and consume bit at
--     current @matchScrutPos@ (the exact key "Kappa.Ownership"'s walk records
--     for the scrutinee occurrence). Drop for consuming 'LastUse' only when the
--     source flat local itself owns the value. Drop for consuming 'NonLast'
--     because the occurrence was already @kdup@'d at its 'CVar' site, so the
--     match consumes the freshly incremented reference it received. NEVER drop
--     for read-only/borrowed occurrences — the caller or enclosing owner still
--     owns the value (§1\/§3 borrow invariant), and a @kdrop@ here would be the
--     decrement-below-floor the underflow assert exists to catch.
--   * a fresh structural scrutinee — 'CCtor', 'CRecordV', 'CInject', or the
--     saturated eta-expanded constructor application that codegen lowers to the
--     same direct @kctor@ as 'CCtor' — is an owning value: rc==1, no other owner,
--     dies at the match ⇒ ALWAYS drop. 'CSealE' is transparent to this decision.
--   * any __other__ shape (a general 'CApp' call result, 'CProj'\/'CForceE'\/… whose head
--     may be a borrowing projection returning a non-owned reference, or an
--     unresolvable 'CVar') — do NOT drop: dropping a borrowed-out reference would
--     underflow. This remains leak-biased until the producer shape has a local
--     ownership proof like the structural constructor cases above.
--
-- Inert under the OFF baseline, so codegen is byte-identical there.
rcScrutDropDecision :: Term -> Gen Bool
rcScrutDropDecision scrut = do
  enabled <- gets gsRcEnabled
  if not enabled
    then pure False
    else withChild P.matchScrutPos (go scrut)
  where
    go = \case
      CVar i -> do
        -- Drop only when the resolved occurrence is consuming and the
        -- match owns the reference it compiled: a consuming NonLast has been
        -- dup'd at the CVar site, while a consuming LastUse is droppable only
        -- if the source flat local itself owns the value.
        mi <- rcUseInfoHere
        sourceOwns <- flatLocalOwnsAt i
        pure $ case mi of
          Just (LastUse, True) -> sourceOwns
          Just (NonLast, True) -> True
          _ -> False
      t@CApp {}
        | Just {} <- etaCtorApp t -> pure True
      -- Fresh owning allocations: rc==1, die at the match.
      CCtor {} -> pure True
      CRecordV {} -> pure True
      CInject {} -> pure True
      CSealE _ e -> withChild P.childPos (go e)
      -- General calls and projections can return borrowed references. Without
      -- result ownership metadata, do not drop them as match-owned cells.
      _ -> pure False

-- | The S2.3 OWNED/BORROWED call-boundary classification (b.3) at a 'CGlob' call
-- head: read the callee's owned\/borrowed\/shared parameter convention from its
-- declared type plus S2.3c primitive overrides ('Repr.argConvSelectGlobal', the
-- S1.5-validated accessor). This helper remains validation-only: current codegen
-- consumes the same convention at argument lowering sites via
-- 'callArgNeedsOwnedForGlobal'/'compileCallArg', where owned arguments are
-- materialized and borrowed arguments stay bare. There is still NO caller-side
-- post-call drop —
--
--   * 'Repr.ArgOwned' — the caller TRANSFERS ownership; the callee consumes
--     (drops\/reuses) it. No caller drop.
--   * 'Repr.ArgShared' — a conservative transfer (the callee may dup\/drop). No
--     caller drop.
--   * 'Repr.ArgBorrowed' — the callee NEVER drops; the value stays the caller's
--     and is reclaimed at the caller's OWN binder seam (b.4), NEVER post-call.
--     This is the §1\/§3 borrow invariant — a borrowed value (e.g. one reachable
--     from a live ExitStack) is never dropped by the callee.
--
-- The argument's own dup\/move is decided at the lowering point for that argument
-- (or, for ordinary expression reads, per-occurrence at its 'CVar'), and the drop
-- discipline (b.4) never drops a @boBorrowed@ binder — so the convention is
-- honoured WITHOUT any extra emission here. We still evaluate
-- 'Repr.argConvSelectGlobal' on the ON path (forcing it) so the S1.5-validated accessor
-- is exercised over the corpus and a regression in it would surface; a non-'CGlob'
-- head, or an unwalkable codomain ('Nothing'), is the all-shared fallback (still
-- no drop). 'boRefined' (§3a) is observe-only and NOT consulted (that is S3+).
-- Inert under the OFF baseline. (Deliberately does NOT write 'gsRcFindings' — that
-- channel is the R-path miss signal; per-call boundary noise would corrupt its
-- \"zero misattribution\" count.)
rcClassifyCallBoundary :: GName -> Gen ()
rcClassifyCallBoundary g = do
  enabled <- gets gsRcEnabled
  when enabled $ do
    ctx <- gets gsEvalCtx
    let convs = Repr.argConvSelectGlobal ctx g -- unknown global → all-shared fallback
    -- Force the accessor so it is genuinely exercised on the ON path (a regression
    -- in the S1.5-validated convention walk would surface here); the verdict is
    -- otherwise unused by this validation-only helper.
    length (show convs) `seq` pure ()

-- | Run an action with a fresh (empty) statement buffer and the given
-- current-env expression, returning the produced statements in order plus
-- the action's result; restores the caller's buffer and env afterwards.
captured :: Text -> Gen a -> Gen ([Text], a)
captured env act = do
  saved <- gets gsStmts
  savedEnv <- gets gsEnv
  -- R2.3-rest: a flat worker binds let/match vars by prepending C locals to
  -- gsParamLvals; restoring it here scopes those bindings to this block (an
  -- if-branch / match-alt), exactly as the KEnv tail did for the boxed path.
  -- A no-op for the boxed path (gsParamLvals is empty there).
  savedFlat <- saveFlatLocalScope
  modify' $ \g -> g {gsStmts = [], gsEnv = env}
  r <- act
  produced <- gets gsStmts
  modify' $ \g ->
    g
      { gsStmts = saved
      , gsEnv = savedEnv
      }
  restoreFlatLocalScope savedFlat
  pure (reverse produced, r)

-- | Record an unsupported-construct finding and return a placeholder C
-- expression so error collection can continue.
unsupported :: Text -> Text -> Gen Text
unsupported construct detail = do
  g <- gets gsCur
  sites <- gets gsDeclSites
  let sp = Map.findWithDefault noSpan g sites
  modify' $ \st -> st {gsErrs = backendUnsupported g sp construct detail : gsErrs st}
  pure "kunit()"

-- | A construct that is provably NOT a runtime value of an accepted,
-- erased program (a type-level term, an elaboration invariant, or an
-- elaboration-time/staging value). Reaching it in value position is an
-- internal-invariant violation reported (never silently miscompiled) per
-- §27.7; see docs/NATIVE_ESCALATIONS.md. Same diagnostic channel as
-- 'unsupported' — the detail carries the spec citation.
escalated :: Text -> Text -> Gen Text
escalated = unsupported

-- | Enqueue a global for emission (idempotent).
enqueue :: GName -> Gen ()
enqueue g = do
  seen <- gets gsEmitted
  unless (g `Set.member` seen) $
    modify' $ \st -> st {gsEmitted = Set.insert g (gsEmitted st), gsQueue = g : gsQueue st}

-- ── Names ────────────────────────────────────────────────────────────

-- | A unique, valid C identifier for a global's accessor function.
cGlobIdent :: GName -> Text
cGlobIdent g = "kg_" <> mangle (gKey g)

mangle :: Text -> Text
mangle = T.concatMap esc
  where
    esc c
      | isAsciiLower c || isAsciiUpper c || isDigit c = T.singleton c
      | otherwise = "_" <> T.pack (showHex (ord c) "") <> "_"

-- | A C string literal (quoted, escaped) for arbitrary UTF-8 text.
cStr :: Text -> Text
cStr t = "\"" <> T.concatMap esc t <> "\""
  where
    esc c = case c of
      '"' -> "\\\""
      '\\' -> "\\\\"
      '\n' -> "\\n"
      '\t' -> "\\t"
      '\r' -> "\\r"
      _
        | isAscii c && c >= ' ' -> T.singleton c
        -- Emit non-ASCII / control bytes via their UTF-8 octets in OCTAL.
        -- A C octal escape consumes at most three digits, so \NNN cannot be
        -- extended by a following ASCII digit (unlike \xNN, which greedily
        -- absorbs subsequent hex digits — e.g. "café2" would mis-escape).
        | otherwise -> T.concat [octet b | b <- utf8Bytes c]
    octet b = "\\" <> T.pack (pad3 (showOct b ""))
    pad3 s = replicate (3 - length s) '0' ++ s

-- | A C @kstr@ literal carrying the exact UTF-8 byte length.  A String
-- literal may contain an embedded NUL (@\\u{0}@), so it must NOT be built
-- with @kstr0@ (which derives the length via @strlen@ and would truncate
-- at the NUL — corrupting both I/O and String equality).  @cStr@ escapes
-- the NUL as an octal byte, and this length is the UTF-8 byte count.
cStrL :: Text -> Text
cStrL s = "kstr(" <> cStr s <> ", " <> T.pack (show (utf8Len s)) <> ")"

-- ── LR2: numeric constructor / variant tags ─────────────────────────
--
-- A constructor/variant value carries a small integer `tagid` so pattern
-- matching dispatches on an int compare (kctor_tagid/kvariant_tagid) instead
-- of a kctor_is/kvariant_is strcmp.  The id must be IDENTICAL at every
-- construction site and every match site for a given name; codegen guarantees
-- this with one rule:
--
--   * the runtime builds 8 builtins (Unit/True/False/::/Nil/Some/None/__rat)
--     so those share a FIXED enum with the runtime — codegen spells them with
--     the kappart.h `KCT_*` names (`builtinCtorTag`);
--   * every other (user) constructor is referenced by a `KT_<mangle gKey>`
--     name, collected into `gsCollectCtors`, and given a `KCT_USER_BASE + i`
--     id by `assemble` (the value is irrelevant to correctness — both sides
--     use the same symbolic name — only its disjointness from the builtins,
--     guaranteed by KCT_USER_BASE, and from other user ctors, guaranteed by
--     `mangle` being injective, matter);
--   * variants are never runtime-built, so all variant tags are user ids:
--     a `KVT_<mangle tag>` name, collected into `gsCollectVars`, 0-based.

-- | The fixed kappart.h @KCT_*@ id for a runtime-built builtin constructor,
-- or @Nothing@ for a user constructor (which gets a @KT_*@ id). A thin
-- re-export of the single source of truth in "Kappa.Builtins"
-- ('Builtins.runtimeCtors'); the emitted symbolic @KCT_*@ name is resolved to
-- its numeric value by the C compiler against the included @kappart.h@.
--
-- §11 Ordering (LT\/EQ\/GT) is deliberately NOT here: @durationCompare@ and
-- the @Ord@ instances are @.kp@ definitions, so Ordering is a USER constructor
-- codegen builds (id @KCT_USER_BASE+i@) — the runtime never delivers it.
builtinCtorTag :: Text -> Maybe Text
builtinCtorTag = Builtins.builtinCtorCName

-- | The C tag constant for a constructor, recording a user constructor's use
-- so @assemble@ emits its @KT_*@ enum entry.
ctorTagConst :: GName -> Gen Text
ctorTagConst g = case builtinCtorTag (gKey g) of
  Just kc -> pure kc
  Nothing -> do
    modify' $ \st -> st {gsCollectCtors = Set.insert (gKey g) (gsCollectCtors st)}
    pure ("KT_" <> mangle (gKey g))

-- | The C tag constant for a §13 variant member tag, recording its use so
-- @assemble@ emits its @KVT_*@ enum entry.
variantTagConst :: Text -> Gen Text
variantTagConst tag = do
  modify' $ \st -> st {gsCollectVars = Set.insert tag (gsCollectVars st)}
  pure ("KVT_" <> mangle tag)

-- | The @enum { KT_… = …, … }@ blocks for every collected user constructor
-- and variant tag, emitted by @assemble@ after @#include "kappart.h"@ so the
-- symbolic names referenced in generated constructions/matches are defined.
tagEnumBlock :: GenState -> [Text]
tagEnumBlock st =
  ctorBlock (Set.toList (gsCollectCtors st))
    ++ block "KVT_" "" (Set.toList (gsCollectVars st))
  where
    -- KBackendIR Stage 2: the user-ctor numbering (sort gKeys, assign
    -- @KCT_USER_BASE + i@) is the single authority 'Repr.assignUserCtorTags',
    -- shared with the LLVM backend so the two agree on every id by
    -- construction.  We still EMIT the symbolic @KCT_USER_BASE + i@ offset
    -- (byte-identical to before — the C compiler resolves it against the
    -- included kappart.h), but derive @i@ from the shared id map rather than a
    -- second open-coded @sort@ + @zip@.
    ctorBlock names = case sort names of
      [] -> []
      sorted ->
        let ids = Repr.assignUserCtorTags names
         in ["enum {"]
              ++ [ "  KT_" <> mangle n <> " = KCT_USER_BASE + "
                     <> T.pack (show (Map.findWithDefault 0 n ids - Builtins.kctUserBase)) <> ","
                 | n <- sorted
                 ]
              ++ ["};"]
    -- §13 variant member tags are never runtime-built (no shared id authority);
    -- they keep their own 0-based per-program numbering.
    block prefix base names = case sort names of
      [] -> []
      sorted ->
        ["enum {"]
          ++ [ "  " <> prefix <> mangle n <> " = " <> base <> T.pack (show i) <> ","
             | (i, n) <- zip [(0 :: Int) ..] sorted
             ]
          ++ ["};"]

-- | The number of UTF-8 bytes a 'Text' encodes to (the C string length).
utf8Len :: Text -> Int
utf8Len = T.foldl' (\acc c -> acc + length (utf8Bytes c)) 0

-- | UTF-8 encode a single character to bytes.
utf8Bytes :: Char -> [Int]
utf8Bytes c =
  let n = ord c
   in if n < 0x80
        then [n]
        else if n < 0x800
          then [0xC0 + (n `div` 0x40), 0x80 + (n `mod` 0x40)]
          else if n < 0x10000
            then [0xE0 + (n `div` 0x1000), 0x80 + ((n `div` 0x40) `mod` 0x40), 0x80 + (n `mod` 0x40)]
            else
              [ 0xF0 + (n `div` 0x40000)
              , 0x80 + ((n `div` 0x1000) `mod` 0x40)
              , 0x80 + ((n `div` 0x40) `mod` 0x40)
              , 0x80 + (n `mod` 0x40)
              ]

-- ── Top-level driver ─────────────────────────────────────────────────

-- | The primitive names implemented by the base @kappart@ runtime
-- (the split C runtime under @runtime/@). Kept in lock-step with that runtime:
-- emitting a primitive
-- outside this set (plus any FFI extension) is a compile-time
-- 'E_BACKEND_UNSUPPORTED'.
basePrims :: Set Text
basePrims =
  Set.fromList
    [ -- integer
      "addInt", "subInt", "mulInt", "divInt", "modInt", "negInt"
    , "eqInt", "ltInt", "leInt"
      -- §18.1.6 Duration/Instant constructors, compare, arithmetic, clock
    , "__nowNanos" -- §18.1 clock prim (raw ns); Duration/Instant ops are the std.time .kp fragment
      -- double
    , "addDouble", "subDouble", "mulDouble", "divDouble", "negDouble"
    , "eqDouble", "ltDouble", "floatEq"
      -- §6.1.7 libm floating-point / transcendental math + fixed-precision format
    , "sqrt", "sin", "cos", "tan", "asin", "acos", "atan", "atan2"
    , "exp", "log", "pow", "floor", "ceil", "fabs", "showFixed"
      -- string / scalar
    , "stringAppend", "eqStr", "ltStr", "eqScalar", "ltScalar"
    , "showInt", "showDouble", "showScalar", "showStringLit"
      -- §28.2 Rational
    , "__ratOfInt", "__ratNum", "__ratDen", "addRat", "subRat", "mulRat"
    , "divRat", "negRat", "eqRat", "ltRat", "showRat", "ratOfDouble"
      -- §6.1 numeric conversions
    , "natToInt", "natOfInt", "intToNat", "intToDouble", "primitiveIntToString"
      -- §6.5/§29.5 byte / bytes / grapheme atoms
    , "eqByte", "ltByte", "showByte", "eqBytes", "ltBytes", "showBytes"
    , "eqGrapheme", "showGrapheme"
      -- §29.5 std.bytes portable operations over the exact byte sequence
    , "__bytesEmpty", "__bytesSingleton", "__bytesLength", "__bytesIsEmpty"
    , "__bytesGet", "__bytesIndexUnsafe", "__bytesAppend", "__bytesSlice"
    , "__bytesTake", "__bytesDrop", "__bytesStartsWith", "__bytesEndsWith"
    , "__bytesContains", "__bytesFind", "__bytesBreakIndex", "__bytesToList"
    , "__bytesFromList", "__bytesCompact"
      -- §29.5 linear BytesBuilder
    , "__newBytesBuilder", "__bytesBuilderByte", "__bytesBuilderBytes"
    , "__finishBytesBuilder"
      -- §29.4 std.unicode (table-free): UTF-8 codec, scalars, byte/nat
    , "__utf8Bytes", "__utf8Valid", "__decodeUtf8Lossy", "__byteLength"
    , "__uniScalarValue", "__scalarInRange", "__scalarOfValue", "__scalarToString"
    , "__stringScalars", "__scalarCount", "__byteToNat", "__natToByte"
    , "__graphemeToString"
      -- §29.4 StringBuilder + string cursors + incremental UTF-8 decoder
    , "__newStringBuilder", "__stringBuilderString", "__stringBuilderScalar"
    , "__stringBuilderGrapheme", "__finishStringBuilder"
    , "__stringStart", "__stringEnd", "__stringCursorOffset", "__stringNextScalar"
    , "__stringPrevScalar", "__stringSpan", "__stringCompact"
    , "__newUtf8Decoder", "__decodeUtf8Chunk", "__finishUtf8Decoder"
      -- §29.4 table-driven Unicode (UAX#15 normalization, UAX#29 segmentation)
    , "__normalize", "__caseFold", "__stringGraphemes", "__graphemeCount"
    , "__graphemeValid", "__graphemeOfString", "__stringNextGrapheme"
    , "__stringWords", "__stringSentences"
      -- §29.1 std.atomic bitwise + repr-equality + §29.3 std.hash FNV-1a
    , "__intAnd", "__intOr", "__intXor", "__atomicRepEq"
      -- §29.1 std.atomic boxed mutex-protected cell ops -> krt2_atomic_* (runtime/atomic.c)
    , "__newAtomicRef", "__atomicLoad", "__atomicStore", "__atomicExchange"
    , "__atomicCompareExchange", "__atomicFetchAdd", "__atomicFetchSub"
    , "__atomicFetchAnd", "__atomicFetchOr", "__atomicFetchXor"
    , "__hashMixInt", "__hashMixDouble", "__hashMixString", "__hashMixBytes"
      -- §20 collection carriers / §28.2 transport / range enumeration
    , "__queryFromList", "__queryToList", "__setFromList", "__setToList"
    , "__arrayFromList", "__arrayToList", "__mapFromEntries", "__mapToList"
    , "__transport", "__arrayIndexUnsafe", "__rangeEnum", "unsafeConsume"
      -- §28.2 proof helper
    , "__absurd"
      -- IO
    , "printString", "printlnString", "ioPure", "ioBind", "ioThen", "throwIO", "catchIO", "finallyIO"
    , "onExit", "onInterrupt" -- §18.1.4 reason-carrying finalizers; lowered to krt2_on_exit/krt2_on_interrupt nodes (compileAppGlob)
    , "__reraiseCause" -- §18.1.4 re-raise a full Cause; lowered to a krt2_reraise node (compileAppGlob), no primEntry
    , "__race", "__timeout" -- §18.1.6 lowered to krt2_race/krt2_timeout nodes (compileAppGlob), no primEntry
    , "withScope", "__interruptWait", "__interruptNoWait", "__interruptForkAny" -- §19.5/§18.1.4 lowered to krt2_* nodes (compileAppGlob)
    , "blocking" -- §18.1.11 rt-blocking source bridge; lowered to krt2_blocking (compileAppGlob)
    , "uninterruptible", "__mask", "poll" -- §18.1.12 masking; lowered to krt2_uninterruptible/krt2_mask/krt2_poll nodes (compileAppGlob)
    , "__restoreAt" -- §18.1.12 rank-2 restore adapter; lowered to a bare kapp(raw, act) onto the 1-arg runtime restore (compileAppGlob); no runtime entry of its own
    , "demonitor" -- §18.1.8 no-op; kpf_demonitor shim (primEntries)
    , "__ioNewRef", "__ioReadRef", "__ioWriteRef"
      -- MUTABLE-ARRAY-DESIGN §4.1 boxed mutable array (kpf_io___newArray/...)
    , "__newArray", "__arrayRead", "__arrayWrite", "__arrayLen"
      -- §18.1.7 fiber-local state (FiberRef cells; copy-on-fork at fork); kpf_*_fiber_ref shims
    , "newFiberRef", "getFiberRef", "setFiberRef", "modifyFiberRef"
    , "locallyFiberRef" -- §18.1.7 lowered to a krt2_locally_fiber_ref bind tree (compileAppGlob)
      -- §18.1.13 STM (single-agent: TVar = cell, `atomically` runs the action)
    , "newTVar", "readTVar", "writeTVar", "atomically", "retry", "stmBind", "stmPure"
      -- §18.1.4/.6/.9 concurrency node builders (CPS do-kernel)
    , "__forkRun", "__forkDaemon", "__awaitFiber", "cede", "__sleepForNanos"
    , "__currentFiberId", "__fiberId" -- §18.1.10 fiber identity; kpf_current_fiber_id/kpf_fiber_id shims
    , "newPromise", "completePromise", "awaitPromiseExit"
    , "pollPromise", "isDonePromise" -- §18.11 non-blocking peek; kpf_poll_promise/kpf_is_done_promise shims
      -- §18.1.8 structured scopes + monitors (CPS do-kernel, Stage 3)
    , "newScope", "forkIn", "shutdownScope", "monitor", "awaitMonitor"
    ]

-- | Compile the reachable closure of @main@ to a C translation unit.
-- @ffiPrims@ are the additional primitive names the linked FFI runtime
-- implements (empty for the no-FFI build).  Returns @Left errs@ when any
-- reachable definition uses an unsupported construct (the caller renders
-- these as 'E_BACKEND_UNSUPPORTED'), or @Right csource@ on success. When
-- Perceus RC validation is enabled, the result also carries the R-path findings
-- so the IO driver can report them on both successful and failed builds.
generateC :: Bool -> CheckState -> GName -> Set Text -> Map GName ResolvedNativeSymbol -> Either ([BackendError], Maybe [Text]) (Text, Maybe [Text])
generateC rcEnabled cs mainG ffiPrims hostSyms =
  let evalCtx0 = EvalCtx (Globals (csGlobals cs)) (csMetas cs) False (csFacts cs)
      st0 =
        GenState
          { gsFresh = 0
          , gsStmts = []
          , gsEnv = "0"
          , gsParamLvals = []
          , gsParamBinders = []
          , gsParamOwns = []
          , gsTopFlatFrame = False
          , gsTop = []
          , gsProtos = []
          , gsEmitted = Set.singleton mainG
          , gsQueue = [mainG]
          , gsErrs = []
          , gsCur = mainG
          , gsGlobals = csGlobals cs
          , gsEvalCtx = evalCtx0
          , gsBodies = csCoreBodies cs
          , gsSuspenders = suspenderGlobalsWith (blockingHostGlobals hostSyms) evalCtx0 (csGlobals cs) (csCoreBodies cs)
          , gsOwnership = csOwnership cs
          , gsCurOwn = Nothing
          , gsPath = []
          , gsRcEnabled = rcEnabled
          , gsRcFindings = []
          , gsRcBranchVisited = Set.empty
          , gsCtors = csCtors cs
          , gsDatas = Map.keysSet (csDatas cs)
          , gsTraits = Map.keysSet (csTraits cs)
          , gsDeclSites = csDeclSites cs
          , gsPrims = Set.union basePrims ffiPrims
          , gsPrimUsed = Set.empty
          , gsHostSyms = hostSyms
          , gsHostUsed = Set.empty
          , gsBounceMemo = Map.empty
          , gsLoops = []
          , gsDefer = []
          , gsScopeDefers = []
          , gsDeferLabels = []
          , gsI64Escape = "*kovf = KRT2_SCALAR_OVERFLOW; return 0;"
          , gsCollectCtors = Set.empty
          , gsCollectVars = Set.empty
          }
      final = execState (drainQueue >> emitMain mainG) st0
      -- §18.1.17/§27.6/§34.3.3 Stage-4a backend legality: this native backend's
      -- KK_HANDLER runtime is ONE-SHOT (it omits `rt-multishot-effects`: no persistent
      -- copy-on-resume of a captured segment), so a reachable MULTI-SHOT effect
      -- operation is rejected at compile time rather than miscompiled to
      -- one-shot semantics.  The interpreter (the differential oracle) supports
      -- multi-shot, so this gate is backend-local — it does not fire under `run`.
      multishotErrs = multishotLegality cs (gsEmitted final)
      rcFindings = reverse (gsRcFindings final) ++ rcBranchSiteFindings final
      rcErrs = rcFindingErrors (gsRcEnabled final) mainG (Map.findWithDefault noSpan mainG (csDeclSites cs)) rcFindings
      mRcFindings = if gsRcEnabled final then Just rcFindings else Nothing
   in case reverse (gsErrs final) ++ multishotErrs ++ rcErrs of
        [] -> Right (assemble final, mRcFindings)
        errs -> Left (errs, mRcFindings)

rcBranchSiteFindings :: GenState -> [Text]
rcBranchSiteFindings st
  | not (gsRcEnabled st) = []
  | otherwise =
      [ rcUseSiteMiss
          g
          Nothing
          (reverse site)
          "branch drop site key was not visited by C codegen"
      | g <- Set.toList (gsEmitted st)
      , Just own <- [Map.lookup g (gsOwnership st)]
      , site <- Map.keys (oiBranchDropSites own)
      , (g, site) `Set.notMember` gsRcBranchVisited st
      ]

rcFindingErrors :: Bool -> GName -> Span -> [Text] -> [BackendError]
rcFindingErrors False _ _ _ = []
rcFindingErrors True _ _ [] = []
rcFindingErrors True mainG sp findings =
  [ backendUnsupported
      mainG
      sp
        "Perceus RC R-path ownership lookup"
        ( "Perceus RC validation found "
            <> T.pack (show (length findings))
            <> " ownership side-table path miss(es); S2.3 validation requires zero so a path drift cannot silently suppress dup/drop decisions. First misses: "
            <> T.intercalate " | " (take 5 findings)
        )
  ]

-- | Backend legality (§34.3.3): a reachable @__EffOp@ node naming a multi-shot
-- operation is rejected, because the one-shot KK_HANDLER runtime cannot persist
-- a captured resumption.  Scans the bodies of the globals actually emitted
-- (the reachable closure of @main@) for @CCtor __EffOp [_, opName, …]@.  Shared
-- by the C and LLVM backends (both link the one-shot kappart2 runtime).
multishotLegality :: CheckState -> Set GName -> [BackendError]
multishotLegality cs emitted
  | Set.null multi = []
  | otherwise =
      [ backendFeatureMissing g (Map.findWithDefault noSpan g (csDeclSites cs)) "multi-shot effect operation"
          ( "the operation '" <> opn
              <> "' declares a multi-shot resumption (quantity ω / 1+), which requires the 'rt-multishot-effects' runtime capability the native backend does not advertise; declare it one-shot (quantity 1, the default) to resume at most once (§18.1.17, §27.6, §34.3.3)" )
      | g <- Set.toList emitted
      , Just body <- [Map.lookup g (csCoreBodies cs)]
      , opn <- Set.toList (termMultishotOps multi body)
      ]
  where
    multi = csMultishotOps cs

-- | The multi-shot operation names a term performs (an @__EffOp@ ctor whose
-- second field is a string literal in the multi-shot set).
termMultishotOps :: Set Text -> Term -> Set Text
termMultishotOps multi = go
  where
    go t = case t of
      CCtor g _ (_ : CLit (LitStr opn) : _)
        | g == Builtins.prelEffOp, opn `Set.member` multi ->
            Set.insert opn (Set.unions (map go (subterms t)))
      _ -> Set.unions (map go (subterms t))
    subterms t = case t of
      CLam _ _ _ b -> [b]
      CPi _ _ _ _ a b -> [a, b]
      CApp _ a b -> [a, b]
      CCtor _ mty as -> maybe [] pure mty ++ as
      CMatch s mty alts ->
        [s] ++ maybe [] pure mty
          ++ concat [maybe [] pure (caGuard a) ++ [caBody a] | a <- alts]
      CRecordT fs -> map snd fs
      CRecordV fs -> map snd fs
      CProj e _ -> [e]
      CProjAt e _ _ -> [e]
      CVariantT ts -> ts
      CLet _ _ ty rhs b -> [ty, rhs, b]
      CLetRec _ _ ty rhs b -> [ty, rhs, b]
      _ -> []

-- | Emit globals until the work queue is empty.
drainQueue :: Gen ()
drainQueue = do
  q <- gets gsQueue
  case q of
    [] -> pure ()
    (g : rest) -> do
      modify' $ \st -> st {gsQueue = rest}
      emitGlobal g
      drainQueue

-- | Emit one global's accessor function (memoised so recursion and CAF
-- sharing terminate and are evaluated once).
emitGlobal :: GName -> Gen ()
emitGlobal g = do
  modify' $ \st -> st {gsCur = g}
  bodies <- gets gsBodies
  let ident = cGlobIdent g
  modify' $ \st -> st {gsProtos = ("static KValue *" <> ident <> "(void);") : gsProtos st}
  -- A global reaches here only after compileGlob has ruled out a primitive,
  -- a host intrinsic, and a constructor, so a missing core body means a
  -- type-level / opaque / type-alias reference (e.g. `type Int = Integer`,
  -- or an opaque builtin type used as a value).  These are computationally
  -- erased (§12.2, §31.2) — their accessor yields the unit placeholder, the
  -- same inert value the interpreter never inspects — so an accepted program
  -- that mentions such a name compiles rather than being refused.  (Trait
  -- dictionaries and derived projections DO have recorded core bodies via
  -- recordCoreBody, so they take the Just branch below.)
  case Map.lookup g bodies of
    Nothing -> do
      -- Erase to the unit placeholder ONLY for a genuinely type-level / opaque
      -- global (a data\/trait name or a sort-typed builtin like @Integer@).  A
      -- real value-typed global with no recorded core body is NOT erasable —
      -- silently substituting unit would miscompile it (e.g. a top-level
      -- prefixed binding before recordCoreBody covered it).  Such a case is a
      -- backend gap, surfaced honestly rather than mis-lowered.
      typeLevel <- isTypeGlob g
      placeholder <-
        if typeLevel
          then pure "kunit()"
          else
            unsupported "definition"
              ( "'" <> gKey g <> "' has no recorded core body and is not a "
                  <> "type-level global, so it cannot be lowered (no-core-body)"
              )
      (stmts, _) <- captured "0" (pure ())
      finishGlobal ident stmts placeholder
    Just tm -> do
      -- A global whose body is a type-level / staging term (a `Type`-typed
      -- or `Syntax`-typed definition) is computationally erased (§12.2,
      -- §31.2): its accessor yields the unit placeholder, exactly as the
      -- interpreter's value for it is never inspected at runtime.  This is
      -- the by-name counterpart of the erasure that 'compileErasableArg'
      -- applies to inline type-level/quote arguments.
      --
      -- ALSO erase a definition whose RESULT TYPE is a RuntimeErased proof — a
      -- propositional equality or h-prop evidence (e.g. the prelude lemmas
      -- 'isPropEq'/'unsafeAssertProof'/'cong', reached via lawful-by-default
      -- 'Monoid').  Their bodies are the ADMIT primitives '__eqProof' /
      -- '__unsafeAssertProof' the native runtime does not implement; the proof
      -- is runtime-irrelevant (§12.2/§31.2/§14.4) so its accessor is the unit
      -- placeholder and its body is NOT compiled — keeping those primitives off
      -- the reachable native closure.  See 'resultIsProofP'.
      proof <- resultIsProof g
      erasable <- (proof ||) <$> isErasableArg tm
      if erasable
        then do
          (stmts, _) <- captured "0" (pure ())
          finishGlobal ident stmts "kunit()"
        else case funcArity tm of
          -- A function global is lowered to a worker (a loop, so a tail
          -- self-call runs in constant C stack) plus a curried closure for
          -- partial application and first-class use.
          (n, inner) | n >= 1 -> compileFunctionGlobal g n inner
          _ -> do
            -- Perceus RC S2.1: a CAF body sits at the structural root (empty path).
            own <- requireOwnInfo g
            (stmts, e) <- withBodyOwn own [] (captured "0" (compile tm))
            finishGlobal ident stmts e

-- | The leading-lambda arity of a term and the body beneath those binders.
funcArity :: Term -> (Int, Term)
funcArity = go 0
  where
    go !n (CLam _ _ _ b) = go (n + 1) b
    go !n t = (n, t)

-- | Does this worker body create a heap value that captures the enclosing
-- environment BY REFERENCE (a closure\/thunk\/do-action\/recursive let)?  If
-- so, the QW2 in-place parameter-cell update is UNSAFE: such a value can
-- escape one loop iteration (returned, consed into a list, deferred, …) and a
-- later @cell->val =@ mutation would overwrite the snapshot it must observe,
-- diverging from the interpreter (which evaluates each recursive call in a
-- fresh environment).  When this holds the worker rebuilds the parameter env
-- each iteration instead (the pre-QW2 behaviour, correct for escaping
-- closures).  Conservative: ANY such construct anywhere in the body disables
-- the in-place loop, even if that particular closure does not actually escape.
bodyCapturesEnv :: Term -> Bool
bodyCapturesEnv = go
  where
    go t = case t of
      CLam {} -> True -- kclo(fn, env)
      CLetRec {} -> True -- recursive closure captures the binder cell
      CDo {} -> True -- kio(fn, env)
      CThunkE {} -> True -- kthunk(fn, env, 0)  (Delay)
      CLazyE {} -> True -- kthunk(fn, env, 1)  (Memo)
      CQuote {} -> True -- conservative (erased, but never in a hot worker)
      -- P0-B: a saturated eta-expanded constructor application lowers to a
      -- direct 'kctor' (no 'kclo' over the env — see 'etaCtorApp'), so it
      -- captures its field VALUES, not the env, exactly like a 'CCtor'.
      -- Look through the eta lambdas to the real fields so this no longer
      -- forces the per-iteration env rebuild.
      CApp {} | Just (_, ctorArgs) <- etaCtorApp t -> any go ctorArgs
      CApp _ f a -> go f || go a
      CCtor _ _ args -> any go args
      CMatch s _ alts -> go s || any goAlt alts
      CProj e _ -> go e
      CProjAt e _ _ -> go e
      CInject _ e -> go e
      CForceE e -> go e
      CSealE _ e -> go e
      CLet _ _ ty rhs body -> go ty || go rhs || go body
      CIf c th el -> go c || go th || go el
      CRecordV fs -> any (go . snd) fs
      CRecordT fs -> any (go . snd) fs
      CVariantT ts -> any go ts
      CSigT _ e -> go e
      CPi _ _ _ _ a b -> go a || go b
      CVar {} -> False
      CGlob {} -> False
      CSort {} -> False
      CLit {} -> False
      CMeta {} -> False
    goAlt (CaseAlt _ mg body) = maybe False go mg || go body

-- | Lower a function global to: a worker @kw_…(p0,…,p{n-1})@ whose body is
-- a @while(1)@ loop (so a tail self-call reassigns the C parameters and
-- @continue@s instead of recursing in C — bounded C stack for tail
-- recursion), plus a curried arity-1 closure chain that collects the
-- arguments and calls the worker, returned by the accessor @kg_…()@.
--
-- Two modes (R2.3): when the body is capture-free ('bodyCapturesEnv' is
-- 'False'), the worker is FLAT — parameters are the C parameters read directly
-- (via 'gsParamLvals'), and @let@/@match@-bound locals are plain C locals
-- (R2.3-rest), so NO @KEnv@ is built at all.  When the body captures the env by
-- reference (a closure\/thunk\/do that can escape an iteration), the env is
-- REBUILT at the loop top from the reassigned C params (so each iteration's
-- escaping closures capture a distinct env, matching the interpreter) and
-- variables are read via @kvar@.
compileFunctionGlobal :: GName -> Int -> Term -> Gen ()
compileFunctionGlobal g n inner = do
  let ident = cGlobIdent g
      worker = "kw_" <> mangle (gKey g)
      ps = ["p" <> T.pack (show i) | i <- [0 .. n - 1]]
      inPlace = not (bodyCapturesEnv inner)
      -- R2.3 FLAT frame: a CAPTURE-FREE body reads parameters directly from the
      -- C parameters (no KEnv node, no kvar chain walk); a tail self-call
      -- reassigns the C params in place (like rebuild mode, but with no env to
      -- rebuild).  Strict subset of the QW2 in-place case.  A capture-free body
      -- can only bind via `let`/`match` (CLetRec/CDo/CLam are env-capturing, so
      -- excluded) — those push C locals onto 'gsParamLvals' (R2.3-rest), so no
      -- KEnv is needed for binder-bearing bodies either.
      flat = inPlace
      -- Two worker modes: FLAT (capture-free) reads params as direct C locals
      -- (gsParamLvals) with NO KEnv; REBUILD (capturing) rebuilds kw_env at the
      -- loop top each iteration and reads via kvar.  Both reassign the C params
      -- on a tail self-call (slots=ps) — so the in-place QW2 KEnv-cell mode is
      -- subsumed by FLAT (which keeps no KEnv at all).
      ti = TailInfo g n ps
      -- rebuild mode: rebuild kw_env at the loop top from the C params.
      envExpr = foldl (\acc p -> "kpush(" <> p <> ", " <> acc <> ")") "0" ps
      loopTopEnv
        | flat = [] -- FLAT: params are direct C locals, no KEnv
        | otherwise = ["    KEnv *kw_env = " <> envExpr <> "; (void)kw_env;"]
      paramDecls = T.intercalate ", " ["KValue *" <> p | p <- ps]
  -- In a flat worker, a CVar resolves to its C parameter (gsParamLvals), and a
  -- let/match binding prepends a C local; the mapping is reset for a capturing
  -- worker so CVar/binders fall back to kvar/kpush.  (A flat body has no
  -- env-capturing form, so a lifted closure can never read it.)
  -- Perceus RC S2.1: enter the body-own scope. The analysis walks the WHOLE body
  -- including the @n@ leading 'CLam's the worker frame just stripped, so @inner@
  -- sits at the structural path @replicate n lamBodyPos@ from the body root — seed
  -- 'gsPath' with that prefix so the walk-and-lookup keys land at the right offset.
  own <- requireOwnInfo g
  saved <- gets gsParamLvals
  savedBinders <- gets gsParamBinders
  savedOwns <- gets gsParamOwns
  savedTopFlat <- gets gsTopFlatFrame
  let paramBids = reverse [BinderId g (replicate j P.lamBodyPos) | j <- [0 .. n - 1]]
      -- The binder table says which parameters are droppable in the source
      -- contract, but the worker ABI has not yet normalized every incoming
      -- actual to an owned reference. Keep the BinderIds for exact resolution and
      -- future caller-transfer completion; do not let S2.3d drop params from the
      -- callee frame yet.
      paramOwns = replicate n False
  modify' $ \st ->
    st
      { gsParamLvals = if flat then reverse ps else []
      , gsParamBinders = if flat then map Just paramBids else []
      , gsParamOwns = if flat then paramOwns else []
      , gsTopFlatFrame = flat
      }
  (bodyStmts, ()) <-
    withBodyOwn own (replicate n P.lamBodyPos) $
      captured "kw_env" (consume (SinkTail ti) inner)
  modify' $ \st ->
    st
      { gsParamLvals = saved
      , gsParamBinders = savedBinders
      , gsParamOwns = savedOwns
      , gsTopFlatFrame = savedTopFlat
      }
  let workerFn =
        T.unlines $
          ["static KValue *" <> worker <> "(" <> paramDecls <> ") {"]
            ++ ["  while (1) {"]
            ++ loopTopEnv
            ++ map ("    " <>) bodyStmts
            ++ [ "  }"
               , "}"
               ]
  emitTop ("static KValue *" <> worker <> "(" <> paramDecls <> ");") workerFn
  -- curried closure chain clo_0 … clo_{n-1}; clo_{n-1} calls the worker.
  cloNames <- mapM (\i -> freshFn ("kclo" <> T.pack (show i) <> "_")) [0 .. n - 1]
  forM_ (zip [0 ..] cloNames) $ \(i, nm) -> do
    let body
          | i < n - 1 =
              "  return kclo(" <> (cloNames !! (i + 1)) <> ", kpush(arg, cenv));"
          | otherwise =
              -- saturating call: p{n-1} = arg; p_j = kvar(cenv, n-2-j)
              let collected = [ "kvar(cenv, " <> T.pack (show (n - 2 - j)) <> ")" | j <- [0 .. n - 2] ]
                  callArgs = T.intercalate ", " (collected ++ ["arg"])
               in "  return " <> worker <> "(" <> callArgs <> ");"
        fn =
          T.unlines
            [ "static KValue *" <> nm <> "(KEnv *cenv, KValue *arg) {"
            , "  (void)cenv; (void)arg;"
            , body
            , "}"
            ]
    emitTop ("static KValue *" <> nm <> "(KEnv *, KValue *);") fn
  -- accessor: the memoised curried closure value (its forward declaration
  -- was already emitted by 'emitGlobal').
  (cacheHit, publishFresh) <- globalCacheOwnershipPlan
  let accessor =
        T.unlines
          ( [ "static KValue *" <> ident <> "(void) {"
            , "  static _Atomic(KValue *) cache = NULL;"
            , "  KValue *cached = atomic_load_explicit(&cache, memory_order_acquire);"
            , cacheHit
            , "  KValue *fresh = kclo(" <> head cloNames <> ", 0);"
            ]
              ++ publishFresh
              ++ [ "}" ]
          )
  modify' $ \st -> st {gsTop = accessor : gsTop st}
  -- LR1/R2.2: if g is a monomorphic first-order scalar function (Int and/or
  -- Double params + scalar result) with a scalar-expressible body, ALSO emit
  -- the typed unboxed worker beside the boxed kw_g.
  mplan <- scalarPlan g
  case mplan of
    Just (_, pks, ret, scalarInner) -> compileScalarWorker g pks ret scalarInner
    Nothing -> pure ()

-- ── LR1/R2.2: typed unboxed scalar workers (int64 / double) ──────────────
-- A first-order monomorphic SCALAR function — parameters and result each
-- Int/Nat/Integer (→ @int64_t@) or Float/Double (→ @double@), read from
-- @gdType@ — with a scalar-EXPRESSIBLE body gets an auxiliary unboxed worker
-- beside the boxed @kw_g@: typed scalar params + a while-loop for tail
-- self-calls (no @KEnv@/@kvar@/box per iteration).  A saturated direct call
-- (compileScalarCall) unboxes each arg BY ITS KIND and, on a wrong-tag arg
-- (kunbox_i64/kunbox_dbl escape) OR an int64 overflow, sets @kovf@ and re-runs
-- the BOXED worker from the ORIGINAL boxed args — so the boxed/GMP path is
-- always the reference result (the unbox tag-check is the soundness net: even
-- a mis-derived kind escapes to boxed, never miscompiles).  @kw_g@, the
-- closure chain, and the accessor are unchanged; the unboxed worker is reached
-- only from the saturated fast path.  Body grammar (conservative allowlist;
-- else ⇒ boxed-only): a scalar literal, a param/var, the int arith prims
-- (add/sub/mul/div/mod/neg)Int (overflow-escaped), the double arith prims
-- (add/sub/mul/div/neg)Double (plain IEEE, no escape — wraps to ±inf/NaN like
-- the boxed prim), @intToDouble@ (an int→double cast), the safe compares
-- (eq/lt/le)Int and ltDouble/floatEq ONLY as an @if@ condition, @if@ in tail
-- position, and SATURATED self-calls.  (CLet and @if@ in value position are
-- deferred — they make a body ineligible, never miscompiled.  @eqDouble@ is
-- EXCLUDED: it is §6.1.3 raw-bit equality, not C @==@; @leDouble@ has no
-- runtime prim.)

-- | The scalar kind of a worker parameter / result: an unboxed @int64_t@ or
-- @double@.
data ScalarKind = KInt64 | KDouble deriving (Eq)

-- | The C type for a scalar kind.
cScalarTy :: ScalarKind -> Text
cScalarTy KInt64 = "int64_t"
cScalarTy KDouble = "double"

-- | Box a raw scalar C value back into a @KValue@ by its kind.
boxScalar :: ScalarKind -> Text -> Text
boxScalar KInt64 e = "kint(" <> e <> ")"
boxScalar KDouble e = "kdbl(" <> e <> ")"

-- | Unbox a @KValue@ argument to a raw scalar by its kind, escaping (setting
-- @ovf@) on a wrong tag — the soundness net for the typed worker.
unboxScalar :: ScalarKind -> Text -> Text -> Text
unboxScalar KInt64 box ovf = "kunbox_i64(" <> box <> ", &" <> ovf <> ")"
unboxScalar KDouble box ovf = "kunbox_dbl(" <> box <> ", &" <> ovf <> ")"

-- | R2.4: a worker parameter slot is either an unboxed scalar (int64/double) or
-- a boxed @KValue *@ passed through verbatim (a record/ADT/etc. param that is
-- not scalar but whose scalar FIELDS may be read+coerced).  An all-@PScalar@
-- worker is the LR1/R2.2 case (byte-identical @kwi_@/@kwd_@ output); a worker
-- with any @PBoxed@ slot is a MIXED worker (@kwm_@).
data ParamKind = PScalar !ScalarKind | PBoxed deriving (Eq)

-- | The C type for a parameter slot.
cParamTy :: ParamKind -> Text
cParamTy (PScalar k) = cScalarTy k
cParamTy PBoxed = "KValue *"

-- | The scalar kind of a slot, or 'Nothing' for a boxed slot.
paramSK :: ParamKind -> Maybe ScalarKind
paramSK (PScalar k) = Just k
paramSK PBoxed = Nothing

-- | A scalar arith prim, with its (result kind, argument kinds).  @intToDouble@
-- is the one cross-kind coercion (int → double, emitted as a C cast).
arithPrim :: Text -> Maybe (ScalarKind, [ScalarKind])
arithPrim = \case
  "addInt" -> Just (KInt64, [KInt64, KInt64])
  "subInt" -> Just (KInt64, [KInt64, KInt64])
  "mulInt" -> Just (KInt64, [KInt64, KInt64])
  "divInt" -> Just (KInt64, [KInt64, KInt64])
  "modInt" -> Just (KInt64, [KInt64, KInt64])
  "negInt" -> Just (KInt64, [KInt64])
  "addDouble" -> Just (KDouble, [KDouble, KDouble])
  "subDouble" -> Just (KDouble, [KDouble, KDouble])
  "mulDouble" -> Just (KDouble, [KDouble, KDouble])
  "divDouble" -> Just (KDouble, [KDouble, KDouble])
  "negDouble" -> Just (KDouble, [KDouble])
  "intToDouble" -> Just (KDouble, [KInt64])
  _ -> Nothing

-- | A scalar comparison usable as an @if@ condition: (C operator, operand
-- kind).  ONLY comparisons whose C operator EXACTLY matches the runtime prim:
-- the int compares, @ltDouble@ (IEEE @<@) and @floatEq@ (IEEE @==@).
-- @eqDouble@ is excluded — §6.1.3 raw-bit equality differs from C @==@ on NaN
-- and signed zero; @leDouble@ has no runtime prim to mirror.
cmpPrim :: Text -> Maybe (Text, ScalarKind)
cmpPrim = \case
  "eqInt" -> Just ("==", KInt64)
  "ltInt" -> Just ("<", KInt64)
  "leInt" -> Just ("<=", KInt64)
  "ltDouble" -> Just ("<", KDouble)
  "floatEq" -> Just ("==", KDouble)
  _ -> Nothing

-- | A saturated self-call: spine head is the worker's own global @self@ with
-- exactly @n@ explicit args (FULL GName equality, like 'selfTailArgs').
lr1SelfArgs :: GName -> Int -> Term -> Maybe [Term]
lr1SelfArgs self n term = case spineOf term of
  (CGlob g, sargs)
    | g == self, expl <- [a | (Expl, a) <- sargs], length expl == n -> Just expl
  _ -> Nothing

andM :: [Gen Bool] -> Gen Bool
andM = foldr (\m acc -> do b <- m; if b then acc else pure False) (pure True)

orM :: [Gen Bool] -> Gen Bool
orM = foldr (\m acc -> do b <- m; if b then pure True else acc) (pure False)

-- | Strip leading lambdas, recording each binder's (icity, quantity).
stripLamsQ :: Term -> ([(Icit, Q)], Term)
stripLamsQ = go []
  where
    go acc (CLam ic q _ b) = go ((ic, q) : acc) b
    go acc t = (reverse acc, t)

-- | The per-parameter scalar kinds and result kind of @g@ IF it is eligible
-- for an unboxed worker: a recorded body of @n@ explicit relevant binders, a
-- scalar type telescope of exactly @n@ runtime params + a scalar result, and a
-- scalar-expressible body.  @Nothing@ ⇒ boxed-only (never a miscompile).
-- | §6/§7 Stage 1.5 — the SUSPENDABILITY WITNESS that gates the unboxed scalar
-- worker.  A scalar worker keeps its values in raw C locals (@double@/@int64_t@);
-- those locals are absent from the @KEnv@ chain and the continuation @f->k@, so a
-- fiber park (await/fork/race/timeout/atomically/STM retry) at any point where a
-- raw scalar is live would LOSE it on resume (CPS-DESIGN R5) — a silent
-- miscompile, no crash.  So a worker may be emitted ONLY for a body that PROVABLY
-- does not may-suspend.  Returns @True@ if the body MAY suspend; the witness
-- ERRS TOWARD may-suspend (unknown ⇒ True ⇒ refuse the worker ⇒ stay boxed):
--
--   * a spine head that is a suspending primitive ('isSuspendingPrim') or a
--     global in the transitive §3.3 suspender closure ('gsSuspenders');
--   * an opaque higher-order call whose spine head is a local/param 'CVar'
--     (may suspend depending on the value passed — §6 "effect-polymorphic /
--     opaque-higher-order ⇒ may-suspend");
--
-- Today the arithmetic-only body grammar ('scalarEligTail'/'scalarKindOf')
-- already makes a scalar body suspension-free *implicitly* (no admitted form
-- is an IO/suspending op, and a non-scalar result kind already rejects every
-- @UIO a@ function).  This witness makes that property EXPLICIT and INDEPENDENT
-- so it survives the Stage-2a-pre widening to @let@/@match@ (which CAN carry a
-- suspending sub-term) and is the named soundness gate of §7 Stage 1.5 — not an
-- emergent accident of the allowlist.  It walks the WHOLE body (not just the
-- tail spine), recursing into @if@ branches and every prim/self-call argument,
-- because a suspension anywhere a raw scalar is live is unsound — not only in
-- tail position.
scalarBodyMaySuspend :: Set GName -> Term -> Bool
scalarBodyMaySuspend susp = go
  where
    -- a call's spine head decides suspendability for this node; the arguments
    -- are then walked too (a suspending op can hide in an argument position).
    -- Only an APPLICATION counts as a call here — a bare 'CVar'/'CGlob' LEAF
    -- (a value read, not an invocation) cannot itself park, so it is never
    -- flagged (else every scalar local read would falsely read as may-suspend).
    headSusp t = case t of
      CApp {} -> case fst (spineOf t) of
        CGlob h -> isSuspendingPrim h || h `Set.member` susp
        CVar _ -> True -- opaque higher-order call: may suspend (conservative)
        _ -> False
      _ -> False
    go t =
      headSusp t || case t of
        CIf c th el -> go c || go th || go el
        CApp _ a b -> go a || go b
        CMatch s _ alts -> go s || any (\a -> maybe False go (caGuard a) || go (caBody a)) alts
        CLet _ _ _ rhs body -> go rhs || go body
        CLetRec _ _ _ rhs body -> go rhs || go body
        CDo _ _ -> True -- a do-block is an IO action: conservatively may-suspend
        CCtor _ _ as -> any go as
        CSealE _ e -> go e
        CSigT _ e -> go e
        CForceE e -> go e
        CThunkE e -> go e
        CLazyE e -> go e
        CInject _ e -> go e
        CProj e _ -> go e
        CProjAt e _ _ -> go e
        _ -> False

scalarPlan :: GName -> Gen (Maybe ([Bool], [ParamKind], ScalarKind, Term))
scalarPlan g = do
  bodies <- gets gsBodies
  susp <- gets gsSuspenders
  case Map.lookup g bodies of
    Nothing -> pure Nothing
    Just body -> do
      let (binders, _) = stripLamsQ body
          n = length binders
      -- all binders explicit + relevant: an implicit/erased binder is passed
      -- kunit() (compileErasableArg), which a scalar worker must never read.
      if n >= 1 && all (\(ic, q) -> ic == Expl && q /= Q0) binders
        then do
          mkinds <- typeScalarKinds g n
          case mkinds of
            -- require at least one unboxed scalar param (else there is nothing
            -- to win — an all-boxed body stays on the boxed/flat path).
            Just (mask, pks, ret) | any (/= PBoxed) pks -> do
              -- §7 Stage 1.5 SOUNDNESS GATE (before the body grammar check): a
              -- worker whose body may suspend would lose its raw-scalar C locals
              -- across a park (§6).  Refuse it (→ boxed) — never miscompile.
              -- Gates on BOTH the global's own transitive suspender membership
              -- (g ∈ gsSuspenders) and a per-body walk for an inlined/opaque
              -- suspending sub-term, so it stays sound once locals widen.
              case dropStaticPrefixLams mask (dropStaticGlobalPrefixArgs g mask body) of
                Nothing -> pure Nothing
                Just scalarBody -> do
                  let (_, scalarInner) = stripLamsQ scalarBody
                  ok <- scalarEligTail g pks (reverse pks) ret scalarInner
                  let mayParK = g `Set.member` susp || scalarBodyMaySuspend susp scalarInner
                  pure (if ok && not mayParK then Just (mask, pks, ret, scalarInner) else Nothing)
            _ -> pure Nothing
        else pure Nothing

-- | Read @g@'s per-parameter kinds (unboxed scalar or boxed) and its (scalar)
-- result kind from its elaborated type (quoted to a Term Pi telescope).  A
-- non-scalar param domain is 'PBoxed' (R2.4 mixed worker — kept boxed,
-- passed through); the RESULT must be scalar (a boxed-result worker is not
-- eligible in this slice).  The count-match against @n@ (the body's structural
-- binder count) is a HARD guard: a disagreement (point-free style, an
-- unfoldable type alias, a function-typed result) yields @Nothing@, so a kind
-- is never assigned to the wrong binder.
typeScalarKinds :: GName -> Int -> Gen (Maybe ([Bool], [ParamKind], ScalarKind))
typeScalarKinds g n = do
  globals <- gets gsGlobals
  ctx <- gets gsEvalCtx
  pure $ case Map.lookup g globals of
    Nothing -> Nothing
    Just gd -> do
      -- KBackendIR Stage 3: rep selection is 'Repr.repSelect' — the single
      -- authority that walks the type telescope and classifies every relevant
      -- explicit param + the result as int/double/boxed.  This backend's
      -- @ParamKind@/@ScalarKind@ are just the projection of that 'Rep' plan:
      -- the per-param 'Rep' becomes a 'PScalar'/'PBoxed' slot, and the RESULT
      -- 'Rep' must be a scalar (a boxed-result worker is not eligible in this
      -- slice — so a non-scalar result rep yields @Nothing@).
      mask <- Repr.runtimeParamMask ctx (gdType gd)
      (paramReps, retRep) <- Repr.repSelect ctx (gdType gd)
      ret <- repScalarKind retRep
      let pks = map paramRepKind paramReps
      if length mask == n && length pks == length (filter id mask)
        then Just (mask, pks, ret)
        else Nothing
  where
    -- A param slot is an unboxed scalar (int/double) or a boxed pass-through
    -- (R2.4 mixed worker) for any non-scalar rep.
    paramRepKind r = maybe PBoxed PScalar (repScalarKind r)

-- | The unboxed scalar kind of a 'Repr.Rep', or 'Nothing' for a rep that has no
-- unboxed scalar representation (boxed / immediate-ctor).  This is the
-- backend-local projection of the shared rep classification onto this backend's
-- two-element @ScalarKind@ (the only reps it unboxes today).
repScalarKind :: Repr.Rep -> Maybe ScalarKind
repScalarKind = \case
  Repr.RepInt -> Just KInt64
  Repr.RepDouble -> Just KDouble
  _ -> Nothing

-- | For a global head @g@, the per-spine-position erasure flags read from its
-- elaborated type's Pi telescope: @True@ at a binder whose quantity is 'Q0'
-- (computationally erased, §31.2), @False@ otherwise.  The list runs in
-- telescope order, which 'spineOf' lists arguments in (binder @k@ ↔ spine
-- position @k@); spine positions past the telescope (a result that is itself a
-- function value, applied further) get @False@.
--
-- This is the FIX for the interp-vs-native divergence on @sequence@ /
-- @sequence_@ / @for_@ / @traverse@ over IO: an ERASED type argument that is a
-- type-level APPLICATION @f a@ (a 'CApp' whose head is a type VARIABLE) is
-- otherwise lowered as a real runtime @kapp(kvar f, kvar a)@ over two
-- unit-valued (erased) slots, because the purely SYNTACTIC 'isErasableArg'
-- only inspects the spine head ('CVar' → @False@).  The interpreter keeps type
-- arguments as applicable values so it never crashes; the C/LLVM backends
-- crash with @kapp: applying a non-function value@.  Erasing by the binder's
-- 'Q0' QUANTITY — the elaborator's own irrelevance verdict — is syntax-blind
-- and so erases the application form too.  Unlike 'typeScalarKinds' (explicit
-- value binders only), this walks the WHOLE telescope, since an erased
-- argument can sit at an implicit OR explicit position.
-- The pure core ('erasedSpinePositionsP' / 'eraseQ0ArgsP') is exported so the
-- LLVM backend ("Kappa.Backend.LLVM") shares the SAME erasure verdict with its
-- own 'gsGlobals' / 'gsEvalCtx'.

-- | The pure spine-erasure analysis (see 'erasedSpinePositions').
-- FAIL-SAFE: an unknown global, or a 'gdType' that does not 'force' to a 'VPi'
-- telescope (an unsolved-meta/thunk head), yields @[]@ — i.e. nothing is flagged.
-- That can only UNDER-erase (miss a position), never over-erase: a missed
-- type-application position reverts to the original @kapp(unit,unit)@ crash, but
-- a dictionary or runtime value is never wrongly dropped.
erasedSpinePositionsP :: Map GName GlobalDef -> EvalCtx -> GName -> [Bool]
erasedSpinePositionsP globals ctx g =
  case Map.lookup g globals of
    Nothing -> []
    Just gd -> walk 0 (gdType gd)
  where
    walk lvl ty =
      case force ctx ty of
        VPi _ q _ _ dom clo ->
          (q == Q0 || isKindDomain lvl dom) : walk (lvl + 1) (closApply lvl clo)
        _ -> []
    closApply lvl (Closure env body) = eval ctx (VRigid lvl [] : env) body
    -- A parameter whose DOMAIN is a kind (@Type@, or @A -> … -> Type@) is a type
    -- or type constructor: it is RuntimeErased (Spec §1.1.1 — types carry no
    -- runtime representation; §11.4 — there is no typecase), so it is erasable
    -- REGARDLESS of its quantity (a type argument need not be 'Q0').  This is the
    -- broader half of the verdict: 'Q0' alone caught the type args that happened
    -- to be quantity-zero, but a non-'Q0' type *application* @f a@ would still
    -- crash as @kapp(unit,unit)@.  Crucially this NEVER erases a dictionary: a
    -- dict's domain is a trait type @C a : Type@ — an inhabitant of a kind, not a
    -- kind — so 'isKindDomain' is False for it (Spec §14.4: @IsTrait@ does not
    -- imply @RuntimeErased@; a method projection is runtime-relevant).  Proofs of
    -- a 'RuntimeErased'/'IsProp' proposition are likewise erasable, but at a
    -- non-'Q0' position that needs the elaborator's IsProp evidence (not re-derived
    -- here); the common Q0 proof position is already covered above.  Mirrors
    -- 'Kappa.Check.isKindLike'.
    isKindDomain lvl v =
      case force ctx v of
        VSort _ -> True
        VPi _ _ _ _ _ clo -> isKindDomain (lvl + 1) (closApply lvl clo)
        _ -> False

-- | Rewrite a global-headed application @g a0 a1 …@ so each argument at an
-- ERASED (Q0 OR type-level/kind-domain) telescope position becomes a 'CSort'
-- placeholder — see
-- 'erasedSpinePositions' for the why.  The icities are preserved (an erased arg
-- can be implicit or explicit); the placeholder is then erased to @kunit()@ by
-- the existing 'compileErasableArg' path, with no new threading.  Positions past
-- the telescope keep their original term.
eraseQ0Args :: GName -> Term -> Gen Term
eraseQ0Args g term = do
  globals <- gets gsGlobals
  ctx <- gets gsEvalCtx
  pure (eraseQ0ArgsP globals ctx g term)

-- | The pure spine rewrite (see 'eraseQ0Args').
eraseQ0ArgsP :: Map GName GlobalDef -> EvalCtx -> GName -> Term -> Term
eraseQ0ArgsP globals ctx g term =
  let flags = erasedSpinePositionsP globals ctx g
      (hd, sargs) = spineOf term
      go _ [] = []
      go (er : ers) ((ic, a) : rest) = (ic, if er then CSort 0 else a) : go ers rest
      go [] rest = rest -- spine longer than the telescope: leave the tail as-is
      sargs' = go flags sargs
   in foldl (\f (ic, a) -> CApp ic f a) hd sargs'

-- | Is @g@'s RESULT type a RuntimeErased PROOF — a propositional equality
-- (@(=) x y@ / the §21.6 @CoreEq@), or h-prop evidence (@IsProp@ / @IsSubsingleton@
-- / @IsSet@ / @IsContr@ / @IsGroupoid@)?  Such a definition is computationally
-- irrelevant (Spec §12.2/§31.2/§14.4: a proof of an h-prop carries no runtime
-- content), so its accessor is the unit placeholder and its BODY is NOT compiled.
--
-- WHY this exists: 'Monoid' is now lawful-by-default — every instance carries the
-- equational laws @appendAssoc@/@append*Identity@, whose discharge reaches the
-- prelude proof lemmas @isPropEq@/@unsafeAssertProof@/@cong@, whose bodies are the
-- ADMIT primitives @__eqProof@/@__unsafeAssertProof@ the native runtime does not
-- implement.  Erasing the proof-typed lemmas keeps those primitives off the
-- reachable native closure.  This is the by-RESULT-type counterpart of the
-- by-ARGUMENT erasure 'erasedSpinePositionsP' applies (a 'Q0'/kind-domain proof
-- ARGUMENT is already erased; a proof RESULT was not).
--
-- SOUNDNESS: erases ONLY genuine proofs.  The result-head set is exactly the
-- prelude's propositional-equality and h-prop marker traits — none of which has a
-- runtime-relevant inhabitant (their members are all erased proofs, §14.4).  A def
-- whose result is a real runtime value (an @Int@, a dictionary, an @IO@ action …)
-- has a non-proof head and is left untouched.  FAIL-SAFE like
-- 'erasedSpinePositionsP': an unknown global / a 'gdType' that does not 'force' to
-- a recognisable telescope yields @False@ (compile for real — never erase on doubt).
--
-- The @forall (@0 p : Type). (@_ : IsProp p) -> … -> p@ shape (i.e.
-- 'unsafeAssertProof') has a result that is a bound VARIABLE @p@, not a proof head;
-- it is recognised by the @IsProp p@ / @IsSubsingleton p@ HYPOTHESIS that pins the
-- SAME binder as the result (compared by absolute de Bruijn level).
--
-- Exported so "Kappa.Backend.LLVM" shares the identical verdict (mirrors
-- 'erasedSpinePositionsP').
resultIsProofP :: Map GName GlobalDef -> EvalCtx -> GName -> Bool
resultIsProofP globals ctx g =
  case Map.lookup g globals of
    Nothing -> False
    Just gd -> walk 0 [] (quote ctx 0 (gdType gd))
  where
    -- @lvl@ is the telescope DEPTH so far (number of binders in scope = the
    -- absolute de Bruijn level of the next binder).  @propLvls@ collects the
    -- absolute levels of binders pinned by an @IsProp _@ / @IsSubsingleton _@
    -- hypothesis somewhere earlier in the telescope.
    walk lvl propLvls ty = case ty of
      CPi _ _ _ _ dom cod ->
        -- A domain @IsProp (CVar j)@ / @IsSubsingleton (CVar j)@ at depth @lvl@
        -- pins the binder at absolute level @lvl-1-j@ as proof-typed.
        let propLvls' = case hypProofVarLevel lvl dom of
              Just l -> l : propLvls
              Nothing -> propLvls
         in walk (lvl + 1) propLvls' cod
      r -> resultIsProof' lvl propLvls r
    -- The result type @r@ sits at depth @lvl@.  It is a proof when its head is a
    -- propositional-equality / h-prop marker, OR it is a bound variable that a
    -- prior hypothesis pinned as proof-typed.
    resultIsProof' lvl propLvls r =
      case headGlob r of
        Just h | h `Set.member` proofHeads -> True
        _ -> case r of
          CVar i -> (lvl - 1 - i) `elem` propLvls
          _ -> False
    -- For a domain term at depth @lvl@, if it is @IsProp (CVar j)@ /
    -- @IsSubsingleton (CVar j)@ return the absolute level of the pinned binder.
    hypProofVarLevel lvl dom =
      case spineOf dom of
        (CGlob h, [(_, CVar j)])
          | h == Builtins.prelIsProp || h == Builtins.prelIsSubsingleton ->
              Just (lvl - 1 - j)
        _ -> Nothing
    -- The prelude's propositional-equality type and h-prop marker traits.  Every
    -- inhabitant of one of these is a RuntimeErased proof (§14.4) — no runtime
    -- content — so a definition producing one is computationally erased.
    proofHeads =
      Set.fromList
        [ Builtins.prelEqType
        , Builtins.prelIsProp
        , Builtins.prelIsSubsingleton
        , Builtins.prelIsSet
        , Builtins.gPrel "IsContr"
        , Builtins.gPrel "IsGroupoid"
        , Builtins.gPrel "CoreEq"
        ]

-- | 'resultIsProofP' in 'Gen' (this backend's monad), reading the shared
-- 'gsGlobals' / 'gsEvalCtx'.
resultIsProof :: GName -> Gen Bool
resultIsProof g = do
  globals <- gets gsGlobals
  ctx <- gets gsEvalCtx
  pure (resultIsProofP globals ctx g)

-- KBackendIR Stage 3: the head-type → scalar-representation discriminator is
-- 'Repr.scalarRep' / 'Repr.repSelect' (the shared rep table); this backend's
-- @ScalarKind@ is the @RepInt@/@RepDouble@ projection of it ('repScalarKind').
-- 'typeScalarKinds' consumes 'Repr.repSelect' directly, so the standalone
-- head-discriminator wrapper that used to live here is gone — its only caller
-- was the param/result classification now derived from the shared rep plan.

-- | Eligibility of a tail-position term against the worker's return kind: an
-- @if@ (safe-compare condition, eligible branches), a @let@ whose RHS is a
-- scalar (Int/Double) sub-expression (the binder is then in scope, scalar, for
-- the body — so a hot loop with a let temporary, e.g. mandelbrot's FMA
-- temporaries, stays scalar-eligible instead of boxing), a saturated self-call
-- (each arg checks against the corresponding PARAM kind), or a leaf value whose
-- kind equals the return kind.  @dks@ is the DE-BRUIJN-ORDERED local-kind
-- context (innermost binder first; initially @reverse pks@) — every let-binder
-- prepends to it (see 'varParamKind'); @pks@ stays the source-order PARAM kinds
-- for self-call arity ('lr1SelfArgs') and per-slot arg checking.
scalarEligTail :: GName -> [ParamKind] -> [ParamKind] -> ScalarKind -> Term -> Gen Bool
scalarEligTail g pks dks ret term = case term of
  CIf c t e -> andM [scalarEligCond g pks dks ret c, scalarEligTail g pks dks ret t, scalarEligTail g pks dks ret e]
  -- §let: a let-bound scalar keeps the body scalar-eligible.  The RHS must be a
  -- scalar value (Int/Double); its kind is prepended to @dks@ as a 'PScalar'
  -- slot so the body reads the binder at de Bruijn 0.  A non-scalar RHS makes
  -- the whole body ineligible (→ boxed), never miscompiled.  (CLetRec stays
  -- unhandled: a local fixpoint is not a scalar value.)
  CLet _ _ _ rhs body -> do
    mk <- scalarKindOf g pks dks ret rhs
    case mk of
      Just k -> scalarEligTail g pks (PScalar k : dks) ret body
      Nothing -> pure False
  _
    | Just args <- lr1SelfArgs g (length pks) term -> andM (zipWith (selfArgElig g pks dks ret) pks args)
    | otherwise -> scalarHasKind g pks dks ret ret term

-- | A self-call argument is eligible iff: for a scalar param slot, the arg is a
-- value of that scalar kind; for a boxed param slot, the arg is a PASS-THROUGH
-- of a boxed param (a bare @CVar@ of a boxed slot) — the only boxed value the
-- mixed worker can supply without unboxing/rebuilding (R2.4 slice).
selfArgElig :: GName -> [ParamKind] -> [ParamKind] -> ScalarKind -> ParamKind -> Term -> Gen Bool
selfArgElig g pks dks ret pk arg = case pk of
  PScalar k -> scalarHasKind g pks dks ret k arg
  -- any boxed CVar into a boxed slot is fine: source type-checking already
  -- guarantees the self-call arg's type matches the param, and the runtime
  -- representation of every boxed slot is the uniform @KValue *@.
  PBoxed -> pure $ case arg of
    CVar j -> varParamKind dks j == Just PBoxed
    _ -> False

-- | Is @term@ a FIXED-OFFSET projection of a BOXED param (@krec_at(boxed,i)@)?
-- Its boxed field value can be coerced to any scalar kind by a tag-checked
-- unbox (R2.4), so it is admissible in any scalar position.  ONLY 'CProjAt'
-- (the P0.4 closed-record fixed-offset form, which codegen lowers to
-- @krec_at@) qualifies; a name-based 'CProj' (open/sealed record, dict member,
-- tuple ≥10) is NOT handled by the coercion codegen, so it must stay
-- ineligible here (→ boxed worker) rather than reach the worker and escalate
-- on a valid program.
isBoxedProj :: [ParamKind] -> Term -> Bool
isBoxedProj dks term = case term of
  CProjAt (CVar j) _ _ -> varParamKind dks j == Just PBoxed
  _ -> False

-- | Does the value-position @term@ have scalar kind @k@?  A projection of a
-- boxed param is coercible to any @k@ (a tag-checked unbox at codegen).
scalarHasKind :: GName -> [ParamKind] -> [ParamKind] -> ScalarKind -> ScalarKind -> Term -> Gen Bool
scalarHasKind g pks dks ret k term
  | isBoxedProj dks term = pure True
  | otherwise = do
      mk <- scalarKindOf g pks dks ret term
      pure (mk == Just k)

-- | The scalar kind of a value-position expression, or @Nothing@ if it is not
-- scalar-expressible (every prim arg must match the prim's expected kind, so a
-- mixed-kind misuse such as @addInt acc n@ with @acc:Double@ is rejected, never
-- miscompiled).  A self-call's result is the worker's return kind.  A @let@
-- whose RHS is scalar binds a scalar binder for its body (so a value-position
-- @let@ — e.g. a nested FMA temporary — is scalar-expressible, not @Nothing@).
-- A bare @CVar@ of a BOXED param is NOT a scalar value (it is only usable as a
-- projection base — see 'isBoxedProj'), so it is @Nothing@ here.
scalarKindOf :: GName -> [ParamKind] -> [ParamKind] -> ScalarKind -> Term -> Gen (Maybe ScalarKind)
scalarKindOf g pks dks ret term = case term of
  CLit (LitInt m)
    | m >= toInteger (minBound :: Int) && m <= toInteger (maxBound :: Int) -> pure (Just KInt64)
    | otherwise -> pure Nothing
  CLit (LitDouble _) -> pure (Just KDouble)
  CVar i -> pure (varParamKind dks i >>= paramSK)
  CLet _ _ _ rhs body -> do
    mk <- scalarKindOf g pks dks ret rhs
    case mk of
      Just k -> scalarKindOf g pks (PScalar k : dks) ret body
      Nothing -> pure Nothing
  _ -> case spineOf term of
    (CGlob h, sargs) -> do
      let expl = [a | (Expl, a) <- sargs]
      mp <- globPrimName h
      case mp of
        Just p | Just (rk, argks) <- arithPrim p, length expl == length argks -> do
          oks <- sequence (zipWith (scalarHasKind g pks dks ret) argks expl)
          pure (if and oks then Just rk else Nothing)
        _
          | Just args <- lr1SelfArgs g (length pks) term -> do
              oks <- sequence (zipWith (selfArgElig g pks dks ret) pks args)
              pure (if and oks then Just ret else Nothing)
          | otherwise -> pure Nothing
    _ -> pure Nothing

-- | The kind of de Bruijn variable @i@ against a DE-BRUIJN-ORDERED local-kind
-- context @dks@ (index 0 = innermost binder).  The worker body's initial @dks@
-- is @reverse pks@ (so de Bruijn 0 is the LAST param); a 'CLet' PREPENDS its
-- binder's kind, so a let-bound scalar is read at index 0 with the params
-- shifted up by one.  Out of range ⇒ Nothing.  (The §let widening replaced the
-- old params-only @varParamKind pks i = pks !! (n-1-i)@ — the de-Bruijn list IS
-- @reverse pks@ extended with lets, so the index is direct.)
varParamKind :: [ParamKind] -> Int -> Maybe ParamKind
varParamKind dks i =
  if i >= 0 && i < length dks then Just (dks !! i) else Nothing

-- | Eligibility of an @if@ condition: a saturated SAFE scalar compare whose
-- operands have the comparison's operand kind.
scalarEligCond :: GName -> [ParamKind] -> [ParamKind] -> ScalarKind -> Term -> Gen Bool
scalarEligCond g pks dks ret term = case spineOf term of
  (CGlob h, sargs) -> do
    let expl = [a | (Expl, a) <- sargs]
    mp <- globPrimName h
    case (mp >>= cmpPrim, expl) of
      (Just (_, opk), [a, b]) -> andM [scalarHasKind g pks dks ret opk a, scalarHasKind g pks dks ret opk b]
      _ -> pure False
  _ -> pure False

-- | The unboxed worker name: keep @kwi_@ for an all-@int64@ worker (so existing
-- golden C is byte-stable); a worker with any @double@ param/result uses
-- @kwd_@.
scalarWorkerName :: GName -> [ParamKind] -> ScalarKind -> Text
scalarWorkerName g pks ret
  | any (== PBoxed) pks = "kwm_" <> mangle (gKey g) -- mixed boxed/unboxed (R2.4)
  | all (== PScalar KInt64) pks && ret == KInt64 = "kwi_" <> mangle (gKey g)
  | otherwise = "kwd_" <> mangle (gKey g)

-- | Emit the unboxed worker with per-slot param types + (scalar) return type,
-- e.g. @double kwd_g(double, int64_t, int *kovf)@ or, with a boxed slot,
-- @KValue *kwm_g(int64_t, KValue *, int64_t, int *kovf)@.
compileScalarWorker :: GName -> [ParamKind] -> ScalarKind -> Term -> Gen ()
compileScalarWorker g pks ret inner = do
  let n = length pks
      worker = scalarWorkerName g pks ret
      ps = ["p" <> T.pack (show i) | i <- [0 .. n - 1]]
      env = reverse ps -- de Bruijn 0 = innermost binder = the LAST param
      dks = reverse pks -- de-Bruijn-ordered slot kinds, parallel to @env@
      paramDecls = T.intercalate ", " (zipWith (\k p -> cParamTy k <> " " <> p) pks ps ++ ["int *kovf"])
  (bodyStmts, ()) <- captured "0" (scalarTail g pks ret ps env dks inner)
  let fn =
        T.unlines $
          [ "static " <> cScalarTy ret <> " " <> worker <> "(" <> paramDecls <> ") {"
          , "  int64_t kspc = KRT2_SP_QUANTUM;"
          , "  while (1) {"
          ]
            ++ map ("    " <>) bodyStmts
            ++ [ "  }"
               , "}"
               ]
  emitTop ("static " <> cScalarTy ret <> " " <> worker <> "(" <> paramDecls <> ");") fn

-- | The C expression and type for one self-call argument: a scalar slot is
-- compiled to its scalar kind; a boxed slot is a pass-through of the boxed C
-- param (eligibility guarantees the arg is a bare @CVar@ of a boxed slot).
scalarSelfArg :: GName -> [ParamKind] -> ScalarKind -> [Text] -> [ParamKind] -> ParamKind -> Term -> Gen (Text, Text)
scalarSelfArg g pks ret env dks pk a = case pk of
  PScalar k -> do e <- scalarExpr g pks ret env dks k a; pure (cScalarTy k, e)
  PBoxed -> case a of
    CVar j -> pure ("KValue *", env !! j)
    _ -> do e <- lr1Unreachable; pure ("KValue *", e)

-- | Compile the body in TAIL position: @if@ branches recurse in tail; a @let@
-- emits its scalar RHS into a fresh typed C local and recurses on the body with
-- that local pushed at de Bruijn 0 (so a let temporary in a hot loop stays in a
-- register — no boxing); a saturated self-call reassigns the params (each temp
-- typed by its slot kind) and @continue@s (an in-place loop — no @KEnv@); any
-- other (leaf, scalar) expr is returned.  @env@/@dks@ are kept in lock-step (the
-- C-local name and its scalar kind at each de-Bruijn slot).
scalarTail :: GName -> [ParamKind] -> ScalarKind -> [Text] -> [Text] -> [ParamKind] -> Term -> Gen ()
scalarTail g pks ret ps env dks term = case term of
  CIf c t e -> do
    cond <- scalarCond g pks ret env dks c
    (tb, ()) <- captured "0" (scalarTail g pks ret ps env dks t)
    (eb, ()) <- captured "0" (scalarTail g pks ret ps env dks e)
    emit ("if (" <> cond <> ") {")
    forM_ tb (emit . ("  " <>))
    emit "} else {"
    forM_ eb (emit . ("  " <>))
    emit "}"
  -- §let: bind the scalar RHS in a fresh typed C local and recurse on the body
  -- with (local, kind) pushed at de Bruijn 0.  Its kind is the RHS's bottom-up
  -- scalar kind (eligibility already proved it scalar); a let in a SELF-call
  -- branch correctly reads the param values via the shifted env.
  CLet _ _ _ rhs body -> do
    k <- letScalarKind g pks dks ret rhs
    e <- scalarExpr g pks ret env dks k rhs
    t <- freshN "lt_"
    emit (cScalarTy k <> " " <> t <> " = " <> e <> ";")
    scalarTail g pks ret ps (t : env) (PScalar k : dks) body
  _
    | Just args <- lr1SelfArgs g (length pks) term -> do
        -- tail self-call: evaluate new args into typed temps FIRST (they may
        -- read current params), then reassign params and loop.
        temps <- forM (zip pks args) $ \(pk, a) -> do
          (cty, ae) <- scalarSelfArg g pks ret env dks pk a
          t <- freshN "ti_"
          emit (cty <> " " <> t <> " = " <> ae <> ";")
          pure t
        forM_ (zip ps temps) $ \(p, t) -> emit (p <> " = " <> t <> ";")
        emitScalarWorkerSafepoint
        emit "continue;"
    | otherwise -> do
        e <- scalarExpr g pks ret env dks ret term
        emit ("return " <> e <> ";")

-- | The scalar kind a let-RHS evaluates to, recomputed at codegen for the C
-- local's type.  Eligibility ('scalarKindOf') already proved it 'Just'; this
-- re-derivation keeps the C-local declaration in sync with that verdict (a
-- 'Nothing' here is the same invariant break the 'lr1Unreachable' guards catch,
-- so default to the worker's return kind rather than miscompile).
letScalarKind :: GName -> [ParamKind] -> [ParamKind] -> ScalarKind -> Term -> Gen ScalarKind
letScalarKind g pks dks ret rhs = do
  mk <- scalarKindOf g pks dks ret rhs
  pure (maybe ret id mk)

-- | Compile a scalar-expressible value: a literal, a var, an arith op (int ops
-- overflow-escaped, double ops plain IEEE, @intToDouble@ a cast), or a
-- (non-tail) self-call (whose @kovf@ is propagated immediately). Each int op
-- that overflows sets @*kovf@ (or runs 'gsI64Escape') and bails at once —
-- never a wrapped value.
-- | Worker-side unbox of a boxed value to a scalar: the worker's escape flag is
-- the @int *kovf@ parameter (already a pointer), so pass it directly (unlike
-- 'unboxScalar' at a call site, which takes @&@ of a local int).
unboxWorker :: ScalarKind -> Text -> Text
unboxWorker KInt64 fb = "kunbox_i64(" <> fb <> ", kovf)"
unboxWorker KDouble fb = "kunbox_dbl(" <> fb <> ", kovf)"

-- | Compile a scalar-expressible value for the demanded scalar kind @dk@: a
-- boxed-param field read coerced to @dk@ (R2.4), a literal, a (scalar) param
-- var, an arith op, or a (non-tail) self-call.
-- @dk@ is only consulted for the boxed-field coercion; everything else is
-- determined bottom-up (so all-scalar output is unaffected).
scalarExpr :: GName -> [ParamKind] -> ScalarKind -> [Text] -> [ParamKind] -> ScalarKind -> Term -> Gen Text
scalarExpr = scalarExprBody

scalarExprBody :: GName -> [ParamKind] -> ScalarKind -> [Text] -> [ParamKind] -> ScalarKind -> Term -> Gen Text
scalarExprBody g pks ret env dks dk term
  -- R2.4: a record-field read of a BOXED param yields a boxed value; coerce it
  -- to the demanded scalar kind with a tag-checked unbox that escapes to the
  -- boxed worker on a wrong tag (so a non-Int/Double field never miscompiles).
  | CProjAt (CVar j) _ off <- term, isBoxedProj dks term = do
      fb <- freshN "fb_"
      emit ("KValue *" <> fb <> " = krec_at(" <> (env !! j) <> ", " <> T.pack (show off) <> ");")
      t <- freshN "ti_"
      emit (cScalarTy dk <> " " <> t <> " = " <> unboxWorker dk fb <> ";")
      emit "if (*kovf) return 0;"
      pure t
  | otherwise = case term of
      CLit (LitInt m) -> pure (cIntLit m)
      CLit (LitDouble d) -> pure (cDblLit d)
      CVar i -> pure (env !! i)
      -- §let in value position: emit the scalar RHS into a fresh typed local and
      -- evaluate the body with it pushed at de Bruijn 0 (the value-position twin
      -- of 'scalarTail's let case — e.g. an inner FMA temporary used by a leaf
      -- return expression).
      CLet _ _ _ rhs body -> do
        k <- letScalarKind g pks dks ret rhs
        e <- scalarExpr g pks ret env dks k rhs
        t <- freshN "lt_"
        emit (cScalarTy k <> " " <> t <> " = " <> e <> ";")
        scalarExpr g pks ret (t : env) (PScalar k : dks) dk body
      _ -> case spineOf term of
        (CGlob h, sargs) -> do
          let expl = [a | (Expl, a) <- sargs]
          mp <- globPrimName h
          case mp of
            Just p | Just (_, argks) <- arithPrim p, length expl == length argks -> scalarArith g pks ret env dks p expl
            _
              | Just args <- lr1SelfArgs g (length pks) term -> do
                  aes <- mapM (\(pk, a) -> snd <$> scalarSelfArg g pks ret env dks pk a) (zip pks args)
                  t <- freshN "ti_"
                  emit (cScalarTy ret <> " " <> t <> " = " <> scalarWorkerName g pks ret <> "(" <> T.intercalate ", " (aes ++ ["kovf"]) <> ");")
                  emit "if (*kovf) return 0;"
                  pure t
              | otherwise -> lr1Unreachable
        _ -> lr1Unreachable

-- | Lower one scalar arith op.  Int ops mirror the @kp_*Int@ runtime helpers
-- exactly (§6 unbounded Integer promotes to GMP via the boxed escape; div/mod
-- by zero traps; INT64_MIN edges escape).  Double ops are plain IEEE (no
-- overflow/zero trap — they wrap to ±inf/NaN exactly like @kp_*Double@) and
-- match the boxed path's per-operation rounding: each op is emitted into its
-- own statement/temp, and the driver compiles with @-ffp-contract=off@
-- (Driver.hs), so the compiler cannot fuse a @mul@-then-@add@ into a
-- single-rounding FMA at any @-O@ level.  @intToDouble@ is a C cast (== the
-- prim's @(double)i@).
scalarArith :: GName -> [ParamKind] -> ScalarKind -> [Text] -> [ParamKind] -> Text -> [Term] -> Gen Text
scalarArith g pks ret env dks p expl = do
  -- each arg is compiled for the prim's expected kind (so a boxed-field arg is
  -- coerced to the right scalar kind); arithPrim p is Just by the caller.
  let argks = maybe [] snd (arithPrim p)
  aes <- sequence (zipWith (\k a -> scalarExpr g pks ret env dks k a) argks expl)
  t <- freshN "ti_"
  esc <- gets gsI64Escape -- worker: `*kovf=1; return 0;`
  case (p, aes) of
    ("addInt", [a, b]) -> emit ("int64_t " <> t <> "; if (__builtin_add_overflow(" <> a <> ", " <> b <> ", &" <> t <> ")) { " <> esc <> " }")
    ("subInt", [a, b]) -> emit ("int64_t " <> t <> "; if (__builtin_sub_overflow(" <> a <> ", " <> b <> ", &" <> t <> ")) { " <> esc <> " }")
    ("mulInt", [a, b]) -> emit ("int64_t " <> t <> "; if (__builtin_mul_overflow(" <> a <> ", " <> b <> ", &" <> t <> ")) { " <> esc <> " }")
    ("negInt", [a]) -> emit ("int64_t " <> t <> "; if (" <> a <> " == INT64_MIN) { " <> esc <> " } else " <> t <> " = -" <> a <> ";")
    ("divInt", [a, b]) -> emit ("if (" <> b <> " == 0) krt_fail(\"divInt: division by zero\"); int64_t " <> t <> "; if (" <> a <> " == INT64_MIN && " <> b <> " == -1) { " <> esc <> " } else " <> t <> " = " <> a <> " / " <> b <> ";")
    ("modInt", [a, b]) -> emit ("if (" <> b <> " == 0) krt_fail(\"modInt: division by zero\"); int64_t " <> t <> "; if (" <> a <> " == INT64_MIN && " <> b <> " == -1) " <> t <> " = 0; else " <> t <> " = " <> a <> " % " <> b <> ";")
    ("addDouble", [a, b]) -> emit ("double " <> t <> " = " <> a <> " + " <> b <> ";")
    ("subDouble", [a, b]) -> emit ("double " <> t <> " = " <> a <> " - " <> b <> ";")
    ("mulDouble", [a, b]) -> emit ("double " <> t <> " = " <> a <> " * " <> b <> ";")
    ("divDouble", [a, b]) -> emit ("double " <> t <> " = " <> a <> " / " <> b <> ";")
    ("negDouble", [a]) -> emit ("double " <> t <> " = -" <> a <> ";")
    ("intToDouble", [a]) -> emit ("double " <> t <> " = (double)" <> a <> ";")
    _ -> lr1UnreachableStmt
  pure t

-- | Compile an @if@ condition (a saturated safe scalar compare) to a C boolean
-- expr.  The C operator comes from 'cmpPrim', which admits only comparisons
-- whose C operator matches the runtime prim exactly.
scalarCond :: GName -> [ParamKind] -> ScalarKind -> [Text] -> [ParamKind] -> Term -> Gen Text
scalarCond g pks ret env dks term = case spineOf term of
  (CGlob h, sargs) -> do
    let expl = [a | (Expl, a) <- sargs]
    mp <- globPrimName h
    case (mp >>= cmpPrim, expl) of
      (Just (op, opk), [a, b]) -> do
        ae <- scalarExpr g pks ret env dks opk a
        be <- scalarExpr g pks ret env dks opk b
        pure ("(" <> ae <> " " <> op <> " " <> be <> ")")
      _ -> lr1Unreachable
  _ -> lr1Unreachable

-- These are unreachable when 'scalarPlan' classified the body as eligible;
-- they record a backend error (never a silent miscompile) if an invariant
-- breaks.
lr1Unreachable :: Gen Text
lr1Unreachable = escalated "LR1-i64" "an int64-ineligible term reached the unboxed worker (LR1 eligibility invariant violated)"

lr1UnreachableStmt :: Gen ()
lr1UnreachableStmt = lr1Unreachable >> pure ()

emitScalarWorkerSafepoint :: Gen ()
emitScalarWorkerSafepoint = do
  emit "if (--kspc <= 0) {"
  emit "  kspc = KRT2_SP_QUANTUM;"
  emit "  if (krt2_safepoint()) { *kovf = KRT2_SCALAR_ABORT; return 0; }"
  emit "}"

-- | The saturated fast path at a call site: unbox each arg by its scalar kind,
-- call the unboxed worker, and escape to the boxed @kw_g@ (from the ORIGINAL
-- boxed args) on a wrong-tag arg or an int64 overflow.
compileScalarCall :: GName -> [ParamKind] -> ScalarKind -> [(Icit, Term)] -> [Int] -> Gen Text
compileScalarCall g pks ret sargs runtimeIdxs = do
  let worker = scalarWorkerName g pks ret
      kw = "kw_" <> mangle (gKey g)
      k = length sargs
  ownedFlags <- callArgNeedsOwnedForGlobal g sargs
  -- Perceus RC S2.1: thread each saturating arg's spine path so its CVar uses
  -- resolve in the analysis side-table (this is an exactly-saturated call, so the
  -- list position is the spine index).
  aes <-
    mapM
      (\(j, needOwned, (_, a)) -> withSpineArg k j (compileCallArg needOwned a))
      (zip3 [0 ..] ownedFlags sargs)
  ts <- forM aes $ \ae -> do
    t <- freshN "la_"
    emit ("KValue *" <> t <> " = " <> ae <> ";")
    pure t
  let rtTs = [ts !! i | i <- runtimeIdxs, i >= 0, i < length ts]
  ovf <- freshN "kovf_"
  emit ("int " <> ovf <> " = 0;")
  -- scalar slots unbox (tag-checked → escape); boxed slots pass through.
  avs <- forM (zip pks rtTs) $ \(pk, t) -> case pk of
    PScalar k -> do
      av <- freshN "lu_"
      emit (cScalarTy k <> " " <> av <> " = " <> unboxScalar k t ovf <> ";")
      pure av
    PBoxed -> pure t
  r <- freshN "lr_"
  res <- freshN "lres_"
  let boxed = "ktrampoline(" <> kw <> "(" <> T.intercalate ", " ts <> "))"
  emit ("KValue *" <> res <> ";")
  -- a wrong-tag arg short-circuits to boxed WITHOUT calling the unboxed worker
  -- (so it never runs on garbage 0-args, e.g. a spurious /0 trap).  A worker-side
  -- safe-point abort is distinct from overflow: it transfers control to the
  -- runtime unwinder so active exit actions run before the pending interrupt is
  -- delivered and before any enclosing generated pure/do frame can run more
  -- source code. It must not rerun boxed code or fabricate a Unit result.
  emit ("if (" <> ovf <> ") { " <> res <> " = " <> boxed <> "; }")
  emit "else {"
  emit ("  " <> cScalarTy ret <> " " <> r <> " = " <> worker <> "(" <> T.intercalate ", " (avs ++ ["&" <> ovf]) <> ");")
  emit ("  if (" <> ovf <> " == KRT2_SCALAR_ABORT) {")
  emit "    krt2_scalar_abort();"
  emit "    return kunit();"
  emit "  }"
  emit ("  " <> res <> " = " <> ovf <> " ? " <> boxed <> " : " <> boxScalar ret r <> ";")
  emit "}"
  pure res

-- | Append a forward declaration + a completed top-level C function.
emitTop :: Text -> Text -> Gen ()
emitTop proto fn = modify' $ \st -> st {gsTop = fn : gsTop st, gsProtos = proto : gsProtos st}

-- Global/CAF caches are process-wide publish points. RC-on accessors return a
-- distinct counted owner for the caller while the cache keeps its own owner;
-- RC-off keeps the legacy raw return, but still marks the cached graph shared so
-- storage fast paths see the same publication discriminator.
globalCacheOwnershipPlan :: Gen (Text, [Text])
globalCacheOwnershipPlan = do
  rcOn <- gets gsRcEnabled
  let shareFresh = ["  krc_mark_shared_recursive(fresh);"]
      cacheHit
        | rcOn = "  if (cached) return kdup(cached);"
        | otherwise = "  if (cached) return cached;"
      publishFresh
        | rcOn =
            [ "  KValue *expected = NULL;" ]
              ++ shareFresh
              ++ [ "  if (atomic_compare_exchange_strong_explicit(&cache, &expected, fresh,"
                 , "                                            memory_order_release,"
                 , "                                            memory_order_acquire)) {"
                 , "    return kdup(fresh);"
                 , "  }"
                 , "  kdrop(fresh);"
                 , "  return kdup(expected);"
                 ]
        | otherwise =
            shareFresh
              ++ [ "  atomic_store_explicit(&cache, fresh, memory_order_release);"
                 , "  return fresh;"
                 ]
  pure (cacheHit, publishFresh)

finishGlobal :: Text -> [Text] -> Text -> Gen ()
finishGlobal ident stmts e = do
  (cacheHit, publishFresh) <- globalCacheOwnershipPlan
  let fn =
        T.unlines $
          [ "static KValue *" <> ident <> "(void) {"
          , "  static _Atomic(KValue *) cache = NULL;"
          , "  KValue *cached = atomic_load_explicit(&cache, memory_order_acquire);"
          , cacheHit
          , "  KEnv *env = 0; (void)env;"
          ]
            ++ map ("  " <>) stmts
            ++ [ "  KValue *fresh = " <> e <> ";"
               ]
            ++ publishFresh
            ++ [ "}" ]
  modify' $ \st -> st {gsTop = fn : gsTop st}

-- | The C @main@: initialise the GC and run @main@'s IO action.
-- | The kappart2 runtime owns the scheduler: @main@ runs as the root fiber and
-- returns its terminal Exit (Success a | Failure cause); the process exit code
-- is 0 on Success, 1 on Failure.
emitMain :: GName -> Gen ()
emitMain g = do
  rcOn <- gets gsRcEnabled
  let ident = cGlobIdent g
      rcGate = ["  krc_set_enabled(0);" | not rcOn]
      fn =
        T.unlines
          ( [ "int main(void) {" ]
              ++ rcGate
              ++ [ "  krt2_new(0);"
                 , "  KValue *kexit = krt2_run_main(" <> ident <> "());"
                 , "  return krt2_exit_is_success(kexit) ? 0 : 1;"
                 , "}"
                 ]
          )
  modify' $ \st -> st {gsTop = fn : gsTop st}

assemble :: GenState -> Text
assemble st =
  T.unlines $
    [ "/* Generated by the Kappa native backend (Kappa.Backend.C). */"
    , "#include \"kappart2.h\"" -- the kappart2 runtime; pulls in kappart.h too
    , "#include <stdatomic.h>"
    , ""
    ]
      -- LR2: per-program numeric constructor/variant tag ids (KT_/KVT_),
      -- referenced by the generated constructions and pattern-match tests.
      ++ tagEnumBlock st
      ++ [""]
      -- §34.5.3: extern decls for each used builtin primitive's direct C
      -- entry point, so the optimized output calls it directly (no by-name dispatch).
      ++ primExternBlock st
      -- §27.1.1: direct extern prototypes + typed marshalling wrappers for
      -- each used host-binding member — the manifest-declared C symbols are
      -- called DIRECTLY (no name table, no strcmp dispatch).
      ++ hostNativeBlock st
      ++ reverse (gsProtos st)
      ++ [""]
      ++ reverse (gsTop st)

-- | Extern declarations for the direct C entry point of each used builtin
-- primitive (@kpf_*@). The optimized output calls these directly; the runtime
-- defines them. There is no by-name firing path in the runtime — every prim is
-- reached by a direct call or a curried @knative@ function pointer.
primExternBlock :: GenState -> [Text]
primExternBlock st
  | null cfns = []
  | otherwise =
      ["/* §34.5.3 builtin primitives: direct entry points (no string dispatch). */"]
        ++ ["extern KValue *" <> cfn <> "(KValue **);" | cfn <- cfns]
        ++ [""]
  where
    -- distinct entry-point names (several prims share one kpf_*)
    cfns =
      Set.toList . Set.fromList $
        [cfn | n <- Set.toList (gsPrimUsed st), Just (PrimEntry cfn _ _) <- [Map.lookup n primEntries]]

-- | The native host-binding block: one @extern@ prototype per distinct C
-- symbol used, followed by one marshalling wrapper per used member
-- ('Kappa.Backend.NativeFfi'). Empty when no host.native member is used.
hostNativeBlock :: GenState -> [Text]
hostNativeBlock st
  | null used = []
  | otherwise =
      [ "/* §27.1.1 native host bindings: direct extern prototypes + typed wrappers. */" ]
        ++ dedupKeep (map externPrototype used)
        ++ [""]
        ++ map wrapperDefinition used
        ++ [""]
  where
    used = [rns | g <- Set.toList (gsHostUsed st), Just rns <- [Map.lookup g (gsHostSyms st)]]
    dedupKeep = go Set.empty
      where
        go _ [] = []
        go seen (x : xs)
          | x `Set.member` seen = go seen xs
          | otherwise = x : go (Set.insert x seen) xs

-- ── Term lowering ────────────────────────────────────────────────────

-- | Compile a term: emit any needed statements into the current buffer and
-- return a C expression (of type @KValue *@) for its value.
compile :: Term -> Gen Text
compile term = do
  -- §12.2/§31.2/§14.4: a value whose head is a proof-typed global — a
  -- propositional-equality / h-prop lemma like 'isPropEq' / 'unsafeAssertProof'
  -- / 'cong' (reached via lawful-by-default 'Monoid' law members) — is
  -- RuntimeErased.  Erase the WHOLE maximal spine to the unit placeholder so the
  -- ADMIT primitives '__eqProof'/'__unsafeAssertProof' beneath those lemmas are
  -- never reached at runtime.  A proof is inert (never eliminated/applied), and a
  -- proof ARGUMENT to anything is itself erased ('eraseQ0Args' /
  -- 'compileErasableArg'), so the spine never feeds a live continuation — erasing
  -- the maximal spine cannot drop a runtime-relevant computation.  See
  -- 'resultIsProofP'.  ('subst'/'pathInd', whose result is a motive-typed VALUE,
  -- are correctly NOT proof-typed and fall through to the real compile path.)
  proofSpine <- case headGlob term of
    Just g -> resultIsProof g
    Nothing -> pure False
  if proofSpine then pure "kunit()" else compileTerm term

compileTerm :: Term -> Gen Text
compileTerm term = case term of
  CVar i -> do
    -- Perceus RC walk-and-lookup (R-path) plus R2.3 flat-local resolution. The
    -- ownership policy for ordinary expression reads is only the S2.2 NonLast
    -- dup; owned call/store positions use 'compileOwnedVarUse' instead.
    e <- compileVarRef i
    -- Perceus RC S2.2 (b.2): a 'NonLast' occurrence is SHARED downstream → wrap in
    -- @kdup@ (rc increment, immediates skipped). Inert under the OFF baseline,
    -- whose generated entry point also disables runtime RC effects.
    rcDupVarUse e
  CGlob g -> compileGlob g
  CLit l -> compileLit l
  CApp {} -> compileApp term
  CLam _ _ _ body -> compileLam body
  CCtor g _ args -> compileCtor g args
  CIf {} -> sinkToExpr term
  CMatch {} -> sinkToExpr term
  CLet {} -> sinkToExpr term
  CLetRec {} -> sinkToExpr term
  CRecordV fs -> compileRecord fs
  CProj e f -> do
    ee <- withChild P.childPos (compile e)
    pure ("kproj(" <> ee <> ", " <> cStr f <> ")")
  -- P0.4: a projection of a statically-known CLOSED record reads the field at
  -- its fixed lexicographic offset (krec_at, the tuple fast path) instead of a
  -- kproj-by-name strcmp scan.  Open/sealed/dynamic records keep plain CProj.
  CProjAt e _ i -> do
    ee <- withChild P.childPos (compile e)
    pure (recAtExpr ee i)
  -- S2.3b: do-kernel bodies are no longer treated as an ownership-erased
  -- island. Mutable-variable reads/writes are ordinary runtime uses, so the RC
  -- validation path must see any CVar lowered while compiling the do body and
  -- fail closed on missing side-table facts.
  CDo lbl items -> compileDo lbl items
  -- §13 closed/open variants: injection is a tagged payload.
  CInject tag e -> do
    ee <- withChild P.childPos (compile e)
    tc <- variantTagConst tag
    pure ("kinject(" <> tc <> ", " <> cStr tag <> ", " <> ee <> ")")
  -- §13.2.10: `seal` is pure and non-generative (seal e as S ≡ e), so a
  -- sealed package's runtime value is exactly its underlying record/value.
  CSealE _ e -> withChild P.childPos (compile e)
  -- §19 suspensions: Delay re-evaluates on force; Memo caches.
  CThunkE e -> withChild P.childPos (compileSuspension 0 e)
  CLazyE e -> withChild P.childPos (compileSuspension 1 e)
  CForceE t -> do
    te <- withChild P.childPos (compile t)
    pure ("kforce(" <> te <> ")")
  -- ── Escalated: NOT runtime values in an accepted, erased program ──
  -- A type-level / staging term (sort, function/record/variant/signature
  -- type, unsolved-dictionary meta, syntax quote) is computationally erased
  -- (§12.2 quantity-0 erasure, §31.2; §30.2.4 for staging): its runtime
  -- value is the unit placeholder, which the interpreter likewise never
  -- inspects.  Erasing it here (rather than rejecting) means a type/Syntax
  -- value reached through ANY position — an argument, a field, a global
  -- body, a local `let` binding — compiles and runs, so no accepted program
  -- is refused over an erased term (compileErasableArg handles the common
  -- argument/field sites directly; this is the catch-all).
  CSort _ -> pure "kunit()"
  CPi {} -> pure "kunit()"
  CRecordT _ -> pure "kunit()"
  CVariantT _ -> pure "kunit()"
  CSigT {} -> pure "kunit()"
  CMeta _ -> pure "kunit()"
  CQuote {} -> pure "kunit()"

-- | Head global of an application spine, if any.
headGlob :: Term -> Maybe GName
headGlob = \case
  CApp _ f _ -> headGlob f
  CGlob g -> Just g
  CCtor g _ _ -> Just g
  _ -> Nothing

-- | An application spine: head term plus its arguments with icities.
spineOf :: Term -> (Term, [(Icit, Term)])
spineOf = go []
  where
    go acc (CApp ic f a) = go ((ic, a) : acc) f
    go acc t = (t, acc)

-- | Recognise a fully-saturated application of an eta-expanded constructor
-- and beta-reduce it to a direct constructor (gap P0-A).
--
-- §10.1 'etaCtor' elaborates a constructor value of @k@ Pi binders into @k@
-- nested lambdas whose innermost body is a saturated @CCtor g [CVar …]@
-- selecting only the runtime-field binders (erased implicit/type binders are
-- dropped from the payload).  An applied occurrence keeps that
-- @CApp (… (CLam … (CCtor g …))) a@ shape, so without this it lowers through a
-- @k@-deep curried @kclo@/@kapp@ chain (one cons cell costs ~3 closures + 3
-- @kpush@ + 2 @kapp@ — the cost that dominates @listfold@/@adtbuild@).
--
-- When the spine applies exactly one argument per lambda the redex
-- beta-reduces: each body @CVar j@ names the binder at de Bruijn index @j@,
-- i.e. spine position @k-1-j@ (the spine lists arguments outermost-first),
-- supplied by the applied argument there.  Because every field var is a bare
-- binder reference (never a compound term or a free variable), the reduction
-- is a simultaneous substitution that just selects applied arguments — no
-- index shifting on open terms.  The result is @CCtor g [selected args]@,
-- compiled by 'compileCtor' as a direct @kctor@.
--
-- 'Nothing' for a partial application (still a closure), an over-application
-- (impossible for a well-typed ctor, but rejected for safety), or any head
-- that is not an eta-expanded constructor — all of which keep the general
-- curried lowering.
etaCtorApp :: Term -> Maybe (GName, [Term])
etaCtorApp term =
  case spineOf term of
    (hd, sargs)
      | (k, body) <- funcArity hd -- count the leading eta lambdas
      , k >= 1
      , k == length sargs
      , CCtor g _ fieldVars <- body ->
          (,) g <$> traverse (pick (map snd sargs) k) fieldVars
    _ -> Nothing
  where
    -- a field var must be a bare in-range binder reference; anything else
    -- (a compound subterm, or a free variable at index >= k) bails to the
    -- general lowering rather than misreading the payload.
    pick args k = \case
      CVar j | j >= 0, j < k -> Just (args !! (k - 1 - j))
      _ -> Nothing

-- | Like 'etaCtorApp', but also report the SPINE INDEX each picked field arg came
-- from (the @k-1-j@ position for a field var @CVar j@). Perceus RC S2.1 threads
-- the eta-ctor's field args by this spine index so they key the same way the
-- analysis walked the curried-CApp eta-ctor application — the beta-reduction
-- 'compileCtor' performs changes the emitted structure but not the args' origin.
etaCtorAppSpine :: Term -> Maybe (GName, Int, [(Int, Term)])
etaCtorAppSpine term =
  case spineOf term of
    (hd, sargs)
      | (k, body) <- funcArity hd
      , k >= 1
      , k == length sargs
      , CCtor g _ fieldVars <- body ->
          (\picks -> (g, k, picks)) <$> traverse (pick (map snd sargs) k) fieldVars
    _ -> Nothing
  where
    pick args k = \case
      CVar j | j >= 0, j < k -> Just (k - 1 - j, args !! (k - 1 - j))
      _ -> Nothing

-- | Compile an eta-ctor application ('etaCtorApp') as a direct 'kctor', threading
-- each field arg at its original CApp-spine path (Perceus RC S2.1 R-path) instead
-- of the 'CCtor'-field path — because the analysis walked the un-reduced curried
-- application. @g@ is the ctor, @k@ the spine length, @picks@ the field args paired
-- with the spine index each came from (FIELD order).
compileEtaCtorApp :: GName -> Int -> [(Int, Term)] -> Gen Text
compileEtaCtorApp g k picks =
  compileCtorPaths (\i -> withSpineArg k (fst (picks !! i))) g (map snd picks)

-- | If @term@ is a saturated call to the worker's own global (a tail
-- self-call), return its arguments (with icities); the worker then loops
-- instead of recursing in C.
selfTailArgs :: TailInfo -> Term -> Maybe [(Icit, Term)]
selfTailArgs ti term = case spineOf term of
  (CGlob g, args) | g == tiName ti && length args == tiArity ti -> Just args
  _ -> Nothing

-- | The self-tail-loop path is a direct global call in disguise, so it must
-- apply the same static/Q0 argument rewrite as 'compileApp' before compiling
-- argument temporaries. Otherwise an erased implicit type argument whose source
-- is a 'CVar' is lowered as a runtime read at a path the ownership walk correctly
-- omitted.
selfTailArgsForLoop :: TailInfo -> Term -> Gen (Maybe [(Icit, Term)])
selfTailArgsForLoop ti term =
  case spineOf term of
    (CGlob g, args)
      | g == tiName ti
      , length args == tiArity ti -> do
          term' <- eraseQ0Args g term
          pure (selfTailArgs ti term')
    _ -> pure Nothing

-- | Lower a self-tail-call to a loop step: recompute the arguments into
-- fresh temporaries (they may read the current parameters), rebind the
-- worker's parameter variables, and @continue@.
emitTailLoop :: [Text] -> TailInfo -> [(Icit, Term)] -> Gen ()
emitTailLoop cleanup ti args = do
  -- Evaluate every new argument into a temp FIRST (an arg may read a current
  -- parameter via @kvar@), THEN update the parameter cells in place — so the
  -- loop reuses the cells built once in 'compileFunctionGlobal' rather than
  -- allocating a fresh env each iteration (QW2).
  -- Perceus RC S2.1: a self-tail-call is a saturated spine, so thread each new
  -- argument's spine path ('withSpineArg') — its CVar uses key the same way the
  -- analysis walked the original tail-call CApp.
  let k = length args
  temps <- forM (zip [0 ..] args) $ \(j, (_ic, a)) -> do
    e <- withSpineArg k j (compileErasableArg a) -- erase type-level/staging args (§31.2), any icity
    t <- freshN "tc_"
    emit ("KValue *" <> t <> " = " <> e <> ";")
    pure t
  mapM_ emit cleanup
  -- reassign the C parameters (FLAT: read directly; REBUILD: the loop top
  -- rebuilds kw_env from them).  Temps first, so an arg may read a current param.
  forM_ (zip (tiSlots ti) temps) $ \(slot, t) -> emit (slot <> " = " <> t <> ";")
  emit "continue;"

-- | Emit a tail-position application.  A call whose spine head is a
-- primitive cannot recurse, so it is computed directly and returned (the
-- saturated-prim fast path, no needless partial-application box or bounce).
-- A call to anything else (a function value / closure that could recurse)
-- becomes a trampoline @kbounce(f,a)@, returned so the driving
-- @kapp@/@krun_io@ performs the deferred application in constant C stack.
-- NOTE: this is the AUTHORITY on when a worker returns a @K_BOUNCE@;
-- 'workerMayBounce' mirrors the @kbounce@ condition below and must be kept in
-- lock-step (a new @kbounce@ arm here without updating it would make R3.1's
-- trampoline elision unsound).
emitTailApp :: [Text] -> Term -> Gen ()
emitTailApp cleanup term
  -- P0-A: a saturated eta-expanded constructor in tail position is a final
  -- data value (it cannot bounce or recurse), so build it directly and
  -- return it rather than trampolining through the closure chain.
  | Just (g, k, picks) <- etaCtorAppSpine term = do
      e <- compileEtaCtorApp g k picks
      mapM_ emit cleanup
      emit ("return " <> e <> ";")
emitTailApp cleanup term = do
  let (hd, _) = spineOf term
  mp <- case hd of CGlob g -> globPrimName g; _ -> pure Nothing
  case (mp, term) of
    (Just _, _) -> do
      e <- compile term -- prim spine: direct helper / entry-point call, computed here, no trampoline
      mapM_ emit cleanup
      emit ("return " <> e <> ";")
    (Nothing, CApp Expl f a) -> do
      -- Perceus RC S2.1: head/arg at the shared 'appHeadPos'/'appArgPos'.
      fe <- withChild P.appHeadPos (compile f)
      ae <- withChild P.appArgPos (compileCallArg True a)
      mapM_ emit cleanup
      emit ("return kbounce(" <> fe <> ", " <> ae <> ");")
    _ -> do
      e <- compile term
      mapM_ emit cleanup
      emit ("return " <> e <> ";")

-- | Is the implicit argument to this head erased at runtime? Primitive
-- and constructor heads erase implicit arguments (§31.2).  Primitives are
-- the @__prim@ module globals and the prelude globals whose value is a
-- bare 'VPrim' (the @prim@ registrations in "Kappa.Prelude").
isErasedHead :: Term -> Gen Bool
isErasedHead t = case headGlob t of
  Just g@(GName m _)
    | m == primModule -> pure True
    | otherwise -> do
        globals <- gets gsGlobals
        ctors <- gets gsCtors
        case Map.lookup g globals of
          Just gd | isVPrimValue (gdValue gd) -> pure True
          _ -> pure (Map.member g ctors)
  Nothing -> pure False

isVPrimValue :: Maybe Value -> Bool
isVPrimValue (Just (VPrim _ _)) = True
isVPrimValue _ = False

-- | Is this implicit argument purely type-level (computationally erased),
-- so an erased binder receiving it can be passed an unused placeholder?
-- Type-level forms and references to type/trait globals are erasable;
-- everything else (dictionaries, runtime values) is compiled for real.
isErasableArg :: Term -> Gen Bool
isErasableArg = \case
  CSort _ -> pure True
  CPi {} -> pure True
  CVariantT _ -> pure True
  CRecordT _ -> pure True
  CSigT {} -> pure True -- §13.2.10 signature type, erased (§12.2, §31.2)
  CMeta _ -> pure True
  CQuote {} -> pure True -- §21/§23 syntax quote: elaboration-time, erased
  CApp _ f _ -> isErasableArg f -- the spine head decides (e.g. @(List a))
  CGlob g -> isTypeGlob g
  _ -> pure False

-- | Compile a value-position argument, erasing it to the unit placeholder
-- when it is a type-level / staging term (§12.2, §31.2): an explicit
-- @(t : Type)@ / @(s : Syntax _)@ argument or constructor field is a
-- compile-time/static-object position (§11.1.6.1, §11.1.6.2) the spec
-- mandates be erased.  The interpreter stores the evaluated type/quote
-- value but never inspects it at runtime; emitting @kunit()@ keeps the
-- arity (so positional field projection stays aligned) while avoiding the
-- type-level guards in 'compile'.
compileErasableArg :: Term -> Gen Text
compileErasableArg = compileErasableArgOwned False

compileErasableArgOwned :: Bool -> Term -> Gen Text
compileErasableArgOwned needOwned a = do
  er <- isErasableArg a
  if er then pure "kunit()" else compileOwnedResult needOwned a

compileBorrowedCallArg :: Term -> Gen Text
compileBorrowedCallArg = \case
  CVar i -> compileVarRef i
  CProj e f -> do
    ee <- withChild P.childPos (compileBorrowedCallArg e)
    pure ("kproj(" <> ee <> ", " <> cStr f <> ")")
  CProjAt e _ i -> do
    ee <- withChild P.childPos (compileBorrowedCallArg e)
    pure (recAtExpr ee i)
  CSealE _ e -> withChild P.childPos (compileBorrowedCallArg e)
  t -> compile t

compileOwnedResult :: Bool -> Term -> Gen Text
compileOwnedResult needOwned = \case
  CVar i
    | needOwned -> compileOwnedVarUse i
  CProj e f -> do
    ee <- withChild P.childPos (compile e)
    rcOwnProjectionResult needOwned e ("kproj(" <> ee <> ", " <> cStr f <> ")")
  CProjAt e _ i -> do
    ee <- withChild P.childPos (compile e)
    rcOwnProjectionResult needOwned e (recAtExpr ee i)
  CSealE _ e -> withChild P.childPos (compileOwnedResult needOwned e)
  t@CIf {} -> sinkToExprOwned needOwned t
  t@CMatch {} -> sinkToExprOwned needOwned t
  t@CLet {} -> sinkToExprOwned needOwned t
  t@CLetRec {} -> sinkToExprOwned needOwned t
  t -> compile t

compileCallArg :: Bool -> Term -> Gen Text
compileCallArg needOwned a = do
  er <- isErasableArg a
  if er
    then pure "kunit()"
    else if needOwned then compileOwnedResult True a else compileBorrowedCallArg a

flagAt :: [Bool] -> Int -> Bool
flagAt flags i = case drop i flags of
  flag : _ -> flag
  [] -> True

callArgNeedsOwnedForGlobal :: GName -> [(Icit, Term)] -> Gen [Bool]
callArgNeedsOwnedForGlobal g sargs = do
  ctx <- gets gsEvalCtx
  go (Repr.argConvSelectGlobal ctx g) sargs
  where
    go _ [] = pure []
    go convs ((ic, a) : rest)
      | ic /= Expl = (False :) <$> go convs rest
      | otherwise = do
          erased <- isErasableArg a
          if erased
            then (False :) <$> go convs rest
            else do
              let (needsOwned, convs') =
                    case convs of
                      Just (Repr.ArgBorrowed : cs) -> (False, Just cs)
                      Just (_ : cs) -> (True, Just cs)
                      Just [] -> (True, convs)
                      Nothing -> (True, Nothing)
              (needsOwned :) <$> go convs' rest

betaApplyArgs :: Term -> [(Icit, Term)] -> Maybe Term
betaApplyArgs = foldM step
  where
    step (CLam lamIc _ _ body) (argIc, arg)
      | lamIc == argIc = Just (substTopTerm arg body)
    step _ _ = Nothing

selectedGlobalRecord :: Term -> Gen (Maybe Term)
selectedGlobalRecord dict = case spineOf dict of
  (CGlob g, args) -> do
    bodies <- gets gsBodies
    pure $ do
      body <- Map.lookup g bodies
      betaApplyArgs body args
  (CRecordV {}, []) -> pure (Just dict)
  (CSealE _ inner, []) -> selectedGlobalRecord inner
  _ -> pure Nothing

selectedProjectedMember :: Term -> Text -> Gen (Maybe Term)
selectedProjectedMember dict fld =
  selectedGlobalRecord dict >>= \case
    Just (CRecordV fs) -> pure (lookup fld fs)
    Just (CSealE _ inner) -> selectedProjectedMember inner fld
    _ -> pure Nothing

-- | A selected dictionary/member projection whose KNOWN dictionary body is just
-- an eta wrapper around a runtime primitive can be lowered as that primitive
-- call.  This is the principled version of the S2.3c/S3.3 "readRef/writeRef via
-- MonadRef evidence" fast path: the decision is keyed by the selected evidence
-- body's Core and the resolved primitive identity ('globPrimName'), never by the
-- projected field spelling alone.  Unknown/local evidence and non-primitive
-- member bodies stay on the ordinary curried 'kapp' path.
compileSelectedProjectedPrimitiveApp :: Term -> Gen (Maybe Text)
compileSelectedProjectedPrimitiveApp term = case spineOf term of
  (CProj dict fld, sargs) -> go dict fld sargs
  (CProjAt dict fld _, sargs) -> go dict fld sargs
  _ -> pure Nothing
  where
    go dict fld sargs = do
      mmember <- selectedProjectedMember dict fld
      case mmember >>= (`betaApplyArgs` sargs) of
        Just reduced
          | reduced /= term
          , (CGlob g, _reducedArgs) <- spineOf reduced -> do
              globPrimName g >>= \case
                Just _ -> Just <$> compileApp reduced
                Nothing -> pure Nothing
        _ -> pure Nothing

-- | A global that denotes a type or trait (so a reference to it in
-- argument position is computationally erased): a declared data type or
-- trait, or a global whose kind is a sort (e.g. the builtin @Integer@).
isTypeGlob :: GName -> Gen Bool
isTypeGlob g = do
  datas <- gets gsDatas
  traits <- gets gsTraits
  globals <- gets gsGlobals
  ctx <- gets gsEvalCtx
  let sortish = case Map.lookup g globals of
        Just gd -> isTypeKindTerm (quote ctx 0 (gdType gd))
        Nothing -> False
  pure (g `Set.member` datas || g `Set.member` traits || sortish)

isTypeKindTerm :: Term -> Bool
isTypeKindTerm = \case
  CSort _ -> True
  CPi _ _ _ _ _ body -> isTypeKindTerm body
  _ -> False

-- | Emit a reference to a runtime primitive, after confirming the linked
-- runtime implements it; an unimplemented primitive is a compile-time
-- 'E_BACKEND_UNSUPPORTED' (never a silent runtime failure).
-- | §34.5.3: a bare reference to a builtin primitive lowers to a DIRECT call
-- on its runtime entry point. A nullary pure builtin is a value, fired
-- immediately (@kpf_x(0)@); any other builtin becomes a curried native
-- action carrying the function pointer (@knative@, pure fires on saturation,
-- IO suspends). There is NO by-name string dispatch. An unknown primitive is a
-- compile-time 'E_BACKEND_UNSUPPORTED'.
emitPrim :: Text -> Gen Text
-- §18.1.12 `poll` is a 0-arity IO action that IS the OP_POLL node: a bare
-- reference (e.g. `ioBind poll k`, where `poll` is the action operand) lowers to
-- the node builder directly, exactly as the saturated `poll` case in
-- 'compileAppGlob'.  There is no curried `kpf_poll` wrapper in the runtime.
emitPrim "poll" = pure "krt2_poll()"
emitPrim name = case Map.lookup name primEntries of
  Just (PrimEntry cfn ar isio) -> do
    markPrimUsed name
    pure $
      if ar == 0 && not isio
        then cfn <> "((KValue **)0)"
        else "knative(" <> cfn <> ", " <> T.pack (show ar) <> ", " <> cStr name <> ", " <> ioFlag isio <> ")"
  Nothing ->
    unsupported "primitive"
      ("the primitive '" <> name <> "' is not implemented by the native runtime")

ioFlag :: Bool -> Text
ioFlag b = if b then "1" else "0"

-- | Record a builtin primitive as referenced so 'assemble' emits its extern.
markPrimUsed :: Text -> Gen ()
markPrimUsed n = modify' (\st -> st {gsPrimUsed = Set.insert n (gsPrimUsed st)})

-- | §27.1.1: a bare reference to a host-binding member lowers to a curried
-- native action carrying the codegen-emitted wrapper pointer ('knative').
-- Native bindings are conservatively typed in UIO, so the action is IO
-- (suspended). 'assemble' emits the wrapper + extern prototype per used member.
emitHostNative :: GName -> ResolvedNativeSymbol -> Gen Text
emitHostNative g rns = do
  markHostUsed g
  collectHostCtors rns
  ctor <- hostNativeCtor rns
  pure
    ( ctor <> "(" <> wrapperCName rns <> ", "
        <> T.pack (show (length (rns.params))) <> ", "
        <> cStr (rns.cSymbol) <> ", 1)"
    )

hostNativeCtor :: ResolvedNativeSymbol -> Gen Text
hostNativeCtor rns = case rns.ffiClass of
  FfiNonblocking -> pure "knative"
  FfiBlocking -> pure "knative_blocking"
  FfiBlockingCancellable ->
    unsupported "native binding"
      ("the native runtime does not implement cancellable blocking calls for '"
        <> rns.cSymbol <> "'")

hostNativeSatCtor :: ResolvedNativeSymbol -> Gen Text
hostNativeSatCtor rns = case rns.ffiClass of
  FfiNonblocking -> pure "knative_sat"
  FfiBlocking -> pure "knative_sat_blocking"
  FfiBlockingCancellable ->
    unsupported "native binding"
      ("the native runtime does not implement cancellable blocking calls for '"
        <> rns.cSymbol <> "'")

-- | Record a host member as referenced so 'assemble' emits its wrapper.
markHostUsed :: GName -> Gen ()
markHostUsed g = modify' (\st -> st {gsHostUsed = Set.insert g (gsHostUsed st)})

-- | Register the std.ffi wrapper constructors a host symbol's marshalling
-- builds (MkI64/MkU32/MkRawPtr/…) so 'assemble' emits their KT_ tag ids
-- (shared with any in-program match on the same ctor).
collectHostCtors :: ResolvedNativeSymbol -> Gen ()
collectHostCtors rns =
  modify' (\st -> st {gsCollectCtors = foldr Set.insert (gsCollectCtors st) (rnsCollectCtors rns)})

-- | The runtime primitive name a global resolves to, if it is one (a
-- @primModule@ name, a prelude @prim@ registration, or a §34.5 host
-- intrinsic that satisfied an @expect@), and that name is implemented by
-- the linked runtime.  Mirrors the prim-resolving arms of 'compileGlob'.
globPrimName :: GName -> Gen (Maybe Text)
globPrimName g@(GName m nm) = do
  prims <- gets gsPrims
  let known n = if n `Set.member` prims then Just n else Nothing
  if m == primModule
    then pure (known nm)
    else do
      globals <- gets gsGlobals
      pure $ case Map.lookup g globals of
        Just gd | Just (VPrim pname _) <- gdValue gd -> known pname
        _ -> Nothing

-- | §34.5.3: the complete builtin-primitive table — each primitive maps to
-- its DIRECT C entry point (@kp_*@/@kpf_*@ in the runtime: pure builtins, and
-- the effectful @kpf_io_*@ ones the do-kernel sequences), its arity, and
-- whether it is an IO action. Codegen emits a direct call to the entry point
-- (saturated) or a curried @knative@ value (partial) — never a by-name string
-- dispatch. This table is the single source of truth for each prim's arity and
-- IO-ness; the native suite catches any drift from the runtime's helpers.
data PrimEntry = PrimEntry !Text !Int !Bool -- ^ C entry point, arity, isIO

primEntries :: Map Text PrimEntry
primEntries = Map.fromList
  [ ("__arrayFromList", PrimEntry "kpf___queryFromList" 1 False)
  , ("__arrayIndexUnsafe", PrimEntry "kpf___arrayIndexUnsafe" 2 False)
  -- MUTABLE-ARRAY-DESIGN §4.1 boxed mutable array.  The forall (e a) is Q0 and
  -- dropped by eraseQ0ArgsP before codegen, so the entry sees only value args.
  -- __arrayLen is PURE (isIO=False); the three mutators are IO (isIO=True).
  , ("__newArray", PrimEntry "kpf_io___newArray" 2 True)
  , ("__arrayRead", PrimEntry "kpf_io___arrayRead" 2 True)
  , ("__arrayWrite", PrimEntry "kpf_io___arrayWrite" 3 True)
  , ("__arrayLen", PrimEntry "kpf___arrayLen" 1 False)
  , ("__arrayToList", PrimEntry "kpf___queryFromList" 1 False)
  , ("__absurd", PrimEntry "kpf___absurd" 1 False)
  , ("__atomicRepEq", PrimEntry "kpf___atomicRepEq" 2 False)
  -- §29.1 std.atomic: each IO prim enters runtime/atomic.c and performs one
  -- indivisible operation on the boxed AtomicRef cell selected by std.atomic's
  -- surface wrapper. The runtime validates the requested memory-order code, but
  -- the current representation is mutex-backed rather than lock-free. isIO=True:
  -- a saturated call becomes a knative_sat suspended action (the op runs when
  -- krun_io fires it); atomics never park, so the synchronous bridge is the
  -- complete path (no CK-machine node). The arities match the prelude prim types
  -- (order + cell + payload).
  , ("__newAtomicRef", PrimEntry "kpf_io___newAtomicRef" 1 True)
  , ("__atomicLoad", PrimEntry "kpf_io___atomicLoad" 2 True)
  , ("__atomicStore", PrimEntry "kpf_io___atomicStore" 3 True)
  , ("__atomicExchange", PrimEntry "kpf_io___atomicExchange" 3 True)
  , ("__atomicCompareExchange", PrimEntry "kpf_io___atomicCompareExchange" 5 True)
  , ("__atomicFetchAdd", PrimEntry "kpf_io___atomicFetchAdd" 3 True)
  , ("__atomicFetchSub", PrimEntry "kpf_io___atomicFetchSub" 3 True)
  , ("__atomicFetchAnd", PrimEntry "kpf_io___atomicFetchAnd" 3 True)
  , ("__atomicFetchOr", PrimEntry "kpf_io___atomicFetchOr" 3 True)
  , ("__atomicFetchXor", PrimEntry "kpf_io___atomicFetchXor" 3 True)
  , ("__byteLength", PrimEntry "kpf___byteLength" 1 False)
  , ("__byteToNat", PrimEntry "kpf___byteToNat" 1 False)
  , ("__bytesAppend", PrimEntry "kpf___bytesAppend" 2 False)
  , ("__bytesBreakIndex", PrimEntry "kpf___bytesBreakIndex" 2 False)
  , ("__bytesBuilderByte", PrimEntry "kpf___bytesBuilderByte" 2 False)
  , ("__bytesBuilderBytes", PrimEntry "kpf___bytesBuilderBytes" 2 False)
  , ("__bytesCompact", PrimEntry "kpf___bytesCompact" 1 False)
  , ("__bytesContains", PrimEntry "kpf___bytesContains" 2 False)
  , ("__bytesDrop", PrimEntry "kpf___bytesDrop" 2 False)
  , ("__bytesEmpty", PrimEntry "kpf___bytesEmpty" 0 False)
  , ("__bytesEndsWith", PrimEntry "kpf___bytesEndsWith" 2 False)
  , ("__bytesFind", PrimEntry "kpf___bytesFind" 2 False)
  , ("__bytesFromList", PrimEntry "kpf___bytesFromList" 1 False)
  , ("__bytesGet", PrimEntry "kpf___bytesGet" 2 False)
  , ("__bytesIndexUnsafe", PrimEntry "kpf___bytesIndexUnsafe" 2 False)
  , ("__bytesIsEmpty", PrimEntry "kpf___bytesIsEmpty" 1 False)
  , ("__bytesLength", PrimEntry "kpf___bytesLength" 1 False)
  , ("__bytesSingleton", PrimEntry "kpf___bytesSingleton" 1 False)
  , ("__bytesSlice", PrimEntry "kpf___bytesSlice" 3 False)
  , ("__bytesStartsWith", PrimEntry "kpf___bytesStartsWith" 2 False)
  , ("__bytesTake", PrimEntry "kpf___bytesTake" 2 False)
  , ("__bytesToList", PrimEntry "kpf___bytesToList" 1 False)
  , ("__caseFold", PrimEntry "kpf___caseFold" 1 False)
  , ("__decodeUtf8Chunk", PrimEntry "kpf___decodeUtf8Chunk" 2 False)
  , ("__decodeUtf8Lossy", PrimEntry "kpf___decodeUtf8Lossy" 1 False)
  , ("__finishBytesBuilder", PrimEntry "kpf___finishBytesBuilder" 1 False)
  , ("__finishStringBuilder", PrimEntry "kpf___finishStringBuilder" 1 False)
  , ("__finishUtf8Decoder", PrimEntry "kpf___finishUtf8Decoder" 1 False)
  , ("__graphemeCount", PrimEntry "kpf___graphemeCount" 1 False)
  , ("__graphemeOfString", PrimEntry "kpf___graphemeOfString" 1 False)
  , ("__graphemeToString", PrimEntry "kpf___graphemeToString" 1 False)
  , ("__graphemeValid", PrimEntry "kpf___graphemeValid" 1 False)
  , ("__hashMixBytes", PrimEntry "kpf___hashMixBytes" 2 False)
  , ("__hashMixDouble", PrimEntry "kpf___hashMixDouble" 2 False)
  , ("__hashMixInt", PrimEntry "kpf___hashMixInt" 2 False)
  , ("__hashMixString", PrimEntry "kpf___hashMixString" 2 False)
  , ("__intAnd", PrimEntry "kpf___intAnd" 2 False)
  , ("__intOr", PrimEntry "kpf___intOr" 2 False)
  , ("__intXor", PrimEntry "kpf___intXor" 2 False)
  , ("__mapFromEntries", PrimEntry "kpf___queryFromList" 1 False)
  , ("__mapToList", PrimEntry "kpf___queryFromList" 1 False)
  , ("__natToByte", PrimEntry "kpf___natToByte" 1 False)
  , ("__newBytesBuilder", PrimEntry "kpf___newBytesBuilder" 0 False)
  , ("__newStringBuilder", PrimEntry "kpf___newStringBuilder" 0 False)
  , ("__newUtf8Decoder", PrimEntry "kpf___newUtf8Decoder" 0 False)
  , ("__normalize", PrimEntry "kpf___normalize" 2 False)
  , ("__queryFromList", PrimEntry "kpf___queryFromList" 1 False)
  , ("__queryToList", PrimEntry "kpf___queryFromList" 1 False)
  , ("__rangeEnum", PrimEntry "kpf___rangeEnum" 3 False)
  , ("__ratDen", PrimEntry "kpf___ratDen" 1 False)
  , ("__ratNum", PrimEntry "kpf___ratNum" 1 False)
  , ("__ratOfInt", PrimEntry "kpf___ratOfInt" 1 False)
  , ("__scalarCount", PrimEntry "kpf___scalarCount" 1 False)
  , ("__scalarInRange", PrimEntry "kpf___scalarInRange" 1 False)
  , ("__scalarOfValue", PrimEntry "kpf___scalarOfValue" 1 False)
  , ("__scalarToString", PrimEntry "kpf___scalarToString" 1 False)
  , ("__setFromList", PrimEntry "kpf___queryFromList" 1 False)
  , ("__setToList", PrimEntry "kpf___queryFromList" 1 False)
  , ("__stringBuilderGrapheme", PrimEntry "kpf___stringBuilderGrapheme" 2 False)
  , ("__stringBuilderScalar", PrimEntry "kpf___stringBuilderScalar" 2 False)
  , ("__stringBuilderString", PrimEntry "kpf___stringBuilderString" 2 False)
  , ("__stringCompact", PrimEntry "kpf___queryFromList" 1 False)
  , ("__stringCursorOffset", PrimEntry "kpf___stringCursorOffset" 2 False)
  , ("__stringEnd", PrimEntry "kpf___stringEnd" 1 False)
  , ("__stringGraphemes", PrimEntry "kpf___stringGraphemes" 1 False)
  , ("__stringNextGrapheme", PrimEntry "kpf___stringNextGrapheme" 2 False)
  , ("__stringNextScalar", PrimEntry "kpf___stringNextScalar" 2 False)
  , ("__stringPrevScalar", PrimEntry "kpf___stringPrevScalar" 2 False)
  , ("__stringScalars", PrimEntry "kpf___stringScalars" 1 False)
  , ("__stringSentences", PrimEntry "kpf___stringSentences" 1 False)
  , ("__stringSpan", PrimEntry "kpf___stringSpan" 3 False)
  , ("__stringStart", PrimEntry "kpf___stringStart" 1 False)
  , ("__stringWords", PrimEntry "kpf___stringWords" 1 False)
  , ("__transport", PrimEntry "kpf___queryFromList" 1 False)
  , ("__uniScalarValue", PrimEntry "kpf___uniScalarValue" 1 False)
  , ("__utf8Bytes", PrimEntry "kpf___utf8Bytes" 1 False)
  , ("__utf8Valid", PrimEntry "kpf___utf8Valid" 1 False)
  , ("acos", PrimEntry "kpf_acos" 1 False)
  , ("addDouble", PrimEntry "kpf_addDouble" 2 False)
  , ("addInt", PrimEntry "kpf_addInt" 2 False)
  , ("addRat", PrimEntry "kpf_addRat" 2 False)
  , ("asin", PrimEntry "kpf_asin" 1 False)
  , ("atan", PrimEntry "kpf_atan" 1 False)
  , ("atan2", PrimEntry "kpf_atan2" 2 False)
  , ("ceil", PrimEntry "kpf_ceil" 1 False)
  , ("cos", PrimEntry "kpf_cos" 1 False)
  , ("divDouble", PrimEntry "kpf_divDouble" 2 False)
  , ("divInt", PrimEntry "kpf_divInt" 2 False)
  , ("divRat", PrimEntry "kpf_divRat" 2 False)
  , ("eqByte", PrimEntry "kpf_eqByte" 2 False)
  , ("eqBytes", PrimEntry "kpf_eqBytes" 2 False)
  , ("eqDouble", PrimEntry "kpf_eqDouble" 2 False)
  , ("eqGrapheme", PrimEntry "kpf_eqGrapheme" 2 False)
  , ("eqInt", PrimEntry "kpf_eqInt" 2 False)
  , ("eqRat", PrimEntry "kpf_eqRat" 2 False)
  , ("eqScalar", PrimEntry "kpf_eqScalar" 2 False)
  , ("eqStr", PrimEntry "kpf_eqStr" 2 False)
  , ("exp", PrimEntry "kpf_exp" 1 False)
  , ("fabs", PrimEntry "kpf_fabs" 1 False)
  , ("floatEq", PrimEntry "kpf_floatEq" 2 False)
  , ("floor", PrimEntry "kpf_floor" 1 False)
  , ("intToDouble", PrimEntry "kpf_intToDouble" 1 False)
  , ("intToNat", PrimEntry "kpf_intToNat" 1 False)
  , ("ioBind", PrimEntry "kpf_io_ioBind" 2 True)
  , ("ioPure", PrimEntry "kpf_io_ioPure" 1 True)
  , ("ioThen", PrimEntry "kpf_io_ioThen" 2 True)
  , ("throwIO", PrimEntry "kpf_io_throwIO" 1 True)
  , ("catchIO", PrimEntry "kpf_io_catchIO" 2 True)
  , ("finallyIO", PrimEntry "kpf_io_finallyIO" 2 True)
  -- §18.1.11 source-level blocking bridge. Saturated calls lower directly to
  -- krt2_blocking; this wrapper keeps a first-class/partially-applied
  -- `blocking` value semantically identical.
  , ("blocking", PrimEntry "kpf_blocking" 1 False)
  -- §12.4.3 first-class borrowed views (runtime borrow = value)
  , ("captureBorrow", PrimEntry "kpf_captureBorrow" 1 False)
  , ("withBorrowView", PrimEntry "kpf_withBorrowView" 2 False)
  -- §18.1.21/.22 algebraic-effect handlers (Stage 4a): lower to the kappart2
  -- CK-machine nodes so a handler clause runs ON the scheduler and may park —
  -- `__handleEff` installs a KK_HANDLER prompt (OP_HANDLE), `__effBind` is the
  -- monadic bind node (OP_BIND), and `runPure` drives the resulting Eff tree to
  -- its value synchronously (krt2_run_eff).  This replaces the pure free-monad
  -- prims (kpf___handleEff/kpf___effBind/kpf_runPure, which cannot park).  The
  -- `__EffOp`/`__EffPure` tree nodes are interpreted directly by fiber_step.
  , ("runPure", PrimEntry "kpf_run_eff" 1 False)
  , ("__effBind", PrimEntry "kpf_eff_bind" 2 False)
  , ("__handleEff", PrimEntry "kpf_rt_handle" 5 False)
  , ("__effDoscope", PrimEntry "kpf_eff_doscope" 1 False)
  , ("__effDefer", PrimEntry "kpf_eff_defer" 1 False)
  , ("leInt", PrimEntry "kpf_leInt" 2 False)
  , ("log", PrimEntry "kpf_log" 1 False)
  , ("ltByte", PrimEntry "kpf_ltByte" 2 False)
  , ("ltBytes", PrimEntry "kpf_ltBytes" 2 False)
  , ("ltDouble", PrimEntry "kpf_ltDouble" 2 False)
  , ("ltInt", PrimEntry "kpf_ltInt" 2 False)
  , ("ltRat", PrimEntry "kpf_ltRat" 2 False)
  , ("ltScalar", PrimEntry "kpf_ltScalar" 2 False)
  , ("ltStr", PrimEntry "kpf_ltStr" 2 False)
  , ("modInt", PrimEntry "kpf_modInt" 2 False)
  , ("mulDouble", PrimEntry "kpf_mulDouble" 2 False)
  , ("mulInt", PrimEntry "kpf_mulInt" 2 False)
  , ("mulRat", PrimEntry "kpf_mulRat" 2 False)
  , ("natOfInt", PrimEntry "kpf_natToInt" 1 False)
  , ("natToInt", PrimEntry "kpf_natToInt" 1 False)
  , ("negDouble", PrimEntry "kpf_negDouble" 1 False)
  , ("negInt", PrimEntry "kpf_negInt" 1 False)
  -- §18.1.6 Duration constructors (pure Int -> nanosecond Int)
    -- §18.1 Duration/Instant arithmetic = signed-ns Int add/sub (reuse kp_addInt/subInt)
  , ("__nowNanos", PrimEntry "kpf_now" 0 True) -- UIO Instant: reads the monotonic clock
  , ("negRat", PrimEntry "kpf_negRat" 1 False)
  , ("__ioNewRef", PrimEntry "kpf_io_newRef" 1 True)
  , ("pow", PrimEntry "kpf_pow" 2 False)
  , ("primitiveIntToString", PrimEntry "kpf_primitiveIntToString" 1 False)
  , ("printString", PrimEntry "kpf_io_printString" 1 True)
  , ("printlnString", PrimEntry "kpf_io_printlnString" 1 True)
  , ("ratOfDouble", PrimEntry "kpf_ratOfDouble" 1 False)
  , ("__ioReadRef", PrimEntry "kpf_io_readRef" 1 True)
  , ("showByte", PrimEntry "kpf_showByte" 1 False)
  , ("showBytes", PrimEntry "kpf_showBytes" 1 False)
  , ("showDouble", PrimEntry "kpf_showDouble" 1 False)
  , ("showFixed", PrimEntry "kpf_showFixed" 2 False)
  , ("showGrapheme", PrimEntry "kpf_showGrapheme" 1 False)
  , ("showInt", PrimEntry "kpf_showInt" 1 False)
  , ("showRat", PrimEntry "kpf_showRat" 1 False)
  , ("showScalar", PrimEntry "kpf_showScalar" 1 False)
  , ("showStringLit", PrimEntry "kpf_showStringLit" 1 False)
  , ("sin", PrimEntry "kpf_sin" 1 False)
  , ("sqrt", PrimEntry "kpf_sqrt" 1 False)
  , ("stringAppend", PrimEntry "kpf_stringAppend" 2 False)
  , ("subDouble", PrimEntry "kpf_subDouble" 2 False)
  , ("subInt", PrimEntry "kpf_subInt" 2 False)
  , ("subRat", PrimEntry "kpf_subRat" 2 False)
  , ("tan", PrimEntry "kpf_tan" 1 False)
  , ("unsafeConsume", PrimEntry "kpf_unsafeConsume" 1 False)
  , ("__ioWriteRef", PrimEntry "kpf_io_writeRef" 2 True)
  -- §18.1.4/§18.1.6/§18.1.9 concurrency node builders (CPS do-kernel): each
  -- lowers to its krt2_* OP_* node so the CK-machine can park on it.  isIO=False
  -- because building the node is pure construction; the node IS the suspended
  -- action the CPS-lowered do-block sequences via krt2_bind.
  , ("__forkRun", PrimEntry "kpf_fork" 1 False)
  , ("__forkDaemon", PrimEntry "kpf_fork_daemon" 1 False)
  , ("__awaitFiber", PrimEntry "kpf_await" 1 False)
  , ("cede", PrimEntry "kpf_cede" 0 False)
  , ("__sleepForNanos", PrimEntry "kpf_sleep_for" 1 False)
  -- §18.1.10 fiber identity: OP_CURRENT_FIBER_ID / OP_FIBER_ID node builders
  -- (need the running fiber's state, so CK-machine driven — see suspendingNames).
  , ("__currentFiberId", PrimEntry "kpf_current_fiber_id" 0 False)
  , ("__fiberId", PrimEntry "kpf_fiber_id" 1 False)
  , ("newPromise", PrimEntry "kpf_new_promise" 0 False)
  , ("completePromise", PrimEntry "kpf_complete_promise" 2 False)
  , ("awaitPromiseExit", PrimEntry "kpf_await_promise_exit" 1 False)
  , ("pollPromise", PrimEntry "kpf_poll_promise" 1 False)       -- §18.11 non-blocking peek
  , ("isDonePromise", PrimEntry "kpf_is_done_promise" 1 False)
  -- §18.1.7 FiberRef cells: get/set/new/modify lower to OP_*_FIBER_REF nodes.
  , ("newFiberRef", PrimEntry "kpf_new_fiber_ref" 1 False)
  , ("getFiberRef", PrimEntry "kpf_get_fiber_ref" 1 False)
  , ("setFiberRef", PrimEntry "kpf_set_fiber_ref" 2 False)
  , ("modifyFiberRef", PrimEntry "kpf_modify_fiber_ref" 2 False)
  -- §18.1.8 structured scopes + monitors (Stage 3)
  , ("newScope", PrimEntry "kpf_new_scope" 0 False)
  , ("forkIn", PrimEntry "kpf_fork_in" 2 False)
  , ("shutdownScope", PrimEntry "kpf_shutdown_scope" 1 False)
  , ("monitor", PrimEntry "kpf_monitor" 1 False)
  , ("awaitMonitor", PrimEntry "kpf_await_monitor" 1 False)
  , ("demonitor", PrimEntry "kpf_demonitor" 1 True) -- §18.1.8 no-op -> Unit

  -- §18.1.13 STM (journaled): newTVar/readTVar/writeTVar/atomically/stmBind/
  -- stmPure are STM_* / OP_ATOMICALLY node-builders (compileAppGlob); check is a
  -- .kp def. Only `retry` keeps a primEntry — it is nullary (no explicit args, so
  -- it never reaches the compileAppGlob spine), and fires kpf_retry immediately
  -- to yield the STM_RETRY node.
  , ("retry", PrimEntry "kpf_retry" 0 False)
  ]

-- | Internal-consistency problems between the two primitive tables. The
-- saturated fast-path table 'primDirect' (@kp_*@ helpers) must be a subset of
-- the full registry 'primEntries' (@kpf_*@ wrappers, arity, IO-ness): every
-- prim with a direct lowering must also have a registry entry, and the two
-- must agree on arity — otherwise a saturated call and a partial/by-value
-- reference to the same prim would disagree on how many arguments it takes.
-- Reports any 'primDirect' entry missing from the registry, or whose arity
-- disagrees. An empty result means the tables are consistent. Surfaced by the
-- pipeline's §28 contract pass, so a drift becomes a reported diagnostic rather
-- than a silent miscompile.
primRegistryDiagnostics :: [Text]
primRegistryDiagnostics =
  [ msg
  | (name, (_, dArity)) <- Map.toList primDirectTable
  , Just msg <- [checkOne name dArity]
  ]
  where
    checkOne name dArity = case Map.lookup name primEntries of
      Nothing ->
        Just ("primDirect '" <> name <> "' has no primEntries registry entry")
      Just (PrimEntry _ eArity _)
        | eArity /= dArity ->
            Just
              ( "primDirect '" <> name <> "' has arity " <> tShow dArity
                  <> " but primEntries records arity " <> tShow eArity
              )
        | otherwise -> Nothing
    tShow :: Show a => a -> Text
    tShow = T.pack . show

-- | QW1: the statically-known saturated pure primitives that have a direct C
-- helper (`kp_…` in the runtime).  A saturated call to one of these is
-- lowered to a direct helper call — no string dispatch, no `prim_arity` /
-- `prim_is_io` check, no per-call argument array.  Maps the primitive name to
-- (helper C name, explicit arity).  These `kp_…` helpers are the runtime's
-- single source of truth for each prim's semantics; the native suite catches
-- any drift between this table and the runtime.  IO / partial / unlisted prims
-- lower to a curried `knative` value instead.
primDirect :: Text -> Maybe (Text, Int)
primDirect = (`Map.lookup` primDirectTable)

-- | The backing table for 'primDirect', kept enumerable so the §28 prim-registry
-- contract check ('primRegistryDiagnostics') can cross-validate every direct
-- entry against the full 'primEntries' registry.
primDirectTable :: Map Text (Text, Int)
primDirectTable = Map.fromList
  [ ("addInt", ("kp_addInt", 2))
  , ("subInt", ("kp_subInt", 2))
  , ("mulInt", ("kp_mulInt", 2))
  , ("divInt", ("kp_divInt", 2))
  , ("modInt", ("kp_modInt", 2))
  , ("negInt", ("kp_negInt", 1))
  , ("eqInt", ("kp_eqInt", 2))
  , ("ltInt", ("kp_ltInt", 2))
  , ("leInt", ("kp_leInt", 2))
  , ("addDouble", ("kp_addDouble", 2))
  , ("subDouble", ("kp_subDouble", 2))
  , ("mulDouble", ("kp_mulDouble", 2))
  , ("divDouble", ("kp_divDouble", 2))
  , ("negDouble", ("kp_negDouble", 1))
  , ("ltDouble", ("kp_ltDouble", 2))
  , ("floatEq", ("kp_floatEq", 2))
  , ("eqDouble", ("kp_eqDouble", 2))
  -- §6.1.7 libm floating-point / transcendental math + fixed-precision format
  , ("sqrt", ("kp_sqrt", 1))
  , ("sin", ("kp_sin", 1))
  , ("cos", ("kp_cos", 1))
  , ("tan", ("kp_tan", 1))
  , ("asin", ("kp_asin", 1))
  , ("acos", ("kp_acos", 1))
  , ("atan", ("kp_atan", 1))
  , ("atan2", ("kp_atan2", 2))
  , ("exp", ("kp_exp", 1))
  , ("log", ("kp_log", 1))
  , ("pow", ("kp_pow", 2))
  , ("floor", ("kp_floor", 1))
  , ("ceil", ("kp_ceil", 1))
  , ("fabs", ("kp_fabs", 1))
  , ("showFixed", ("kp_showFixed", 2))
  , ("stringAppend", ("kp_stringAppend", 2))
  , ("eqStr", ("kp_eqStr", 2))
  , ("ltStr", ("kp_ltStr", 2))
  , ("eqScalar", ("kp_eqScalar", 2))
  , ("ltScalar", ("kp_ltScalar", 2))
  , ("showInt", ("kp_showInt", 1))
  , ("showDouble", ("kp_showDouble", 1))
  , ("showScalar", ("kp_showScalar", 1))
  , ("showStringLit", ("kp_showStringLit", 1))
  , ("intToDouble", ("kp_intToDouble", 1))
  , ("eqByte", ("kp_eqByte", 2))
  , ("ltByte", ("kp_ltByte", 2))
  , ("__intAnd", ("kp_intAnd", 2))
  , ("__intOr", ("kp_intOr", 2))
  , ("__intXor", ("kp_intXor", 2))
  ]

-- | Compile an application spine.  When the spine head is a known runtime
-- primitive, emit a direct helper call ('primDirect') for a saturated pure
-- prim, else a direct call on its C entry point over a stack argument array —
-- the saturated case fires in one call with no intermediate curried
-- partial-application boxes or per-argument allocation (the dominant cost in
-- hot numeric loops).
-- Otherwise fall back to per-argument 'kapp'/'kappi'.
compileApp :: Term -> Gen Text
compileApp term
  -- P0-A: a saturated eta-expanded constructor application is a direct
  -- 'kctor', not a curried closure chain (see 'etaCtorApp'). S2.1 threads the
  -- field args by their CApp-spine origin ('compileEtaCtorApp').
  | Just (g, k, picks) <- etaCtorAppSpine term = compileEtaCtorApp g k picks
compileApp term0 = do
  -- FIX (interp-vs-native): at an ORDINARY-function-global spine, replace each
  -- argument sitting at a 'Q0' (computationally erased, §31.2) telescope position
  -- with a 'CSort' placeholder.  'compileErasableArg' already lowers a 'CSort' to
  -- @kunit()@, so this erases the argument WHOLESALE — regardless of its syntax.
  -- Without it, an erased type-level APPLICATION @f a@ (a 'CApp' over type
  -- variables) survives the purely-syntactic 'isErasableArg' (which only looks
  -- at the spine head) and lowers to a real @kapp(kvar f, kvar a)@ over two
  -- unit-valued slots — the @sequence@/@sequence_@/@for_@/@traverse@-over-IO
  -- crash (@kapp: applying a non-function value@).  Rewriting the term here keeps
  -- EVERY downstream path consistent ('compileAppGlob', 'compileDirectCall' +
  -- 'applyExtra', the prim special-cases, and the 'compileAppDefault' curried
  -- fallback all re-derive from this term / its spine).
  --
  -- ONLY for a NON-erased head (an ordinary defined function global).  For an
  -- erased head — a primitive or a constructor ('isErasedHead') — elaboration
  -- has ALREADY dropped the implicit arguments from the spine, so spine position
  -- k no longer aligns with telescope binder k; erasing by telescope index there
  -- would wrongly unit-out a real EXPLICIT value argument (e.g. the @Eff@ value
  -- and continuation of the @__effBind@ prim, whose @~>@ value binders sit at
  -- telescope positions 3/4 while the spine holds only those two args).  Those
  -- heads never exhibit the type-application bug anyway (their implicit args are
  -- dropped, not lowered), and keep the existing per-arg erasure.
  erasedHd <- isErasedHead term0
  term <-
    if erasedHd
      then pure term0
      else case fst (spineOf term0) of
        CGlob g -> eraseQ0Args g term0
        _ -> pure term0
  let (hd, sargs) = spineOf term
  compileSelectedProjectedPrimitiveApp term >>= \case
    Just e -> pure e
    Nothing -> case hd of
      CGlob g -> do
      -- Perceus RC S2.3 (b.3): validate the callee's owned/borrowed/shared
      -- parameter convention at this CGlob head. Argument materialization happens
      -- at each call argument so selected primitive wrappers can preserve borrowed
      -- handles and own transferred values.
        rcClassifyCallBoundary g
        hostSyms <- gets gsHostSyms
        case Map.lookup g hostSyms of
        -- §27.1.1: a saturated host-member application is a DIRECT native
        -- action — collect the args and build a saturated 'knative_sat'
        -- (the suspended UIO action krun_io fires by calling the emitted
        -- wrapper). A partial application falls through to the curried
        -- bare-reference path (compileGlob → knative + kapp).
          Just rns
            | let arity = length (rns.params)
                  explIxH = [(j, a) | (j, (Expl, a)) <- zip [0 ..] sargs]
            , length explIxH >= arity
            , arity > 0 -> do
                markHostUsed g
                collectHostCtors rns
                -- Perceus RC S2.1: thread each host arg's spine path.
                let kH = length sargs
                ownedFlags <- callArgNeedsOwnedForGlobal g sargs
                aes <-
                  mapM
                    (\(j, a) -> withSpineArg kH j (compileCallArg (flagAt ownedFlags j) a))
                    (take arity explIxH)
                arr <- freshN "na_"
                emit ("KValue *" <> arr <> "[] = {" <> T.intercalate ", " aes <> "};")
                ctor <- hostNativeSatCtor rns
                pure
                  ( ctor <> "(" <> wrapperCName rns <> ", "
                      <> T.pack (show arity) <> ", " <> arr <> ", 1)"
                  )
          _ -> compileAppGlob g sargs term
      _ -> compileAppDefault term

-- | The non-host global application spine (primitive / direct-call / default).
compileAppGlob :: GName -> [(Icit, Term)] -> Term -> Gen Text
compileAppGlob g sargs term = do
      mp <- globPrimName g
      susp <- gets gsSuspenders
      -- Perceus RC S2.1: thread each CK-machine node special-case arg by its TRUE
      -- spine index. A @Monad@-instance prim (ioBind/stmBind/…) carries a LEADING
      -- implicit dictionary/type arg, so the explicit-arg position is NOT the spine
      -- index — 'explIxG' pairs each explicit arg with its real spine index, and
      -- 'peaIx j t' threads that index. Inert under the OFF baseline.
      ownedFlags <- callArgNeedsOwnedForGlobal g sargs
      let kk = length sargs
          explIxG = [(j, a) | (j, (Expl, a)) <- zip [0 ..] sargs]
          peaIx j t = withSpineArg kk j (compileCallArg (flagAt ownedFlags j) t)
      case mp of
        -- §3.1 general CPS: an @ioBind@/@ioThen@ EXPRESSION (not a do-block —
        -- e.g. the prelude @join@/@race@/@timeout@ bodies) whose FIRST action may
        -- suspend becomes a CK-machine bind/then node, so the head action can
        -- park.  The synchronous @kpf_io_ioBind@ bridge cannot park, so a
        -- suspending head there would mis-run; the CDo path is already CPS, this
        -- is the same lowering for the raw @ioBind@ spine.  Gated on §3.3
        -- ('gsSuspenders') — a sequential @ioBind@ stays on the cheap bridge.
        Just "ioBind"
          | [(jm, m), (jk, k)] <- explIxG
          , mayActSuspend susp m -> do
              mc <- peaIx jm m
              kc <- peaIx jk k
              pure ("krt2_bind(" <> mc <> ", " <> kc <> ")")
        Just "ioThen"
          | [(jm, m), (jn, n)] <- explIxG
          , mayActSuspend susp m -> do
              mc <- peaIx jm m
              nc <- peaIx jn n
              pure ("krt2_then(" <> mc <> ", " <> nc <> ")")
        -- §18.1.4 catchIO/finallyIO: ALWAYS the CK-machine node-builder, never
        -- the kpf_io_* bridge.  finallyIO builds krt2_finally = an OP_DOSCOPE tree;
        -- the synchronous bridge can now drive the non-suspending case for legacy
        -- thunks, but source do-blocks that mention these structured-finalizer
        -- nodes are still force-CPS-lowered so ordinary execution goes through the
        -- documented OP_DOSCOPE/OP_DEFER path.  catchIO is grouped with finallyIO
        -- for one uniform path, so a may-suspend body/handler (e.g. `catchIO
        -- (join f) h`) is never mis-run on the bridge.
        Just "catchIO"
          | [(jb, body), (jh, h)] <- explIxG -> do
              bc <- peaIx jb body
              hc <- peaIx jh h
              pure ("krt2_catch(" <> bc <> ", " <> hc <> ")")
        Just "finallyIO"
          | [(jb, body), (jf, fin)] <- explIxG -> do
              bc <- peaIx jb body
              fc <- peaIx jf fin
              pure ("krt2_finally(" <> bc <> ", " <> fc <> ")")
        -- §18.1.4 onExit/onInterrupt: reason-carrying finalizers — run the body,
        -- then on exit run the handler with the reconstructed Exit (onExit, every
        -- exit) or InterruptCause (onInterrupt, only on interrupt).  Always the
        -- CK-machine node (an OP_DOSCOPE tree). The enclosing block is always
        -- CPS-lowered (suspendingNames) so reason-carrying finalizers run on the
        -- do-kernel path, while the sync bridge remains only a non-parking legacy
        -- fallback.
        Just "onExit"
          | [(jb, body), (jh, h)] <- explIxG -> do
              bc <- peaIx jb body
              hc <- peaIx jh h
              pure ("krt2_on_exit(" <> bc <> ", " <> hc <> ")")
        Just "onInterrupt"
          | [(jb, body), (jh, h)] <- explIxG -> do
              bc <- peaIx jb body
              hc <- peaIx jh h
              pure ("krt2_on_interrupt(" <> bc <> ", " <> hc <> ")")
        -- §18.1.7 locallyFiberRef: install `val` for the body's dynamic extent,
        -- restoring on exit (a masked finalizer).  krt2_locally_fiber_ref is a
        -- get/set/finally bind tree the CK-machine drives.
        Just "locallyFiberRef"
          | [(jr, ref), (jv, val), (jb, body)] <- explIxG -> do
              rc <- peaIx jr ref
              vc <- peaIx jv val
              bc <- peaIx jb body
              pure ("krt2_locally_fiber_ref(" <> rc <> ", " <> vc <> ", " <> bc <> ")")
        -- §18.1.4 __reraiseCause: re-raise a captured Cause as-is (the
        -- join/race/timeout failure arms).  A CK-machine OP_RERAISE node (not the
        -- typed-only kfail bridge): catchable iff the cause is a Fail, else it
        -- propagates to the fiber's Failure(cause) outcome (mirrors
        -- Interp.reraiseCauseValue).  These bodies are already CPS (they await),
        -- so the node is always CK-machine-driven.
        Just "__reraiseCause"
          | [(jc, c)] <- explIxG -> do
              cc <- peaIx jc c
              pure ("krt2_reraise(" <> cc <> ")")
        -- §18.1.6 race/timeout: the krt2_race/krt2_timeout node builders (a
        -- krt2_bind tree the CK-machine drives — forks both, awaits the first
        -- signal, interrupts the loser).  The prelude race/timeout bodies are
        -- `ioBind (__race l r) (\o -> match o …)`, so the surrounding ioBind
        -- lowers to krt2_bind (§3.3 has __race/__timeout as suspending).
        Just "__race"
          | [(jl, l), (jr, r)] <- explIxG -> do
              lc <- peaIx jl l
              rc <- peaIx jr r
              pure ("krt2_race(" <> lc <> ", " <> rc <> ")")
        Just "__timeout"
          | [(jd, d), (ji, io)] <- explIxG -> do
              dc <- peaIx jd d
              ic <- peaIx ji io
              pure ("krt2_timeout(" <> dc <> ", " <> ic <> ")")
        -- §19.5 withScope: run a body with a fresh structured scope, shutting it
        -- down on exit (krt2_with_scope is a krt2_bind tree the CK-machine drives).
        Just "withScope"
          | [(ju, use)] <- explIxG -> do
              uc <- peaIx ju use
              pure ("krt2_with_scope(" <> uc <> ")")
        -- §18.1.11 blocking bridge: run the body on the rt-blocking lane.
        Just "blocking"
          | [(jb, body)] <- explIxG -> do
              bc <- peaIx jb body
              pure ("krt2_blocking(" <> bc <> ")")
        -- §18.1.12 masking: the OP_UNINTERRUPTIBLE/OP_MASK/OP_POLL node builders.
        -- `uninterruptible body` raises mask_depth for the body (krt2_uninterruptible);
        -- `mask`'s surface wrapper forwards to `__mask f`, which the runtime applies
        -- to its `restore` closure (krt2_mask); `poll` is the explicit checkpoint
        -- (krt2_poll). All are CK-machine nodes driven by the do-kernel.
        Just "uninterruptible"
          | [(jb, body)] <- explIxG -> do
              bc <- peaIx jb body
              pure ("krt2_uninterruptible(" <> bc <> ")")
        Just "__mask"
          | [(jf, f)] <- explIxG -> do
              fc <- peaIx jf f
              pure ("krt2_mask(" <> fc <> ")")
        -- §18.1.12 rank-2 adapter: `__restoreAt raw act` re-applies the raw 1-arg
        -- runtime restore closure to `act`. The source rank-2-ness is honored at
        -- the use site (a kunit-filled type slot on the surrounding wrapper, see
        -- Prelude `__restoreAt`/`mask`); HERE the prim's own type args are already
        -- erased from the spine, so the two explicit operands lower to a plain
        -- `kapp(raw, act)` — NO `kappi` — exactly the 1-arg runtime call. Both
        -- operands are runtime values (a closure and an IO action), so they are
        -- compiled, not erased.
        Just "__restoreAt"
          | [(jraw, raw), (jact, act)] <- explIxG -> do
              rawc <- withSpineArg kk jraw (compileOwnedResult (flagAt ownedFlags jraw) raw)
              actc <- withSpineArg kk jact (compileOwnedResult (flagAt ownedFlags jact) act)
              pure ("kapp(" <> rawc <> ", " <> actc <> ")")
        Just "poll"
          | null [a | (Expl, a) <- sargs] -> pure "krt2_poll()"
        -- §18.1.4 interruption: __interruptWait (request + await termination) and
        -- __interruptNoWait (request, return at once) — OP_INTERRUPT[_FORK] nodes.
        Just "__interruptWait"
          | [(jc, cause), (jf, fib)] <- explIxG -> do
              cc <- peaIx jc cause
              fc <- peaIx jf fib
              pure ("krt2_interrupt_as(" <> cc <> ", " <> fc <> ")")
        Just "__interruptNoWait"
          | [(jc, cause), (jf, fib)] <- explIxG -> do
              cc <- peaIx jc cause
              fc <- peaIx jf fib
              pure ("krt2_interrupt_fork_as(" <> cc <> ", " <> fc <> ")")
        -- Same OP_INTERRUPT_FORK node as __interruptNoWait, only differently typed
        -- (free result error channel) — used by `disconnect`'s onInterrupt finalizer.
        Just "__interruptForkAny"
          | [(jc, cause), (jf, fib)] <- explIxG -> do
              cc <- peaIx jc cause
              fc <- peaIx jf fib
              pure ("krt2_interrupt_fork_as(" <> cc <> ", " <> fc <> ")")
        -- §18.1.13 STM: the journaled monad (stm.c).  The STM do-notation
        -- desugars (via Monad STM) to stmBind/stmPure; the TVar ops + retry are
        -- STM_* tree leaves; `atomically` runs the tree in a transaction
        -- (OP_ATOMICALLY) that journals reads/writes, commits, and retry-parks
        -- the fiber on its read TVars (woken on write).  stmBind/atomically are
        -- ALWAYS nodes (STM is never on the synchronous bridge).
        Just "stmBind"
          | [(jm, m), (jk, k)] <- explIxG -> do
              mc <- peaIx jm m
              kc <- peaIx jk k
              pure ("krt2_stm_bind(" <> mc <> ", " <> kc <> ")")
        Just "stmPure"
          | [(jv, v)] <- explIxG -> do
              vc <- peaIx jv v
              pure ("krt2_stm_pure(" <> vc <> ")")
        Just "newTVar"
          | [(jv, v)] <- explIxG -> do
              vc <- peaIx jv v
              pure ("krt2_new_tvar(" <> vc <> ")")
        Just "readTVar"
          | [(jtv, tv)] <- explIxG -> do
              tc <- peaIx jtv tv
              pure ("krt2_read_tvar(" <> tc <> ")")
        Just "writeTVar"
          | [(jtv, tv), (jv, v)] <- explIxG -> do
              tc <- peaIx jtv tv
              vc <- peaIx jv v
              pure ("krt2_write_tvar(" <> tc <> ", " <> vc <> ")")
        Just "atomically"
          | [(js, s)] <- explIxG -> do
              sc <- peaIx js s
              pure ("krt2_atomically(" <> sc <> ")")
        Just pname | explIx@(_ : _) <- [(j, a) | (j, (Expl, a)) <- zip [0 ..] sargs] ->
          case Map.lookup pname primEntries of
            -- §34.5.3: a saturated builtin lowers to a DIRECT call on its C
            -- entry point — no string dispatch. A pure builtin: the QW1
            -- positional fast path ('primDirect', no argument array) when
            -- available, else a direct @kpf_x(arr)@. An IO builtin: a
            -- saturated @knative_sat@ (the suspended action krun_io fires by
            -- calling the entry point). Partial / over-application falls
            -- through to the curried bare-reference path (emitPrim → knative).
            Just (PrimEntry cfn ar isio) | length explIx == ar -> do
              markPrimUsed pname
              -- Perceus RC S2.1: thread each builtin arg's spine path
              -- ('withSpineArg') so its CVar uses resolve in the analysis
              -- side-table (the @mulInt r r@ / @stringAppend@ arg CVars).
              let k = length sargs
              aes <-
                mapM
                  (\(j, a) -> withSpineArg k j (compileCallArg (flagAt ownedFlags j) a))
                  explIx
              if isio
                then do
                  arr <- freshN "na_"
                  emit ("KValue *" <> arr <> "[] = {" <> T.intercalate ", " aes <> "};")
                  pure ("knative_sat(" <> cfn <> ", " <> T.pack (show ar) <> ", " <> arr <> ", 1)")
                else case primDirect pname of
                  Just (helper, har) | har == ar ->
                    pure (helper <> "(" <> T.intercalate ", " aes <> ")")
                  _ -> do
                    arr <- freshN "pa_"
                    emit ("KValue *" <> arr <> "[] = {" <> T.intercalate ", " aes <> "};")
                    pure (cfn <> "(" <> arr <> ")")
            _ -> compileAppDefault term -- partial / over-applied: curried path
        Just _ -> compileAppDefault term -- prim with no explicit args yet
        Nothing -> do
          ar <- globFuncArity g
          case ar of
            Just n | length sargs >= n -> compileDirectCall g n sargs
            _ -> compileAppDefault term

-- | The worker arity of a function global @g@ — its leading-lambda count,
-- if @g@ has a recorded core body that is lowered to a worker (≥ 1 binder
-- via 'compileFunctionGlobal').  'Nothing' for CAFs, primitives, and
-- constructors (which have no worker to call directly).
globFuncArity :: GName -> Gen (Maybe Int)
globFuncArity g = do
  bodies <- gets gsBodies
  pure $ case Map.lookup g bodies of
    Just tm | (n, _) <- funcArity tm, n >= 1 -> Just n
    _ -> Nothing

-- | Can the boxed worker for @g@ (arity @n@, recorded body @body@) EVER return
-- a @K_BOUNCE@?  A worker returns a bounce only from a tail-position general
-- application ('emitTailApp's @kbounce@) — a tail @CApp Expl@ whose head is not
-- a prim, not a saturated self-call (which loops in place), and not an
-- eta-expanded constructor (which builds a value, R1.1).  Self-loops, leaf
-- values, prim/ctor results, the IO do-kernel (which returns @K_IOTAIL@
-- markers, NOT bounces), and @if@/@match@/@let@ over those never bounce.
-- Conservative: anything not provably bounce-free counts as may-bounce.  When
-- 'False', a saturated call can drop the 'ktrampoline' wrapper, since
-- @ktrampoline@ drains only @K_BOUNCE@ and passes every other value through
-- untouched — so @ktrampoline(kw_g(…)) ≡ kw_g(…)@ for a non-bouncing worker
-- (P1-E / R3.1).
--
-- This is the dual of 'emitTailApp': it must classify a tail position as
-- "bounces" exactly when 'emitTailApp' would emit @return kbounce(…)@ for it.
-- The two are coupled — if 'emitTailApp' grows a new @kbounce@ arm, this
-- analysis must grow with it or it becomes UNSOUND (a dropped trampoline is a
-- stack overflow at scale).  'consume' reaches a worker's tail positions
-- through @if@/@match@/@let@; only a tail @CApp Expl@ that is not a saturated
-- self-call (loops), a prim spine, or an eta-ctor (a value) actually bounces.
--
-- Lowered-IR implication: a function carries a "tail-call/bounce effect" bit;
-- a call to a callee with no such effect needs no trampoline drain (it lowers
-- to a direct call), realizing the §7 "trampolines → loop/musttail/direct vs
-- boxed-trampoline fallback" requirement for the non-bouncing case.
--
-- Cache invariant: during one 'generateC' run, 'gsBodies' is immutable and
-- each @(GName, arity)@ denotes a single worker body.  The cache key can
-- therefore omit the 'body' argument; it is still passed explicitly so callers
-- that have already looked up the body do not repeat that lookup.
workerMayBounce :: GName -> Int -> Term -> Gen Bool
workerMayBounce g n body = do
  memo <- gets gsBounceMemo
  case Map.lookup (g, n) memo of
    Just (Just b) -> pure b
    Just Nothing -> pure True
    Nothing -> do
      modify' $ \st -> st {gsBounceMemo = Map.insert (g, n) Nothing (gsBounceMemo st)}
      b <- workerMayBounceUncached g n body
      modify' $ \st -> st {gsBounceMemo = Map.insert (g, n) (Just b) (gsBounceMemo st)}
      pure b

workerMayBounceUncached :: GName -> Int -> Term -> Gen Bool
workerMayBounceUncached g n = tailMay
  where
    tailMay term = case term of
      CIf _ t e -> orM [tailMay t, tailMay e]
      CMatch _ _ alts -> orM [tailMay b | CaseAlt _ _ b <- alts]
      CLet _ _ _ _ body -> tailMay body
      CLetRec _ _ _ _ body -> tailMay body
      _
        -- a saturated self-call loops in place; 'lr1SelfArgs' is the shared
        -- recognizer (explicit-arg count == n) — intentionally stricter than
        -- 'selfTailArgs' (full-spine count), which only ever makes this MORE
        -- conservative (keeps a trampoline), never unsound.
        | Just _ <- lr1SelfArgs g n term -> pure False
        | CApp Expl _ _ <- term -> do
            let (hd, _) = spineOf term
            prim <- case hd of CGlob h -> globPrimName h; _ -> pure Nothing
            pure $ case (prim, etaCtorApp term) of
              (Nothing, Nothing) -> True -- a general tail call → kbounce
              _ -> False -- prim spine / eta-ctor → returns a value
        | otherwise -> pure False -- a leaf value / IO action (no bounce)

-- | A saturated (or over-saturated) call to a known function global: call
-- its worker @kw_…@ directly with the leading @n@ arguments instead of
-- building and draining a curried arity-1 closure chain.  The worker's result
-- is driven through 'ktrampoline' ONLY when its body can return a tail-call
-- bounce ('workerMayBounce'); a provably non-bouncing worker is called
-- directly (R3.1).  Any surplus arguments are then applied normally.
-- Type-level/staging arguments are erased (§31.2).
compileDirectCall :: GName -> Int -> [(Icit, Term)] -> Gen Text
compileDirectCall g n sargs = do
  enqueue g
  mplan <- scalarPlan g
  case mplan of
    -- LR1/R2.2: an exactly-saturated call to a scalar-eligible worker takes the
    -- unboxed fast path (with a boxed escape).  Surplus args / partial calls
    -- keep the boxed worker.
    Just (mask, pks, ret, _)
      | length sargs == length mask
      , let runtimeIdxs = [i | (i, keep) <- zip [0 :: Int ..] mask, keep]
      , length runtimeIdxs == length pks ->
          compileScalarCall g pks ret sargs runtimeIdxs
    _ -> do
      let k = length sargs
          (callArgs, extra) = splitAt n sargs
          worker = "kw_" <> mangle (gKey g)
      ownedFlags <- callArgNeedsOwnedForGlobal g sargs
      -- Perceus RC S2.1: thread each saturating argument's nested-CApp spine path
      -- ('withSpineArg') so its CVar uses resolve in the analysis side-table.
      aes <-
        mapM
          (\(j, (_, a)) -> withSpineArg k j (compileCallArg (flagAt ownedFlags j) a))
          (zip [0 ..] callArgs)
      bodies <- gets gsBodies
      mayBounce <- case Map.lookup g bodies of
        Just body | (_, inner) <- funcArity body -> workerMayBounce g n inner
        Nothing -> pure True -- no recorded body → keep the trampoline
      let call = worker <> "(" <> T.intercalate ", " aes <> ")"
          base = if mayBounce then "ktrampoline(" <> call <> ")" else call
      -- the surplus (over-application) args follow the call at spine indices n..k-1.
      foldM (applyExtra k) base (zip [n ..] extra)
  where
    applyExtra k acc (j, (Expl, a)) = do
      ae <- withSpineArg k j (compileCallArg True a)
      pure ("kapp(" <> acc <> ", " <> ae <> ")")
    applyExtra k acc (j, (Impl, a)) = do
      ae <- withSpineArg k j (compileErasableArg a)
      pure ("kappi(" <> acc <> ", " <> ae <> ")")

-- | The general curried application lowering (one 'kapp'/'kappi' per arg).
compileAppDefault :: Term -> Gen Text
compileAppDefault = \case
  -- Perceus RC S2.1: this curried fallback recurses through the CApp structure
  -- itself, so threading head/arg at the shared 'appHeadPos'/'appArgPos' here
  -- reproduces the analysis walk's nested-CApp path exactly (no separate spine
  -- index bookkeeping needed). Inert under the OFF baseline.
  CApp Expl f a -> do
    fe <- withChild P.appHeadPos (compile f)
    ae <- withChild P.appArgPos (compileCallArg True a) -- §31.2: an explicit type-level/staging arg is erased
    pure ("kapp(" <> fe <> ", " <> ae <> ")")
  CApp Impl f a -> do
    erased <- isErasedHead f
    if erased
      then withChild P.appHeadPos (compile f) -- implicit arg to a prim/constructor: erased (§31.2)
      else do
        fe <- withChild P.appHeadPos (compile f)
        ae <- withChild P.appArgPos (compileErasableArg a)
        pure ("kappi(" <> fe <> ", " <> ae <> ")")
  t -> compile t

compileGlob :: GName -> Gen Text
compileGlob g@(GName m nm)
  | m == primModule = emitPrim nm
  | otherwise = do
      globals <- gets gsGlobals
      ctors <- gets gsCtors
      hostSyms <- gets gsHostSyms
      case Map.lookup g globals of
        -- A prelude `prim` registration: its value is a bare VPrim, so it
        -- maps directly to the runtime primitive of the same name.
        Just gd | Just (VPrim pname _) <- gdValue gd ->
          emitPrim pname
        -- §27.1.1: a provided host-binding member (an abstract global of a
        -- manifest-selected `host.native.*` module) lowers to a curried
        -- native action carrying the codegen-emitted wrapper pointer — a
        -- DIRECT typed call, no runtime name dispatch. The wrapper + extern
        -- prototype are emitted by 'assemble' for each used member. The
        -- gname→symbol map is built per build from the manifest's native
        -- bindings (never a hardcoded catalog).
        Just gd
          | Nothing <- gdValue gd
          , Just rns <- Map.lookup g hostSyms ->
              emitHostNative g rns
        _ -> case Map.lookup g ctors of
          Just ci ->
            -- A nullary constructor used as a value builds directly (the
            -- 'Repr.LayoutImmediate' / @b010@ case). A positive-arity
            -- constructor reference is eta-expanded to a saturated CCtor under
            -- lambdas by elaboration (§10.1 etaCtor), so a bare positive-arity
            -- ctor never reaches codegen for an accepted program; treat it as
            -- an internal invariant.
            case Repr.ctorLayoutByArity (length (ciFields ci)) of
              Repr.LayoutImmediate -> do
                tc <- ctorTagConst g
                pure ("kctor0(" <> tc <> ", " <> cStr (gKey g) <> ")")
              _ -> escalated "bare-ctor"
                ("constructor '" <> nm <> "' is referenced un-eta-expanded; \
                 \accepted programs eta-expand constructor values (§10.1)")
          Nothing -> do
            enqueue g
            pure (cGlobIdent g <> "()")

compileLit :: Literal -> Gen Text
compileLit = \case
  LitInt n
    | n >= toInteger (minBound :: Int) && n <= toInteger (maxBound :: Int) ->
        pure ("kint(" <> intLit n <> ")")
    -- §6: Integer is unbounded; a literal beyond int64 is a runtime bignum.
    | otherwise -> pure ("kbigint_str(" <> cStr (T.pack (show n)) <> ")")
  LitDouble d -> pure ("kdbl(" <> T.pack (show d) <> ")")
  LitStr s -> pure (cStrL s)
  LitScalar c -> pure ("kchr(" <> T.pack (show (ord c)) <> ")")
  -- §6.5 byte literal: a single octet.
  LitByte w -> pure ("kbyte(" <> T.pack (show (fromIntegral w :: Int)) <> ")")
  -- §29.5 byte-sequence literal: the exact byte content.  kbytes copies the
  -- bytes into GC memory, so a block-scoped compound literal is safe.
  LitBytes bs -> pure (cBytesLit bs)
  -- §6.5 grapheme literal: an exact scalar sequence rendered as UTF-8 text.
  LitGrapheme g -> pure (cStrL g)
  where
    intLit = cIntLit

-- | A C @int64_t@ literal for an in-range integer.  @INT64_MIN@ has no
-- positive counterpart in C (its magnitude overflows @long long@), so it
-- is emitted via the @<stdint.h>@ macro rather than @(-9223372036854775808LL)@.
cIntLit :: Integer -> Text
cIntLit n
  | n == toInteger (minBound :: Int) = "INT64_MIN"
  | n < 0 = "(-" <> T.pack (show (abs n)) <> "LL)"
  | otherwise = T.pack (show n) <> "LL"

-- | A C @double@ literal, using the SAME shortest round-trippable text as the
-- boxed @kdbl@ path (so the unboxed and boxed paths parse to the identical
-- double).  A source @LitDouble@ is finite, so 'show' never yields
-- Infinity/NaN, and Haskell's @Double@ 'show' always includes a @.@ or @e@, so
-- the text is always a valid C floating (double) literal.
cDblLit :: Double -> Text
cDblLit = T.pack . show

-- | A §29.5 byte-sequence literal.  @kbytes@ copies its input into GC
-- memory, so a block-scoped compound literal of @unsigned char@ is safe;
-- the empty sequence avoids a zero-length array (ill-formed in ISO C).
cBytesLit :: ByteString -> Text
cBytesLit bs
  | BS.null bs = "kbytes((const unsigned char *)\"\", 0)"
  | otherwise =
      "kbytes((const unsigned char[]){"
        <> T.intercalate "," [T.pack (show (fromIntegral w :: Int)) | w <- BS.unpack bs]
        <> "}, "
        <> T.pack (show (BS.length bs))
        <> ")"

-- | A lambda: lift its body into a fresh top-level closure function and
-- return a @kclo@ capturing the current environment.
compileLam :: Term -> Gen Text
compileLam body = do
  fnName <- freshFn "kfn_"
  env <- gets gsEnv -- the captured environment at closure creation
  -- The body is compiled in the 'SinkBounce' tail sink so a tail-position
  -- application (e.g. the recursive call of a local @let rec@ lambda) defers to
  -- the driving trampoline (§27.5A.3) rather than recursing in the C stack.
  --
  -- R3.2 FLAT CLOSURE: when the body is capture-free (no nested closure/thunk/do
  -- captures the parameter by reference), the parameter is read DIRECTLY as the
  -- C argument @arg@ (de Bruijn 0, via 'gsParamLvals') and let/match locals are
  -- flat C locals — NO per-application @kpush(arg, cenv)@.  Captured free vars
  -- (de Bruijn ≥ 1) are read from @cenv@ via the shifted 'CVar' fallback.  When
  -- the body captures the env, the parameter must live in a real @KEnv@ (a
  -- nested closure captures it by reference), so build @kpush(arg, cenv)@ as
  -- before and read everything via it (gsParamLvals empty).
  let flat = not (bodyCapturesEnv body)
  saved <- gets gsParamLvals
  savedBinders <- gets gsParamBinders
  savedOwns <- gets gsParamOwns
  savedTopFlat <- gets gsTopFlatFrame
  bid <- currentBinderIdHere
  bodyEnv <- if flat then pure "cenv" else freshN "lenv_"
  modify' $ \st ->
    st
      { gsParamLvals = if flat then ["arg"] else []
      , gsParamBinders = if flat then [Just bid] else []
      , gsParamOwns = if flat then [False] else []
      , gsTopFlatFrame = False
      }
  -- Perceus RC S2.1: the lambda body sits at 'lamBodyPos' under the CLam node.
  (stmts, ()) <- withChild P.lamBodyPos (captured bodyEnv (consume SinkBounce body))
  modify' $ \st ->
    st
      { gsParamLvals = saved
      , gsParamBinders = savedBinders
      , gsParamOwns = savedOwns
      , gsTopFlatFrame = savedTopFlat
      }
  -- non-flat: materialise kpush(arg, cenv) only when a variable is read (a
  -- constant lambda references neither — keeps the C -Wall clean).
  let usesEnv = (not flat) && any (T.isInfixOf bodyEnv) stmts
      envDecl = ["  KEnv *" <> bodyEnv <> " = kpush(arg, cenv);" | usesEnv]
      fn =
        T.unlines $
          [ "static KValue *" <> fnName <> "(KEnv *cenv, KValue *arg) {"
          , "  (void)cenv; (void)arg;"
          ]
            ++ envDecl
            ++ map ("  " <>) stmts
            ++ [ "}"
               ]
  modify' $ \st ->
    st
      { gsTop = fn : gsTop st
      , gsProtos = ("static KValue *" <> fnName <> "(KEnv *, KValue *);") : gsProtos st
      }
  pure ("kclo(" <> fnName <> ", " <> env <> ")")

compileCtor :: GName -> [Term] -> Gen Text
compileCtor = compileCtorPaths (\i -> withChild (P.ctorArgPos i))

-- | 'compileCtor' parameterised by the per-field PATH wrapper. A genuine 'CCtor'
-- node threads each field at 'ctorArgPos' (the default 'compileCtor'); an eta-ctor
-- application beta-reduced to a ctor ('compileEtaCtorApp') threads each field at
-- the original CApp-spine position the analysis walked, so its CVar uses still
-- resolve in the side-table despite the beta-reduction. @argPath i@ wraps the
-- compilation of field @i@ (0-based, FIELD order).
compileCtorPaths :: (Int -> Gen Text -> Gen Text) -> GName -> [Term] -> Gen Text
compileCtorPaths argPath g args = do
  -- §31.2: erase type-level / staging fields to a unit placeholder so the
  -- constructor's runtime arity (and positional projection) is preserved
  -- without compiling a type/quote value (which the interpreter stores but
  -- never inspects).
  argEs <-
    mapM
      (\(i, a) -> argPath i (compileCallArg True a))
      (zip [0 ..] args)
  tc <- ctorTagConst g
  -- KBackendIR Stage 2: the nullary ⇒ canonical @b010@ immediate decision is
  -- 'Repr.ctorLayoutByArity' (shared with the LLVM backend); 'Repr.LayoutImmediate'
  -- lowers to @kctor0@, anything else builds a boxed @kctor@ over its fields.
  case Repr.ctorLayoutByArity (length argEs) of
    Repr.LayoutImmediate -> pure ("kctor0(" <> tc <> ", " <> cStr (gKey g) <> ")")
    _ -> do
      arr <- freshN "args_"
      emit ("KValue *" <> arr <> "[] = {" <> T.intercalate ", " argEs <> "};")
      pure ("kctor(" <> tc <> ", " <> cStr (gKey g) <> ", " <> T.pack (show (length argEs)) <> ", " <> arr <> ")")

compileRecord :: [(Text, Term)] -> Gen Text
compileRecord fs = do
  valEs <-
    mapM
      (\(i, (_, v)) -> withChild (P.recordFieldPos i) (compileCallArg True v))
      (zip [0 ..] fs)
  namesArr <- freshN "rnames_"
  valsArr <- freshN "rvals_"
  let names = T.intercalate ", " [cStr n | (n, _) <- fs]
  -- The names array must outlive this C stack frame: krec stores the
  -- pointer without copying (the field labels are compile-time string
  -- literals), so a record built in a CAF accessor / closure and projected
  -- later would otherwise read a dangling stack array.  Emit it as static.
  emit ("static const char *" <> namesArr <> "[] = {" <> names <> "};")
  emit ("KValue *" <> valsArr <> "[] = {" <> T.intercalate ", " valEs <> "};")
  pure ("krec(" <> T.pack (show (length fs)) <> ", " <> namesArr <> ", " <> valsArr <> ")")

withEnv :: Text -> Gen a -> Gen a
withEnv e act = do
  saved <- gets gsEnv
  modify' $ \g -> g {gsEnv = e}
  r <- act
  modify' $ \g -> g {gsEnv = saved}
  pure r

-- ── Result sinks (shared by if/match/let in both expression and
-- function-body-tail position) ──────────────────────────────────────

-- | The self-recursion context of the function currently being compiled
-- as a worker: a saturated tail call to it becomes a loop instead of a C
-- call (see 'compileFunctionGlobal').
data TailInfo = TailInfo
  { tiName :: !GName -- ^ the worker's own global
  , tiArity :: !Int -- ^ number of leading binders
  , tiSlots :: ![Text] -- ^ the per-parameter update targets, in binder order: the mutable C parameter variables @p0@…@p{n-1}@.  A tail self-call evaluates its new args into temps then reassigns these (FLAT: params are direct C locals; REBUILD: the loop top rebuilds @kw_env@ from the reassigned params)
  }

-- | Where a computed value flows: into a C variable (expression context),
-- out of a worker as its tail result (a top-level function's tail position,
-- where a saturated self-call becomes a loop), or out of a closure/local
-- let-rec lambda body in tail position (where a tail application becomes a
-- trampoline 'kbounce' so local/mutual tail recursion runs in constant C
-- stack, §27.5A.3 — there are no worker params to loop on).
data Sink = SinkVar !Text | SinkOwnedVar !Bool !Text | SinkTail !TailInfo | SinkBounce | SinkCleanup ![Text] !Sink

sinkWithCleanup :: [Text] -> Sink -> Sink
sinkWithCleanup [] sink = sink
sinkWithCleanup ds (SinkCleanup ds' sink) = SinkCleanup (ds <> ds') sink
sinkWithCleanup ds sink = SinkCleanup ds sink

sinkCleanupLines :: Sink -> [Text]
sinkCleanupLines (SinkCleanup ds sink) = ds <> sinkCleanupLines sink
sinkCleanupLines _ = []

sinkHasCleanup :: Sink -> Bool
sinkHasCleanup = not . null . sinkCleanupLines

sinkTailInfo :: Sink -> Maybe TailInfo
sinkTailInfo (SinkTail ti) = Just ti
sinkTailInfo (SinkCleanup _ sink) = sinkTailInfo sink
sinkTailInfo _ = Nothing

sinkIsTail :: Sink -> Bool
sinkIsTail sink = case sinkTailInfo sink of
  Just _ -> True
  Nothing -> False

sinkIsBounce :: Sink -> Bool
sinkIsBounce SinkBounce = True
sinkIsBounce (SinkCleanup _ sink) = sinkIsBounce sink
sinkIsBounce _ = False

sinkNeedsOwnedResult :: Sink -> Bool
sinkNeedsOwnedResult (SinkOwnedVar needOwned _) = needOwned
sinkNeedsOwnedResult (SinkCleanup _ sink) = sinkNeedsOwnedResult sink
sinkNeedsOwnedResult _ = False

sinkStoresBeforeCleanup :: Sink -> Bool
sinkStoresBeforeCleanup (SinkVar _) = True
sinkStoresBeforeCleanup (SinkOwnedVar _ _) = True
sinkStoresBeforeCleanup _ = False

sinkResult :: Sink -> Text -> Gen ()
sinkResult (SinkVar r) e = emit (r <> " = " <> e <> ";")
sinkResult (SinkOwnedVar _ r) e = emit (r <> " = " <> e <> ";")
sinkResult (SinkTail _) e = emit ("return " <> e <> ";")
sinkResult SinkBounce e = emit ("return " <> e <> ";")
sinkResult (SinkCleanup ds sink) e | sinkStoresBeforeCleanup sink = do
  sinkResult sink e
  mapM_ emit ds
sinkResult (SinkCleanup ds sink) e = do
  tmp <- freshN "ret_"
  emit ("KValue *" <> tmp <> " = " <> e <> ";")
  mapM_ emit ds
  sinkResult sink tmp

-- | Does @term@ compile to a CK-machine action NODE (krt2_bind/then/reraise) via
-- 'compileAppGlob's special cases?  In tail position such a node must be RETURNED
-- so the CK-machine drives it next — NOT handed to 'emitTailApp's per-argument
-- trampoline, which compiles the prim head as a bare reference ('emitPrim') and
-- loses the lowering (and rejects @__reraiseCause@, which has no @primEntry@).
cpsNodeApp :: Term -> Gen Bool
cpsNodeApp term = do
  let (hd, sargs) = spineOf term
  case hd of
    CGlob g -> do
      mp <- globPrimName g
      susp <- gets gsSuspenders
      pure $ case (mp, [a | (Expl, a) <- sargs]) of
        (Just "ioBind", [m, _]) -> mayActSuspend susp m
        (Just "ioThen", [m, _]) -> mayActSuspend susp m
        -- §18.1.4: finallyIO/catchIO ALWAYS lower to the krt2_finally/krt2_catch
        -- node-builder (an OP_DOSCOPE / OP_CATCH tree), so in tail position the
        -- node must be RETURNED for the CK-machine to drive — exactly like
        -- onExit/onInterrupt.  (Unconditional, not gated on `mayActSuspend body`:
        -- even though the sync bridge has a non-parking OP_DOSCOPE fallback,
        -- structured finalizers belong on the documented do-kernel path.)
        (Just "catchIO", [_, _]) -> True
        (Just "finallyIO", [_, _]) -> True
        (Just "onExit", [_, _]) -> True
        (Just "onInterrupt", [_, _]) -> True
        (Just "locallyFiberRef", [_, _, _]) -> True
        (Just "__reraiseCause", [_]) -> True
        (Just "__race", [_, _]) -> True
        (Just "__timeout", [_, _]) -> True
        (Just "withScope", [_]) -> True
        (Just "uninterruptible", [_]) -> True
        (Just "__mask", [_]) -> True
        (Just "poll", []) -> True
        (Just "__interruptWait", [_, _]) -> True
        (Just "__interruptNoWait", [_, _]) -> True
        (Just "__interruptForkAny", [_, _]) -> True
        (Just "atomically", [_]) -> True
        (Just "stmBind", [_, _]) -> True
        _ -> False
    _ -> pure False

-- | Compile @term@ so its value flows to @sink@, recursing through the
-- control forms (if/match/let) so that a self-tail-call deep inside a
-- branch is lowered to a loop rather than a recursive C call.  This single
-- traversal serves both expression context ('SinkVar') and the worker's
-- tail position ('SinkTail'), so the two can never drift.
consume :: Sink -> Term -> Gen ()
consume sink term = case term of
  CIf c t e -> consumeIf sink c t e
  CMatch scrut _ alts -> consumeMatch sink scrut alts
  CLet _ _ _ rhs body -> do
    -- erase a type-level / staging binding (e.g. `let t = Int`) to the unit
    -- placeholder (§31.2) rather than compiling it as a value.
    -- Perceus RC S2.1: rhs at 'letRhsPos', body at 'letBodyPos'.
    rhsOwnsLocal <- withChild P.letRhsPos (rcTermProducesOwnedHere rhs)
    re <- withChild P.letRhsPos (compileErasableArgOwned rhsOwnsLocal rhs)
    lvals <- gets gsParamLvals
    if null lvals
      then do
        -- boxed worker: push the binding onto the KEnv chain.
        env <- gets gsEnv
        e2 <- freshN "env_"
        emit ("KEnv *" <> e2 <> " = kpush(" <> re <> ", " <> env <> ");")
        withEnv e2 (withChild P.letBodyPos (consume sink body))
      else do
        -- R2.3-rest FLAT worker: bind a C local (no KEnv); 'bindFlatLocal'
        -- prepends it as de Bruijn index 0 for exactly the lexical body of this
        -- CLet. This explicit scope is required even inside a 'captured' block:
        -- a nested expression let in an RHS must not shift later outer CVar
        -- lookups (for example an enclosing if condition or else branch).
        -- Perceus RC S2.3 (b.4): the let binder's drop decision is taken at the
        -- CLet node (gsPath = the let path → the binder's BinderId), against the
        -- bound C LOCAL (R-flat). The local is dropped only when the analysis says
        -- it is droppable AND the initializer is manifestly owned. Structural
        -- projection results become manifestly owned only where the base-use
        -- side table proves a read from an owned aggregate and codegen emitted
        -- the balancing kdup; unproven call/projection shapes stay leak-biased. Emitted at
        -- the body's NORMAL completion — i.e. only when the body sinks into a
        -- continuing result var ('SinkVar'); in a 'SinkTail'/'SinkBounce' body the
        -- value 'return's, so a trailing drop is unreachable.
        drp0 <- rcBinderDroppableHere
        let drp = drp0 && rhsOwnsLocal
        bid <- currentBinderIdHere
        savedFlat <- saveFlatLocalScope
        lv <- bindFlatLocal "let_" (Just bid) rhsOwnsLocal re
        let bodySink = if drp then sinkWithCleanup ["kdrop(" <> lv <> ");"] sink else sink
        withChild P.letBodyPos (consume bodySink body)
        restoreFlatLocalScope savedFlat
  -- A local recursive let: allocate the binder cell, evaluate the rhs
  -- (a function whose closure captures the cell but does not read it until
  -- applied), then back-patch (docs/NATIVE_BACKEND.md §5).
  CLetRec _ _ _ rhs body -> do
    env <- gets gsEnv
    e2 <- freshN "env_"
    emit ("KEnv *" <> e2 <> " = kpush(kunit(), " <> env <> ");")
    -- Perceus RC S2.1: rhs at 'letRhsPos', body at 'letBodyPos'.
    re <- withEnv e2 (withChild P.letRhsPos (compile rhs))
    emit (e2 <> "->val = " <> re <> ";")
    withEnv e2 (withChild P.letBodyPos (consume sink body))
  _ -> do
    isCps <- cpsNodeApp term
    let fallback
          | sinkIsTail sink
          , CApp Expl _ _ <- term
          , isCps =
              compile term >>= sinkResult sink
          | sinkIsTail sink
          , CApp Expl _ _ <- term
          , sinkHasCleanup sink =
              compile term >>= sinkResult sink
          | sinkIsTail sink
          , CApp Expl _ _ <- term =
              emitTailApp (sinkCleanupLines sink) term
          | sinkIsBounce sink
          , CApp Expl _ _ <- term
          , isCps =
              compile term >>= sinkResult sink
          | sinkIsBounce sink
          , CApp Expl _ _ <- term
          , sinkHasCleanup sink =
              compile term >>= sinkResult sink
          | sinkIsBounce sink
          , CApp Expl _ _ <- term =
              emitTailApp (sinkCleanupLines sink) term
          -- A suspending ioBind/ioThen or __reraiseCause in tail position lowers to a
          -- CK-machine NODE (compileAppGlob): RETURN it so the machine drives it, not
          -- emitTailApp (which would lose the lowering — see 'cpsNodeApp').
          -- Any other tail-position explicit application: return a trampoline
          -- bounce so the chain (mutual recursion, calls through a value, local
          -- let-rec) runs in constant C stack (§27.5A.3); the driving trampoline
          -- is the kapp/kappi at the non-tail site that demanded the value.
          -- A closure / local let-rec lambda body in tail position: the same bounce,
          -- so a tail self-call defers to the driving trampoline (constant C stack).
          | otherwise = do
              e <- compileOwnedResult (sinkHasCleanup sink || sinkNeedsOwnedResult sink) term
              sinkResult sink e
    case sinkTailInfo sink of
      Just ti -> do
        margs <- selfTailArgsForLoop ti term
        case margs of
          -- Direct saturated self-call: loop in the worker (no allocation).
          Just args -> emitTailLoop (sinkCleanupLines sink) ti args
          Nothing -> fallback
      Nothing -> fallback

-- | Compile an if/match/let in expression context: declare a fresh result
-- variable and consume into it.
sinkToExpr :: Term -> Gen Text
sinkToExpr = sinkToExprOwned False

sinkToExprOwned :: Bool -> Term -> Gen Text
sinkToExprOwned needOwned term = do
  r <- freshN "r_"
  emit ("KValue *" <> r <> " = 0;")
  consume (SinkOwnedVar needOwned r) term
  pure r

consumeIf :: Sink -> Term -> Term -> Term -> Gen ()
consumeIf sink c t e = do
  -- Perceus RC S2.1: cond/then/else at 'ifCondPos'/'ifThenPos'/'ifElsePos'.
  ce <- withChild P.ifCondPos (compile c)
  env <- gets gsEnv
  (tStmts, ()) <- withChild P.ifThenPos (captured env (rcEmitBranchDeadDropsHere >> consume sink t))
  (eStmts, ()) <- withChild P.ifElsePos (captured env (rcEmitBranchDeadDropsHere >> consume sink e))
  emit ("if (kas_bool(" <> ce <> ")) {")
  forM_ tStmts (emit . ("  " <>))
  emit "} else {"
  forM_ eStmts (emit . ("  " <>))
  emit "}"

-- ── Pattern matching ─────────────────────────────────────────────────

consumeMatch :: Sink -> Term -> [CaseAlt] -> Gen ()
consumeMatch sink scrut alts = do
  -- Perceus RC S2.3a (§a): decide whether the match owns a reference to the
  -- scrutinee CELL that it must discharge with a per-arm @kdrop(sv)@. Computed
  -- BEFORE compiling the scrutinee (so 'rcUseKindHere' for a 'CVar' scrutinee
  -- reads the same 'matchScrutPos' key the analysis recorded, and so the verdict
  -- is fixed once for every arm). Inert under OFF.
  dropCell <- rcScrutDropDecision scrut
  -- Perceus RC S2.1: the scrutinee sits at 'matchScrutPos' under the CMatch node.
  se <- withChild P.matchScrutPos (compile scrut)
  sv <- freshN "scrut_"
  emit ("KValue *" <> sv <> " = " <> se <> ";")
  env <- gets gsEnv
  done <- freshN "matched_"
  emit ("int " <> done <> " = 0;")
  -- §17.2.3: an or-pattern whose alternatives list the shared binders in a
  -- different order than the first needs a per-alternative de-Bruijn body
  -- permutation; the native backend distributes alternatives over a shared
  -- body and does not perform it, so refuse rather than miscompile. (The
  -- interpreter — the §27 conformance engine — handles this case.)
  forM_ alts $ \(CaseAlt pat _ _) ->
    when (orReordered pat) $
      void $
        unsupported "or-pattern-reordered-binders"
          "an or-pattern alternative that binds the shared names in a different order than the first alternative is not supported by the native backend (use a consistent binder order across alternatives)"
  -- Perceus RC S2.1: the arms sit under 'matchArmsPos', each at 'matchArmPos ai'
  -- by its ORIGINAL alt index 'ai' — the index "Kappa.Ownership"'s 'walkAlts'
  -- keys against. An or-pattern alt 'expandTopOr's into several sub-alts that all
  -- SHARE the original 'ai' (the analysis does not expand), so the arm-body path
  -- still matches; the intra-pattern slot paths of an or-expansion may diverge,
  -- which is a TOLERATED miss (logged, never a wrong binder).
  withChild P.matchArmsPos $
    forM_ (zip [0 ..] alts) $ \(ai, alt) ->
      withChild (P.matchArmPos ai) $
        forM_ (expandTopOr alt) $ \subAlt -> consumeAlt sink sv dropCell env done subAlt
  emit ("if (!" <> done <> ") krt_fail(\"non-exhaustive match\");")

-- | Whether a pattern contains an or-pattern whose alternatives bind the shared
-- names in a non-canonical order (a non-identity permutation on some
-- alternative) — see 'consumeMatch'.
orReordered :: CorePat -> Bool
orReordered = \case
  CPOr ps perms -> any (\pm -> pm /= [0 .. length pm - 1]) perms || any orReordered ps
  CPCtor _ _ ps -> any orReordered ps
  CPTuple ps -> any orReordered ps
  CPRecord fs _ -> any (orReordered . snd) fs
  CPInject _ p -> orReordered p
  CPAs _ p -> orReordered p
  _ -> False

-- | §17.2.3: a top-level or-pattern alternative is equivalent to one
-- alternative per branch (matchPat's firstJust, in order), with the same
-- guard and body. Splitting here lets each branch's variable bindings be
-- handled by the ordinary single-pattern path, so or-patterns that bind
-- variables work without decision-tree compilation.
expandTopOr :: CaseAlt -> [CaseAlt]
expandTopOr (CaseAlt pat g body) = [CaseAlt p g body | p <- distributePat pat]

-- | §17.2.3: expand a pattern into the list of or-free patterns it denotes,
-- distributing every nested 'CPOr' as the Cartesian product over its
-- positions (left-to-right, matching the interpreter's first-match order).
-- Each or-branch binds the same variables, so all expansions share the
-- alternative's guard and body; the resulting or-free patterns are then
-- handled by the ordinary single-pattern test/binding path.
distributePat :: CorePat -> [CorePat]
distributePat = \case
  CPOr ps _ -> concatMap distributePat ps
  CPCtor g nEx ps -> [CPCtor g nEx qs | qs <- mapM distributePat ps]
  CPTuple ps -> [CPTuple qs | qs <- mapM distributePat ps]
  CPRecord fs rest ->
    let (names, pats) = unzip fs
     in [CPRecord (zip names qs) rest | qs <- mapM distributePat pats]
  CPInject t p -> [CPInject t q | q <- distributePat p]
  CPAs n p -> [CPAs n q | q <- distributePat p]
  p -> [p] -- CPWild / CPVar / CPLit / CPInjectRest: no nested or

consumeAlt :: Sink -> Text -> Bool -> Text -> Text -> CaseAlt -> Gen ()
consumeAlt sink sv dropCell env done (CaseAlt pat mguard body) = do
  emit ("if (!" <> done <> ") {")
  -- pattern test + bindings produced as a nested block
  (blk, ()) <- captured env $ do
    mtest <- patTest sv pat
    case mtest of
      Nothing -> consumeAltBody sink sv dropCell env done pat mguard body
      Just test -> do
        emit ("if (" <> test <> ") {")
        consumeAltBody sink sv dropCell env done pat mguard body
        emit "}"
  forM_ blk (emit . ("  " <>))
  emit "}"

-- | Bind the pattern variables, evaluate the optional guard, and on a full
-- match consume the body into the sink (and mark @done@; for a 'SinkTail'
-- body the @done@ store is dead — the body has returned/looped — but
-- harmless).
consumeAltBody :: Sink -> Text -> Bool -> Text -> Text -> CorePat -> Maybe Term -> Term -> Gen ()
consumeAltBody sink sv dropCell env done pat mguard body = do
  -- patTest already verified the constructor/shape; bindings just project.
  -- Perceus RC S2.3a/S3.2 (§a): the cell-drop fires for THIS arm only when the
  -- match owns the scrutinee cell ('dropCell'). S3.2 routes that cleanup through
  -- the sink, so returning 'SinkTail'/'SinkBounce' arms emit the drop before the
  -- return instead of leaving the scrutinee to Boehm.
  -- The kept-field DUP and the cell @kdrop@ are an ATOMIC PAIR: a field projected
  -- via a borrowing 'kctor_arg'/'kproj' (no incref) is dup'd so it survives the
  -- following @kdrop(sv)@ (which S3.2 lets recursively free fields when the cell
  -- is unique).
  -- So the field-dup must fire IFF the cell-drop does — dupping a kept field on an
  -- arm that then skips the cell-drop would be an UNPAIRED dup (a permanent rc
  -- inflation / leak, never balanced). Guarded arms bind fields before evaluating
  -- the guard, so a failed guard cannot run the success-branch balancing drops;
  -- keep guarded arms conservative until guard-failure cleanup is modeled.
  let dropHere = dropCell && maybe True (const False) mguard
  env' <- bindPatScrutDup dropHere sv env pat
  -- Perceus RC S2.3 (b.4, per-arm): decide the drops for this arm's pattern-slot
  -- binders HERE (gsPath = the arm path, so 'patSlotPos k' keys each slot), against
  -- the bound flat C locals (R-flat). These drops only fire with 'dropHere',
  -- because otherwise pattern locals are raw borrowed projections, not dup-owned
  -- fields. The slot's de Bruijn index @k@ is its
  -- 'gsParamLvals' index right after binding (the LAST patBinding is index 0,
  -- matching the analysis's @depth+n-1-k@ levels). Computed BEFORE descending into
  -- the body so the lookup key is the arm path; emitted through the sink cleanup
  -- after normal body evaluation and before any tail return. Boxed (KEnv) arms
  -- have empty 'gsParamLvals' → no flat local → no drop (left to Boehm).
  patDrops <- if dropHere then rcPatSlotDropLvals pat else pure []
  let altCleanup = map (\lv -> "kdrop(" <> lv <> ");") patDrops <> ["kdrop(" <> sv <> ");" | dropHere]
      bodySink = sinkWithCleanup altCleanup sink
  -- Perceus RC S2.1: under the arm path, the guard sits at 'altGuardPos' and the
  -- body at 'altBodyPos' (the pattern-slot binders are at 'patSlotPos k', looked
  -- up only by the binder pass S2.3, not here).
  case mguard of
    Nothing -> do
      rcEmitBranchDeadDropsHere
      withEnv env' (withChild P.altBodyPos (consume bodySink body))
      emit (done <> " = 1;")
    Just gd -> do
      ge <- withEnv env' (withChild P.altGuardPos (compile gd))
      emit ("if (kas_bool(" <> ge <> ")) {")
      rcEmitBranchDeadDropsHere
      withEnv env' (withChild P.altBodyPos (consume bodySink body))
      emit ("  " <> done <> " = 1;")
      emit "}"

-- | Perceus RC S2.3: the bound flat C locals to @kdrop@ for the pattern-slot
-- binders of @pat@ that the analysis says are droppable without a consuming
-- 'LastUse' (b.4/S2.3b/S3.2). Non-consuming projection reads are only allowed
-- to coexist with these drops when the result is materialized as owned at the
-- result site.
-- The slot's de Bruijn index @k@ (0 = innermost, the LAST 'patBindings' entry) is
-- its 'gsParamLvals' index in the just-bound arm scope. Returns @[]@ under the OFF
-- baseline, in a boxed arm (empty 'gsParamLvals' — no flat local to drop against),
-- or for any slot the analysis did not mark droppable-with-no-LastUse.
rcPatSlotDropLvals :: CorePat -> Gen [Text]
rcPatSlotDropLvals pat = do
  enabled <- gets gsRcEnabled
  lvals <- gets gsParamLvals
  if not enabled || null lvals
    then pure []
    else do
      let n = patBindersC pat
      fmap concat $ forM [0 .. n - 1] $ \k -> do
        drp <- rcPatSlotDroppableHere k
        pure [lvals !! k | drp && k < length lvals]

-- | A C boolean expression that is true iff @pat@ matches the value @v@
-- (a pure expression; no side effects, no bindings).  'Nothing' means the
-- pattern always matches (e.g. a variable or wildcard).
patTest :: Text -> CorePat -> Gen (Maybe Text)
patTest v = \case
  CPWild -> pure Nothing
  CPVar _ -> pure Nothing
  CPAs _ p -> patTest v p
  CPLit l -> do
    le <- litValue l
    case le of
      Just lv -> pure (Just ("klit_eq(" <> v <> ", " <> lv <> ")"))
      Nothing -> pure (Just "0") -- unsupported literal: never matches (error already recorded)
  CPCtor g _ ps -> do
    let nps = length ps
    subs <- forM (zip [0 ..] ps) $ \(i, p) ->
      patTest (ctorArgExpr v nps i) p
    -- LR2: dispatch on the numeric ctor identity (int compare) rather than a
    -- kctor_is strcmp.  kctor_tagid returns -1 for a non-ctor scrutinee, so
    -- this preserves the `v->tag == K_CTOR &&` type guard kctor_is carried.
    tc <- ctorTagConst g
    let here = "kctor_tagid(" <> v <> ") == " <> tc
    pure (Just (conj (here : [t | Just t <- subs])))
  CPTuple ps -> do
    let n = length ps
    subs <- forM (zip [0 ..] ps) $ \(i, p) ->
      patTest (recAtExpr v i) p
    let szTest = "krec_size(" <> v <> ") == " <> T.pack (show n)
    pure (Just (conj (szTest : [t | Just t <- subs])))
  -- §17.2.5: a record pattern's rest binder always matches; the named
  -- fields determine the test (with or without a rest binder).
  CPRecord pfs _ -> recordTests v pfs
  CPOr ps _ -> do
    -- Top-level binding or-patterns are split into separate alternatives
    -- before reaching here (see consumeMatch), so any CPOr that arrives is
    -- nested. Non-binding nested ors disjoin their tests; a nested or that
    -- binds variables would need decision-tree compilation.
    if all bindsNothing ps
      then do
        subs <- mapM (patTest v) ps
        pure (Just (disj [maybe "1" id t | t <- subs]))
      else do
        _ <- unsupported "CPOr-nested-binding"
          "a nested or-pattern that binds variables is not supported (lift it to top-level alternatives)"
        pure (Just "0")
  -- §13 variant patterns: tag match + payload sub-test.
  CPInject tag p -> do
    sub <- patTest ("kvariant_payload(" <> v <> ")") p
    -- LR2: numeric variant dispatch (kvariant_tagid -> -1 for a non-variant).
    tc <- variantTagConst tag
    let here = "kvariant_tagid(" <> v <> ") == " <> tc
    pure (Just (conj (here : [t | Just t <- [sub]])))
  -- §13 residual-row pattern: a variant whose tag is none of the excluded.
  CPInjectRest excl -> do
    tcs <- mapM variantTagConst excl
    pure (Just (conj ("kis_variant(" <> v <> ")" : ["kvariant_tagid(" <> v <> ") != " <> tc | tc <- tcs])))
  where
    recordTests rv pfs = do
      subs <- forM pfs $ \(n, p) -> patTest ("kproj(" <> rv <> ", " <> cStr n <> ")") p
      case [t | Just t <- subs] of
        [] -> pure Nothing
        ts -> pure (Just (conj ts))

-- | The C expression for the i-th bound argument of a constructor value
-- @v@ whose pattern binds @nps@ trailing arguments (matchPat drops the
-- leading non-bound arguments).
ctorArgExpr :: Text -> Int -> Int -> Text
ctorArgExpr v nps i =
  "kctor_arg(" <> v <> ", kctor_argc(" <> v <> ") - " <> T.pack (show nps) <> " + " <> T.pack (show i) <> ")"

recAtExpr :: Text -> Int -> Text
recAtExpr v i = "krec_at(" <> v <> ", " <> T.pack (show i) <> ")"

-- | C expression for a §17.2.5 record rest binder: @rec@ minus the named
-- fields, passing the excluded names via a C99 compound literal.
recWithoutExpr :: Text -> [Text] -> Text
recWithoutExpr v names
  | null names = "krec_without(" <> v <> ", 0, 0)"
  | otherwise =
      "krec_without(" <> v <> ", " <> T.pack (show (length names))
        <> ", (const char*[]){" <> T.intercalate ", " (map cStr names) <> "})"

conj :: [Text] -> Text
conj [] = "1"
conj [x] = x
conj xs = "(" <> T.intercalate " && " xs <> ")"

disj :: [Text] -> Text
disj [] = "0"
disj [x] = x
disj xs = "(" <> T.intercalate " || " xs <> ")"

bindsNothing :: CorePat -> Bool
bindsNothing = \case
  CPWild -> True
  CPLit _ -> True
  -- @nEx@ skolem placeholder slots ARE bindings, so a ctor pattern with
  -- existentials does not "bind nothing".
  CPCtor _ nEx ps -> nEx == 0 && all bindsNothing ps
  CPTuple ps -> all bindsNothing ps
  CPOr ps _ -> all bindsNothing ps
  CPInjectRest _ -> True
  _ -> False

-- | The values a pattern binds, as C expressions over the scrutinee
-- expression @sv@, in matchPat's left-to-right binding order (rightmost
-- binder ends up at de Bruijn index 0).
patBindings :: Text -> CorePat -> [Text]
patBindings = go
  where
    go v = \case
      CPWild -> []
      CPLit _ -> []
      CPVar _ -> [v]
      CPAs _ p -> v : go v p
      CPCtor _ nEx ps ->
        -- §17.1: the @nEx@ existential-skolem slots come FIRST, so after the
        -- match path reverses the binding list they land BELOW the field binders
        -- — exactly where 'ctorFieldTypesCtx' bound the skolems. They are erased
        -- types never read at runtime; @kunit()@ is the placeholder (mirrors the
        -- interpreter's 'VRecordV []' and the LLVM backend's unit placeholder).
        let nps = length ps
         in replicate nEx "kunit()"
              ++ concat [go (ctorArgExpr v nps i) p | (i, p) <- zip [0 ..] ps]
      CPTuple ps -> concat [go (recAtExpr v i) p | (i, p) <- zip [0 ..] ps]
      -- §17.2.5: named-field bindings, then (if a non-discard rest binder)
      -- the remaining fields as a narrower record — matchPat's order.
      CPRecord pfs mrest ->
        concat [go ("kproj(" <> v <> ", " <> cStr n <> ")") p | (n, p) <- pfs]
          ++ case mrest of
            Just nm | not (T.null nm) -> [recWithoutExpr v (map fst pfs)]
            _ -> []
      CPOr _ _ -> [] -- only non-binding or-patterns reach here
      -- §13 variant payload / whole-value bindings (matchPat semantics).
      CPInject _ p -> go ("kvariant_payload(" <> v <> ")") p
      CPInjectRest _ -> [v]

litValue :: Literal -> Gen (Maybe Text)
litValue = \case
  LitInt n
    | n >= toInteger (minBound :: Int) && n <= toInteger (maxBound :: Int) ->
        pure (Just ("kint(" <> cIntLit n <> ")"))
    -- §6: an out-of-int64 integer literal pattern is a bignum (klit_eq
    -- compares K_BIGINT via mpz).
    | otherwise -> pure (Just ("kbigint_str(" <> cStr (T.pack (show n)) <> ")"))
  LitStr s -> pure (Just (cStrL s))
  LitScalar c -> pure (Just ("kchr(" <> T.pack (show (ord c)) <> ")"))
  LitDouble d -> pure (Just ("kdbl(" <> T.pack (show d) <> ")"))
  -- §6.5/§29.5 byte/bytes/grapheme literal patterns (klit_eq compares
  -- K_BYTE by octet, K_BYTES by content, grapheme as K_STR by bytes).
  LitByte w -> pure (Just ("kbyte(" <> T.pack (show (fromIntegral w :: Int)) <> ")"))
  LitBytes bs -> pure (Just (cBytesLit bs))
  LitGrapheme g -> pure (Just (cStrL g))

-- ── do-kernel ────────────────────────────────────────────────────────

-- | §18.1 CPS do-kernel (Stage 1).  A do-block whose binds reach a SUSPENDING
-- operation (fork/await/sleepFor/cede/awaitPromiseExit/…) cannot run on the
-- synchronous @krun_io@ bridge — the fiber must be able to park.  Such a block
-- is lowered to a @krt2_*@ action TREE the CK-machine drives node-by-node
-- (parking at OP_FORK/OP_AWAIT/…), instead of a @kio@ do-fn.
--
-- Detection is the CPS-DESIGN §3.3 suspendability analysis: a bind whose action
-- reaches a suspending primitive — directly OR transitively through the call
-- graph ('suspenderGlobals') — may suspend, so the block is CPS-lowered.  This
-- catches a user helper that forks/awaits, not only a literal @fork@/@await@.
-- A suspending op inside a defer/loop/if/var/return block is Stage-2 work and is
-- not yet CPS-lowered ('cpsEligible' is False); such a block is DIAGNOSED
-- (fail-closed in 'compileDo'), not mis-run on the bridge.
-- The wired-and-tested suspending operations, by name.  Only the surface
-- (preludeModule) and prim (primModule) globals are matched — a user global
-- named e.g. @join@/@race@/@timeout@ in another module never triggers CPS.
-- (Stage-3 ops — forkIn/shutdownScope/awaitMonitor — and the derived
-- join/race/timeout are added here as each is wired and tested.)
suspendingNames :: Set Text
suspendingNames =
  Set.fromList
    [ "fork", "forkDaemon", "await", "awaitPromise" -- surface (std.prelude)
    , "__forkRun", "__forkDaemon", "__awaitFiber" -- prims (__prim)
    , "cede"
      -- §18.1.6 clock/timers: the raw prims lower to native IO/OP nodes, and the
      -- std.prelude wrappers are ordinary source heads that can appear directly
      -- in a do item before transitive prelude bodies are available.
    , "nowMonotonic", "__nowNanos", "sleepFor", "sleepUntil", "__sleepForNanos"
    , "newPromise", "completePromise", "awaitPromiseExit"
    , "__race", "__timeout" -- §18.1.6 race/timeout (compile to krt2_race/krt2_timeout nodes)
    , "withScope", "__interruptWait", "__interruptNoWait" -- §19.5/§18.1.4 scope + interruption nodes
    , "blocking" -- §18.1.11 source-level rt-blocking bridge
    , "uninterruptible", "__mask", "poll" -- §18.1.12 masking: OP_UNINTERRUPTIBLE/OP_MASK/OP_POLL nodes
      -- §18.1.8 structured scopes/monitors: not all "suspend" (newScope/forkIn/
      -- monitor build a node; shutdownScope/awaitMonitor park) but all are
      -- CK-machine OP_* nodes, so a block using them must be CPS-lowered.
    , "newScope", "forkIn", "shutdownScope", "monitor", "awaitMonitor"
    , "atomically", "stmBind" -- §18.1.13 STM: atomically retry-parks; stmBind builds the STM tree
      -- §18.1.4 reason-carrying finalizers: structured do-kernel nodes, forced
      -- onto CPS for ordinary do-block execution; the sync bridge is only a
      -- non-parking legacy fallback.
    , "onExit", "onInterrupt"
      -- §18.1.4 finallyIO/catchIO: `finallyIO body fin` lowers to krt2_finally =
      -- krt2_doscope(then(defer fin) body) — an OP_DOSCOPE tree.  Listing them
      -- here force-CPS-lowers any block whose tail/body uses them onto the full
      -- CK-machine path, exactly as onExit/onInterrupt.  The sync bridge has a
      -- non-parking fallback for legacy thunks, but this is the normal lowering.
      -- (catchIO is OP_CATCH, which the bridge *does* drive, but it is grouped with
      -- finallyIO for one uniform CK-machine path: its node builder is now
      -- unconditional too, so a may-suspend handler/body is never mis-run.)
    , "finallyIO", "catchIO"
      -- §18.1.7 FiberRef ops + §18.11 promise peeks: synchronous OP_* nodes, but
      -- they need the current fiber's state (f->locals / promise cell), which the
      -- synchronous krun_io bridge has no handle to — so a block using them is
      -- CPS-lowered to run on the CK-machine.
    , "newFiberRef", "getFiberRef", "setFiberRef", "modifyFiberRef", "locallyFiberRef"
    , "pollPromise", "isDonePromise"
      -- §18.1.10 fiber identity: OP_CURRENT_FIBER_ID/OP_FIBER_ID read the running
      -- fiber's state (f->id), which the synchronous krun_io bridge has no handle
      -- to — so a block using them is CPS-lowered to run on the CK-machine.
    , "currentFiberId", "fiberId" -- surface (std.prelude)
    , "__currentFiberId", "__fiberId" -- prims (__prim)
    ]

-- | Is g one of the suspending / CK-machine primitive ops, by module + name?
-- Only the prelude / __prim globals match — a user global named join/race never does.
isSuspendingPrim :: GName -> Bool
isSuspendingPrim (GName m nm) =
  (m == primModule || m == ModuleName ["std", "prelude"]) && nm `Set.member` suspendingNames

-- | Every global referenced anywhere in a term — the call-graph out-edges used by
-- the §3.3 transitive-suspender closure.
termGlobals :: Term -> Set GName
termGlobals = goT
  where
    goCond = \case
      KCondPure t -> goT t
      KCondAction t -> goT t

    goT t = case t of
      CVar {} -> Set.empty
      CGlob g -> Set.singleton g
      CLam _ _ _ b -> goT b
      CPi _ _ _ _ ty b -> goT ty <> goT b
      CApp _ a b -> goT a <> goT b
      CSort {} -> Set.empty
      CLit {} -> Set.empty
      CCtor g _ args -> Set.insert g (goAll args)
      CMatch s _ alts -> goT s <> mconcat [maybe Set.empty goT (caGuard a) <> goT (caBody a) | a <- alts]
      CRecordT fs -> goAll (map snd fs)
      CRecordV fs -> goAll (map snd fs)
      CProj e _ -> goT e
      CProjAt e _ _ -> goT e
      CVariantT ts -> goAll ts
      CInject _ e -> goT e
      CLet _ _ ty rhs body -> goT ty <> goT rhs <> goT body
      CLetRec _ _ ty rhs body -> goT ty <> goT rhs <> goT body
      CMeta {} -> Set.empty
      CDo _ items -> goItems items
      CSealE _ e -> goT e
      CSigT _ e -> goT e
      CThunkE e -> goT e
      CLazyE e -> goT e
      CForceE e -> goT e
      CIf c th el -> goT c <> goT th <> goT el
      CQuote _ ts -> goAll ts
    goAll = mconcat . map goT
    goItems = mconcat . map goItem
    goItem it = case it of
      KBind _ _ e _ -> goT e
      KLet _ _ e -> goT e
      KLetQ _ e me -> goT e <> maybe Set.empty (goT . snd) me
      KExpr e -> goT e
      KVarItem _ _ actT _ -> goT actT
      KAssign _ _ _ actT _ -> goT actT
      KReturn e -> goT e
      KBreak _ -> Set.empty
      KContinue _ -> Set.empty
      KWhile _ c b me -> goCond c <> goItems b <> maybe Set.empty goItems me
      KFor _ _ s b me -> goT s <> goItems b <> maybe Set.empty goItems me
      KIf alts me -> mconcat [goT c <> goItems b | (c, b) <- alts] <> maybe Set.empty goItems me
      KDefer _ e -> goT e
      KUsing _ a r -> goT a <> goT r
      KSubDo _ items -> goItems items

-- | §3.3 suspendability analysis: the least set of globals that TRANSITIVELY
-- reach a suspending primitive — a global whose body references one directly,
-- calls another such global (closed under the call graph), or returns an @IO@
-- action built by applying a local higher-order parameter in action position.
-- Computed once over all recorded core bodies.  This is the SOUND replacement
-- for the old syntactic spine-head check: it catches a user helper that
-- forks/awaits, and also wrappers such as @withBridge blocking@ where the
-- suspending action transformer is passed as a value.
suspenderGlobals :: Map GName Term -> Set GName
suspenderGlobals = suspenderGlobalsWith Set.empty emptySuspenderCtx Map.empty
  where
    emptySuspenderCtx = EvalCtx (Globals Map.empty) Map.empty False Map.empty

suspenderGlobalsWith :: Set GName -> EvalCtx -> Map GName GlobalDef -> Map GName Term -> Set GName
suspenderGlobalsWith extraSeed ctx globals bodies = fixpoint seed
  where
    refs = Map.map termGlobals bodies
    seed =
      extraSeed
        <> Map.keysSet (Map.filter (any isSuspendingPrim) refs)
        <> Map.keysSet (Map.filterWithKey higherOrderActionWrapper bodies)
    fixpoint s =
      let s' = s <> Map.keysSet (Map.filter (any (`Set.member` s)) refs)
       in if s' == s then s else fixpoint s'

    higherOrderActionWrapper g body =
      globalReturnsIO g && termReturnsLocalHeadedAction body

    globalReturnsIO g =
      maybe False (valueReturnsIO 0 . gdType) (Map.lookup g globals)

    valueReturnsIO lvl ty =
      case force ctx ty of
        VPi _ _ _ _ _ (Closure env body) ->
          valueReturnsIO (lvl + 1) (eval ctx (VRigid lvl [] : env) body)
        VGlobN ioG args ->
          ioG == Builtins.prelIO && length args == 2
        _ -> False

-- | True when a term's returned action can be a parameter-headed call.  This is
-- intentionally narrower than "contains any local call": pure local calls inside
-- an IO-producing helper do not force the helper into the suspender seed unless
-- they appear in an action position.
termReturnsLocalHeadedAction :: Term -> Bool
termReturnsLocalHeadedAction = goTail
  where
    localHead = spineHeadIsLocal
    goTail = \case
      CLam _ _ _ b -> goTail b
      CLet _ _ _ _ body -> goTail body
      CLetRec _ _ _ _ body -> goTail body
      CSealE _ e -> goTail e
      CDo _ items -> any goItem items
      t -> localHead t

    goCond = \case
      KCondPure _ -> False
      KCondAction t -> localHead t || goTail t
    goItems = any goItem
    goItem = \case
      KBind _ _ t _ -> localHead t || goTail t
      KExpr t -> localHead t || goTail t
      KVarItem _ _ t _ -> localHead t || goTail t
      KAssign _ _ _ t _ -> localHead t || goTail t
      KWhile _ c b me -> goCond c || goItems b || maybe False goItems me
      KFor _ _ _ b me -> goItems b || maybe False goItems me
      KIf alts me -> any (goItems . snd) alts || maybe False goItems me
      KDefer _ t -> localHead t || goTail t
      KUsing _ a r -> localHead a || goTail a || localHead r || goTail r
      KSubDo _ b -> goItems b
      _ -> False

blockingHostGlobals :: Map GName ResolvedNativeSymbol -> Set GName
blockingHostGlobals =
  Map.keysSet . Map.filter (isBlockingClass . (.ffiClass))
  where
    isBlockingClass = \case
      FfiNonblocking -> False
      FfiBlocking -> True
      FfiBlockingCancellable -> True

-- | Does this action (its spine head) reach a suspending op?  A suspending prim,
-- or a global in the §3.3 transitive-suspender set.
spineHeadSuspends :: Set GName -> Term -> Bool
spineHeadSuspends susp t = case fst (spineOf t) of
  CGlob g -> isSuspendingPrim g || g `Set.member` susp
  _ -> False

-- | §3.3 higher-order: is this action's spine head a local/parameter (a @CVar@)?
-- Then the action MAY suspend depending on the caller (e.g. @bracketM@'s @use r@,
-- where @use@ is an IO-action parameter).  A combinator over it is CPS-lowered
-- conservatively: the CK-machine drives a sequential local action just fine, and
-- only it can drive a suspending one — whereas the synchronous bridge cannot.
spineHeadIsLocal :: Term -> Bool
spineHeadIsLocal t = case fst (spineOf t) of
  CVar _ -> True
  _ -> False

-- | An action that an IO combinator (ioBind/catchIO/…) must drive through the
-- CK-machine: it either reaches a suspending op (§3.3) or is parameter-headed
-- (higher-order, may-suspend).
mayActSuspend :: Set GName -> Term -> Bool
mayActSuspend susp t = spineHeadSuspends susp t || spineHeadIsLocal t

-- | Does any action in the block (recursively, including loop/if bodies) reach a
-- suspending operation?  When @incLocal@ is 'True' an OPAQUE HIGHER-ORDER call —
-- one whose spine head is a local\/param 'CVar' — also counts as may-suspend
-- (§3.3 / 'spineHeadIsLocal'): the value passed may itself suspend, and — the
-- decisive case — a `restore`\/`mask`-supplied action transformer ALWAYS builds
-- an OP_RESTORE\/OP_MASK node that ONLY the CK-machine can drive (the synchronous
-- krun_io bridge has no OP_RESTORE case, so a legacy do-block binding `restore x`
-- would run the raw node unevaluated — `x` never runs, the result is the node
-- itself).  The strict version (@incLocal@ = 'False') gates the FAIL-CLOSED
-- diagnostic, so a local-headed call there does not newly reject a block; the
-- may-suspend version gates CPS ELIGIBILITY (a simple block is lowered onto the
-- CK-machine).  This mirrors 'scalarBodyMaySuspend'/'mayActSuspend', which
-- already treat a local-headed call as conservatively may-suspend.
blockSuspendsWith :: Bool -> Set GName -> [KItem] -> Bool
blockSuspendsWith incLocal susp = any itemSuspends
  where
    s = \case
      CDo _ items -> blockSuspendsWith incLocal susp items
      t -> spineHeadSuspends susp t || (incLocal && spineHeadIsLocal t)
    condSuspends (KCondPure _) = False
    condSuspends (KCondAction t) = s t
    recur = blockSuspendsWith incLocal susp
    itemSuspends (KBind _ _ t _) = s t
    itemSuspends (KExpr t) = s t
    itemSuspends (KAssign _ _ _ actT _) = s actT
    itemSuspends (KReturn t) = s t
    itemSuspends (KVarItem _ _ actT _) = s actT
    itemSuspends (KWhile _ c b me) = condSuspends c || recur b || maybe False recur me
    itemSuspends (KFor _ _ _ b me) = recur b || maybe False recur me
    itemSuspends (KIf alts me) = any (recur . snd) alts || maybe False recur me
    itemSuspends (KDefer _ e) = s e
    -- A `using` release is an action built from the selected release function
    -- and the acquired resource at runtime. Even when the acquire action itself
    -- is non-suspending, the release path must be installed and driven by the
    -- CK doscope/finalizer machinery rather than the legacy raw bridge.
    itemSuspends KUsing {} = True
    -- a transparent sub-do runs in THIS block's continuation chain, so a
    -- suspending op inside it makes this block suspend too (CPS LOOP FAMILY §4).
    itemSuspends (KSubDo _ b) = recur b
    itemSuspends _ = False

-- | The STRICT suspender test (named-suspender / §3.3-global heads only): gates
-- the FAIL-CLOSED diagnostic in 'compileDo'.  A local-headed call is NOT counted
-- here, so this version never newly rejects an otherwise-legacy block.
blockSuspends :: Set GName -> [KItem] -> Bool
blockSuspends = blockSuspendsWith False

cpsEligible :: Set GName -> [KItem] -> Bool
cpsEligible susp items =
  -- CPS-eligibility counts an opaque higher-order (local-headed) action as
  -- may-suspend (incLocal = True): a `restore x` / `use r` bind in an otherwise
  -- SIMPLE block must be CK-lowered (only the CK-machine drives OP_RESTORE).  The
  -- `all simpleLinear` guard keeps this from ever turning a non-CPS-able block
  -- into the fail-closed path — a non-simple block with a local-headed call stays
  -- legacy exactly as before.
  all simpleLinear items && (blockSuspendsWith True susp items || any needsRuntimeFinalizers items)
  where
    -- Stage 1: binds/lets/effects.  Stage 2: plus plain `defer` (lowered through
    -- the runtime's OP_DOSCOPE/OP_DEFER).  Stage 2.5 — the CPS LOOP FAMILY (§4):
    -- var / := / while / break / continue / return now lower through selected
    -- MonadRef actions; checker-witnessed builtin IO refs use the CK-machine's
    -- OP_WHILE/KK_LOOP + OP_NEW_REF/OP_READ_REF/OP_WRITE_REF + the
    -- abrupt-control nodes, so a may-suspend block containing them is no longer
    -- fail-closed.  Scope discipline: the WELL-SCOPED CORE handles the unlabeled
    -- `while` (no else), `var`/`:=` (assign to a `var` cell), unlabeled
    -- `break`/`continue`, `return`, plain `defer`, statement-`if`, and a
    -- transparent statement-position sub-do (labeled or unlabeled), and `using` (§19.5 resource scope, lowered
    -- through krt2_uninterruptible + krt2_finally, reusing the bracketM
    -- machinery).  Labeled loops, `for`, loop `else`, and `let?` remain
    -- fail-closed (DIAGNOSED in 'compileDo', not mis-lowered).
    simpleLinear KBind {} = True
    simpleLinear KLet {} = True
    simpleLinear KExpr {} = True
    simpleLinear KUsing {} = True
    simpleLinear (KDefer Nothing _) = True
    simpleLinear KVarItem {} = True
    simpleLinear (KAssign (CVar _) _ _ _ _) = True
    simpleLinear KReturn {} = True
    simpleLinear (KBreak Nothing) = True
    simpleLinear (KContinue Nothing) = True
    simpleLinear (KWhile Nothing _ body Nothing) = all simpleLinear body
    simpleLinear (KIf alts mels) =
      all (all simpleLinear . snd) alts && maybe True (all simpleLinear) mels
    simpleLinear (KSubDo _ body) = all simpleLinear body
    simpleLinear _ = False
    needsRuntimeFinalizers (KDefer Nothing _) = True
    needsRuntimeFinalizers KUsing {} = True
    needsRuntimeFinalizers (KWhile Nothing _ body mels) =
      any needsRuntimeFinalizers body || maybe False (any needsRuntimeFinalizers) mels
    needsRuntimeFinalizers (KIf alts mels) =
      any (any needsRuntimeFinalizers . snd) alts || maybe False (any needsRuntimeFinalizers) mels
    needsRuntimeFinalizers (KSubDo _ body) = any needsRuntimeFinalizers body
    needsRuntimeFinalizers _ = False

-- | Lower a CPS-eligible do-block: build its @krt2_*@ action tree, wrapping it
-- in a @krt2_doscope@ when the block carries §18.7 defers (so they run LIFO and
-- masked on every exit, via OP_DOSCOPE/KK_DOSCOPE).  With no defers there is no
-- scope frame — just the bind tree.
compileDoCps :: [KItem] -> Gen Text
compileDoCps items = do
  tree <- cpsItems items
  -- §18.8: a `return` exits THIS do-block (yielding its value), not the fiber.
  -- When CPS-lowered the block is inlined into a larger continuation chain, so a
  -- bare OP_RETURN would unwind past the block to the fiber's KK_DONE.  Wrap the
  -- block in krt2_retscope (KK_RETSCOPE), which catches the RK_RETURN and
  -- delivers the value as the block's result — restoring do-block-scoped return.
  let scoped = if any itemReturns items then "krt2_retscope(" <> tree <> ")" else tree
  pure $ if any hasScope items then "krt2_doscope(" <> scoped <> ")" else scoped
  where
    hasScope (KDefer _ _) = True
    hasScope _ = False
    -- a `return` anywhere in THIS block (recursing into its own loop/if/subdo
    -- bodies, which return from this block, but NOT into a nested do VALUE).
    itemReturns (KReturn _) = True
    itemReturns (KWhile _ _ b mels) = any itemReturns b || maybe False (any itemReturns) mels
    itemReturns (KIf alts mels) = any (any itemReturns . snd) alts || maybe False (any itemReturns) mels
    itemReturns (KSubDo _ b) = any itemReturns b
    itemReturns _ = False

-- | Lower a CPS-eligible do-block to its @krt2_bind@/@krt2_then@ action tree.
-- Each non-tail bind becomes @krt2_bind(action, kclo(kdok_N, env))@ with the
-- continuation emitted as a sibling function; a discarded effect becomes
-- @krt2_then@; the tail action is returned directly (tail position — the
-- CK-machine, not a nested bind, so the spine stays bounded).
cpsItems :: [KItem] -> Gen Text
cpsItems = cpsItemsFrom 0

cpsItemsFrom :: Int -> [KItem] -> Gen Text
cpsItemsFrom start items = case items of
  [] -> pure "krt2_pure(kunit())"
  item : rest ->
    let ix = start
        next = ix + 1
        itemChild child = withChild (P.doItemPos ix) . withChild child
        itemNode = withChild (P.doItemPos ix)
        restTree = cpsItemsFrom next rest
     in case item of
          -- TAIL position: a self-tail-call / mutual-recursion /
          -- call-through-a-value here is DEFERRED behind a continuation so the
          -- recursion is C-stack-bounded (see 'cpsTailAction'); a CPS-node or
          -- primitive head is built directly.
          KExpr t
            | null rest -> itemChild P.kExprActionPos (cpsTailAction t)
            | otherwise -> seqThen [P.doItemPos ix, P.kExprActionPos] t restTree
          KBind _ _ t _
            | null rest -> itemChild P.kBindActionPos (cpsTailAction t)
          KBind _ CPWild t _ -> seqThen [P.doItemPos ix, P.kBindActionPos] t restTree
          KBind _ pat t _ -> do
            m <- itemChild P.kBindActionPos (cpsActionTerm t)
            contFn <- emitCpsCont pat next rest
            env <- gets gsEnv
            pure ("krt2_bind(" <> m <> ", kclo(" <> contFn <> ", " <> env <> "))")
          KLet _ CPWild t -> itemChild P.kLetValuePos (compile t) >> restTree
          KLet _ pat t -> do
            -- a `let` binds a PURE value. Current-value reads and splices have
            -- already been lifted by the checker into preceding bind/action
            -- items, so there is no hidden monadic read to discover here.
            bindA <- itemChild P.kLetValuePos (cpsActionOfPure t)
            contFn <- emitCpsCont pat next rest
            env <- gets gsEnv
            pure ("krt2_bind(" <> bindA <> ", kclo(" <> contFn <> ", " <> env <> "))")
          -- ── CPS LOOP FAMILY (CPS-DESIGN §4) ──────────────────────────
          -- @var x = init@: bind the MonadRef.newRef action chosen by
          -- elaboration and push the resulting Ref onto the captured env
          -- (de Bruijn 0) for the continuation.
          KVarItem x _ actT _ -> do
            refA <- itemChild P.kVarActionPos (cpsActionTerm actT)
            contFn <- emitCpsCont (CPVar x) next rest
            env <- gets gsEnv
            pure ("krt2_bind(" <> refA <> ", kclo(" <> contFn <> ", " <> env <> "))")
          -- @x := rhs@ / @x <- rhs@ (a var assignment): run the
          -- MonadRef.writeRef action selected during elaboration, so CPS and
          -- non-CPS paths use the same evidence.
          KAssign _ _ _ actT _ -> do
            writeA <- itemChild P.kAssignActionPos (cpsActionTerm actT)
            r <- restTree
            pure ("krt2_then(" <> writeA <> ", " <> r <> ")")
          -- @return v@: exit THIS do-block (OP_RETURN -> RK_RETURN, caught by
          -- the enclosing KK_RETSCOPE — compileDoCps), running every crossed
          -- do-scope's defers en route.
          KReturn t -> do
            rv <- itemChild P.kReturnValuePos (cpsActionOfPure t)
            contFn <- emitCpsReturnCont
            env <- gets gsEnv
            pure ("krt2_bind(" <> rv <> ", kclo(" <> contFn <> ", " <> env <> "))")
          -- @break@ / @continue@ (unlabeled): target the innermost OP_WHILE's KK_LOOP.
          KBreak Nothing -> pure "krt2_break()"
          KContinue Nothing -> pure "krt2_continue()"
          -- @while c { body }@ (unlabeled, no else): OP_WHILE[condIO, bodyIO] -> KK_LOOP.
          KWhile Nothing cond body Nothing -> do
            condA <- itemChild P.kWhileCondPos (cpsCondAction cond)
            bodyA <- itemNode (withChild P.kWhileBodyPos (cpsItems body))
            r <- restTree
            pure ("krt2_then(krt2_while(" <> condA <> ", " <> bodyA <> "), " <> r <> ")")
          -- a statement-`if` in a CPS block: each branch is a CPS action tree;
          -- the if's normal completion is Unit, so a non-tail if sequences its
          -- Unit result before the rest via krt2_then.
          KIf alts mels -> do
            br <- itemNode (cpsIf alts mels)
            if null rest
              then pure br
              else do
                r <- restTree
                pure ("krt2_then(" <> br <> ", " <> r <> ")")
          -- a transparent nested do-statement (§18.8.3.1): its own bindings
          -- are scoped to the sub-block, but abrupt control propagates outward.
          KSubDo _ body -> do
            sub0 <- itemNode (withChild P.kSubDoBodyPos (cpsItems body))
            let sub = if any directDefers body then "krt2_doscope(" <> sub0 <> ")" else sub0
            if null rest
              then pure sub
              else do
                r <- restTree
                pure ("krt2_then(" <> sub <> ", " <> r <> ")")
          -- §18.7 plain defer: register the action on the enclosing do-scope's
          -- ExitStack (OP_DEFER), then continue.
          KDefer Nothing t -> do
            de <- itemChild P.kDeferActionPos (compileDeferAction t)
            r <- restTree
            pure ("krt2_then(krt2_defer(" <> de <> "), " <> r <> ")")
          -- §19.5/§18.8.3 `using pat <- acquire`: lower through
          -- krt2_acquire_release (rt.c), the same protected-scope machinery
          -- `bracketM` uses.
          KUsing pat acquireT releaseT -> do
            acqA <- itemChild P.kUsingAcquirePos (cpsActionTerm acquireT)
            relV <- itemChild P.kUsingReleasePos (compile releaseT)
            useFn <- emitCpsCont pat next rest
            env <- gets gsEnv
            pure
              ( "krt2_acquire_release(" <> acqA <> ", " <> relV
                  <> ", kclo(" <> useFn <> ", " <> env <> "))"
              )
          _ ->
            unsupported "do-kernel (CPS)" ("unexpected item in a CPS do-block: " <> T.pack (show item))
  where
    seqThen revPrefix t restTree = do
      m <- withChildren revPrefix (cpsActionTerm t)
      r <- restTree
      pure ("krt2_then(" <> m <> ", " <> r <> ")")

    withChildren [] act = act
    withChildren (p : ps) act = withChild p (withChildren ps act)

-- | A §18.7 defer registered DIRECTLY in this item list, not in a nested
-- loop/if/subdo. Such a branch/subdo list needs its own krt2_doscope so the
-- finalizer runs at that list's exit, not at the enclosing do-scope exit.
directDefers :: KItem -> Bool
directDefers (KDefer _ _) = True
directDefers _ = False

-- | Emit a CPS continuation function @kdok_N(KEnv *cenv, KValue *karg)@: bind
-- the delivered value @karg@ to @pat@ (extending the captured @cenv@), then
-- build the rest of the block as a tree.
emitCpsCont :: CorePat -> Int -> [KItem] -> Gen Text
emitCpsCont pat next rest = do
  fnName <- freshFn "kdok_"
  (stmts, tree) <- captured "cenv" $ do
    e2 <- bindPatScrut "karg" "cenv" pat
    withEnv e2 (cpsItemsFrom next rest)
  let fn =
        T.unlines $
          ["static KValue *" <> fnName <> "(KEnv *cenv, KValue *karg) {", "  (void)cenv; (void)karg;"]
            ++ map ("  " <>) stmts
            ++ ["  return " <> tree <> ";", "}"]
  modify' $ \st ->
    st
      { gsTop = fn : gsTop st
      , gsProtos = ("static KValue *" <> fnName <> "(KEnv *, KValue *);") : gsProtos st
      }
  pure fnName

-- ── CPS LOOP FAMILY helpers (CPS-DESIGN §4) ──────────────────────────────

-- | Compile an IO ACTION term in a CPS block. Current-value reads and splices
-- have already been lifted by the checker into action terms or do-kernel binds.
cpsActionTerm :: Term -> Gen Text
cpsActionTerm = compile

-- | Compile a CPS do-block's TAIL action (the last @KExpr@/@KBind@ in the
-- block) — the position where an IO/STM tail self-call lives.
--
-- For a CPS-node head (ioBind/ioThen/atomically/catchIO/… — 'cpsNodeApp') or a
-- non-application the action IS already the krt2_* node tree the CK-machine
-- drives, so build it directly ('cpsActionTerm').
--
-- BUT for a tail-position call to a non-primitive FUNCTION — a self-tail-call
-- like @do { atomically (acquire …); atomically (release …); philosopher … }@,
-- or a mutual-recursion / call-through-a-value — 'cpsActionTerm' would
-- @compile@ it as a SATURATED native call (@ktrampoline(kw_g(args))@) built
-- EAGERLY while the enclosing krt2_then/bind tree is constructed.  The callee's
-- body is itself such a do-block, so each round constructs one more level
-- before the CK-machine ever steps — the recursion grows the native fiber stack
-- (SIGBUS at ~7000 rounds), exactly the eager-tree bug.
--
-- Defer it instead: emit the call inside a one-shot continuation
-- @kdok_N(cenv, karg)@ and return @krt2_bind(krt2_pure(unit), kclo(kdok_N,
-- env))@.  The CK-machine runs the (trivial) @krt2_pure@, then fires KK_BIND,
-- which @kapp@s the continuation — building the NEXT level only when the machine
-- reaches it.  The leading actions still run, in order, unchanged; only the tail
-- self-call's lowering moves from an eager native call to a CK-machine-driven
-- bounce, so the recursion runs at constant fiber-stack depth and can still park
-- (STM retry / await) — the CK-machine drives the deferred tree, not the
-- synchronous krun_io bridge (which is why this is a @krt2_bind@, not @kio_tail@).
cpsTailAction :: Term -> Gen Text
cpsTailAction t = do
  defer <- deferrableTailCall t
  if not defer
    then cpsActionTerm t
    else do
      fnName <- freshFn "kdok_"
      (stmts, tree) <- captured "cenv" (cpsActionTerm t)
      let fn =
            T.unlines $
              ["static KValue *" <> fnName <> "(KEnv *cenv, KValue *karg) {", "  (void)cenv; (void)karg;"]
                ++ map ("  " <>) stmts
                ++ ["  return " <> tree <> ";", "}"]
      modify' $ \st ->
        st
          { gsTop = fn : gsTop st
          , gsProtos = ("static KValue *" <> fnName <> "(KEnv *, KValue *);") : gsProtos st
          }
      env <- gets gsEnv
      pure ("krt2_bind(krt2_pure(kunit()), kclo(" <> fnName <> ", " <> env <> "))")

-- | Whether a CPS tail action should be DEFERRED behind a continuation rather
-- than compiled eagerly into the action tree ('cpsTailAction').  True for a
-- saturated/curried call to a non-primitive function — the case 'emitTailApp'
-- would lower to a @kbounce@ (mutual recursion, a self-tail-call, or a call
-- through a value): such a call returns a further action tree and must be built
-- lazily so the recursion is C-stack-bounded.  A CPS-node head ('cpsNodeApp')
-- or a primitive-headed call already builds a node the CK-machine drives (or a
-- leaf that cannot recurse), so it is NOT deferred — keeping the tree minimal.
deferrableTailCall :: Term -> Gen Bool
deferrableTailCall t = do
  isCps <- cpsNodeApp t
  if isCps
    then pure False
    else case spineOf t of
      (hd, args)
        | any ((== Expl) . fst) args -> case hd of
            CGlob g -> do
              mp <- globPrimName g
              pure (mp == Nothing) -- a non-prim global: a (possibly self-) function call → defer
            _ -> pure True -- a call THROUGH a value (closure / local let-rec) → defer
      _ -> pure False -- not an application (a bare value / pure node) → no deferral

-- | Lift a pure value into an IO action. Any current-value reads in source have
-- already become preceding MonadRef.readRef binds during checking.
cpsActionOfPure :: Term -> Gen Text
cpsActionOfPure term = do
  fnName <- freshFn "kdok_"
  (stmts, v) <- captured "cenv" (compile term)
  let fn =
        T.unlines $
          [ "static KValue *" <> fnName <> "(KEnv *cenv, KValue *karg) {"
          , "  (void)cenv; (void)karg;"
          ]
            ++ map ("  " <>) stmts
            ++ [ "  return krt2_pure(" <> v <> ");"
               , "}"
               ]
  modify' $ \st ->
    st
      { gsTop = fn : gsTop st
      , gsProtos = ("static KValue *" <> fnName <> "(KEnv *, KValue *);") : gsProtos st
      }
  env <- gets gsEnv
  pure ("krt2_bind(krt2_pure(kunit()), kclo(" <> fnName <> ", " <> env <> "))")

-- | Build the @cond@ action of a CPS @while@: an action whose stepped result is
-- the loop's Bool condition. Current reads in a source condition elaborate to
-- 'KCondAction' so the runtime re-runs the selected MonadRef.readRef action on
-- every iteration.
cpsCondAction :: KCond -> Gen Text
cpsCondAction = \case
  KCondPure t -> cpsActionOfPure t
  KCondAction t -> cpsActionTerm t

-- | The @return v@ continuation: the delivered value @karg@ exits the do-block
-- via OP_RETURN (the abrupt-control node unwinds crossed do-scopes, running
-- their defers, then is caught by the block's KK_RETSCOPE — §18.8).
emitCpsReturnCont :: Gen Text
emitCpsReturnCont = do
  fnName <- freshFn "kdok_"
  let body =
        [ "static KValue *" <> fnName <> "(KEnv *cenv, KValue *karg) {"
        , "  (void)cenv;"
        , "  return krt2_return(karg);"
        , "}"
        ]
  modify' $ \st ->
    st
      { gsTop = T.unlines body : gsTop st
      , gsProtos = ("static KValue *" <> fnName <> "(KEnv *, KValue *);") : gsProtos st
      }
  pure fnName

-- | A statement-@if@ in a CPS block: each branch is a CPS action tree.  The
-- condition is a pure Bool (R7-normalized if it reads a var); the runtime picks
-- the branch.  Built as @krt2_bind(<condAction>, kclo(select))@ where @select@
-- dispatches in C on the delivered Bool to the chosen branch's tree.
cpsIf :: [(Term, [KItem])] -> Maybe [KItem] -> Gen Text
cpsIf alts mels = goAlts 0 alts
  where
    armCount = length alts

    goAlts _ [] = case mels of
      Just els -> withChild (P.kIfElsePos armCount) (cpsScopedItems els)
      Nothing -> pure "krt2_pure(kunit())" -- no/exhausted else: Unit (§18.8)
    goAlts ai ((c, body) : more) = do
      condA <- withChild (P.kIfCondPos ai) (cpsActionOfPure c)
      thenFn <- emitCpsBranchCont (withChild (P.kIfBodyPos ai) (cpsScopedItems body))
      elseFn <- emitCpsBranchCont (goAlts (ai + 1) more)
      env <- gets gsEnv
      sel <- emitCpsIfSelect thenFn elseFn
      pure ("krt2_bind(" <> condA <> ", kclo(" <> sel <> ", " <> env <> "))")
    cpsScopedItems body = do
      tree <- cpsItems body
      pure $ if any directDefers body then "krt2_doscope(" <> tree <> ")" else tree

-- | Emit a branch builder @kdok_N(KEnv *cenv, KValue *karg)@ ignoring @karg@,
-- returning the branch's CPS tree (built under the captured env, unextended).
emitCpsBranchCont :: Gen Text -> Gen Text
emitCpsBranchCont build = do
  fnName <- freshFn "kdok_"
  (stmts, tree) <- captured "cenv" build
  let fn =
        T.unlines $
          ["static KValue *" <> fnName <> "(KEnv *cenv, KValue *karg) {", "  (void)cenv; (void)karg;"]
            ++ map ("  " <>) stmts
            ++ ["  return " <> tree <> ";", "}"]
  modify' $ \st ->
    st
      { gsTop = fn : gsTop st
      , gsProtos = ("static KValue *" <> fnName <> "(KEnv *, KValue *);") : gsProtos st
      }
  pure fnName

-- | Emit the if-selector @kdok_N(KEnv *cenv, KValue *karg)@: on the delivered
-- Bool @karg@, return the then-branch tree or the else-branch tree (each built
-- by applying its closure to the captured env + Unit).
emitCpsIfSelect :: Text -> Text -> Gen Text
emitCpsIfSelect thenFn elseFn = do
  fnName <- freshFn "kdok_"
  let body =
        [ "static KValue *" <> fnName <> "(KEnv *cenv, KValue *karg) {"
        , "  return kas_bool(karg)"
        , "    ? " <> thenFn <> "(cenv, kunit())"
        , "    : " <> elseFn <> "(cenv, kunit());"
        , "}"
        ]
  modify' $ \st ->
    st
      { gsTop = T.unlines body : gsTop st
      , gsProtos = ("static KValue *" <> fnName <> "(KEnv *, KValue *);") : gsProtos st
      }
  pure fnName

-- | Compile a do-block to a suspended IO action (@kio@) whose body runs
-- the scope.  The captured environment is the current one.  A block reaching a
-- suspending operation is CPS-lowered instead (see 'cpsEligible').
compileDo :: Maybe Text -> [KItem] -> Gen Text
compileDo lbl items = do
  susp <- gets gsSuspenders
  if cpsEligible susp items
    then compileDoCps items
    -- A block that reaches a suspending op but is not a CPS-able shape would be
    -- mis-run on the synchronous bridge (fork/await never park) — fail closed
    -- with a clear diagnostic instead, until the relevant CPS stage lands.
    else
      if blockSuspends susp items
        then
          unsupported
            "do-kernel"
            ( "a suspending operation (fork/await/sleepFor/…) appears in a do-block shape the "
                <> "native backend does not yet CPS-lower (a loop, if, using, labeled defer, "
                <> "monadic assignment, or return); see runtime/docs/CPS-DESIGN.md (Stage 2+)"
            )
        else compileDoLegacy lbl items

compileDoLegacy :: Maybe Text -> [KItem] -> Gen Text
compileDoLegacy lbl items = do
  fnName <- freshFn "kdo_"
  env <- gets gsEnv
  -- A do-block is a fresh scope in its own C function: its defer frames,
  -- labeled-scope map and enclosing loops do not extend into it (control
  -- cannot break out of, nor defer@L into, a do-block VALUE's outer scope),
  -- so reset those for the do-fn body. compileItems sets up this scope's
  -- §18.7 defer frame (tagged with `lbl` for defer@label routing).
  saved <- gets $ \g -> (gsDefer g, gsScopeDefers g, gsLoops g, gsDeferLabels g)
  modify' $ \g -> g {gsDefer = [], gsScopeDefers = [], gsLoops = [], gsDeferLabels = []}
  (stmts, ()) <- captured "cenv" (compileItems lbl Tail items)
  modify' $ \g -> let (d, s, l, dl) = saved in g {gsDefer = d, gsScopeDefers = s, gsLoops = l, gsDeferLabels = dl}
  let fn =
        T.unlines $
          [ "static KValue *" <> fnName <> "(KEnv *cenv) {"
          , "  (void)cenv;"
          ]
            ++ map ("  " <>) stmts
            ++ ["}"]
  modify' $ \st ->
    st
      { gsTop = fn : gsTop st
      , gsProtos = ("static KValue *" <> fnName <> "(KEnv *);") : gsProtos st
      }
  pure ("kio(" <> fnName <> ", " <> env <> ")")

-- | §18.7 @defer t@: register a CK-machine action that evaluates @t@ lazily at
-- scope exit.  The interpreter stores @evalK env t@ in the exit list, so @t@'s
-- sub-expressions observe state mutated between registration and finalizer
-- drain.  The generated action therefore captures the current environment (the
-- @var@ cells, not snapshots) and puts the actual @compile t@ work behind a
-- one-shot continuation.  The finalizer driver executes that continuation under
-- the CK machine; if @t@ parks (sleepFor/blocking/await/...), suspension is
-- preserved instead of being forced through the synchronous @krun_io@ bridge.
compileDeferAction :: Term -> Gen Text
compileDeferAction t = do
  fnName <- freshFn "kdefer_"
  env <- gets gsEnv
  (stmts, e) <- captured "cenv" (compile t)
  let fn =
        T.unlines $
          [ "static KValue *" <> fnName <> "(KEnv *cenv, KValue *karg) {"
          , "  (void)cenv; (void)karg;"
          ]
            ++ map ("  " <>) stmts
            ++ [ "  return " <> e <> ";"
               , "}"
               ]
  emitTop ("static KValue *" <> fnName <> "(KEnv *, KValue *);") fn
  pure ("krt2_bind(krt2_pure(kunit()), kclo(" <> fnName <> ", " <> env <> "))")

-- | A §19 suspension: lift the delayed expression into a fresh thunk
-- function capturing the current environment; @memo@ is 1 for Memo (cache
-- on first force) and 0 for Delay (re-evaluate each force).
compileSuspension :: Int -> Term -> Gen Text
compileSuspension memo e = do
  fnName <- freshFn "kth_"
  env <- gets gsEnv
  (stmts, ve) <- captured "cenv" (compile e)
  let fn =
        T.unlines $
          [ "static KValue *" <> fnName <> "(KEnv *cenv) {"
          , "  (void)cenv;"
          ]
            ++ map ("  " <>) stmts
            ++ [ "  return " <> ve <> ";"
               , "}"
               ]
  emitTop ("static KValue *" <> fnName <> "(KEnv *);") fn
  pure ("kthunk(" <> fnName <> ", " <> env <> ", " <> T.pack (show memo) <> ")")

-- | Whether a scope is in tail position (the do-block body, whose final
-- value is the block's result) or nested (a loop\/if body, run for effect
-- with control flow propagating via C statements).  Both share the same
-- item handling and environment threading — the only differences are the
-- result of a trailing 'KExpr' and the empty-scope fall-through.
-- | 'Tail': the do-block result is this scope's last value (a trailing
-- 'KExpr' propagates its IO action's result).  'Nested': run for effect,
-- control flow via C statements (a loop / non-tail @if@ body).
-- 'TailEffect': a tail statement-@if@ branch (§18.8) — still tail position
-- for stack-safety (the trailing IO action defers via @kio_effect@), but
-- its normal completion is discarded so the do-block yields Unit (matching
-- the interpreter's @KIf@ completion); a @return@ still propagates its
-- value as a non-local early return.
data ScopeMode = Tail | Nested | TailEffect
  deriving stock (Eq)

-- | Compile a sequence of do-kernel items, threading the environment
-- through bindings.  Mirrors 'Kappa.Interp.runScope' completion: in 'Tail'
-- position the scope @return@s the last 'KExpr' value (or Unit); in
-- 'Nested' position items run for effect and break\/continue\/return
-- propagate via C statements.  A single traversal serves both modes so the
-- two can never drift (the previous split caused real divergences).
-- | §18.7: count the @defer@L@ actions in a kernel subtree that target the
-- scope labeled @L@. Recurses into nested loop/if bodies (which route their
-- @defer@L@ to this scope) but never into a 'KDefer' action term (a nested
-- @do@ VALUE there is a fresh scope with its own label map).
countLabeledDefers :: Text -> [KItem] -> Int
countLabeledDefers s = sum . map go
  where
    go (KDefer (Just l) _) | l == s = 1
    go (KWhile _ _ body mels) = countLabeledDefers s body + maybe 0 (countLabeledDefers s) mels
    go (KFor _ _ _ body mels) = countLabeledDefers s body + maybe 0 (countLabeledDefers s) mels
    go (KIf alts mels) = sum [countLabeledDefers s b | (_, b) <- alts] + maybe 0 (countLabeledDefers s) mels
    -- a transparent nested do-statement routes its @defer@s@ to this scope,
    -- unless it is itself labeled @s@ (then it owns those defers)
    go (KSubDo subL body) | subL == Just s = 0
                          | otherwise = countLabeledDefers s body
    go _ = 0

compileItems :: Maybe Text -> ScopeMode -> [KItem] -> Gen ()
compileItems selfLabel mode items0 = do
  -- A scope that registers §18.7 defers gets a frame (a GC-heap array +
  -- count, declared at scope entry — for a loop body that means a fresh
  -- frame per iteration).  A Tail/TailEffect scope's frame is pushed on
  -- gsDefer and flushed after the tail IO action (kio_finally, via
  -- emitTailIO/emitTailReturn); a Nested scope's frame is pushed on
  -- gsScopeDefers and flushed INLINE at normal completion here (and at any
  -- break/continue/return that unwinds it — see gotoLoop / KReturn).
  --
  -- The frame must be sized for every action that lands on it: the
  -- unlabeled `defer`s written DIRECTLY in this scope, plus any
  -- `defer@selfLabel` written anywhere in this scope's kernel subtree
  -- (nested loop/if bodies route to it). A `defer@other` written here
  -- routes to an enclosing frame, so it is NOT counted at this scope.
  -- §19.5 `using` also attaches a release to this scope's exit frame.
  let ndirect = length [() | KDefer Nothing _ <- items0] + length [() | KUsing {} <- items0]
      nlabeled = case selfLabel of
        Just s -> countLabeledDefers s items0
        Nothing -> 0
      ndefer = ndirect + nlabeled
  if ndefer == 0
    then goAt 0 items0
    else do
      arr <- freshN "kdef_"
      cnt <- freshN "kdc_"
      emit ("KValue **" <> arr <> " = (KValue **)kgc_alloc(sizeof(KValue *) * " <> T.pack (show ndefer) <> "); (void)" <> arr <> ";")
      emit ("int " <> cnt <> " = 0; (void)" <> cnt <> ";")
      let frame = (arr, cnt)
      case mode of
        Nested -> modify' $ \g -> g {gsScopeDefers = frame : gsScopeDefers g}
        _ -> modify' $ \g -> g {gsDefer = frame : gsDefer g}
      forM_ selfLabel $ \l -> modify' $ \g -> g {gsDeferLabels = (l, frame) : gsDeferLabels g}
      goAt 0 items0
      forM_ selfLabel $ \_ -> modify' $ \g -> g {gsDeferLabels = drop 1 (gsDeferLabels g)}
      case mode of
        Nested -> do flushFramesInline [frame]; modify' $ \g -> g {gsScopeDefers = drop 1 (gsScopeDefers g)}
        _ -> modify' $ \g -> g {gsDefer = drop 1 (gsDefer g)}
  where
    itemChild ix child = withChild (P.doItemPos ix) . withChild child

    goAt _ [] = case mode of
      -- both Tail and a discarded tail if-branch yield Unit here; route
      -- through emitTailReturn so any §18.7 defers are still flushed.
      Tail -> emitTailReturn "kunit()"
      TailEffect -> emitTailReturn "kunit()"
      Nested -> pure ()
    goAt ix (item : rest) = case item of
      KExpr t
        | null rest -> do
            te <- itemChild ix P.kExprActionPos (compile t)
            case mode of
              -- The do-block's tail IO action is its result: defer it to the
              -- driving krun_io (constant C stack, §27.5A.3), carrying any
              -- §18.7 finalizers along (emitTailIO).
              Tail -> emitTailIO False te
              -- A tail statement-if branch: same, but the result is
              -- discarded (the do-block yields Unit).
              TailEffect -> emitTailIO True te
              Nested -> emitRunIODiscard te
      KExpr t -> do
        te <- itemChild ix P.kExprActionPos (compile t)
        emitRunIODiscard te >> goAt (ix + 1) rest
      -- A wildcard binding introduces no name: emit the right-hand side
      -- for its effect (a bind runs the IO action; a let just evaluates)
      -- without an unused C variable (keeps the generated C -Wall clean).
      KLet _ CPWild t -> do
        te <- itemChild ix P.kLetValuePos (compile t)
        emit ("(void)(" <> te <> ");")
        goAt (ix + 1) rest
      KLet _ pat t -> do
        te <- itemChild ix P.kLetValuePos (compile t)
        sv <- freshN "let_"
        emit ("KValue *" <> sv <> " = " <> te <> ";")
        bindAndContinue sv pat
      KBind _ CPWild t _ -> do
        te <- itemChild ix P.kBindActionPos (compile t)
        emitRunIODiscard te
        goAt (ix + 1) rest
      KBind _ pat t _ -> do
        te <- itemChild ix P.kBindActionPos (compile t)
        sv <- emitRunIOValue "bind_" te
        bindAndContinue sv pat
      -- §18 early non-local return: unwind every enclosing Nested scope
      -- (loop/if bodies) running their defers first, then return the value
      -- through emitTailReturn (which flushes the Tail-scope defer frames).
      KReturn t -> do
        te <- itemChild ix P.kReturnValuePos (compile t)
        scopeFrames <- gets gsScopeDefers
        flushFramesInline scopeFrames
        emitTailReturn te
      KVarItem _ _ actT _ -> do
        -- S2.3b: run the checker-selected MonadRef.newRef action on the
        -- C/default fallback path. The former scalar-loop peephole bypassed
        -- MonadRef evidence, so this backend must not reconstruct raw refs until
        -- an evidence-aware C scalarizer proves equivalence.
        te <- itemChild ix P.kVarActionPos (compile actT)
        ref <- emitRunIOValue "var_" te
        env <- gets gsEnv
        e2 <- freshN "env_"
        emit ("KEnv *" <> e2 <> " = kpush(" <> ref <> ", " <> env <> ");")
        withEnv e2 (goAt (ix + 1) rest)
      KAssign _ _ _ actT _ -> do
        ae <- itemChild ix P.kAssignActionPos (compile actT)
        emitRunIODiscard ae
        goAt (ix + 1) rest
      -- A statement-`if` that is the do-block's tail: its branches are in
      -- tail position, so a recursive IO call in a branch must defer (not
      -- recurse through krun_io).  Compile the branches in 'TailEffect'
      -- (each path returns); the if's normal completion is discarded so the
      -- do-block yields Unit (§18.8).  A non-tail `if` runs for effect.
      KIf alts mels
        -- A statement-`if` that is the do-block's tail: its branches are in
        -- tail position, so compile them in 'TailEffect' (each path returns,
        -- deferring its tail IO action + finalizers via emitTailIO — stack
        -- safe and defer-correct).  A non-tail `if` runs for effect.
        | null rest && (mode == Tail || mode == TailEffect) -> withChild (P.doItemPos ix) (compileKIfTail mode alts mels)
        | otherwise -> withChild (P.doItemPos ix) (compileKIf alts mels) >> goAt (ix + 1) rest
      KWhile ml cond bdy mels -> withChild (P.doItemPos ix) (compileLoop ml (LoopWhile cond) bdy mels) >> goAt (ix + 1) rest
      KFor ml pat src bdy mels -> withChild (P.doItemPos ix) (compileLoop ml (LoopFor pat src) bdy mels) >> goAt (ix + 1) rest
      -- §18.8.3.1: a transparent nested do-statement compiles as a child scope
      -- (its own §18.7 defer frame and label) that inherits the enclosing
      -- loop/return targets.  If it is itself the tail item of a value-returning
      -- do-block, preserve the enclosing tail mode: `else do ...` in a tail
      -- branch must return the sub-do's final value, not discard it as an
      -- effect-only nested statement.
      KSubDo subLbl subItems
        | null rest && (mode == Tail || mode == TailEffect) -> withChild (P.doItemPos ix) (withChild P.kSubDoBodyPos (compileItems subLbl mode subItems))
        | otherwise -> withChild (P.doItemPos ix) (withChild P.kSubDoBodyPos (compileItems subLbl Nested subItems)) >> goAt (ix + 1) rest
      KBreak ml -> gotoLoop ml lcBreak
      KContinue ml -> gotoLoop ml lcContinue
      -- §18 let? : bind the pattern and continue, or run the else block
      -- (which replaces the rest of this scope).
      KLetQ pat t mElse -> do
        te <- itemChild ix P.kLetQScrutPos (compile t)
        sv <- freshN "letq_"
        emit ("KValue *" <> sv <> " = " <> te <> ";")
        env <- gets gsEnv
        let onElse = withChild (P.doItemPos ix) (compileLetQElse mode sv mElse)
        case distributePat pat of
          -- Common case: a single (or-free) pattern.  Preserves the
          -- irrefutable fast path and the simple if\/else lowering.
          [single] -> do
            mtest <- patTest sv single
            let onMatch = do env' <- bindPatScrut sv env single; withEnv env' (goAt (ix + 1) rest)
            case mtest of
              Nothing -> onMatch -- irrefutable: always binds
              Just test -> do
                (mblk, ()) <- captured env onMatch
                (eblk, ()) <- captured env onElse
                emit ("if (" <> test <> ") {")
                forM_ mblk (emit . ("  " <>))
                emit "} else {"
                forM_ eblk (emit . ("  " <>))
                emit "}"
          -- §17.2.3 binding or-pattern in let? position: try each or-free
          -- alternative in source order; the first whose runtime test passes
          -- binds its variables and continues with the rest of the scope,
          -- otherwise the else block runs (matching the interpreter, which
          -- tries the alternatives in order before falling to the else).
          alts -> do
            done <- freshN "letqm_"
            emit ("int " <> done <> " = 0;")
            forM_ alts $ \alt -> do
              emit ("if (!" <> done <> ") {")
              (blk, ()) <- captured env $ do
                mtest <- patTest sv alt
                let bindAndGo = do
                      env' <- bindPatScrut sv env alt
                      withEnv env' (goAt (ix + 1) rest)
                case mtest of
                  Nothing -> bindAndGo >> emit (done <> " = 1;")
                  Just test -> do
                    emit ("if (" <> test <> ") {")
                    bindAndGo
                    emit ("  " <> done <> " = 1;")
                    emit "}"
              forM_ blk (emit . ("  " <>))
              emit "}"
            (eblk, ()) <- captured env onElse
            emit ("if (!" <> done <> ") {")
            forM_ eblk (emit . ("  " <>))
            emit "}"
      -- §18.7: register a do-block-scope exit action (run LIFO at exit).
      -- A defer nested in a loop/if body is a distinct per-iteration scope
      -- whose timing this do-block-level model would change, so it is
      -- rejected rather than run at the wrong time.
      -- §18.7: register onto THIS scope's defer frame (the head of the
      -- relevant stack — gsDefer for a Tail/TailEffect scope, gsScopeDefers
      -- for a Nested loop/if body).  ndefer>0 guarantees the frame exists.
      -- The deferred action is a SUSPENDED thunk evaluated at scope exit
      -- (not eagerly at registration), so it observes state mutated between
      -- here and the flush — matching the interpreter (`evalK ... t` is run
      -- lazily from the exit list).
      KDefer ml t -> do
        de <- itemChild ix P.kDeferActionPos (compileDeferAction t)
        -- §18.7: `defer@L` registers onto the frame of the enclosing scope
        -- labeled L (which may be outer; its C arr/cnt locals are lexically
        -- in scope here). Plain `defer` uses the current scope's frame.
        frame <- gets $ \g -> case ml of
          Just l | Just fr <- lookup l (gsDeferLabels g) -> fr
          _ -> case mode of
            Nested -> head (gsScopeDefers g)
            _ -> head (gsDefer g)
        -- Legacy synchronous do-code can abort from a native safe point while C
        -- helper frames are still active, before the ordinary C defer frame is
        -- flushed. Register the same action with the runtime abort-exit stack
        -- and put a token finalizer in the ordinary frame, so normal exit and
        -- safe-point abort share the same exactly-once action.
        deferTok <- freshN "udeftok_"
        emit ("KValue *" <> deferTok <> " = krt2_abort_exit_push(" <> de <> ");")
        registerDefer frame ("krt2_abort_exit_finalizer(" <> deferTok <> ")")
        goAt (ix + 1) rest
      -- §19.5: acquire the owned resource, attach `release resource` to this
      -- scope's exit frame (run LIFO with defers via krun_io at exit, on every
      -- exit path), then bind `pat` (borrowed) for the rest of the scope.
      KUsing pat acquireT releaseT -> do
        ae <- itemChild ix P.kUsingAcquirePos (compile acquireT)
        rv <- emitRunIOValue "ures_" ae
        re <- itemChild ix P.kUsingReleasePos (compile releaseT)
        frame <- gets $ \g -> case mode of
          Nested -> head (gsScopeDefers g)
          _ -> head (gsDefer g)
        -- §32.2.6: register the release with the runtime abort-exit stack. The
        -- ordinary finalizer captures the returned token; if a scalar/boxed
        -- safe-point abort drains it first, the finalizer becomes a no-op, so a
        -- `using` release runs at most once.
        let releaseExpr = "kapp(" <> re <> ", " <> rv <> ")"
        releaseTok <- freshN "ureltok_"
        emit ("KValue *" <> releaseTok <> " = krt2_abort_exit_push(" <> releaseExpr <> ");")
        registerDefer frame ("krt2_abort_exit_finalizer(" <> releaseTok <> ")")
        bindAndContinue rv pat
      where
        -- bind an irrefutable do-pattern (with a runtime check for any
        -- refutable shape) and continue with the rest of this scope (the
        -- `rest` closed over from the enclosing `go (item : rest)` clause)
        bindAndContinue sv pat = do
          env <- gets gsEnv
          mtest <- patTest sv pat
          case mtest of
            Just test ->
              emit ("if (!(" <> test <> ")) krt_fail(\"irrefutable binding failed at runtime\");")
            Nothing -> pure ()
          env' <- bindPatScrut sv env pat
          withEnv env' (goAt (ix + 1) rest)

-- | §18.2.5: jump to a loop's continue\/break target. @ml@ selects the
-- loop: 'Nothing' is the innermost; @Just l@ the enclosing loop labelled
-- @l@ (the elaborator already verified the label resolves).
gotoLoop :: Maybe Text -> (LoopCtx -> Text) -> Gen ()
gotoLoop ml proj = do
  loops <- gets gsLoops
  let target = case ml of
        Nothing -> case loops of (lc : _) -> Just lc; [] -> Nothing
        Just l -> lookupLoop l loops
  case target of
    Just lc -> do
      -- §18.7: a break/continue unwinds every Nested defer scope from here
      -- down to (and including) the target loop's body, running their
      -- defers LIFO before the jump.  lcScopeDepth is gsScopeDefers' length
      -- at the target loop's body entry, so the crossed frames are the ones
      -- above it.
      depth <- gets (length . gsScopeDefers)
      frames <- gets (take (depth - lcScopeDepth lc) . gsScopeDefers)
      flushFramesInline frames
      emit ("goto " <> proj lc <> ";")
    Nothing -> emit "break;" -- defensive: rejected upstream (§18.2.5)
  where
    lookupLoop l = foldr (\lc acc -> if lcLabel lc == Just l then Just lc else acc) Nothing

-- | Return a pure value from a Tail scope, first running its §18.7 defer
-- frames LIFO (innermost frame first) inline — the value is not a tail IO
-- action, so there is no recursion to keep off the C stack.
emitTailReturn :: Text -> Gen ()
emitTailReturn e = do
  frames <- gets gsDefer
  case frames of
    [] -> emit ("return " <> e <> ";")
    _ -> do
      r <- freshN "ret_"
      emit ("KValue *" <> r <> " = " <> e <> ";")
      flushFramesInline frames
      emit ("return " <> r <> ";")

-- | Run defer frames LIFO inline (innermost frame first; within a frame,
-- last-registered first).  Each `cnt` is drained so a later flush on a
-- different control path is a no-op.
flushFramesInline :: [(Text, Text)] -> Gen ()
flushFramesInline frames =
  forM_ frames $ \(arr, cnt) -> do
    result <- freshN "defer_result"
    emit ("KValue *" <> result <> " = krt2_run_legacy_finalizers(kunit(), " <> arr <> ", &" <> cnt <> ");")
    emit ("if (kis_fail(" <> result <> ") || krt2_is_reraise_action(" <> result <> ")) return " <> result <> ";")

-- | Run an IO action in generated do-kernel code and propagate typed native
-- failures immediately.  A failure exits the current generated scope after
-- draining every active §18.7 defer frame, mirroring the interpreter's
-- exception unwinding instead of binding the failure sentinel as an ordinary
-- value.
emitRunIOValue :: Text -> Text -> Gen Text
emitRunIOValue prefix action = do
  v <- freshN prefix
  emit ("KValue *" <> v <> " = krun_io(" <> action <> ");")
  emitPropagateFailure v
  pure v

emitRunIODiscard :: Text -> Gen ()
emitRunIODiscard action = do
  v <- emitRunIOValue "io_" action
  emit ("(void)" <> v <> ";")

emitPropagateFailure :: Text -> Gen ()
emitPropagateFailure v = do
  frames <- gets $ \g -> gsScopeDefers g ++ gsDefer g
  result <- freshN "fail_result"
  emit ("if (kis_fail(" <> v <> ") || krt2_is_reraise_action(" <> v <> ")) {")
  emit ("  KValue *" <> result <> " = " <> v <> ";")
  forM_ frames $ \(arr, cnt) ->
    emit ("  " <> result <> " = krt2_run_legacy_finalizers(" <> result <> ", " <> arr <> ", &" <> cnt <> ");")
  emit ("  return " <> result <> ";")
  emit "}"

-- | §32.2.6 back-edge safe point for a generated BOXED loop (the general
-- 'compileLoop' lowering).
-- These loops run synchronously under the @krun_io@ K_NATIVE bridge — the
-- CK-machine is not iterating — so a pending interrupt is only OBSERVED when
-- @krt2_safepoint()@ is called at the loop's back-edge.  A register counter,
-- reloaded to @KRT2_SP_QUANTUM@, gates the real (still cheap) check so the loop
-- pays only a decrement + predictable branch per iteration; every QUANTUM
-- iterations it calls @krt2_safepoint()@, which sets @safepoint_hit@ and returns
-- 1 iff @interrupt_pending && mask_depth==0@ (a masked fiber returns 0 —
-- suppression holds).  On a 1 we escape the generated do-fn through
-- @krt2_scalar_abort()@; the runtime catches that at the current fiber-step
-- boundary, drains active abort-exit tokens through @begin_finseq@ (masked,
-- suspendable, failure-composing), and delivers the interrupt before any later
-- source effects can run. Boxed loops have already committed every mutation to
-- their ref cells, so there is no loop-state flush to perform here.
emitSafepointAbort :: Text -> Gen ()
emitSafepointAbort spc = do
  emit ("if (--" <> spc <> " <= 0) { " <> spc <> " = KRT2_SP_QUANTUM; if (krt2_safepoint()) {")
  emit "  krt2_scalar_abort();"
  emit "  return kunit();"
  emit "} }"

-- | Return a do-block's tail IO action, deferring its execution to the
-- driving @krun_io@ loop so a sequenced IO tail-recursion runs in constant
-- C stack (§27.5A.3).  @discard@ marks a tail statement-@if@ branch whose
-- result is dropped (the do-block yields Unit).  The active Tail-scope
-- defer frames (innermost first) are handed over with the action via nested
-- @kio_finally@ (finalizers run after the action completes, accumulated on
-- the krun_io heap stack rather than the C stack — order: innermost first).
emitTailIO :: Bool -> Text -> Gen ()
emitTailIO discard action = do
  frames <- gets gsDefer
  case frames of
    [] -> emit ("return " <> (if discard then "kio_effect(" else "kio_tail(") <> action <> ");")
    _ ->
      let core = if discard then "kio_effect(" <> action <> ")" else action
          wrapped = foldl (\acc (arr, cnt) -> "kio_finally(" <> acc <> ", " <> arr <> ", " <> cnt <> ")") core frames
       in emit ("return " <> wrapped <> ";")

-- | Register a §18.7 deferred action into the given (arr, cnt) frame.
registerDefer :: (Text, Text) -> Text -> Gen ()
registerDefer (arr, cnt) te = emit (arr <> "[" <> cnt <> "++] = " <> te <> ";")

-- | Like 'bindPat' but threads the concrete scrutinee C-expression
-- through the binding projections.
bindPatScrut :: Text -> Text -> CorePat -> Gen Text
bindPatScrut = bindPatScrutDup False

-- | Perceus RC S2.3a (§a): 'bindPatScrut' with an optional kept-field @kdup@.
-- When @dupFields@ is 'True' (the arm both owns the scrutinee cell and will drop
-- it at its 'SinkVar' seam — the 'dropHere' in 'consumeAltBody'), each bound field
-- projection @kctor_arg(sv,…)@ is wrapped in @kdup(…)@ so the surviving field
-- keeps a reference of its own before the following @kdrop(sv)@. S3.1 still only
-- maintains the paired rc invariant; S3.2 will make this the guard against freeing
-- a unique scrutinee cell while a projected field escapes. @kdup@ skips
-- immediates, so an immediate field is a runtime no-op. With @dupFields@ 'False'
-- this is exactly the old
-- 'bindPatScrut' (byte-identical), so every non-match-destructure caller (the
-- do-kernel\/closure-arg\/let-pattern paths) and every returning-arm match is
-- unchanged.
bindPatScrutDup :: Bool -> Text -> Text -> CorePat -> Gen Text
bindPatScrutDup dupFields sv env pat = do
  lvals <- gets gsParamLvals
  let wrap valExpr = if dupFields then "kdup(" <> valExpr <> ")" else valExpr
  if null lvals
    then foldM push env (patBindings sv pat) -- boxed: kpush each onto the KEnv
    else do
      -- R2.3-rest FLAT worker: bind each pattern variable to a C local via
      -- 'bindFlatLocal' (the LAST binding becomes de Bruijn index 0, matching
      -- the kpush order); the scope is restored by the enclosing 'captured'.
      let vals = patBindings sv pat
          n = length vals
      forM_ (zip [0 ..] vals) $ \(j, valExpr) -> do
        bid <- currentPatSlotBinderId (n - 1 - j)
        void (bindFlatLocal "pat_" (Just bid) dupFields (wrap valExpr))
      gets gsEnv -- unchanged (flat reads via gsParamLvals, not the KEnv)
  where
    push e valExpr = do
      n <- freshN "env_"
      let v = if dupFields then "kdup(" <> valExpr <> ")" else valExpr
      emit ("KEnv *" <> n <> " = kpush(" <> v <> ", " <> e <> ");")
      pure n

-- | R2.3-rest: bind @valExpr@ to a fresh C local in a flat worker and prepend
-- it to 'gsParamLvals' as de Bruijn index 0 (params and earlier binders shift
-- up); the enclosing 'captured' block restores the scope.  Returns the C name.
bindFlatLocal :: Text -> Maybe BinderId -> Bool -> Text -> Gen Text
bindFlatLocal prefix mbid ownsRef valExpr = do
  v <- freshN prefix
  emit ("KValue *" <> v <> " = " <> valExpr <> ";")
  modify' $ \st ->
    st
      { gsParamLvals = v : gsParamLvals st
      , gsParamBinders = mbid : gsParamBinders st
      , gsParamOwns = ownsRef : gsParamOwns st
      }
  pure v

compileKIf :: [(Term, [KItem])] -> Maybe [KItem] -> Gen ()
compileKIf alts mels = go 0 alts
  where
    armCount = length alts

    go _ [] = case mels of
      Just els -> withChild (P.kIfElsePos armCount) (emitBlock els)
      Nothing -> pure ()
    go ai ((c, body) : more) = do
      ce <- withChild (P.kIfCondPos ai) (compile c)
      emit ("if (kas_bool(" <> ce <> ")) {")
      env <- gets gsEnv
      (blk, ()) <- withChild (P.kIfBodyPos ai) (captured env (compileItems Nothing Nested body))
      forM_ blk (emit . ("  " <>))
      emit "}"
      unless (null more && mels == Nothing) $ do
        emit "else {"
        go (ai + 1) more
        emit "}"
    emitBlock items = do
      env <- gets gsEnv
      (blk, ()) <- captured env (compileItems Nothing Nested items)
      emit "{"
      forM_ blk (emit . ("  " <>))
      emit "}"

-- | Compile a do-block's TAIL statement-`if`: every branch is compiled in
-- 'TailEffect' (so each path ends in a @return@ — a recursive IO call in a
-- branch defers via @kio_effect@ rather than recursing through @krun_io@,
-- §27.5A.3), and a missing/exhausted else yields Unit (§18.8 — the if's
-- normal completion is discarded).
compileKIfTail :: ScopeMode -> [(Term, [KItem])] -> Maybe [KItem] -> Gen ()
compileKIfTail tailMode alts mels = goAlts 0 alts
  where
    armCount = length alts

    goAlts _ [] = case mels of
      Just els -> withChild (P.kIfElsePos armCount) (emitBranch els)
      Nothing -> emitTailReturn "kunit()" -- no/exhausted else: yield Unit, flush defers
    goAlts ai ((c, body) : more) = do
      ce <- withChild (P.kIfCondPos ai) (compile c)
      emit ("if (kas_bool(" <> ce <> ")) {")
      withChild (P.kIfBodyPos ai) (emitBranch body)
      emit "} else {"
      goAlts (ai + 1) more
      emit "}"
    emitBranch items = do
      env <- gets gsEnv
      (blk, ()) <- captured env (compileItems Nothing tailMode items)
      forM_ blk (emit . ("  " <>))

data LoopKind = LoopWhile !KCond | LoopFor !CorePat !Term

compileLoopCond :: KCond -> Gen Text
compileLoopCond = \case
  KCondPure t -> compile t
  KCondAction t -> compile t >>= emitRunIOValue "cond_"

-- | Compile a @while@\/@for@ loop using explicit @goto@ labels, so §18.2.5
-- labelled @break@\/@continue@ targeting an outer loop work uniformly and
-- the §18.8 @else@ (run only on normal completion, not after a @break@) is
-- placed past the body and before the break label.
compileLoop :: Maybe Text -> LoopKind -> [KItem] -> Maybe [KItem] -> Gen ()
compileLoop mlabel kind body mels = do
  env <- gets gsEnv
  n <- freshN "lp_"
  let contL = "kcont_" <> n -- continue target (re-test)
      advL = "kadv_" <> n -- for-loop advance (continue lands here)
      normL = "knorm_" <> n -- normal completion (run else)
      endL = "kend_" <> n -- break target (skip else)
      -- continue re-tests; for a `for` it must advance the cursor first.
      contTarget = case kind of LoopWhile _ -> contL; LoopFor _ _ -> advL
  -- the Nested defer-frame depth OUTSIDE this loop's body; a break/continue
  -- to this loop unwinds the frames pushed since (§18.7, see gotoLoop).
  scopeDepth <- gets (length . gsScopeDefers)
  let ctx = LoopCtx mlabel contTarget endL scopeDepth
  -- A label is emitted only when something jumps to it (continue → advL,
  -- break → endL), so the generated loop has no unused goto labels under
  -- -Wall; contL/normL are always part of the loop's own control flow.
  let usesLabel l = any (T.isInfixOf ("goto " <> l))
  -- §32.2.6 back-edge safe point (FINDING A): this boxed loop runs under the
  -- synchronous krun_io bridge with no CK re-entry, so a pending interrupt is
  -- observed ONLY when we call krt2_safepoint() at the back-edge.  One register
  -- counter per loop, reloaded to KRT2_SP_QUANTUM, gates the (cheap) check — see
  -- emitSafepointAbort.  Without this an infinite general `for`/`while` (a
  -- readRef/writeRef body, any closure — anything outside the scalar fast path)
  -- would HANG an interrupted fiber, breaking the interp==native invariant (the
  -- interpreter installs loopSafepoint at every while AND for back-edge).
  spc <- freshN "spc_"
  emit ("int64_t " <> spc <> " = KRT2_SP_QUANTUM;")
  bodyBlk <- case kind of
    LoopWhile cond -> do
      (condBlk, ce) <- withChild P.kWhileCondPos (captured env (compileLoopCond cond))
      (bb, ()) <- withChild P.kWhileBodyPos (withLoop ctx (captured env (compileItems mlabel Nested body)))
      emit (contL <> ": ;")
      forM_ condBlk (emit . ("  " <>))
      emit ("if (!kas_bool(" <> ce <> ")) goto " <> normL <> ";")
      forM_ bb emit
      emitSafepointAbort spc
      emit ("goto " <> contL <> ";")
      pure bb
    LoopFor pat src -> do
      se <- withChild P.kForSourcePos (compile src)
      it <- freshN "it_"
      emit ("KValue *" <> it <> " = " <> se <> ";")
      (bb, ()) <- withChild P.kForBodyPos $ withLoop ctx $ captured env $ case pat of
        -- a wildcard element binds nothing: skip the unused element var
        CPWild -> compileItems mlabel Nested body
        _ -> do
          elemV <- freshN "elem_"
          emit ("KValue *" <> elemV <> " = kctor_arg(" <> it <> ", 0);")
          e' <- bindPatScrut elemV env pat
          withEnv e' (compileItems mlabel Nested body)
      emit (contL <> ": ;")
      emit ("if (!kis_cons(" <> it <> ")) goto " <> normL <> ";")
      forM_ bb emit
      when (usesLabel advL bb) $ emit (advL <> ": ;")
      emit (it <> " = kctor_arg(" <> it <> ", 1);")
      emitSafepointAbort spc
      emit ("goto " <> contL <> ";")
      pure bb
  emit (normL <> ": ;")
  elsBlk <- case mels of
    Just els -> do
      let elseChild = case kind of
            LoopWhile _ -> P.kWhileElsePos
            LoopFor {} -> P.kForElsePos
      (eb, ()) <- withChild elseChild (captured env (compileItems Nothing Nested els))
      emit "{"
      forM_ eb (emit . ("  " <>))
      emit "}"
      pure eb
    Nothing -> pure []
  when (usesLabel endL bodyBlk || usesLabel endL elsBlk) $ emit (endL <> ": ;")

-- | Run an action with @ctx@ pushed as the innermost enclosing loop.
withLoop :: LoopCtx -> Gen a -> Gen a
withLoop ctx act = do
  saved <- gets gsLoops
  modify' $ \g -> g {gsLoops = ctx : saved}
  r <- act
  modify' $ \g -> g {gsLoops = saved}
  pure r

-- | §18 let? else branch: bind the residue pattern and run the else action
-- as the scope's result (it replaces the rest of the scope).  With no
-- @else@, a failed let? is a runtime defect (no Alternative available).
compileLetQElse :: ScopeMode -> Text -> Maybe (CorePat, Term) -> Gen ()
compileLetQElse mode sv mElse = case mElse of
  Nothing -> emit "krt_fail(\"let? pattern failed and no Alternative is available\");"
  Just (rp, fe) -> do
    env <- gets gsEnv
    -- §18.2.1: the else residue pattern is matched against the SCRUTINEE; a
    -- refutable residue that does not match is a runtime error — mirroring the
    -- interpreter (`matchPat ec rp x` -> Nothing -> "let? else: residue
    -- pattern failed").  Without this test the backend would bind the wrong
    -- constructor's fields and run the else body, silently diverging.
    mtest <- patTest sv rp
    case mtest of
      Just test -> emit ("if (!(" <> test <> ")) krt_fail(\"let? else: residue pattern failed\");")
      Nothing -> pure ()
    env' <- bindPatScrut sv env rp
    fee <- withEnv env' (withChild P.kLetQElsePos (compile fe))
    -- the else action replaces the rest of the scope, so it is the tail:
    -- defer it (stack-safe, §27.5A.3, with finalizers) the same way a
    -- trailing KExpr is.
    case mode of
      Tail -> emitTailIO False fee
      TailEffect -> emitTailIO True fee
      Nested -> emitRunIODiscard fee
