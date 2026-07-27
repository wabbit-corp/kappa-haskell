{-# LANGUAGE OverloadedRecordDot #-}

-- | Native backend: lower S5.A 'Kappa.Backend.IR.BackendTerm' roots to C that
-- links against the @kappart@ runtime (see @runtime/kappart.h@ and
-- docs/NATIVE_BACKEND.md).
--
-- The main value/do lowering is a structural recursion over the separate
-- KBackendIR tree. Residual KCore reads in this module are planning/verification
-- inputs (for example scalar worker eligibility and suspender closure), not
-- ownership or value-emission side tables. Any unsupported backend node or
-- do-kernel item is a compile-time 'E_BACKEND_UNSUPPORTED' error naming the
-- construct (and the definition it appears in) — never a silent fallback to
-- interpreter behaviour.
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
  , backendIRValidationErrors
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
  , resultIsProofP
  ) where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Char (isAscii, isAsciiLower, isAsciiUpper, isDigit, ord)
import Data.List (sort)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, isJust, mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Control.Monad (foldM, forM, forM_, guard, unless, void, when)
import Control.Monad.State.Strict
import Kappa.Backend.IR
  ( BackendAlt (..)
  , BackendBinder (..)
  , BackendBinderId (..)
  , BackendBody (..)
  , BackendCond (..)
  , BackendCtorLayout (..)
  , BackendIRViolation (..)
  , BackendItem (..)
  , BackendMeta (..)
  , BackendNodeId (..)
  , BackendParam (..)
  , BackendPat (..)
  , BackendTerm (..)
  , BackendUse (..)
  , KBackendIR (..)
  , lowerKBackendIR
  , validateCoreCapabilities
  , validateKBackendIR
  )
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
import Kappa.Check (CheckState (..), CtorInfo (..), InstanceEntry (..))
import Kappa.Core
import Kappa.CoreOps (spineOfTerm)
import Kappa.Diagnostic
import Kappa.Eval (EvalCtx (..), GlobalDef (..), Globals (..), eval, force, quote)
import Kappa.Ownership
  ( BinderOwn (..)
  , UseKind (..)
  )
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

-- | S5.A fail-closed gate: the real KBackendIR tree must carry the node-local
-- facts the backend needs before either native emitter runs. Malformed lowered
-- trees fail closed before target emission.
backendIRValidationErrors :: CheckState -> GName -> [BackendError]
backendIRValidationErrors cs mainG =
  backendIRValidationErrorsFrom cs mainG
    (validateCoreCapabilities cs ++ validateKBackendIR (lowerKBackendIR cs))

backendIRValidationErrorsFrom :: CheckState -> GName -> [BackendIRViolation] -> [BackendError]
backendIRValidationErrorsFrom cs mainG findings =
  promotionErrors ++ otherErrors
  where
    promotions = [v | v <- findings, bivCode v == "E_PARAMETRIC_TYPE_PROMOTION"]
    others = [v | v <- findings, bivCode v /= "E_PARAMETRIC_TYPE_PROMOTION"]
    promotionErrors =
      [ BackendError
          (bivBody v)
          (Map.findWithDefault noSpan (bivBody v) (csDeclSites cs))
          "E_PARAMETRIC_TYPE_PROMOTION"
          (Just "kappa.type.parametric-promotion")
          "KCore capability verification"
          (bivMessage v)
      | v <- promotions
      ]
    otherErrors = case others of
      [] -> []
      _ ->
        [ backendUnsupported
            mainG
            (Map.findWithDefault noSpan mainG (csDeclSites cs))
            "KBackendIR validation"
            ( "KBackendIR validation found "
                <> T.pack (show (length others))
                <> " lowered-tree invariant violation(s); native codegen requires zero. First findings: "
                <> T.intercalate " | " (take 5 (map renderBackendIRViolation others))
            )
        ]

renderBackendIRViolation :: BackendIRViolation -> Text
renderBackendIRViolation v =
  gnameText (bivBody v)
    <> "@"
    <> nodeText (bivNode v)
    <> " "
    <> bivCode v
    <> ": "
    <> bivMessage v
  where
    nodeText (BackendNodeId n) = T.pack (show n)

-- ── Code-generation monad ────────────────────────────────────────────

data GenState = GenState
  { gsFresh :: !Int
  , gsStmts :: ![Text] -- ^ current function body, reversed
  , gsEnv :: !Text -- ^ C expression for the current KEnv*
  , gsParamLvals :: ![Text] -- ^ R2.3: in a FLAT (capture-free) first-order worker, the C lvalue for each de Bruijn index — the params (index @i@ = source param @n-1-i@) plus any @let@/@match@-bound locals prepended at index 0 (R2.3-rest); a 'CVar' reads the C local directly instead of walking @kvar(kw_env,i)@. Empty outside a flat worker body (then 'CVar' uses @kvar@).
  , gsParamBinders :: ![Maybe BackendBinderId] -- ^ Parallel to 'gsParamLvals': the KBackendIR ownership binder identity for each flat local when known. Needed by S2.3d branch-dead drops so codegen drops the already-bound C local for exactly the binder named by node metadata.
  , gsParamOwns :: ![Bool] -- ^ Parallel to 'gsParamLvals': whether the flat local currently owns a reference for generic ownership decisions (projection ownership, branch-dead drops, consuming-call moves). Constructor let-locals are owning when their RHS is a proven fresh allocation; pattern locals are owning only when the match path materialises or moves the field owner; worker parameters stay non-owning here until full callee-scope drop normalization lands.
  , gsParamReusable :: ![Bool] -- ^ Parallel to 'gsParamLvals': whether a consuming match scrutinee may attempt S5 runtime-guarded reuse. This is intentionally narrower than 'gsParamOwns': generated worker parameters can be reusable for a ktry_reuse_ctor branch without becoming generally droppable locals.
  , gsTopFlatFrame :: !Bool -- ^ True only while compiling a top-level flat worker body. S2.3d can treat a missing branch-dead binder mapping as path/metadata drift in this frame; nested flat closures may deliberately omit outer captured binders and therefore keep missing branch-drop locals leak-biased.
  , gsTop :: ![Text] -- ^ completed top-level C functions, reversed
  , gsProtos :: ![Text] -- ^ forward declarations, reversed
  , gsEmitted :: !(Set GName) -- ^ globals already emitted or enqueued
  , gsQueue :: ![GName] -- ^ globals still to emit
  , gsErrs :: ![BackendError] -- ^ unsupported-construct findings
  , gsCur :: !GName -- ^ definition currently being compiled (for diagnostics)
  , gsGlobals :: !(Map GName GlobalDef)
  , gsEvalCtx :: !EvalCtx -- ^ R2.2: a non-runtime EvalCtx (built from the CheckState) used only to 'quote' a global's 'gdType' to a Term so the per-parameter scalar kinds can be read from its Pi telescope.
  , gsBackendBodies :: !(Map GName BackendBody)
  , gsBodies :: !(Map GName Term)
  , gsIOMonadRefDicts :: !(Set GName)
  , gsSuspenders :: !(Set GName) -- ^ §3.3: globals that TRANSITIVELY reach a suspending primitive (fork/await/…); computed once from gsBodies. A do-bind whose action's spine head is in here may suspend, so its do-block is CPS-lowered.
  , gsRcEnabled :: !Bool -- ^ Perceus RC maintenance gate. Default ON for native builds; @KAPPA_PERCEUS_RC=0@ is the explicit byte-identical baseline and emits @krc_set_enabled(0)@ so generated @kdup@/@kdrop@ maintenance has no runtime counting/freeing effect. S4 publish marking still emits because shared bits are synchronization metadata for Ref/Array storage. When enabled, non-erased runtime variables consume node-local KBackendIR 'BackendUse' metadata, and binders/drops consume 'BackendBinder'/'BackendMeta' metadata.
  , gsReuseEnabled :: !Bool -- ^ S5 FBIP reuse gate. This is intentionally separate from 'gsRcEnabled': @KAPPA_PERCEUS_REUSE=0@ leaves RC maintenance and validation active while disabling only drop-guided in-place reuse sites for reuse-on/off differentials.
  , gsRcFindings :: ![Text] -- ^ Perceus RC validation log, populated only when 'gsRcEnabled'. With S5.A this is limited to impossible missing KBackendIR node-local ownership metadata after validation; ordinary dup/drop decisions read 'BackendUse'/'BackendBinder' fields directly.
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
  , flsBinders :: ![Maybe BackendBinderId]
  , flsOwns :: ![Bool]
  , flsReusable :: ![Bool]
  }

saveFlatLocalScope :: Gen FlatLocalScope
saveFlatLocalScope =
  FlatLocalScope
    <$> gets gsParamLvals
    <*> gets gsParamBinders
    <*> gets gsParamOwns
    <*> gets gsParamReusable

restoreFlatLocalScope :: FlatLocalScope -> Gen ()
restoreFlatLocalScope saved =
  modify' $ \g ->
    g
      { gsParamLvals = flsLvals saved
      , gsParamBinders = flsBinders saved
      , gsParamOwns = flsOwns saved
      , gsParamReusable = flsReusable saved
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

rcRecordFinding :: Text -> Gen ()
rcRecordFinding msg =
  modify' $ \st -> st {gsRcFindings = msg : gsRcFindings st}

rcMetadataMiss :: GName -> Maybe Int -> Text -> Text
rcMetadataMiss g mi detail =
  gKey g
    <> maybe "" (\i -> " var#" <> T.pack (show i)) mi
    <> ": "
    <> detail

-- | The S2.3b use verdict plus the consume/read bit attached to THIS lowered
-- variable node. A missing node-local use after 'validateKBackendIR' is an
-- internal invariant failure and remains fail-closed in RC-on builds.
rcUseInfoOf :: Maybe BackendUse -> Maybe Int -> Gen (Maybe (UseKind, Bool))
rcUseInfoOf use mi = do
  enabled <- gets gsRcEnabled
  if not enabled
    then pure Nothing
    else case use of
      Just u -> pure (Just (buUseKind u, buConsumes u))
      Nothing -> do
        g <- gets gsCur
        rcRecordFinding $
          rcMetadataMiss g mi "KBackendIR variable node has no BackendUse metadata"
        pure Nothing

-- | Wrap a 'CVar' use-expression in @kdup(...)@ when the analysis classified the
-- occurrence as a consuming 'NonLast' (S2.2 / b.2 plus S2.3b): the value is used
-- again downstream and the current consumer receives its own reference. Read-only
-- 'NonLast' occurrences (projection bases, borrowed call args) leave the bare
-- expression, since no consumer-side drop will balance a dup. 'kdup' skips
-- immediates (its @kis_imm@ guard), so an immediate-valued binder wrap is a
-- runtime no-op.
rcDupVarUse :: Maybe BackendUse -> Int -> Text -> Gen Text
rcDupVarUse use i e = do
  mi <- rcUseInfoOf use (Just i)
  pure $ case mi of
    Just (NonLast, True) -> "kdup(" <> e <> ")"
    _ -> e

-- | Compile the raw C expression for a variable occurrence after validating its
-- node-local ownership metadata. This intentionally does not apply a dup/move
-- policy; callers choose that policy according to the value-flow context.
compileVarRef :: Maybe BackendUse -> Int -> Gen Text
compileVarRef use i = do
  void (rcUseInfoOf use (Just i))
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
compileOwnedVarUse :: Maybe BackendUse -> Int -> Gen Text
compileOwnedVarUse = compileOwnedVarUseWithReusable False

-- | Variant used only for direct calls to known KBackendIR workers whose
-- selected parameter convention consumes ownership. A flat worker parameter is
-- not generally droppable in its caller frame, but S5 marks it reusable so a
-- consuming LastUse can transfer the unique cell to the callee and let the
-- callee's runtime-guarded match reuse prove rc==1. Other owned positions keep
-- using 'compileOwnedVarUse', so reusable params do not become movable into
-- arbitrary stores/constructors.
compileOwnedVarUseWithReusable :: Bool -> Maybe BackendUse -> Int -> Gen Text
compileOwnedVarUseWithReusable allowReusable use i = do
  e <- compileVarRef use i
  rcOn <- gets gsRcEnabled
  if not rcOn
    then pure e
    else do
      mi <- rcUseInfoOf use (Just i)
      sourceOwns <- flatLocalOwnsAt i
      sourceReusable <- if allowReusable then flatLocalReusableAt i else pure False
      let canMove = sourceOwns || sourceReusable
      let needsDup = case mi of
            Just (_, False) -> False
            Just (NonLast, True) -> True
            Just (LastUse, True) -> not canMove
            Just (Borrowed, True) -> True
            Nothing -> not canMove
      pure $ if needsDup then "kdup(" <> e <> ")" else e

-- | A projection such as @p.left@ borrows its field from the owning aggregate
-- @p@. When that projection result is itself going to be returned, stored in an
-- owning local, or transferred to a consuming call, codegen must materialise an
-- owned reference with @kdup@ before any later cleanup can drop @p@. The proof is
-- the structural base term plus the ownership side table for that exact base use:
-- an owned flat local read in a non-consuming position. No field-name recognition.
rcProjectionResultCanOwn :: BackendTerm -> Gen Bool
rcProjectionResultCanOwn = \case
  BVar _ use i -> do
    mi <- rcUseInfoOf use (Just i)
    sourceOwns <- flatLocalOwnsAt i
    pure $ sourceOwns && case mi of
      Just (_, False) -> True
      _ -> False
  BSeal _ _ e -> (rcProjectionResultCanOwn e)
  _ -> pure False

rcOwnProjectionResult :: Bool -> BackendTerm -> Text -> Gen Text
rcOwnProjectionResult needOwned base raw =
  if not needOwned
    then pure raw
    else do
      canOwn <- (rcProjectionResultCanOwn base)
      pure $ if canOwn then "kdup(" <> raw <> ")" else raw

flatLocalOwnsAt :: Int -> Gen Bool
flatLocalOwnsAt i = do
  owns <- gets gsParamOwns
  pure $ case drop i owns of
    own : _ -> own
    [] -> False

flatLocalReusableAt :: Int -> Gen Bool
flatLocalReusableAt i = do
  reusable <- gets gsParamReusable
  pure $ case drop i reusable of
    reuse : _ -> reuse
    [] -> False

withFlatLocalOwnership :: Maybe BackendBinderId -> Bool -> Gen a -> Gen a
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
          , gsParamReusable = ownsRef : gsParamReusable st
          }
      r <- act
      restoreFlatLocalScope saved
      pure r

-- | Conservative S2.3b/S2.3d ownership result check for a flat @let@
-- initializer.
-- Scope-close drops are only safe when the local is known to hold an owned
-- reference. Projection results are accepted only when the base-use metadata
-- proves an owned aggregate is read in a non-consuming position and the result
-- site can materialise an owned @kdup@; unproven call/projection shapes stay
-- leak-biased. A saturated eta-expanded constructor application is accepted
-- because this same structural recognizer is what codegen beta-reduces to a
-- direct fresh @kctor@ allocation; this is symbolically tied to the Core shape,
-- not to a source spelling.
rcTermProducesOwnedHere :: BackendTerm -> Gen Bool
rcTermProducesOwnedHere t = case t of
  BApp {}
    | Just {} <- etaCtorApp t -> pure True
  BApp {} -> directWorkerCallReturnsOwned t
  BVar _ use i -> do
    mi <- rcUseInfoOf use (Just i)
    sourceOwns <- flatLocalOwnsAt i
    pure $ case mi of
      Just (LastUse, True) -> sourceOwns
      Just (NonLast, True) -> True
      _ -> False
  BCtor {} -> pure True
  BRecord {} -> pure True
  BInject {} -> pure True
  BThunk {} -> pure True
  BLazy {} -> pure True
  BSeal _ _ e -> (rcTermProducesOwnedHere e)
  BProj _ e _ _ -> (rcProjectionResultCanOwn e)
  BIf _ _ th el ->
    (&&)
      <$> (rcTermProducesOwnedHere th)
      <*> (rcTermProducesOwnedHere el)
  BLet _ mb _ _ rhs body -> do
    rhsOwns <- (rcTermProducesOwnedHere rhs)
    withFlatLocalOwnership (bbBinderId <$> mb) rhsOwns $
      (rcTermProducesOwnedHere body)
  BLetRec _ mb _ _ rhs body -> do
    rhsOwns <- (rcTermProducesOwnedHere rhs)
    withFlatLocalOwnership (bbBinderId <$> mb) rhsOwns $
      (rcTermProducesOwnedHere body)
  BMatch _ _ alts _ ->
    and
      <$> forM
        alts
          ( \(BackendAlt _ _ _ _ body) ->
              (rcTermProducesOwnedHere body)
          )
  _ -> pure False

directWorkerCallReturnsOwned :: BackendTerm -> Gen Bool
directWorkerCallReturnsOwned term = do
  bodies <- gets gsBackendBodies
  pure $ case spineOf term of
    (BGlob _ g, args) ->
      case Map.lookup g bodies of
        Just body
          | length args == length (bbParams body) ->
              workerBodyReturnsOwned bodies Set.empty body
        _ -> False
    _ -> False

workerBodyReturnsOwned :: Map GName BackendBody -> Set GName -> BackendBody -> Bool
workerBodyReturnsOwned bodies seen body =
  termReturnsOwned bodies (Set.insert (bbOwner body) seen) initialOwns (bbRoot body)
  where
    initialOwns = reverse (map workerParamOwns (bbParams body))

termReturnsOwned :: Map GName BackendBody -> Set GName -> [Bool] -> BackendTerm -> Bool
termReturnsOwned bodies seen owns = go owns
  where
    go env = \case
      term@BApp {} ->
        case etaCtorApp term of
          Just {} -> True
          Nothing -> workerCallReturnsOwnedStatic seen term
      BVar _ use i -> varUseReturnsOwned env use i
      BCtor {} -> True
      BRecord {} -> True
      BInject {} -> True
      BThunk {} -> True
      BLazy {} -> True
      BSeal _ _ e -> go env e
      -- A worker tail-returning a projection currently emits the borrowed
      -- projection expression unless the local sink has cleanup that forces
      -- materialisation. A caller-side direct-call proof cannot see that sink
      -- cleanup, so it must not classify projection returns as owned.
      BProj {} -> False
      BIf _ _ th el -> go env th && go env el
      BLet _ _ _ _ rhs body ->
        let rhsOwns = go env rhs
         in go (rhsOwns : env) body
      BLetRec _ _ _ _ rhs body ->
        let rhsOwns = go env rhs
         in go (rhsOwns : env) body
      BMatch _ _ alts _ ->
        all
          ( \(BackendAlt _ _ binders _ body) ->
              -- Pattern binders are borrowing projections out of the scrutinee
              -- unless the emitting arm pairs them with an explicit dup/drop
              -- cleanup. This structural callee summary has no sink-local
              -- cleanup information, so pattern locals are conservatively
              -- non-owned and outer variables are shifted behind them.
              go (replicate (length binders) False <> env) body
          )
          alts
      _ -> False

    workerCallReturnsOwnedStatic seen0 term =
      case spineOf term of
        (BGlob _ g, args) ->
          case Map.lookup g bodies of
            Just body
              | length args == length (bbParams body) ->
                  if g `Set.member` seen0
                    then True
                    else workerBodyReturnsOwned bodies seen0 body
            _ -> False
        _ -> False

    varUseReturnsOwned env use i =
      case drop i env of
        own : _ ->
          case use of
            Just (BackendUse _ LastUse True) -> own
            Just (BackendUse _ NonLast True) -> True
            _ -> False
        [] -> False

-- | The S2.3 drop DECISION for a lowered binder node. Returns 'True' iff a
-- @kdrop@ against the binder's bound C local should be emitted at that scope's
-- close (b.4):
--
--   * the binder is 'boDroppable' (@0@\/@≤1@\/@ω@ — carries no consumption
--     obligation) and NOT 'boBorrowed' (a borrowed value is the caller's; the
--     callee never drops it — §1\/§3); AND
  --   * the binder has NO consuming 'LastUse' occurrence in its scope
  --     ('oiBinderConsumingUses' holds no 'LastUse'). Non-consuming projection
  --     reads may coexist with the close-drop because projection results are now
  --     owned at the result/let/consuming-call sites that can outlive the aggregate.
  --     S2.3d branch-dead drops are handled separately by
--     'rcEmitBranchDeadDropsHere', using explicit node-local drop sites and the
--     current flat-local ownership metadata; this helper remains the ordinary
--     whole-scope close-drop gate.
--
-- Inert under the OFF baseline. Missing binder metadata yields 'False' after
-- 'validateKBackendIR' has already made that a compile-time error.
rcBinderDroppableHere :: Maybe BackendBinder -> Gen Bool
rcBinderDroppableHere mb = do
  enabled <- gets gsRcEnabled
  pure $ enabled && case mb of
    Just (BackendBinder _ _ bo hasConsumingLastUse) ->
      boDroppable bo && not (boBorrowed bo) && not hasConsumingLastUse
    Nothing -> False

branchDropAllowedBinder :: BackendBinder -> Bool
branchDropAllowedBinder (BackendBinder _ _ bo _) =
  boDeclQ bo /= Q0 && boDroppable bo && not (boBorrowed bo)

-- | Emit a @kdrop(<lval>)@ statement against a bound C LOCAL (b.4 / R-flat:
-- ALWAYS the bound local, never a fresh @kvar(env,i)@ rvalue re-read). The
-- runtime decrements RC and, in S3/S4, may reclaim strict FREESET values at zero;
-- the @kdrop@ assert remains the primary differential check for underflow.
rcEmitDrop :: Text -> Gen ()
rcEmitDrop lv = emit ("kdrop(" <> lv <> ");")

-- | S2.3d branch-dead drop emission. The KBackendIR node names binders that are
-- absent from this selected branch while live in a sibling path; this helper
-- resolves those lowered binder identities to the current flat C locals and
-- emits drops only when the local is known to own a reference. No guessed @kvar@
-- reread, no name-based match, and no structural path lookup.
cleanupDropLvals :: [Text] -> Set Text
cleanupDropLvals =
  Set.fromList . mapMaybe parse
  where
    parse line =
      case T.stripPrefix "kdrop(" line >>= T.stripSuffix ");" of
        Just lv -> Just lv
        Nothing -> Nothing

rcEmitBranchDeadDropsHere :: [Text] -> BackendMeta -> Gen ()
rcEmitBranchDeadDropsHere scheduledCleanup meta = do
  enabled <- gets gsRcEnabled
  when enabled $ do
    g <- gets gsCur
    lvals <- gets gsParamLvals
    bids <- gets gsParamBinders
    owns <- gets gsParamOwns
    topFlat <- gets gsTopFlatFrame
    let siteBids = bmBranchDrops meta
        flat = zip3 lvals bids owns
        knownFlatBids = [bid | (_, Just bid, _) <- flat]
        bidOf (BackendBinder bid _ _ _) = bid
        originOf (BackendBinder _ origin _ _) = origin
        lvalFor binder =
          case [lv | (lv, Just bid', True) <- flat, bid' == bidOf binder] of
            lv : _ -> Just lv
            [] -> Nothing
        scheduled = cleanupDropLvals scheduledCleanup
        targets0 =
          [ lv
          | binder <- siteBids
          , branchDropAllowedBinder binder
          , Just lv <- [lvalFor binder]
          ]
        targets = filter (`Set.notMember` scheduled) targets0
        unresolved =
          [ originOf binder <> " => " <> T.pack (show (bidOf binder))
          | binder <- siteBids
          , branchDropAllowedBinder binder
          , bidOf binder `notElem` knownFlatBids
          ]
    case unresolved of
      _ | not topFlat -> pure ()
      [] -> pure ()
      _ ->
        rcRecordFinding $
          rcMetadataMiss
            g
            Nothing
            ( "branch drop site listed droppable binder(s) with no top-level flat-local metadata: "
                <> T.intercalate ", " unresolved
            )
    mapM_ rcEmitDrop targets

backendTermMeta :: BackendTerm -> BackendMeta
backendTermMeta = \case
  BUnit meta -> meta
  BVar meta _ _ -> meta
  BGlob meta _ -> meta
  BLit meta _ -> meta
  BLam meta _ _ _ _ _ -> meta
  BApp meta _ _ -> meta
  BCtor meta _ _ -> meta
  BMatch meta _ _ _ -> meta
  BRecord meta _ -> meta
  BProj meta _ _ _ -> meta
  BInject meta _ _ -> meta
  BLet meta _ _ _ _ _ -> meta
  BLetRec meta _ _ _ _ _ -> meta
  BDo meta _ _ -> meta
  BSeal meta _ _ -> meta
  BThunk meta _ -> meta
  BLazy meta _ -> meta
  BForce meta _ -> meta
  BIf meta _ _ _ -> meta

-- | Perceus RC S2.3a (§a) — the MATCH-DESTRUCTURE cell-drop DECISION.
--
-- A @match@'s arms read their scrutinee's fields out via BORROWING projections
-- (@kctor_arg@\/@kproj@\/@krec_at@\/@kvariant_payload@ all return the field
-- without an incref), so once the bound fields are dup'd-out the scrutinee CELL
-- itself is leaked unless the match drops it. This decides, from the SCRUTINEE
-- shape and (for a 'BVar' scrutinee) its node-local use verdict plus consume bit,
-- whether the match owns a reference to the cell that it must discharge with a
-- @kdrop(sv)@:
--
--   * a __'BVar'__ scrutinee — read the use verdict and consume bit attached to
--     that lowered variable node. Drop for consuming 'LastUse' only when the
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
rcScrutDropDecision :: BackendTerm -> Gen Bool
rcScrutDropDecision scrut = do
  enabled <- gets gsRcEnabled
  if not enabled
    then pure False
    else (go scrut)
  where
    go = \case
      BVar _ use i -> do
        -- Drop only when the resolved occurrence is consuming and the
        -- match owns the reference it compiled: a consuming NonLast has been
        -- dup'd at the CVar site, while a consuming LastUse is droppable only
        -- if the source flat local itself owns the value. S5 reusable worker
        -- params are reported separately by 'rcScrutReuseDecision' because
        -- they are consumed only at the matched-arm seam, not as generally
        -- owned locals.
        mi <- rcUseInfoOf use (Just i)
        sourceOwns <- flatLocalOwnsAt i
        pure $ case mi of
          Just (LastUse, True) -> sourceOwns
          Just (NonLast, True) -> True
          _ -> False
      t@BApp {}
        | Just {} <- etaCtorApp t -> pure True
      -- Fresh owning allocations: rc==1, die at the match.
      BCtor {} -> pure True
      BRecord {} -> pure True
      BInject {} -> pure True
      BSeal _ _ e -> (go e)
      -- General calls and projections can return borrowed references. Without
      -- result ownership metadata, do not drop them as match-owned cells.
      _ -> pure False

-- | S5.B reusable-parameter consumption is narrower than normal ownership
-- cleanup. A flat worker parameter may be transferred into a same-size match
-- rebuild even though the backend still keeps parameters borrowed for generic
-- branch cleanup and arbitrary consuming calls. This decision is intentionally
-- independent from the reuse-emission kill switch: @KAPPA_PERCEUS_REUSE=0@
-- disables the in-place rewrite primitives, but the callee still owns the
-- transferred parameter and must consume it through the ordinary dup/drop path.
rcScrutReuseDecision :: BackendTerm -> Gen Bool
rcScrutReuseDecision scrut = do
  rcOn <- gets gsRcEnabled
  if not rcOn
    then pure False
    else go scrut
  where
    go = \case
      BVar _ use i -> do
        mi <- rcUseInfoOf use (Just i)
        sourceReusable <- flatLocalReusableAt i
        pure $ case mi of
          Just (LastUse, True) -> sourceReusable
          _ -> False
      BSeal _ _ e -> go e
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
-- §11 Ordering is runtime-built by the ordinary TypeLevel comparison primitive,
-- so LT/EQ/GT are fixed runtime constructors alongside Exit/Cause outcomes.
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
-- Perceus RC validation is enabled, the result also carries KBackendIR metadata
-- findings so the IO driver can report them on both successful and failed
-- builds.
generateC :: Bool -> Bool -> CheckState -> GName -> Set Text -> Map GName ResolvedNativeSymbol -> Either ([BackendError], Maybe [Text]) (Text, Maybe [Text])
generateC rcEnabled reuseEnabled cs mainG ffiPrims hostSyms =
  let backendIr = lowerKBackendIR cs
      backendIrFindings =
        validateCoreCapabilities cs ++ validateKBackendIR backendIr
      backendIrErrs = backendIRValidationErrorsFrom cs mainG backendIrFindings
      backendIrReport = map renderBackendIRViolation backendIrFindings
      mBackendIrReport = if rcEnabled then Just backendIrReport else Nothing
   in if not (null backendIrErrs)
        then Left (backendIrErrs, mBackendIrReport)
        else
          let evalCtx0 = EvalCtx (Globals (csGlobals cs)) (csMetas cs) False (csFacts cs)
              st0 =
                GenState
                  { gsFresh = 0
                  , gsStmts = []
                  , gsEnv = "0"
                  , gsParamLvals = []
                  , gsParamBinders = []
                  , gsParamOwns = []
                  , gsParamReusable = []
                  , gsTopFlatFrame = False
                  , gsTop = []
                  , gsProtos = []
                  , gsEmitted = Set.singleton mainG
                  , gsQueue = [mainG]
                  , gsErrs = []
                  , gsCur = mainG
                  , gsGlobals = csGlobals cs
                  , gsEvalCtx = evalCtx0
                  , gsBackendBodies = kbirBodies backendIr
                  , gsBodies = csCoreBodies cs
                  , gsIOMonadRefDicts = ioMonadRefDicts (csInstances cs)
                  , gsSuspenders = suspenderGlobalsWith (blockingHostGlobals hostSyms) evalCtx0 (csGlobals cs) (csCoreBodies cs)
                  , gsRcEnabled = rcEnabled
                  , gsReuseEnabled = rcEnabled && reuseEnabled
                  , gsRcFindings = []
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
              rcFindings = backendIrReport ++ reverse (gsRcFindings final)
              rcErrs = rcFindingErrors (gsRcEnabled final) mainG (Map.findWithDefault noSpan mainG (csDeclSites cs)) rcFindings
              mRcFindings = if gsRcEnabled final then Just rcFindings else Nothing
           in case reverse (gsErrs final) ++ multishotErrs ++ rcErrs of
                [] -> Right (assemble final, mRcFindings)
                errs -> Left (errs, mRcFindings)

ioMonadRefDicts :: [InstanceEntry] -> Set GName
ioMonadRefDicts =
  Set.fromList
    . map ieDict
    . filter isIOMonadRefInstance
  where
    isIOMonadRefInstance ie =
      ieTrait ie == Builtins.prelMonadRef
        && gnameModule (ieDict ie) == Builtins.preludeModule
        && case ieHead ie of
          [t] -> termHeadGlob t == Just Builtins.prelIO
          _ -> False
    gnameModule (GName m _) = m
    termHeadGlob = \case
      CApp _ f _ -> termHeadGlob f
      CUniverseLift _ _ _ t -> termHeadGlob t
      CGlob g -> Just g
      CGlobal g _ -> Just g
      _ -> Nothing

rcFindingErrors :: Bool -> GName -> Span -> [Text] -> [BackendError]
rcFindingErrors False _ _ _ = []
rcFindingErrors True _ _ [] = []
rcFindingErrors True mainG sp findings =
  [ backendUnsupported
      mainG
      sp
        "Perceus RC KBackendIR ownership metadata"
        ( "Perceus RC validation found "
            <> T.pack (show (length findings))
            <> " missing KBackendIR ownership metadata finding(s); S5.A requires zero so native emission cannot silently suppress dup/drop decisions. First findings: "
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
  backendBodies <- gets gsBackendBodies
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
  case Map.lookup g backendBodies of
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
    Just body -> do
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
      erasable <- (proof ||) <$> isErasableArg (bbRoot body)
      if erasable
        then do
          (stmts, _) <- captured "0" (pure ())
          finishGlobal ident stmts "kunit()"
        else case (length (bbParams body), bbRoot body) of
          -- A function global is lowered to a worker (a loop, so a tail
          -- self-call runs in constant C stack) plus a curried closure for
          -- partial application and first-class use.
          (n, inner) | n >= 1 -> compileFunctionGlobal g (bbParams body) inner
          _ -> do
            -- A CAF body sits at the KBackendIR root.
            (stmts, e) <- captured "0" (compile (bbRoot body))
            finishGlobal ident stmts e

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
bodyCapturesEnv :: BackendTerm -> Bool
bodyCapturesEnv = go
  where
    go t = case t of
      BLam {} -> True -- kclo(fn, env)
      BLetRec {} -> True -- recursive closure captures the binder cell
      BDo {} -> True -- kio(fn, env)
      BThunk {} -> True -- kthunk(fn, env, 0)  (Delay)
      BLazy {} -> True -- kthunk(fn, env, 1)  (Memo)
      -- P0-B: a saturated eta-expanded constructor application lowers to a
      -- direct 'kctor' (no 'kclo' over the env — see 'etaCtorApp'), so it
      -- captures its field VALUES, not the env, exactly like a 'CCtor'.
      -- Look through the eta lambdas to the real fields so this no longer
      -- forces the per-iteration env rebuild.
      BApp {} | Just (_, ctorArgs) <- etaCtorApp t -> any go ctorArgs
      BApp _ f args -> go f || any (\(_, _, a) -> go a) args
      BCtor _ _ args -> any go args
      BMatch _ s alts _ -> go s || any goAlt alts
      BProj _ e _ _ -> go e
      BInject _ _ e -> go e
      BForce _ e -> go e
      BSeal _ _ e -> go e
      BLet _ _ _ _ rhs body -> go rhs || go body
      BIf _ c th el -> go c || go th || go el
      BRecord _ fs -> any (go . snd) fs
      BVar {} -> False
      BGlob {} -> False
      BUnit {} -> False
      BLit {} -> False
    goAlt (BackendAlt _ _ _ mg body) = maybe False go mg || go body

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
compileFunctionGlobal :: GName -> [BackendParam] -> BackendTerm -> Gen ()
compileFunctionGlobal g params inner = do
  rcOn <- gets gsRcEnabled
  let ident = cGlobIdent g
      worker = "kw_" <> mangle (gKey g)
      n = length params
      ps = ["p" <> T.pack (show i) | i <- [0 .. n - 1]]
      paramOwnsSource = if rcOn then map workerParamOwns params else replicate n False
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
  saved <- gets gsParamLvals
  savedBinders <- gets gsParamBinders
  savedOwns <- gets gsParamOwns
  savedReusable <- gets gsParamReusable
  savedTopFlat <- gets gsTopFlatFrame
  let paramBids = reverse (map (fmap bbBinderId . bpBinder) params)
      -- FLAT worker parameters are eligible for S5's runtime-guarded reuse
      -- branch, but they are not generally owned locals: branch-dead drops,
      -- projection ownership, and arbitrary consuming calls still require a
      -- locally materialized owner. This preserves the pre-S5 leak-biased
      -- parameter seam while allowing a ktry_reuse_ctor branch to prove and
      -- consume a unique scrutinee cell.
      paramOwns = replicate n False
      paramReusable = reverse paramOwnsSource
  modify' $ \st ->
    st
      { gsParamLvals = if flat then reverse ps else []
      , gsParamBinders = if flat then paramBids else []
      , gsParamOwns = if flat then paramOwns else []
      , gsParamReusable = if flat then paramReusable else []
      , gsTopFlatFrame = flat
      }
  (bodyStmts, ()) <- captured "kw_env" (consume (SinkTail ti) inner)
  modify' $ \st ->
    st
      { gsParamLvals = saved
      , gsParamBinders = savedBinders
      , gsParamOwns = savedOwns
      , gsParamReusable = savedReusable
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
              let collected =
                    [ let raw = "kvar(cenv, " <> T.pack (show (n - 2 - j)) <> ")"
                       in if flagAt paramOwnsSource j
                            then "kdup(" <> raw <> ")"
                            else raw
                    | j <- [0 .. n - 2]
                    ]
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
  case cloNames of
    [] ->
      void $
        unsupported
          "function-global"
          ("zero-arity function global reached curried closure generation for " <> gKey g)
    entryClo : _ -> do
      let accessor =
            T.unlines
              ( [ "static KValue *" <> ident <> "(void) {"
                , "  static _Atomic(KValue *) cache = NULL;"
                , "  KValue *cached = atomic_load_explicit(&cache, memory_order_acquire);"
                , cacheHit
                , "  KValue *fresh = kclo(" <> entryClo <> ", 0);"
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

workerParamOwns :: BackendParam -> Bool
workerParamOwns (BackendParam ic _ (Just (BackendBinder _ _ bo _))) =
  ic == Expl && boDeclQ bo /= Q0 && not (boBorrowed bo)
workerParamOwns _ = False

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

andM :: [Gen Bool] -> Gen Bool
andM = foldr (\m acc -> do b <- m; if b then acc else pure False) (pure True)

orM :: [Gen Bool] -> Gen Bool
orM = foldr (\m acc -> do b <- m; if b then pure True else acc) (pure False)

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
scalarBodyMaySuspend :: Set GName -> BackendTerm -> Bool
scalarBodyMaySuspend susp = go
  where
    -- a call's spine head decides suspendability for this node; the arguments
    -- are then walked too (a suspending op can hide in an argument position).
    -- Only an APPLICATION counts as a call here — a bare 'BVar'/'BGlob' LEAF
    -- (a value read, not an invocation) cannot itself park, so it is never
    -- flagged (else every scalar local read would falsely read as may-suspend).
    headSusp t = case t of
      BApp {} -> case fst (spineOf t) of
        BGlob _ h -> isSuspendingPrim h || h `Set.member` susp
        BVar {} -> True -- opaque higher-order call: may suspend (conservative)
        _ -> False
      _ -> False
    go t =
      headSusp t || case t of
        BIf _ c th el -> go c || go th || go el
        BApp _ f args -> go f || any (go . argTerm) args
        BMatch _ s alts _ -> go s || any (\(BackendAlt _ _ _ gd b) -> maybe False go gd || go b) alts
        BLet _ _ _ _ rhs body -> go rhs || go body
        BLetRec _ _ _ _ rhs body -> go rhs || go body
        BDo {} -> True -- a do-block is an IO action: conservatively may-suspend
        BCtor _ _ as -> any go as
        BSeal _ _ e -> go e
        BForce _ e -> go e
        BThunk _ e -> go e
        BLazy _ e -> go e
        BInject _ _ e -> go e
        BProj _ e _ _ -> go e
        BRecord _ fs -> any (go . snd) fs
        _ -> False

scalarPlan :: GName -> Gen (Maybe ([Bool], [ParamKind], ScalarKind, BackendTerm))
scalarPlan g = do
  bodies <- gets gsBackendBodies
  susp <- gets gsSuspenders
  case Map.lookup g bodies of
    Nothing -> pure Nothing
    Just body -> do
      let params = bbParams body
          n = length params
      -- KBackendIR has already omitted runtime-erased binders. A scalar worker
      -- still requires every remaining runtime parameter to be explicit; an
      -- implicit runtime dictionary or closure-like argument stays boxed.
      if n >= 1 && all ((== Expl) . bpIcit) params
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
              let scalarInner = bbRoot body
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
      if length (filter id mask) == n && length pks == n
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
-- by-ARGUMENT erasure that KBackendIR lowering applies (a 'Q0'/kind-domain proof
-- ARGUMENT is already structurally absent; a proof RESULT was not).
--
-- SOUNDNESS: erases ONLY genuine proofs.  The result-head set is exactly the
-- prelude's propositional-equality and h-prop marker traits — none of which has a
-- runtime-relevant inhabitant (their members are all erased proofs, §14.4).  A def
-- whose result is a real runtime value (an @Int@, a dictionary, an @IO@ action …)
-- has a non-proof head and is left untouched.  FAIL-SAFE like
-- 'Repr.resultIsProofBodyGlobal': an unknown global / a 'gdType' that does not 'force' to
-- a recognisable telescope yields @False@ (compile for real — never erase on doubt).
--
-- The @forall (@0 p : Type). (@_ : IsProp p) -> … -> p@ shape (i.e.
-- 'unsafeAssertProof') has a result that is a bound VARIABLE @p@, not a proof head;
-- it is recognised by the @IsProp p@ / @IsSubsingleton p@ HYPOTHESIS that pins the
-- SAME binder as the result (compared by absolute de Bruijn level).
--
-- Exported so "Kappa.Backend.LLVM" shares the identical verdict (mirrors
-- 'Repr.erasedSpinePositions').
resultIsProofP :: Map GName GlobalDef -> EvalCtx -> GName -> Bool
resultIsProofP = Repr.resultIsProofBodyGlobal

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
scalarEligTail :: GName -> [ParamKind] -> [ParamKind] -> ScalarKind -> BackendTerm -> Gen Bool
scalarEligTail g pks dks ret term = case term of
  BIf _ c t e -> andM [scalarEligCond g pks dks ret c, scalarEligTail g pks dks ret t, scalarEligTail g pks dks ret e]
  -- §let: a let-bound scalar keeps the body scalar-eligible.  The RHS must be a
  -- scalar value (Int/Double); its kind is prepended to @dks@ as a 'PScalar'
  -- slot so the body reads the binder at de Bruijn 0.  A non-scalar RHS makes
  -- the whole body ineligible (→ boxed), never miscompiled.  (CLetRec stays
  -- unhandled: a local fixpoint is not a scalar value.)
  BLet _ _ _ _ rhs body -> do
    mk <- scalarKindOf g pks dks ret rhs
    case mk of
      Just k -> scalarEligTail g pks (PScalar k : dks) ret body
      Nothing -> pure False
  _
    | Just args <- lr1SelfArgsBackend g (length pks) term -> andM (zipWith (selfArgElig g pks dks ret) pks args)
    | otherwise -> scalarHasKind g pks dks ret ret term

-- | A self-call argument is eligible iff: for a scalar param slot, the arg is a
-- value of that scalar kind; for a boxed param slot, the arg is a PASS-THROUGH
-- of a boxed param (a bare @CVar@ of a boxed slot) — the only boxed value the
-- mixed worker can supply without unboxing/rebuilding (R2.4 slice).
selfArgElig :: GName -> [ParamKind] -> [ParamKind] -> ScalarKind -> ParamKind -> BackendTerm -> Gen Bool
selfArgElig g pks dks ret pk arg = case pk of
  PScalar k -> scalarHasKind g pks dks ret k arg
  -- any boxed CVar into a boxed slot is fine: source type-checking already
  -- guarantees the self-call arg's type matches the param, and the runtime
  -- representation of every boxed slot is the uniform @KValue *@.
  PBoxed -> pure $ case arg of
    BVar _ _ j -> varParamKind dks j == Just PBoxed
    _ -> False

-- | Is @term@ a FIXED-OFFSET projection of a BOXED param (@krec_at(boxed,i)@)?
-- Its boxed field value can be coerced to any scalar kind by a tag-checked
-- unbox (R2.4), so it is admissible in any scalar position.  ONLY 'CProjAt'
-- (the P0.4 closed-record fixed-offset form, which codegen lowers to
-- @krec_at@) qualifies; a name-based 'CProj' (open/sealed record, dict member,
-- tuple ≥10) is NOT handled by the coercion codegen, so it must stay
-- ineligible here (→ boxed worker) rather than reach the worker and escalate
-- on a valid program.
isBoxedProj :: [ParamKind] -> BackendTerm -> Bool
isBoxedProj dks term = case term of
  BProj _ (BVar _ _ j) _ (Just _) -> varParamKind dks j == Just PBoxed
  _ -> False

-- | Does the value-position @term@ have scalar kind @k@?  A projection of a
-- boxed param is coercible to any @k@ (a tag-checked unbox at codegen).
scalarHasKind :: GName -> [ParamKind] -> [ParamKind] -> ScalarKind -> ScalarKind -> BackendTerm -> Gen Bool
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
scalarKindOf :: GName -> [ParamKind] -> [ParamKind] -> ScalarKind -> BackendTerm -> Gen (Maybe ScalarKind)
scalarKindOf g pks dks ret term = case term of
  BLit _ (LitInt m)
    | m >= toInteger (minBound :: Int) && m <= toInteger (maxBound :: Int) -> pure (Just KInt64)
    | otherwise -> pure Nothing
  BLit _ (LitDouble _) -> pure (Just KDouble)
  BVar _ _ i -> pure (varParamKind dks i >>= paramSK)
  BLet _ _ _ _ rhs body -> do
    mk <- scalarKindOf g pks dks ret rhs
    case mk of
      Just k -> scalarKindOf g pks (PScalar k : dks) ret body
      Nothing -> pure Nothing
  _ -> case spineOf term of
    (BGlob _ h, sargs) -> do
      let expl = [argTerm a | a <- sargs, argIcit a == Expl]
      mp <- globPrimName h
      case mp of
        Just p | Just (rk, argks) <- arithPrim p, length expl == length argks -> do
          oks <- sequence (zipWith (scalarHasKind g pks dks ret) argks expl)
          pure (if and oks then Just rk else Nothing)
        _
          | Just args <- lr1SelfArgsBackend g (length pks) term -> do
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
scalarEligCond :: GName -> [ParamKind] -> [ParamKind] -> ScalarKind -> BackendTerm -> Gen Bool
scalarEligCond g pks dks ret term = case spineOf term of
  (BGlob _ h, sargs) -> do
    let expl = [argTerm a | a <- sargs, argIcit a == Expl]
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
compileScalarWorker :: GName -> [ParamKind] -> ScalarKind -> BackendTerm -> Gen ()
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
scalarSelfArg :: GName -> [ParamKind] -> ScalarKind -> [Text] -> [ParamKind] -> ParamKind -> BackendTerm -> Gen (Text, Text)
scalarSelfArg g pks ret env dks pk a = case pk of
  PScalar k -> do e <- scalarExpr g pks ret env dks k a; pure (cScalarTy k, e)
  PBoxed -> case a of
    BVar _ _ j -> pure ("KValue *", env !! j)
    _ -> do e <- lr1Unreachable; pure ("KValue *", e)

-- | Compile the body in TAIL position: @if@ branches recurse in tail; a @let@
-- emits its scalar RHS into a fresh typed C local and recurses on the body with
-- that local pushed at de Bruijn 0 (so a let temporary in a hot loop stays in a
-- register — no boxing); a saturated self-call reassigns the params (each temp
-- typed by its slot kind) and @continue@s (an in-place loop — no @KEnv@); any
-- other (leaf, scalar) expr is returned.  @env@/@dks@ are kept in lock-step (the
-- C-local name and its scalar kind at each de-Bruijn slot).
scalarTail :: GName -> [ParamKind] -> ScalarKind -> [Text] -> [Text] -> [ParamKind] -> BackendTerm -> Gen ()
scalarTail g pks ret ps env dks term = case term of
  BIf _ c t e -> do
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
  BLet _ _ _ _ rhs body -> do
    k <- letScalarKind g pks dks ret rhs
    e <- scalarExpr g pks ret env dks k rhs
    t <- freshN "lt_"
    emit (cScalarTy k <> " " <> t <> " = " <> e <> ";")
    scalarTail g pks ret ps (t : env) (PScalar k : dks) body
  _
    | Just args <- lr1SelfArgsBackend g (length pks) term -> do
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
letScalarKind :: GName -> [ParamKind] -> [ParamKind] -> ScalarKind -> BackendTerm -> Gen ScalarKind
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
scalarExpr :: GName -> [ParamKind] -> ScalarKind -> [Text] -> [ParamKind] -> ScalarKind -> BackendTerm -> Gen Text
scalarExpr = scalarExprBody

scalarExprBody :: GName -> [ParamKind] -> ScalarKind -> [Text] -> [ParamKind] -> ScalarKind -> BackendTerm -> Gen Text
scalarExprBody g pks ret env dks dk term
  -- R2.4: a record-field read of a BOXED param yields a boxed value; coerce it
  -- to the demanded scalar kind with a tag-checked unbox that escapes to the
  -- boxed worker on a wrong tag (so a non-Int/Double field never miscompiles).
  | BProj _ (BVar _ _ j) _ (Just off) <- term, isBoxedProj dks term = do
      fb <- freshN "fb_"
      emit ("KValue *" <> fb <> " = krec_at(" <> (env !! j) <> ", " <> T.pack (show off) <> ");")
      t <- freshN "ti_"
      emit (cScalarTy dk <> " " <> t <> " = " <> unboxWorker dk fb <> ";")
      emit "if (*kovf) return 0;"
      pure t
  | otherwise = case term of
      BLit _ (LitInt m) -> pure (cIntLit m)
      BLit _ (LitDouble d) -> pure (cDblLit d)
      BVar _ _ i -> pure (env !! i)
      -- §let in value position: emit the scalar RHS into a fresh typed local and
      -- evaluate the body with it pushed at de Bruijn 0 (the value-position twin
      -- of 'scalarTail's let case — e.g. an inner FMA temporary used by a leaf
      -- return expression).
      BLet _ _ _ _ rhs body -> do
        k <- letScalarKind g pks dks ret rhs
        e <- scalarExpr g pks ret env dks k rhs
        t <- freshN "lt_"
        emit (cScalarTy k <> " " <> t <> " = " <> e <> ";")
        scalarExpr g pks ret (t : env) (PScalar k : dks) dk body
      _ -> case spineOf term of
        (BGlob _ h, sargs) -> do
          let expl = [argTerm a | a <- sargs, argIcit a == Expl]
          mp <- globPrimName h
          case mp of
            Just p | Just (_, argks) <- arithPrim p, length expl == length argks -> scalarArith g pks ret env dks p expl
            _
              | Just args <- lr1SelfArgsBackend g (length pks) term -> do
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
scalarArith :: GName -> [ParamKind] -> ScalarKind -> [Text] -> [ParamKind] -> Text -> [BackendTerm] -> Gen Text
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
scalarCond :: GName -> [ParamKind] -> ScalarKind -> [Text] -> [ParamKind] -> BackendTerm -> Gen Text
scalarCond g pks ret env dks term = case spineOf term of
  (BGlob _ h, sargs) -> do
    let expl = [argTerm a | a <- sargs, argIcit a == Expl]
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
compileScalarCall :: GName -> [ParamKind] -> ScalarKind -> [BackendArg] -> [Int] -> Gen Text
compileScalarCall g pks ret sargs runtimeIdxs = do
  let worker = scalarWorkerName g pks ret
      kw = "kw_" <> mangle (gKey g)
  ownedFlags <- callArgNeedsOwnedForArgs sargs
  aes <-
    mapM
      (\(needOwned, a) -> compileCallArg needOwned (argTerm a))
      (zip ownedFlags sargs)
  ts <- forM aes $ \ae -> do
    t <- freshN "la_"
    emit ("KValue *" <> t <> " = " <> ae <> ";")
    pure t
  let rtTs = [ts !! i | i <- runtimeIdxs, i >= 0, i < length ts]
  ovf <- freshN "kovf_"
  emit ("int " <> ovf <> " = 0;")
  -- scalar slots unbox (tag-checked → escape); boxed slots pass through.
  avs <- forM (zip pks rtTs) $ \(pk, t) -> case pk of
    PScalar sk -> do
      av <- freshN "lu_"
      emit (cScalarTy sk <> " " <> av <> " = " <> unboxScalar sk t ovf <> ";")
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

-- ── KBackendIR lowering ───────────────────────────────────────────────

type BackendArg = (Icit, Maybe Repr.ArgConv, BackendTerm)

argIcit :: BackendArg -> Icit
argIcit (ic, _, _) = ic

argConv :: BackendArg -> Maybe Repr.ArgConv
argConv (_, conv, _) = conv

argTerm :: BackendArg -> BackendTerm
argTerm (_, _, t) = t

-- | Compile a KBackendIR term: emit any needed statements into the current buffer and
-- return a C expression (of type @KValue *@) for its value.
compile :: BackendTerm -> Gen Text
compile term = do
  -- §12.2/§31.2/§14.4: a value whose head is a proof-typed global — a
  -- propositional-equality / h-prop lemma like 'isPropEq' / 'unsafeAssertProof'
  -- / 'cong' (reached via lawful-by-default 'Monoid' law members) — is
  -- RuntimeErased.  Erase the WHOLE maximal spine to the unit placeholder so the
  -- ADMIT primitives '__eqProof'/'__unsafeAssertProof' beneath those lemmas are
  -- never reached at runtime.  A proof is inert (never eliminated/applied), and a
  -- proof ARGUMENT to anything is already structurally absent from KBackendIR;
  -- remaining static placeholders are handled by 'compileErasableArg', so the
  -- spine never feeds a live continuation — erasing the maximal spine cannot
  -- drop a runtime-relevant computation.  See
  -- 'resultIsProofP'.  ('subst'/'pathInd', whose result is a motive-typed VALUE,
  -- are correctly NOT proof-typed and fall through to the real compile path.)
  proofSpine <- case headGlob term of
    Just g -> resultIsProof g
    Nothing -> pure False
  if proofSpine then pure "kunit()" else compileTerm term

compileTerm :: BackendTerm -> Gen Text
compileTerm term = case term of
  BUnit {} -> pure "kunit()"
  BVar _ use i -> do
    -- Perceus RC metadata is attached to this lowered variable occurrence.
    -- Ordinary expression reads apply only the NonLast consuming-use dup policy;
    -- owned call/store/result positions use 'compileOwnedVarUse' instead.
    e <- compileVarRef use i
    rcDupVarUse use i e
  BGlob _ g -> compileGlob g
  BLit _ l -> compileLit l
  BApp {} -> compileApp term
  BLam _ mb _ _ _ body -> compileLam mb body
  BCtor _ layout args -> compileCtorLayout layout args
  BIf {} -> sinkToExpr term
  BMatch {} -> sinkToExpr term
  BLet {} -> sinkToExpr term
  BLetRec {} -> sinkToExpr term
  BRecord _ fs -> compileRecord fs
  BProj _ e f Nothing -> do
    ee <- (compile e)
    pure ("kproj(" <> ee <> ", " <> cStr f <> ")")
  -- P0.4: a projection of a statically-known CLOSED record reads the field at
  -- its fixed lexicographic offset (krec_at, the tuple fast path) instead of a
  -- kproj-by-name strcmp scan.  Open/sealed/dynamic records keep plain BProj.
  BProj _ e _ (Just i) -> do
    ee <- (compile e)
    pure (recAtExpr ee i)
  -- S2.3b: do-kernel bodies are no longer treated as an ownership-erased
  -- island. Mutable-variable reads/writes are ordinary runtime uses, so the RC
  -- validation path must see any lowered variable use in the do body and fail
  -- closed on missing node-local ownership facts.
  BDo _ lbl items -> compileDo lbl items
  -- §13 closed/open variants: injection is a tagged payload.
  BInject _ tag e -> do
    ee <- (compile e)
    tc <- variantTagConst tag
    pure ("kinject(" <> tc <> ", " <> cStr tag <> ", " <> ee <> ")")
  -- §13.2.10: `seal` is pure and non-generative (seal e as S ≡ e), so a
  -- sealed package's runtime value is exactly its underlying record/value.
  BSeal _ _ e -> (compile e)
  -- §19 suspensions: Delay re-evaluates on force; Memo caches.
  BThunk _ e -> (compileSuspension 0 e)
  BLazy _ e -> (compileSuspension 1 e)
  BForce _ t -> do
    te <- (compile t)
    pure ("kforce(" <> te <> ")")

-- | Head global of an application spine, if any.
headGlob :: BackendTerm -> Maybe GName
headGlob = \case
  BApp _ f _ -> headGlob f
  BGlob _ g -> Just g
  BCtor _ layout _ -> Just (bclCtor layout)
  _ -> Nothing

-- | An application spine: head term plus its arguments with icities.
spineOf :: BackendTerm -> (BackendTerm, [BackendArg])
spineOf (BApp _ hd args) =
  let (root, prefix) = spineOf hd
   in (root, prefix ++ args)
spineOf t = (t, [])

backendFuncArity :: BackendTerm -> (Int, BackendTerm)
backendFuncArity = go 0
  where
    go !n (BLam _ _ _ _ _ b) = go (n + 1) b
    go !n t = (n, t)

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
etaCtorApp :: BackendTerm -> Maybe (GName, [BackendTerm])
etaCtorApp term =
  case spineOf term of
    (hd, sargs)
      | (k, body) <- backendFuncArity hd -- count the leading eta lambdas
      , k >= 1
      , k == length sargs
      , BCtor _ layout fieldVars <- body ->
          (,) (bclCtor layout) <$> traverse (pick (map argTerm sargs) k) fieldVars
    _ -> Nothing
  where
    -- a field var must be a bare in-range binder reference; anything else
    -- (a compound subterm, or a free variable at index >= k) bails to the
    -- general lowering rather than misreading the payload.
    pick args k = \case
      BVar _ _ j | j >= 0, j < k -> Just (args !! (k - 1 - j))
      _ -> Nothing

-- | If @term@ is a saturated call to the worker's own global (a tail
-- self-call), return its arguments (with icities); the worker then loops
-- instead of recursing in C.
selfTailArgs :: TailInfo -> BackendTerm -> Maybe [BackendArg]
selfTailArgs ti term = case spineOf term of
  (BGlob _ g, args) | g == tiName ti && length args == tiArity ti -> Just args
  _ -> Nothing

-- | The self-tail-loop path consumes the already-erased KBackendIR spine.
selfTailArgsForLoop :: TailInfo -> BackendTerm -> Gen (Maybe [BackendArg])
selfTailArgsForLoop ti term = pure (selfTailArgs ti term)

-- | Lower a self-tail-call to a loop step: recompute the arguments into
-- fresh temporaries (they may read the current parameters), rebind the
-- worker's parameter variables, and @continue@.
emitTailLoop :: [Text] -> TailInfo -> [BackendArg] -> Gen ()
emitTailLoop cleanup ti args = do
  -- Evaluate every new argument into a temp FIRST (an arg may read a current
  -- parameter via @kvar@), THEN run cleanup, THEN update the parameter cells
  -- in place — so the loop reuses the cells built once in
  -- 'compileFunctionGlobal' rather than allocating a fresh env each iteration
  -- (QW2).  The temps must obey the same owned/borrowed convention as an
  -- ordinary call to the worker: an owned next-iteration parameter may be a
  -- projection out of a let-local whose cleanup runs before the assignment, so
  -- it has to be materialized with kdup before that cleanup can drop the base.
  ownedFlags <- callArgNeedsOwnedForArgs args
  temps <- withTailParamOwnership ti ownedFlags $
    forM (zip [0 ..] args) $ \(i, a) -> do
      mustStabilize <- tailArgNeedsCleanupDup ti cleanup (argTerm a)
      e <-
        if mustStabilize
          then do
            raw <- compileBorrowedCallArg (argTerm a)
            pure ("kdup(" <> raw <> ")")
          else compileCallArg (flagAt ownedFlags i) (argTerm a) -- KBackendIR already erased Q0/type args
      t <- freshN "tc_"
      emit ("KValue *" <> t <> " = " <> e <> ";")
      pure t
  mapM_ emit cleanup
  -- reassign the C parameters (FLAT: read directly; REBUILD: the loop top
  -- rebuilds kw_env from them).  Temps first, so an arg may read a current param.
  forM_ (zip (tiSlots ti) temps) $ \(slot, t) -> emit (slot <> " = " <> t <> ";")
  emit "continue;"

withTailParamOwnership :: TailInfo -> [Bool] -> Gen a -> Gen a
withTailParamOwnership ti ownedFlags act = do
  saved <- gets gsParamOwns
  lvals <- gets gsParamLvals
  let slotOwns = Map.fromList (zip (tiSlots ti) ownedFlags)
      mark lv own = own || Map.findWithDefault False lv slotOwns
      markOwns owns = [mark lv own | (lv, own) <- zip lvals (owns ++ repeat False)] ++ drop (length lvals) owns
  modify' $ \st -> st {gsParamOwns = markOwns (gsParamOwns st)}
  r <- act
  modify' $ \st -> st {gsParamOwns = saved}
  pure r

-- | A self-tail-call is not an ordinary call boundary: its argument temps are
-- evaluated, then the current lexical cleanup runs, then the C parameter slots
-- are reassigned and the loop continues.  A borrowed value read from a
-- soon-to-be-cleaned flat local (especially @local.field@) therefore has to be
-- duplicated before the cleanup can drop the owning aggregate.  Current worker
-- parameters are excluded: they are the loop-carried state itself and are not
-- emitted in the lexical cleanup list.
tailArgNeedsCleanupDup :: TailInfo -> [Text] -> BackendTerm -> Gen Bool
tailArgNeedsCleanupDup _ [] _ = pure False
tailArgNeedsCleanupDup ti _ term = go term
  where
    go = \case
      BVar _ _ i -> flatLocalIsCleanupOwned ti i
      BProj _ base _ _ -> projectionBaseNeedsCleanupDup base
      BSeal _ _ body -> go body
      _ -> pure False

    projectionBaseNeedsCleanupDup = \case
      BVar _ _ i -> flatLocalIsCleanupOwned ti i
      BSeal _ _ body -> projectionBaseNeedsCleanupDup body
      BProj _ base _ _ -> projectionBaseNeedsCleanupDup base
      -- A projection out of any non-flat expression is not a proven borrowed
      -- read from a cleanup-owned local.  Keep the ordinary call lowering
      -- rather than guessing.
      _ -> pure False

flatLocalIsCleanupOwned :: TailInfo -> Int -> Gen Bool
flatLocalIsCleanupOwned ti i = do
  lvals <- gets gsParamLvals
  pure $ case drop i lvals of
    lv : _ -> lv `notElem` tiSlots ti
    [] -> False

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
emitTailApp :: [Text] -> BackendTerm -> Gen ()
emitTailApp cleanup term
  -- P0-A: a saturated eta-expanded constructor in tail position is a final
  -- data value (it cannot bounce or recurse), so build it directly and
  -- return it rather than trampolining through the closure chain.
  | Just (g, args) <- etaCtorApp term = do
      e <- compileCtor g args
      mapM_ emit cleanup
      emit ("return " <> e <> ";")
emitTailApp cleanup term = do
  let (hd, _) = spineOf term
  mp <- case hd of BGlob _ g -> globPrimName g; _ -> pure Nothing
  case (mp, term) of
    (Just _, _) -> do
      e <- compile term -- prim spine: direct helper / entry-point call, computed here, no trampoline
      mapM_ emit cleanup
      emit ("return " <> e <> ";")
    (Nothing, BApp meta f args)
      | Just (prefix, a) <- splitLastExplicit meta f args -> do
      -- Tail-position call-through-value: bounce the final explicit application
      -- so local/mutual recursion stays C-stack bounded. KBackendIR has already
      -- flattened and erased the spine; the prefix rebuild is over runtime args.
      fe <- (compile prefix)
      ae <- (compileCallArg True a)
      mapM_ emit cleanup
      emit ("return kbounce(" <> fe <> ", " <> ae <> ");")
    _ -> do
      e <- compile term
      mapM_ emit cleanup
      emit ("return " <> e <> ";")

splitLastExplicit :: BackendMeta -> BackendTerm -> [BackendArg] -> Maybe (BackendTerm, BackendTerm)
splitLastExplicit meta hd args =
  case breakLastExplicit args of
    Nothing -> Nothing
    Just (prefix, lastArg) ->
      let prefixTerm = case prefix of
            [] -> hd
            _ -> BApp meta hd prefix
       in Just (prefixTerm, argTerm lastArg)
  where
    breakLastExplicit xs =
      case reverse xs of
        a : rs | argIcit a == Expl -> Just (reverse rs, a)
        _ -> Nothing

-- | Is this implicit argument purely type-level (computationally erased),
-- so an erased binder receiving it can be passed an unused placeholder?
-- Type-level forms and references to type/trait globals are erasable;
-- everything else (dictionaries, runtime values) is compiled for real.
isErasableArg :: BackendTerm -> Gen Bool
isErasableArg = \case
  BUnit {} -> pure True
  BApp _ f _ -> isErasableArg f -- the spine head decides (e.g. @(List a))
  BGlob _ g -> isTypeGlob g
  _ -> pure False

-- | Compile a value-position argument, erasing it to the unit placeholder
-- when it is a type-level / staging term (§12.2, §31.2): an explicit
-- @(t : Type)@ / @(s : Syntax _)@ argument or constructor field is a
-- compile-time/static-object position (§11.1.6.1, §11.1.6.2) the spec
-- mandates be erased.  The interpreter stores the evaluated type/quote
-- value but never inspects it at runtime; emitting @kunit()@ keeps the
-- arity (so positional field projection stays aligned) while avoiding the
-- type-level guards in 'compile'.
compileErasableArg :: BackendTerm -> Gen Text
compileErasableArg = compileErasableArgOwned False

compileErasableArgOwned :: Bool -> BackendTerm -> Gen Text
compileErasableArgOwned needOwned a = do
  er <- isErasableArg a
  if er then pure "kunit()" else compileOwnedResult needOwned a

compileBorrowedCallArg :: BackendTerm -> Gen Text
compileBorrowedCallArg = \case
  BVar _ use i -> compileVarRef use i
  BProj _ e f Nothing -> do
    ee <- (compileBorrowedCallArg e)
    pure ("kproj(" <> ee <> ", " <> cStr f <> ")")
  BProj _ e _ (Just i) -> do
    ee <- (compileBorrowedCallArg e)
    pure (recAtExpr ee i)
  BSeal _ _ e -> (compileBorrowedCallArg e)
  t -> compile t

compileOwnedResult :: Bool -> BackendTerm -> Gen Text
compileOwnedResult needOwned = \case
  BVar _ use i
    | needOwned -> compileOwnedVarUse use i
  BProj _ e f Nothing -> do
    ee <- (compile e)
    rcOwnProjectionResult needOwned e ("kproj(" <> ee <> ", " <> cStr f <> ")")
  BProj _ e _ (Just i) -> do
    ee <- (compile e)
    rcOwnProjectionResult needOwned e (recAtExpr ee i)
  BSeal _ _ e -> (compileOwnedResult needOwned e)
  t@BIf {} -> sinkToExprOwned needOwned t
  t@BMatch {} -> sinkToExprOwned needOwned t
  t@BLet {} -> sinkToExprOwned needOwned t
  t@BLetRec {} -> sinkToExprOwned needOwned t
  t -> compile t

compileCallArg :: Bool -> BackendTerm -> Gen Text
compileCallArg needOwned a = do
  er <- isErasableArg a
  if er
    then pure "kunit()"
    else if needOwned then compileOwnedResult True a else compileBorrowedCallArg a

compileDirectCallArg :: Bool -> Bool -> BackendTerm -> Gen Text
compileDirectCallArg needOwned allowReusableTransfer a = do
  er <- isErasableArg a
  if er
    then pure "kunit()"
    else
      if needOwned
        then case a of
          BVar _ use i
            | allowReusableTransfer -> compileOwnedVarUseWithReusable True use i
          BSeal _ _ body -> compileDirectCallArg needOwned allowReusableTransfer body
          _ -> compileOwnedResult True a
        else compileBorrowedCallArg a

compileBoolTest :: BackendTerm -> Gen Text
compileBoolTest = \case
  BSeal _ _ body -> compileBoolTest body
  term -> do
    let (hd, sargs) = spineOf term
        expl = [argTerm a | a <- sargs, argIcit a == Expl]
        intCmp op [a, b] = do
          ae <- compileBorrowedCallArg a
          be <- compileBorrowedCallArg b
          pure ("kint_cmp_fast(" <> ae <> ", " <> be <> ") " <> op <> " 0")
        intCmp _ _ = fallback
        fallback = do
          ce <- compile term
          pure ("kas_bool(" <> ce <> ")")
    case hd of
      BGlob _ g -> do
        mp <- globPrimName g
        case mp of
          Just "eqInt" -> intCmp "==" expl
          Just "ltInt" -> intCmp "<" expl
          Just "leInt" -> intCmp "<=" expl
          _ -> fallback
      _ -> fallback

flagAt :: [Bool] -> Int -> Bool
flagAt flags i = case drop i flags of
  flag : _ -> flag
  [] -> True

callArgNeedsOwnedForArgs :: [BackendArg] -> Gen [Bool]
callArgNeedsOwnedForArgs = go
  where
    go [] = pure []
    go (a : rest)
      | argIcit a /= Expl = (False :) <$> go rest
      | otherwise = do
          erased <- isErasableArg (argTerm a)
          if erased
            then (False :) <$> go rest
            else do
              let needsOwned = case argConv a of
                    Just Repr.ArgBorrowed -> False
                    Just _ -> True
                    Nothing -> True
              (needsOwned :) <$> go rest

-- | A selected dictionary/member projection whose KNOWN dictionary body is just
-- an eta wrapper around a runtime primitive can be lowered as that primitive
-- call.  This is the principled version of the S2.3c/S3.3 "readRef/writeRef via
-- MonadRef evidence" fast path: the decision is keyed by the selected evidence
-- body's Core and the resolved primitive identity ('globPrimName'), never by the
-- projected field spelling alone.  Unknown/local evidence and non-primitive
-- member bodies stay on the ordinary curried 'kapp' path.
compileSelectedProjectedPrimitiveApp :: BackendTerm -> Gen (Maybe Text)
compileSelectedProjectedPrimitiveApp term =
  case spineOf term of
    (BProj _ dict field _, args)
      | Just dictG <- backendEvidenceGlobal dict -> do
      ioDicts <- gets gsIOMonadRefDicts
      if dictG `Set.member` ioDicts
        then do
          mPrim <- selectedIOMonadRefMemberPrimitive dictG field
          case mPrim of
            Just ("__ioNewRef", "kpf_io_newRef", 1) ->
              selectedNewRef [argTerm a | a <- args, argIcit a == Expl]
            Just ("__ioReadRef", "kpf_io_readRef", 1) ->
              selectedReadRef [argTerm a | a <- args, argIcit a == Expl]
            Just ("__ioWriteRef", "kpf_io_writeRef", 2) ->
              selectedWriteRef [argTerm a | a <- args, argIcit a == Expl]
            _ -> pure Nothing
        else pure Nothing
    _ -> pure Nothing
  where
    selectedNewRef [v] =
      Just <$> emitRefPrim "__ioNewRef" "kpf_io_newRef" 1 [(True, v)]
    selectedNewRef _ = pure Nothing

    selectedReadRef [r] =
      Just <$> emitRefPrim "__ioReadRef" "kpf_io_readRef" 1 [(False, r)]
    selectedReadRef _ = pure Nothing

    selectedWriteRef [r, v] =
      Just <$> emitRefPrim "__ioWriteRef" "kpf_io_writeRef" 2 [(False, r), (True, v)]
    selectedWriteRef _ = pure Nothing

    emitRefPrim :: Text -> Text -> Int -> [(Bool, BackendTerm)] -> Gen Text
    emitRefPrim primName cfn arity args = do
      markPrimUsed primName
      aes <-
        forM args $ \(needOwned, a) ->
          compileCallArg needOwned a
      arr <- freshN "na_"
      emit ("KValue *" <> arr <> "[] = {" <> T.intercalate ", " aes <> "};")
      pure ("knative_sat(" <> cfn <> ", " <> T.pack (show arity) <> ", " <> arr <> ", 1)")

selectedIOMonadRefMemberPrimitive :: GName -> Text -> Gen (Maybe (Text, Text, Int))
selectedIOMonadRefMemberPrimitive dictG field =
  case field of
    "newRef" -> member "__ioNewRef" "kpf_io_newRef" 1
    "readRef" -> member "__ioReadRef" "kpf_io_readRef" 1
    "writeRef" -> member "__ioWriteRef" "kpf_io_writeRef" 2
    _ -> pure Nothing
  where
    member primName cfn arity = do
      ok <- dictionaryMemberBodyIsPrimitive dictG field primName arity
      pure $ if ok then Just (primName, cfn, arity) else Nothing

dictionaryMemberBodyIsPrimitive :: GName -> Text -> Text -> Int -> Gen Bool
dictionaryMemberBodyIsPrimitive dictG field primName expectedArity = do
  bodies <- gets gsBodies
  case Map.lookup dictG bodies >>= dictionaryFieldBody field of
    Nothing -> pure False
    Just memberBody -> primitiveEtaBody primName expectedArity memberBody

dictionaryFieldBody :: Text -> Term -> Maybe Term
dictionaryFieldBody field body =
  case stripTermLambdasAndSeals body of
    CRecordV fs -> lookup field fs
    _ -> Nothing

primitiveEtaBody :: Text -> Int -> Term -> Gen Bool
primitiveEtaBody primName expectedArity body = do
  let (hd, args) = spineOfTerm (stripTermLambdasAndSeals body)
      explicitArity = length [() | (Expl, _) <- args]
  headOK <- case hd of
    CGlob g -> (== Just primName) <$> globPrimName g
    _ -> pure False
  pure (headOK && explicitArity == expectedArity)

stripTermLambdasAndSeals :: Term -> Term
stripTermLambdasAndSeals = \case
  CLam _ _ _ body -> stripTermLambdasAndSeals body
  CSealE _ body -> stripTermLambdasAndSeals body
  term -> term

backendEvidenceGlobal :: BackendTerm -> Maybe GName
backendEvidenceGlobal = \case
  BGlob _ g -> Just g
  BSeal _ _ e -> backendEvidenceGlobal e
  BApp _ f args
    | all ((/= Expl) . argIcit) args -> backendEvidenceGlobal f
  _ -> Nothing

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
  -- §11.1.1: TypeLevel is ordinary runtime-capable opaque data. These
  -- helpers share one omega-coefficient/finite-remainder representation across
  -- C and LLVM through the common primitive registry.
  , ("__typeLevelZero", PrimEntry "kpf___typeLevelZero" 0 False)
  , ("__typeLevelOmega", PrimEntry "kpf___typeLevelOmega" 0 False)
  , ("__typeLevelSucc", PrimEntry "kpf___typeLevelSucc" 1 False)
  , ("__typeLevelAdd", PrimEntry "kpf___typeLevelAdd" 2 False)
  , ("__typeLevelMax", PrimEntry "kpf___typeLevelMax" 2 False)
  , ("__typeLevelFromNat", PrimEntry "kpf___typeLevelFromNat" 1 False)
  , ("__compareTypeLevel", PrimEntry "kpf___compareTypeLevel" 2 False)
  , ("__eqTypeLevel", PrimEntry "kpf___eqTypeLevel" 2 False)
  -- MUTABLE-ARRAY-DESIGN §4.1 boxed mutable array.  The forall (e a) is Q0 and
  -- structurally absent from KBackendIR before codegen, so the entry sees only
  -- value args.
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
compileApp :: BackendTerm -> Gen Text
compileApp term
  -- P0-A: a saturated eta-expanded constructor application is a direct
  -- 'kctor', not a curried closure chain (see 'etaCtorApp').
  | Just (g, args) <- etaCtorApp term = compileCtor g args
compileApp term = do
  -- KBackendIR has already discharged Q0/type erasure; the spine here contains
  -- only runtime-kept arguments with their selected calling convention.
  let (hd, sargs) = spineOf term
  compileSelectedProjectedPrimitiveApp term >>= \case
    Just e -> pure e
    Nothing -> case hd of
      BGlob _ g -> do
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
                  explIxH = [(j, argTerm a) | (j, a) <- zip [0 ..] sargs, argIcit a == Expl]
            , length explIxH >= arity
            , arity > 0 -> do
                markHostUsed g
                collectHostCtors rns
                ownedFlags <- callArgNeedsOwnedForArgs sargs
                aes <-
                  mapM
                    (\(j, a) -> compileCallArg (flagAt ownedFlags j) a)
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
compileAppGlob :: GName -> [BackendArg] -> BackendTerm -> Gen Text
compileAppGlob g sargs term = do
      mp <- globPrimName g
      susp <- gets gsSuspenders
      -- Explicit arguments keep their original KBackendIR calling convention.
      -- A @Monad@-instance prim (ioBind/stmBind/…) carries a leading implicit
      -- dictionary/type argument, so 'explIxG' keeps the original spine index for
      -- selecting the already-computed ownership flag.
      ownedFlags <- callArgNeedsOwnedForArgs sargs
      let explIxG = [(j, argTerm a) | (j, a) <- zip [0 ..] sargs, argIcit a == Expl]
          peaIx j t = compileCallArg (flagAt ownedFlags j) t
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
          , backendMayActSuspend susp m -> do
              mc <- peaIx jm m
              kc <- peaIx jk k
              pure ("krt2_bind(" <> mc <> ", " <> kc <> ")")
        Just "ioThen"
          | [(jm, m), (jn, n)] <- explIxG
          , backendMayActSuspend susp m -> do
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
              rawc <- compileOwnedResult (flagAt ownedFlags jraw) raw
              actc <- compileOwnedResult (flagAt ownedFlags jact) act
              pure ("kapp(" <> rawc <> ", " <> actc <> ")")
        Just "poll"
          | null [a | a <- sargs, argIcit a == Expl] -> pure "krt2_poll()"
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
        Just pname | explIx@(_ : _) <- [(j, argTerm a) | (j, a) <- zip [0 ..] sargs, argIcit a == Expl] ->
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
              aes <-
                mapM
                  (\(j, a) -> compileCallArg (flagAt ownedFlags j) a)
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

-- | The worker arity of a function global @g@ after KCore→KBackendIR erasure.
-- This is the actual @kw_g@ ABI arity; kind-domain/q0 parameters are absent
-- from 'bbParams'.
globFuncArity :: GName -> Gen (Maybe Int)
globFuncArity g = do
  bodies <- gets gsBackendBodies
  pure $ case Map.lookup g bodies of
    Just body | let n = length (bbParams body), n >= 1 -> Just n
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
workerMayBounce :: GName -> Int -> BackendTerm -> Gen Bool
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

workerMayBounceUncached :: GName -> Int -> BackendTerm -> Gen Bool
workerMayBounceUncached g n = tailMay
  where
    tailMay term = case term of
      BIf _ _ t e -> orM [tailMay t, tailMay e]
      BMatch _ _ alts _ -> orM [tailMay b | BackendAlt _ _ _ _ b <- alts]
      BLet _ _ _ _ _ body -> tailMay body
      BLetRec _ _ _ _ _ body -> tailMay body
      _
        -- a saturated self-call loops in place; 'lr1SelfArgs' is the shared
        -- recognizer (explicit-arg count == n) — intentionally stricter than
        -- 'selfTailArgs' (full-spine count), which only ever makes this MORE
        -- conservative (keeps a trampoline), never unsound.
        | Just _ <- lr1SelfArgsBackend g n term -> pure False
        | hasExplicitApp term -> do
            let (hd, _) = spineOf term
            prim <- case hd of BGlob _ h -> globPrimName h; _ -> pure Nothing
            pure $ case (prim, coreEtaCtorApp term) of
              (Nothing, Nothing) -> True -- a general tail call → kbounce
              _ -> False -- prim spine / eta-ctor → returns a value
        | otherwise -> pure False -- a leaf value / IO action (no bounce)

lr1SelfArgsBackend :: GName -> Int -> BackendTerm -> Maybe [BackendTerm]
lr1SelfArgsBackend self n term = case spineOf term of
  (BGlob _ g, sargs)
    | g == self
    , expl <- [argTerm a | a <- sargs, argIcit a == Expl]
    , length expl == n ->
        Just expl
  _ -> Nothing

hasExplicitApp :: BackendTerm -> Bool
hasExplicitApp term =
  any ((== Expl) . argIcit) (snd (spineOf term))

coreEtaCtorApp :: BackendTerm -> Maybe (GName, [BackendTerm])
coreEtaCtorApp = etaCtorApp

-- | A saturated (or over-saturated) call to a known function global: call
-- its worker @kw_…@ directly with the leading @n@ arguments instead of
-- building and draining a curried arity-1 closure chain.  The worker's result
-- is driven through 'ktrampoline' ONLY when its body can return a tail-call
-- bounce ('workerMayBounce'); a provably non-bouncing worker is called
-- directly (R3.1).  Any surplus arguments are then applied normally.
-- Type-level/staging arguments are erased (§31.2).
compileDirectCall :: GName -> Int -> [BackendArg] -> Gen Text
compileDirectCall g n sargs = do
  enqueue g
  mplan <- scalarPlan g
  case mplan of
    -- LR1/R2.2: an exactly-saturated call to a scalar-eligible worker takes the
    -- unboxed fast path (with a boxed escape).  Surplus args / partial calls
    -- keep the boxed worker.
    Just (_mask, pks, ret, _)
      | length sargs == length pks
      , let runtimeIdxs = [0 .. length pks - 1] ->
          compileScalarCall g pks ret sargs runtimeIdxs
    _ -> do
      let (callArgs, extra) = splitAt n sargs
          worker = "kw_" <> mangle (gKey g)
      ownedFlags <- callArgNeedsOwnedForArgs sargs
      bodies <- gets gsBackendBodies
      let calleeOwnsFlags =
            case Map.lookup g bodies of
              Just body -> map workerParamOwns (bbParams body)
              Nothing -> replicate n False
      aes <-
        mapM
          (\(j, a) ->
              compileDirectCallArg
                (flagAt ownedFlags j)
                (flagAt calleeOwnsFlags j)
                (argTerm a)
          )
          (zip [0 ..] callArgs)
      mayBounce <- case Map.lookup g bodies of
        Just body -> workerMayBounce g n (bbRoot body)
        Nothing -> pure True -- no recorded body → keep the trampoline
      let call = worker <> "(" <> T.intercalate ", " aes <> ")"
          base = if mayBounce then "ktrampoline(" <> call <> ")" else call
      -- the surplus (over-application) args follow the saturated direct call.
      foldM applyExtra base extra
  where
    applyExtra acc a | argIcit a == Expl = do
      ae <- compileCallArg True (argTerm a)
      pure ("kapp(" <> acc <> ", " <> ae <> ")")
    applyExtra acc a = do
      ae <- compileErasableArg (argTerm a)
      pure ("kappi(" <> acc <> ", " <> ae <> ")")

-- | The general curried application lowering (one 'kapp'/'kappi' per arg).
compileAppDefault :: BackendTerm -> Gen Text
compileAppDefault term =
  case spineOf term of
    (hd, []) -> compile hd
    (hd, args) -> do
      start <- (compile hd)
      foldM step start args
  where
    step acc a
      | argIcit a == Expl = do
          ae <- compileCallArg True (argTerm a)
          pure ("kapp(" <> acc <> ", " <> ae <> ")")
      | otherwise = do
          ae <- compileErasableArg (argTerm a)
          pure ("kappi(" <> acc <> ", " <> ae <> ")")

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
compileLam :: Maybe BackendBinder -> BackendTerm -> Gen Text
compileLam mb body = do
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
  savedReusable <- gets gsParamReusable
  savedTopFlat <- gets gsTopFlatFrame
  bodyEnv <- if flat then pure "cenv" else freshN "lenv_"
  modify' $ \st ->
    st
      { gsParamLvals = if flat then ["arg"] else []
      , gsParamBinders = if flat then [bbBinderId <$> mb] else []
      , gsParamOwns = if flat then [False] else []
      , gsParamReusable = if flat then [False] else []
      , gsTopFlatFrame = False
      }
  -- Perceus RC S2.1: the lambda body sits at 'lamBodyPos' under the CLam node.
  (stmts, ()) <- (captured bodyEnv (consume SinkBounce body))
  modify' $ \st ->
    st
      { gsParamLvals = saved
      , gsParamBinders = savedBinders
      , gsParamOwns = savedOwns
      , gsParamReusable = savedReusable
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

compileCtor :: GName -> [BackendTerm] -> Gen Text
compileCtor g args = do
  -- KBackendIR has already omitted erased constructor fields, so this argv
  -- order is exactly the runtime-kept layout consumed by projections and
  -- pattern bindings.
  argEs <- mapM (compileCallArg True) args
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

compileCtorLayout :: BackendCtorLayout -> [BackendTerm] -> Gen Text
compileCtorLayout layout = compileCtor (bclCtor layout)

compileCtorFromSource :: Text -> BackendCtorLayout -> BackendCtorLayout -> [BackendTerm] -> [Maybe Int] -> Gen Text
compileCtorFromSource source oldLayout newLayout args moveSlots = do
  argEs <-
    forM (zip args moveSlots) $ \(arg, mslot) ->
      case mslot of
        Just {} -> compileBorrowedCallArg arg
        Nothing -> compileCallArg True arg
  tc <- ctorTagConst (bclCtor newLayout)
  arr <-
    case argEs of
      [] -> pure "NULL"
      _ -> do
        a <- freshN "args_"
        emit ("KValue *" <> a <> "[] = {" <> T.intercalate ", " argEs <> "};")
        pure a
  moveArr <-
    if any isJust moveSlots
      then do
        a <- freshN "moves_"
        let slotText = maybe "-1" (T.pack . show)
        emit ("int " <> a <> "[] = {" <> T.intercalate ", " (map slotText moveSlots) <> "};")
        pure a
      else pure "NULL"
  pure
    ( "kdrop_reuse_ctor_alloc("
        <> source
        <> ", "
        <> T.pack (show (bclRuntimeFields oldLayout))
        <> ", "
        <> tc
        <> ", "
        <> cStr (gKey (bclCtor newLayout))
        <> ", "
        <> T.pack (show (length argEs))
        <> ", "
        <> arr
        <> ", "
        <> moveArr
        <> ")"
    )

compileCtorFromTokenSkip :: Text -> BackendCtorLayout -> [BackendTerm] -> [Maybe Int] -> Set Int -> Gen Text
compileCtorFromTokenSkip token newLayout args moveSlots skipSlots = do
  argEs <-
    forM (zip args moveSlots) $ \(arg, mslot) ->
      case mslot of
        Just {} -> compileBorrowedCallArg arg
        Nothing -> compileCallArg True arg
  tc <- ctorTagConst (bclCtor newLayout)
  arr <-
    case argEs of
      [] -> pure "NULL"
      _ -> do
        a <- freshN "args_"
        emit ("KValue *" <> a <> "[] = {" <> T.intercalate ", " argEs <> "};")
        pure a
  let skipList = Set.toAscList skipSlots
  moveArr <-
    if any isJust moveSlots
      then do
        a <- freshN "moves_"
        let slotText = maybe "-1" (T.pack . show)
        emit ("int " <> a <> "[] = {" <> T.intercalate ", " (map slotText moveSlots) <> "};")
        pure a
      else pure "NULL"
  skipArr <-
    case skipList of
      [] -> pure "NULL"
      _ -> do
        a <- freshN "skip_"
        emit ("int " <> a <> "[] = {" <> T.intercalate ", " (map (T.pack . show) skipList) <> "};")
        pure a
  pure
    ( "kreuse_ctor_skip("
        <> token
        <> ", "
        <> tc
        <> ", "
        <> cStr (gKey (bclCtor newLayout))
        <> ", "
        <> T.pack (show (length argEs))
        <> ", "
        <> arr
        <> ", "
        <> moveArr
        <> ", "
        <> skipArr
        <> ", "
        <> T.pack (show (length skipList))
        <> ")"
    )

compileRecord :: [(Text, BackendTerm)] -> Gen Text
compileRecord fs = do
  valEs <-
    mapM
      (\(_, v) -> (compileCallArg True v))
      fs
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
cpsNodeApp :: BackendTerm -> Gen Bool
cpsNodeApp term = do
  let (hd, sargs) = spineOf term
  case hd of
    BGlob _ g -> do
      mp <- globPrimName g
      susp <- gets gsSuspenders
      pure $ case (mp, [argTerm a | a <- sargs, argIcit a == Expl]) of
        (Just "ioBind", [m, _]) -> backendMayActSuspend susp m
        (Just "ioThen", [m, _]) -> backendMayActSuspend susp m
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
consume :: Sink -> BackendTerm -> Gen ()
consume sink term = case term of
  BIf _ c t e -> consumeIf sink c t e
  BMatch _ scrut alts layouts -> consumeMatch sink scrut alts layouts
  BLet _ mb _ _ rhs body -> do
    -- erase a type-level / staging binding (e.g. `let t = Int`) to the unit
    -- placeholder (§31.2) rather than compiling it as a value.
    -- Perceus RC S2.1: rhs at 'letRhsPos', body at 'letBodyPos'.
    rhsOwnsLocal <- (rcTermProducesOwnedHere rhs)
    re <- (compileErasableArgOwned rhsOwnsLocal rhs)
    lvals <- gets gsParamLvals
    if null lvals
      then do
        -- boxed worker: push the binding onto the KEnv chain.
        env <- gets gsEnv
        e2 <- freshN "env_"
        emit ("KEnv *" <> e2 <> " = kpush(" <> re <> ", " <> env <> ");")
        withEnv e2 ((consume sink body))
      else do
        -- R2.3-rest FLAT worker: bind a C local (no KEnv); 'bindFlatLocal'
        -- prepends it as de Bruijn index 0 for exactly the lexical body of this
        -- CLet. This explicit scope is required even inside a 'captured' block:
        -- a nested expression let in an RHS must not shift later outer CVar
        -- lookups (for example an enclosing if condition or else branch).
        -- Perceus RC S2.3 (b.4): the let binder's drop decision is taken from the
        -- lowered binder metadata on this BLet node, against the bound C LOCAL
        -- (R-flat). The local is dropped only when the analysis says
        -- it is droppable AND the initializer is manifestly owned. Structural
        -- projection results become manifestly owned only where the base-use
        -- side table proves a read from an owned aggregate and codegen emitted
        -- the balancing kdup; unproven call/projection shapes stay leak-biased. Emitted at
        -- the body's NORMAL completion — i.e. only when the body sinks into a
        -- continuing result var ('SinkVar'); in a 'SinkTail'/'SinkBounce' body the
        -- value 'return's, so a trailing drop is unreachable.
        drp0 <- rcBinderDroppableHere mb
        let drp = drp0 && rhsOwnsLocal
        savedFlat <- saveFlatLocalScope
        lv <- bindFlatLocal "let_" (bbBinderId <$> mb) rhsOwnsLocal re
        let bodySink = if drp then sinkWithCleanup ["kdrop(" <> lv <> ");"] sink else sink
        (consume bodySink body)
        restoreFlatLocalScope savedFlat
  -- A local recursive let: allocate the binder cell, evaluate the rhs
  -- (a function whose closure captures the cell but does not read it until
  -- applied), then back-patch (docs/NATIVE_BACKEND.md §5).
  BLetRec _ _ _ _ rhs body -> do
    env <- gets gsEnv
    e2 <- freshN "env_"
    emit ("KEnv *" <> e2 <> " = kpush(kunit(), " <> env <> ");")
    -- Perceus RC S2.1: rhs at 'letRhsPos', body at 'letBodyPos'.
    re <- withEnv e2 ((compile rhs))
    emit (e2 <> "->val = " <> re <> ";")
    withEnv e2 ((consume sink body))
  _ -> do
    isCps <- cpsNodeApp term
    let fallback
          | sinkIsTail sink
          , BApp {} <- term
          , isCps =
              compile term >>= sinkResult sink
          | sinkIsTail sink
          , BApp {} <- term
          , sinkHasCleanup sink =
              compile term >>= sinkResult sink
          | sinkIsTail sink
          , BApp {} <- term =
              emitTailApp (sinkCleanupLines sink) term
          | sinkIsBounce sink
          , BApp {} <- term
          , isCps =
              compile term >>= sinkResult sink
          | sinkIsBounce sink
          , BApp {} <- term
          , sinkHasCleanup sink =
              compile term >>= sinkResult sink
          | sinkIsBounce sink
          , BApp {} <- term =
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
sinkToExpr :: BackendTerm -> Gen Text
sinkToExpr = sinkToExprOwned False

sinkToExprOwned :: Bool -> BackendTerm -> Gen Text
sinkToExprOwned needOwned term = do
  r <- freshN "r_"
  emit ("KValue *" <> r <> " = 0;")
  consume (SinkOwnedVar needOwned r) term
  pure r

consumeIf :: Sink -> BackendTerm -> BackendTerm -> BackendTerm -> Gen ()
consumeIf sink c t e = do
  -- Perceus RC S2.1: cond/then/else at 'ifCondPos'/'ifThenPos'/'ifElsePos'.
  ce <- compileBoolTest c
  env <- gets gsEnv
  let scheduledCleanup = sinkCleanupLines sink
  (tStmts, ()) <- (captured env (rcEmitBranchDeadDropsHere scheduledCleanup (backendTermMeta t) >> consume sink t))
  (eStmts, ()) <- (captured env (rcEmitBranchDeadDropsHere scheduledCleanup (backendTermMeta e) >> consume sink e))
  emit ("if (" <> ce <> ") {")
  forM_ tStmts (emit . ("  " <>))
  emit "} else {"
  forM_ eStmts (emit . ("  " <>))
  emit "}"

-- ── Pattern matching ─────────────────────────────────────────────────

consumeMatch :: Sink -> BackendTerm -> [BackendAlt] -> [(GName, BackendCtorLayout)] -> Gen ()
consumeMatch sink scrut alts layouts = do
  -- Perceus RC S2.3a (§a): decide whether the match owns a reference to the
  -- scrutinee CELL that it must discharge with a per-arm @kdrop(sv)@. The
  -- verdict is carried by this KBackendIR node's metadata, so it is fixed once
  -- for every arm without reattaching a path-keyed ownership side table. Inert
  -- under OFF.
  dropCell <- rcScrutDropDecision scrut
  reuseCell <- rcScrutReuseDecision scrut
  se <- (compile scrut)
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
  forM_ alts $ \(BackendAlt _ pat _ _ _) ->
    when (orReordered pat) $
      void $
        unsupported "or-pattern-reordered-binders"
          "an or-pattern alternative that binds the shared names in a different order than the first alternative is not supported by the native backend (use a consistent binder order across alternatives)"
  -- KBackendIR already carries runtime-kept pattern shapes and branch metadata;
  -- top-level or-patterns can be distributed here without reconstructing any
  -- structural ownership path.
  let layoutMap = Map.fromList layouts
  forM_ alts $ \alt ->
    forM_ (expandBackendAltTopOr alt) $ \subAlt ->
      consumeAlt sink sv dropCell reuseCell layoutMap env done subAlt
  emit ("if (!" <> done <> ") krt_fail(\"non-exhaustive match\");")

data CtorReuseCandidate = CtorReuseCandidate
  { crcOldLayout :: !BackendCtorLayout
  , crcNewLayout :: !BackendCtorLayout
  , crcArgs :: ![BackendTerm]
  , crcMoveSlots :: ![Maybe Int]
  , crcSkipSlots :: !(Set Int)
  }

ctorReuseFootprint :: BackendCtorLayout -> Maybe Int
ctorReuseFootprint layout = do
  info <- bclInfo layout
  Repr.clBoxedFootprintBytes info

patCtorReuseLayout :: Map GName BackendCtorLayout -> BackendPat -> Maybe BackendCtorLayout
patCtorReuseLayout layouts = \case
  BPCtor g _ _
    | g == Builtins.prelNatZero || g == Builtins.prelNatSucc ->
        Nothing
  BPCtor g runtimeArity _ -> do
    layout <- Map.lookup g layouts
    guard (runtimeArity == bclRuntimeFields layout)
    pure layout
  -- An as-pattern binds the whole scrutinee cell as a real runtime local.
  -- Token reuse overwrites that exact cell, so until whole-cell alias liveness
  -- is modeled, S5.B must fail closed rather than peeking through BPAs.
  BPAs {} -> Nothing
  _ -> Nothing

directCtorReuseBody :: BackendTerm -> Maybe (BackendCtorLayout, [BackendTerm])
directCtorReuseBody = \case
  BCtor _ layout args -> Just (layout, args)
  BSeal _ _ body -> directCtorReuseBody body
  _ -> Nothing

patDirectCtorFieldVars :: BackendPat -> Maybe (Map Int Int)
patDirectCtorFieldVars = \case
  BPCtor _ _ fields -> do
    slotsInBindingOrder <- fmap concat $
      forM fields $ \(slot, p) ->
        case p of
          BPVar {} -> Just [slot]
          BPWild -> Just []
          _ -> Nothing
    let n = length slotsInBindingOrder
    pure $
      Map.fromList
        [ (n - 1 - bindIx, slot)
        | (bindIx, slot) <- zip [0 ..] slotsInBindingOrder
        ]
  BPAs {} -> Nothing
  _ -> Nothing

shiftCtorFieldVars :: Int -> Map Int Int -> Map Int Int
shiftCtorFieldVars n
  | n <= 0 = id
  | otherwise = Map.mapKeys (+ n)

directMovedArgSlot :: Map Int Int -> BackendTerm -> Maybe Int
directMovedArgSlot slots = \case
  BVar _ (Just (BackendUse _ LastUse True)) i -> Map.lookup i slots
  BSeal _ _ e -> directMovedArgSlot slots e
  _ -> Nothing

ctorReuseMoveSlotsWith :: Map Int Int -> [BackendTerm] -> [Maybe Int]
ctorReuseMoveSlotsWith slots args =
  let raw = map (directMovedArgSlot slots) args
      moved = catMaybes raw
   in if Set.size (Set.fromList moved) == length moved
        then raw
        else replicate (length args) Nothing

data CtorFieldSlotUse = CtorFieldSlotUse
  { cfsAlways :: !(Set Int)
  , cfsMay :: !(Set Int)
  }

slotUseNone :: CtorFieldSlotUse
slotUseNone = CtorFieldSlotUse Set.empty Set.empty

slotUseOne :: Int -> CtorFieldSlotUse
slotUseOne slot = CtorFieldSlotUse (Set.singleton slot) (Set.singleton slot)

slotUseSeq :: [CtorFieldSlotUse] -> CtorFieldSlotUse
slotUseSeq uses =
  CtorFieldSlotUse
    { cfsAlways = Set.unions (map cfsAlways uses)
    , cfsMay = Set.unions (map cfsMay uses)
    }

slotUseChoice :: CtorFieldSlotUse -> CtorFieldSlotUse -> CtorFieldSlotUse
slotUseChoice a b =
  CtorFieldSlotUse
    { cfsAlways = cfsAlways a `Set.intersection` cfsAlways b
    , cfsMay = cfsMay a `Set.union` cfsMay b
    }

slotUseStable :: CtorFieldSlotUse -> Bool
slotUseStable use = cfsAlways use == cfsMay use

consumedCtorFieldSlotUse :: Map Int Int -> BackendTerm -> CtorFieldSlotUse
consumedCtorFieldSlotUse = go
  where
    go fields = \case
      BVar _ (Just (BackendUse _ LastUse True)) i ->
        maybe slotUseNone slotUseOne (Map.lookup i fields)
      BVar {} -> slotUseNone
      BSeal _ _ body -> go fields body
      BApp _ f args -> slotUseSeq (go fields f : map (go fields . argTerm) args)
      BCtor _ _ args -> slotUseSeq (map (go fields) args)
      BMatch _ scrut alts _ ->
        slotUseSeq
          [ go fields scrut
          , slotUseAlts
              [ go (shiftCtorFieldVars (length binders) fields) body
              | BackendAlt _ _ binders _ body <- alts
              ]
          ]
      BRecord _ fields0 -> slotUseSeq (map (go fields . snd) fields0)
      BProj _ base _ _ -> go fields base
      BInject _ _ payload -> go fields payload
      BLet _ _ _ _ rhs body -> slotUseSeq [go fields rhs, go (shiftCtorFieldVars 1 fields) body]
      BLetRec _ _ _ _ _ body -> go (shiftCtorFieldVars 1 fields) body
      BForce _ body -> go fields body
      BIf _ cond th el -> slotUseSeq [go fields cond, slotUseChoice (go fields th) (go fields el)]
      BThunk {} -> slotUseNone
      BLazy {} -> slotUseNone
      BLam {} -> slotUseNone
      BDo {} -> slotUseNone
      BUnit {} -> slotUseNone
      BGlob {} -> slotUseNone
      BLit {} -> slotUseNone

    slotUseAlts [] = slotUseNone
    slotUseAlts (x : xs) = foldl slotUseChoice x xs

consumedCtorFieldSlotsInArgsWith :: Map Int Int -> [BackendTerm] -> Maybe (Set Int)
consumedCtorFieldSlotsInArgsWith fields args =
  let use = slotUseSeq (map (consumedCtorFieldSlotUse fields) args)
   in if slotUseStable use then Just (cfsAlways use) else Nothing

branchDeadCtorFieldSlots :: BackendPat -> [Maybe BackendBinder] -> BackendMeta -> Set Int
branchDeadCtorFieldSlots pat binders meta =
  case patDirectCtorFieldVars pat of
    Nothing -> Set.empty
    Just fields ->
      Set.fromList
        [ slot
        | (dbIx, slot) <- Map.toList fields
        , Just binder <- [binderAt dbIx]
        , branchDropAllowedBinder binder
        , binderId binder `Set.member` branchDrops
        ]
  where
    binderAt i = case drop i binders of
      b : _ -> b
      [] -> Nothing
    binderId (BackendBinder bid _ _ _) = bid
    branchDrops = Set.fromList [bid | BackendBinder bid _ _ _ <- bmBranchDrops meta]

patDupFlagsForReuse :: BackendPat -> CtorReuseCandidate -> [Bool]
patDupFlagsForReuse pat candidate =
  let n = length (patBindings "0" pat)
      movedSlots = Set.fromList (catMaybes (crcMoveSlots candidate))
      directFields = fromMaybe Map.empty (patDirectCtorFieldVars pat)
   in [ maybe True (`Set.notMember` movedSlots) (Map.lookup (n - 1 - j) directFields)
      | j <- [0 .. n - 1]
      ]

sameSizeCtorReuseCandidate :: Map GName BackendCtorLayout -> BackendPat -> [Maybe BackendBinder] -> BackendTerm -> Maybe CtorReuseCandidate
sameSizeCtorReuseCandidate layouts pat binders body = do
  oldLayout <- patCtorReuseLayout layouts pat
  directSameSizeCtorReuseCandidate oldLayout pat binders body

directSameSizeCtorReuseCandidate :: BackendCtorLayout -> BackendPat -> [Maybe BackendBinder] -> BackendTerm -> Maybe CtorReuseCandidate
directSameSizeCtorReuseCandidate oldLayout pat binders body = do
  (newLayout, args) <- directCtorReuseBody body
  sameSizeCtorReuseCandidateFrom oldLayout pat binders newLayout args

sameSizeCtorReuseCandidateFrom :: BackendCtorLayout -> BackendPat -> [Maybe BackendBinder] -> BackendCtorLayout -> [BackendTerm] -> Maybe CtorReuseCandidate
sameSizeCtorReuseCandidateFrom oldLayout pat _binders newLayout args = do
  let fields = fromMaybe Map.empty (patDirectCtorFieldVars pat)
  sameSizeCtorReuseCandidateFromFields fields oldLayout newLayout args

sameSizeCtorReuseCandidateFromFields :: Map Int Int -> BackendCtorLayout -> BackendCtorLayout -> [BackendTerm] -> Maybe CtorReuseCandidate
sameSizeCtorReuseCandidateFromFields fields oldLayout newLayout args = do
  guard (staticallyBoxedCtorLayout oldLayout && staticallyBoxedCtorLayout newLayout)
  oldBytes <- ctorReuseFootprint oldLayout
  newBytes <- ctorReuseFootprint newLayout
  let moveSlots = ctorReuseMoveSlotsWith fields args
      movedSlots = Set.fromList (catMaybes moveSlots)
  consumedSlots <- consumedCtorFieldSlotsInArgsWith fields args
  if oldBytes == newBytes && bclRuntimeFields oldLayout == bclRuntimeFields newLayout
    then
      Just
        CtorReuseCandidate
          { crcOldLayout = oldLayout
          , crcNewLayout = newLayout
          , crcArgs = args
          , crcMoveSlots = moveSlots
          , crcSkipSlots = movedSlots `Set.union` consumedSlots
          }
    else Nothing

staticallyBoxedCtorLayout :: BackendCtorLayout -> Bool
staticallyBoxedCtorLayout layout =
  case bclInfo layout of
    Just info -> Repr.clLayoutClass info == Repr.LayoutBoxed
    Nothing -> False

tokenCtorReuseCandidateFrom :: BackendCtorLayout -> Map Int Int -> BackendCtorLayout -> [BackendTerm] -> Maybe CtorReuseCandidate
tokenCtorReuseCandidateFrom oldLayout fields newLayout args = do
  candidate <- sameSizeCtorReuseCandidateFromFields fields oldLayout newLayout args
  if staticallyBoxedCtorLayout oldLayout && staticallyBoxedCtorLayout newLayout
    then Just candidate
    else Nothing

termHasTokenCtorReuse :: BackendCtorLayout -> BackendPat -> BackendTerm -> Bool
termHasTokenCtorReuse oldLayout pat =
  case patDirectCtorFieldVars pat of
    Nothing -> const False
    Just fields -> go fields
  where
    stable fields term = slotUseStable (consumedCtorFieldSlotUse fields term)
    go fields = \case
      BCtor _ newLayout args -> isJust (tokenCtorReuseCandidateFrom oldLayout fields newLayout args)
      BSeal _ _ body -> go fields body
      BIf _ cond th el ->
        stable fields cond
          && go fields th
          && go fields el
      BLet _ _ _ _ rhs body ->
        stable fields rhs
          && go (shiftCtorFieldVars 1 fields) body
      BLetRec _ _ _ _ _ body ->
        go (shiftCtorFieldVars 1 fields) body
      _ -> False

-- | Whether a pattern contains an or-pattern whose alternatives bind the shared
-- names in a non-canonical order (a non-identity permutation on some
-- alternative) — see 'consumeMatch'.
orReordered :: BackendPat -> Bool
orReordered = \case
  BPOr ps perms -> any (\pm -> pm /= [0 .. length pm - 1]) perms || any orReordered ps
  BPCtor _ _ fields -> any (orReordered . snd) fields
  BPTuple _ fields -> any (orReordered . snd) fields
  BPRecord fs _ -> any (orReordered . snd) fs
  BPInject _ p -> orReordered p
  BPAs _ p -> orReordered p
  _ -> False

-- | §17.2.3: a top-level or-pattern alternative is equivalent to one
-- alternative per branch (matchPat's firstJust, in order), with the same
-- guard and body. Splitting here lets each branch's variable bindings be
-- handled by the ordinary single-pattern path, so or-patterns that bind
-- variables work without decision-tree compilation.
expandBackendAltTopOr :: BackendAlt -> [BackendAlt]
expandBackendAltTopOr (BackendAlt meta pat binders g body) =
  [BackendAlt meta p binders g body | p <- distributePat pat]

-- | §17.2.3: expand a pattern into the list of or-free patterns it denotes,
-- distributing every nested 'CPOr' as the Cartesian product over its
-- positions (left-to-right, matching the interpreter's first-match order).
-- Each or-branch binds the same variables, so all expansions share the
-- alternative's guard and body; the resulting or-free patterns are then
-- handled by the ordinary single-pattern test/binding path.
distributePat :: BackendPat -> [BackendPat]
distributePat = \case
  BPOr ps _ -> concatMap distributePat ps
  BPCtor g runtimeArity fields ->
    let (indices, patterns) = unzip fields
     in [BPCtor g runtimeArity (zip indices qs) | qs <- mapM distributePat patterns]
  BPTuple runtimeArity fields ->
    let (indices, patterns) = unzip fields
     in [BPTuple runtimeArity (zip indices qs) | qs <- mapM distributePat patterns]
  BPRecord fs rest ->
    let (names, pats) = unzip fs
     in [BPRecord (zip names qs) rest | qs <- mapM distributePat pats]
  BPInject t p -> [BPInject t q | q <- distributePat p]
  BPAs n p -> [BPAs n q | q <- distributePat p]
  p -> [p] -- BPWild / BPVar / BPLit / BPInjectRest: no nested or

consumeAlt :: Sink -> Text -> Bool -> Bool -> Map GName BackendCtorLayout -> Text -> Text -> BackendAlt -> Gen ()
consumeAlt sink sv dropCell reuseCell layouts env done (BackendAlt altMeta pat binders mguard body) = do
  emit ("if (!" <> done <> ") {")
  -- pattern test + bindings produced as a nested block
  (blk, ()) <- captured env $ do
    mtest <- patTest sv pat
    case mtest of
      Nothing -> consumeAltBody sink altMeta sv dropCell reuseCell layouts env done pat binders mguard body
      Just test -> do
        emit ("if (" <> test <> ") {")
        consumeAltBody sink altMeta sv dropCell reuseCell layouts env done pat binders mguard body
        emit "}"
  forM_ blk (emit . ("  " <>))
  emit "}"

-- | Bind the pattern variables, evaluate the optional guard, and on a full
-- match consume the body into the sink (and mark @done@; for a 'SinkTail'
-- body the @done@ store is dead — the body has returned/looped — but
-- harmless).
consumeAltBody :: Sink -> BackendMeta -> Text -> Bool -> Bool -> Map GName BackendCtorLayout -> Text -> Text -> BackendPat -> [Maybe BackendBinder] -> Maybe BackendTerm -> BackendTerm -> Gen ()
consumeAltBody sink altMeta sv dropCell reuseCell layouts env done pat binders mguard body = do
  -- patTest already verified the constructor/shape; bindings just project.
  -- Perceus RC S2.3a/S3.2 (§a): the cell-drop fires for THIS arm only when the
  -- match owns the scrutinee cell ('dropCell') or when an S5 reusable flat
  -- worker parameter was transferred to this callee ('reuseCell'). S3.2 routes
  -- that cleanup through the sink, so returning 'SinkTail'/'SinkBounce' arms
  -- emit the drop before the return instead of leaving the scrutinee to Boehm.
  -- The kept-field DUP and the cell @kdrop@ are an ATOMIC PAIR: a field projected
  -- via a borrowing 'kctor_arg'/'kproj' (no incref) is dup'd so it survives the
  -- following @kdrop(sv)@ (which S3.2 lets recursively free fields when the cell
  -- is unique).
  -- So the field-dup must fire IFF the cell-drop does — dupping a kept field on an
  -- arm that then skips the cell-drop would be an UNPAIRED dup (a permanent rc
  -- inflation / leak, never balanced). Guarded arms bind fields before evaluating
  -- the guard, so a failed guard cannot run the success-branch balancing drops;
  -- keep guarded arms conservative until guard-failure cleanup is modeled.
  reuseOn <- gets gsReuseEnabled
  let unguarded = maybe True (const False) mguard
      canOwnForReuse = (dropCell || reuseCell) && unguarded
      reuseOldLayoutAll = if canOwnForReuse then patCtorReuseLayout layouts pat else Nothing
      reuseCandidateAll = if canOwnForReuse then sameSizeCtorReuseCandidate layouts pat binders body else Nothing
  flat <- not . null <$> gets gsParamLvals
  let earlyReuseShape =
        case reuseOldLayoutAll of
          Just oldLayout ->
            flat
              && staticallyBoxedCtorLayout oldLayout
              && termHasTokenCtorReuse oldLayout pat body
          Nothing -> False
      -- A reusable flat parameter is not a generally owned local: it should be
      -- consumed at this seam only when the S5 shape proof would have consumed
      -- it. With KAPPA_PERCEUS_REUSE=0 that consumption falls back to the
      -- ordinary dup/drop path; arbitrary non-reuse matches stay leak-biased.
      dropHere = (dropCell || (reuseCell && (earlyReuseShape || isJust reuseCandidateAll))) && unguarded
      reuseOldLayout = if reuseOn then reuseOldLayoutAll else Nothing
      reuseCandidate = if reuseOn then reuseCandidateAll else Nothing
  case (mguard, reuseOldLayout) of
    (Nothing, Just oldLayout)
      | earlyReuseShape ->
          consumeEarlyReuseAltBody sink altMeta sv env done pat binders body oldLayout dropHere
    _ -> consumeAltBodyLateReuse sink altMeta sv dropHere layouts env done pat binders mguard body reuseCandidate

consumeAltBodyLateReuse :: Sink -> BackendMeta -> Text -> Bool -> Map GName BackendCtorLayout -> Text -> Text -> BackendPat -> [Maybe BackendBinder] -> Maybe BackendTerm -> BackendTerm -> Maybe CtorReuseCandidate -> Gen ()
consumeAltBodyLateReuse sink altMeta sv dropHere _layouts env done pat binders mguard body reuseCandidate = do
  let
      dupFlags =
        case reuseCandidate of
          Just candidate -> patDupFlagsForReuse pat candidate
          Nothing -> replicate (length (patBindings sv pat)) dropHere
  -- Late reuse has not proved that @sv@ is a boxed constructor cell yet: a
  -- source can reach this path because it is packed/immediate, shared, or
  -- otherwise not reusable.  Bind through the generic accessor here; the
  -- early-token branch is the only path allowed to use direct boxed slots.
  env' <- bindPatScrutDupSelectiveWith Nothing dupFlags binders sv env pat
  -- Perceus RC S2.3 (b.4, per-arm): decide the drops for this arm's pattern-slot
  -- binders from lowered arm metadata, against the bound flat C locals (R-flat).
  -- These drops only fire with 'dropHere',
  -- because otherwise pattern locals are raw borrowed projections, not dup-owned
  -- fields. The slot's de Bruijn index @k@ is its
  -- 'gsParamLvals' index right after binding (the LAST patBinding is index 0,
  -- matching the analysis's @depth+n-1-k@ levels). Computed BEFORE descending into
  -- the body so the lookup key is the arm path; emitted through the sink cleanup
  -- after normal body evaluation and before any tail return. Boxed (KEnv) arms
  -- have empty 'gsParamLvals' → no flat local → no drop (left to Boehm).
  patDrops <- if dropHere then rcPatSlotDropLvals binders pat else pure []
  let consumesScrutineeViaReuse = case reuseCandidate of
        Just {} -> True
        Nothing -> False
      altCleanup = map (\lv -> "kdrop(" <> lv <> ");") patDrops <> ["kdrop(" <> sv <> ");" | dropHere && not consumesScrutineeViaReuse]
      bodySink = sinkWithCleanup altCleanup sink
  -- Perceus RC S2.1: under the arm path, the guard sits at 'altGuardPos' and the
  -- body at 'altBodyPos' (the pattern-slot binders are at 'patSlotPos k', looked
  -- up only by the binder pass S2.3, not here).
  case mguard of
    Nothing -> do
      rcEmitBranchDeadDropsHere (sinkCleanupLines bodySink) altMeta
      withEnv env' $
        case reuseCandidate of
          Just candidate ->
            compileCtorFromSource sv (crcOldLayout candidate) (crcNewLayout candidate) (crcArgs candidate) (crcMoveSlots candidate) >>= sinkResult bodySink
          Nothing ->
            consume bodySink body
      emit (done <> " = 1;")
    Just gd -> do
      ge <- withEnv env' (compileBoolTest gd)
      emit ("if (" <> ge <> ") {")
      rcEmitBranchDeadDropsHere (sinkCleanupLines bodySink) altMeta
      withEnv env' ((consume bodySink body))
      emit ("  " <> done <> " = 1;")
      emit "}"

consumeEarlyReuseAltBody :: Sink -> BackendMeta -> Text -> Text -> Text -> BackendPat -> [Maybe BackendBinder] -> BackendTerm -> BackendCtorLayout -> Bool -> Gen ()
consumeEarlyReuseAltBody sink altMeta sv env done pat binders body oldLayout _dropHere = do
  token <- freshN "reuse_"
  emit ("KValue *" <> token <> " = ktry_reuse_ctor(" <> sv <> ", " <> T.pack (show (bclRuntimeFields oldLayout)) <> ");")
  emit ("if (" <> token <> ") {")
  savedUnique <- saveFlatLocalScope
  let n = length (patBindings sv pat)
      dupUnique = replicate n False
      ownUnique = replicate n True
      layoutMap = Map.singleton (bclCtor oldLayout) oldLayout
      altDeadSlots = branchDeadCtorFieldSlots pat binders altMeta
      fieldSlots = fromMaybe Map.empty (patDirectCtorFieldVars pat)
  envUnique <- bindPatScrutOwnershipSelectiveWith (Just layoutMap) dupUnique ownUnique binders sv env pat
  rcEmitBranchDeadDropsHere (sinkCleanupLines sink) altMeta
  withEnv envUnique $
    consumeTokenReuseBody sink token oldLayout pat binders fieldSlots altDeadSlots body
  emit ("  " <> done <> " = 1;")
  restoreFlatLocalScope savedUnique
  emit "} else {"
  savedFallback <- saveFlatLocalScope
  consumeAltBodyLateReuse sink altMeta sv True layoutMap env done pat binders Nothing body (directSameSizeCtorReuseCandidate oldLayout pat binders body)
  restoreFlatLocalScope savedFallback
  emit "}"

consumeTokenReuseBody :: Sink -> Text -> BackendCtorLayout -> BackendPat -> [Maybe BackendBinder] -> Map Int Int -> Set Int -> BackendTerm -> Gen ()
consumeTokenReuseBody sink token oldLayout pat binders fieldSlots pathSkipSlots term =
  case term of
    BCtor _ newLayout args ->
      case tokenCtorReuseCandidateFrom oldLayout fieldSlots newLayout args of
        Just candidate ->
          let candidateSkip = crcSkipSlots candidate `Set.union` pathSkipSlots
           in compileCtorFromTokenSkip token (crcNewLayout candidate) (crcArgs candidate) (crcMoveSlots candidate) candidateSkip >>= sinkResult sink
        Nothing ->
          emit "krt_fail(\"internal: S5 reuse token path lost same-size constructor\");"
    BSeal _ _ body -> consumeTokenReuseBody sink token oldLayout pat binders fieldSlots pathSkipSlots body
    BIf _ c th el -> consumeTokenReuseIf sink token oldLayout pat binders fieldSlots pathSkipSlots c th el
    BLet _ mb _ _ rhs body -> consumeTokenReuseLet sink token oldLayout pat binders fieldSlots pathSkipSlots mb rhs body
    _ -> emit "krt_fail(\"internal: S5 reuse token path reached non-constructor body\");"

consumeTokenReuseIf :: Sink -> Text -> BackendCtorLayout -> BackendPat -> [Maybe BackendBinder] -> Map Int Int -> Set Int -> BackendTerm -> BackendTerm -> BackendTerm -> Gen ()
consumeTokenReuseIf sink token oldLayout pat binders fieldSlots pathSkipSlots c th el = do
  ce <- compileBoolTest c
  env <- gets gsEnv
  let condSkip = cfsAlways (consumedCtorFieldSlotUse fieldSlots c)
      branchSkip term = pathSkipSlots `Set.union` condSkip `Set.union` branchDeadCtorFieldSlots pat binders (backendTermMeta term)
  (tStmts, ()) <-
    captured env $
      rcEmitBranchDeadDropsHere (sinkCleanupLines sink) (backendTermMeta th)
        >> consumeTokenReuseBody sink token oldLayout pat binders fieldSlots (branchSkip th) th
  (eStmts, ()) <-
    captured env $
      rcEmitBranchDeadDropsHere (sinkCleanupLines sink) (backendTermMeta el)
        >> consumeTokenReuseBody sink token oldLayout pat binders fieldSlots (branchSkip el) el
  emit ("if (" <> ce <> ") {")
  forM_ tStmts (emit . ("  " <>))
  emit "} else {"
  forM_ eStmts (emit . ("  " <>))
  emit "}"

consumeTokenReuseLet :: Sink -> Text -> BackendCtorLayout -> BackendPat -> [Maybe BackendBinder] -> Map Int Int -> Set Int -> Maybe BackendBinder -> BackendTerm -> BackendTerm -> Gen ()
consumeTokenReuseLet sink token oldLayout pat binders fieldSlots pathSkipSlots mb rhs body = do
  rhsOwnsLocal <- rcTermProducesOwnedHere rhs
  re <- compileErasableArgOwned rhsOwnsLocal rhs
  let rhsSkip = cfsAlways (consumedCtorFieldSlotUse fieldSlots rhs)
      bodySkip = pathSkipSlots `Set.union` rhsSkip
      bodyFields = shiftCtorFieldVars 1 fieldSlots
  lvals <- gets gsParamLvals
  if null lvals
    then do
      env <- gets gsEnv
      e2 <- freshN "env_"
      emit ("KEnv *" <> e2 <> " = kpush(" <> re <> ", " <> env <> ");")
      withEnv e2 (consumeTokenReuseBody sink token oldLayout pat binders bodyFields bodySkip body)
    else do
      drp0 <- rcBinderDroppableHere mb
      let drp = drp0 && rhsOwnsLocal
      savedFlat <- saveFlatLocalScope
      lv <- bindFlatLocal "let_" (bbBinderId <$> mb) rhsOwnsLocal re
      let bodySink = if drp then sinkWithCleanup ["kdrop(" <> lv <> ");"] sink else sink
      consumeTokenReuseBody bodySink token oldLayout pat binders bodyFields bodySkip body
      restoreFlatLocalScope savedFlat

-- | Perceus RC S2.3: the bound flat C locals to @kdrop@ for the pattern-slot
-- binders of @pat@ that the analysis says are droppable without a consuming
-- 'LastUse' (b.4/S2.3b/S3.2). Non-consuming projection reads are only allowed
-- to coexist with these drops when the result is materialized as owned at the
-- result site.
-- The slot's de Bruijn index @k@ (0 = innermost, the LAST 'patBindings' entry) is
-- its 'gsParamLvals' index in the just-bound arm scope. Returns @[]@ under the OFF
-- baseline, in a boxed arm (empty 'gsParamLvals' — no flat local to drop against),
-- or for any slot the analysis did not mark droppable-with-no-LastUse.
rcPatSlotDropLvals :: [Maybe BackendBinder] -> BackendPat -> Gen [Text]
rcPatSlotDropLvals binders pat = do
  enabled <- gets gsRcEnabled
  lvals <- gets gsParamLvals
  if not enabled || null lvals
    then pure []
    else do
      let n = length (patBindings "0" pat)
      fmap concat $ forM [0 .. n - 1] $ \k -> do
        let mb = case drop k binders of
              b : _ -> b
              [] -> Nothing
        drp <- rcBinderDroppableHere mb
        pure [lvals !! k | drp && k < length lvals]

-- | A C boolean expression that is true iff @pat@ matches the value @v@
-- (a pure expression; no side effects, no bindings).  'Nothing' means the
-- pattern always matches (e.g. a variable or wildcard).
patTest :: Text -> BackendPat -> Gen (Maybe Text)
patTest v = \case
  BPWild -> pure Nothing
  BPVar _ -> pure Nothing
  BPAs _ p -> patTest v p
  BPLit l -> do
    le <- litValue l
    case le of
      Just lv -> pure (Just ("klit_eq(" <> v <> ", " <> lv <> ")"))
      Nothing -> pure (Just "0") -- unsupported literal: never matches (error already recorded)
  BPCtor g _ fields -> do
    if
      | g == Builtins.prelNatZero ->
          pure (Just ("kis_int_any(" <> v <> ") && kint_cmp(" <> v <> ", kint(0)) == 0"))
      | g == Builtins.prelNatSucc -> do
          subs <- forM fields $ \(_, p) ->
            patTest (natPredecessorExpr v) p
          let here = "kis_int_any(" <> v <> ") && kint_cmp(" <> v <> ", kint(0)) > 0"
          pure (Just (conj (here : [t | Just t <- subs])))
      | otherwise -> do
          subs <- forM fields $ \(index, p) ->
            patTest (ctorArgAtExpr v index) p
          -- LR2: dispatch on the numeric ctor identity (int compare) rather than a
          -- kctor_is strcmp.  kctor_tagid returns -1 for a non-ctor scrutinee, so
          -- this preserves the `v->tag == K_CTOR &&` type guard kctor_is carried.
          tc <- ctorTagConst g
          let here = "kctor_tagid(" <> v <> ") == " <> tc
          pure (Just (conj (here : [t | Just t <- subs])))
  BPTuple runtimeArity fields -> do
    subs <- forM fields $ \(index, p) ->
      patTest (recAtExpr v index) p
    let szTest = "krec_size(" <> v <> ") == " <> T.pack (show runtimeArity)
    pure (Just (conj (szTest : [t | Just t <- subs])))
  -- §17.2.5: a record pattern's rest binder always matches; the named
  -- fields determine the test (with or without a rest binder).
  BPRecord pfs _ -> recordTests v pfs
  BPOr ps _ -> do
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
  BPInject tag p -> do
    sub <- patTest ("kvariant_payload(" <> v <> ")") p
    -- LR2: numeric variant dispatch (kvariant_tagid -> -1 for a non-variant).
    tc <- variantTagConst tag
    let here = "kvariant_tagid(" <> v <> ") == " <> tc
    pure (Just (conj (here : [t | Just t <- [sub]])))
  -- §13 residual-row pattern: a variant whose tag is none of the excluded.
  BPInjectRest excl -> do
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
ctorArgAtExpr :: Text -> Int -> Text
ctorArgAtExpr v index =
  "kctor_arg(" <> v <> ", " <> T.pack (show index) <> ")"

natPredecessorExpr :: Text -> Text
natPredecessorExpr v = "kp_subInt(" <> v <> ", kint(1))"

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

bindsNothing :: BackendPat -> Bool
bindsNothing = \case
  BPWild -> True
  BPLit _ -> True
  BPCtor _ _ fields -> all (bindsNothing . snd) fields
  BPTuple _ fields -> all (bindsNothing . snd) fields
  BPOr ps _ -> all bindsNothing ps
  BPInjectRest _ -> True
  _ -> False

-- | The values a pattern binds, as C expressions over the scrutinee
-- expression @sv@, in matchPat's left-to-right binding order (rightmost
-- binder ends up at de Bruijn index 0).
patBindings :: Text -> BackendPat -> [Text]
patBindings = go
  where
    go v = \case
      BPWild -> []
      BPLit _ -> []
      BPVar _ -> [v]
      BPAs _ pattern' -> v : go v pattern'
      BPCtor g _ fields
        | g == Builtins.prelNatZero -> []
        | g == Builtins.prelNatSucc ->
            concat [go (natPredecessorExpr v) pattern' | (_, pattern') <- fields]
        | otherwise ->
            concat [go (ctorArgAtExpr v index) pattern' | (index, pattern') <- fields]
      BPTuple _ fields ->
        concat [go (recAtExpr v index) pattern' | (index, pattern') <- fields]
      BPRecord fields rest ->
        concat [go ("kproj(" <> v <> ", " <> cStr name <> ")") pattern' | (name, pattern') <- fields]
          ++ case rest of
            Just "_" -> []
            Just _ -> [recWithoutExpr v (map fst fields)]
            Nothing -> []
      BPOr _ _ -> []
      BPInject _ pattern' -> go ("kvariant_payload(" <> v <> ")") pattern'
      BPInjectRest _ -> [v]

patBindingsWithLayouts :: Map GName BackendCtorLayout -> Text -> BackendPat -> [Text]
patBindingsWithLayouts layouts sv pat0 = go sv pat0
  where
    go v pat = case pat of
      BPWild -> []
      BPLit _ -> []
      BPVar _ -> [v]
      BPAs _ p -> v : go v p
      BPCtor g runtimeArity fields ->
        if
          | g == Builtins.prelNatZero -> []
          | g == Builtins.prelNatSucc ->
              concat [go (natPredecessorExpr v) p | (_, p) <- fields]
          | otherwise ->
              let arg i =
                    case Map.lookup g layouts of
                      Just layout
                        | staticallyBoxedCtorLayout layout
                        , bclRuntimeFields layout == runtimeArity ->
                            v <> "->as.ctor.args[" <> T.pack (show i) <> "]"
                      _ -> ctorArgAtExpr v i
               in concat [go (arg i) p | (i, p) <- fields]
      BPTuple _ fields -> concat [go (recAtExpr v i) p | (i, p) <- fields]
      BPRecord fs mrest ->
        concat [go ("kproj(" <> v <> ", " <> cStr n <> ")") p | (n, p) <- fs]
          ++ case mrest of
            Just "_" -> []
            Just _ -> [recWithoutExpr v (map fst fs)]
            Nothing -> []
      BPInject _ p -> go ("kvariant_payload(" <> v <> ")") p
      BPInjectRest _ -> [v]
      BPOr {} -> patBindings v pat

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
      CUniverseLift _ _ _ inner -> goT inner
      CSchemaLift _ _ _ _ _ _ _ _ inner -> goT inner
      CArithmeticProof _ -> Set.empty
      CVar {} -> Set.empty
      CLocal {} -> Set.empty
      CGlob g -> Set.singleton g
      CLam _ _ _ b -> goT b
      CPi _ _ _ _ ty b -> goT ty <> goT b
      CApp _ a b -> goT a <> goT b
      CSort {} -> Set.empty
      CLevel {} -> Set.empty
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
      CLetPolyM _ _ _ _ ty rhs body -> goT ty <> goT rhs <> goT body
      CLetRecPolyM _ _ _ _ ty rhs body -> goT ty <> goT rhs <> goT body
      CLetRecGroupM _ definitions body ->
        Set.unions
          (goT body : [goT (clrdType definition) <> goT (clrdRhs definition) | definition <- definitions])
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
spineHeadSuspends susp t = case fst (spineOfTerm t) of
  CGlob g -> isSuspendingPrim g || g `Set.member` susp
  _ -> False

-- | §3.3 higher-order: is this action's spine head a local/parameter (a @CVar@)?
-- Then the action MAY suspend depending on the caller (e.g. @bracketM@'s @use r@,
-- where @use@ is an IO-action parameter).  A combinator over it is CPS-lowered
-- conservatively: the CK-machine drives a sequential local action just fine, and
-- only it can drive a suspending one — whereas the synchronous bridge cannot.
spineHeadIsLocal :: Term -> Bool
spineHeadIsLocal t = case fst (spineOfTerm t) of
  CVar _ -> True
  _ -> False

backendSpineHeadSuspends :: Set GName -> BackendTerm -> Bool
backendSpineHeadSuspends susp t = case fst (spineOf t) of
  BGlob _ g -> isSuspendingPrim g || g `Set.member` susp
  _ -> False

backendSpineHeadIsLocal :: BackendTerm -> Bool
backendSpineHeadIsLocal t = case fst (spineOf t) of
  BVar {} -> True
  _ -> False

backendMayActSuspend :: Set GName -> BackendTerm -> Bool
backendMayActSuspend susp t = backendSpineHeadSuspends susp t || backendSpineHeadIsLocal t

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
-- CK-machine).  This mirrors 'scalarBodyMaySuspend' and the KBackendIR action
-- suspension checks, which
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

backendBlockSuspendsWith :: Bool -> Set GName -> [BackendItem] -> Bool
backendBlockSuspendsWith incLocal susp = any itemSuspends
  where
    s = \case
      BDo _ _ items -> backendBlockSuspendsWith incLocal susp items
      t -> backendSpineHeadSuspends susp t || (incLocal && backendSpineHeadIsLocal t)
    condSuspends (BKCondPure _) = False
    condSuspends (BKCondAction t) = s t
    recur = backendBlockSuspendsWith incLocal susp
    itemSuspends (BKBind _ _ _ _ t _) = s t
    itemSuspends (BKExpr _ t) = s t
    itemSuspends (BKAssign _ _ _ actT _) = s actT
    itemSuspends (BKReturn _ t) = s t
    itemSuspends (BKVarItem _ _ _ actT _) = s actT
    itemSuspends (BKWhile _ _ c b me) = condSuspends c || recur b || maybe False recur me
    itemSuspends (BKFor _ _ _ _ _ b me) = recur b || maybe False recur me
    itemSuspends (BKIf _ alts me) = any (recur . snd) alts || maybe False recur me
    itemSuspends (BKDefer _ _ e) = s e
    itemSuspends BKUsing {} = True
    itemSuspends (BKSubDo _ _ b) = recur b
    itemSuspends _ = False

backendBlockSuspends :: Set GName -> [BackendItem] -> Bool
backendBlockSuspends = backendBlockSuspendsWith False

backendCpsEligible :: Set GName -> [BackendItem] -> Bool
backendCpsEligible susp items =
  all simpleLinear items && (backendBlockSuspendsWith True susp items || any needsRuntimeFinalizers items)
  where
    simpleLinear BKBind {} = True
    simpleLinear BKLet {} = True
    simpleLinear BKExpr {} = True
    simpleLinear BKUsing {} = True
    simpleLinear (BKDefer _ Nothing _) = True
    simpleLinear BKVarItem {} = True
    simpleLinear BKAssign {} = True
    simpleLinear BKReturn {} = True
    simpleLinear (BKBreak _ Nothing) = True
    simpleLinear (BKContinue _ Nothing) = True
    simpleLinear (BKWhile _ Nothing _ body Nothing) = all simpleLinear body
    simpleLinear (BKIf _ alts mels) =
      all (all simpleLinear . snd) alts && maybe True (all simpleLinear) mels
    simpleLinear (BKSubDo _ _ body) = all simpleLinear body
    simpleLinear _ = False
    needsRuntimeFinalizers (BKDefer _ Nothing _) = True
    needsRuntimeFinalizers BKUsing {} = True
    needsRuntimeFinalizers (BKWhile _ Nothing _ body mels) =
      any needsRuntimeFinalizers body || maybe False (any needsRuntimeFinalizers) mels
    needsRuntimeFinalizers (BKIf _ alts mels) =
      any (any needsRuntimeFinalizers . snd) alts || maybe False (any needsRuntimeFinalizers) mels
    needsRuntimeFinalizers (BKSubDo _ _ body) = any needsRuntimeFinalizers body
    needsRuntimeFinalizers _ = False

-- | Lower a CPS-eligible do-block: build its @krt2_*@ action tree, wrapping it
-- in a @krt2_doscope@ when the block carries §18.7 defers (so they run LIFO and
-- masked on every exit, via OP_DOSCOPE/KK_DOSCOPE).  With no defers there is no
-- scope frame — just the bind tree.
compileDoCps :: [BackendItem] -> Gen Text
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
    hasScope (BKDefer _ _ _) = True
    hasScope _ = False
    -- a `return` anywhere in THIS block (recursing into its own loop/if/subdo
    -- bodies, which return from this block, but NOT into a nested do VALUE).
    itemReturns (BKReturn _ _) = True
    itemReturns (BKWhile _ _ _ b mels) = any itemReturns b || maybe False (any itemReturns) mels
    itemReturns (BKIf _ alts mels) = any (any itemReturns . snd) alts || maybe False (any itemReturns) mels
    itemReturns (BKSubDo _ _ b) = any itemReturns b
    itemReturns _ = False

-- | Lower a CPS-eligible do-block to its @krt2_bind@/@krt2_then@ action tree.
-- Each non-tail bind becomes @krt2_bind(action, kclo(kdok_N, env))@ with the
-- continuation emitted as a sibling function; a discarded effect becomes
-- @krt2_then@; the tail action is returned directly (tail position — the
-- CK-machine, not a nested bind, so the spine stays bounded).
cpsItems :: [BackendItem] -> Gen Text
cpsItems = cpsItemsFrom 0

cpsItemsFrom :: Int -> [BackendItem] -> Gen Text
cpsItemsFrom start items = case items of
  [] -> pure "krt2_pure(kunit())"
  item : rest ->
    let ix = start
        next = ix + 1
        restTree = cpsItemsFrom next rest
        itemChild _ act = act
        itemNode act = act
     in case item of
          -- TAIL position: a self-tail-call / mutual-recursion /
          -- call-through-a-value here is DEFERRED behind a continuation so the
          -- recursion is C-stack-bounded (see 'cpsTailAction'); a CPS-node or
          -- primitive head is built directly.
          BKExpr _ t
            | null rest -> itemChild () (cpsTailAction t)
            | otherwise -> seqThen [(), ()] t restTree
          BKBind _ _ _ _ t _
            | null rest -> itemChild () (cpsTailAction t)
          BKBind _ _ BPWild _ t _ -> seqThen [(), ()] t restTree
          BKBind _ _ pat binders t _ -> do
            m <- itemChild () (cpsActionTerm t)
            contFn <- emitCpsCont pat binders next rest
            env <- gets gsEnv
            pure ("krt2_bind(" <> m <> ", kclo(" <> contFn <> ", " <> env <> "))")
          BKLet _ _ BPWild _ t -> itemChild () (compile t) >> restTree
          BKLet _ _ pat binders t -> do
            -- a `let` binds a PURE value. Current-value reads and splices have
            -- already been lifted by the checker into preceding bind/action
            -- items, so there is no hidden monadic read to discover here.
            bindA <- itemChild () (cpsActionOfPure t)
            contFn <- emitCpsCont pat binders next rest
            env <- gets gsEnv
            pure ("krt2_bind(" <> bindA <> ", kclo(" <> contFn <> ", " <> env <> "))")
          -- ── CPS LOOP FAMILY (CPS-DESIGN §4) ──────────────────────────
          -- @var x = init@: bind the MonadRef.newRef action chosen by
          -- elaboration and push the resulting Ref onto the captured env
          -- (de Bruijn 0) for the continuation.
          BKVarItem _ mb _ actT _ -> do
            refA <- itemChild () (cpsActionTerm actT)
            contFn <- emitCpsCont (BPVar "_var") [mb] next rest
            env <- gets gsEnv
            pure ("krt2_bind(" <> refA <> ", kclo(" <> contFn <> ", " <> env <> "))")
          -- @x := rhs@ / @x <- rhs@ (a var assignment): run the
          -- MonadRef.writeRef action selected during elaboration, so CPS and
          -- non-CPS paths use the same evidence.
          BKAssign _ _ _ actT _ -> do
            writeA <- itemChild () (cpsActionTerm actT)
            r <- restTree
            pure ("krt2_then(" <> writeA <> ", " <> r <> ")")
          -- @return v@: exit THIS do-block (OP_RETURN -> RK_RETURN, caught by
          -- the enclosing KK_RETSCOPE — compileDoCps), running every crossed
          -- do-scope's defers en route.
          BKReturn _ t -> do
            rv <- itemChild () (cpsActionOfPure t)
            contFn <- emitCpsReturnCont
            env <- gets gsEnv
            pure ("krt2_bind(" <> rv <> ", kclo(" <> contFn <> ", " <> env <> "))")
          -- @break@ / @continue@ (unlabeled): target the innermost OP_WHILE's KK_LOOP.
          BKBreak _ Nothing -> pure "krt2_break()"
          BKContinue _ Nothing -> pure "krt2_continue()"
          -- @while c { body }@ (unlabeled, no else): OP_WHILE[condIO, bodyIO] -> KK_LOOP.
          BKWhile _ Nothing cond body Nothing -> do
            condA <- itemChild () (cpsCondAction cond)
            bodyA <- itemNode ((cpsItems body))
            r <- restTree
            pure ("krt2_then(krt2_while(" <> condA <> ", " <> bodyA <> "), " <> r <> ")")
          -- a statement-`if` in a CPS block: each branch is a CPS action tree;
          -- the if's normal completion is Unit, so a non-tail if sequences its
          -- Unit result before the rest via krt2_then.
          BKIf _ alts mels -> do
            br <- itemNode (cpsIf alts mels)
            if null rest
              then pure br
              else do
                r <- restTree
                pure ("krt2_then(" <> br <> ", " <> r <> ")")
          -- a transparent nested do-statement (§18.8.3.1): its own bindings
          -- are scoped to the sub-block, but abrupt control propagates outward.
          BKSubDo _ _ body -> do
            sub0 <- itemNode ((cpsItems body))
            let sub = if any directDefers body then "krt2_doscope(" <> sub0 <> ")" else sub0
            if null rest
              then pure sub
              else do
                r <- restTree
                pure ("krt2_then(" <> sub <> ", " <> r <> ")")
          -- §18.7 plain defer: register the action on the enclosing do-scope's
          -- ExitStack (OP_DEFER), then continue.
          BKDefer _ Nothing t -> do
            de <- itemChild () (compileDeferAction t)
            r <- restTree
            pure ("krt2_then(krt2_defer(" <> de <> "), " <> r <> ")")
          -- §19.5/§18.8.3 `using pat <- acquire`: lower through
          -- krt2_acquire_release (rt.c), the same protected-scope machinery
          -- `bracketM` uses.
          BKUsing _ pat binders acquireT releaseT -> do
            acqA <- itemChild () (cpsActionTerm acquireT)
            relV <- itemChild () (compile releaseT)
            useFn <- emitCpsCont pat binders next rest
            env <- gets gsEnv
            pure
              ( "krt2_acquire_release(" <> acqA <> ", " <> relV
                  <> ", kclo(" <> useFn <> ", " <> env <> "))"
              )
          _ ->
            unsupported "do-kernel (CPS)" ("unexpected item in a CPS do-block: " <> T.pack (show item))
  where
    seqThen _ t restTree = do
      m <- cpsActionTerm t
      r <- restTree
      pure ("krt2_then(" <> m <> ", " <> r <> ")")

-- | A §18.7 defer registered DIRECTLY in this item list, not in a nested
-- loop/if/subdo. Such a branch/subdo list needs its own krt2_doscope so the
-- finalizer runs at that list's exit, not at the enclosing do-scope exit.
directDefers :: BackendItem -> Bool
directDefers (BKDefer _ _ _) = True
directDefers _ = False

-- | Emit a CPS continuation function @kdok_N(KEnv *cenv, KValue *karg)@: bind
-- the delivered value @karg@ to @pat@ (extending the captured @cenv@), then
-- build the rest of the block as a tree.
emitCpsCont :: BackendPat -> [Maybe BackendBinder] -> Int -> [BackendItem] -> Gen Text
emitCpsCont pat binders next rest = do
  fnName <- freshFn "kdok_"
  (stmts, tree) <- captured "cenv" $ do
    e2 <- bindPatScrutDup False binders "karg" "cenv" pat
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
cpsActionTerm :: BackendTerm -> Gen Text
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
cpsTailAction :: BackendTerm -> Gen Text
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
deferrableTailCall :: BackendTerm -> Gen Bool
deferrableTailCall t = do
  isCps <- cpsNodeApp t
  if isCps
    then pure False
    else case spineOf t of
      (hd, args)
        | any ((== Expl) . argIcit) args -> case hd of
            BGlob _ g -> do
              mp <- globPrimName g
              pure (mp == Nothing) -- a non-prim global: a (possibly self-) function call → defer
            _ -> pure True -- a call THROUGH a value (closure / local let-rec) → defer
      _ -> pure False -- not an application (a bare value / pure node) → no deferral

-- | Lift a pure value into an IO action. Any current-value reads in source have
-- already become preceding MonadRef.readRef binds during checking.
cpsActionOfPure :: BackendTerm -> Gen Text
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
cpsCondAction :: BackendCond -> Gen Text
cpsCondAction = \case
  BKCondPure t -> cpsActionOfPure t
  BKCondAction t -> cpsActionTerm t

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
cpsIf :: [(BackendTerm, [BackendItem])] -> Maybe [BackendItem] -> Gen Text
cpsIf alts mels = goAlts alts
  where
    goAlts [] = case mels of
      Just els -> (cpsScopedItems els)
      Nothing -> pure "krt2_pure(kunit())" -- no/exhausted else: Unit (§18.8)
    goAlts ((c, body) : more) = do
      condA <- (cpsActionOfPure c)
      thenFn <- emitCpsBranchCont ((cpsScopedItems body))
      elseFn <- emitCpsBranchCont (goAlts more)
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
compileDo :: Maybe Text -> [BackendItem] -> Gen Text
compileDo lbl items = do
  susp <- gets gsSuspenders
  if backendCpsEligible susp items
    then compileDoCps items
    -- A block that reaches a suspending op but is not a CPS-able shape would be
    -- mis-run on the synchronous bridge (fork/await never park) — fail closed
    -- with a clear diagnostic instead, until the relevant CPS stage lands.
    else
      if backendBlockSuspends susp items
        then
          unsupported
            "do-kernel"
            ( "a suspending operation (fork/await/sleepFor/…) appears in a do-block shape the "
                <> "native backend does not yet CPS-lower (a loop, if, using, labeled defer, "
                <> "monadic assignment, or return); see runtime/docs/CPS-DESIGN.md (Stage 2+)"
            )
        else compileDoLegacy lbl items

compileDoLegacy :: Maybe Text -> [BackendItem] -> Gen Text
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
compileDeferAction :: BackendTerm -> Gen Text
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
compileSuspension :: Int -> BackendTerm -> Gen Text
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

currentDeferFrame :: ScopeMode -> Gen (Text, Text)
currentDeferFrame mode = do
  frames <- gets $ \g -> case mode of
    Nested -> gsScopeDefers g
    _ -> gsDefer g
  case frames of
    frame : _ -> pure frame
    [] -> do
      void $
        unsupported
          "defer-frame"
          "internal error: a defer/using item was lowered without an active defer frame"
      pure ("0", "0")

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
countLabeledDefers :: Text -> [BackendItem] -> Int
countLabeledDefers s = sum . map go
  where
    go (BKDefer _ (Just l) _) | l == s = 1
    go (BKWhile _ _ _ body mels) = countLabeledDefers s body + maybe 0 (countLabeledDefers s) mels
    go (BKFor _ _ _ _ _ body mels) = countLabeledDefers s body + maybe 0 (countLabeledDefers s) mels
    go (BKIf _ alts mels) = sum [countLabeledDefers s b | (_, b) <- alts] + maybe 0 (countLabeledDefers s) mels
    -- a transparent nested do-statement routes its @defer@s@ to this scope,
    -- unless it is itself labeled @s@ (then it owns those defers)
    go (BKSubDo _ subL body) | subL == Just s = 0
                          | otherwise = countLabeledDefers s body
    go _ = 0

compileItems :: Maybe Text -> ScopeMode -> [BackendItem] -> Gen ()
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
  let ndirect = length [() | BKDefer _ Nothing _ <- items0] + length [() | BKUsing {} <- items0]
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
    itemChild _ _ act = act

    goAt :: Int -> [BackendItem] -> Gen ()
    goAt _ [] = case mode of
      -- both Tail and a discarded tail if-branch yield Unit here; route
      -- through emitTailReturn so any §18.7 defers are still flushed.
      Tail -> emitTailReturn "kunit()"
      TailEffect -> emitTailReturn "kunit()"
      Nested -> pure ()
    goAt ix (item : rest) = case item of
      BKExpr _ t
        | null rest -> do
            te <- itemChild ix () (compile t)
            case mode of
              -- The do-block's tail IO action is its result: defer it to the
              -- driving krun_io (constant C stack, §27.5A.3), carrying any
              -- §18.7 finalizers along (emitTailIO).
              Tail -> emitTailIO False te
              -- A tail statement-if branch: same, but the result is
              -- discarded (the do-block yields Unit).
              TailEffect -> emitTailIO True te
              Nested -> emitRunIODiscard te
      BKExpr _ t -> do
        te <- itemChild ix () (compile t)
        emitRunIODiscard te >> goAt (ix + 1) rest
      -- A wildcard binding introduces no name: emit the right-hand side
      -- for its effect (a bind runs the IO action; a let just evaluates)
      -- without an unused C variable (keeps the generated C -Wall clean).
      BKLet _ _ BPWild _ t -> do
        te <- itemChild ix () (compile t)
        emit ("(void)(" <> te <> ");")
        goAt (ix + 1) rest
      BKLet _ _ pat binders t -> do
        te <- itemChild ix () (compile t)
        sv <- freshN "let_"
        emit ("KValue *" <> sv <> " = " <> te <> ";")
        bindAndContinue binders sv pat
      BKBind _ _ BPWild _ t _ -> do
        te <- itemChild ix () (compile t)
        emitRunIODiscard te
        goAt (ix + 1) rest
      BKBind _ _ pat binders t _ -> do
        te <- itemChild ix () (compile t)
        sv <- emitRunIOValue "bind_" te
        bindAndContinue binders sv pat
      -- §18 early non-local return: unwind every enclosing Nested scope
      -- (loop/if bodies) running their defers first, then return the value
      -- through emitTailReturn (which flushes the Tail-scope defer frames).
      BKReturn _ t -> do
        te <- itemChild ix () (compile t)
        scopeFrames <- gets gsScopeDefers
        flushFramesInline scopeFrames
        emitTailReturn te
      BKVarItem _ _ _ actT _ -> do
        -- S2.3b: run the checker-selected MonadRef.newRef action on the
        -- C/default fallback path. The former scalar-loop peephole bypassed
        -- MonadRef evidence, so this backend must not reconstruct raw refs until
        -- an evidence-aware C scalarizer proves equivalence.
        te <- itemChild ix () (compile actT)
        ref <- emitRunIOValue "var_" te
        env <- gets gsEnv
        e2 <- freshN "env_"
        emit ("KEnv *" <> e2 <> " = kpush(" <> ref <> ", " <> env <> ");")
        withEnv e2 (goAt (ix + 1) rest)
      BKAssign _ _ _ actT _ -> do
        ae <- itemChild ix () (compile actT)
        emitRunIODiscard ae
        goAt (ix + 1) rest
      -- A statement-`if` that is the do-block's tail: its branches are in
      -- tail position, so a recursive IO call in a branch must defer (not
      -- recurse through krun_io).  Compile the branches in 'TailEffect'
      -- (each path returns); the if's normal completion is discarded so the
      -- do-block yields Unit (§18.8).  A non-tail `if` runs for effect.
      BKIf _ alts mels
        -- A statement-`if` that is the do-block's tail: its branches are in
        -- tail position, so compile them in 'TailEffect' (each path returns,
        -- deferring its tail IO action + finalizers via emitTailIO — stack
        -- safe and defer-correct).  A non-tail `if` runs for effect.
        | null rest && (mode == Tail || mode == TailEffect) -> (compileKIfTail mode alts mels)
        | otherwise -> (compileKIf alts mels) >> goAt (ix + 1) rest
      BKWhile _ ml cond bdy mels -> (compileLoop ml (LoopWhile cond) bdy mels) >> goAt (ix + 1) rest
      BKFor _ ml pat binders src bdy mels -> (compileLoop ml (LoopFor pat binders src) bdy mels) >> goAt (ix + 1) rest
      -- §18.8.3.1: a transparent nested do-statement compiles as a child scope
      -- (its own §18.7 defer frame and label) that inherits the enclosing
      -- loop/return targets.  If it is itself the tail item of a value-returning
      -- do-block, preserve the enclosing tail mode: `else do ...` in a tail
      -- branch must return the sub-do's final value, not discard it as an
      -- effect-only nested statement.
      BKSubDo _ subLbl subItems
        | null rest && (mode == Tail || mode == TailEffect) -> ((compileItems subLbl mode subItems))
        | otherwise -> ((compileItems subLbl Nested subItems)) >> goAt (ix + 1) rest
      BKBreak _ ml -> gotoLoop ml lcBreak
      BKContinue _ ml -> gotoLoop ml lcContinue
      -- §18 let? : bind the pattern and continue, or run the else block
      -- (which replaces the rest of this scope).
      BKLetQ _ pat binders t mElse -> do
        te <- itemChild ix () (compile t)
        sv <- freshN "letq_"
        emit ("KValue *" <> sv <> " = " <> te <> ";")
        env <- gets gsEnv
        let onElse = (compileLetQElse mode sv mElse)
        case distributePat pat of
          -- Common case: a single (or-free) pattern.  Preserves the
          -- irrefutable fast path and the simple if\/else lowering.
          [single] -> do
            mtest <- patTest sv single
            let onMatch = do env' <- bindPatScrutDup False binders sv env single; withEnv env' (goAt (ix + 1) rest)
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
                      env' <- bindPatScrutDup False binders sv env alt
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
      BKDefer _ ml t -> do
        de <- itemChild ix () (compileDeferAction t)
        -- §18.7: `defer@L` registers onto the frame of the enclosing scope
        -- labeled L (which may be outer; its C arr/cnt locals are lexically
        -- in scope here). Plain `defer` uses the current scope's frame.
        mframe <- gets $ \g -> case ml of
          Just l -> lookup l (gsDeferLabels g)
          _ -> Nothing
        frame <- maybe (currentDeferFrame mode) pure mframe
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
      BKUsing _ pat binders acquireT releaseT -> do
        ae <- itemChild ix () (compile acquireT)
        rv <- emitRunIOValue "ures_" ae
        re <- itemChild ix () (compile releaseT)
        frame <- currentDeferFrame mode
        -- §32.2.6: register the release with the runtime abort-exit stack. The
        -- ordinary finalizer captures the returned token; if a scalar/boxed
        -- safe-point abort drains it first, the finalizer becomes a no-op, so a
        -- `using` release runs at most once.
        let releaseExpr = "kapp(" <> re <> ", " <> rv <> ")"
        releaseTok <- freshN "ureltok_"
        emit ("KValue *" <> releaseTok <> " = krt2_abort_exit_push(" <> releaseExpr <> ");")
        registerDefer frame ("krt2_abort_exit_finalizer(" <> releaseTok <> ")")
        bindAndContinue binders rv pat
      where
        -- bind an irrefutable do-pattern (with a runtime check for any
        -- refutable shape) and continue with the rest of this scope (the
        -- `rest` closed over from the enclosing `go (item : rest)` clause)
        bindAndContinue binders sv pat = do
          env <- gets gsEnv
          mtest <- patTest sv pat
          case mtest of
            Just test ->
              emit ("if (!(" <> test <> ")) krt_fail(\"irrefutable binding failed at runtime\");")
            Nothing -> pure ()
          env' <- bindPatScrutDup False binders sv env pat
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

-- | Perceus RC S2.3a (§a): bind a pattern from a concrete scrutinee
-- C-expression, optionally wrapping kept fields in @kdup@.
-- When @dupFields@ is 'True' (the arm both owns the scrutinee cell and will drop
-- it at its 'SinkVar' seam — the 'dropHere' in 'consumeAltBody'), each bound field
-- projection @kctor_arg(sv,…)@ is wrapped in @kdup(…)@ so the surviving field
-- keeps a reference of its own before the following @kdrop(sv)@. S3.1 still only
-- maintains the paired rc invariant; S3.2 will make this the guard against freeing
-- a unique scrutinee cell while a projected field escapes. @kdup@ skips
-- immediates, so an immediate field is a runtime no-op. With @dupFields@
-- 'False' this is exactly the plain pattern-binding path, so every
-- non-match-destructure caller (the
-- do-kernel\/closure-arg\/let-pattern paths) and every returning-arm match is
-- unchanged.
bindPatScrutDup :: Bool -> [Maybe BackendBinder] -> Text -> Text -> BackendPat -> Gen Text
bindPatScrutDup dupFields binders sv env pat =
  bindPatScrutDupSelective (replicate (length (patBindings sv pat)) dupFields) binders sv env pat

bindPatScrutDupSelective :: [Bool] -> [Maybe BackendBinder] -> Text -> Text -> BackendPat -> Gen Text
bindPatScrutDupSelective =
  bindPatScrutDupSelectiveWith Nothing

bindPatScrutDupSelectiveWith :: Maybe (Map GName BackendCtorLayout) -> [Bool] -> [Maybe BackendBinder] -> Text -> Text -> BackendPat -> Gen Text
bindPatScrutDupSelectiveWith mlayouts dupFlags =
  bindPatScrutOwnershipSelectiveWith mlayouts dupFlags dupFlags

bindPatScrutOwnershipSelectiveWith :: Maybe (Map GName BackendCtorLayout) -> [Bool] -> [Bool] -> [Maybe BackendBinder] -> Text -> Text -> BackendPat -> Gen Text
bindPatScrutOwnershipSelectiveWith mlayouts dupFlags ownFlags binders sv env pat = do
  lvals <- gets gsParamLvals
  rcEnabled <- gets gsRcEnabled
  let wrap j valExpr = if dupAt j then "kdup(" <> valExpr <> ")" else valExpr
      vals = case mlayouts of
        Just layouts | rcEnabled -> patBindingsWithLayouts layouts sv pat
        Nothing -> patBindings sv pat
        _ -> patBindings sv pat
  if null lvals
    then foldM push env (zip [0 ..] vals) -- boxed: kpush each onto the KEnv
    else do
      -- R2.3-rest FLAT worker: bind each pattern variable to a C local via
      -- 'bindFlatLocal' (the LAST binding becomes de Bruijn index 0, matching
      -- the kpush order); the scope is restored by the enclosing 'captured'.
      let n = length vals
      forM_ (zip [0 ..] vals) $ \(j, valExpr) -> do
        let mb = case drop (n - 1 - j) binders of
              b : _ -> b
              [] -> Nothing
        void (bindFlatLocal "pat_" (bbBinderId <$> mb) (ownAt j) (wrap j valExpr))
      gets gsEnv -- unchanged (flat reads via gsParamLvals, not the KEnv)
  where
    push e (j, valExpr) = do
      n <- freshN "env_"
      let v = if dupAt j then "kdup(" <> valExpr <> ")" else valExpr
      emit ("KEnv *" <> n <> " = kpush(" <> v <> ", " <> e <> ");")
      pure n
    dupAt j = case drop j dupFlags of
      flag : _ -> flag
      [] -> True
    ownAt j = case drop j ownFlags of
      flag : _ -> flag
      [] -> dupAt j

-- | R2.3-rest: bind @valExpr@ to a fresh C local in a flat worker and prepend
-- it to 'gsParamLvals' as de Bruijn index 0 (params and earlier binders shift
-- up); the enclosing 'captured' block restores the scope.  Returns the C name.
bindFlatLocal :: Text -> Maybe BackendBinderId -> Bool -> Text -> Gen Text
bindFlatLocal prefix mbid ownsRef valExpr = do
  v <- freshN prefix
  emit ("KValue *" <> v <> " = " <> valExpr <> ";")
  modify' $ \st ->
    st
      { gsParamLvals = v : gsParamLvals st
      , gsParamBinders = mbid : gsParamBinders st
      , gsParamOwns = ownsRef : gsParamOwns st
      , gsParamReusable = ownsRef : gsParamReusable st
      }
  pure v

compileKIf :: [(BackendTerm, [BackendItem])] -> Maybe [BackendItem] -> Gen ()
compileKIf alts mels = go alts
  where
    go [] = case mels of
      Just els -> (emitBlock els)
      Nothing -> pure ()
    go ((c, body) : more) = do
      ce <- compileBoolTest c
      emit ("if (" <> ce <> ") {")
      env <- gets gsEnv
      (blk, ()) <- (captured env (compileItems Nothing Nested body))
      forM_ blk (emit . ("  " <>))
      emit "}"
      unless (null more && mels == Nothing) $ do
        emit "else {"
        go more
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
compileKIfTail :: ScopeMode -> [(BackendTerm, [BackendItem])] -> Maybe [BackendItem] -> Gen ()
compileKIfTail tailMode alts mels = goAlts alts
  where
    goAlts [] = case mels of
      Just els -> (emitBranch els)
      Nothing -> emitTailReturn "kunit()" -- no/exhausted else: yield Unit, flush defers
    goAlts ((c, body) : more) = do
      ce <- compileBoolTest c
      emit ("if (" <> ce <> ") {")
      (emitBranch body)
      emit "} else {"
      goAlts more
      emit "}"
    emitBranch items = do
      env <- gets gsEnv
      (blk, ()) <- captured env (compileItems Nothing tailMode items)
      forM_ blk (emit . ("  " <>))

data LoopKind = LoopWhile !BackendCond | LoopFor !BackendPat ![Maybe BackendBinder] !BackendTerm

compileLoopCond :: BackendCond -> Gen Text
compileLoopCond = \case
  BKCondPure t -> compile t
  BKCondAction t -> compile t >>= emitRunIOValue "cond_"

-- | Compile a @while@\/@for@ loop using explicit @goto@ labels, so §18.2.5
-- labelled @break@\/@continue@ targeting an outer loop work uniformly and
-- the §18.8 @else@ (run only on normal completion, not after a @break@) is
-- placed past the body and before the break label.
compileLoop :: Maybe Text -> LoopKind -> [BackendItem] -> Maybe [BackendItem] -> Gen ()
compileLoop mlabel kind body mels = do
  env <- gets gsEnv
  n <- freshN "lp_"
  let contL = "kcont_" <> n -- continue target (re-test)
      advL = "kadv_" <> n -- for-loop advance (continue lands here)
      normL = "knorm_" <> n -- normal completion (run else)
      endL = "kend_" <> n -- break target (skip else)
      -- continue re-tests; for a `for` it must advance the cursor first.
      contTarget = case kind of LoopWhile _ -> contL; LoopFor {} -> advL
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
      (condBlk, ce) <- (captured env (compileLoopCond cond))
      (bb, ()) <- (withLoop ctx (captured env (compileItems mlabel Nested body)))
      emit (contL <> ": ;")
      forM_ condBlk (emit . ("  " <>))
      emit ("if (!kas_bool(" <> ce <> ")) goto " <> normL <> ";")
      forM_ bb emit
      emitSafepointAbort spc
      emit ("goto " <> contL <> ";")
      pure bb
    LoopFor pat binders src -> do
      se <- (compile src)
      it <- freshN "it_"
      emit ("KValue *" <> it <> " = " <> se <> ";")
      (bb, ()) <-  withLoop ctx $ captured env $ case pat of
        -- a wildcard element binds nothing: skip the unused element var
        BPWild -> compileItems mlabel Nested body
        _ -> do
          elemV <- freshN "elem_"
          emit ("KValue *" <> elemV <> " = kctor_arg(" <> it <> ", 0);")
          e' <- bindPatScrutDup False binders elemV env pat
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
      (eb, ()) <- (captured env (compileItems Nothing Nested els))
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
compileLetQElse :: ScopeMode -> Text -> Maybe (BackendPat, [Maybe BackendBinder], BackendTerm) -> Gen ()
compileLetQElse mode sv mElse = case mElse of
  Nothing -> emit "krt_fail(\"let? pattern failed and no Alternative is available\");"
  Just (rp, binders, fe) -> do
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
    env' <- bindPatScrutDup False binders sv env rp
    fee <- withEnv env' ((compile fe))
    -- the else action replaces the rest of the scope, so it is the tail:
    -- defer it (stack-safe, §27.5A.3, with finalizers) the same way a
    -- trailing KExpr is.
    case mode of
      Tail -> emitTailIO False fee
      TailEffect -> emitTailIO True fee
      Nested -> emitRunIODiscard fee
