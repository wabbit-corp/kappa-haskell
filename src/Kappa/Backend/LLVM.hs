{-# LANGUAGE OverloadedRecordDot #-}

-- | Native backend (LLVM textual IR): lower S5.A
-- 'Kappa.Backend.IR.BackendTerm' roots to a complete @.ll@ translation unit
-- that links against the same @kappart2@ runtime the C backend uses
-- ("Kappa.Backend.C"). Residual KCore reads in this module are scalar/planning
-- inputs, not value-emission or ownership side tables.
--
-- Phase 1 contract (milestones M0–M5): UNIFORM-BOXED PARITY with the C
-- backend.  The value model, the runtime, the @KEnv@/@kpush@/@kvar@
-- discipline, and the @knative_sat@/@kapp@/@kctor@ ABI are identical to C;
-- only the emitted text differs (LLVM IR instead of C statements).  The
-- output must match the C backend's observable behaviour bit-for-bit.
--
-- Landed so far: M0 (hello-world: a saturated effectful primitive over string
-- literals), M1 (Int literals + the pure first-order @kp_*@ prims), M2
-- (cross-global arity-0 CAF references), and Milestone B — LOCAL BINDINGS
-- ('CVar'/'CLet' via the uniform @kpush@/@kvar@ environment) plus a widened
-- pure-direct prim table (the String and Integer-bitwise @kp_*@ helpers).  The
-- structural scaffolding (the work queue, the memoised accessor shape, the
-- @\@main@ entry point, the assembled module) mirrors 'Kappa.Backend.C'
-- one-to-one so later milestones (constructors, closures, do) slot in by adding
-- 'compile' arms, not by reworking the frame.
--
-- The single structural difference from C: C nests expressions in one
-- string; LLVM is three-address, so 'compile' returns an SSA OPERAND
-- (a @%reg@, an @\@global@, or @ptr null@) and materialises every
-- sub-result as an instruction first.
module Kappa.Backend.LLVM
  ( generateLL
  , hostFfiSidecar
  ) where

import Data.Char (isAsciiLower, isAsciiUpper, isDigit, ord)
import Data.List (sort)
import Data.Maybe (isJust, mapMaybe)
import Data.Word (Word8)
import GHC.Float (castDoubleToWord64)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Control.Monad (forM, forM_, foldM, msum, mplus, replicateM, unless, when, void)
import Control.Monad.State.Strict
import Kappa.Backend.C (BackendError (..), PrimEntry (..), backendIRValidationErrors, backendUnsupported, generateC, multishotLegality, primDirect, primEntries, resultIsProofP, suspenderGlobalsWith)
import Kappa.Backend.IR
  ( BackendAlt (..)
  , BackendBody (..)
  , BackendCond (..)
  , BackendCtorLayout (..)
  , BackendItem (..)
  , BackendMeta (..)
  , BackendParam (..)
  , BackendPat (..)
  , BackendTerm (..)
  , KBackendIR (..)
  , lowerKBackendIR
  )
import Kappa.Backend.NativeFfi (ResolvedNativeSymbol (..), externPrototype, rnsCollectCtors, wrapperCName, wrapperDefinition)
import qualified Kappa.Backend.Repr as Repr
import qualified Kappa.Builtins as Builtins
import Kappa.Build.Types (FfiClass (..))
import Kappa.Check (CheckState (..))
import Kappa.Core
import Kappa.Eval (EvalCtx (..), GlobalDef (..), Globals (..), quote)
import Kappa.Source (ModuleName (..), Span, noSpan)
import Numeric (showHex)

-- ── Code-generation monad ────────────────────────────────────────────
--
-- A minimal port of 'Kappa.Backend.C.GenState' (the M0 subset).  The
-- worklist + metadata fields keep their C roles verbatim; the C
-- statement/expression fields are replaced by LLVM-IR-text + SSA-value
-- fields (the §1.2 mapping in the foundation plan).

data GenState = GenState
  { gsFresh :: !Int -- ^ fresh counter; feeds SSA @%vN@ registers AND block labels
  , gsInsns :: ![Text] -- ^ instructions of the CURRENT basic block, reversed
  , gsEnv :: !Text -- ^ SSA VALUE operand for the current @KEnv*@ (no @ptr@ type prefix; @"null"@ at top level, a @%vN@ once a binder pushes a slot via @kpush@). Use sites supply the @ptr@ type (e.g. @kvar(ptr <env>, …)@).
  , gsTop :: ![Text] -- ^ completed top-level @define@s, reversed
  , gsDecls :: !(Set Text) -- ^ runtime @declare@ lines (Set-dedup: one fn referenced many times)
  , gsStrs :: ![(Text, Text, Int)] -- ^ string pool: (global name, escaped IR bytes, byte length)
  , gsCStrs :: ![(Text, Text, Int)] -- ^ NUL-terminated C-string pool for @kbigint_str@: (global name, escaped IR bytes incl. trailing NUL, total length)
  , gsGlobalsExtra :: ![Text] -- ^ extra module-level globals (e.g. each accessor's @.cache@)
  , gsEmitted :: !(Set GName) -- ^ globals already emitted or enqueued
  , gsQueue :: ![GName] -- ^ globals still to emit
  , gsErrs :: ![BackendError] -- ^ unsupported-construct findings
  , gsCur :: !GName -- ^ definition currently being compiled (for diagnostics)
  , gsGlobals :: !(Map GName GlobalDef)
  , gsEvalCtx :: !EvalCtx -- ^ a non-runtime EvalCtx (from the CheckState), used only to 'quote' a global's 'gdType' to a Term in 'isTypeGlob' (the sort-kind erasure fallback — mirrors C's 'gsEvalCtx').
  , gsBodies :: !(Map GName Term)
  , gsBackendBodies :: !(Map GName BackendBody)
  , gsSuspenders :: !(Set GName) -- ^ Shared §3.3 transitive suspender closure. A do-block that reaches one of these heads must lower to a CK-machine action tree; a non-suspending block can stay as a suspended legacy kio thunk so its pure lets are not evaluated at action construction time.
  , gsPrims :: !(Set Text) -- ^ primitive names the linked runtime implements
  , gsDeclSites :: !(Map GName Span)
  , gsCtorTags :: !(Map Text Int) -- ^ Milestone C: USER-constructor gKey -> numeric tag id (@KCT_USER_BASE+i@). Precomputed once ('hostCtorTags') so 'compileCtor'/'compileMatch' can emit a literal @i32@ immediate (LLVM has no symbolic enum constant like the C backend's @KT_*@). Builtin ctors are NOT here — they use the fixed 'builtinCtorTagId'. Milestone L: includes the @std.ffi@ ctors host marshalling builds, so the @.ll@ and the wrapper sidecar agree on ids.
  , gsBlock :: !Text -- ^ Milestone C: label of the basic block currently being filled. A @phi@ at a control-flow join needs the PREDECESSOR block of each incoming value, which — for a branch that itself emitted control flow (a nested match/if) — is NOT the branch-entry label but whatever block was active when the branch finished. 'compileIf'/'compileMatch' read this after compiling each arm to spell the phi's incoming labels correctly. Updated by 'startBlock'.
  , gsCtorSet :: !(Set GName) -- ^ Milestone D: every declared constructor's gname. An IMPLICIT application whose head is a constructor erases its implicit arg (§31.2); 'isErasedHead' consults this (mirrors C's 'gsCtors' membership test).
  , gsDataSet :: !(Set GName) -- ^ Milestone D: declared data-type / trait gnames — a reference to one in argument position is computationally erased ('isTypeGlob'); mirrors C's @gsDatas@ ∪ @gsTraits@.
  , gsHostSyms :: !(Map GName ResolvedNativeSymbol) -- ^ Milestone L (§27.1.1/§36.28): each provided @host.native.*@ member ↦ its resolved native symbol (C symbol + ABI signature), built per build from the manifest's native bindings. A reference to such a member is lowered like a PRIM over the codegen-emitted C-wrapper symbol ('wrapperCName') — a saturated reference to a @knative_sat@ over the wrapper, a curried/bare reference to a @knative@ closure — and the wrapper is compiled+linked from a sidecar @.c@ the Driver emits ('hostFfiSidecar'). Mirrors C's @gsHostSyms@; recognised at the REFERENCE so a host member is NEVER enqueued as a no-core-body CAF.
  , gsScalarHelpers :: !(Set Text) -- ^ names of scalar-worker helper @define@s already emitted (the @.ll@-local arg-unbox @kunbox_i64_ll@/@kunbox_dbl_ll@), so each is emitted exactly once.
  , gsScalarLetSlots :: ![Text] -- ^ entry-block scratch slots reserved for scalar-worker 'CLet' binders. Popped during scalar worker emission so tail loops store into fixed slots instead of executing 'alloca' on every iteration.
  , gsRcRuntimeEnabled :: !Bool -- ^ Whether this LLVM binary may run runtime RC counting/freeing effects. LLVM still delegates RC validation to C when requested, but until LLVM emits ownership maintenance itself, generated LLVM binaries keep the runtime @kdup@/@kdrop@ gate off. S4 publish marking still emits because shared bits are synchronization metadata.
  }

type Gen = State GenState

type BackendArg = (Icit, Maybe Repr.ArgConv, BackendTerm)

argIcit :: BackendArg -> Icit
argIcit (ic, _, _) = ic

argTerm :: BackendArg -> BackendTerm
argTerm (_, _, t) = t

-- | A fresh SSA register name (@%vN@) — every non-trivial LLVM value must be
-- named; this is the LLVM analogue of C's nested r-values.
freshReg :: Gen Text
freshReg = do
  n <- gets gsFresh
  modify' $ \g -> g {gsFresh = n + 1}
  pure ("%v" <> T.pack (show n))

-- | A fresh basic-block label (no leading @%@; used bare after @label:@ and as
-- @label %name@ in branch/phi operands).  Shares 'gsFresh' with 'freshReg' so a
-- label and a register never collide.
freshLabel :: Text -> Gen Text
freshLabel base = do
  n <- gets gsFresh
  modify' $ \g -> g {gsFresh = n + 1}
  pure (base <> T.pack (show n))

-- | Prepend an IR instruction to the current basic block.
emit :: Text -> Gen ()
emit s = modify' $ \g -> g {gsInsns = s : gsInsns g}

-- | Open a new basic block: emit its @label:@ header and record it as the
-- current block ('gsBlock') so a later @phi@ names the right predecessor.  The
-- caller is responsible for having terminated the previous block (every LLVM
-- block needs exactly one terminator) before calling this.
startBlock :: Text -> Gen ()
startBlock label = do
  emit (label <> ":")
  modify' $ \g -> g {gsBlock = label}

-- | Add a runtime @declare@ line (idempotent — a Set).
declRuntime :: Text -> Gen ()
declRuntime d = modify' $ \g -> g {gsDecls = Set.insert d (gsDecls g)}

-- | Run a sub-action with a fresh (empty) instruction buffer and the given
-- current-env operand, returning the produced instructions IN ORDER, the label
-- of the block ACTIVE when the action finished (which differs from the @build@
-- entry when the action emitted its own control flow — the accessor's trailing
-- @store@/@br@/@phi@ must reference this final block, not @build@), and the
-- action's result; restores the caller's buffer, env, and block afterwards.
-- The LLVM analogue of C's 'captured'.
captured :: Text -> Gen a -> Gen ([Text], Text, a)
captured env act = do
  saved <- gets gsInsns
  savedEnv <- gets gsEnv
  savedBlock <- gets gsBlock
  savedScalarLetSlots <- gets gsScalarLetSlots
  -- The captured region is spliced verbatim under the accessor's @build:@
  -- label, so that is the block active when @act@ starts emitting; a control
  -- form ('compileMatch'/'compileIf') reads/updates 'gsBlock' from here.
  modify' $ \g -> g {gsInsns = [], gsEnv = env, gsBlock = "build"}
  r <- act
  produced <- gets gsInsns
  endBlock <- gets gsBlock
  modify' $ \g -> g {gsInsns = saved, gsEnv = savedEnv, gsBlock = savedBlock, gsScalarLetSlots = savedScalarLetSlots}
  pure (reverse produced, endBlock, r)

-- | Record an unsupported-construct finding and return a placeholder operand
-- so error collection can continue.
unsupported :: Text -> Text -> Gen Text
unsupported construct detail = do
  g <- gets gsCur
  sites <- gets gsDeclSites
  let sp = Map.findWithDefault noSpan g sites
  modify' $ \st -> st {gsErrs = backendUnsupported g sp construct detail : gsErrs st}
  -- a unit placeholder operand; M0 never reaches this on the happy path.
  declRuntime "declare ptr @kunit()"
  r <- freshReg
  emit (r <> " = call ptr @kunit()")
  pure r

-- | Enqueue a global for emission (idempotent).  Identical role to C's
-- 'Kappa.Backend.C.enqueue'.
enqueue :: GName -> Gen ()
enqueue g = do
  seen <- gets gsEmitted
  unless (g `Set.member` seen) $
    modify' $ \st -> st {gsEmitted = Set.insert g (gsEmitted st), gsQueue = g : gsQueue st}

-- ── Names ────────────────────────────────────────────────────────────
--
-- Identical mangling to 'Kappa.Backend.C': LLVM identifiers admit the same
-- @[A-Za-z0-9_]@ charset C does, so @kg_main_2e_main@ is a legal LLVM symbol
-- (prefixed with @\@@ at use sites).

-- | A unique, valid identifier for a global's accessor function (no @\@@).
cGlobIdent :: GName -> Text
cGlobIdent g = "kg_" <> mangle (gKey g)

mangle :: Text -> Text
mangle = T.concatMap esc
  where
    esc c
      | isAsciiLower c || isAsciiUpper c || isDigit c = T.singleton c
      | otherwise = "_" <> T.pack (showHex (ord c) "") <> "_"

-- ── Constructor tag ids (Milestone C) ────────────────────────────────
--
-- A constructor value carries a small integer @tagid@; pattern matching
-- dispatches on an int compare (@kctor_tagid@) rather than a name strcmp.  The
-- id must be IDENTICAL at every construction site and every match site for a
-- given constructor — this backend guarantees that with the SAME two-bucket
-- rule the C backend uses ("Kappa.Backend.C", LR2 §244):
--
--   * BUILTIN constructors (the eight the runtime builds — Unit/True/False/
--     ::/Nil/Some/None/__rat — plus the §18.1 effect/Exit/Cause/outcome ctors
--     the runtime delivers) use the FIXED numeric ids from runtime/kappart.h's
--     @KCT_*@ enum.  This is load-bearing for cross-backend value flow: e.g.
--     every comparison prim (@eqInt@/@ltInt@/@eqStr@/…) builds its Bool via the
--     runtime's @kbool@, which tags it @KCT_TRUE@/@KCT_FALSE@; a @match@ on a
--     comparison result — or a 'compileIf' — only dispatches correctly if THIS
--     backend's True/False ids equal the runtime's.  'builtinCtorTagId' is the
--     numeric transcription of that enum and MUST stay in sync with kappart.h.
--   * USER constructors (everything else) get @KCT_USER_BASE+i@, assigned by
--     'hostCtorTags' deterministically (sorted by gKey).  These are self-
--     consistent within the @.ll@ (construct id == match id); the sorted
--     assignment additionally makes them match the C backend's @KT_*@ enum for
--     debuggability.  Milestone L: the assignment ALSO covers the @std.ffi@
--     wrapper ctors a host binding marshals through, so the @.ll@ and the
--     Driver's wrapper sidecar @.c@ ('hostFfiSidecar') agree on each id.

-- The fixed @KCT_*@ numeric id for a runtime-built builtin constructor
-- ('builtinCtorTagId') and the user-id base ('kctUserBase') are imported from
-- "Kappa.Builtins" — the single source of truth shared with the C backend and
-- checked against @runtime/kappart.h@. LLVM IR has no symbolic enum constant
-- (unlike the C backend's @KCT_*@ names), so this backend spells the literal
-- number 'builtinCtorTagId' returns.

-- | Walk every recorded core body and assign each referenced USER constructor
-- (one not in 'builtinCtorTagId') a @KCT_USER_BASE+i@ id, sorting the gKeys so
-- the assignment is deterministic (Blue<Green<Red ⇒ 40,41,42) and matches the
-- C backend's @KT_*@ enum order.  Builtins are excluded (they keep their fixed
-- ids).  Computed once up front so 'compile' can emit a literal @i32@.
-- | Milestone L: the user-constructor tag map, INCLUDING the @std.ffi.MkXxx@
-- wrapper constructors a host-binding member's marshalling builds
-- ('rnsCollectCtors': @MkI64@/@MkU64@/@MkRawPtr@/…).  Folding the host ctors in
-- here is what makes the @.ll@ and the Driver's wrapper sidecar @.c@ agree on a
-- ctor's numeric tag id: a host symbol that boxes its result as @MkU64@ (in the
-- sidecar, via @kctor(KT_std_ffi_MkU64, …)@) and an in-program match on the same
-- @MkU64@ (in the @.ll@, via a literal @i32@) MUST use the identical id, or the
-- match never fires.  Both derive that id from THIS map — the @.ll@ via
-- 'gsCtorTags', the sidecar via 'hostFfiSidecar' (which emits a @#define
-- KT_<mangle> <id>@ for exactly the ctors a wrapper references).  The ordering
-- (sorted gKeys from 'kctUserBase') is unchanged, so a program that uses no host
-- bindings gets byte-identical ids to before.
hostCtorTags :: Map GName Term -> Map GName ResolvedNativeSymbol -> Map Text Int
hostCtorTags bodies hostSyms =
  let bodyKeys = foldMap userCtorKeys (Map.elems bodies)
      hostKeys = Set.fromList (concatMap rnsCollectCtors (Map.elems hostSyms))
      keys = Set.toList (Set.union bodyKeys hostKeys)
   in -- KBackendIR Stage 2: the user-ctor numbering (sort gKeys, assign
      -- @KCT_USER_BASE + i@) is the single authority in "Kappa.Backend.Repr",
      -- shared with the C backend so the two agree on every id by construction.
      Repr.assignUserCtorTags keys

-- | The gKeys of every USER constructor referenced (constructed via 'CCtor' or
-- matched via 'CPCtor') anywhere in a term.  Builtins are dropped — they do not
-- need a codegen-assigned id.
userCtorKeys :: Term -> Set Text
userCtorKeys = goT
  where
    user g
      | Repr.isBuiltinCtor g = Set.empty -- builtins keep fixed ids; not numbered
      | otherwise = Set.singleton (gKey g)
    goT t = case t of
      CUniverseLift _ _ _ inner -> goT inner
      CSchemaLift _ _ _ _ _ _ _ _ inner -> goT inner
      CVar {} -> Set.empty
      CLocal {} -> Set.empty
      CGlob {} -> Set.empty
      CLam _ _ _ b -> goT b
      CPi _ _ _ _ ty b -> goT ty <> goT b
      CApp _ a b -> goT a <> goT b
      CSort {} -> Set.empty
      CLevel {} -> Set.empty
      CLit {} -> Set.empty
      CCtor g _ args -> user g <> foldMap goT args
      CMatch s _ alts -> goT s <> foldMap goAlt alts
      CRecordT fs -> foldMap (goT . snd) fs
      CRecordV fs -> foldMap (goT . snd) fs
      CProj e _ -> goT e
      CProjAt e _ _ -> goT e
      CVariantT ts -> foldMap goT ts
      CInject _ e -> goT e
      CLet _ _ ty rhs body -> goT ty <> goT rhs <> goT body
      CLetRec _ _ ty rhs body -> goT ty <> goT rhs <> goT body
      CLetPolyM _ _ _ _ ty rhs body -> goT ty <> goT rhs <> goT body
      CLetRecPolyM _ _ _ _ ty rhs body -> goT ty <> goT rhs <> goT body
      CLetRecGroupM _ definitions body ->
        Set.unions
          (goT body : [goT (clrdType definition) <> goT (clrdRhs definition) | definition <- definitions])
      CMeta {} -> Set.empty
      CDo _ items -> foldMap goItem items -- §M-E+: ctors ARE built/matched in the do-kernel
      CSealE _ e -> goT e
      CSigT _ e -> goT e
      CThunkE e -> goT e
      CLazyE e -> goT e
      CForceE e -> goT e
      CIf c th el -> goT c <> goT th <> goT el
      CQuote _ ts -> foldMap goT ts
    goAlt (CaseAlt pat mg body) =
      goPat pat <> maybe Set.empty goT mg <> goT body
    -- §M-E+: a do-kernel item carries Terms (its actions/conditions) AND its own
    -- CorePat binders (KBind/KLet/KLetQ/KFor/KUsing) — both can mention user ctors.
    -- Mirrors 'Kappa.CoreOps.foldTerm' goK, plus the patterns that walker ignores.
    -- WITHOUT this, a ctor used only inside a do-block was missed -> defaulted to
    -- 'kctUserBase' -> tag-id collision -> non-exhaustive/wrong match (the delve bug).
    goItem k = case k of
      KBind _ pat t _ -> goPat pat <> goT t
      KLet _ pat t -> goPat pat <> goT t
      KLetQ pat t m -> goPat pat <> goT t <> foldMap (\(p, e) -> goPat p <> goT e) m
      KExpr t -> goT t
      KVarItem _ _ actT _ -> goT actT
      KAssign _ _ _ actT _ -> goT actT
      KReturn t -> goT t
      KBreak _ -> Set.empty
      KContinue _ -> Set.empty
      KWhile _ c b e -> goT (kCondTermLL c) <> foldMap goItem b <> foldMap (foldMap goItem) e
      KFor _ pat s b e -> goPat pat <> goT s <> foldMap goItem b <> foldMap (foldMap goItem) e
      KIf alts e -> foldMap (\(c, b) -> goT c <> foldMap goItem b) alts <> foldMap (foldMap goItem) e
      KDefer _ t -> goT t
      KUsing pat a r -> goPat pat <> goT a <> goT r
      KSubDo _ b -> foldMap goItem b
    goPat p = case p of
      CPWild -> Set.empty
      CPVar _ -> Set.empty
      CPLit _ -> Set.empty
      CPCtor g _ ps -> user g <> foldMap goPat ps
      CPTuple ps -> foldMap goPat ps
      CPRecord fs _ -> foldMap (goPat . snd) fs
      CPInject _ q -> goPat q
      CPInjectRest _ -> Set.empty
      CPOr ps _ -> foldMap goPat ps
      CPAs _ q -> goPat q

-- | Resolve a constructor's gKey to its numeric tag id: the fixed builtin id if
-- it is one, else its precomputed @KCT_USER_BASE+i@ id.  A user ctor missing
-- from the map would be an internal bug ('hostCtorTags' walks all bodies
-- before codegen), so default to @kctUserBase@ rather than crash — a clean
-- non-match at worst, never a silent collision with a builtin.
ctorTagId :: GName -> Gen Int
ctorTagId g = do
  tags <- gets gsCtorTags
  -- KBackendIR Stage 2: builtin-or-user tag-id resolution is the single
  -- authority 'Repr.tagId' — the SAME resolver the C backend routes through,
  -- so a literal @i32@ here and the C backend's @KCT_*@/@KT_*@ name resolve to
  -- identical numbers.
  pure (Repr.tagId tags g)

-- ── String literal pool ──────────────────────────────────────────────

-- | UTF-8 byte length of a string (mirrors 'Kappa.Backend.C.utf8Len').
utf8Len :: Text -> Int
utf8Len = T.foldl' (\acc c -> acc + length (utf8Bytes c)) 0

-- | UTF-8 encode one character to bytes (mirrors 'Kappa.Backend.C.utf8Bytes').
utf8Bytes :: Char -> [Int]
utf8Bytes c =
  let n = ord c
   in if n < 0x80
        then [n]
        else
          if n < 0x800
            then [0xC0 + (n `div` 0x40), 0x80 + (n `mod` 0x40)]
            else
              if n < 0x10000
                then [0xE0 + (n `div` 0x1000), 0x80 + ((n `div` 0x40) `mod` 0x40), 0x80 + (n `mod` 0x40)]
                else
                  [ 0xF0 + (n `div` 0x40000)
                  , 0x80 + ((n `div` 0x1000) `mod` 0x40)
                  , 0x80 + ((n `div` 0x40) `mod` 0x40)
                  , 0x80 + (n `mod` 0x40)
                  ]

-- | The byte sequence of a string in LLVM @c"..."@ notation: printable
-- ASCII verbatim, everything else (including @"@, @\@, and high UTF-8 bytes)
-- as a two-hex-digit @\\HH@ escape.  Carrying the exact byte length (NOT
-- @strlen@) mirrors C's 'cStrL' so an embedded NUL is NUL-safe.
llvmBytes :: Text -> Text
llvmBytes s = T.concat [byte b | c <- T.unpack s, b <- utf8Bytes c]
  where
    byte b
      | b == 0x22 = esc b -- "
      | b == 0x5C = esc b -- backslash
      | b >= 0x20 && b < 0x7F = T.singleton (toEnum b)
      | otherwise = esc b
    esc b =
      let h = showHex b ""
          h2 = if length h == 1 then '0' : h else h
       in "\\" <> T.pack h2

-- | Intern a string literal into the module's constant pool and return the
-- SSA operand for its runtime @KValue*@ — a @kstr(ptr, i64 byteLen)@ call.
-- Uses @kstr@ (explicit byte length), NEVER @kstr0@, so a string with an
-- embedded NUL is not truncated (parity with C's 'cStrL').
internStr :: Text -> Gen Text
internStr s = do
  n <- gets (length . gsStrs)
  let name = "@.str." <> T.pack (show n)
      len = utf8Len s
  modify' $ \g -> g {gsStrs = (name, llvmBytes s, len) : gsStrs g}
  declRuntime "declare ptr @kstr(ptr, i64)"
  r <- freshReg
  emit (r <> " = call ptr @kstr(ptr " <> name <> ", i64 " <> T.pack (show len) <> ")")
  pure r

-- | Intern a NUL-terminated C string into the module's constant pool and
-- return its @\@.cstr.N@ global name (a @ptr@ operand).  Unlike 'internStr'
-- (a length-carrying @KValue*@ via @kstr@), this is a raw @const char *@ for
-- @kbigint_str@: the constant carries a trailing @\\00@ byte so the callee can
-- @strlen@ it.  A bigint decimal is ASCII @[0-9-]@ only, so no UTF-8 escaping
-- subtlety applies, but 'llvmBytes' handles it uniformly regardless.
internCStr :: Text -> Gen Text
internCStr s = do
  n <- gets (length . gsCStrs)
  let name = "@.cstr." <> T.pack (show n)
      bytes = llvmBytes s <> "\\00" -- explicit NUL terminator
      len = utf8Len s + 1
  modify' $ \g -> g {gsCStrs = (name, bytes, len) : gsCStrs g}
  pure name

-- ── Top-level driver ─────────────────────────────────────────────────

-- | Lower a checked program to a complete LLVM IR translation unit, or
-- report the unsupported constructs.  The SAME signature as
-- 'Kappa.Backend.C.generateC', so the Driver dispatches on flags with no
-- change to the call site's type.
generateLL :: Bool -> Bool -> CheckState -> GName -> Set Text -> Map GName ResolvedNativeSymbol -> Either ([BackendError], Maybe [Text]) (Text, Maybe [Text])
generateLL rcEnabled reuseEnabled cs mainG ffiPrims hostSyms =
  case backendIRValidationErrors cs mainG of
    errs@(_ : _) -> Left (errs, Nothing)
    [] ->
      case rcValidation of
        Left failure -> Left failure
        Right mRcFindings ->
          let
            evalCtx0 = EvalCtx (Globals (csGlobals cs)) (csMetas cs) False (csFacts cs)
            backendIr = lowerKBackendIR cs
            st0 =
              GenState
                { gsFresh = 0
                , gsInsns = []
                , gsEnv = "null"
                , gsTop = []
                , gsDecls = Set.empty
                , gsStrs = []
                , gsCStrs = []
                , gsGlobalsExtra = []
                , gsEmitted = Set.singleton mainG
                , gsQueue = [mainG]
                , gsErrs = []
                , gsCur = mainG
                , gsGlobals = csGlobals cs
                , gsEvalCtx = evalCtx0
                , gsBodies = csCoreBodies cs
                , gsBackendBodies = kbirBodies backendIr
                , gsSuspenders = suspenderGlobalsWith (blockingHostGlobals hostSyms) evalCtx0 (csGlobals cs) (csCoreBodies cs)
                , gsPrims = Set.union basePrims ffiPrims
                , gsDeclSites = csDeclSites cs
                , gsCtorTags = hostCtorTags (csCoreBodies cs) hostSyms
                , gsBlock = "build"
                , gsCtorSet = Map.keysSet (csCtors cs)
                , gsDataSet = Set.union (Map.keysSet (csDatas cs)) (Map.keysSet (csTraits cs))
                , gsHostSyms = hostSyms
                , gsScalarHelpers = Set.empty
                , gsScalarLetSlots = []
                , gsRcRuntimeEnabled = False
                }
            final = execState (drainQueue >> emitMain mainG) st0
            -- §18.1.17/§27.6/§34.3.3 Stage-4a: the LLVM backend links the SAME one-shot
            -- kappart2 runtime, so it rejects a reachable multi-shot resumption too.
            multishotErrs = multishotLegality cs (gsEmitted final)
           in case reverse (gsErrs final) ++ multishotErrs of
                [] -> Right (assembleLL final, mRcFindings)
                errs -> Left (errs, mRcFindings)
  where
    -- Reuse the C backend's fail-closed KBackendIR/RC validation before LLVM
    -- emission. This keeps LLVM RC builds from silently bypassing node-local
    -- ownership metadata while avoiding a second, drifting validation path.
    rcValidation
      | rcEnabled = case generateC True reuseEnabled cs mainG ffiPrims hostSyms of
          Left failure -> Left failure
          Right (_, mRcFindings) -> Right mRcFindings
      | otherwise = Right Nothing

-- | Milestone L (§27.1.1): the C-WRAPPER SIDECAR translation unit for a build's
-- host-native FFI members.  The @.ll@ the LLVM backend emits lowers a host
-- member reference like a prim over the wrapper symbol ('wrapperCName') and
-- @declare@s that symbol extern; this sidecar @.c@ DEFINES each wrapper (reusing
-- the SAME 'externPrototype' / 'wrapperDefinition' marshalling the C backend
-- uses — the FFI boundary is inherently C-ABI, so the marshalling is not
-- re-derived in IR), and the Driver compiles + links it alongside the @.ll@ and
-- the runtime @.c@ sources.  Wrappers are emitted for ALL host syms (an unused
-- one is dead-stripped by the linker), so no usage tracking is needed.
--
-- The @KT_<mangle>@ tag-id macros a wrapper references for an @std.ffi.MkXxx@ /
-- @MkRawPtr@ boxed result are @#define@d here to the SAME numeric ids the @.ll@
-- assigns ('hostCtorTags' over the program's core bodies + the host syms), so a
-- ctor a wrapper builds matches an in-program pattern-match on it.  Returns
-- 'Nothing' when there are no host syms (the Driver then emits no sidecar).
hostFfiSidecar :: CheckState -> Map GName ResolvedNativeSymbol -> Maybe Text
hostFfiSidecar cs hostSyms
  | Map.null hostSyms = Nothing
  | otherwise =
      let syms = Map.elems hostSyms
          tagMap = hostCtorTags (csCoreBodies cs) hostSyms
          -- the std.ffi ctors any wrapper actually boxes/unboxes (MkU64/MkI32/…);
          -- each gets a KT_<mangle> define so the wrapper's kctor(KT_…, …) uses
          -- the exact id the .ll's match emits.  Sorted for a deterministic file.
          ctorKeys = sort (Set.toList (Set.fromList (concatMap rnsCollectCtors syms)))
          ktDefines =
            [ "#define KT_" <> mangle k <> " " <> T.pack (show i)
            | k <- ctorKeys
            , Just i <- [Map.lookup k tagMap]
            ]
          protos = dedupKeep (map externPrototype syms)
          -- 'wrapperDefinition' emits the wrapper @static@ (the C backend keeps
          -- it in the same TU as the call site).  In the sidecar the wrapper is
          -- a SEPARATE TU from the .ll that calls it, so it needs EXTERNAL
          -- linkage — strip the leading @static @ so the symbol is visible to
          -- the .ll's extern @declare@.  ('wrapperDefinition' is unchanged: the C
          -- backend, the only other caller, still gets the @static@ form.)
          wrappers = map (externalizeWrapper . wrapperDefinition) syms
       in Just . T.unlines $
            [ "/* Generated by the Kappa LLVM backend host-FFI sidecar"
                <> " (Kappa.Backend.LLVM.hostFfiSidecar). */"
            , "/* §27.1.1 native host bindings: the C-wrapper marshalling the"
                <> " emitted .ll calls extern. */"
            , "#include \"kappart2.h\"" -- same runtime header the generated C uses; pulls in kappart.h
            , ""
            , "/* std.ffi wrapper-ctor tag ids — identical to the .ll's literal"
                <> " ids (LLVM.hostCtorTags) so a boxed FFI result matches an"
                <> " in-program pattern-match on it. */"
            ]
              ++ ktDefines
              ++ [""]
              ++ protos
              ++ [""]
              ++ wrappers
  where
    -- keep first occurrence, drop later duplicates (a C symbol shared by two
    -- members gets one extern prototype) — mirrors C.hs 'hostNativeBlock'.
    dedupKeep = go Set.empty
      where
        go _ [] = []
        go seen (x : xs)
          | x `Set.member` seen = go seen xs
          | otherwise = x : go (Set.insert x seen) xs
    -- Give the wrapper external linkage by dropping the leading @static @ that
    -- 'wrapperDefinition' prepends.  Each wrapper definition begins with the
    -- exact prefix @"static KValue *"@; replace just that one occurrence.
    externalizeWrapper t = case T.stripPrefix "static " t of
      Just rest -> rest
      Nothing -> t

-- | The base primitives the @kappart@ runtime implements.  Milestone I widens
-- this to EVERY prim in the shared 'primEntries' table (the C backend's full
-- catalogue of cfn/arity/isIO), minus the small 'ckMachinePrims' blocklist of
-- ops whose synchronous @knative@/@knative_sat@ bridge would diverge from the
-- CK-machine semantics the interpreter (the oracle) and the C backend's
-- node-builders give them.  Every name here is lowerable: a saturated call goes
-- through 'compilePrimApp' (IO ⇒ @knative_sat@; pure ⇒ @kp_*@ direct or the
-- @kpf_*(arr)@ array call), and a bare/partial reference goes through
-- 'compilePrimValue' (the curried @knative@ closure).
--
-- INVARIANT: 'globPrimName' returns a name only when it is in @gsPrims@, and
-- 'compilePrimApp'/'compilePrimValue' must then handle it — which they do for
-- any 'primEntries' member.  The do-kernel monad/ref ops (@ioBind@/@ioThen@/
-- @ioPure@ and the internal @__ioNewRef@/@__ioReadRef@/@__ioWriteRef@) are
-- still recognised here. In
-- do-contexts, surface `var` / assignment already carry MonadRef-selected
-- action terms, and 'compileMonadicAction' handles those as ordinary actions.
-- Direct primitive calls outside that path fall to the generic @knative_sat@
-- lowering, exactly as in the C backend.
basePrims :: Set Text
basePrims =
  Set.difference (Map.keysSet primEntries) ckMachinePrims
    -- §18.1.12 masking node-builders ('ioNodeBuilder'): like the exception ops,
    -- these have no @kpf_*@ entry in 'primEntries' (they ARE krt2_* nodes), so add
    -- them here so 'globPrimName' recognises a saturated `uninterruptible`/`mask`/
    -- `poll` and routes it to 'compilePrimApp' → 'compileIoNode' (krt2_*) rather
    -- than the bare-value path.
    `Set.union` Set.fromList ["blocking", "uninterruptible", "__mask", "poll"]
    -- §18.1.12 rank-2 restore adapter: lowered to a bare kapp(raw, act) in
    -- 'compilePrimApp' (no kpf_* entry, no krt2_* node), so add it here so
    -- 'globPrimName' recognises a saturated `__restoreAt` rather than rejecting it.
    `Set.union` Set.fromList ["__restoreAt"]
    -- §18.1.4/§18.1.7 reason-carrying finalizers + locallyFiberRef: krt2_* node
    -- builders ('ioNodeBuilder'), no kpf_* primEntry, so add them here too.
    `Set.union` Set.fromList ["onExit", "onInterrupt", "locallyFiberRef"]
    -- §18.1.4 __reraiseCause: the @krt2_reraise@ node-builder (the join/race/
    -- timeout/awaitPromise failure arms re-raise a captured Cause as-is).  It is a
    -- registered prim with NO kpf_* primEntry (catchIO/finallyIO/throwIO DO have
    -- one, so they ride the difference above; __reraiseCause does not), so add it
    -- here so a saturated `__reraiseCause c` routes to 'compileIoNode' (krt2_reraise)
    -- rather than the unsupported bare-value path — the join/awaitPromise gap.
    `Set.union` Set.fromList ["__reraiseCause"]
    -- §18.1.13 STM + §18.1.6/§19.5 race/timeout/withScope + §18.1.4 explicit-cause
    -- interruption: krt2_* node-builders ('ioNodeBuilder') with no kpf_* primEntry
    -- (the C backend special-cases them in 'compileAppGlob').  Add them here so
    -- 'globPrimName' recognises a saturated occurrence and routes it to
    -- 'compilePrimApp' → 'compileIoNode' (the krt2_* node) rather than the
    -- unsupported bare-value path.  The STM Monad/Applicative dictionaries
    -- reference stmBind/stmPure by value, but the ELABORATOR eta-expands a bare
    -- node-builder prim into nested lambdas whose LEAF is a SATURATED application
    -- (e.g. `\m k -> stmBind m k`), so 'compileTail' reaches that saturated leaf
    -- and 'compileIoNode' builds the node — exactly as the C backend lowers the
    -- same eta-expanded Core (C.hs join/dictionary output: a kfn chain ending in
    -- `krt2_stm_bind(kvar(cenv,0), arg)`).  A node-builder prim with no kpf_*
    -- wrapper that is GENUINELY partially applied (hand-written `writeTVar t` by
    -- value) is rejected on BOTH backends identically ('compilePrimValue' here,
    -- 'emitPrim' in C) — it does not arise in elaborated programs.
    `Set.union` Set.fromList
      [ "stmBind", "stmPure", "newTVar", "readTVar", "writeTVar", "atomically"
      , "__race", "__timeout", "withScope", "__interruptWait", "__interruptNoWait"
      , "__interruptForkAny"
      ]

-- | The prims kept OUT of LLVM coverage because their meaning is the CK-machine
-- node, not the synchronous @knative@/@knative_sat@ bridge.  As of the
-- curried-CK-prim milestone this blocklist is EMPTY: every CK-machine prim is now
-- lowered, exactly as the C backend does it, on the uniform CK-machine path —
--
--   * Milestone M closed the EXCEPTION ops (throwIO/catchIO/finallyIO), which
--     lived here because of a CONCRETE parity divergence (the @ioerror@ native
--     case): @catchIO risky handler@ where @risky@ is a do-block
--     (`printlnString "before"; raise "boom"; …`) lowers @risky@ to a @krt2_*@
--     action tree, but the synchronous @kpf_io_catchIO@ bridge's @krun_io@ could
--     not drive that tree — it dropped the body's effects and the thrown value
--     (interp/C print @before\\ncaught:boom\\nafter@; the bridge printed only
--     @after@).  They became 'ioNodeBuilder' node-builders in 'compilePrimApp'.
--
--   * The curried-CK-prim milestone closes the rest.  STM (atomically/stmBind/
--     stmPure/newTVar/readTVar/writeTVar) and §18.1.6/§19.5 race/timeout/
--     withScope/explicit-cause interruption have NO @primEntry@ — the C backend
--     special-cases them in 'compileAppGlob' — so they are added to
--     'ioNodeBuilder' (the @krt2_stm_*@/@krt2_atomically@/@krt2_race@/… builders).
--     fork/await/scope/monitor/sleep all reduce to prims that DO have a @kpf_*@
--     entry in the shared 'primEntries' (@__forkRun@→@kpf_fork@, @__awaitFiber@→
--     @kpf_await@, @__sleepForNanos@→@kpf_sleep_for@, @newScope@→@kpf_new_scope@,
--     @forkIn@→@kpf_fork_in@, @monitor@→@kpf_monitor@, @retry@→@kpf_retry@, …);
--     each @kpf_*@ wrapper itself builds the krt2_* node, so once de-blocklisted
--     they lower through the ORDINARY 'compilePrimApp'/'compilePrimValue' paths —
--     a saturated occurrence to @kpf_*(arr)@ and a curried/by-value reference to
--     @knative(\@kpf_*, …)@ — byte-identical to the C backend (the surface
--     @fork@/@await@/@sleepFor@/@self@/@spawn@ names are PRELUDE functions, not
--     prims, so they never needed an entry here at all).
--
-- The do-kernel ('compileDo') follows the C backend's semantic split:
-- suspending or structured-finalizer blocks lower to @krt2_*@ action trees with
-- LAZY continuation closures, while simple non-suspending do values are delayed
-- behind @kio(fn, env)@ so their pure lets run when the action executes, not when
-- the action value is constructed.
ckMachinePrims :: Set Text
ckMachinePrims = Set.empty

-- | Emit globals until the work queue is empty (mirrors C's 'drainQueue').
drainQueue :: Gen ()
drainQueue = do
  q <- gets gsQueue
  case q of
    [] -> pure ()
    (g : rest) -> do
      modify' $ \st -> st {gsQueue = rest}
      emitGlobal g
      drainQueue

-- | Emit one global's accessor as a memoised @kg_*()@ CAF: a module-level
-- @.cache@ global plus an accessor that compiles the term once, caches it, and
-- returns the cached-or-fresh value.
--
-- Milestone D removes the M0 arity≥1 guard.  A FUNCTION-shaped global
-- (@f = lam x => …@) is simply a CAF whose value is a (nested) 'CLam'; the body
-- is compiled UNIFORMLY in tail position and the 'CLam' lowers to a @kclo@
-- (see 'compileLam').  The memoised accessor then caches that closure — which is
-- capture-free (its @cenv@ is @null@), so the cache is sound.  Recursion works
-- without a build-time loop: a self-reference is @CGlob f@ → a call to THIS
-- accessor, and the closure is built LAZILY (the @kfn_N@ body runs only when
-- applied), so emitting/​caching @f@'s closure never re-enters @f@'s accessor.
emitGlobal :: GName -> Gen ()
emitGlobal g = do
  modify' $ \st -> st {gsCur = g}
  bodies <- gets gsBackendBodies
  let ident = cGlobIdent g
  case Map.lookup g bodies of
    Nothing -> do
      -- §12.2/§31.2: a genuinely type-level / opaque global (a data\/trait name, or
      -- a sort-typed builtin like @Integer@ pulled in by an instance head) is
      -- computationally ERASED — its accessor yields the unit placeholder (the inert
      -- value the interpreter never inspects), so an accepted program that mentions
      -- it compiles rather than being refused.  Mirrors the C backend (C.hs:483-499).
      -- A real value-typed global with no recorded body is NOT erasable (that would
      -- miscompile it) — surfaced honestly as a backend gap.
      typeLevel <- isTypeGlob g
      if typeLevel
        then do
          (insns, endBlock, operand) <- captured "null" compileUnit
          emitArity0Accessor ident insns endBlock operand
        else
          reportArity0Failure ident
            ("'" <> gKey g <> "' has no recorded core body and is not a type-level "
              <> "global, so it cannot be lowered (no-core-body)")
    Just body -> do
      -- §12.2/§31.2/§14.4: a definition whose RESULT TYPE is a RuntimeErased proof
      -- (a propositional equality / h-prop evidence — e.g. the prelude lemmas
      -- 'isPropEq'/'unsafeAssertProof'/'cong' reached via lawful-by-default
      -- 'Monoid') is computationally irrelevant: its body is the ADMIT primitive
      -- '__eqProof'/'__unsafeAssertProof' the LLVM runtime cannot lower, so its
      -- accessor is the unit placeholder and its body is NOT compiled (no scalar
      -- worker either).  Mirrors the C backend's 'emitGlobal'; see 'resultIsProofP'.
      proof <- resultIsProof g
      if proof
        then do
          (insns, endBlock, operand) <- captured "null" compileUnit
          emitArity0Accessor ident insns endBlock operand
        else case bbParams body of
          params@(_ : _) -> do
            (insns, endBlock, operand) <- captured "null" (compileCurriedFunction params (bbRoot body))
            emitArity0Accessor ident insns endBlock operand
            emitScalarWorkerIfEligible g
          [] -> do
          -- A CAF accessor's value is consumed DIRECTLY (cached + returned to a plain
          -- caller), so it must be a real value/closure — NOT a tail position.  Using
          -- 'compile' (not 'compileTail') drains any final application through @kapp@
          -- immediately; otherwise the cache would store an undrained @K_BOUNCE@ (a
          -- deferred tail call only the trampoline inside @kapp@ knows how to run), and
          -- a later 'kapp(op, …)' / 'showInt op' would see a non-value.  A function-shaped
          -- global is unaffected: its body is a 'CLam', a value in both paths.  Only the
          -- lifted @kfn_N@ FUNCTION body (invoked through @kapp@'s trampoline) is tail
          -- position and keeps 'compileTail'.
            (insns, endBlock, operand) <- captured "null" (compile (bbRoot body))
            emitArity0Accessor ident insns endBlock operand
            emitScalarWorkerIfEligible g

emitScalarWorkerIfEligible :: GName -> Gen ()
emitScalarWorkerIfEligible g = do
          -- Scalar function worker: if @g@ is a monomorphic first-order Int/Double
          -- function with a scalar-expressible body, ALSO emit the typed unboxed
          -- worker (@kwi_@/@kwd_@) beside the boxed curried-closure accessor.  A
          -- saturated direct call ('compileApp') then takes the unboxed fast path
          -- (with a boxed escape).  Mirrors the C backend's 'emitGlobal' tail.
  mplan <- scalarFnPlanLL g
  case mplan of
    Just (_, pks, ret, scalarInner) ->
      compileScalarFnWorkerLL g pks ret scalarInner
    Nothing -> pure ()

backendFuncArity :: BackendTerm -> (Int, BackendTerm)
backendFuncArity = go 0
  where
    go !n (BLam _ _ _ _ _ b) = go (n + 1) b
    go !n t = (n, t)

-- | Emit a memoised arity-0 accessor (the §3.1 IR): a @.cache@ global, a
-- load+null-check fast path, a @build@ block that compiles the term and stores
-- the result, and a @phi@ that returns the cached-or-fresh value.  @endBlock@ is
-- the label of the block active when the term FINISHED compiling — the same as
-- @build@ for straight-line code, but a distinct join block when the term
-- introduced control flow (a @match@/@if@).  The trailing @store@/@br@ run in
-- that block, and the @ret@ phi names it as the fresh value's predecessor.
emitArity0Accessor :: Text -> [Text] -> Text -> Text -> Gen ()
emitArity0Accessor ident buildInsns endBlock operand = do
  declRuntime "declare void @krc_mark_shared_recursive(ptr)"
  let cacheG = "@" <> ident <> ".cache"
  modify' $ \st ->
    st {gsGlobalsExtra = (cacheG <> " = internal global ptr null, align 8") : gsGlobalsExtra st}
  let def =
        T.unlines $
          [ "define internal ptr @" <> ident <> "() {"
          , "entry:"
          , "  %cached = load atomic ptr, ptr " <> cacheG <> " acquire, align 8"
          , "  %hit = icmp ne ptr %cached, null"
          , "  br i1 %hit, label %ret, label %build"
          , ""
          , "build:"
          ]
            ++ map ("  " <>) buildInsns
            ++ [ "  call void @krc_mark_shared_recursive(ptr " <> operand <> ")" ]
            ++ [ "  store atomic ptr " <> operand <> ", ptr " <> cacheG <> " release, align 8"
               , "  br label %ret"
               , ""
               , "ret:"
               , "  %r = phi ptr [ %cached, %entry ], [ " <> operand <> ", %" <> endBlock <> " ]"
               , "  ret ptr %r"
               , "}"
               ]
  modify' $ \st -> st {gsTop = def : gsTop st}

-- | Report an arity-0 accessor we cannot lower, while still emitting a
-- well-formed (placeholder) accessor so module assembly stays valid for
-- error reporting.  ('generateLL' discards the assembled module when there
-- are errors; the accessor only needs to keep the State consistent.)
reportArity0Failure :: Text -> Text -> Gen ()
reportArity0Failure ident detail = do
  (insns, endBlock, operand) <- captured "null" (unsupported "definition" detail)
  emitArity0Accessor ident insns endBlock operand

-- | The @\@main@ entry point.  It follows the C runtime entry protocol
-- (@krt2_new(0)@, @krt2_run_main(kg_main())@, success -> process 0) but keeps
-- runtime RC counting/freeing effects disabled until LLVM emits matching ownership operations.
-- Default LLVM builds still run the C-side RC validator when requested; only
-- C currently claims generated free-on-zero execution.
emitMain :: GName -> Gen ()
emitMain g = do
  rcRuntimeOn <- gets gsRcRuntimeEnabled
  let ident = cGlobIdent g
  declRuntime "declare ptr @krt2_new(i32)"
  declRuntime "declare ptr @krt2_run_main(ptr)"
  declRuntime "declare i32 @krt2_exit_is_success(ptr)"
  unless rcRuntimeOn $
    declRuntime "declare void @krc_set_enabled(i32)"
  let rcGate =
        [ "  call void @krc_set_enabled(i32 0)" | not rcRuntimeOn ]
      body =
        [ "define i32 @main() {"
        , "entry:"
        ]
          ++ rcGate
          ++ [ "  %rt = call ptr @krt2_new(i32 0)"
             , "  %m = call ptr @" <> ident <> "()"
             , "  %exit = call ptr @krt2_run_main(ptr %m)"
             , "  %ok = call i32 @krt2_exit_is_success(ptr %exit)"
             , "  %fail = icmp eq i32 %ok, 0"
             , "  %code = select i1 %fail, i32 1, i32 0"
             , "  ret i32 %code"
             , "}"
             ]
  let def =
        T.unlines body
  modify' $ \st -> st {gsTop = def : gsTop st}

-- | Concatenate the translation unit: header, string-constant pool, the
-- @.cache@ globals, the dedup'd @declare@ set, and the top-level @define@s
-- (mirrors C's 'assemble').  No @target triple@/@datalayout@ — clang infers
-- host defaults (avoids override warnings).
assembleLL :: GenState -> Text
assembleLL st =
  T.unlines $
    [ "; Generated by the Kappa native backend (Kappa.Backend.LLVM)."
    , "; uniform-boxed parity with Kappa.Backend.C; same kappart2 runtime."
    , "source_filename = \"kappa\""
    , ""
    ]
      ++ strPool
      ++ cStrPool
      ++ [""]
      ++ reverse (gsGlobalsExtra st)
      ++ [""]
      ++ Set.toList (gsDecls st)
      ++ [""]
      ++ reverse (gsTop st)
  where
    -- A string pool entry: @.str.N = private constant [len x i8] c"...".  The
    -- LHS keeps the leading @ (it is a module-level global definition).
    strPool =
      [ name <> " = private unnamed_addr constant [" <> T.pack (show len)
          <> " x i8] c\"" <> bytes <> "\", align 1"
      | (name, bytes, len) <- reverse (gsStrs st)
      ]
    -- NUL-terminated C-string constants for @kbigint_str@ (length already
    -- includes the trailing @\\00@ that 'internCStr' appended to @bytes@).
    cStrPool =
      [ name <> " = private unnamed_addr constant [" <> T.pack (show len)
          <> " x i8] c\"" <> bytes <> "\", align 1"
      | (name, bytes, len) <- reverse (gsCStrs st)
      ]

-- ── Term lowering ────────────────────────────────────────────────────

-- | Compile a term: emit any needed instructions into the current basic
-- block and return an SSA OPERAND (@%reg@ / @\@global@ / @ptr null@) for its
-- value.  The three-address discipline is the one structural difference
-- from C's 'compile' (which returns a nested expression string).
--
-- Supported subset: a literal, a bare global reference, a saturated
-- application whose head is a known prim, a bound-variable read ('CVar'), and a
-- non-recursive local @let@ ('CLet').  General application and closures remain
-- a later milestone.
compile :: BackendTerm -> Gen Text
compile term = do
  -- §12.2/§31.2/§14.4: a value whose head is a proof-typed global (a
  -- propositional-equality / h-prop lemma such as 'isPropEq' /
  -- 'unsafeAssertProof' / 'cong', reached via lawful-by-default 'Monoid' law
  -- members) is RuntimeErased — erase the WHOLE maximal spine to the unit
  -- placeholder so the ADMIT primitives '__eqProof'/'__unsafeAssertProof' beneath
  -- those lemmas are never reached.  Mirrors the C backend's 'compile' proof
  -- guard (C.hs); see 'resultIsProofP' for the soundness argument.
  proofSpine <- case headGlob term of
    Just g -> resultIsProof g
    Nothing -> pure False
  if proofSpine then compileUnit else compileTerm term

compileTerm :: BackendTerm -> Gen Text
compileTerm term = case term of
  BUnit {} -> compileUnit
  BLit _ l -> compileLit l
  BGlob _ g -> compileGlob g
  BApp {} -> compileApp term
  BVar _ _ i -> compileVar i
  BLam _ _ _ _ _ body -> compileLam body
  BLet _ _ _ _ rhs body -> compileLet rhs body
  -- Milestone J: a recursive local let — the body is in expression position
  -- here, so the body-compiler is plain 'compile'.
  BLetRec _ _ _ _ rhs body -> compileLetRecWith compile rhs body
  -- §19 suspensions: Delay re-evaluates on force; Memo caches (memo flag).
  BThunk _ e -> compileSuspension 0 e
  BLazy _ e -> compileSuspension 1 e
  BForce _ e -> compileForce e
  BCtor _ layout args -> compileCtor (bclCtor layout) args
  BIf _ c t e -> compileIf c t e
  BMatch _ scrut alts _ -> compileMatch scrut alts
  BDo _ lbl items -> compileDo lbl items
  -- Records (Milestone H) — a record VALUE, a name-based projection, and a
  -- precomputed-offset projection.  All three are plain values, so 'compileTail'
  -- routes them here unchanged (its @_ -> compile term@ fallback).
  BRecord _ fs -> compileRecord fs
  BProj _ e f Nothing -> compileProj e f
  BProj _ e _ (Just i) -> compileProjAt e i
  -- A record TYPE is type-level / quantity-0 erased (§12.2): if one ever reaches
  -- value position it is the unit placeholder, never inspected (mirrors C's
  -- @CRecordT _ -> kunit()@).  Keeps an erased record type from being reported as
  -- an unsupported "record".
  BSeal _ _ e -> compile e
  BInject _ tag e -> compileInject tag e
  _ ->
    unsupported "term"
      ("the LLVM backend M0 cannot lower this construct: " <> constructName term)

compileCurriedFunction :: [BackendParam] -> BackendTerm -> Gen Text
compileCurriedFunction params inner = case params of
  [] -> compile inner
  _ : rest -> do
    fnIdent <- freshLabel "kfn_"
    capturedEnv <- gets gsEnv
    declRuntime "declare ptr @kpush(ptr, ptr)"
    declRuntime "declare ptr @kclo(ptr, ptr)"
    (bodyInsns, _endBlock, resultOp) <- captured "%env" $ do
      emit ("%env = call ptr @kpush(ptr %arg, ptr %cenv)")
      if null rest
        then compileTail inner
        else compileCurriedFunction rest inner
    let def =
          T.unlines $
            [ "define internal ptr @" <> fnIdent <> "(ptr %cenv, ptr %arg) {"
            , "build:"
            ]
              ++ map ("  " <>) bodyInsns
              ++ [ "  ret ptr " <> resultOp
                 , "}"
                 ]
    modify' $ \st -> st {gsTop = def : gsTop st}
    r <- freshReg
    emit (r <> " = call ptr @kclo(ptr @" <> fnIdent <> ", ptr " <> capturedEnv <> ")")
    pure r

-- | Compile a term in TAIL position — a function body, a @match@/@if@ branch.
-- This is what gives DEEP recursion stack safety (Milestone D): a tail-position
-- closure call is deferred to the trampoline via @kbounce@ instead of recursing
-- in the C stack.  The AUTHORITY is the C backend's 'emitTailApp' (C.hs:1525):
--
--   * A general CLOSURE application (a 'CApp' spine whose head is NOT a
--     saturated prim and NOT an eta-ctor): evaluate the head and all-but-last
--     args EAGERLY with the ordinary @kapp@ chain (they build the partial
--     closure), then RETURN @call ptr \@kbounce(ptr %headClosure, ptr %lastArg)@
--     for the final application.  The driving @kapp@'s trampoline drains the
--     bounce, so a self-tail-recursive call runs in CONSTANT C stack.
--   * A saturated PRIM application (or eta-ctor): a prim/ctor returns a value
--     and never bounces — compile it normally and return it ('compile').
--   * 'CLet': compile the rhs NON-tail, @kpush@, then 'compileTail' the body
--     (restoring the env after) — the let-bound tail call still bounces.
--   * 'CMatch' / 'CIf': 'compileTail' each branch and @phi@ the results at the
--     join.  A @kbounce@ value flows through the phi unchanged and is drained by
--     the caller — that is fine.
--   * Any VALUE form ('CLam' / 'CLit' / 'CCtor' / 'CVar' / 'CGlob' / …): compile
--     normally and return it.  In particular a 'CLam' in tail position is a
--     closure VALUE returned directly — NOT bounced.
--
-- A non-tail subexpression uses plain 'compile' (the @kapp@ chain); its C-stack
-- depth is bounded by EXPRESSION depth, not recursion depth.
compileTail :: BackendTerm -> Gen Text
compileTail term = case term of
  BApp {}
    -- A saturated eta-expanded constructor is a final data value — build it
    -- directly (it cannot bounce or recurse).
    | Just (g, ctorArgs) <- etaCtorApp term -> compileCtor g ctorArgs
    | otherwise -> do
        let (hd, _) = backendSpineOf term
        mp <- case hd of BGlob _ g -> globPrimName g; _ -> pure Nothing
        case mp of
          -- A prim spine returns a value (no bounce) iff it is the saturated
          -- fast path; otherwise it falls through 'compile' to the kapp chain.
          Just pname | saturatedPrim pname term -> compile term
          _ -> compileTailApp term
  BLet _ _ _ _ rhs body -> do
    rv <- compile rhs
    env0 <- gets gsEnv
    declRuntime "declare ptr @kpush(ptr, ptr)"
    env1 <- freshReg
    emit (env1 <> " = call ptr @kpush(ptr " <> rv <> ", ptr " <> env0 <> ")")
    modify' $ \g -> g {gsEnv = env1}
    bv <- compileTail body
    modify' $ \g -> g {gsEnv = env0}
    pure bv
  BIf _ c t e -> compileIfWith compileTail c t e
  BMatch _ scrut alts _ -> compileMatchWith compileTail scrut alts
  -- Milestone J: a recursive local let whose BODY is in tail position — thread
  -- the tail-ness through to the body (the body-compiler is 'compileTail') so a
  -- tail self-call inside it still lowers to a @kbounce@ and deep local
  -- recursion stays stack-safe.
  BLetRec _ _ _ _ rhs body -> compileLetRecWith compileTail rhs body
  -- A force is a value (the forced thunk's result); compile it and return it.
  BForce _ e -> compileForce e
  -- Every other form is a value (or a non-bouncing construct): compile it
  -- normally and return it.  A CLam here is a closure value, NOT a bounce.
  _ -> compile term

-- | Is @pname@ a SATURATED-prim application in @term@ (so it returns a value
-- and never bounces)?  Mirrors the C backend's saturated-prim fast-path gate
-- ('compileAppGlob' fires its direct arm only at the exact arity): the
-- explicit-argument count equals the prim's known arity.  The arity is read
-- from ANY of the three saturated lowerings — an IO prim ('ioPrimEntry'), a
-- pure prim with a @kp_*@ helper ('pureDirectEntry'), or a pure prim with only
-- a @kpf_*@ wrapper ('primNativeEntry') — so a saturated nat/byte/bytes
-- conversion takes the direct wrapper-array call instead of the curried @kapp@
-- chain, exactly as the C backend does.  An under-/over-saturated prim spine
-- stays a curried closure through @kapp@ (and may bounce).
saturatedPrim :: Text -> BackendTerm -> Bool
saturatedPrim pname term =
  let (_, sargs) = backendSpineOf term
      nexpl = length [() | a <- sargs, argIcit a == Expl]
   in case primArity pname of
        Just ar -> nexpl == ar
        Nothing -> False

-- | The runtime arity of a lowerable prim (across all three saturated paths).
-- The CK-machine node-builders ('ioNodeBuilder' — exception ops + §18.1.12
-- masking) have no @kpf_*@ entry but ARE saturated-lowerable, so consult them
-- too; otherwise a saturated `uninterruptible`/`mask`/`poll` would be classed as
-- a bare value and rejected.
primArity :: Text -> Maybe Int
primArity "__restoreAt" = Just 2 -- §18.1.12 rank-2 restore adapter: kapp(raw, act)
primArity pname = case primNativeEntry pname of
  Just (_, ar, _) -> Just ar
  Nothing -> case ioNodeBuilder pname of
    Just (_, ar) -> Just ar
    Nothing -> Nothing

-- | Lower a general CLOSURE application in TAIL position: the head + all but the
-- final explicit argument are built EAGERLY with the ordinary @kapp@ chain (the
-- partial-closure spine), and the FINAL application is a @kbounce@ that the
-- driving @kapp@'s trampoline drains — bounding the C stack on tail recursion.
-- An implicit final argument (or no explicit argument at all) cannot bounce by
-- itself, so it falls back to a plain 'compile' of the whole spine.
compileTailApp :: BackendTerm -> Gen Text
compileTailApp term = case term of
  BApp _ f args
    | Just (prefix, lastArg) <- splitLastExplicit f args -> do
        fe <- compile prefix
        ae <- compileErasableArg lastArg
        declRuntime "declare ptr @kbounce(ptr, ptr)"
        r <- freshReg
        emit (r <> " = call ptr @kbounce(ptr " <> fe <> ", ptr " <> ae <> ")")
        pure r
  _ -> compile term
  where
    splitLastExplicit hd args =
      case reverse args of
        a : rs | argIcit a == Expl -> Just (rebuild hd (reverse rs), argTerm a)
        _ -> Nothing
    rebuild hd [] = hd
    rebuild hd xs = BApp (backendMetaOf term) hd xs

-- | A bound variable read (Milestone B): @call ptr \@kvar(ptr %env, i32 i)@,
-- where @%env@ is the current 'gsEnv' operand and @i@ is the de Bruijn /index/
-- (0 = innermost binder = top of the env chain).  This is the UNIFORM
-- environment realisation — every binder pushes exactly one env slot
-- ('compileLet'), so the index lines up with Core's de Bruijn numbering with
-- no flat-param shortcut (the C backend's @gsParamLvals@ fast path is
-- deliberately NOT replicated; it is always correct, just not the fastest).
-- The interpreter is the oracle: if a let/var program's output diverges, the
-- index threading is wrong.
compileVar :: Int -> Gen Text
compileVar i = do
  env <- gets gsEnv
  declRuntime "declare ptr @kvar(ptr, i32)"
  r <- freshReg
  emit (r <> " = call ptr @kvar(ptr " <> env <> ", i32 " <> T.pack (show i) <> ")")
  pure r

-- | A single non-recursive @let@ (Milestone B).  The 'CLet' constructor is
-- @CLet q name ty rhs body@; only @rhs@ and @body@ matter for codegen (the
-- quantity/name/type are erased here).  Lower it by compiling @rhs@ to an
-- operand, pushing it onto the env chain
-- (@%env1 = call ptr \@kpush(ptr %v, ptr %env0)@ — value first, env second,
-- matching the runtime's @kpush(KValue *v, KEnv *e)@), then compiling @body@
-- with 'gsEnv' set to the extended env so a @CVar 0@ in @body@ reads the
-- let-bound value.  The previous env operand is RESTORED afterwards (a @let@
-- in expression position must not leak its binder into a sibling expression).
compileLet :: BackendTerm -> BackendTerm -> Gen Text
compileLet rhs body = do
  rv <- compile rhs
  env0 <- gets gsEnv
  declRuntime "declare ptr @kpush(ptr, ptr)"
  env1 <- freshReg
  emit (env1 <> " = call ptr @kpush(ptr " <> rv <> ", ptr " <> env0 <> ")")
  modify' $ \g -> g {gsEnv = env1}
  bv <- compile body
  modify' $ \g -> g {gsEnv = env0}
  pure bv

-- ── Recursive local let + suspensions (Milestone J) ──────────────────

-- | A recursive local @let@ ('CLetRec' @q name ty rhs body@ — only @rhs@ and
-- @body@ matter here, and BOTH live UNDER the binder, i.e. de Bruijn index 0 in
-- each refers to the let-bound name).  Mirrors the C backend's backpatch
-- fixpoint (C.hs:2541, docs/NATIVE_BACKEND.md §5):
--
--   * push a PLACEHOLDER slot @%e2 = call ptr \@kpush(ptr <kunit()>, ptr %env0)@
--     — the binder is de Bruijn 0 in @%e2@;
--   * compile @rhs@ with 'gsEnv' := @%e2@.  For a recursive lambda the rhs is a
--     @kclo@ that CAPTURES @%e2@ but does not read the slot until applied, so a
--     self-reference inside it reads @kvar(%e2, 0)@ at RUN time — by which point
--     the slot has been backpatched to the real rhs value;
--   * backpatch @call void \@kenv_set_val(ptr %e2, ptr %re)@ — overwrite the
--     placeholder with the real rhs operand (the runtime helper added in PART 0,
--     since this backend's opaque @ptr@ cannot write @e2->val@ directly the way
--     the C backend does);
--   * compile @body@ with 'gsEnv' := @%e2@ using the supplied body-compiler
--     (@compile@ in expression position, @compileTail@ in tail position — this
--     is what threads tail-ness through so deep local recursion is stack-safe);
--   * restore 'gsEnv' to @%env0@ afterwards.
compileLetRecWith :: (BackendTerm -> Gen Text) -> BackendTerm -> BackendTerm -> Gen Text
compileLetRecWith compileBody rhs body = do
  env0 <- gets gsEnv
  declRuntime "declare ptr @kpush(ptr, ptr)"
  declRuntime "declare ptr @kunit()"
  declRuntime "declare void @kenv_set_val(ptr, ptr)"
  -- The placeholder slot: a unit value the rhs never reads before backpatch.
  ph <- freshReg
  emit (ph <> " = call ptr @kunit()")
  e2 <- freshReg
  emit (e2 <> " = call ptr @kpush(ptr " <> ph <> ", ptr " <> env0 <> ")")
  -- Compile the rhs under %e2 (it captures the binder cell but does not read it
  -- until run time); then backpatch the slot to the real rhs value.
  modify' $ \g -> g {gsEnv = e2}
  re <- compile rhs
  emit ("call void @kenv_set_val(ptr " <> e2 <> ", ptr " <> re <> ")")
  -- Compile the body under %e2 (with whatever tail-ness the caller threaded in).
  bv <- compileBody body
  modify' $ \g -> g {gsEnv = env0}
  pure bv

-- | A §19 suspension (mirrors C's 'compileSuspension', C.hs:3150): lift the
-- delayed expression @e@ into a fresh ONE-ARG thunk function and build a
-- @kthunk@ over it.  @memo@ is 0 for Delay ('CThunkE', re-evaluate each force)
-- and 1 for Memo ('CLazyE', cache on first force).
--
-- The thunk function is @KIOFn = KValue*(*)(KEnv*)@ — a ONE-ARG (env only)
-- function, NOT the two-arg @kfn@ closure shape:
--   @define internal ptr \@kthn_N(ptr %env) { <compile e with gsEnv := %env> }@.
-- The thunk captures the CURRENT env DIRECTLY (no @kpush@): @e@'s de Bruijn
-- indices read @%env@ as-is, since the suspension introduces no binder.  At the
-- use site: @call ptr \@kthunk(ptr \@kthn_N, ptr <gsEnv>, i32 <memo>)@.
compileSuspension :: Int -> BackendTerm -> Gen Text
compileSuspension memo e = do
  fnIdent <- freshLabel "kthn_"
  capturedEnv <- gets gsEnv
  declRuntime "declare ptr @kthunk(ptr, ptr, i32)"
  -- Compile @e@ in its OWN buffer with the thunk's %env as the env operand (no
  -- kpush: the delayed expression reads the captured chain unchanged).
  (bodyInsns, _endBlock, resultOp) <- captured "%env" (compile e)
  let def =
        T.unlines $
          [ "define internal ptr @" <> fnIdent <> "(ptr %env) {"
          , "build:"
          ]
            ++ map ("  " <>) bodyInsns
            ++ [ "  ret ptr " <> resultOp
               , "}"
               ]
  modify' $ \st -> st {gsTop = def : gsTop st}
  r <- freshReg
  emit
    ( r
        <> " = call ptr @kthunk(ptr @"
        <> fnIdent
        <> ", ptr "
        <> capturedEnv
        <> ", i32 "
        <> T.pack (show memo)
        <> ")"
    )
  pure r

-- | A §19 @force@ ('CForceE'): @call ptr \@kforce(ptr %v)@ where @%v@ is the
-- compiled thunk operand (mirrors C.hs:1382).  In tail position this is still a
-- value — 'compileTail' returns it.
compileForce :: BackendTerm -> Gen Text
compileForce e = do
  ve <- compile e
  declRuntime "declare ptr @kforce(ptr)"
  r <- freshReg
  emit (r <> " = call ptr @kforce(ptr " <> ve <> ")")
  pure r

-- ── Lambdas / closures (Milestone D) ─────────────────────────────────

-- | A lambda @lam x => body@ (mirrors C's 'compileLam', using the SIMPLE
-- curried model — one @kclo@ per lambda, one @kpush@ per parameter; the C
-- backend's flat-closure / worker optimisation is deliberately NOT ported).
--
-- The body is lifted into a fresh top-level
-- @define internal ptr \@kfn_N(ptr %cenv, ptr %arg)@ whose first act is
-- @%env = call ptr \@kpush(ptr %arg, ptr %cenv)@ — the parameter becomes env
-- slot 0.  The body is then compiled in TAIL position ('compileTail') with
-- 'gsEnv' := @%env@, and the result is @ret@'d.
--
-- At the USE site we emit @call ptr \@kclo(ptr \@kfn_N, ptr <gsEnv>)@, capturing
-- the WHOLE current environment (no free-variable analysis).  This is sound
-- because every binder pushes exactly one env slot: inside @kfn_N@ the chain is
-- (param :: capturedEnv), so the body's Core de Bruijn indices read correctly
-- via @kvar@ with NO renumbering — index 0 is the parameter, index i+1 is what
-- index i named in the enclosing scope.
--
-- 'captured' gives @kfn_N@ its own instruction buffer (and restores the caller's
-- buffer / env / block); the @define@ is emitted via 'gsTop'.
compileLam :: BackendTerm -> Gen Text
compileLam body = do
  fnIdent <- freshLabel "kfn_"
  capturedEnv <- gets gsEnv -- the env captured at closure-creation time
  declRuntime "declare ptr @kpush(ptr, ptr)"
  declRuntime "declare ptr @kclo(ptr, ptr)"
  -- Compile the body in its OWN buffer: the parameter is pushed onto %cenv to
  -- form %env, then the body runs in tail position over %env.
  -- The third 'captured' result (the block active when the body finished) is
  -- unused here: a lambda body ends in a straight @ret@, which is appended
  -- textually after the body's final block, so 'compileTail' has already wired
  -- any internal control flow + phis and the @ret@ just returns the operand
  -- defined in that last block.  (Contrast the accessor, where the trailing
  -- @store@/@phi@ must name the end block — hence 'emitArity0Accessor' uses it.)
  (bodyInsns, _endBlock, resultOp) <- captured "%env" $ do
    emit ("%env = call ptr @kpush(ptr %arg, ptr %cenv)")
    compileTail body
  -- The body's first block is labeled @build@ to match 'captured' (which sets
  -- @gsBlock = "build"@): a control form in the body (a @match@/@if@ taking the
  -- irrefutable fast path) reads @gsBlock@ for a phi predecessor, so the textual
  -- label and the recorded one MUST agree, or the phi names a non-existent block.
  let def =
        T.unlines $
          [ "define internal ptr @" <> fnIdent <> "(ptr %cenv, ptr %arg) {"
          , "build:"
          ]
            ++ map ("  " <>) bodyInsns
            ++ [ "  ret ptr " <> resultOp
               , "}"
               ]
  modify' $ \st -> st {gsTop = def : gsTop st}
  r <- freshReg
  emit (r <> " = call ptr @kclo(ptr @" <> fnIdent <> ", ptr " <> capturedEnv <> ")")
  pure r

-- ── Constructors (Milestone C) ───────────────────────────────────────

-- | A saturated constructor application (mirrors C's 'compileCtor').  The
-- runtime ABI is the same as the C backend uses:
--
--   * nullary    — @call ptr \@kctor0(i32 <tag>, ptr <name>)@;
--   * with fields — materialise a stack @[argc x ptr]@, store each compiled
--     field operand, then @call ptr \@kctor(i32 <tag>, ptr <name>, i32 argc,
--     ptr <fields>)@.
--
-- @<tag>@ is the literal numeric id ('ctorTagId'); @<name>@ is the ctor's gKey
-- interned as a NUL-terminated C string (the same string the C backend passes —
-- diagnostics / rep-equality only, never dispatch).  Type-level / staging
-- fields are NOT erased here (Milestone C targets value-carrying ctors); a ctor
-- with an erased field falls through to the per-argument 'compile', which
-- reports it cleanly if it is not yet lowerable.
compileCtor :: GName -> [BackendTerm] -> Gen Text
compileCtor g args = do
  tag <- ctorTagId g
  nameG <- internCStr (gKey g)
  let tagOp = T.pack (show tag)
  -- KBackendIR Stage 2: the nullary ⇒ canonical @b010@ immediate decision is
  -- 'Repr.ctorLayoutByArity' (the arity-pure slice both backends act on); a
  -- 'Repr.LayoutImmediate' ctor lowers to @kctor0@, anything else to @kctor@.
  case Repr.ctorLayoutByArity (length args) of
    Repr.LayoutImmediate -> do
      declRuntime "declare ptr @kctor0(i32, ptr)"
      r <- freshReg
      emit (r <> " = call ptr @kctor0(i32 " <> tagOp <> ", ptr " <> nameG <> ")")
      pure r
    _ -> do
      argEs <- mapM compile args
      let argc = length argEs
      arr <- freshReg
      emit (arr <> " = alloca [" <> T.pack (show argc) <> " x ptr], align 8")
      forM_ (zip [0 :: Int ..] argEs) $ \(i, ae) -> do
        slot <- freshReg
        emit (slot <> " = getelementptr inbounds [" <> T.pack (show argc)
                <> " x ptr], ptr " <> arr <> ", i64 0, i64 " <> T.pack (show i) <> "")
        emit ("store ptr " <> ae <> ", ptr " <> slot <> ", align 8")
      declRuntime "declare ptr @kctor(i32, ptr, i32, ptr)"
      r <- freshReg
      emit (r <> " = call ptr @kctor(i32 " <> tagOp <> ", ptr " <> nameG
              <> ", i32 " <> T.pack (show argc) <> ", ptr " <> arr <> ")")
      pure r

compileInject :: Text -> BackendTerm -> Gen Text
compileInject tag payload = do
  pe <- compile payload
  nameG <- internCStr tag
  declRuntime "declare ptr @kinject(i32, ptr, ptr)"
  r <- freshReg
  -- LLVM's variant pattern path uses string-tag tests and still rejects
  -- residual-row variant patterns, so the numeric tag is not observed there.
  -- Keep it deterministic and non-negative until variant tag ids become part of
  -- KBackendIR layout metadata.
  emit (r <> " = call ptr @kinject(i32 0, ptr " <> nameG <> ", ptr " <> pe <> ")")
  pure r

-- ── Records (Milestone H) ────────────────────────────────────────────

-- | The unit placeholder operand (@call ptr \@kunit()@) — used for an erased
-- type-level term that reaches value position (e.g. a 'CRecordT').
compileUnit :: Gen Text
compileUnit = do
  declRuntime "declare ptr @kunit()"
  r <- freshReg
  emit (r <> " = call ptr @kunit()")
  pure r

unitAction :: Gen Text
unitAction = do
  u <- compileUnit
  declRuntime "declare ptr @krt2_pure(ptr)"
  r <- freshReg
  emit (r <> " = call ptr @krt2_pure(ptr " <> u <> ")")
  pure r

-- | A record VALUE (mirrors C's 'compileRecord').  The fields arrive in canonical
-- lexicographic order — the SAME order the @K_REC@ runtime layout expects — so we
-- preserve it.  The runtime constructor is
--
--   @KValue *krec(int n, const char **names, KValue **vals)@
--
-- which STORES the @names@ pointer without copying (the labels are compile-time
-- literals) and COPIES @vals@ into a GC array (runtime/value.c).  So:
--
--   * the NAMES array must OUTLIVE this frame — emit it as a module-level
--     @private constant [n x ptr]@ of pointers to the interned field-name
--     C-strings (the LLVM analogue of C's @static const char*[]@).  A record
--     built in a CAF/closure and projected later would otherwise read a dangling
--     stack array.
--   * the VALS array can be a per-call @alloca@ (krec copies it immediately),
--     exactly like 'compileCtor' materialises its field array.
--
-- The argument shape matches the C backend EXACTLY: a wrong field order or a
-- missing name array breaks the name-based 'kproj' path.
compileRecord :: [(Text, BackendTerm)] -> Gen Text
compileRecord fs = do
  let n = length fs
  -- Compile each field value (in canonical order) BEFORE materialising arrays,
  -- so any instructions the fields emit land before the krec call.  A type-level
  -- field erases to @kunit()@ ('compileErasableArg'), exactly as C's
  -- 'compileRecord' does — so an erased field never reports unsupported.
  valEs <- mapM (compileErasableArg . snd) fs
  -- The names array: a module-level constant of pointers to interned C-strings.
  nameGs <- mapM (internCStr . fst) fs
  namesArr <- freshNamesGlobal nameGs
  declRuntime "declare ptr @krec(i32, ptr, ptr)"
  if n == 0
    then do
      -- An empty record: no vals array needed (krec stores NULL for n==0).
      r <- freshReg
      emit (r <> " = call ptr @krec(i32 0, ptr " <> namesArr <> ", ptr null)")
      pure r
    else do
      valsArr <- freshReg
      emit (valsArr <> " = alloca [" <> T.pack (show n) <> " x ptr], align 8")
      forM_ (zip [0 :: Int ..] valEs) $ \(i, ve) -> do
        slot <- freshReg
        emit (slot <> " = getelementptr inbounds [" <> T.pack (show n)
                <> " x ptr], ptr " <> valsArr <> ", i64 0, i64 " <> T.pack (show i) <> "")
        emit ("store ptr " <> ve <> ", ptr " <> slot <> ", align 8")
      r <- freshReg
      emit (r <> " = call ptr @krec(i32 " <> T.pack (show n) <> ", ptr " <> namesArr
              <> ", ptr " <> valsArr <> ")")
      pure r

-- | Emit a module-level @[n x ptr]@ constant holding the given interned-C-string
-- globals (the field-name pointer array @krec@ stores).  Returns its global name.
-- Lives in 'gsGlobalsExtra' (rendered alongside the @.cache@ globals) so it
-- outlives every call frame, matching C's @static const char*[]@.
freshNamesGlobal :: [Text] -> Gen Text
freshNamesGlobal nameGs = do
  k <- gets gsFresh
  modify' $ \g -> g {gsFresh = k + 1}
  let gname = "@.rnames." <> T.pack (show k)
      n = length nameGs
      elems = T.intercalate ", " ["ptr " <> ng | ng <- nameGs]
      def = gname <> " = private unnamed_addr constant [" <> T.pack (show n)
              <> " x ptr] [" <> elems <> "], align 8"
  modify' $ \g -> g {gsGlobalsExtra = def : gsGlobalsExtra g}
  pure gname

-- | A name-based projection (mirrors C's @kproj(rec, "f")@).  Compile the record
-- to an operand, intern the field name as a C-string, and call
-- @KValue *kproj(KValue *rec, const char *name)@.  This is the path used for dict
-- members (trait-method access) and open/sealed records — a strcmp scan over the
-- record's stored name array (which is exactly why 'compileRecord' must store it).
compileProj :: BackendTerm -> Text -> Gen Text
compileProj e f = do
  rec <- compile e
  nameG <- internCStr f
  declRuntime "declare ptr @kproj(ptr, ptr)"
  r <- freshReg
  emit (r <> " = call ptr @kproj(ptr " <> rec <> ", ptr " <> nameG <> ")")
  pure r

-- | A precomputed-offset projection (mirrors C's @krec_at(rec, i)@).  The index
-- @i@ is @f@'s slot in the lexicographically-sorted field list (elaboration's
-- closed-record fast path), so this reads the field at a fixed offset with no
-- name scan: @KValue *krec_at(KValue *rec, int i)@.
compileProjAt :: BackendTerm -> Int -> Gen Text
compileProjAt e i = do
  rec <- compile e
  declRuntime "declare ptr @krec_at(ptr, i32)"
  r <- freshReg
  emit (r <> " = call ptr @krec_at(ptr " <> rec <> ", i32 " <> T.pack (show i) <> ")")
  pure r

-- ── if (Milestone C) ─────────────────────────────────────────────────

-- | An @if@ expression (mirrors C's 'consumeIf', which tests @kas_bool@).  The
-- condition is compiled to a @KValue*@, coerced to an @i1@ via @kas_bool@
-- (@call i32 \@kas_bool(ptr)@ then @icmp ne i32 _, 0@), and branched on.  Each
-- arm computes its operand in its own block; the result is a @phi ptr@ at the
-- join over the two arms' PREDECESSOR blocks (read from 'gsBlock' after each arm
-- — a nested control form in an arm leaves a different block active than the
-- arm's entry, so the phi must name the block that actually reaches the join).
compileIf :: BackendTerm -> BackendTerm -> BackendTerm -> Gen Text
compileIf = compileIfWith compile

-- | 'compileIf' parameterised on how each ARM is compiled: 'compile' for an
-- expression-position @if@, 'compileTail' for a tail-position one (so a tail
-- call inside a branch lowers to @kbounce@).  The condition is always compiled
-- non-tail (it is forced to an @i1@ here), and the arm results meet at a
-- @phi ptr@ over the two arms' predecessor blocks — a @kbounce@ value flows
-- through the phi unchanged.
compileIfWith :: (BackendTerm -> Gen Text) -> BackendTerm -> BackendTerm -> BackendTerm -> Gen Text
compileIfWith arm c t e = do
  cv <- compile c
  declRuntime "declare i32 @kas_bool(ptr)"
  bi <- freshReg
  emit (bi <> " = call i32 @kas_bool(ptr " <> cv <> ")")
  cond <- freshReg
  emit (cond <> " = icmp ne i32 " <> bi <> ", 0")
  thenL <- freshLabel "if.then."
  elseL <- freshLabel "if.else."
  joinL <- freshLabel "if.join."
  emit ("br i1 " <> cond <> ", label %" <> thenL <> ", label %" <> elseL)
  -- then arm
  startBlock thenL
  tv <- arm t
  thenEnd <- gets gsBlock
  emit ("br label %" <> joinL)
  -- else arm
  startBlock elseL
  ev <- arm e
  elseEnd <- gets gsBlock
  emit ("br label %" <> joinL)
  -- join
  startBlock joinL
  r <- freshReg
  emit (r <> " = phi ptr [ " <> tv <> ", %" <> thenEnd <> " ], [ "
          <> ev <> ", %" <> elseEnd <> " ]")
  pure r

-- ── Pattern matching (Milestone C; recursive in Milestone K) ──────────

-- | A @match@ expression (mirrors C's 'consumeMatch' / 'consumeAlt' chain,
-- specialised to expression position).  The scrutinee is compiled once; each
-- alternative runs a (now RECURSIVE) pattern test that short-circuits to a
-- per-alt @fail@ block, then binds the pattern's fields ('kpush' onto 'gsEnv',
-- in pattern order) and compiles the body.  Every alt block branches to a shared
-- join whose @phi ptr@ selects the matched alt's operand.  A fall-through past
-- the last alt calls @krt_fail("non-exhaustive match")@ (mirroring the C
-- backend's @if (!matched) krt_fail(...)@), in an UNREACHABLE-then-branch block
-- that still feeds the join (with a @null@ placeholder) so the phi is
-- well-formed.
--
-- SUPPORTED pattern forms (Milestone K extends this to the C backend's full
-- structural set): bare var/wildcard catch-alls ('CPVar'/'CPWild'),
-- constructor patterns with arbitrary NESTED sub-patterns ('CPCtor', recursing
-- via @kctor_arg@), tuple patterns ('CPTuple' via @krec_at@), record patterns
-- ('CPRecord' via @kproj@, incl. a binding rest via @krec_without@), variant
-- patterns ('CPInject' via @kvariant_is@/@kvariant_payload@), as-patterns
-- ('CPAs'), literal patterns ('CPLit', @klit_eq@), and top-level or-patterns
-- ('CPOr', expanded into separate alternatives via 'expandTopOrLL').  Guards are
-- supported (an extra @kas_bool@ test inside the alt).  Still UNSUPPORTED (a
-- clean 'unsupported', never a miscompile): residual-row variant patterns
-- ('CPInjectRest'), nested binding or-patterns, and an or-pattern that binds the
-- shared names in a non-canonical order ('orReorderedLL' — refused like C).
compileMatch :: BackendTerm -> [BackendAlt] -> Gen Text
compileMatch = compileMatchWith compile

-- | 'compileMatch' parameterised on how each ALT BODY is compiled: 'compile' for
-- an expression-position @match@, 'compileTail' for a tail-position one (so a
-- tail call inside an alt body lowers to @kbounce@).  A bounce flows through the
-- join @phi@ unchanged and is drained by the caller.  The scrutinee and any
-- guard are always compiled non-tail (they are forced to values here).
compileMatchWith :: (BackendTerm -> Gen Text) -> BackendTerm -> [BackendAlt] -> Gen Text
compileMatchWith compileBody scrut alts = do
  sv <- compile scrut
  joinL <- freshLabel "match.join."
  -- §17.2.3: an or-pattern whose alternatives list the shared binders in a
  -- different ORDER than the first needs a per-alternative de-Bruijn body
  -- permutation; this backend distributes alternatives over a shared body and
  -- does not perform it, so refuse rather than miscompile (mirrors the C
  -- backend's 'consumeMatch' guard; the interpreter handles this case).
  forM_ alts $ \(BackendAlt _ pat _ _ _) ->
    when (orReorderedLL pat) $
      void $
        unsupported "pattern"
          "an or-pattern alternative that binds the shared names in a different order than the first alternative is not supported by the LLVM backend (use a consistent binder order across alternatives, or the C backend)"
  -- Milestone K: expand every top-level or-pattern into separate or-free
  -- alternatives (mirroring the C backend's 'expandTopOr'/'distributePat'), so
  -- each branch is handled by the ordinary recursive test/bind path and binds the
  -- shared variables in its own structural order — the body's de Bruijn layout
  -- stays correct because the reordered case was refused just above.
  let alts' = concatMap expandTopOrLL alts
  -- Each alt contributes one (operand, predecessor-block) pair to the phi; the
  -- non-exhaustive fallback contributes an (unreachable) @null@ incoming so the
  -- phi is always well-formed even for a match with no value-producing alt.
  incomings <- compileAlts compileBody sv joinL alts'
  startBlock joinL
  r <- freshReg
  let phiArgs = T.intercalate ", " ["[ " <> op <> ", %" <> blk <> " ]" | (op, blk) <- incomings]
  emit (r <> " = phi ptr " <> phiArgs)
  pure r

-- | Milestone K: §17.2.3 — expand one alternative whose pattern contains
-- or-patterns into the list of or-free alternatives it denotes (the Cartesian
-- product over every nested 'CPOr', left-to-right, matching the interpreter's
-- first-match order).  All branches share the alternative's guard and body.
-- Mirrors the C backend's 'expandTopOr'/'distributePat' (C.hs:2632).
expandTopOrLL :: BackendAlt -> [BackendAlt]
expandTopOrLL (BackendAlt meta pat binders g body) = [BackendAlt meta p binders g body | p <- distributePatLL pat]

-- | The or-free patterns a pattern denotes, distributing every nested 'CPOr' as
-- the Cartesian product over its positions (mirrors C's 'distributePat').
distributePatLL :: BackendPat -> [BackendPat]
distributePatLL = \case
  BPOr ps _ -> concatMap distributePatLL ps
  BPCtor g runtimeArity fields ->
    let (indices, patterns) = unzip fields
     in [BPCtor g runtimeArity (zip indices qs) | qs <- mapM distributePatLL patterns]
  BPTuple runtimeArity fields ->
    let (indices, patterns) = unzip fields
     in [BPTuple runtimeArity (zip indices qs) | qs <- mapM distributePatLL patterns]
  BPRecord fs rest ->
    let (names, pats) = unzip fs
     in [BPRecord (zip names qs) rest | qs <- mapM distributePatLL pats]
  BPInject t p -> [BPInject t q | q <- distributePatLL p]
  BPAs n p -> [BPAs n q | q <- distributePatLL p]
  p -> [p] -- BPWild / BPVar / BPLit / BPInjectRest: no nested or

-- | Whether a pattern contains an or-pattern whose alternatives bind the shared
-- names in a NON-canonical order (a non-identity permutation on some
-- alternative) — these need a per-alternative de Bruijn permutation the shared-
-- body distribution can't express.  Mirrors C's 'orReordered' (C.hs:2617).
orReorderedLL :: BackendPat -> Bool
orReorderedLL = \case
  BPOr ps perms -> any (\pm -> pm /= [0 .. length pm - 1]) perms || any orReorderedLL ps
  BPCtor _ _ fields -> any (orReorderedLL . snd) fields
  BPTuple _ fields -> any (orReorderedLL . snd) fields
  BPRecord fs _ -> any (orReorderedLL . snd) fs
  BPInject _ p -> orReorderedLL p
  BPAs _ p -> orReorderedLL p
  _ -> False

-- | Lower the alternatives of a 'compileMatch' as a test/branch chain.  The
-- chain is linearised so each alt's FAILURE path opens the next alt's block
-- inline (no dangling fall-through): 'compileAlt' is given an @onFail@ action
-- that emits the continuation INTO the current (already-open, unterminated)
-- block.  Returns the @(operand, predecessor-block)@ incomings for the join phi
-- — one per alt that reaches the join, plus the non-exhaustive fallback's
-- (unreachable) @null@ incoming.
compileAlts :: (BackendTerm -> Gen Text) -> Text -> Text -> [BackendAlt] -> Gen [(Text, Text)]
compileAlts compileBody sv joinL = go
  where
    go [] = do
      -- No alt matched: abort like the C backend's krt_fail, then feed the join
      -- a placeholder so the phi stays well-formed (this edge is unreachable).
      declRuntime "declare void @krt_fail(ptr)"
      cur <- gets gsCur
      msg <- internCStr ("non-exhaustive match in " <> gKey cur)
      emit ("call void @krt_fail(ptr " <> msg <> ")")
      blk <- gets gsBlock
      emit ("br label %" <> joinL)
      pure [("null", blk)]
    go (alt : rest) = compileAlt compileBody sv joinL alt (go rest)

-- | Lower one alternative.  @onFail@ emits the failure continuation (the next
-- alt, or the non-exhaustive fallback) and returns ITS join incomings; the
-- caller guarantees the block current when @onFail@ runs is open and
-- unterminated.  Structure: an optional pattern-tag test branches to a fresh
-- @fail@ block (where @onFail@ runs) or the @ok@ block; in @ok@ the fields are
-- bound, an optional guard is checked (a failing guard ALSO routes to a fail
-- block running @onFail@), the body is compiled, and control branches to the
-- join.  'gsEnv' is restored after binding so a sibling alt never inherits the
-- binders.  Returns this alt's incomings ++ @onFail@'s.
compileAlt :: (BackendTerm -> Gen Text) -> Text -> Text -> BackendAlt -> Gen [(Text, Text)] -> Gen [(Text, Text)]
compileAlt compileBody sv joinL (BackendAlt _ pat _ mguard body) onFail = do
  -- A pattern that contributes no test (a bare var/wildcard, or an as-pattern /
  -- nested shape over only those) with no guard is the unconditional catch-all:
  -- bind and run the body directly (the C backend's first-match order makes any
  -- later alt dead), with NO failure block — nothing can route there.
  case (patAlwaysMatches pat, mguard) of
    (True, Nothing) -> do
      inc <- bindAndBody compileBody sv joinL pat body
      pure [inc]
    _ -> do
      -- Otherwise at least one failable test (a tag/shape/literal check) or a
      -- guard exists; give the failure path a block so 'onFail' has somewhere to
      -- emit, and thread it through the RECURSIVE pattern test so a nested
      -- sub-pattern that fails short-circuits to the SAME continuation (and never
      -- projects deeper — the field accessors abort on a shape mismatch, so the
      -- C backend's `&&` short-circuit MUST be reproduced with control flow).
      failL <- freshLabel "alt.fail."
      patTestBranch sv pat failL
      -- The current block is now "all of the pattern's tests passed": bind, check
      -- the optional guard, run the body.  Binding re-projects the (now shape-
      -- confirmed) fields — safe, since the test established every accessor's
      -- precondition.
      env0 <- gets gsEnv
      env' <- bindPat sv pat
      modify' $ \g -> g {gsEnv = env'}
      okIncs <- case mguard of
        Nothing -> do
          inc <- bodyToJoin compileBody joinL body
          pure [inc]
        Just gd -> do
          gv <- compile gd
          declRuntime "declare i32 @kas_bool(ptr)"
          gb <- freshReg
          emit (gb <> " = call i32 @kas_bool(ptr " <> gv <> ")")
          gcond <- freshReg
          emit (gcond <> " = icmp ne i32 " <> gb <> ", 0")
          passL <- freshLabel "guard.ok."
          gfailL <- freshLabel "guard.no."
          emit ("br i1 " <> gcond <> ", label %" <> passL <> ", label %" <> gfailL)
          startBlock passL
          inc <- bodyToJoin compileBody joinL body
          -- A failing guard falls through to the SAME failure continuation as a
          -- failing pattern test: branch to the shared failL.
          startBlock gfailL
          emit ("br label %" <> failL)
          pure [inc]
      modify' $ \g -> g {gsEnv = env0}
      -- failure: open the fail block and run the continuation there.
      startBlock failL
      failIncs <- onFail
      pure (okIncs ++ failIncs)

-- | Bind the pattern's fields, compile the body, and branch to the join,
-- restoring 'gsEnv' afterwards.  Returns the body's @(operand, pred-block)@.
bindAndBody :: (BackendTerm -> Gen Text) -> Text -> Text -> BackendPat -> BackendTerm -> Gen (Text, Text)
bindAndBody compileBody sv joinL pat body = do
  env0 <- gets gsEnv
  env' <- bindPat sv pat
  modify' $ \g -> g {gsEnv = env'}
  inc <- bodyToJoin compileBody joinL body
  modify' $ \g -> g {gsEnv = env0}
  pure inc

-- | Compile @body@ (with the supplied body compiler — 'compile' or
-- 'compileTail') in the current (env-extended) block, branch to the join, and
-- report the body's @(operand, predecessor-block)@ for the join phi.  The
-- predecessor is read AFTER compiling the body (a nested match/if leaves a
-- different block active than the body's entry; a tail body's @kbounce@ value
-- is the operand and flows through the phi).
bodyToJoin :: (BackendTerm -> Gen Text) -> Text -> BackendTerm -> Gen (Text, Text)
bodyToJoin compileBody joinL body = do
  bv <- compileBody body
  bvBlk <- gets gsBlock
  emit ("br label %" <> joinL)
  pure (bv, bvBlk)

-- | Milestone K: does @pat@ contribute NO runtime test at all — i.e. it matches
-- every value of its (statically known) type?  True for a bare variable /
-- wildcard, an as-pattern or nested shape over only those, a tuple/record whose
-- every field is irrefutable, and a single-member variant-inject over an
-- irrefutable payload (the variant's row is statically a singleton at that
-- position, so no tag test is needed — same as the C backend's @patTest@
-- returning 'Nothing').  A 'CPCtor', 'CPLit', or 'CPInjectRest' is always
-- refutable (it dispatches on a tag / equality).  Mirrors which 'CorePat' forms
-- C's 'patTest' answers 'Nothing' for.
patAlwaysMatches :: BackendPat -> Bool
patAlwaysMatches = \case
  BPWild -> True
  BPVar _ -> True
  BPAs _ p -> patAlwaysMatches p
  BPTuple _ fields -> all (patAlwaysMatches . snd) fields
  BPRecord fs _ -> all (patAlwaysMatches . snd) fs
  -- A CPInject test exists in the C backend (kvariant_tagid dispatch), so an
  -- inject is refutable; keep parity by treating it as a test.
  _ -> False

-- | Milestone K: emit the RECURSIVE pattern test for @pat@ against scrutinee
-- operand @v@, branching to @failL@ on ANY mismatch and FALLING THROUGH (into a
-- fresh open block) when every sub-test passes.  This mirrors the C backend's
-- 'patTest' but threads the short-circuit through CONTROL FLOW rather than a
-- pure @&&@ expression — load-bearing, because the field accessors
-- (@kctor_arg@/@krec_at@/@kvariant_payload@) ABORT (@krt_fail@) on a shape
-- mismatch, so a nested sub-pattern must NOT be projected until its parent's
-- tag/shape has been confirmed.  Each refutable check (tag, size, literal,
-- variant tag) emits @br i1 cond, label %next, label %failL@ and continues in
-- @next@; an irrefutable sub-pattern emits nothing.  After the call the current
-- block is the "all tests passed" block.
--
--   * 'CPWild' / 'CPVar' -> no test.
--   * 'CPAs' n p -> test p (the as-name binds the whole value, no test).
--   * 'CPLit' l -> @klit_eq(v, lit)@.
--   * 'CPCtor' g ps -> @kctor_tagid(v) == tag(g)@, then recurse into each field
--     i at @kctor_arg(v, kctor_argc(v) - nps + i)@ (the C M-C offset).
--   * 'CPTuple' ps -> @krec_size(v) == n@, then recurse into @krec_at(v, i)@.
--   * 'CPRecord' fs _ -> recurse into @kproj(v, f)@ for each named field (the
--     rest binder always matches, so it adds no test — like C's 'patTest').
--   * 'CPInject' t p -> @kvariant_is(v, "t")@ (the runtime's string-tag test —
--     self-contained, unlike the numeric @kvariant_tagid@ enum the C backend
--     uses, which has no LLVM counterpart since this backend never BUILDS
--     variants), then recurse into @kvariant_payload(v)@.
--   * 'CPInjectRest' / 'CPOr' -> a clean 'unsupported' (see notes below); emit a
--     constant-false branch so the IR stays well-formed.
patTestBranch :: Text -> BackendPat -> Text -> Gen ()
patTestBranch v pat failL = case pat of
  BPWild -> pure ()
  BPVar _ -> pure ()
  BPAs _ p -> patTestBranch v p failL
  -- Milestone F: a literal pattern — value-equality against the scrutinee via
  -- the SAME runtime call the C backend uses (@klit_eq(v, lit)@, an @int@ truthy
  -- result).  A literal binds no fields ('patBindingsLL' returns @[]@), so this
  -- is purely a test.  An unsupported literal records an error and never matches.
  BPLit l -> do
    mlv <- litValueLL l
    case mlv of
      Nothing -> branchFalse -- unsupported literal: error already recorded
      Just lv -> do
        declRuntime "declare i32 @klit_eq(ptr, ptr)"
        eqi <- freshReg
        emit (eqi <> " = call i32 @klit_eq(ptr " <> v <> ", ptr " <> lv <> ")")
        cond <- freshReg
        emit (cond <> " = icmp ne i32 " <> eqi <> ", 0")
        branchOn cond
  BPCtor g _ fields -> do
    if
      | g == Builtins.prelNatZero -> do
          requireNatural v
          cmp <- compareNaturalWithZero v
          cond <- freshReg
          emit (cond <> " = icmp eq i32 " <> cmp <> ", 0")
          branchOn cond
      | g == Builtins.prelNatSucc -> do
          requireNatural v
          cmp <- compareNaturalWithZero v
          cond <- freshReg
          emit (cond <> " = icmp sgt i32 " <> cmp <> ", 0")
          branchOn cond
          forM_ fields $ \(_, p) -> do
            predecessor <- natPredecessorLL v
            patTestBranch predecessor p failL
      | otherwise -> do
          tag <- ctorTagId g
          declRuntime "declare i32 @kctor_tagid(ptr)"
          ti <- freshReg
          emit (ti <> " = call i32 @kctor_tagid(ptr " <> v <> ")")
          cond <- freshReg
          emit (cond <> " = icmp eq i32 " <> ti <> ", " <> T.pack (show tag))
          branchOn cond
          -- Tag confirmed: recurse left-to-right through the physical runtime
          -- indices recorded by KBackendIR after erasure and hidden-field lowering.
          forM_ fields $ \(index, p) -> do
            av <- ctorArgAtLL v index
            patTestBranch av p failL
  BPTuple runtimeArity fields -> do
    -- A tuple IS a record (K_REC); the arity is fixed, but the C backend still
    -- guards on @krec_size@, so mirror that, then recurse into @krec_at(v, i)@.
    declRuntime "declare i32 @krec_size(ptr)"
    sz <- freshReg
    emit (sz <> " = call i32 @krec_size(ptr " <> v <> ")")
    cond <- freshReg
    emit (cond <> " = icmp eq i32 " <> sz <> ", " <> T.pack (show runtimeArity))
    branchOn cond
    forM_ fields $ \(index, p) -> do
      av <- recAtLL v index
      patTestBranch av p failL
  -- §17.2.5: a record pattern's rest binder always matches; the named fields
  -- determine the test.  Recurse into each @kproj(v, f)@.
  BPRecord pfs _ ->
    forM_ pfs $ \(f, p) -> do
      av <- projNameLL v f
      patTestBranch av p failL
  -- §13 variant pattern: tag test via the runtime's string-tag predicate, then
  -- recurse into the payload.
  BPInject tag p -> do
    nameG <- internCStr tag
    declRuntime "declare i32 @kvariant_is(ptr, ptr)"
    isv <- freshReg
    emit (isv <> " = call i32 @kvariant_is(ptr " <> v <> ", ptr " <> nameG <> ")")
    cond <- freshReg
    emit (cond <> " = icmp ne i32 " <> isv <> ", 0")
    branchOn cond
    av <- variantPayloadLL v
    patTestBranch av p failL
  -- Deferred forms: record a clean unsupported and emit a never-taken branch so
  -- the surrounding IR is still well-formed.
  BPInjectRest _ -> do
    _ <- unsupported "pattern"
      "the LLVM backend does not lower residual-row variant patterns (CPInjectRest); use the C backend"
    branchFalse
  BPOr _ _ -> do
    -- Top-level or-patterns are expanded into separate alternatives before
    -- codegen ('expandTopOrLL' / 'distributePatLL'), so any CPOr reaching here is
    -- nested — which would need decision-tree compilation.  Deferred.
    _ <- unsupported "pattern"
      "the LLVM backend does not lower nested or-patterns (CPOr); lift them to top-level alternatives or use the C backend"
    branchFalse
  where
    -- Continue iff @cond@ holds, else jump to the shared failure continuation.
    branchOn cond = do
      okL <- freshLabel "pat.ok."
      emit ("br i1 " <> cond <> ", label %" <> okL <> ", label %" <> failL)
      startBlock okL
    -- A never-matching pattern: unconditionally route to failL, then open a dead
    -- block for the (unreachable) fall-through so subsequent emits stay legal.
    branchFalse = do
      deadL <- freshLabel "pat.dead."
      emit ("br label %" <> failL)
      startBlock deadL
    requireNatural operand = do
      declRuntime "declare i32 @kis_int_any(ptr)"
      isInteger <- freshReg
      emit (isInteger <> " = call i32 @kis_int_any(ptr " <> operand <> ")")
      cond <- freshReg
      emit (cond <> " = icmp ne i32 " <> isInteger <> ", 0")
      branchOn cond
    compareNaturalWithZero operand = do
      zero <- litValueLL (LitInt 0)
      case zero of
        Nothing -> pure "1"
        Just zeroOperand -> do
          declRuntime "declare i32 @kint_cmp(ptr, ptr)"
          comparison <- freshReg
          emit (comparison <> " = call i32 @kint_cmp(ptr " <> operand <> ", ptr " <> zeroOperand <> ")")
          pure comparison

-- | A pattern whose fields 'bindPatDo' can push as a single env slot without a
-- shape test: a variable, a wildcard, or an as-pattern over one of those.  Used
-- only by the do-kernel's irrefutable binder fast path.
isVarLike :: BackendPat -> Bool
isVarLike = \case
  BPVar _ -> True
  BPWild -> True
  BPAs _ p -> isVarLike p
  _ -> False

-- | Bind a pattern's variables by pushing each projected field onto the env
-- chain ('kpush'), in the SAME left-to-right order the C backend's
-- 'patBindings' uses (so the rightmost binder lands at de Bruijn index 0 and the
-- body's indices line up).  Returns the extended env operand.  Mirrors C's
-- 'bindPatScrut' (boxed path) restricted to the Milestone-C pattern subset.
bindPat :: Text -> BackendPat -> Gen Text
bindPat sv pat = do
  env0 <- gets gsEnv
  vals <- patBindingsLL sv pat
  foldM push env0 vals
  where
    push e valOp = do
      declRuntime "declare ptr @kpush(ptr, ptr)"
      n <- freshReg
      emit (n <> " = call ptr @kpush(ptr " <> valOp <> ", ptr " <> e <> ")")
      pure n

-- | Milestone K: the field operands a pattern binds, as compiled SSA operands,
-- in matchPat's left-to-right binding order — RECURSIVELY, mirroring the C
-- backend's 'patBindings' (C.hs ~2792) so the binder ORDER (and thus the body's
-- de Bruijn indices) agrees exactly.  The order MUST match 'patBinders'
-- (C.hs:875): the rightmost binder lands at de Bruijn index 0 once 'bindPat'
-- @kpush@es them left-to-right.
--
--   * 'CPVar' -> @[v]@.            'CPWild' -> @[]@.
--   * 'CPAs' n p -> @v : go p@     (the as-name FIRST, then the inner — C's
--                                   @v : go v p@, matching @patBinders = 1 +
--                                   inner@).
--   * 'CPCtor' g ps -> concat the fields left-to-right, each at
--     @kctor_arg(v, kctor_argc(v) - nps + i)@ (the C M-C offset, 'ctorArgExpr').
--   * 'CPTuple' ps -> concat the fields left-to-right at @krec_at(v, i)@.
--   * 'CPRecord' fs mr -> the named-field bindings left-to-right, then (only for
--     a non-discard rest binder) the residual record — matchPat's order.  The
--     rest binder is deferred ('krec_without' is not emitted here); a record
--     pattern WITH a binding rest is reported unsupported in 'patTestBranch'
--     (its test path) — but a discard / absent rest binds cleanly.
--   * 'CPInject' t p -> the payload's bindings at @kvariant_payload(v)@.
patBindingsLL :: Text -> BackendPat -> Gen [Text]
patBindingsLL = go
  where
    go v = \case
      BPWild -> pure []
      BPLit _ -> pure []
      BPVar _ -> pure [v]
      BPAs _ p -> do rest <- go v p; pure (v : rest)
      BPCtor g _ fields
        | g == Builtins.prelNatZero -> pure []
        | g == Builtins.prelNatSucc ->
            concat <$> mapM (\(_, p) -> natPredecessorLL v >>= \av -> go av p) fields
        | otherwise ->
            concat <$> mapM (\(index, p) -> ctorArgAtLL v index >>= \av -> go av p) fields
      BPTuple _ fields ->
        concat <$> mapM (\(index, p) -> recAtLL v index >>= \av -> go av p) fields
      BPRecord pfs mrest -> do
        named <- concat <$> mapM (\(f, p) -> projNameLL v f >>= \av -> go av p) pfs
        case mrest of
          Just nm | not (T.null nm) -> do
            rv <- recWithoutLL v (map fst pfs)
            pure (named ++ [rv])
          _ -> pure named
      BPInject _ p -> variantPayloadLL v >>= \pl -> go pl p
      BPInjectRest _ -> pure [v]
      BPOr _ _ -> pure [] -- only non-binding ors could reach here; deferred anyway

-- | @kctor_arg(v, kctor_argc(v) - nps + i)@ as SSA: read the field count,
-- compute the absolute index, then the field.  Matches C's 'ctorArgExpr' — the
-- M-C offset that drops the leading (non-bound) constructor arguments.
ctorArgAtLL :: Text -> Int -> Gen Text
ctorArgAtLL v index = do
  declRuntime "declare ptr @kctor_arg(ptr, i32)"
  r <- freshReg
  emit (r <> " = call ptr @kctor_arg(ptr " <> v <> ", i32 " <> T.pack (show index) <> ")")
  pure r

natPredecessorLL :: Text -> Gen Text
natPredecessorLL value = do
  one <- litValueLL (LitInt 1)
  case one of
    Nothing -> pure "null"
    Just oneOperand -> do
      declRuntime "declare ptr @kp_subInt(ptr, ptr)"
      result <- freshReg
      emit (result <> " = call ptr @kp_subInt(ptr " <> value <> ", ptr " <> oneOperand <> ")")
      pure result

-- | @krec_at(v, i)@ as SSA — a tuple's i-th positional field (mirrors C's
-- 'recAtExpr').
recAtLL :: Text -> Int -> Gen Text
recAtLL v i = do
  declRuntime "declare ptr @krec_at(ptr, i32)"
  r <- freshReg
  emit (r <> " = call ptr @krec_at(ptr " <> v <> ", i32 " <> T.pack (show i) <> ")")
  pure r

-- | @kproj(v, "f")@ as SSA — a record's named field (mirrors C's @kproj@).
projNameLL :: Text -> Text -> Gen Text
projNameLL v f = do
  nameG <- internCStr f
  declRuntime "declare ptr @kproj(ptr, ptr)"
  r <- freshReg
  emit (r <> " = call ptr @kproj(ptr " <> v <> ", ptr " <> nameG <> ")")
  pure r

-- | @kvariant_payload(v)@ as SSA — a variant's carried value (mirrors C).
variantPayloadLL :: Text -> Gen Text
variantPayloadLL v = do
  declRuntime "declare ptr @kvariant_payload(ptr)"
  r <- freshReg
  emit (r <> " = call ptr @kvariant_payload(ptr " <> v <> ")")
  pure r

-- | @krec_without(v, n, names)@ as SSA — the §17.2.5 record rest binder: the
-- record minus the named fields, passing the excluded names as a constant @ptr@
-- array (mirrors C's 'recWithoutExpr').
recWithoutLL :: Text -> [Text] -> Gen Text
recWithoutLL v names = do
  declRuntime "declare ptr @krec_without(ptr, i32, ptr)"
  arr <-
    if null names
      then pure "null"
      else freshNamesGlobal =<< mapM internCStr names
  r <- freshReg
  emit (r <> " = call ptr @krec_without(ptr " <> v <> ", i32 " <> T.pack (show (length names)) <> ", ptr " <> arr <> ")")
  pure r

-- ── do-kernel (Milestone E) ──────────────────────────────────────────
--
-- A do-block follows the C backend's semantic split. If §3.3 says the block may
-- suspend, or if it contains `using` (mask/restore/finalizer nodes), it lowers to
-- a @krt2_*@ ACTION TREE — the CPS path the kappart2 CK-machine
-- ('krt2_run_main') drives. Otherwise the same action-building body is placed
-- behind @kio(fn, env)@ by 'compileDoLegacyLL', preserving IO value suspension:
-- pure lets inside a do-block value run when the action executes, not when the
-- action is constructed as a CAF/fork argument. The do thunk returns a
-- @K_IOTAIL@ marker around the block's action tree, matching the C backend's
-- legacy trampoline rather than recursively forcing the tree inside the thunk.
-- The whole block still compiles to a single 'KValue*' action operand.
--
-- Stack safety (the load-bearing invariant): every non-final item becomes a
-- @krt2_bind(action, kclo(@kdo_N, env))@ where @kdo_N@ is a lifted continuation
-- closure whose body — the REST of the block — is compiled INSIDE @kdo_N@, not
-- inline.  So building the tree never recurses through @rest@ on the C stack at
-- build time, and at run time the CK-machine pops one bind frame per step (the
-- spine stays bounded even for IO-recursive blocks).  This is exactly the M-D
-- 'compileLam' machinery: a one-argument @kfn@-style function captured by @kclo@
-- over the WHOLE current env (no free-var analysis — every binder is one env
-- slot, so the continuation's de Bruijn indices line up after the delivered
-- value is pushed at index 0).
--
-- SUPPORTED items: 'KBind', 'KExpr', 'KLet', mutable 'KVarItem'/'KAssign',
-- unlabeled else-less 'KWhile' with unlabeled 'KBreak'/'KContinue', 'KReturn',
-- unlabeled 'KDefer', statement 'KIf', statement 'KSubDo', and 'KUsing'.
-- A binder with a structured
-- pattern is lowered through the same environment/pattern machinery as the
-- match path. Still-deferred items fail the whole block closed via
-- @E_BACKEND_UNSUPPORTED@ rather than partially lowering.
compileDo :: Maybe Text -> [BackendItem] -> Gen Text
compileDo _lbl items
  -- The optional scope label is only observable through §18.7 defers / labeled
  -- abrupt control, all of which are deferred below; for the linear subset it
  -- has no runtime effect, so it is ignored here (parity with the C CPS path,
  -- which threads it only through 'krt2_doscope').
  | Just bad <- firstUnsupportedItem items = unsupportedDoItem bad
  | otherwise = do
      susp <- gets gsSuspenders
      mScalar <- scalarLoopPlanLL items
      -- `cpsEligible` is shared with the C backend and counts both named
      -- suspenders and local-headed restore-like actions. `using` builds
      -- mask/restore/finalizer nodes even when its acquire action itself cannot
      -- suspend, so it is also kept on the CK-machine path.
      if isJust mScalar || backendCpsEligibleLL susp items || blockUsesUsingLL items
        then maybe (cpsItemsLL items) emitScalarLoopLL mScalar >>= wrapDoActionLL items
        else compileDoLegacyLL items

backendSpineHeadSuspendsLL :: Set GName -> BackendTerm -> Bool
backendSpineHeadSuspendsLL susp t = case fst (backendSpineOf t) of
  BGlob _ g -> isSuspendingPrimLL g || g `Set.member` susp
  _ -> False
  where
    isSuspendingPrimLL (GName m nm) =
      (m == primModule || m == ModuleName ["std", "prelude"]) && nm `Set.member` suspendingNamesLL
    suspendingNamesLL =
      Set.fromList
        [ "fork", "forkDaemon", "await", "awaitPromise"
        , "__forkRun", "__forkDaemon", "__awaitFiber"
        , "cede", "nowMonotonic", "__nowNanos", "sleepFor", "sleepUntil", "__sleepForNanos"
        , "newPromise", "completePromise", "awaitPromiseExit"
        , "__race", "__timeout", "withScope", "__interruptWait", "__interruptNoWait"
        , "blocking", "uninterruptible", "__mask", "poll"
        , "newScope", "forkIn", "shutdownScope", "monitor", "awaitMonitor"
        , "atomically", "stmBind"
        , "onExit", "onInterrupt", "finallyIO", "catchIO"
        , "newFiberRef", "getFiberRef", "setFiberRef", "modifyFiberRef", "locallyFiberRef"
        , "pollPromise", "isDonePromise"
        , "currentFiberId", "fiberId", "__currentFiberId", "__fiberId"
        ]

backendSpineHeadIsLocalLL :: BackendTerm -> Bool
backendSpineHeadIsLocalLL t = case fst (backendSpineOf t) of
  BVar {} -> True
  _ -> False

backendBlockSuspendsWithLL :: Bool -> Set GName -> [BackendItem] -> Bool
backendBlockSuspendsWithLL incLocal susp = any itemSuspends
  where
    s = \case
      BDo _ _ items -> backendBlockSuspendsWithLL incLocal susp items
      t -> backendSpineHeadSuspendsLL susp t || (incLocal && backendSpineHeadIsLocalLL t)
    condSuspends (BKCondPure _) = False
    condSuspends (BKCondAction t) = s t
    recur = backendBlockSuspendsWithLL incLocal susp
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

backendCpsEligibleLL :: Set GName -> [BackendItem] -> Bool
backendCpsEligibleLL susp items =
  all simpleLinear items && (backendBlockSuspendsWithLL True susp items || any needsRuntimeFinalizers items)
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

blockUsesUsingLL :: [BackendItem] -> Bool
blockUsesUsingLL = any go
  where
    go = \case
      BKUsing {} -> True
      BKWhile _ _ _ body me -> blockUsesUsingLL body || maybe False blockUsesUsingLL me
      BKIf _ alts me -> any (blockUsesUsingLL . snd) alts || maybe False blockUsesUsingLL me
      BKSubDo _ _ body -> blockUsesUsingLL body
      _ -> False

wrapReturnScopeLL :: [BackendItem] -> Text -> Gen Text
wrapReturnScopeLL items actionOp
  | itemsReturnLL items = do
      declRuntime "declare ptr @krt2_retscope(ptr)"
      r <- freshReg
      emit (r <> " = call ptr @krt2_retscope(ptr " <> actionOp <> ")")
      pure r
  | otherwise = pure actionOp

wrapDoActionLL :: [BackendItem] -> Text -> Gen Text
wrapDoActionLL items actionOp = do
  returned <- wrapReturnScopeLL items actionOp
  if any directDefersLL items
    then wrapDoScopeLL returned
    else pure returned

wrapDoScopeLL :: Text -> Gen Text
wrapDoScopeLL actionOp = do
  declRuntime "declare ptr @krt2_doscope(ptr)"
  r <- freshReg
  emit (r <> " = call ptr @krt2_doscope(ptr " <> actionOp <> ")")
  pure r

compileDoLegacyLL :: [BackendItem] -> Gen Text
compileDoLegacyLL items = do
      fnIdent <- freshLabel "kdo_"
      capturedEnv <- gets gsEnv
      (bodyInsns, _endBlock, scopedOp) <- captured "%env" (cpsItemsLL items >>= wrapDoActionLL items)
      declRuntime "declare ptr @kio_tail(ptr)"
      let def =
            T.unlines $
              [ "define internal ptr @" <> fnIdent <> "(ptr %env) {"
              , "build:"
              ]
                ++ map ("  " <>) bodyInsns
                ++ [ "  %tail = call ptr @kio_tail(ptr " <> scopedOp <> ")"
                   , "  ret ptr %tail"
                   , "}"
                   ]
      modify' $ \st -> st {gsTop = def : gsTop st}
      declRuntime "declare ptr @kio(ptr, ptr)"
      r <- freshReg
      emit (r <> " = call ptr @kio(ptr @" <> fnIdent <> ", ptr " <> capturedEnv <> ")")
      pure r

deferActionTreeLL :: Text -> Gen Text -> Gen Text
deferActionTreeLL label buildAction = do
  fnIdent <- freshLabel label
  capturedEnv <- gets gsEnv
  (bodyInsns, _endBlock, actionOp) <- captured "%cenv" buildAction
  let def =
        T.unlines $
          [ "define internal ptr @" <> fnIdent <> "(ptr %cenv, ptr %arg) {"
          , "build:"
          , "  ; %arg intentionally ignored: this thunk delays action-tree construction"
          ]
            ++ map ("  " <>) bodyInsns
            ++ [ "  ret ptr " <> actionOp
               , "}"
               ]
  modify' $ \st -> st {gsTop = def : gsTop st}
  declRuntime "declare ptr @kunit()"
  declRuntime "declare ptr @krt2_pure(ptr)"
  declRuntime "declare ptr @kclo(ptr, ptr)"
  declRuntime "declare ptr @krt2_bind(ptr, ptr)"
  unit <- freshReg
  emit (unit <> " = call ptr @kunit()")
  seed <- freshReg
  emit (seed <> " = call ptr @krt2_pure(ptr " <> unit <> ")")
  clo <- freshReg
  emit (clo <> " = call ptr @kclo(ptr @" <> fnIdent <> ", ptr " <> capturedEnv <> ")")
  r <- freshReg
  emit (r <> " = call ptr @krt2_bind(ptr " <> seed <> ", ptr " <> clo <> ")")
  pure r

itemsReturnLL :: [BackendItem] -> Bool
itemsReturnLL = any go
  where
    go = \case
      BKReturn _ _ -> True
      BKWhile _ _ _ body me -> itemsReturnLL body || maybe False itemsReturnLL me
      BKIf _ alts me -> any (itemsReturnLL . snd) alts || maybe False itemsReturnLL me
      BKSubDo _ _ body -> itemsReturnLL body
      _ -> False

directDefersLL :: BackendItem -> Bool
directDefersLL BKDefer {} = True
directDefersLL _ = False

-- | The first do-item outside the supported subset, if any — used to fail the
-- WHOLE block closed before emitting a partial tree. The supported set includes
-- linear bind/let/action items, statement @if@, mutable cells, unlabeled
-- else-less @while@ with unlabeled @break@/@continue@, @return@, statement
-- sub-do, unlabeled @defer@, and @using@. A labeled loop / @break@ /
-- @continue@, a @while@-@else@, 'KFor', labeled 'KDefer', and 'KLetQ' remain
-- deferred (they fail closed).
firstUnsupportedItem :: [BackendItem] -> Maybe BackendItem
firstUnsupportedItem = go
  where
    go [] = Nothing
    go (it : rest) = case it of
      BKBind {} -> go rest
      BKExpr {} -> go rest
      BKLet {} -> go rest
      BKVarItem {} -> go rest
      BKAssign {} -> go rest
      BKReturn {} -> go rest
      BKBreak _ Nothing -> go rest
      BKContinue _ Nothing -> go rest
      BKDefer _ Nothing _ -> go rest
      -- §18.8 while: only the UNLABELED, else-less form is lowered, and its body
      -- must be entirely supported too — recurse into it so a deferred item nested
      -- in the loop is caught here rather than mis-lowered.  (A labeled loop or a
      -- while-else hits the catch-all below and fails the block closed.)  The
      -- condition itself is lowered by 'compileMonadicCond'.
      BKWhile _ Nothing _cond body Nothing ->
        case go body of
          Just bad -> Just bad
          Nothing -> go rest
      BKIf _ alts mels ->
        case msum (map (go . snd) alts) `mplus` (mels >>= go) of
          Just bad -> Just bad
          Nothing -> go rest
      -- Milestone M: a statement-position sub-do is supported — recurse into its
      -- items so a genuinely-unsupported inner item still fails the block closed.
      -- The label is ignored (a labeled sub-scope's break@L/continue@L would show
      -- up as a labeled KBreak/KContinue nested here and be rejected by 'go').
      BKSubDo _ _lbl subItems ->
        case go subItems of
          Just bad -> Just bad
          Nothing -> go rest
      -- §19.5 `using pat <- acquire`: lowered through krt2_acquire_release (the
      -- bracketM machinery), with the rest of the block as the `use` body — so
      -- the rest must itself be entirely supported (recurse, like KSubDo/KIf).
      BKUsing {} ->
        go rest
      _ -> Just it

-- | Report a do-item this backend cannot yet lower. Still deferred: a LABELED
-- loop / break / continue, a @while@-@else@, 'KFor', labeled 'KDefer', and 'KLetQ' —
-- each fails the block closed.
unsupportedDoItem :: BackendItem -> Gen Text
unsupportedDoItem it =
  unsupported "do-kernel"
    ( "the LLVM backend does not yet lower this do-kernel item (use the C "
        <> "backend): "
        <> doItemKind it
    )

-- | A short label for an unsupported do-item, for the diagnostic.
doItemKind :: BackendItem -> Text
doItemKind = \case
  BKLetQ {} -> "let? (fallible binding)"
  BKVarItem {} -> "var (mutable cell)"
  BKAssign {} -> "assignment"
  BKReturn {} -> "return"
  BKBreak _ (Just l) -> "labeled break@" <> l
  BKBreak _ Nothing -> "break"
  BKContinue _ (Just l) -> "labeled continue@" <> l
  BKContinue _ Nothing -> "continue"
  BKWhile _ (Just l) _ _ _ -> "labeled while loop (@" <> l <> ")"
  BKWhile _ _ _ _ (Just _) -> "while loop with an else block"
  BKWhile {} -> "while loop"
  BKFor {} -> "for loop"
  BKIf {} -> "do-if"
  BKDefer {} -> "defer"
  BKUsing {} -> "using"
  BKSubDo {} -> "statement-position sub-do"
  _ -> "this construct"

-- | Lower a linear do-block to its @krt2_*@ action tree (mirrors C's 'cpsItems',
-- C.hs:3006).  An empty block is @krt2_pure(kunit())@; the FINAL item is the
-- block's action (compiled directly, in tail-ish position — its own value); a
-- non-final bind/action/let becomes a @krt2_bind@ over a lazily-compiled
-- continuation closure, so pure RHS work observes source order with defers,
-- interrupts, and scalar safepoints.
cpsItemsLL :: [BackendItem] -> Gen Text
cpsItemsLL items = do
  mplan <- scalarLoopPlanLL items
  case mplan of
    Just plan -> emitScalarLoopLL plan
    Nothing -> cpsItemsGenericLL items

cpsItemsGenericLL :: [BackendItem] -> Gen Text
cpsItemsGenericLL items = case items of
  [] -> do
    declRuntime "declare ptr @kunit()"
    declRuntime "declare ptr @krt2_pure(ptr)"
    u <- freshReg
    emit (u <> " = call ptr @kunit()")
    r <- freshReg
    emit (r <> " = call ptr @krt2_pure(ptr " <> u <> ")")
    pure r
  -- FINAL item: a plain action or a monadic bind whose value is the block's
  -- result.  Compiled directly — the block's tail action, which the CK-machine
  -- drives (no surrounding bind, so the spine stays bounded).
  [BKExpr _ t] -> compileMonadicAction t
  [BKBind _ _ _ _ t _] -> compileMonadicAction t
  -- FINAL let: a pure binding with no following action is degenerate (the block
  -- must end in an action), but lower it as a delayed pure action for totality.
  [BKLet _ _ _ _ t] -> pureValueActionLL t
  -- FINAL do-kernel `if` (Milestone F): the if-action IS the block's result —
  -- lower it to its phi'd action operand and return it directly (no surrounding
  -- bind; the CK-machine drives whichever branch's action the phi selected).
  [BKIf _ alts mels] -> compileDoIf alts mels
  -- A plain ACTION with a following rest: treat as `_ <- action; rest` so REST
  -- stays LAZY inside the continuation closure (NOT krt2_then with an eager rest
  -- operand — that would eagerly build the tail and overflow on IO recursion).
  (BKExpr _ t : rest) -> bindThen t BPWild rest
  -- A monadic bind: `x <- action; rest`.
  (BKBind _ _ pat _ t _ : rest) -> bindThen t pat rest
  -- NON-final do-kernel `if` (Milestone F): build the if-action, then sequence
  -- it with REST as `_ <- ifAction; rest` (REST lazy inside a kdo_N closure),
  -- exactly the 'KExpr' shape — the if's own result is discarded (§18.8).
  (BKIf _ alts mels : rest) -> do
    ifAction <- compileDoIf alts mels
    seqActionThen ifAction BPWild rest
  -- A pure LET binding: current reads/splices have already been lifted by the
  -- checker into preceding bind/action items, so no hidden monadic splice remains
  -- in the RHS.  Still, the pure RHS must run when the action reaches this source
  -- point, not while building the surrounding action tree; scalar safepoint
  -- aborts and preceding defers depend on that ordering.
  (BKLet _ _ BPWild _ t : rest) -> do
    valueAct <- pureValueActionLL t
    seqActionThen valueAct BPWild rest
  (BKLet _ _ pat _ t : rest) -> do
    valueAct <- pureValueActionLL t
    seqActionThen valueAct pat rest
  -- ── Milestone G: the imperative do-kernel ──────────────────────────
  -- ── FINAL imperative items (the block's tail action) ──────────────
  -- A FINAL `var` is degenerate (a do-block ends in an action), but the newRef
  -- IS an action — return it directly.  A FINAL assignment is its writeRef
  -- action; a FINAL return/break/continue/while is its own action operand.
  [BKVarItem _ _ _ actT _] -> do
    refAct <- compileMonadicAction actT
    unitAct <- unitAction
    declRuntime "declare ptr @krt2_then(ptr, ptr)"
    r <- freshReg
    emit (r <> " = call ptr @krt2_then(ptr " <> refAct <> ", ptr " <> unitAct <> ")")
    pure r
  [BKAssign _ _ _ actT _] -> compileMonadicAction actT
  [BKReturn _ e] -> returnAction e
  [BKBreak _ Nothing] -> breakAction
  [BKContinue _ Nothing] -> continueAction
  [BKWhile _ Nothing cond body Nothing] -> whileAction cond body
  -- ── NON-final imperative items (sequenced with the rest) ──────────
  BKVarItem _ _ _ actT _ : rest -> do
    -- S2.3b: run the checker-selected MonadRef.newRef action for shapes that
    -- the evidence-aware scalar planner rejected. Rejected regions stay on the
    -- generic selected-action path; the backend must not reconstruct raw refs.
    refAct <- compileMonadicAction actT
    seqActionThen refAct (BPVar "_var") rest
  -- `var x = e` ≡ `x <- MonadRef.newRef e`: the checker has already built the
  -- selected MonadRef action. Bind it like a 'KBind' so the slot at de Bruijn 0
  -- holds the Ref. Explicit reads are ordinary actions lifted by the do-splice
  -- pass; assignment is 'KAssign'.
  -- `x = e` / `x <- e`: sequence the checker-selected MonadRef.writeRef action.
  -- The action already encodes the selected evidence and any monadic RHS
  -- binding, so LLVM must not reconstruct a raw IO ref write here.
  (BKAssign _ _ _ actT _ : rest) -> do
    writeAct <- compileMonadicAction actT
    seqActionThen writeAct BPWild rest
  -- `return e`: an early-return IO action (`krt2_return value`).  Whatever
  -- follows in the items list is dead (return unwinds the fiber), but it is
  -- sequenced uniformly anyway — the CK-machine never delivers past the return.
  (BKReturn _ e : rest) -> do
    retAct <- returnAction e
    seqActionThen retAct BPWild rest
  -- `break` / `continue` (unlabeled): an abrupt-control IO action targeting the
  -- innermost enclosing `krt2_while`.  Like 'KReturn', anything after is dead.
  (BKBreak _ Nothing : rest) -> do
    a <- breakAction
    seqActionThen a BPWild rest
  (BKContinue _ Nothing : rest) -> do
    a <- continueAction
    seqActionThen a BPWild rest
  -- `while cond do body` (unlabeled, no else): `krt2_while(condIO, bodyIO)`,
  -- where condIO re-reads its `var`s each iteration ('compileMonadicCond') and
  -- bodyIO is the body's own action tree ('compileLoopBody').  Sequenced like a
  -- 'KExpr' (`_ <- whileAction; rest`) — the while's normal completion is Unit.
  (BKWhile _ Nothing cond body Nothing : rest) -> do
    whileAct <- whileAction cond body
    seqActionThen whileAct BPWild rest
  -- §18.7 plain defer: register a lazily-built action on the current do-scope's
  -- ExitStack, then continue.  `wrapDoActionLL`/`wrapScopedItemsLL` guarantee
  -- that any item list containing a direct plain defer has a surrounding
  -- krt2_doscope, so OP_DEFER never lands outside a scope.
  (BKDefer _ Nothing t : rest) -> do
    de <- deferActionTreeLL "kdefer_" (compileMonadicAction t)
    declRuntime "declare ptr @krt2_defer(ptr)"
    reg <- freshReg
    emit (reg <> " = call ptr @krt2_defer(ptr " <> de <> ")")
    seqActionThen reg BPWild rest
  -- ── Milestone M: a statement-position sub-do (`then do { … }`) ──────
  -- §18.8.3.1 'KSubDo': a nested do-block written in statement position.  Its
  -- items are lowered to their OWN @krt2_*@ action tree via the same do-kernel
  -- item compiler ('cpsItemsLL'), and that action is sequenced into the parent.
  -- As the TAIL item the sub-do's action IS the block's result (no surrounding
  -- bind — it is returned directly, like a tail 'KExpr'); as a NON-final item it
  -- is `_ <- subAction; rest` (the sub-do's result is discarded, REST lazy inside
  -- the continuation).  The label is IGNORED here — a labeled sub-scope's
  -- break@L/continue@L is a separate concern (deferred via 'firstUnsupportedItem'
  -- recursion), but a plain `then do { … }` works.  The sub-do's own bindings
  -- live inside its 'cpsItemsLL' continuation closures, so the build-time 'gsEnv'
  -- is unchanged and REST sees only the enclosing scope (correct lexical nesting).
  [BKSubDo _ _lbl subItems] -> wrapScopedItemsLL subItems
  (BKSubDo _ _lbl subItems : rest) -> do
    subAct <- wrapScopedItemsLL subItems
    seqActionThen subAct BPWild rest
  -- §19.5/§18.8.3 `using pat <- acquire`: lower through the runtime's
  -- krt2_acquire_release (the SAME machinery `bracketM` uses, §18.1.12):
  --   mask (\restore -> acquire >>= \res -> finally (restore (use res)) (release res))
  -- with `use res = <bind pat=res; rest>` (the rest of the do-block is the
  -- resource's protected scope).  The whole acquire-and-finalizer-register region
  -- runs MASKED, so the release is guaranteed installed before any interrupt can
  -- land; it then runs on every exit (normal/abrupt/error/interrupt), masked LIFO.
  -- Mirrors the C backend's KUsing CPS lowering (C.hs) and the interpreter oracle.
  (BKUsing _ pat _ acquireT releaseT : rest) -> do
    acqA <- compileMonadicAction acquireT
    relV <- compile releaseT
    -- `use res = (bind pat=res; rest)`: a 1-arg continuation closure over the
    -- using-site env, reusing the ordinary bind-continuation emitter.
    useFn <- emitDoCont pat rest
    capturedEnv <- gets gsEnv
    declRuntime "declare ptr @kclo(ptr, ptr)"
    declRuntime "declare ptr @krt2_acquire_release(ptr, ptr, ptr)"
    useClo <- freshReg
    emit (useClo <> " = call ptr @kclo(ptr @" <> useFn <> ", ptr " <> capturedEnv <> ")")
    r <- freshReg
    emit (r <> " = call ptr @krt2_acquire_release(ptr " <> acqA <> ", ptr " <> relV <> ", ptr " <> useClo <> ")")
    pure r
  (it : _) -> unsupportedDoItem it

-- | Lower `pat <- action; rest` (or `action; rest` with @pat = CPWild@) as
-- @krt2_bind(action, kclo(@kdo_N, env))@, where @kdo_N@ is a lifted continuation
-- closure that receives the delivered value, binds it to @pat@, and compiles
-- REST as an action tree.  The rest lives INSIDE @kdo_N@ — that laziness is what
-- keeps an IO-recursive do-block stack-safe (the tree is built one bind at a
-- time as the CK-machine runs it, not all at once at build time).
bindThen :: BackendTerm -> BackendPat -> [BackendItem] -> Gen Text
bindThen action pat rest = do
  m <- compileMonadicAction action
  seqActionThen m pat rest

-- | Sequence an ALREADY-COMPILED action operand @m@ with the rest of the block:
-- @krt2_bind(m, kclo(@kdo_N, env))@ where @kdo_N@ binds the delivered value to
-- @pat@ and lowers REST.  Same machinery as 'bindThen' but the action is a value
-- operand the caller already produced (e.g. a do-kernel @if@'s phi'd action),
-- not a 'Term' to compile.  Keeps REST lazy inside @kdo_N@ for stack safety.
seqActionThen :: Text -> BackendPat -> [BackendItem] -> Gen Text
seqActionThen m pat rest = do
  contFn <- emitDoCont pat rest
  capturedEnv <- gets gsEnv
  declRuntime "declare ptr @kclo(ptr, ptr)"
  declRuntime "declare ptr @krt2_bind(ptr, ptr)"
  k <- freshReg
  emit (k <> " = call ptr @kclo(ptr @" <> contFn <> ", ptr " <> capturedEnv <> ")")
  r <- freshReg
  emit (r <> " = call ptr @krt2_bind(ptr " <> m <> ", ptr " <> k <> ")")
  pure r

-- | Lower a do-kernel @if@ ('KIf') to a single @krt2_*@ ACTION operand (Milestone
-- F), mirroring the C backend's 'compileKIf' chain but producing krt2 actions
-- rather than C statements.  'KIf' is an else-if CHAIN — a list of @(cond,
-- branch-items)@ guarded branches plus an optional final @else@ block.  Each
-- branch is its own sub-do: its items lower via 'cpsItemsLL' to a branch action.
--
-- The lowering is exactly 'compileIf' (cond → @kas_bool@ → @icmp ne@ → @br i1@ to
-- a then/else block), except the THEN arm is the branch's sub-do action and the
-- ELSE arm is the rest of the chain (the next guarded branch, or the final else
-- / an implicit @krt2_pure(kunit())@ when there is no/exhausted else — §18.8: a
-- one-armed if's normal completion is Unit).  The two arm actions meet at a
-- @phi ptr@; each phi incoming names the arm's ACTUAL end block (read from
-- 'gsBlock' after the arm), since a branch may emit its own control flow (a
-- nested if, a bind tree).  'gsEnv' is saved/restored around each branch so a
-- branch's local 'KLet' bindings never leak into a sibling branch or the join.
--
-- The if must be a RUNTIME-branching action, not a build-time @br i1@.  Inside a
-- @krt2_while@ body the body action tree is built ONCE and re-run each iteration
-- (rt.c KK_LOOP), so a build-time branch on the condition would freeze the
-- decision at the first iteration.  Instead, the condition is an ACTION
-- ('compileMonadic' — it re-reads its explicit Ref reads each iteration) and the branch
-- is chosen INSIDE a lifted selector closure that the CK-machine re-invokes with
-- the freshly-evaluated condition value: @krt2_bind(condIO, kclo(@doifsel))@.  The
-- selector @br i1@s on @kas_bool(%cond)@ and RETURNS the taken branch's action
-- (built fresh each invocation), so the choice re-decides every iteration.  This
-- is also correct (just slightly less direct) for a non-loop / recursive do-if,
-- where the containing closure would rebuild the tree each call anyway.
compileDoIf :: [(BackendTerm, [BackendItem])] -> Maybe [BackendItem] -> Gen Text
compileDoIf alts mels = go alts
  where
    -- The else continuation once the guard chain is exhausted: the final else
    -- block's sub-do, or an implicit `pure unit` (a missing/empty else yields
    -- Unit, the if's discarded normal completion — parity with C's
    -- 'compileKIfTail' / 'krt2_pure(kunit())').
    go [] = case mels of
      Just els -> branchAction els
      Nothing -> do
        declRuntime "declare ptr @kunit()"
        declRuntime "declare ptr @krt2_pure(ptr)"
        u <- freshReg
        emit (u <> " = call ptr @kunit()")
        r <- freshReg
        emit (r <> " = call ptr @krt2_pure(ptr " <> u <> ")")
        pure r
    go ((cond, body) : more) = do
      -- condIO re-evaluates the guard each time it runs.
      condIO <- compileMonadic cond
      selFn <- emitDoIfSelector body more
      capturedEnv <- gets gsEnv
      declRuntime "declare ptr @kclo(ptr, ptr)"
      declRuntime "declare ptr @krt2_bind(ptr, ptr)"
      k <- freshReg
      emit (k <> " = call ptr @kclo(ptr @" <> selFn <> ", ptr " <> capturedEnv <> ")")
      r <- freshReg
      emit (r <> " = call ptr @krt2_bind(ptr " <> condIO <> ", ptr " <> k <> ")")
      pure r
    -- Lower one branch's items to its action, isolating its env so a local
    -- binding in the branch does not extend into the join's de Bruijn layout.
    branchAction items = do
      env0 <- gets gsEnv
      a <- cpsItemsLL items
      modify' $ \g -> g {gsEnv = env0}
      if any directDefersLL items
        then wrapDoScopeLL a
        else pure a
    -- A selector closure @doifsel(%cenv, %cond)@: it does NOT bind %cond into the
    -- env (it is the guard's Bool, not a value binder).  @br i1@ on
    -- @kas_bool(%cond)@; the then-block returns this guard's branch action, the
    -- else-block returns the rest of the chain — both built fresh on each call so
    -- a loop re-decides the branch every iteration.  %cenv is the enclosing env.
    emitDoIfSelector body more = do
      fnIdent <- freshLabel "doifsel_"
      (bodyInsns, _endBlock, resultOp) <- captured "%cenv" $ do
        modify' $ \g -> g {gsEnv = "%cenv"}
        declRuntime "declare i32 @kas_bool(ptr)"
        bi <- freshReg
        emit (bi <> " = call i32 @kas_bool(ptr %cond)")
        c1 <- freshReg
        emit (c1 <> " = icmp ne i32 " <> bi <> ", 0")
        thenL <- freshLabel "doif.then."
        elseL <- freshLabel "doif.else."
        joinL <- freshLabel "doif.join."
        emit ("br i1 " <> c1 <> ", label %" <> thenL <> ", label %" <> elseL)
        startBlock thenL
        tv <- branchAction body
        thenEnd <- gets gsBlock
        emit ("br label %" <> joinL)
        startBlock elseL
        ev <- go more
        elseEnd <- gets gsBlock
        emit ("br label %" <> joinL)
        startBlock joinL
        r <- freshReg
        emit (r <> " = phi ptr [ " <> tv <> ", %" <> thenEnd <> " ], [ "
                <> ev <> ", %" <> elseEnd <> " ]")
        pure r
      let def =
            T.unlines $
              [ "define internal ptr @" <> fnIdent <> "(ptr %cenv, ptr %cond) {"
              , "build:"
              ]
                ++ map ("  " <>) bodyInsns
                ++ [ "  ret ptr " <> resultOp
                   , "}"
                   ]
      modify' $ \st -> st {gsTop = def : gsTop st}
      pure fnIdent

-- | Emit a continuation closure @kdo_N(ptr %cenv, ptr %arg)@ (a one-argument
-- @kfn@, exactly the 'compileLam' shape): bind the delivered @%arg@ to @pat@ by
-- extending the captured @%cenv@, then compile REST as a @krt2_*@ action tree
-- and @ret@ it.  Emitted via 'gsTop' and invoked by @krt2_bind@ through @kclo@.
emitDoCont :: BackendPat -> [BackendItem] -> Gen Text
emitDoCont pat rest = do
  fnIdent <- freshLabel "kdo_"
  declRuntime "declare ptr @kpush(ptr, ptr)"
  -- Compile the continuation body in its OWN buffer (like 'compileLam'): %cenv is
  -- the captured env; the delivered value %arg is bound to @pat@ over it, and the
  -- block's REST is built as an action tree under the extended env.
  (bodyInsns, _endBlock, resultOp) <- captured "%cenv" $ do
    env1 <- bindPatDo "%arg" pat
    modify' $ \g -> g {gsEnv = env1}
    cpsItemsLL rest
  let def =
        T.unlines $
          [ "define internal ptr @" <> fnIdent <> "(ptr %cenv, ptr %arg) {"
          , "build:"
          ]
            ++ map ("  " <>) bodyInsns
            ++ [ "  ret ptr " <> resultOp
               , "}"
               ]
  modify' $ \st -> st {gsTop = def : gsTop st}
  pure fnIdent

-- | Bind a do-item's binder pattern, delivering the action's result operand
-- @v@.  A simple variable/wildcard binder ('CPVar'/'CPWild'/'CPAs' over those)
-- is a direct env push, mirroring 'bindPat'.  An intricate constructor/tuple
-- PATTERN is destructured by projecting it through a single-alt 'CMatch': bind
-- @v@ to a fresh var, then match — i.e. the same kpush-then-project the
-- match path already lowers.  Returns the extended env operand.
bindPatDo :: Text -> BackendPat -> Gen Text
bindPatDo v pat
  | isVarLike pat = bindPat v pat
  | otherwise = do
      -- A structured binder: push the whole value as one slot (so the rest can
      -- read it), then project each field via 'patBindingsLL' (the same
      -- single-level constructor projection the match path uses).  Restricting
      -- to 'patBindingsLL'-supported shapes keeps parity with the match subset;
      -- a shape it cannot bind is reported there (a clean unsupported).
      env0 <- gets gsEnv
      vals <- patBindingsLL v pat
      foldM pushSlot env0 vals
  where
    pushSlot e valOp = do
      declRuntime "declare ptr @kpush(ptr, ptr)"
      n <- freshReg
      emit (n <> " = call ptr @kpush(ptr " <> valOp <> ", ptr " <> e <> ")")
      pure n

wrapScopedItemsLL :: [BackendItem] -> Gen Text
wrapScopedItemsLL items = do
  action <- cpsItemsLL items
  if any directDefersLL items
    then wrapDoScopeLL action
    else pure action

-- ── Milestone G: the imperative do-kernel ────────────────────────────
--
-- Mutable cells, `while` loops, and abrupt control, lowered onto the kappart2
-- CK-machine the do-kernel already uses (NOT the C backend's synchronous
-- `goto`/`krun_io` loop, which is a Phase-2 perf path).  The load-bearing fact:
-- `krt2_while(condIO, bodyIO)` RE-RUNS both action operands every iteration
-- (rt.c OP_WHILE → KK_LOOP). Normal source `!` splices and mutable-current reads
-- are lifted by the checker to preceding monadic binds or stored as action terms
-- in 'KCondAction', so LLVM lowering only sees ordinary do-kernel actions here.

-- | Lift a pure value-position term into a re-runnable IO ACTION yielding the
-- term's value.
compileMonadic :: BackendTerm -> Gen Text
compileMonadic t = do
  v <- compile t
  declRuntime "declare ptr @krt2_pure(ptr)"
  r <- freshReg
  emit (r <> " = call ptr @krt2_pure(ptr " <> v <> ")")
  pure r

-- | Lower an ACTION-position term to a re-runnable IO action.
compileMonadicAction :: BackendTerm -> Gen Text
compileMonadicAction = compile

-- | Lower a pure term to a delayed action yielding that value.  This is used for
-- pure @let@ inside CPS do-kernel lowering: the RHS may contain long scalar work
-- or safepoints, so it must execute in source order when the CK machine reaches
-- the let, not while the surrounding action tree is being constructed.
pureValueActionLL :: BackendTerm -> Gen Text
pureValueActionLL t =
  deferActionTreeLL "kpure_" $ do
    v <- compile t
    declRuntime "declare ptr @krt2_pure(ptr)"
    r <- freshReg
    emit (r <> " = call ptr @krt2_pure(ptr " <> v <> ")")
    pure r

-- | The @return e@ early-exit IO action: @krt2_return(value)@. Current reads and
-- splices inside @e@ have already been lifted into preceding binds by the
-- checker, so @e@ is a pure value at this point.
returnAction :: BackendTerm -> Gen Text
returnAction e = do
  v <- compile e
  declRuntime "declare ptr @krt2_return(ptr)"
  r <- freshReg
  emit (r <> " = call ptr @krt2_return(ptr " <> v <> ")")
  pure r

-- | The unlabeled @break@ IO action: @krt2_break()@ — exits the innermost
-- enclosing @krt2_while@ (rt.c KK_LOOP, RK_BREAK).
breakAction :: Gen Text
breakAction = do
  declRuntime "declare ptr @krt2_break()"
  r <- freshReg
  emit (r <> " = call ptr @krt2_break()")
  pure r

-- | The unlabeled @continue@ IO action: @krt2_continue()@ — re-tests the
-- innermost enclosing @krt2_while@'s condition (rt.c KK_LOOP, RK_CONTINUE).
continueAction :: Gen Text
continueAction = do
  declRuntime "declare ptr @krt2_continue()"
  r <- freshReg
  emit (r <> " = call ptr @krt2_continue()")
  pure r

-- | The @while cond do body@ IO action: @krt2_while(condIO, bodyIO)@.  Both
-- operands are re-runnable actions ('compileMonadicCond' / 'compileLoopBody'),
-- which the CK-machine re-executes each iteration (so `var` reads re-evaluate).
-- The loop's normal completion (condition False) yields Unit.
whileAction :: BackendCond -> [BackendItem] -> Gen Text
whileAction cond body = do
  condIO <- compileMonadicCond cond
  bodyIO <- compileLoopBody body
  declRuntime "declare ptr @krt2_while(ptr, ptr)"
  r <- freshReg
  emit (r <> " = call ptr @krt2_while(ptr " <> condIO <> ", ptr " <> bodyIO <> ")")
  pure r

-- | The condition action for a @while@: a re-runnable IO action yielding a Bool.
compileMonadicCond :: BackendCond -> Gen Text
compileMonadicCond = \case
  BKCondPure t -> compileMonadic t
  BKCondAction t -> compileMonadicAction t

-- | The body action for a @while@: the body items lowered to a `krt2_*` action
-- tree via 'cpsItemsLL'.  The body runs under the enclosing env (its `var`s are
-- env slots the loop's actions read); 'krt2_while' re-runs this whole action each
-- iteration, and `var` reads inside re-execute because they are IO read actions.
compileLoopBody :: [BackendItem] -> Gen Text
compileLoopBody body =
  deferActionTreeLL "kwhile_body_" (cpsItemsLL body)

-- ── Function scalar worker (the LLVM @kwi_@/@kwd_@ analog) ────────────
--
-- A faithful port of the C backend's function scalar-worker
-- ('Kappa.Backend.C.compileScalarWorker' / 'compileScalarCall' /
-- 'scalarPlan'): a monomorphic FIRST-ORDER scalar function — every relevant
-- explicit parameter and the result an @Int@ ('RepInt' ⇒ @i64@) or @Double@
-- ('RepDouble' ⇒ @double@) — with a scalar-EXPRESSIBLE body gets an auxiliary
-- UNBOXED worker beside the boxed curried-closure path.  A saturated direct call
-- unboxes each argument by its kind, calls the worker, and ESCAPES to the boxed
-- path (the curried @kg_@/@kapp@/@ktrampoline@ chain over the ORIGINAL boxed
-- args) on a wrong-tag argument or an int64 overflow — so the boxed/GMP result
-- is always the reference (the unbox tag-check is the soundness net: even a
-- mis-derived kind escapes to boxed, never miscompiles).
--
-- This is the LLVM analogue of the C function worker. The body grammar is the
-- SAME conservative allowlist as C's 'scalarEligTail'/'scalarKindOf' (scalar
-- literal, scalar param/let var, the int+double arith prims, @intToDouble@, the
-- safe compares as an @if@ condition, @if@/@let@ in tail or value position, and
-- saturated self-calls) — which admits
-- NO suspending or IO form, so a worker body is suspension-free BY CONSTRUCTION
-- (the §7 Stage 1.5 witness the C backend spells out is implied here by the
-- narrow grammar — there is no admitted leaf at which a fiber could park, so no
-- raw-scalar SSA value is ever live across a suspension point).

kCondTermLL :: KCond -> Term
kCondTermLL = \case
  KCondPure t -> t
  KCondAction t -> t

i64InRangeLL :: Integer -> Bool
i64InRangeLL m = m >= toInteger (minBound :: Int) && m <= toInteger (maxBound :: Int)

-- | A defensive backend error for a term the scalar-worker eligibility analysis
-- should have excluded.
escalateScalarLL :: Gen Text
escalateScalarLL =
  unsupported
    "scalar-worker"
    "an ineligible term reached the LLVM scalar worker (eligibility invariant violated)"

-- | The scalar kind of a worker param/result: an unboxed @i64@ or @double@.
data ScalarKindLL = KInt64L | KDoubleL deriving (Eq)

-- | A worker parameter slot: an unboxed scalar or a boxed @ptr@ pass-through.
-- (The LLVM port today only emits ALL-scalar workers — the mixed @kwm_@ record
-- slice is C-only; a body that reads a boxed-param field is left to the boxed
-- path.  'PBoxedLL' is kept for parity of the analysis shape.)
data ParamKindLL = PScalarLL !ScalarKindLL | PBoxedLL deriving (Eq)

-- | The LLVM type text for a scalar kind.
llScalarTy :: ScalarKindLL -> Text
llScalarTy KInt64L = "i64"
llScalarTy KDoubleL = "double"

scalarOverflowLL :: Text
scalarOverflowLL = "1"

scalarAbortLL :: Text
scalarAbortLL = "2"

scalarSpQuantumLL :: Text
scalarSpQuantumLL = "65536"

-- | The LLVM type text for a parameter slot (an all-scalar worker never has a
-- boxed slot; default to @i64@ defensively).
pkTyLL :: ParamKindLL -> Text
pkTyLL = maybe "i64" llScalarTy . paramSKLL

-- | The scalar kind of a slot, or 'Nothing' for a boxed slot.
paramSKLL :: ParamKindLL -> Maybe ScalarKindLL
paramSKLL (PScalarLL k) = Just k
paramSKLL PBoxedLL = Nothing

-- | The 'Repr.Rep' → 'ScalarKindLL' projection (mirror of C's 'repScalarKind').
repScalarKindLL :: Repr.Rep -> Maybe ScalarKindLL
repScalarKindLL = \case
  Repr.RepInt -> Just KInt64L
  Repr.RepDouble -> Just KDoubleL
  _ -> Nothing

-- | A scalar arith prim and its (result kind, argument kinds) — the FULL Int +
-- Double set (mirror of C's 'arithPrim').  @intToDouble@ is the one cross-kind
-- coercion (Int → Double).
arithPrimLL2 :: Text -> Maybe (ScalarKindLL, [ScalarKindLL])
arithPrimLL2 = \case
  "addInt" -> Just (KInt64L, [KInt64L, KInt64L])
  "subInt" -> Just (KInt64L, [KInt64L, KInt64L])
  "mulInt" -> Just (KInt64L, [KInt64L, KInt64L])
  "divInt" -> Just (KInt64L, [KInt64L, KInt64L])
  "modInt" -> Just (KInt64L, [KInt64L, KInt64L])
  "negInt" -> Just (KInt64L, [KInt64L])
  "addDouble" -> Just (KDoubleL, [KDoubleL, KDoubleL])
  "subDouble" -> Just (KDoubleL, [KDoubleL, KDoubleL])
  "mulDouble" -> Just (KDoubleL, [KDoubleL, KDoubleL])
  "divDouble" -> Just (KDoubleL, [KDoubleL, KDoubleL])
  "negDouble" -> Just (KDoubleL, [KDoubleL])
  "intToDouble" -> Just (KDoubleL, [KInt64L])
  _ -> Nothing

-- | A scalar comparison usable as an @if@ condition: (LLVM compare op-class +
-- predicate, operand kind).  ONLY comparisons whose semantics match the runtime
-- prim EXACTLY — the int compares (@icmp@), @ltDouble@ (IEEE @<@ ⇒ @fcmp olt@)
-- and @floatEq@ (IEEE @==@ ⇒ @fcmp oeq@).  @eqDouble@ (§6.1.3 raw-bit equality)
-- and @leDouble@ (no runtime prim) are excluded — same exclusions as C's
-- 'cmpPrim'.  The first component is "icmp <pred>" or "fcmp <pred>".
cmpPrimLL2 :: Text -> Maybe (Text, ScalarKindLL)
cmpPrimLL2 = \case
  "eqInt" -> Just ("icmp eq", KInt64L)
  "ltInt" -> Just ("icmp slt", KInt64L)
  "leInt" -> Just ("icmp sle", KInt64L)
  "ltDouble" -> Just ("fcmp olt", KDoubleL)
  "floatEq" -> Just ("fcmp oeq", KDoubleL)
  _ -> Nothing

-- ── Evidence-aware LLVM scalar var/while loop ────────────────────────

data ScalarCondLoopLL = ScalarCondLoopLL !(Map Int RefCellId) !BackendTerm

data ScalarAssignLoopLL = ScalarAssignLoopLL !RefCellId !(Map Int RefCellId) !BackendTerm

data ScalarLoopLL = ScalarLoopLL
  { sllCells :: ![RefCellId]
  , sllInits :: ![Integer]
  , sllCond :: !ScalarCondLoopLL
  , sllBody :: ![ScalarAssignLoopLL]
  , sllRest :: ![BackendItem]
  }

cellOfWitnessLL :: RefLoweringWitness -> RefCellId
cellOfWitnessLL (BuiltinIORefWitness cid) = cid

newWitnessCellLL :: Maybe RefActionWitness -> Maybe RefCellId
newWitnessCellLL = \case
  Just (BuiltinIORefNew w) -> Just (cellOfWitnessLL w)
  _ -> Nothing

readWitnessCellLL :: Maybe RefActionWitness -> Maybe RefCellId
readWitnessCellLL = \case
  Just (BuiltinIORefRead w) -> Just (cellOfWitnessLL w)
  _ -> Nothing

writeWitnessCellLL :: Maybe RefActionWitness -> Maybe RefCellId
writeWitnessCellLL = \case
  Just (BuiltinIORefWrite w) -> Just (cellOfWitnessLL w)
  _ -> Nothing

loopCellIndexLL :: Map RefCellId Int -> RefCellId -> Maybe Int
loopCellIndexLL cells cid = Map.lookup cid cells

shiftReadEnvLL :: Map Int RefCellId -> Map Int RefCellId
shiftReadEnvLL = Map.mapKeysMonotonic (+ 1)

bindReadEnvLL :: RefCellId -> Map Int RefCellId -> Map Int RefCellId
bindReadEnvLL cid env = Map.insert 0 cid (shiftReadEnvLL env)

intArithPrimLoopLL :: Text -> Maybe Int
intArithPrimLoopLL p = case arithPrimLL2 p of
  Just (KInt64L, args) | all (== KInt64L) args -> Just (length args)
  _ -> Nothing

intCmpPrimLoopLL :: Text -> Maybe Text
intCmpPrimLoopLL p = case cmpPrimLL2 p of
  Just (op, KInt64L)
    | Just predTxt <- T.stripPrefix "icmp " op -> Just predTxt
  _ -> Nothing

scalarReadCellLL :: Map RefCellId Int -> Map Int RefCellId -> BackendTerm -> Maybe RefCellId
scalarReadCellLL cells env = \case
  BVar _ _ i -> do
    cid <- Map.lookup i env
    cid <$ loopCellIndexLL cells cid
  _ -> Nothing

i64LoopExprLL :: Map RefCellId Int -> Map Int RefCellId -> BackendTerm -> Gen Bool
i64LoopExprLL cells env term = case scalarReadCellLL cells env term of
  Just _ -> pure True
  Nothing -> case term of
    BLit _ (LitInt m) -> pure (i64InRangeLL m)
    _ -> case backendSpineOf term of
      (BGlob _ g, sargs) -> do
        mp <- globPrimName g
        let expl = [argTerm a | a <- sargs, argIcit a == Expl]
        case mp >>= intArithPrimLoopLL of
          Just n | length expl == n -> andMLL (map (i64LoopExprLL cells env) expl)
          _ -> pure False
      _ -> pure False

i64LoopCondLL :: Map RefCellId Int -> Map Int RefCellId -> BackendTerm -> Gen Bool
i64LoopCondLL cells env term = case backendSpineOf term of
  (BGlob _ g, sargs) -> do
    mp <- globPrimName g
    let expl = [argTerm a | a <- sargs, argIcit a == Expl]
    case (mp >>= intCmpPrimLoopLL, expl) of
      (Just _, [a, b]) -> andMLL [i64LoopExprLL cells env a, i64LoopExprLL cells env b]
      _ -> pure False
  _ -> pure False

scalarCondPlanLL :: Map RefCellId Int -> BackendCond -> Gen (Maybe ScalarCondLoopLL)
scalarCondPlanLL cells = \case
  BKCondPure t -> do
    ok <- i64LoopCondLL cells Map.empty t
    pure (if ok then Just (ScalarCondLoopLL Map.empty t) else Nothing)
  BKCondAction (BDo _ _ items) -> scalarCondItemsLL cells Map.empty items
  BKCondAction _ -> pure Nothing

scalarCondItemsLL :: Map RefCellId Int -> Map Int RefCellId -> [BackendItem] -> Gen (Maybe ScalarCondLoopLL)
scalarCondItemsLL cells env = \case
  [BKExpr _ t] -> do
    ok <- i64LoopCondLL cells env t
    pure (if ok then Just (ScalarCondLoopLL env t) else Nothing)
  [BKReturn _ t] -> do
    ok <- i64LoopCondLL cells env t
    pure (if ok then Just (ScalarCondLoopLL env t) else Nothing)
  BKBind _ _ (BPVar _) _ _ w : rest
    | Just cid <- readWitnessCellLL w
    , Just _ <- loopCellIndexLL cells cid ->
        scalarCondItemsLL cells (bindReadEnvLL cid env) rest
  BKBind _ _ BPWild _ _ w : rest
    | Just cid <- readWitnessCellLL w
    , Just _ <- loopCellIndexLL cells cid ->
        scalarCondItemsLL cells env rest
  _ -> pure Nothing

scalarBodyPlanLL :: Map RefCellId Int -> [BackendItem] -> Gen (Maybe [ScalarAssignLoopLL])
scalarBodyPlanLL cells = go Map.empty []
  where
    go env acc = \case
      [] -> pure (Just (reverse acc))
      BKBind _ _ (BPVar _) _ _ w : rest
        | Just cid <- readWitnessCellLL w
        , Just _ <- loopCellIndexLL cells cid ->
            go (bindReadEnvLL cid env) acc rest
      BKBind _ _ BPWild _ _ w : rest
        | Just cid <- readWitnessCellLL w
        , Just _ <- loopCellIndexLL cells cid ->
            go env acc rest
      BKAssign _ False rhs _ w : rest
        | Just cid <- writeWitnessCellLL w
        , Just _ <- loopCellIndexLL cells cid -> do
            ok <- i64LoopExprLL cells env rhs
            if ok
              then go Map.empty (ScalarAssignLoopLL cid env rhs : acc) rest
              else pure Nothing
      _ -> pure Nothing

bodyCapturesEnvLL :: BackendTerm -> Bool
bodyCapturesEnvLL = go
  where
    go = \case
      BLam {} -> True
      BLetRec {} -> True
      BDo {} -> True
      BThunk {} -> True
      BLazy {} -> True
      BApp _ f args -> go f || any (go . argTerm) args
      BCtor _ _ args -> any go args
      BMatch _ s alts _ -> go s || any goAlt alts
      BProj _ e _ _ -> go e
      BInject _ _ e -> go e
      BForce _ e -> go e
      BSeal _ _ e -> go e
      BLet _ _ _ _ rhs body -> go rhs || go body
      BIf _ c th el -> go c || go th || go el
      BRecord _ fs -> any (go . snd) fs
      BUnit {} -> False
      BVar {} -> False
      BGlob {} -> False
      BLit {} -> False
    goAlt (BackendAlt _ _ _ mg body) = maybe False go mg || go body

backendCondTermLL :: BackendCond -> BackendTerm
backendCondTermLL = \case
  BKCondPure t -> t
  BKCondAction t -> t

itemHasClosureLL :: BackendItem -> Bool
itemHasClosureLL = \case
  BKExpr _ t -> bodyCapturesEnvLL t
  BKBind _ _ _ _ t _ -> bodyCapturesEnvLL t
  BKLet _ _ _ _ t -> bodyCapturesEnvLL t
  BKLetQ _ _ _ t mels -> bodyCapturesEnvLL t || maybe False (\(_, _, body) -> bodyCapturesEnvLL body) mels
  BKVarItem _ _ initT actT _ -> bodyCapturesEnvLL initT || bodyCapturesEnvLL actT
  BKAssign _ _ rhs actT _ -> bodyCapturesEnvLL rhs || bodyCapturesEnvLL actT
  BKReturn _ t -> bodyCapturesEnvLL t
  BKWhile _ _ c b mels -> bodyCapturesEnvLL (backendCondTermLL c) || any itemHasClosureLL b || maybe False (any itemHasClosureLL) mels
  BKFor _ _ _ _ s b mels -> bodyCapturesEnvLL s || any itemHasClosureLL b || maybe False (any itemHasClosureLL) mels
  BKIf _ alts mels -> any (\(c, b) -> bodyCapturesEnvLL c || any itemHasClosureLL b) alts || maybe False (any itemHasClosureLL) mels
  BKDefer _ _ t -> bodyCapturesEnvLL t
  BKUsing _ _ _ a r -> bodyCapturesEnvLL a || bodyCapturesEnvLL r
  BKSubDo _ _ b -> any itemHasClosureLL b
  BKBreak _ _ -> False
  BKContinue _ _ -> False

scalarLoopPlanLL :: [BackendItem] -> Gen (Maybe ScalarLoopLL)
scalarLoopPlanLL items =
  case span isScalarVar items of
    (varRun@(_ : _), BKWhile _ Nothing cond body Nothing : rest2) -> do
      let inits = mapMaybe initLit varRun
      if length inits /= length varRun
        then pure Nothing
        else do
          let cellsList = map fst inits
              cells = Map.fromList (zip cellsList [0 :: Int ..])
              noClosure = not (any itemHasClosureLL rest2)
          mcond <- scalarCondPlanLL cells cond
          mbody <- scalarBodyPlanLL cells body
          pure $ case (mcond, mbody) of
            (Just condPlan, Just bodyPlan)
              | not (null bodyPlan)
              , noClosure ->
                  Just (ScalarLoopLL cellsList (map snd inits) condPlan bodyPlan rest2)
            _ -> Nothing
    _ -> pure Nothing
  where
    isScalarVar = \case
      BKVarItem _ _ _ _ w -> isJust (newWitnessCellLL w)
      _ -> False
    initLit = \case
      BKVarItem _ _ (BLit _ (LitInt m)) _ w
        | i64InRangeLL m -> (\cid -> (cid, m)) <$> newWitnessCellLL w
      _ -> Nothing

emitScalarLoopLL :: ScalarLoopLL -> Gen Text
emitScalarLoopLL plan =
  -- Keep the optimized region as an IO action, not as eager action-tree
  -- construction. The closure allocates the hidden refs and builds the scalar
  -- native leaf only when the action is executed, so CAF/action reuse preserves
  -- newRef freshness and ref identity.
  deferActionTreeLL "kscalar_region_" (emitScalarLoopActionLL plan)

emitScalarLoopActionLL :: ScalarLoopLL -> Gen Text
emitScalarLoopActionLL plan = do
  let inits = sllInits plan
      cells = sllCells plan
      k = length cells
  declRuntime "declare ptr @kint(i64)"
  declRuntime "declare ptr @kref_new(ptr)"
  declRuntime "declare ptr @kpush(ptr, ptr)"
  env0 <- gets gsEnv
  (refsRev, envK) <-
    foldM
      ( \(acc, env) lit -> do
          box <- freshReg
          emit (box <> " = call ptr @kint(i64 " <> T.pack (show lit) <> ")")
          ref <- freshReg
          emit (ref <> " = call ptr @kref_new(ptr " <> box <> ")")
          env' <- freshReg
          emit (env' <> " = call ptr @kpush(ptr " <> ref <> ", ptr " <> env <> ")")
          pure (ref : acc, env')
      )
      ([], env0)
      inits
  let refs = reverse refsRev
  fnIdent <- emitScalarLoopFnLL plan
  argv <- freshReg
  emit (argv <> " = alloca [" <> T.pack (show k) <> " x ptr], align 8")
  forM_ (zip [0 :: Int ..] refs) $ \(j, ref) -> do
    slot <- freshReg
    emit (slot <> " = getelementptr inbounds [" <> T.pack (show k) <> " x ptr], ptr " <> argv <> ", i64 0, i64 " <> T.pack (show j))
    emit ("store ptr " <> ref <> ", ptr " <> slot <> ", align 8")
  declRuntime "declare ptr @knative_sat(ptr, i32, ptr, i32)"
  loopAct <- freshReg
  emit (loopAct <> " = call ptr @knative_sat(ptr @" <> fnIdent <> ", i32 " <> T.pack (show k) <> ", ptr " <> argv <> ", i32 1)")
  modify' $ \g -> g {gsEnv = envK}
  restAct <-
    if null (sllRest plan)
      then pure loopAct
      else seqActionThen loopAct BPWild (sllRest plan)
  modify' $ \g -> g {gsEnv = env0}
  pure restAct

emitScalarLoopFnLL :: ScalarLoopLL -> Gen Text
emitScalarLoopFnLL plan = do
  fnIdent <- freshLabel "kscalarloop_"
  let cells = sllCells plan
      inits = sllInits plan
      k = length cells
      cellIndex = Map.fromList (zip cells [0 :: Int ..])
  (bodyInsns, _end, ()) <- captured "%args" $ do
    declRuntime "declare ptr @kunit()"
    declRuntime "declare ptr @kint(i64)"
    declRuntime "declare ptr @kref_set(ptr, ptr)"
    cellOf <-
      fmap Map.fromList $
        forM (zip [0 :: Int ..] cells) $ \(j, cid) -> do
          slot <- freshReg
          emit (slot <> " = getelementptr inbounds [" <> T.pack (show k) <> " x ptr], ptr %args, i64 0, i64 " <> T.pack (show j))
          cell <- freshReg
          emit (cell <> " = load ptr, ptr " <> slot <> ", align 8")
          pure (cid, cell)
    slotOf <-
      fmap Map.fromList $
        forM (zip cells inits) $ \(cid, lit) -> do
          sl <- freshReg
          emit (sl <> " = alloca i64, align 8")
          emit ("store i64 " <> T.pack (show lit) <> ", ptr " <> sl <> ", align 8")
          pure (cid, sl)
    declRuntime "declare i32 @krt2_safepoint()"
    spSlot <- freshReg
    emit (spSlot <> " = alloca i64, align 8")
    emit ("store i64 " <> scalarSpQuantumLL <> ", ptr " <> spSlot <> ", align 8")
    contL <- freshLabel "scont_"
    bodyL <- freshLabel "sbody_"
    spchkL <- freshLabel "sspchk_"
    flushL <- freshLabel "sflush_"
    boxedL <- freshLabel "sbox_"
    abortL <- freshLabel "sabort_"
    doneL <- freshLabel "sdone_"
    let flushSnapStores snapOf =
          forM_ cells $ \cid -> do
            bx <- freshReg
            emit (bx <> " = call ptr @kint(i64 " <> snapOf cid <> ")")
            dump <- freshReg
            emit (dump <> " = call ptr @kref_set(ptr " <> (cellOf Map.! cid) <> ", ptr " <> bx <> ")")
        flushSnapTo snapOf target = do
          flushSnapStores snapOf
          emit ("br label %" <> target)
    emit ("br label %" <> contL)
    startBlock contL
    hdrSnaps <-
      fmap Map.fromList $
        forM cells $ \cid -> do
          v <- freshReg
          emit (v <> " = load i64, ptr " <> (slotOf Map.! cid) <> ", align 8")
          pure (cid, v)
    condBit <- scalarCondLoopLL cellIndex slotOf (flushSnapTo (\cid -> hdrSnaps Map.! cid) boxedL) (sllCond plan)
    emit ("br i1 " <> condBit <> ", label %" <> bodyL <> ", label %" <> flushL)
    startBlock bodyL
    bodySnaps <-
      fmap Map.fromList $
        forM cells $ \cid -> do
          v <- freshReg
          emit (v <> " = load i64, ptr " <> (slotOf Map.! cid) <> ", align 8")
          pure (cid, v)
    scalarBodyLoopLL cellIndex slotOf (flushSnapTo (\cid -> bodySnaps Map.! cid) boxedL) (sllBody plan)
    spCur <- freshReg
    emit (spCur <> " = load i64, ptr " <> spSlot <> ", align 8")
    spDec <- freshReg
    emit (spDec <> " = sub i64 " <> spCur <> ", 1")
    emit ("store i64 " <> spDec <> ", ptr " <> spSlot <> ", align 8")
    spGate <- freshReg
    emit (spGate <> " = icmp sle i64 " <> spDec <> ", 0")
    emit ("br i1 " <> spGate <> ", label %" <> spchkL <> ", label %" <> contL)
    startBlock spchkL
    emit ("store i64 " <> scalarSpQuantumLL <> ", ptr " <> spSlot <> ", align 8")
    spRc <- freshReg
    emit (spRc <> " = call i32 @krt2_safepoint()")
    spAbort <- freshReg
    emit (spAbort <> " = icmp ne i32 " <> spRc <> ", 0")
    emit ("br i1 " <> spAbort <> ", label %" <> abortL <> ", label %" <> contL)
    startBlock abortL
    abortSnaps <-
      fmap Map.fromList $
        forM cells $ \cid -> do
          v <- freshReg
          emit (v <> " = load i64, ptr " <> (slotOf Map.! cid) <> ", align 8")
          pure (cid, v)
    flushSnapStores (\cid -> abortSnaps Map.! cid)
    declRuntime "declare void @krt2_scalar_abort()"
    emit "call void @krt2_scalar_abort()"
    emit "unreachable"
    startBlock flushL
    forM_ cells $ \cid -> do
      v <- freshReg
      emit (v <> " = load i64, ptr " <> (slotOf Map.! cid) <> ", align 8")
      bx <- freshReg
      emit (bx <> " = call ptr @kint(i64 " <> v <> ")")
      dump <- freshReg
      emit (dump <> " = call ptr @kref_set(ptr " <> (cellOf Map.! cid) <> ", ptr " <> bx <> ")")
    emit ("br label %" <> doneL)
    startBlock boxedL
    scalarBoxedLoopLL cellIndex cellOf (sllCond plan) (sllBody plan) doneL
    startBlock doneL
    u <- freshReg
    emit (u <> " = call ptr @kunit()")
    emit ("ret ptr " <> u)
  let def =
        T.unlines $
          ["define internal ptr @" <> fnIdent <> "(ptr %args) {", "build:"]
            ++ map ("  " <>) bodyInsns
            ++ ["}"]
  modify' $ \st -> st {gsTop = def : gsTop st}
  pure fnIdent

scalarCondLoopLL :: Map RefCellId Int -> Map RefCellId Text -> Gen () -> ScalarCondLoopLL -> Gen Text
scalarCondLoopLL cells slotOf flushAndGoto (ScalarCondLoopLL env term) = case backendSpineOf term of
  (BGlob _ g, sargs) -> do
    mp <- globPrimName g
    case (mp >>= intCmpPrimLoopLL, [argTerm a | a <- sargs, argIcit a == Expl]) of
      (Just pred_, [a, b]) -> do
        ae <- scalarI64ExprLoopLL cells env slotOf flushAndGoto a
        be <- scalarI64ExprLoopLL cells env slotOf flushAndGoto b
        r <- freshReg
        emit (r <> " = icmp " <> pred_ <> " i64 " <> ae <> ", " <> be)
        pure r
      _ -> escalateScalarLoopLL
  _ -> escalateScalarLoopLL

scalarI64ExprLoopLL :: Map RefCellId Int -> Map Int RefCellId -> Map RefCellId Text -> Gen () -> BackendTerm -> Gen Text
scalarI64ExprLoopLL cells env slotOf flushAndGoto = goE
  where
    goE term = case scalarReadCellLL cells env term of
      Just cid -> do
        r <- freshReg
        emit (r <> " = load i64, ptr " <> (slotOf Map.! cid) <> ", align 8")
        pure r
      Nothing -> case term of
        BLit _ (LitInt m) -> pure (T.pack (show m))
        _ -> case backendSpineOf term of
          (BGlob _ g, sargs) -> do
            mp <- globPrimName g
            let expl = [argTerm a | a <- sargs, argIcit a == Expl]
            case (mp >>= intArithPrimLoopLL, mp, expl) of
              (Just 2, Just nm, [a, b]) -> binOp nm a b
              (Just 1, Just _nm, [a]) -> negOp a
              _ -> escalateScalarLoopLL
          _ -> escalateScalarLoopLL
    binOp nm a b = do
      ae <- goE a
      be <- goE b
      case nm of
        "addInt" -> ovfOp "sadd" ae be
        "subInt" -> ovfOp "ssub" ae be
        "mulInt" -> ovfOp "smul" ae be
        "divInt" -> divModOp True ae be
        "modInt" -> divModOp False ae be
        _ -> escalateScalarLoopLL
    negOp a = do
      ae <- goE a
      ovfOp "ssub" "0" ae
    ovfOp pfx ae be = do
      declRuntime ("declare {i64, i1} @llvm." <> pfx <> ".with.overflow.i64(i64, i64)")
      pair <- freshReg
      emit (pair <> " = call {i64, i1} @llvm." <> pfx <> ".with.overflow.i64(i64 " <> ae <> ", i64 " <> be <> ")")
      val <- freshReg
      emit (val <> " = extractvalue {i64, i1} " <> pair <> ", 0")
      ovf <- freshReg
      emit (ovf <> " = extractvalue {i64, i1} " <> pair <> ", 1")
      okL <- freshLabel "sok_"
      escL <- freshLabel "sesc_"
      emit ("br i1 " <> ovf <> ", label %" <> escL <> ", label %" <> okL)
      startBlock escL
      flushAndGoto
      startBlock okL
      pure val
    divModOp isDiv ae be = do
      declRuntime "declare void @krt_fail(ptr)"
      zchk <- freshReg
      emit (zchk <> " = icmp eq i64 " <> be <> ", 0")
      trapL <- freshLabel "sdz_"
      contL <- freshLabel "sdc_"
      emit ("br i1 " <> zchk <> ", label %" <> trapL <> ", label %" <> contL)
      startBlock trapL
      msgG <- internCStr (if isDiv then "divInt: division by zero" else "modInt: division by zero")
      emit ("call void @krt_fail(ptr " <> msgG <> ")")
      emit "unreachable"
      startBlock contL
      minChk <- freshReg
      emit (minChk <> " = icmp eq i64 " <> ae <> ", -9223372036854775808")
      negOneChk <- freshReg
      emit (negOneChk <> " = icmp eq i64 " <> be <> ", -1")
      edge <- freshReg
      emit (edge <> " = and i1 " <> minChk <> ", " <> negOneChk)
      if isDiv
        then do
          escL <- freshLabel "sde_"
          okL <- freshLabel "sdo_"
          emit ("br i1 " <> edge <> ", label %" <> escL <> ", label %" <> okL)
          startBlock escL
          flushAndGoto
          startBlock okL
          r <- freshReg
          emit (r <> " = sdiv i64 " <> ae <> ", " <> be)
          pure r
        else do
          remL <- freshLabel "smr_"
          joinL <- freshLabel "smj_"
          curBlk <- gets gsBlock
          emit ("br i1 " <> edge <> ", label %" <> joinL <> ", label %" <> remL)
          startBlock remL
          rr <- freshReg
          emit (rr <> " = srem i64 " <> ae <> ", " <> be)
          emit ("br label %" <> joinL)
          startBlock joinL
          r <- freshReg
          emit (r <> " = phi i64 [ 0, %" <> curBlk <> " ], [ " <> rr <> ", %" <> remL <> " ]")
          pure r

scalarBodyLoopLL :: Map RefCellId Int -> Map RefCellId Text -> Gen () -> [ScalarAssignLoopLL] -> Gen ()
scalarBodyLoopLL cells slotOf flushAndGoto body =
  forM_ body $ \(ScalarAssignLoopLL cid env rhs) -> do
    v <- scalarI64ExprLoopLL cells env slotOf flushAndGoto rhs
    emit ("store i64 " <> v <> ", ptr " <> (slotOf Map.! cid) <> ", align 8")

scalarBoxedLoopLL :: Map RefCellId Int -> Map RefCellId Text -> ScalarCondLoopLL -> [ScalarAssignLoopLL] -> Text -> Gen ()
scalarBoxedLoopLL cells cellOf cond body doneL = do
  declRuntime "declare i32 @kas_bool(ptr)"
  declRuntime "declare ptr @kref_get(ptr)"
  declRuntime "declare ptr @kref_set(ptr, ptr)"
  declRuntime "declare i32 @krt2_safepoint()"
  spSlot <- freshReg
  emit (spSlot <> " = alloca i64, align 8")
  emit ("store i64 " <> scalarSpQuantumLL <> ", ptr " <> spSlot <> ", align 8")
  contL <- freshLabel "bxcont_"
  bodyL <- freshLabel "bxbody_"
  spchkL <- freshLabel "bxspchk_"
  abortL <- freshLabel "bxabort_"
  emit ("br label %" <> contL)
  startBlock contL
  cv <- boxedCondExprLL cells cellOf cond
  bb <- freshReg
  emit (bb <> " = call i32 @kas_bool(ptr " <> cv <> ")")
  bit <- freshReg
  emit (bit <> " = icmp ne i32 " <> bb <> ", 0")
  emit ("br i1 " <> bit <> ", label %" <> bodyL <> ", label %" <> doneL)
  startBlock bodyL
  forM_ body $ \(ScalarAssignLoopLL cid env rhs) -> do
    rv <- boxedExprLoopLL cells env cellOf rhs
    dump <- freshReg
    emit (dump <> " = call ptr @kref_set(ptr " <> (cellOf Map.! cid) <> ", ptr " <> rv <> ")")
  spCur <- freshReg
  emit (spCur <> " = load i64, ptr " <> spSlot <> ", align 8")
  spDec <- freshReg
  emit (spDec <> " = sub i64 " <> spCur <> ", 1")
  emit ("store i64 " <> spDec <> ", ptr " <> spSlot <> ", align 8")
  spGate <- freshReg
  emit (spGate <> " = icmp sle i64 " <> spDec <> ", 0")
  emit ("br i1 " <> spGate <> ", label %" <> spchkL <> ", label %" <> contL)
  startBlock spchkL
  emit ("store i64 " <> scalarSpQuantumLL <> ", ptr " <> spSlot <> ", align 8")
  spRc <- freshReg
  emit (spRc <> " = call i32 @krt2_safepoint()")
  spAbort <- freshReg
  emit (spAbort <> " = icmp ne i32 " <> spRc <> ", 0")
  emit ("br i1 " <> spAbort <> ", label %" <> abortL <> ", label %" <> contL)
  startBlock abortL
  declRuntime "declare void @krt2_scalar_abort()"
  emit "call void @krt2_scalar_abort()"
  emit "unreachable"

boxedCondExprLL :: Map RefCellId Int -> Map RefCellId Text -> ScalarCondLoopLL -> Gen Text
boxedCondExprLL cells cellOf (ScalarCondLoopLL env term) =
  boxedExprLoopLL cells env cellOf term

boxedExprLoopLL :: Map RefCellId Int -> Map Int RefCellId -> Map RefCellId Text -> BackendTerm -> Gen Text
boxedExprLoopLL cells env cellOf = goE
  where
    goE term = case scalarReadCellLL cells env term of
      Just cid -> do
        declRuntime "declare ptr @kref_get(ptr)"
        r <- freshReg
        emit (r <> " = call ptr @kref_get(ptr " <> (cellOf Map.! cid) <> ")")
        pure r
      Nothing -> case term of
        BLit _ (LitInt m)
          | i64InRangeLL m -> do
              declRuntime "declare ptr @kint(i64)"
              r <- freshReg
              emit (r <> " = call ptr @kint(i64 " <> T.pack (show m) <> ")")
              pure r
        _ -> case backendSpineOf term of
          (BGlob _ g, sargs) -> do
            mp <- globPrimName g
            case mp >>= boxedPrimSymLoopLL of
              Just sym -> do
                let expl = [argTerm a | a <- sargs, argIcit a == Expl]
                aes <- mapM goE expl
                declRuntime ("declare ptr @" <> sym <> "(" <> T.intercalate ", " (replicate (length aes) "ptr") <> ")")
                r <- freshReg
                emit (r <> " = call ptr @" <> sym <> "(" <> T.intercalate ", " ["ptr " <> a | a <- aes] <> ")")
                pure r
              Nothing -> escalateScalarLoopLL
          _ -> escalateScalarLoopLL

boxedPrimSymLoopLL :: Text -> Maybe Text
boxedPrimSymLoopLL = \case
  "addInt" -> Just "kp_addInt"
  "subInt" -> Just "kp_subInt"
  "mulInt" -> Just "kp_mulInt"
  "divInt" -> Just "kp_divInt"
  "modInt" -> Just "kp_modInt"
  "negInt" -> Just "kp_negInt"
  "eqInt" -> Just "kp_eqInt"
  "ltInt" -> Just "kp_ltInt"
  "leInt" -> Just "kp_leInt"
  _ -> Nothing

escalateScalarLoopLL :: Gen Text
escalateScalarLoopLL =
  unsupported
    "scalar-loop"
    "an int64-ineligible term reached the LLVM evidence-aware scalar loop (eligibility invariant violated)"

-- | A saturated self-call: spine head is the worker's own global @self@ with
-- exactly @n@ explicit runtime args (mirror of C's 'lr1SelfArgsBackend').
lr1SelfArgsLL :: GName -> Int -> BackendTerm -> Maybe [BackendTerm]
lr1SelfArgsLL self n term = case backendSpineOf term of
  (BGlob _ g, sargs)
    | g == self, expl <- [argTerm a | a <- sargs, argIcit a == Expl], length expl == n -> Just expl
  _ -> Nothing

-- | The kind of de Bruijn variable @i@ against a de-Bruijn-ordered local-kind
-- context @dks@ (index 0 = innermost; a 'CLet' prepends).  Mirror of C's
-- 'varParamKind' (post-§let widening).
varKindLL :: [ParamKindLL] -> Int -> Maybe ParamKindLL
varKindLL dks i = if i >= 0 && i < length dks then Just (dks !! i) else Nothing

-- | The per-parameter scalar kinds + (scalar) result kind of @g@ IF it is
-- eligible for an unboxed worker: ≥1 explicit relevant binder, a scalar type
-- telescope matching the binder count + a scalar result, at least one unboxed
-- scalar param, and a scalar-expressible body.  @Nothing@ ⇒ boxed-only (never a
-- miscompile).  Faithful port of C's 'scalarPlan' + 'typeScalarKinds'.
scalarFnPlanLL :: GName -> Gen (Maybe ([Bool], [ParamKindLL], ScalarKindLL, BackendTerm))
scalarFnPlanLL g = do
  bodies <- gets gsBackendBodies
  case Map.lookup g bodies of
    Nothing -> pure Nothing
    Just body -> do
      let params = bbParams body
          n = length params
      -- KBackendIR has already omitted erased binders. A scalar worker still
      -- requires every remaining runtime parameter to be explicit; implicit
      -- runtime dictionaries stay on the boxed path.
      if n >= 1 && all ((== Expl) . bpIcit) params
        then do
          mkinds <- typeScalarKindsLL g n
          case mkinds of
            -- require at least one unboxed scalar param + an ALL-scalar slot set
            -- (the LLVM port does not emit the mixed @kwm_@ boxed-slot worker;
            -- any boxed slot ⇒ stay on the boxed path).
            Just (mask, pks, ret)
              | any (/= PBoxedLL) pks
              , all (/= PBoxedLL) pks -> do
                  let scalarInner = bbRoot body
                  ok <- scalarEligTailLL g pks (reverse pks) ret scalarInner
                  pure (if ok then Just (mask, pks, ret, scalarInner) else Nothing)
            _ -> pure Nothing
        else pure Nothing

-- | Read @g@'s per-parameter + result scalar kinds from its elaborated type via
-- the shared 'Repr.repSelect' (the SAME authority the C backend's
-- 'typeScalarKinds' uses).  The result must be scalar; a count mismatch against
-- the body's binder count yields 'Nothing' (so a kind is never assigned to the
-- wrong binder).  Mirror of C's 'typeScalarKinds'.
typeScalarKindsLL :: GName -> Int -> Gen (Maybe ([Bool], [ParamKindLL], ScalarKindLL))
typeScalarKindsLL g n = do
  globals <- gets gsGlobals
  ctx <- gets gsEvalCtx
  pure $ case Map.lookup g globals of
    Nothing -> Nothing
    Just gd -> do
      mask <- Repr.runtimeParamMask ctx (gdType gd)
      (paramReps, retRep) <- Repr.repSelect ctx (gdType gd)
      ret <- repScalarKindLL retRep
      let pks = map (\r -> maybe PBoxedLL PScalarLL (repScalarKindLL r)) paramReps
      if length (filter id mask) == n && length pks == n
        then Just (mask, pks, ret)
        else Nothing

-- | Eligibility of a tail-position term (mirror of C's 'scalarEligTail',
-- including the §let widening): @if@ (eligible condition + branches), @let@ with
-- a scalar RHS (binder pushed onto @dks@), saturated self-call, or a leaf value
-- of the return kind.
scalarEligTailLL :: GName -> [ParamKindLL] -> [ParamKindLL] -> ScalarKindLL -> BackendTerm -> Gen Bool
scalarEligTailLL g pks dks ret term = case term of
  BIf _ c t e ->
    andMLL
      [ scalarEligCondLL g pks dks ret c
      , scalarEligTailLL g pks dks ret t
      , scalarEligTailLL g pks dks ret e
      ]
  BLet _ _ _ _ rhs body -> do
    mk <- scalarKindOfLL g pks dks ret rhs
    case mk of
      Just k -> scalarEligTailLL g pks (PScalarLL k : dks) ret body
      Nothing -> pure False
  _
    | Just args <- lr1SelfArgsLL g (length pks) term ->
        andMLL (zipWith (selfArgEligLL g pks dks ret) pks args)
    | otherwise -> scalarHasKindLL g pks dks ret ret term

-- | A self-call argument is eligible: a scalar slot wants a value of that scalar
-- kind (a boxed slot never arises — the plan rejects any 'PBoxedLL').  Mirror of
-- C's 'selfArgElig' restricted to the all-scalar worker.
selfArgEligLL :: GName -> [ParamKindLL] -> [ParamKindLL] -> ScalarKindLL -> ParamKindLL -> BackendTerm -> Gen Bool
selfArgEligLL g pks dks ret pk arg = case pk of
  PScalarLL k -> scalarHasKindLL g pks dks ret k arg
  PBoxedLL -> pure False

-- | Does the value-position @term@ have scalar kind @k@?  (Mirror of C's
-- 'scalarHasKind'; the boxed-field-projection coercion is C-only — there are no
-- boxed slots in an LLVM worker.)
scalarHasKindLL :: GName -> [ParamKindLL] -> [ParamKindLL] -> ScalarKindLL -> ScalarKindLL -> BackendTerm -> Gen Bool
scalarHasKindLL g pks dks ret k term = do
  mk <- scalarKindOfLL g pks dks ret term
  pure (mk == Just k)

-- | The scalar kind of a value-position expression, or 'Nothing' if not
-- scalar-expressible (every prim arg must match the prim's expected kind; a
-- self-call's result is the return kind; a scalar-RHS @let@ binds a scalar
-- binder for its body).  Mirror of C's 'scalarKindOf' (with the §let case).
scalarKindOfLL :: GName -> [ParamKindLL] -> [ParamKindLL] -> ScalarKindLL -> BackendTerm -> Gen (Maybe ScalarKindLL)
scalarKindOfLL g pks dks ret term = case term of
  BLit _ (LitInt m)
    | i64InRangeLL m -> pure (Just KInt64L)
    | otherwise -> pure Nothing
  BLit _ (LitDouble _) -> pure (Just KDoubleL)
  BVar _ _ i -> pure (varKindLL dks i >>= paramSKLL)
  BLet _ _ _ _ rhs body -> do
    mk <- scalarKindOfLL g pks dks ret rhs
    case mk of
      Just k -> scalarKindOfLL g pks (PScalarLL k : dks) ret body
      Nothing -> pure Nothing
  _ -> case backendSpineOf term of
    (BGlob _ h, sargs) -> do
      let expl = [argTerm a | a <- sargs, argIcit a == Expl]
      mp <- globPrimName h
      case mp of
        Just p | Just (rk, argks) <- arithPrimLL2 p, length expl == length argks -> do
          oks <- sequence (zipWith (scalarHasKindLL g pks dks ret) argks expl)
          pure (if and oks then Just rk else Nothing)
        _
          | Just args <- lr1SelfArgsLL g (length pks) term -> do
              oks <- sequence (zipWith (selfArgEligLL g pks dks ret) pks args)
              pure (if and oks then Just ret else Nothing)
          | otherwise -> pure Nothing
    _ -> pure Nothing

-- | Eligibility of an @if@ condition: a saturated safe scalar compare whose
-- operands have the comparison's operand kind.  Mirror of C's 'scalarEligCond'.
scalarEligCondLL :: GName -> [ParamKindLL] -> [ParamKindLL] -> ScalarKindLL -> BackendTerm -> Gen Bool
scalarEligCondLL g pks dks ret term = case backendSpineOf term of
  (BGlob _ h, sargs) -> do
    let expl = [argTerm a | a <- sargs, argIcit a == Expl]
    mp <- globPrimName h
    case (mp >>= cmpPrimLL2, expl) of
      (Just (_, opk), [a, b]) ->
        andMLL [scalarHasKindLL g pks dks ret opk a, scalarHasKindLL g pks dks ret opk b]
      _ -> pure False
  _ -> pure False

andMLL :: [Gen Bool] -> Gen Bool
andMLL = foldr (\m acc -> do b <- m; if b then acc else pure False) (pure True)

-- | The unboxed worker symbol: @kwi_@ for an all-@i64@ worker, @kwd_@ for one
-- with any @double@ slot/result (mirror of C's 'scalarWorkerName', minus the
-- mixed @kwm_@ case the LLVM port does not emit).
scalarFnWorkerNameLL :: GName -> [ParamKindLL] -> ScalarKindLL -> Text
scalarFnWorkerNameLL g pks ret
  | all (== PScalarLL KInt64L) pks && ret == KInt64L = "kwi_" <> mangle (gKey g)
  | otherwise = "kwd_" <> mangle (gKey g)

-- | Emit the unboxed worker @define internal <retTy> \@kw{i,d}_g(<scalar
-- params>, ptr %kovf)@ (mirror of C's 'compileScalarWorker').  Each param gets
-- an @i64@/@double@ stack slot (clang's mem2reg promotes them to SSA), the loop
-- body runs in tail position over those slots, a tail self-call stores the new
-- arg values and branches back to the loop header, a leaf returns the value, and
-- an int64 overflow sets @*%kovf = 1@ and returns a zero placeholder.
compileScalarFnWorkerLL :: GName -> [ParamKindLL] -> ScalarKindLL -> BackendTerm -> Gen ()
compileScalarFnWorkerLL g pks ret inner = do
  let n = length pks
      worker = scalarFnWorkerNameLL g pks ret
      retTy = llScalarTy ret
      paramDecl =
        T.intercalate ", " (zipWith (\k i -> pkTyLL k <> " %p" <> T.pack (show i)) pks [0 .. n - 1] ++ ["ptr %kovf"])
  (bodyInsns, _end, ()) <- captured "null" $ do
    -- one stack slot per param, initialised from the incoming param register.
    slots <- forM (zip [0 :: Int ..] pks) $ \(i, k) -> do
      sl <- freshReg
      emit (sl <> " = alloca " <> pkTyLL k <> ", align 8")
      emit ("store " <> pkTyLL k <> " %p" <> T.pack (show i) <> ", ptr " <> sl <> ", align 8")
      pure sl
    -- Each scalar 'let' binder also needs a slot because later CVar reads use
    -- the same de-Bruijn slot machinery as parameters. Reserve those slots in
    -- the worker entry block. Emitting the alloca at the syntactic let site
    -- places it inside the self-tail loop and grows the C stack every iteration.
    -- Current scalar kinds are Int64 and Double, both 8 bytes, so an i64 scratch
    -- alloca is a correctly-sized untyped slot under LLVM opaque pointers.
    letSlots <- replicateM (scalarLetSlotCountLL inner) $ do
      sl <- freshReg
      emit (sl <> " = alloca i64, align 8")
      pure sl
    modify' $ \st -> st {gsScalarLetSlots = letSlots}
    -- de-Bruijn slot/kind context: index 0 = innermost = LAST param (so @reverse@
    -- both the slot list and the kind list), parallel to C's @env = reverse ps@.
    let dslots = reverse slots
        dks = reverse pks
    loopL <- freshLabel "kwloop_"
    spc <- freshReg
    emit (spc <> " = alloca i64, align 8")
    emit ("store i64 " <> scalarSpQuantumLL <> ", ptr " <> spc <> ", align 8")
    emit ("br label %" <> loopL)
    startBlock loopL
    scalarFnTailLL g pks ret loopL spc dslots dks ret inner
  let def =
        T.unlines $
          ["define internal " <> retTy <> " @" <> worker <> "(" <> paramDecl <> ") {", "build:"]
            ++ map ("  " <>) bodyInsns
            ++ ["}"]
  modify' $ \st -> st {gsTop = def : gsTop st}

-- | A zero placeholder operand of the worker's return type (the value returned
-- after an overflow sets @*%kovf@ — the caller ignores it and re-runs boxed).
scalarZeroLL :: ScalarKindLL -> Text
scalarZeroLL KInt64L = "0"
scalarZeroLL KDoubleL = "0.0"

scalarLetSlotCountLL :: BackendTerm -> Int
scalarLetSlotCountLL = go
  where
    go = \case
      BVar {} -> 0
      BGlob {} -> 0
      BLam _ _ _ _ _ b -> go b
      BApp _ f args -> go f + sum (map (go . argTerm) args)
      BUnit {} -> 0
      BLit {} -> 0
      BCtor _ _ args -> sum (map go args)
      BMatch _ s alts _ -> go s + sum [maybe 0 go gd + go body | BackendAlt _ _ _ gd body <- alts]
      BRecord _ fs -> sum (map (go . snd) fs)
      BProj _ e _ _ -> go e
      BInject _ _ e -> go e
      BLet _ _ _ _ rhs body -> 1 + go rhs + go body
      BLetRec _ _ _ _ rhs body -> go rhs + go body
      BDo _ _ items -> sum (map goItem items)
      BSeal _ _ e -> go e
      BThunk _ e -> go e
      BLazy _ e -> go e
      BForce _ e -> go e
      BIf _ c t e -> go c + go t + go e
    goCond = \case
      BKCondPure t -> go t
      BKCondAction t -> go t
    goItem = \case
      BKBind _ _ _ _ t _ -> go t
      BKLet _ _ _ _ t -> go t
      BKLetQ _ _ _ t me -> go t + maybe 0 (\(_, _, body) -> go body) me
      BKExpr _ t -> go t
      BKVarItem _ _ initT t _ -> go initT + go t
      BKAssign _ _ rhs t _ -> go rhs + go t
      BKReturn _ t -> go t
      BKBreak _ _ -> 0
      BKContinue _ _ -> 0
      BKWhile _ _ c body me -> goCond c + sum (map goItem body) + maybe 0 (sum . map goItem) me
      BKFor _ _ _ _ src body me -> go src + sum (map goItem body) + maybe 0 (sum . map goItem) me
      BKIf _ alts me -> sum [go c + sum (map goItem body) | (c, body) <- alts] + maybe 0 (sum . map goItem) me
      BKDefer _ _ t -> go t
      BKUsing _ _ _ a r -> go a + go r
      BKSubDo _ _ items -> sum (map goItem items)

nextScalarLetSlotLL :: Gen Text
nextScalarLetSlotLL = do
  slots <- gets gsScalarLetSlots
  case slots of
    sl : rest -> modify' (\st -> st {gsScalarLetSlots = rest}) >> pure sl
    [] -> error "LLVM scalar worker let-slot preallocation undercount"

-- | Compile the worker body in TAIL position over the de-Bruijn slot/kind
-- context (@dslots@ : @ptr@ stack slots, @dks@ : their kinds — kept in
-- lock-step; a 'CLet' prepends to both).  Mirror of C's 'scalarTail' + its §let
-- case, lowered to LLVM blocks.
scalarFnTailLL :: GName -> [ParamKindLL] -> ScalarKindLL -> Text -> Text -> [Text] -> [ParamKindLL] -> ScalarKindLL -> BackendTerm -> Gen ()
scalarFnTailLL g pks ret loopHdr spc dslots dks loopRet term = case term of
  BIf _ c t e -> do
    cond <- scalarFnCondLL g pks ret dslots dks c
    thenL <- freshLabel "kwthen_"
    elseL <- freshLabel "kwelse_"
    emit ("br i1 " <> cond <> ", label %" <> thenL <> ", label %" <> elseL)
    startBlock thenL
    scalarFnTailLL g pks ret loopHdr spc dslots dks loopRet t
    startBlock elseL
    scalarFnTailLL g pks ret loopHdr spc dslots dks loopRet e
  BLet _ _ _ _ rhs body -> do
    k <- letScalarKindLL g pks dks ret rhs
    e <- scalarFnExprLL g pks ret dslots dks k rhs
    sl <- nextScalarLetSlotLL
    emit ("store " <> llScalarTy k <> " " <> e <> ", ptr " <> sl <> ", align 8")
    scalarFnTailLL g pks ret loopHdr spc (sl : dslots) (PScalarLL k : dks) loopRet body
  _
    | Just args <- lr1SelfArgsLL g (length pks) term -> do
        -- tail self-call: evaluate the new args into registers FIRST (they may
        -- read the current slots), THEN overwrite the param slots and loop.
        let n = length pks
            -- the param slots are the LAST n entries of @dslots@ (any lets are
            -- prepended at the front, so @drop (len-n)@ leaves exactly the params
            -- in de-Bruijn order param_{n-1}..param_0); @reverse@ puts them back in
            -- SOURCE order param_0..param_{n-1} to align with @pks@ / the args.
            paramSlots = reverse (drop (length dslots - n) dslots)
        newVals <- forM (zip pks args) $ \(pk, a) -> case pk of
          PScalarLL k -> scalarFnExprLL g pks ret dslots dks k a
          PBoxedLL -> escalateScalarLL
        forM_ (zip3 paramSlots pks newVals) $ \(sl, pk, v) ->
          emit ("store " <> maybe "i64" llScalarTy (paramSKLL pk) <> " " <> v <> ", ptr " <> sl <> ", align 8")
        emitScalarSafepointLL spc loopHdr loopRet
    | otherwise -> do
        e <- scalarFnExprLL g pks ret dslots dks loopRet term
        emit ("ret " <> llScalarTy loopRet <> " " <> e)

emitScalarSafepointLL :: Text -> Text -> ScalarKindLL -> Gen ()
emitScalarSafepointLL spc loopHdr ret = do
  declRuntime "declare i32 @krt2_safepoint()"
  old <- freshReg
  emit (old <> " = load i64, ptr " <> spc <> ", align 8")
  dec <- freshReg
  emit (dec <> " = sub i64 " <> old <> ", 1")
  emit ("store i64 " <> dec <> ", ptr " <> spc <> ", align 8")
  due <- freshReg
  emit (due <> " = icmp sle i64 " <> dec <> ", 0")
  checkL <- freshLabel "kwspcheck_"
  abortL <- freshLabel "kwspabort_"
  emit ("br i1 " <> due <> ", label %" <> checkL <> ", label %" <> loopHdr)
  startBlock checkL
  emit ("store i64 " <> scalarSpQuantumLL <> ", ptr " <> spc <> ", align 8")
  hit <- freshReg
  emit (hit <> " = call i32 @krt2_safepoint()")
  hitp <- freshReg
  emit (hitp <> " = icmp ne i32 " <> hit <> ", 0")
  emit ("br i1 " <> hitp <> ", label %" <> abortL <> ", label %" <> loopHdr)
  startBlock abortL
  emit ("store i32 " <> scalarAbortLL <> ", ptr %kovf, align 4")
  emit ("ret " <> llScalarTy ret <> " " <> scalarZeroLL ret)

-- | The scalar kind a let-RHS evaluates to (for the slot type), re-derived at
-- codegen.  Eligibility proved it 'Just'; default to @ret@ on the impossible
-- 'Nothing' (mirror of C's 'letScalarKind').
letScalarKindLL :: GName -> [ParamKindLL] -> [ParamKindLL] -> ScalarKindLL -> BackendTerm -> Gen ScalarKindLL
letScalarKindLL g pks dks ret rhs = do
  mk <- scalarKindOfLL g pks dks ret rhs
  pure (maybe ret id mk)

-- | Compile a scalar-expressible value to a native @i64@/@double@ register: a
-- literal, a slot read, an arith op, or a (non-tail) self-call (whose @%kovf@ is
-- checked immediately).  @dk@ is the demanded kind (only consulted to type a
-- literal/zero defensively; everything else is determined bottom-up).  Mirror of
-- C's 'scalarExpr'/'scalarExprBody'.
scalarFnExprLL :: GName -> [ParamKindLL] -> ScalarKindLL -> [Text] -> [ParamKindLL] -> ScalarKindLL -> BackendTerm -> Gen Text
scalarFnExprLL g pks ret dslots dks dk term = case term of
  BLit _ (LitInt m) -> pure (T.pack (show m))
  BLit _ (LitDouble d) -> pure ("0x" <> doubleBitsHex d)
  BVar _ _ i ->
    case (varKindLL dks i, drop i dslots) of
      (Just pk, sl : _) -> do
        let k = maybe ret id (paramSKLL pk)
        r <- freshReg
        emit (r <> " = load " <> llScalarTy k <> ", ptr " <> sl <> ", align 8")
        pure r
      _ -> escalateScalarLL
  BLet _ _ _ _ rhs body -> do
    k <- letScalarKindLL g pks dks ret rhs
    e <- scalarFnExprLL g pks ret dslots dks k rhs
    sl <- nextScalarLetSlotLL
    emit ("store " <> llScalarTy k <> " " <> e <> ", ptr " <> sl <> ", align 8")
    scalarFnExprLL g pks ret (sl : dslots) (PScalarLL k : dks) dk body
  _ -> case backendSpineOf term of
    (BGlob _ h, sargs) -> do
      let expl = [argTerm a | a <- sargs, argIcit a == Expl]
      mp <- globPrimName h
      case mp of
        Just p | Just (_, argks) <- arithPrimLL2 p, length expl == length argks ->
          scalarFnArithLL g pks ret dslots dks p (zip argks expl)
        _
          | Just args <- lr1SelfArgsLL g (length pks) term -> do
              aes <- forM (zip pks args) $ \(pk, a) -> case pk of
                PScalarLL k -> scalarFnExprLL g pks ret dslots dks k a
                PBoxedLL -> escalateScalarLL
              let worker = scalarFnWorkerNameLL g pks ret
                  callArgs =
                    T.intercalate ", " (zipWith (\pk a -> maybe "i64" llScalarTy (paramSKLL pk) <> " " <> a) pks aes ++ ["ptr %kovf"])
              r <- freshReg
              emit (r <> " = call " <> llScalarTy ret <> " @" <> worker <> "(" <> callArgs <> ")")
              -- propagate %kovf immediately: on overflow, return the placeholder.
              ovf <- freshReg
              emit (ovf <> " = load i32, ptr %kovf, align 4")
              ob <- freshReg
              emit (ob <> " = icmp ne i32 " <> ovf <> ", 0")
              escL <- freshLabel "kwcesc_"
              okL <- freshLabel "kwcok_"
              emit ("br i1 " <> ob <> ", label %" <> escL <> ", label %" <> okL)
              startBlock escL
              emit ("ret " <> llScalarTy ret <> " " <> scalarZeroLL ret)
              startBlock okL
              pure r
          | otherwise -> escalateScalarLL
    _ -> escalateScalarLL

-- | Lower one scalar arith op to a native @i64@/@double@ register.  Int ops use
-- the @llvm.s{add,sub,mul}.with.overflow.i64@ intrinsics (overflow sets @*%kovf@
-- and returns the placeholder — the §6 GMP escape); div/mod trap on zero and
-- escape on the INT64_MIN/-1 edge; double ops are plain IEEE (@fadd@/@fmul@/…,
-- no escape — they wrap to ±inf/NaN exactly like the boxed prim); @intToDouble@
-- is @sitofp@.  Mirror of C's 'scalarArith' (same per-op rounding — each op is
-- its own SSA instruction, never fused into an FMA).
scalarFnArithLL :: GName -> [ParamKindLL] -> ScalarKindLL -> [Text] -> [ParamKindLL] -> Text -> [(ScalarKindLL, BackendTerm)] -> Gen Text
scalarFnArithLL g pks ret dslots dks p argspec = do
  aes <- forM argspec $ \(k, a) -> scalarFnExprLL g pks ret dslots dks k a
  case (p, aes) of
    ("addInt", [a, b]) -> ovfOp "sadd" a b
    ("subInt", [a, b]) -> ovfOp "ssub" a b
    ("mulInt", [a, b]) -> ovfOp "smul" a b
    ("negInt", [a]) -> ovfOp "ssub" "0" a
    ("divInt", [a, b]) -> divModOpLL True a b
    ("modInt", [a, b]) -> divModOpLL False a b
    ("addDouble", [a, b]) -> fpOp "fadd" a b
    ("subDouble", [a, b]) -> fpOp "fsub" a b
    ("mulDouble", [a, b]) -> fpOp "fmul" a b
    ("divDouble", [a, b]) -> fpOp "fdiv" a b
    ("negDouble", [a]) -> do
      r <- freshReg
      emit (r <> " = fneg double " <> a)
      pure r
    ("intToDouble", [a]) -> do
      r <- freshReg
      emit (r <> " = sitofp i64 " <> a <> " to double")
      pure r
    _ -> escalateScalarLL
  where
    fpOp op a b = do
      r <- freshReg
      emit (r <> " = " <> op <> " double " <> a <> ", " <> b)
      pure r
    -- an overflow-checked int op: on the overflow bit, set *%kovf and return the
    -- placeholder (the worker bails — the call site re-runs boxed).
    ovfOp pfx a b = do
      declRuntime ("declare {i64, i1} @llvm." <> pfx <> ".with.overflow.i64(i64, i64)")
      pair <- freshReg
      emit (pair <> " = call {i64, i1} @llvm." <> pfx <> ".with.overflow.i64(i64 " <> a <> ", i64 " <> b <> ")")
      val <- freshReg
      emit (val <> " = extractvalue {i64, i1} " <> pair <> ", 0")
      ovf <- freshReg
      emit (ovf <> " = extractvalue {i64, i1} " <> pair <> ", 1")
      escL <- freshLabel "kwoesc_"
      okL <- freshLabel "kwook_"
      emit ("br i1 " <> ovf <> ", label %" <> escL <> ", label %" <> okL)
      startBlock escL
      emit ("store i32 " <> scalarOverflowLL <> ", ptr %kovf, align 4")
      emit ("ret " <> llScalarTy ret <> " " <> scalarZeroLL ret)
      startBlock okL
      pure val
    divModOpLL isDiv a b = do
      declRuntime "declare void @krt_fail(ptr)"
      zchk <- freshReg
      emit (zchk <> " = icmp eq i64 " <> b <> ", 0")
      trapL <- freshLabel "kwdz_"
      contL <- freshLabel "kwdc_"
      emit ("br i1 " <> zchk <> ", label %" <> trapL <> ", label %" <> contL)
      startBlock trapL
      msgG <- internCStr (if isDiv then "divInt: division by zero" else "modInt: division by zero")
      emit ("call void @krt_fail(ptr " <> msgG <> ")")
      emit "unreachable"
      startBlock contL
      minChk <- freshReg
      emit (minChk <> " = icmp eq i64 " <> a <> ", -9223372036854775808")
      negOneChk <- freshReg
      emit (negOneChk <> " = icmp eq i64 " <> b <> ", -1")
      edge <- freshReg
      emit (edge <> " = and i1 " <> minChk <> ", " <> negOneChk)
      if isDiv
        then do
          escL <- freshLabel "kwde_"
          okL <- freshLabel "kwdo_"
          emit ("br i1 " <> edge <> ", label %" <> escL <> ", label %" <> okL)
          startBlock escL
          emit ("store i32 " <> scalarOverflowLL <> ", ptr %kovf, align 4")
          emit ("ret " <> llScalarTy ret <> " " <> scalarZeroLL ret)
          startBlock okL
          r <- freshReg
          emit (r <> " = sdiv i64 " <> a <> ", " <> b)
          pure r
        else do
          remL <- freshLabel "kwmr_"
          joinL <- freshLabel "kwmj_"
          curBlk <- gets gsBlock
          emit ("br i1 " <> edge <> ", label %" <> joinL <> ", label %" <> remL)
          startBlock remL
          rr <- freshReg
          emit (rr <> " = srem i64 " <> a <> ", " <> b)
          emit ("br label %" <> joinL)
          startBlock joinL
          r <- freshReg
          emit (r <> " = phi i64 [ 0, %" <> curBlk <> " ], [ " <> rr <> ", %" <> remL <> " ]")
          pure r

-- | Compile an @if@ condition (a saturated safe scalar compare) to an @i1@.  The
-- compare op-class + predicate come from 'cmpPrimLL2' (icmp for Int, fcmp for the
-- two admitted Double compares).  Mirror of C's 'scalarCond'.
scalarFnCondLL :: GName -> [ParamKindLL] -> ScalarKindLL -> [Text] -> [ParamKindLL] -> BackendTerm -> Gen Text
scalarFnCondLL g pks ret dslots dks term = case backendSpineOf term of
  (BGlob _ h, sargs) -> do
    let expl = [argTerm a | a <- sargs, argIcit a == Expl]
    mp <- globPrimName h
    case (mp >>= cmpPrimLL2, expl) of
      (Just (cmpOp, opk), [a, b]) -> do
        ae <- scalarFnExprLL g pks ret dslots dks opk a
        be <- scalarFnExprLL g pks ret dslots dks opk b
        r <- freshReg
        emit (r <> " = " <> cmpOp <> " " <> llScalarTy opk <> " " <> ae <> ", " <> be)
        pure r
      _ -> escalateScalarLL >> pure "0"
  _ -> escalateScalarLL >> pure "0"

-- | Emit (once per module) the @.ll@-local tag-checked arg-unbox helpers, the
-- LLVM analogue of the C runtime's @kunbox_i64@/@kunbox_dbl@ — which are
-- @static inline@ in @kappart.h@ (so they have NO linkable symbol the @.ll@
-- could call).  We therefore SYNTHESISE them in IR using only LINKABLE runtime
-- functions, with the SAME tag-checked escape semantics, so an out-of-range Int
-- argument falls back to the boxed/GMP path exactly as the C worker does (no
-- abort, no divergence):
--
--   * @kunbox_i64_ll(v, ovf)@: an Int that fits i64 returns its value; anything
--     else sets @*ovf@.  Fit is decided WITHOUT aborting: @kas_u64@ never traps
--     (it wraps a bignum to its low 64 bits), so reboxing those bits with @kint@
--     and comparing to the original via @klit_eq@ is true IFF the value already
--     fit i64 (a non-fitting K_BIGINT reboxes to a DIFFERENT number ⇒ escape).
--     @kis_int_any@ first rejects any non-Int (a defensive guard; a type-checked
--     Int param never hits it).
--   * @kunbox_dbl_ll(v, ovf)@: mirrors @kunbox_dbl@'s wrong-tag ESCAPE via the
--     linkable runtime wrapper, rather than @kas_dbl@'s aborting assertion.
emitScalarUnboxHelpersLL :: Gen ()
emitScalarUnboxHelpersLL = do
  done <- gets gsScalarHelpers
  unless ("kunbox_i64_ll" `Set.member` done) $ do
    modify' $ \st -> st {gsScalarHelpers = Set.insert "kunbox_i64_ll" (gsScalarHelpers st)}
    declRuntime "declare i32 @kis_int_any(ptr)"
    declRuntime "declare i64 @kas_u64(ptr)"
    declRuntime "declare ptr @kint(i64)"
    declRuntime "declare i32 @klit_eq(ptr, ptr)"
    declRuntime "declare double @kunbox_dbl_runtime(ptr, ptr)"
    let i64Helper =
          T.unlines
            [ "define internal i64 @kunbox_i64_ll(ptr %v, ptr %ovf) {"
            , "entry:"
            , "  %isint = call i32 @kis_int_any(ptr %v)"
            , "  %notint = icmp eq i32 %isint, 0"
            , "  br i1 %notint, label %esc, label %chk"
            , "chk:"
            , "  %u = call i64 @kas_u64(ptr %v)"
            , "  %rebox = call ptr @kint(i64 %u)"
            , "  %same = call i32 @klit_eq(ptr %v, ptr %rebox)"
            , "  %bad = icmp eq i32 %same, 0"
            , "  br i1 %bad, label %esc, label %ok"
            , "ok:"
            , "  ret i64 %u"
            , "esc:"
            , "  store i32 " <> scalarOverflowLL <> ", ptr %ovf, align 4"
            , "  ret i64 0"
            , "}"
            ]
        dblHelper =
          T.unlines
            [ "define internal double @kunbox_dbl_ll(ptr %v, ptr %ovf) {"
            , "entry:"
            , "  %d = call double @kunbox_dbl_runtime(ptr %v, ptr %ovf)"
            , "  ret double %d"
            , "}"
            ]
    modify' $ \st -> st {gsTop = dblHelper : i64Helper : gsTop st}

-- | The saturated fast path at a call site (mirror of C's 'compileScalarCall'):
-- unbox each arg by its scalar kind (a wrong tag sets @ovf@), call the unboxed
-- worker, and select the boxed result (the curried @kg_@/@kapp@/@ktrampoline@
-- chain over the ORIGINAL boxed args) on a wrong-tag arg OR an int64 overflow,
-- else re-box the worker's scalar result.
compileScalarFnCallLL :: GName -> [ParamKindLL] -> ScalarKindLL -> [BackendArg] -> [Int] -> Gen Text
compileScalarFnCallLL g pks ret sargs runtimeIdxs = do
  emitScalarUnboxHelpersLL
  let worker = scalarFnWorkerNameLL g pks ret
  -- compile the boxed args once (used to unbox AND as the boxed-escape inputs).
  boxed <- mapM (compileErasableArg . argTerm) sargs
  let runtimeBoxed = [boxed !! i | i <- runtimeIdxs, i >= 0, i < length boxed]
  -- a stack i32 for the unbox/overflow flag.
  ovfSlot <- freshReg
  emit (ovfSlot <> " = alloca i32, align 4")
  emit ("store i32 0, ptr " <> ovfSlot <> ", align 4")
  -- unbox each scalar slot via the @.ll@-local tag-checked helper (sets *ovfSlot
  -- on a wrong/out-of-range arg — the soundness net, mirroring C's @kunbox_*@).
  uvs <- forM (zip pks runtimeBoxed) $ \(pk, bx) -> case pk of
    PScalarLL KInt64L -> do
      r <- freshReg
      emit (r <> " = call i64 @kunbox_i64_ll(ptr " <> bx <> ", ptr " <> ovfSlot <> ")")
      pure r
    PScalarLL KDoubleL -> do
      r <- freshReg
      emit (r <> " = call double @kunbox_dbl_ll(ptr " <> bx <> ", ptr " <> ovfSlot <> ")")
      pure r
    PBoxedLL -> pure bx -- never happens (plan rejects boxed slots)
  -- the boxed escape: kapp the original boxed args onto the curried global, then
  -- drive any tail-call bounce to a value.  (Computed lazily as a block only on
  -- the escape path so the common fast path does not build the closure chain.)
  -- A wrong-tag arg short-circuits to boxed WITHOUT calling the worker.
  preOvf <- freshReg
  emit (preOvf <> " = load i32, ptr " <> ovfSlot <> ", align 4")
  preBad <- freshReg
  emit (preBad <> " = icmp ne i32 " <> preOvf <> ", 0")
  fastL <- freshLabel "kwfast_"
  boxedL <- freshLabel "kwboxed_"
  joinL <- freshLabel "kwjoin_"
  emit ("br i1 " <> preBad <> ", label %" <> boxedL <> ", label %" <> fastL)
  -- fast path: call the unboxed worker; on overflow fall through to boxed.
  startBlock fastL
  let callArgs =
        T.intercalate ", " (zipWith (\pk v -> maybe "i64" llScalarTy (paramSKLL pk) <> " " <> v) pks uvs ++ ["ptr " <> ovfSlot])
  wres <- freshReg
  emit (wres <> " = call " <> llScalarTy ret <> " @" <> worker <> "(" <> callArgs <> ")")
  postOvf <- freshReg
  emit (postOvf <> " = load i32, ptr " <> ovfSlot <> ", align 4")
  postAbort <- freshReg
  emit (postAbort <> " = icmp eq i32 " <> postOvf <> ", " <> scalarAbortLL)
  abortL <- freshLabel "kwabort_"
  postCheckL <- freshLabel "kwpost_"
  emit ("br i1 " <> postAbort <> ", label %" <> abortL <> ", label %" <> postCheckL)
  startBlock abortL
  declRuntime "declare void @krt2_scalar_abort()"
  emit "call void @krt2_scalar_abort()"
  emit "unreachable"
  startBlock postCheckL
  postBad <- freshReg
  emit (postBad <> " = icmp ne i32 " <> postOvf <> ", 0")
  reboxL <- freshLabel "kwrebox_"
  emit ("br i1 " <> postBad <> ", label %" <> boxedL <> ", label %" <> reboxL)
  -- re-box the worker's scalar result.
  startBlock reboxL
  boxedRes <- case ret of
    KInt64L -> do
      declRuntime "declare ptr @kint(i64)"
      r <- freshReg
      emit (r <> " = call ptr @kint(i64 " <> wres <> ")")
      pure r
    KDoubleL -> do
      declRuntime "declare ptr @kdbl(double)"
      r <- freshReg
      emit (r <> " = call ptr @kdbl(double " <> wres <> ")")
      pure r
  reboxBlk <- gets gsBlock
  emit ("br label %" <> joinL)
  -- boxed escape: the curried global applied to the ORIGINAL boxed args, driven
  -- to a value through ktrampoline.  Reached from a wrong-tag arg (preFastBlk)
  -- and from a worker overflow (fastL).
  startBlock boxedL
  gv <- compileGlob g
  applied <- foldM (\acc bx -> do
      declRuntime "declare ptr @kapp(ptr, ptr)"
      r <- freshReg
      emit (r <> " = call ptr @kapp(ptr " <> acc <> ", ptr " <> bx <> ")")
      pure r) gv boxed
  declRuntime "declare ptr @ktrampoline(ptr)"
  boxedDriven <- freshReg
  emit (boxedDriven <> " = call ptr @ktrampoline(ptr " <> applied <> ")")
  boxedBlk <- gets gsBlock
  emit ("br label %" <> joinL)
  -- join: the boxed-escape value or the re-boxed worker result.
  startBlock joinL
  r <- freshReg
  emit (r <> " = phi ptr [ " <> boxedDriven <> ", %" <> boxedBlk <> " ], [ " <> boxedRes <> ", %" <> reboxBlk <> " ]")
  pure r

-- | A short name for the unsupported construct (for the diagnostic detail).
constructName :: BackendTerm -> Text
constructName = \case
  BVar {} -> "variable"
  BLam {} -> "lambda"
  BCtor {} -> "constructor"
  BIf {} -> "if"
  BMatch {} -> "match"
  BLet {} -> "let"
  BLetRec {} -> "letrec"
  BDo {} -> "do"
  BRecord {} -> "record"
  BProj {} -> "projection"
  BInject {} -> "variant-inject"
  BForce {} -> "force"
  BThunk {} -> "delay"
  BLazy {} -> "memo"
  BSeal {} -> "seal"
  BUnit {} -> "unit"
  BGlob {} -> "global"
  BLit {} -> "literal"
  BApp {} -> "application"
  _ -> "term"

compileLit :: Literal -> Gen Text
compileLit = \case
  LitStr s -> internStr s
  LitGrapheme g -> internStr g
  -- §6 Integer is arbitrary-precision.  An in-range literal is an inline
  -- @kint(i64)@; one beyond int64 is a runtime bignum built from its decimal
  -- text via @kbigint_str@ — the SAME split the C backend makes ('compileLit'
  -- in "Kappa.Backend.C": @kint(...)@ vs @kbigint_str("...")@), so big-Integer
  -- literals stay at parity.
  LitInt n
    | n >= toInteger (minBound :: Int) && n <= toInteger (maxBound :: Int) ->
        compileInt n
    | otherwise -> compileBigInt n
  -- Milestone I: Char/Byte/Double literal VALUES (the literal PATTERN forms
  -- already exist in 'litValueLL').  Char and Byte reuse that lowering verbatim
  -- (@kchr@ / @kbyte@).  Double is the parity hazard — see 'compileDbl'.
  LitScalar c -> compileScalar c
  LitByte w -> compileByte w
  LitDouble d -> compileDbl d
  l ->
    unsupported "literal"
      ("the LLVM backend supports String, Int, Char, Byte, and Double literals, not "
        <> litName l)

-- | An in-range Integer literal: @call ptr \@kint(i64 N)@.  LLVM i64 literals
-- accept plain signed decimal (including @-9223372036854775808@ for
-- @INT64_MIN@), so no @INT64_MIN@/@LL@ macro dance is needed — the value is the
-- same as C's 'cIntLit'.
compileInt :: Integer -> Gen Text
compileInt n = do
  declRuntime "declare ptr @kint(i64)"
  r <- freshReg
  emit (r <> " = call ptr @kint(i64 " <> T.pack (show n) <> ")")
  pure r

-- | An out-of-int64 Integer literal: @call ptr \@kbigint_str(ptr \@.cstr.N)@
-- over a NUL-terminated decimal C string (mirrors C's @kbigint_str("…")@).
-- Uses a dedicated NUL-terminated constant pool ('internCStr') because
-- @kbigint_str@ wants a @const char *@, not a length-carrying @KValue*@.
compileBigInt :: Integer -> Gen Text
compileBigInt n = do
  ptrG <- internCStr (T.pack (show n))
  declRuntime "declare ptr @kbigint_str(ptr)"
  r <- freshReg
  emit (r <> " = call ptr @kbigint_str(ptr " <> ptrG <> ")")
  pure r

-- | A Char (Unicode scalar) literal value: @call ptr \@kchr(i32 <ord c>)@ — the
-- SAME builder the C backend's @kchr(<ord c>)@ and the literal-PATTERN path
-- ('litValueLL') use.
compileScalar :: Char -> Gen Text
compileScalar c = do
  declRuntime "declare ptr @kchr(i32)"
  r <- freshReg
  emit (r <> " = call ptr @kchr(i32 " <> T.pack (show (ord c)) <> ")")
  pure r

-- | A Byte (octet) literal value: @call ptr \@kbyte(i8 <w>)@ — the SAME builder
-- the C backend's @kbyte(<w>)@ and the literal-PATTERN path ('litValueLL') use.
compileByte :: Word8 -> Gen Text
compileByte w = do
  declRuntime "declare ptr @kbyte(i8)"
  r <- freshReg
  emit (r <> " = call ptr @kbyte(i8 " <> T.pack (show (fromIntegral w :: Int)) <> ")")
  pure r

-- | A Double literal value: @call ptr \@kdbl(double 0xHHHHHHHHHHHHHHHH)@.
--
-- PARITY HAZARD.  The C backend lowers @LitDouble d@ to @kdbl(<show d>)@ — a
-- decimal whose exact value depends on the C compiler's @strtod@.  Emitting the
-- same decimal text into LLVM IR is NOT guaranteed to parse to the identical
-- 'Double': LLVM's literal parser and the C @strtod@ are independent
-- implementations, and a decimal that round-trips a 'Double' need not be the
-- shortest one each rounds back.  LLVM IR therefore accepts (and the LLVM
-- reference recommends) a HEX float literal — @double 0x@ followed by the raw
-- IEEE-754 big-endian bits — which denotes an EXACT 'Double' with no decimal
-- re-rounding.  We bit-cast the Haskell 'Double' to its 64 IEEE-754 bits
-- ('doubleBitsHex') and emit those, so the boxed value is bit-identical to the
-- C backend's regardless of how @strtod@ rounded the decimal.  (Haskell's
-- 'castDoubleToWord64' uses the platform IEEE-754 representation, the same one
-- the C runtime's @double@ uses.)
compileDbl :: Double -> Gen Text
compileDbl d = do
  declRuntime "declare ptr @kdbl(double)"
  r <- freshReg
  emit (r <> " = call ptr @kdbl(double 0x" <> doubleBitsHex d <> ")")
  pure r

-- | The 16-hex-digit, UPPERCASE, zero-padded big-endian IEEE-754 bit pattern of
-- a 'Double' — the operand LLVM expects after @double 0x@ for an exact
-- (non-decimal) floating literal.  'castDoubleToWord64' is the platform's
-- IEEE-754 reinterpret, so the bits are exactly those the C @double@ holds.
doubleBitsHex :: Double -> Text
doubleBitsHex d =
  let bits = castDoubleToWord64 d
      h = T.toUpper (T.pack (showHex bits ""))
   in T.justifyRight 16 '0' h

litName :: Literal -> Text
litName = \case
  LitInt {} -> "Int"
  LitDouble {} -> "Double"
  LitStr {} -> "String"
  LitScalar {} -> "Char"
  LitByte {} -> "Byte"
  LitBytes {} -> "Bytes"
  LitGrapheme {} -> "Grapheme"

-- | Build a 'CPLit' pattern's literal as a 'KValue*' comparand for @klit_eq@
-- (the analogue of C's 'litValue').  An 'Int' (in-range @kint@ / out-of-range
-- @kbigint_str@) and a 'String'\/'Grapheme' are exactly the value forms
-- 'compileLit' already builds, so this reuses it; 'Char' is @kchr@ and 'Byte'
-- is @kbyte@, the same runtime builders the C backend uses.  'Double' and
-- 'Bytes' literal patterns are NOT yet lowered here — building an LLVM
-- floating-point\/byte-buffer constant is its own hazard (the LLVM value path
-- 'compileLit' doesn't build them either) — so they record a clean unsupported
-- finding and return 'Nothing' (the alt then compiles to a constant-false test,
-- never a miscompile).  Other backends key parity off 'klit_eq', so an Int/
-- String/Char/Byte literal pattern matches the C backend bit-for-bit.
litValueLL :: Literal -> Gen (Maybe Text)
litValueLL = \case
  LitInt n -> Just <$> compileLit (LitInt n)
  LitStr s -> Just <$> compileLit (LitStr s)
  LitGrapheme g -> Just <$> compileLit (LitGrapheme g)
  LitScalar c -> Just <$> compileScalar c
  LitByte w -> Just <$> compileByte w
  l -> do
    _ <- unsupported "pattern"
      ( "the LLVM backend (Milestone F) lowers Int/String/Char/Byte literal "
          <> "patterns, not a " <> litName l <> " literal pattern (use the C backend)"
      )
    pure Nothing

-- | A bare global reference.  A prelude @prim@ registration / @__prim@ name is
-- a primitive: as a VALUE (used unsaturated — e.g. passed to a higher-order
-- function, or partially applied) it is built as a curried native closure
-- ('compilePrimValue', Milestone D).  Any other global is a CAF: emit a call to
-- its accessor and enqueue it.
compileGlob :: GName -> Gen Text
compileGlob g@(GName m nm)
  | m == primModule = compilePrimValue nm
  | otherwise = do
      globals <- gets gsGlobals
      hostSyms <- gets gsHostSyms
      case Map.lookup g globals of
        Just gd | Just (VPrim pname _) <- gdValue gd -> compilePrimValue pname
        -- Milestone L (§27.1.1): a provided host-binding member is lowered like
        -- a PRIM over its codegen-emitted C wrapper — a CURRIED native closure
        -- ('knative' over 'wrapperCName', IO since native bindings are UIO).
        -- Recognised HERE at the reference (mirrors C's 'emitHostNative' at the
        -- 'compileGlob' site), so it is never enqueued as a no-core-body CAF
        -- (the 'emitGlobal' no-core-body rejection — the delve "(definition)"
        -- errors).  A saturated reference takes the 'knative_sat' fast path in
        -- 'compileApp'.
        _ | Just rns <- Map.lookup g hostSyms -> compileHostValue rns
        _ -> do
          enqueue g
          let ident = cGlobIdent g
          -- No forward @declare@: the accessor is enqueued and emitted as a
          -- @define internal@ in THIS module, and LLVM resolves an intra-module
          -- call by name regardless of definition order.  A @declare@ here would
          -- be an external-linkage prototype that CLASHES with the later
          -- @define internal@ (an "invalid redefinition") — so it is omitted.
          r <- freshReg
          emit (r <> " = call ptr @" <> ident <> "()")
          pure r

-- | A primitive used as a VALUE (Milestone D): build the curried native closure
-- @knative(\@kpf_*, arity, name, isio)@ — the same closure the C backend's
-- 'emitPrim' builds (C.hs:1642), which @kapp@ then drives one argument at a time
-- (so partial application of a prim, or passing a prim to a higher-order
-- function, works).  A prim outside the lowered set ('primNativeEntry') is a
-- clean @E_BACKEND_UNSUPPORTED@.
compilePrimValue :: Text -> Gen Text
-- §18.1.12 `poll` is a 0-arity IO action that IS the OP_POLL node; a bare
-- reference lowers to the node builder directly (no curried @kpf_poll@ wrapper),
-- mirroring the C backend's 'emitPrim' special case.
compilePrimValue "poll" = do
  declRuntime "declare ptr @krt2_poll()"
  r <- freshReg
  emit (r <> " = call ptr @krt2_poll()")
  pure r
compilePrimValue pname = case primNativeEntry pname of
  -- A 0-arity PURE prim is a CONSTANT (e.g. @__bytesEmpty@): there is nothing to
  -- curry, so the C backend fires it immediately (@cfn((KValue **)0)@,
  -- C.hs:1619–1620) rather than wrapping a closure.  Mirror that exactly — a
  -- direct call on the @kpf_*@ wrapper with a NULL argument array.
  Just (cfn, 0, False) -> do
    declRuntime ("declare ptr @" <> cfn <> "(ptr)")
    r <- freshReg
    emit (r <> " = call ptr @" <> cfn <> "(ptr null)")
    pure r
  Just (cfn, ar, isio) -> do
    declRuntime "declare ptr @knative(ptr, i32, ptr, i32)"
    declRuntime ("declare ptr @" <> cfn <> "(ptr)")
    nameG <- internCStr pname
    r <- freshReg
    emit (r <> " = call ptr @knative(ptr @" <> cfn <> ", i32 " <> T.pack (show ar)
            <> ", ptr " <> nameG <> ", i32 " <> (if isio then "1" else "0") <> ")")
    pure r
  Nothing ->
    unsupported "primitive"
      ("the LLVM backend does not implement the primitive '" <> pname
        <> "' as a curried value; use the C backend")

-- | Milestone L (§27.1.1): a host-binding member used as a VALUE (a bare /
-- partial reference) lowers exactly like 'compilePrimValue', but over the
-- codegen-emitted C-wrapper symbol ('wrapperCName') instead of a runtime
-- @kpf_*@.  The wrapper has the @KValue *(KValue **)@ prim shape, so @knative@
-- drives it one argument at a time (so partial application / passing the binding
-- to a higher-order function works); arity = the C signature's parameter count;
-- isio = 1 because a native binding is conservatively typed in @UIO@ (the action
-- is suspended, fired by @krun_io@).  Mirrors C's 'emitHostNative' (C.hs:1637).
-- The wrapper is DEFINED in the Driver's sidecar @.c@ and linked in, so a forward
-- @declare@ of the external symbol is all the @.ll@ needs.
compileHostValue :: ResolvedNativeSymbol -> Gen Text
compileHostValue rns = do
  let cfn = wrapperCName rns
      ar = length (rns.params)
  ctor <- hostNativeCtor rns
  declRuntime ("declare ptr @" <> ctor <> "(ptr, i32, ptr, i32)")
  declRuntime ("declare ptr @" <> cfn <> "(ptr)")
  nameG <- internCStr (rns.cSymbol)
  r <- freshReg
  emit (r <> " = call ptr @" <> ctor <> "(ptr @" <> cfn <> ", i32 " <> T.pack (show ar)
          <> ", ptr " <> nameG <> ", i32 1)")
  pure r

hostNativeCtor :: ResolvedNativeSymbol -> Gen Text
hostNativeCtor rns = case rns.ffiClass of
  FfiNonblocking -> pure "knative"
  FfiBlocking -> pure "knative_blocking"
  FfiBlockingCancellable ->
    unsupported "native binding"
      ("the LLVM backend does not implement cancellable blocking calls for '"
        <> rns.cSymbol <> "'")

hostNativeSatCtor :: ResolvedNativeSymbol -> Gen Text
hostNativeSatCtor rns = case rns.ffiClass of
  FfiNonblocking -> pure "knative_sat"
  FfiBlocking -> pure "knative_sat_blocking"
  FfiBlockingCancellable ->
    unsupported "native binding"
      ("the LLVM backend does not implement cancellable blocking calls for '"
        <> rns.cSymbol <> "'")

blockingHostGlobals :: Map GName ResolvedNativeSymbol -> Set GName
blockingHostGlobals =
  Map.keysSet . Map.filter (isBlockingClass . (.ffiClass))
  where
    isBlockingClass = \case
      FfiNonblocking -> False
      FfiBlocking -> True
      FfiBlockingCancellable -> True

backendSpineOf :: BackendTerm -> (BackendTerm, [BackendArg])
backendSpineOf = \case
  BApp _ hd args -> (hd, args)
  t -> (t, [])

backendHeadGlob :: BackendTerm -> Maybe GName
backendHeadGlob = \case
  BGlob _ g -> Just g
  BApp _ f _ -> backendHeadGlob f
  BSeal _ _ e -> backendHeadGlob e
  _ -> Nothing

backendMetaOf :: BackendTerm -> BackendMeta
backendMetaOf = \case
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

-- | Compile an application.  A saturated application whose head is a known
-- primitive lowers per its kind: an IO prim to @knative_sat@ (M0, the §2.3
-- lowering); a PURE first-order prim with a direct @kp_*@ helper to a direct
-- positional call (M1, mirroring C's 'primDirect' fast path).  A saturated
-- application whose head is an arity-≥1 global, or an under-/over-saturated
-- prim, is out of Milestone-A scope (general @kapp@/closures are Milestone C)
-- and reported.
compileApp :: BackendTerm -> Gen Text
compileApp term
  -- §10.1/P0-A: a saturated application of an ETA-EXPANDED constructor — the
  -- @CApp (… (CLam … (CCtor g [CVar…]))) args@ shape elaboration produces for a
  -- field-carrying constructor occurrence ('etaCtorApp') — beta-reduces to a
  -- direct 'compileCtor'.  This is REQUIRED for Milestone C: a literal @Some 7@
  -- or @Pair a b@ in source arrives here as that redex (only nullary ctors come
  -- through as a bare 'CCtor'), so without it 'match'-on-a-constructed-value and
  -- every field-carrying construction would fall to the unsupported head path.
  | Just (g, ctorArgs) <- etaCtorApp term = compileCtor g ctorArgs
compileApp term0 = do
  let term = term0
      (hd, sargs) = backendSpineOf term
  case hd of
    BGlob _ g -> do
      hostSyms <- gets gsHostSyms
      case Map.lookup g hostSyms of
        -- Milestone L (§27.1.1): a SATURATED host-member application is a DIRECT
        -- native action — build the arg array and call @knative_sat@ over the
        -- wrapper (the suspended UIO action @krun_io@ fires by calling the
        -- wrapper).  Mirrors C's 'compileApp' host arm (C.hs:1968) EXACTLY: only
        -- the saturated (explicit args ≥ arity, arity > 0) case takes this fast
        -- path; a partial application falls through to the curried bare-reference
        -- path ('compileGlob' → 'compileHostValue' → @knative@ + @kapp@).
        Just rns
          | let arity = length (rns.params)
                explArgs = [argTerm a | a <- sargs, argIcit a == Expl]
          , length explArgs >= arity
          , arity > 0 -> compileHostSat rns (take arity explArgs)
        _ -> do
          mp <- globPrimName g
          case mp of
            -- A prim spine: take the saturated direct fast path
            -- ('compilePrimApp') when the explicit-argument count matches the
            -- prim's arity; otherwise (partial / over-application) fall through
            -- to the general @kapp@ chain, where the bare prim is a curried
            -- native closure ('compilePrimValue').
            Just pname | saturatedPrim pname term -> compilePrimApp pname sargs
            _ -> do
              -- Scalar function worker fast path: an EXACTLY-saturated call to a
              -- scalar-eligible global (Int/Double params + scalar result) unboxes
              -- its args and calls the @kwi_@/@kwd_@ worker, escaping to the boxed
              -- curried chain on a wrong-tag arg or overflow.  Surplus/partial
              -- calls keep the boxed path.  Mirrors C's 'compileDirectCall'.
              mplan <- scalarFnPlanLL g
              case mplan of
                Just (_mask, pks, ret, _)
                  | length sargs == length pks
                  , let runtimeIdxs = [0 .. length pks - 1] ->
                      compileScalarFnCallLL g pks ret sargs runtimeIdxs
                _ -> compileAppDefault term
    _ -> compileAppDefault term

-- | Milestone L (§27.1.1): lower a saturated host-member application to a direct
-- @knative_sat@ over its C wrapper ('wrapperCName'), the same node 'compileIoSat'
-- builds for an IO prim — only the called symbol differs (the codegen wrapper vs
-- a runtime @kpf_io_*@).  Mirrors C's 'compileApp' host arm (C.hs:1972–1981):
-- compile each of the @arity@ explicit args, materialise a stack @[arity x ptr]@
-- argv, and call @knative_sat(@wrapper, arity, argv, 1)@ (isio = 1: native
-- bindings are UIO, so the action is suspended).  @arity > 0@ is guaranteed by
-- the caller, so the @alloca@ is well-formed.  An over-application (more explicit
-- args than @arity@) takes only the first @arity@ here; the surplus would need a
-- @kapp@ chain on the result — but a native UIO action is itself the value, so an
-- over-application of a host member does not arise in an accepted program (its
-- result is @UIO r@, not a function), matching the C backend which likewise
-- consumes exactly @arity@.
compileHostSat :: ResolvedNativeSymbol -> [BackendTerm] -> Gen Text
compileHostSat rns explArgs = do
  let cfn = wrapperCName rns
      ar = length explArgs
  aes <- mapM compile explArgs
  argv <- freshReg
  emit (argv <> " = alloca [" <> T.pack (show ar) <> " x ptr], align 8")
  forM_ (zip [0 :: Int ..] aes) $ \(i, ae) -> do
    slot <- freshReg
    emit (slot <> " = getelementptr inbounds [" <> T.pack (show ar)
            <> " x ptr], ptr " <> argv <> ", i64 0, i64 " <> T.pack (show i) <> "")
    emit ("store ptr " <> ae <> ", ptr " <> slot <> ", align 8")
  ctor <- hostNativeSatCtor rns
  declRuntime ("declare ptr @" <> ctor <> "(ptr, i32, ptr, i32)")
  declRuntime ("declare ptr @" <> cfn <> "(ptr)")
  r <- freshReg
  emit (r <> " = call ptr @" <> ctor <> "(ptr @" <> cfn <> ", i32 "
          <> T.pack (show ar) <> ", ptr " <> argv <> ", i32 1)")
  pure r

-- | The general application path (Milestone D): a curried @kapp@ chain over the
-- compiled head and arguments — @f x y@ ⇒ @kapp(kapp(compile f, compile x),
-- compile y)@ (mirrors C's 'compileAppDefault', C.hs:2262).  An EXPLICIT
-- argument is applied with @kapp@; an IMPLICIT argument to an ERASED head (a
-- prim or constructor, §31.2) is DROPPED, otherwise it is applied with @kappi@
-- (the runtime's implicit-application entry).  A non-application term is just
-- 'compile'd (the recursion base case).
compileAppDefault :: BackendTerm -> Gen Text
compileAppDefault t@BApp {} = do
  let (hd, args) = backendSpineOf t
  erased <- isErasedHead hd
  h <- compile hd
  foldM (apply erased) h args
  where
    apply erased f a
      | argIcit a == Expl = do
          ae <- compileErasableArg (argTerm a)
          declRuntime "declare ptr @kapp(ptr, ptr)"
          r <- freshReg
          emit (r <> " = call ptr @kapp(ptr " <> f <> ", ptr " <> ae <> ")")
          pure r
      | erased = pure f
      | otherwise = do
          ae <- compileErasableArg (argTerm a)
          declRuntime "declare ptr @kappi(ptr, ptr)"
          r <- freshReg
          emit (r <> " = call ptr @kappi(ptr " <> f <> ", ptr " <> ae <> ")")
          pure r
compileAppDefault t = compile t

-- ── Erasure of type-level / staging arguments (Milestone D) ──────────
--
-- Ports of the C backend's 'isErasedHead' / 'isErasableArg' /
-- 'compileErasableArg' / 'isTypeGlob' (C.hs:1567–1620), the §31.2 erasure
-- discipline.  An implicit argument to a primitive or constructor head is
-- DROPPED; an explicit type-level / staging argument is replaced by a @kunit()@
-- placeholder so a constructor's runtime arity (positional projection) stays
-- aligned without compiling a type/quote value the interpreter never inspects.

-- | Is the (implicit) argument to this head erased at runtime? — a primitive or
-- constructor head erases its implicit arguments (§31.2).
isErasedHead :: BackendTerm -> Gen Bool
isErasedHead t = case headGlob t of
  Just g@(GName m _)
    | m == primModule -> pure True
    | otherwise -> do
        globals <- gets gsGlobals
        ctors <- gets gsCtorSet
        case Map.lookup g globals of
          Just gd | isVPrimValue (gdValue gd) -> pure True
          _ -> pure (g `Set.member` ctors)
  Nothing -> pure False

-- | The 'GName' at the head of a (possibly applied) term, if it is a global.
headGlob :: BackendTerm -> Maybe GName
headGlob = backendHeadGlob

isVPrimValue :: Maybe Value -> Bool
isVPrimValue (Just (VPrim _ _)) = True
isVPrimValue _ = False

-- | Is this argument purely type-level (computationally erased)?  Type-level
-- forms and references to type/trait globals are erasable; everything else is
-- compiled for real.
isErasableArg :: BackendTerm -> Gen Bool
isErasableArg = \case
  BUnit {} -> pure True
  BApp _ f _ -> isErasableArg f -- the spine head decides (e.g. @(List a))
  BGlob _ g -> isTypeGlob g
  BSeal _ _ e -> isErasableArg e
  _ -> pure False

-- | Compile a value-position argument, erasing it to the @kunit()@ placeholder
-- when it is a type-level / staging term (§12.2, §31.2).
compileErasableArg :: BackendTerm -> Gen Text
compileErasableArg a = do
  er <- isErasableArg a
  if er
    then do
      declRuntime "declare ptr @kunit()"
      r <- freshReg
      emit (r <> " = call ptr @kunit()")
      pure r
    else compile a

-- | A global that denotes a type or trait (so a reference to it in argument
-- position is computationally erased): a declared data type or trait, OR a global
-- whose kind is a sort (e.g. the builtin @Integer@, dragged in as an instance head).
-- The sort-kind fallback mirrors the C backend's 'isTypeGlob' (C.hs:1588) — without
-- it a @instance T Integer@ rejects, since @Integer@ has no recorded core body.
isTypeGlob :: GName -> Gen Bool
isTypeGlob g = do
  datas <- gets gsDataSet
  globals <- gets gsGlobals
  ctx <- gets gsEvalCtx
  let sortish = case Map.lookup g globals of
        Just gd -> isTypeKindTerm (quote ctx 0 (gdType gd))
        Nothing -> False
  pure (g `Set.member` datas || sortish)

-- | Does @g@'s RESULT type force to a RuntimeErased PROOF (propositional
-- equality / h-prop evidence)?  Shares the C backend's pure verdict
-- ('resultIsProofP') so both backends erase the identical set of proof lemmas
-- (§12.2/§31.2/§14.4) — see its Haddock for the soundness argument.
resultIsProof :: GName -> Gen Bool
resultIsProof g = do
  globals <- gets gsGlobals
  ctx <- gets gsEvalCtx
  pure (resultIsProofP globals ctx g)

-- | Whether a (quoted) type Term is sort-kinded — a sort, or a Pi telescope ending
-- in a sort.  Mirrors the C backend's 'isTypeKindTerm' (C.hs:1599).
isTypeKindTerm :: Term -> Bool
isTypeKindTerm = \case
  CSort _ -> True
  CPi _ _ _ _ _ body -> isTypeKindTerm body
  _ -> False

-- | §10.1/P0-A: recognise a saturated application of an eta-expanded
-- constructor and beta-reduce it to @(ctor, selected field args)@.  A FAITHFUL
-- port of "Kappa.Backend.C"'s 'etaCtorApp' (the two MUST agree so both backends
-- build the same constructor payload):
--
-- 'etaCtor' (§10.1) elaborates a @k@-Pi constructor into @k@ nested lambdas
-- whose innermost body is @CCtor g [CVar j …]@ over only the runtime-field
-- binders (erased implicit/type binders dropped).  When the spine applies
-- exactly one argument per lambda, the redex reduces: each field @CVar j@ names
-- the binder at de Bruijn index @j@ = spine position @k-1-j@ (the spine lists
-- arguments outermost-first).  Every field var is a bare in-range binder
-- reference, so the reduction is a pure selection — no index shifting.
--
-- 'Nothing' for a partial application (still a closure), an over-application, or
-- any head that is not an eta-expanded constructor.
etaCtorApp :: BackendTerm -> Maybe (GName, [BackendTerm])
etaCtorApp term =
  case backendSpineOf term of
    (hd, sargs)
      | (k, body) <- backendFuncArity hd
      , k >= 1
      , k == length sargs
      , BCtor _ layout fieldVars <- body ->
          (,) (bclCtor layout) <$> traverse (pick (map argTerm sargs) k) fieldVars
    _ -> Nothing
  where
    pick args k = \case
      BVar _ _ j | j >= 0, j < k -> Just (args !! (k - 1 - j))
      _ -> Nothing

-- | Lower a saturated application of a known primitive.  Mirrors the C
-- backend's dispatch in 'compileAppGlob' (C.hs:2110–2124) EXACTLY, so the two
-- backends emit the identical runtime call for any prim:
--
--   * an IO prim ⇒ @knative_sat(cfn, ar, argv, 1)@ ('compileIoSat');
--   * a PURE prim WITH a @kp_*@ direct helper ⇒ the positional fast path
--     @kp_NAME(a0, …)@ ('compilePureDirect', C's QW1 path);
--   * a PURE prim WITHOUT a direct helper ⇒ a direct call to its @kpf_*@
--     wrapper over an argument array @cfn(argv)@ ('compilePureWrapper',
--     C.hs:2121–2124).
--
-- Under-/over-saturation falls back to the curried @knative@ + @kapp@ chain
-- (handled by the caller, which only routes a SATURATED spine here).  A prim
-- outside 'primNativeEntry' (the 'ckMachinePrims' blocklist) never reaches here
-- — 'globPrimName' does not recognise it — but is reported defensively.
compilePrimApp :: Text -> [BackendArg] -> Gen Text
compilePrimApp pname sargs
  -- Milestone M: the EXCEPTION ops are NODE-BUILDERS on the uniform CK-machine
  -- path, NOT the synchronous @kpf_io_*@ bridge — they MUST be intercepted here
  -- before the generic 'ioPrimEntry'/@knative_sat@ arm (mirrors how the C
  -- backend special-cases catchIO/finallyIO/throwIO to @krt2_*@ in
  -- 'compileAppGlob', and how this backend would otherwise mis-run a do-block
  -- body through the bridge — the M-I divergence).  See 'compileIoNode'.
  | Just r <- ioNodeBuilder pname = compileIoNode pname r sargs
  -- §18.1.12 rank-2 restore adapter: `__restoreAt raw act` re-applies the raw
  -- 1-arg runtime restore closure to `act`.  NOT a krt2_* node — it lowers to a
  -- bare @kapp(raw, act)@ (the prim's own type args are already erased from the
  -- spine), the exact 1-arg runtime call the same as the C backend emits.  The
  -- source rank-2-ness is absorbed by the surrounding wrapper's kunit-filled type
  -- slot (see Prelude `__restoreAt`/`mask`).
  | pname == "__restoreAt"
  , [raw, act] <- [argTerm a | a <- sargs, argIcit a == Expl] = do
      rawc <- compile raw
      actc <- compile act
      declRuntime "declare ptr @kapp(ptr, ptr)"
      r <- freshReg
      emit (r <> " = call ptr @kapp(ptr " <> rawc <> ", ptr " <> actc <> ")")
      pure r
compilePrimApp pname sargs =
  case ioPrimEntry pname of
    Just (cfn, ar) -> compileIoSat pname cfn ar sargs
    Nothing ->
      case pureDirectEntry pname of
        Just (helper, ar) -> compilePureDirect pname helper ar sargs
        Nothing ->
          case primNativeEntry pname of
            -- A pure prim with no positional @kp_*@ helper: call its @kpf_*@
            -- wrapper directly over the argument array (C's @cfn(arr)@ arm).
            Just (cfn, ar, False) -> compilePureWrapper pname cfn ar sargs
            _ ->
              unsupported "primitive"
                ("the LLVM backend does not implement the primitive '"
                  <> pname <> "'; use the C backend")

-- | Milestone M: the EXCEPTION node-builders.  Each name maps to its @krt2_*@
-- runtime builder + explicit arity — the SAME node the C backend's
-- 'compileAppGlob' emits, but taken on the UNIFORM CK-machine path always (the
-- LLVM backend has no working synchronous bridge for these, and the bridge is
-- exactly what produced the M-I before/caught/after divergence).  These are
-- recognised in 'compilePrimApp' BEFORE the generic @knative_sat@ arm:
--
--   * @catchIO body handler@   ⇒ @krt2_catch(body, handler)@   (IO a -> (e->IO a) -> IO a)
--   * @finallyIO body fin@     ⇒ @krt2_finally(body, fin)@     (IO a -> IO () -> IO a)
--   * @throwIO err@            ⇒ @krt2_throw(err)@             (e -> IO a)
--   * @__reraiseCause cause@   ⇒ @krt2_reraise(cause)@         (Cause e -> IO a)
--
-- @body@/@fin@ are IO actions: 'compileErasableArg' (≡ 'compile' here) routes a
-- @CDo@ body to 'compileDo' (a @krt2_bind@/@krt2_then@ action tree) and a bare
-- IO call to its own node, so the body operand is already a CK-machine action —
-- the runtime catch/finally node drives it, body effects and the thrown value
-- included.  @handler@ is a function value (@e -> IO a@) compiled to a closure;
-- @err@/@cause@ are plain values.  Mirrors C.hs:2014–2035 (just always-on).
ioNodeBuilder :: Text -> Maybe (Text, Int)
ioNodeBuilder = \case
  -- §18.1 IO MONAD ops: an EXPLICIT ioBind/ioThen/ioPure (e.g. the body of
  -- liftA2/<*>/traverse, applied OUTSIDE a do-block) MUST take the uniform
  -- CK-machine path.  The synchronous kpf_io_ioBind bridge ('compileIoSat')
  -- cannot DRIVE a krt2_bind action tree (a do-block-valued action), so it
  -- silently yields a wrong-typed value — the same divergence class as catchIO
  -- over a do-block.  (The do-kernel 'compileDo' lowers its OWN binds; this arm
  -- only catches explicit applications — exactly where liftA2/traverse broke
  -- delve's loadActors.)
  "ioBind" -> Just ("krt2_bind", 2)
  "ioThen" -> Just ("krt2_then", 2)
  "ioPure" -> Just ("krt2_pure", 1)
  -- exception ops (Milestone M)
  "catchIO" -> Just ("krt2_catch", 2)
  "finallyIO" -> Just ("krt2_finally", 2)
  "throwIO" -> Just ("krt2_throw", 1)
  "__reraiseCause" -> Just ("krt2_reraise", 1)
  -- §18.1.4 reason-carrying finalizers + §18.1.7 locallyFiberRef: the same
  -- krt2_* node-builders the C backend uses (compileAppGlob); a may-suspend body
  -- runs on the uniform CK-machine path.
  "onExit" -> Just ("krt2_on_exit", 2)
  "onInterrupt" -> Just ("krt2_on_interrupt", 2)
  "locallyFiberRef" -> Just ("krt2_locally_fiber_ref", 3)
  -- §18.1.11 source-level blocking bridge: the native profile advertises
  -- rt-blocking, so saturated `blocking body` builds the OP_BLOCKING node.
  "blocking" -> Just ("krt2_blocking", 1)
  -- §18.1.12 masking: the OP_UNINTERRUPTIBLE/OP_MASK/OP_POLL node builders, the
  -- same lowering as the C backend (compileAppGlob).  `uninterruptible body` and
  -- `__mask f` are 1-arg; `poll` is 0-arg (handled below as a bare value too).
  "uninterruptible" -> Just ("krt2_uninterruptible", 1)
  "__mask" -> Just ("krt2_mask", 1)
  "poll" -> Just ("krt2_poll", 0)
  -- §18.1.13 STM (journaled): newTVar/readTVar/writeTVar/stmBind/stmPure are the
  -- STM_* tree leaves and `atomically` runs the tree in an OP_ATOMICALLY
  -- transaction.  These are NODE-BUILDERS with no @primEntry@ (the C backend
  -- special-cases them in 'compileAppGlob', C.hs:2448-2473); on LLVM they take
  -- the same uniform CK-machine path as the exception ops above.  (`retry` is a
  -- 0-arg @kpf_retry@ prim — it stays in 'primEntries', so it is de-blocklisted,
  -- NOT a node-builder here.)
  "stmBind" -> Just ("krt2_stm_bind", 2)
  "stmPure" -> Just ("krt2_stm_pure", 1)
  "newTVar" -> Just ("krt2_new_tvar", 1)
  "readTVar" -> Just ("krt2_read_tvar", 1)
  "writeTVar" -> Just ("krt2_write_tvar", 2)
  "atomically" -> Just ("krt2_atomically", 1)
  -- §18.1.6 race/timeout + §19.5 withScope + §18.1.4 explicit-cause interruption:
  -- node-builders with no @primEntry@ (C special-cases them in 'compileAppGlob',
  -- C.hs:2386-2441), so the LLVM backend must build the same krt2_* node rather
  -- than fall through to the unsupported curried path.  The prelude race/timeout/
  -- withScope bodies apply these saturated, so a saturated spine reaches here.
  "__race" -> Just ("krt2_race", 2)
  "__timeout" -> Just ("krt2_timeout", 2)
  "withScope" -> Just ("krt2_with_scope", 1)
  "__interruptWait" -> Just ("krt2_interrupt_as", 2)
  "__interruptNoWait" -> Just ("krt2_interrupt_fork_as", 2)
  -- same node as __interruptNoWait, free result channel (used by `disconnect`)
  "__interruptForkAny" -> Just ("krt2_interrupt_fork_as", 2)
  _ -> Nothing

-- | Lower a saturated exception op to its @krt2_*@ node-builder
-- ('ioNodeBuilder').  Each explicit argument is compiled to an operand
-- (a body/fin to a CK-machine ACTION, a handler to a closure, an err/cause to a
-- value — all via 'compileErasableArg', exactly as the C backend), then the
-- single @call ptr \@krt2_X(...)@ returns the node.  A CURRIED / under- or
-- over-saturated occurrence (rare) is NOT routed here — the caller only reaches
-- 'compilePrimApp' for a SATURATED spine ('saturatedPrim'); a partial one stays
-- a curried @knative@ closure ('compilePrimValue'), where the runtime drives it.
compileIoNode :: Text -> (Text, Int) -> [BackendArg] -> Gen Text
compileIoNode pname (builder, ar) sargs = do
  let explArgs = [argTerm a | a <- sargs, argIcit a == Expl]
  if length explArgs == ar
    then do
      aes <- mapM compileErasableArg explArgs
      declRuntime ("declare ptr @" <> builder
                     <> "(" <> T.intercalate ", " (replicate ar "ptr") <> ")")
      r <- freshReg
      emit (r <> " = call ptr @" <> builder
              <> "(" <> T.intercalate ", " ["ptr " <> ae | ae <- aes] <> ")")
      pure r
    else
      unsupported "application"
        ("the LLVM backend supports only a SATURATED application of '"
          <> pname <> "' (got " <> T.pack (show (length explArgs))
          <> " of " <> T.pack (show ar) <> " arguments)")

-- | Lower a saturated IO primitive to @knative_sat@ (M0 path, unchanged):
-- build a stack @[N x ptr]@ arg array, store each compiled argument operand,
-- and call @knative_sat(fn, argc, argv, 1)@ (mirrors C.hs:2105–2109).
compileIoSat :: Text -> Text -> Int -> [BackendArg] -> Gen Text
compileIoSat pname cfn ar sargs = do
  let explArgs = [argTerm a | a <- sargs, argIcit a == Expl]
  if length explArgs == ar
    then do
      aes <- mapM compile explArgs
      -- materialise a stack KValue *argv[ar]; store each operand.
      argv <- freshReg
      emit (argv <> " = alloca [" <> T.pack (show ar) <> " x ptr], align 8")
      forM_ (zip [0 :: Int ..] aes) $ \(i, ae) -> do
        slot <- freshReg
        emit (slot <> " = getelementptr inbounds [" <> T.pack (show ar)
                <> " x ptr], ptr " <> argv <> ", i64 0, i64 " <> T.pack (show i) <> "")
        emit ("store ptr " <> ae <> ", ptr " <> slot <> ", align 8")
      declRuntime "declare ptr @knative_sat(ptr, i32, ptr, i32)"
      declRuntime ("declare ptr @" <> cfn <> "(ptr)")
      r <- freshReg
      emit (r <> " = call ptr @knative_sat(ptr @" <> cfn <> ", i32 "
              <> T.pack (show ar) <> ", ptr " <> argv <> ", i32 1)")
      pure r
    else
      unsupported "application"
        ("the LLVM backend supports only a SATURATED application of '"
          <> pname <> "' (got " <> T.pack (show (length explArgs))
          <> " of " <> T.pack (show ar) <> " arguments)")

-- | Lower a saturated PURE first-order primitive to its direct @kp_*@ helper:
-- @call ptr \@kp_NAME(ptr a0, ptr a1, …)@ — a positional call with NO argument
-- array (the C backend's QW1 fast path, C.hs:2110–2112).  Each argument is
-- compiled to an operand in order; @declare ptr \@kp_NAME(ptr, …)@ supplies the
-- prototype.  Parity rests on the helper being the runtime's single source of
-- truth for the prim (same call the C backend emits).
compilePureDirect :: Text -> Text -> Int -> [BackendArg] -> Gen Text
compilePureDirect pname helper ar sargs = do
  let explArgs = [argTerm a | a <- sargs, argIcit a == Expl]
  if length explArgs == ar
    then do
      aes <- mapM compile explArgs
      let ptrParams = T.intercalate ", " (replicate ar "ptr")
          ptrArgs = T.intercalate ", " ["ptr " <> ae | ae <- aes]
      declRuntime ("declare ptr @" <> helper <> "(" <> ptrParams <> ")")
      r <- freshReg
      emit (r <> " = call ptr @" <> helper <> "(" <> ptrArgs <> ")")
      pure r
    else
      unsupported "application"
        ("the LLVM backend supports only a SATURATED application of '"
          <> pname <> "' (got " <> T.pack (show (length explArgs))
          <> " of " <> T.pack (show ar) <> " arguments)")

-- | Lower a saturated PURE primitive that has NO positional @kp_*@ helper to a
-- direct call on its @kpf_*@ wrapper over an argument array: @call ptr \@kpf_X
-- (ptr %argv)@ where @%argv@ is a stack @[ar x ptr]@ holding the compiled
-- arguments.  This is the C backend's @cfn(arr)@ arm (C.hs:2121–2124) — the
-- wrapper IS the runtime's single source of truth for the prim, so both
-- backends emit the identical call.  A 0-arity pure prim never reaches here (it
-- is a bare value, handled by 'compilePrimValue'); @ar@ is therefore ≥ 1 and the
-- @alloca [ar x ptr]@ is well-formed.
compilePureWrapper :: Text -> Text -> Int -> [BackendArg] -> Gen Text
compilePureWrapper pname cfn ar sargs = do
  let explArgs = [argTerm a | a <- sargs, argIcit a == Expl]
  if length explArgs == ar
    then do
      aes <- mapM compile explArgs
      argv <- freshReg
      emit (argv <> " = alloca [" <> T.pack (show ar) <> " x ptr], align 8")
      forM_ (zip [0 :: Int ..] aes) $ \(i, ae) -> do
        slot <- freshReg
        emit (slot <> " = getelementptr inbounds [" <> T.pack (show ar)
                <> " x ptr], ptr " <> argv <> ", i64 0, i64 " <> T.pack (show i) <> "")
        emit ("store ptr " <> ae <> ", ptr " <> slot <> ", align 8")
      declRuntime ("declare ptr @" <> cfn <> "(ptr)")
      r <- freshReg
      emit (r <> " = call ptr @" <> cfn <> "(ptr " <> argv <> ")")
      pure r
    else
      unsupported "application"
        ("the LLVM backend supports only a SATURATED application of '"
          <> pname <> "' (got " <> T.pack (show (length explArgs))
          <> " of " <> T.pack (show ar) <> " arguments)")

-- ── LLVM primitive coverage (the only LLVM-local prim data) ──────────
--
-- The cfn/arity/isIO of every prim, and the @kp_*@ direct-helper subset, are
-- single-sourced in "Kappa.Backend.C" ('primEntries' / 'primDirect').  What is
-- LLVM-specific is only WHICH prims this backend lowers — and as of Milestone I
-- that is EVERY 'primEntries' member except the 'ckMachinePrims' blocklist
-- ('lowerablePrim').  Every prim lowering ('ioPrimEntry'/'pureDirectEntry'/
-- 'primNativeEntry') is a DERIVATION over the shared C tables, so a lowering can
-- never disagree with the C backend on a prim's entry point, arity, or IO-ness —
-- the two backends emit the identical runtime call for any prim both cover.

-- | A prim is lowerable iff it is a 'primEntries' member and NOT in the
-- 'ckMachinePrims' blocklist (which needs the CK-machine, not the synchronous
-- bridge).  The single gate every coverage query derives from.
lowerablePrim :: Text -> Maybe PrimEntry
lowerablePrim name
  | name `Set.member` ckMachinePrims = Nothing
  | otherwise = Map.lookup name primEntries

-- | The (entry point, arity) of a lowerable IO primitive, from the shared
-- 'primEntries'.  A saturated IO prim lowers to @knative_sat(cfn, ar, argv, 1)@
-- — the SAME lowering the C backend gives it (C.hs:2113–2117).
ioPrimEntry :: Text -> Maybe (Text, Int)
ioPrimEntry name = do
  PrimEntry cfn arity isIO <- lowerablePrim name
  if isIO then Just (cfn, arity) else Nothing

-- | The (direct @kp_*@ helper, arity) of a lowerable PURE primitive that HAS a
-- positional fast-path helper in the shared 'primDirect'.  A saturated call
-- emits the identical runtime call in both backends (e.g. @kp_addInt(a,b)@).
-- A pure prim WITHOUT such a helper is lowered via 'primNativeEntry' instead
-- (the @kpf_*(arr)@ array call) — exactly the C backend's fallback arm.
pureDirectEntry :: Text -> Maybe (Text, Int)
pureDirectEntry name = do
  PrimEntry _ _ isIO <- lowerablePrim name
  if isIO then Nothing else primDirect name

-- | The CURRIED native-closure form of a lowerable prim — its @kpf_*@ wrapper
-- entry point, arity, and IO-ness.  Used when a prim appears as a VALUE (a bare
-- reference, or a partial/over-saturated application): the prim is built as
-- @knative(\@kpf_*, arity, name, isio)@, the same curried closure the C
-- backend's 'emitPrim' builds.  Also the source for the saturated PURE-with-no-
-- @kp_*@-helper @kpf_*(arr)@ arm in 'compilePrimApp'.  Derived from the shared
-- 'primEntries', so the wrapper symbol/arity/isIO always agree with the C
-- backend.
--
-- NOTE the @kpf_*@ wrapper is DISTINCT from the @kp_*@ direct helper
-- ('pureDirectEntry'): @kp_addInt(a,b)@ is the saturated fast call, whereas
-- @kpf_addInt@ is the @KValue**@-taking wrapper that @knative@ drives one
-- curried argument at a time.
primNativeEntry :: Text -> Maybe (Text, Int, Bool)
primNativeEntry name = do
  PrimEntry cfn arity isIO <- lowerablePrim name
  Just (cfn, arity, isIO)

-- | The runtime primitive name a global resolves to, if any (a @__prim@
-- module name, or a prelude @prim@ registration whose value is a bare
-- 'VPrim'), and that name is implemented by the linked runtime.  Mirrors C's
-- 'globPrimName'.
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
