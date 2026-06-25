{-# LANGUAGE OverloadedRecordDot #-}

-- | Native backend (LLVM textual IR): lower elaborated KCore
-- ('Kappa.Core.Term') to a complete @.ll@ translation unit that links
-- against the same @kappart2@ runtime the C backend uses
-- ("Kappa.Backend.C").
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
import Data.Word (Word8)
import GHC.Float (castDoubleToWord64)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Control.Monad (forM_, foldM, msum, mplus, unless, when, void)
import Control.Monad.State.Strict
import Kappa.Backend.C (BackendError (..), PrimEntry (..), primDirect, primEntries)
import Kappa.Backend.NativeFfi (ResolvedNativeSymbol (..), externPrototype, rnsCollectCtors, wrapperCName, wrapperDefinition)
import Kappa.Builtins (builtinCtorTagId, kctUserBase)
import Kappa.Check (CheckState (..))
import Kappa.Core
import Kappa.Eval (EvalCtx (..), GlobalDef (..), Globals (..), quote)
import Kappa.Source (Span, noSpan)
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
  , gsPrims :: !(Set Text) -- ^ primitive names the linked runtime implements
  , gsDeclSites :: !(Map GName Span)
  , gsCtorTags :: !(Map Text Int) -- ^ Milestone C: USER-constructor gKey -> numeric tag id (@KCT_USER_BASE+i@). Precomputed once ('hostCtorTags') so 'compileCtor'/'compileMatch' can emit a literal @i32@ immediate (LLVM has no symbolic enum constant like the C backend's @KT_*@). Builtin ctors are NOT here — they use the fixed 'builtinCtorTagId'. Milestone L: includes the @std.ffi@ ctors host marshalling builds, so the @.ll@ and the wrapper sidecar agree on ids.
  , gsBlock :: !Text -- ^ Milestone C: label of the basic block currently being filled. A @phi@ at a control-flow join needs the PREDECESSOR block of each incoming value, which — for a branch that itself emitted control flow (a nested match/if) — is NOT the branch-entry label but whatever block was active when the branch finished. 'compileIf'/'compileMatch' read this after compiling each arm to spell the phi's incoming labels correctly. Updated by 'startBlock'.
  , gsCtorSet :: !(Set GName) -- ^ Milestone D: every declared constructor's gname. An IMPLICIT application whose head is a constructor erases its implicit arg (§31.2); 'isErasedHead' consults this (mirrors C's 'gsCtors' membership test).
  , gsDataSet :: !(Set GName) -- ^ Milestone D: declared data-type / trait gnames — a reference to one in argument position is computationally erased ('isTypeGlob'); mirrors C's @gsDatas@ ∪ @gsTraits@.
  , gsHostSyms :: !(Map GName ResolvedNativeSymbol) -- ^ Milestone L (§27.1.1/§36.28): each provided @host.native.*@ member ↦ its resolved native symbol (C symbol + ABI signature), built per build from the manifest's native bindings. A reference to such a member is lowered like a PRIM over the codegen-emitted C-wrapper symbol ('wrapperCName') — a saturated reference to a @knative_sat@ over the wrapper, a curried/bare reference to a @knative@ closure — and the wrapper is compiled+linked from a sidecar @.c@ the Driver emits ('hostFfiSidecar'). Mirrors C's @gsHostSyms@; recognised at the REFERENCE so a host member is NEVER enqueued as a no-core-body CAF.
  }

type Gen = State GenState

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
  -- The captured region is spliced verbatim under the accessor's @build:@
  -- label, so that is the block active when @act@ starts emitting; a control
  -- form ('compileMatch'/'compileIf') reads/updates 'gsBlock' from here.
  modify' $ \g -> g {gsInsns = [], gsEnv = env, gsBlock = "build"}
  r <- act
  produced <- gets gsInsns
  endBlock <- gets gsBlock
  modify' $ \g -> g {gsInsns = saved, gsEnv = savedEnv, gsBlock = savedBlock}
  pure (reverse produced, endBlock, r)

-- | Record an unsupported-construct finding and return a placeholder operand
-- so error collection can continue.
unsupported :: Text -> Text -> Gen Text
unsupported construct detail = do
  g <- gets gsCur
  sites <- gets gsDeclSites
  let sp = Map.findWithDefault noSpan g sites
  modify' $ \st -> st {gsErrs = BackendError g sp construct detail : gsErrs st}
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
      keys = sort (Set.toList (Set.union bodyKeys hostKeys))
   in Map.fromList (zip keys [kctUserBase ..])

-- | The gKeys of every USER constructor referenced (constructed via 'CCtor' or
-- matched via 'CPCtor') anywhere in a term.  Builtins are dropped — they do not
-- need a codegen-assigned id.
userCtorKeys :: Term -> Set Text
userCtorKeys = goT
  where
    user g = case builtinCtorTagId (gKey g) of
      Just _ -> Set.empty
      Nothing -> Set.singleton (gKey g)
    goT t = case t of
      CVar {} -> Set.empty
      CGlob {} -> Set.empty
      CLam _ _ _ b -> goT b
      CPi _ _ _ _ ty b -> goT ty <> goT b
      CApp _ a b -> goT a <> goT b
      CSort {} -> Set.empty
      CLit {} -> Set.empty
      CCtor g args -> user g <> foldMap goT args
      CMatch s alts -> goT s <> foldMap goAlt alts
      CRecordT fs -> foldMap (goT . snd) fs
      CRecordV fs -> foldMap (goT . snd) fs
      CProj e _ -> goT e
      CProjAt e _ _ -> goT e
      CVariantT ts -> foldMap goT ts
      CInject _ e -> goT e
      CLet _ _ ty rhs body -> goT ty <> goT rhs <> goT body
      CLetRec _ _ ty rhs body -> goT ty <> goT rhs <> goT body
      CMeta {} -> Set.empty
      CDo _ _ -> Set.empty -- do-kernel is not a Milestone-C lowering target
      CSealE _ e -> goT e
      CSigT _ e -> goT e
      CThunkE e -> goT e
      CLazyE e -> goT e
      CForceE e -> goT e
      CIf c th el -> goT c <> goT th <> goT el
      CQuote _ ts -> foldMap goT ts
    goAlt (CaseAlt pat mg body) =
      goPat pat <> maybe Set.empty goT mg <> goT body
    goPat p = case p of
      CPWild -> Set.empty
      CPVar _ -> Set.empty
      CPLit _ -> Set.empty
      CPCtor g ps -> user g <> foldMap goPat ps
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
ctorTagId g = case builtinCtorTagId (gKey g) of
  Just i -> pure i
  Nothing -> do
    tags <- gets gsCtorTags
    pure (Map.findWithDefault kctUserBase (gKey g) tags)

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
-- 'Kappa.Backend.C.generateC', so the Driver dispatches on a flag with no
-- change to the call site's type.
generateLL :: CheckState -> GName -> Set Text -> Map GName ResolvedNativeSymbol -> Either [BackendError] Text
generateLL cs mainG ffiPrims hostSyms =
  let st0 =
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
          , gsEvalCtx = EvalCtx (Globals (csGlobals cs)) (csMetas cs) False (csFacts cs)
          , gsBodies = csCoreBodies cs
          , gsPrims = Set.union basePrims ffiPrims
          , gsDeclSites = csDeclSites cs
          , gsCtorTags = hostCtorTags (csCoreBodies cs) hostSyms
          , gsBlock = "build"
          , gsCtorSet = Map.keysSet (csCtors cs)
          , gsDataSet = Set.union (Map.keysSet (csDatas cs)) (Map.keysSet (csTraits cs))
          , gsHostSyms = hostSyms
          }
      final = execState (drainQueue >> emitMain mainG) st0
   in case reverse (gsErrs final) of
        [] -> Right (assembleLL final)
        errs -> Left errs

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
-- @ioPure@/@newRef@/@readRef@/@writeRef@) are still recognised here, but their
-- NODE-BUILDER handling in 'compileDo'/'compileMonadicAction'/'newRefAction'
-- takes precedence in the do-context (only OUTSIDE it do they fall to the
-- generic @knative_sat@ path, which is exactly what the C backend does too).
basePrims :: Set Text
basePrims = Set.difference (Map.keysSet primEntries) ckMachinePrims

-- | The prims kept OUT of LLVM coverage because their meaning is the CK-machine
-- node, not the synchronous @knative@/@knative_sat@ bridge: structured
-- concurrency (fork/await/spawn/scope/monitor), STM (atomically/stm*/TVars/
-- retry), cooperative scheduling (sleep/yield/self).  The C backend lowers these
-- via dedicated @krt2_*@ node-builders ('compileAppGlob') or its CPS do-kernel;
-- the LLVM backend implements neither, so the synchronous bridge mis-runs a body
-- that is itself a CK-machine action tree.
--
-- Milestone M closed the EXCEPTION ops (throwIO/catchIO/finallyIO), which used
-- to live here because of a CONCRETE parity divergence (the @ioerror@ native
-- case): @catchIO risky handler@ where @risky@ is a do-block
-- (`printlnString "before"; raise "boom"; …`) lowers @risky@ to a @krt2_*@
-- action tree, but the synchronous @kpf_io_catchIO@ bridge's @krun_io@ cannot
-- drive that tree — it dropped the body's effects and the thrown value
-- (interp/C print @before\\ncaught:boom\\nafter@; the bridge printed only
-- @after@).  The fix mirrors the C backend's do-kernel: 'compilePrimApp' lowers
-- catchIO\/finallyIO\/throwIO to the @krt2_catch@\/@krt2_finally@\/@krt2_throw@
-- node-builders on the UNIFORM CK-machine path (always — no sync bridge), so the
-- before\/caught\/after case is now CK-machine-driven end to end and correct.
ckMachinePrims :: Set Text
ckMachinePrims =
  Set.fromList
    [ -- NOTE: the exception ops (throwIO/catchIO/finallyIO) are NO LONGER here
      -- (Milestone M).  They are lowered to the @krt2_throw@/@krt2_catch@/
      -- @krt2_finally@ NODE-BUILDERS in 'compilePrimApp' (the same place
      -- ioBind/ioThen/ioPure become krt2_bind/then/pure) so the runtime
      -- CK-machine drives them end to end — NOT the synchronous
      -- @kpf_io_catchIO@ bridge that produced the M-I before/caught/after
      -- divergence.  The remaining names below still need the CK-machine node
      -- the LLVM backend does not yet build, so they stay a clean unsupported.
      "atomically", "stmBind", "stmPure", "retry"
    , "newTVar", "readTVar", "writeTVar"
    , "forkIO", "fork", "spawn", "spawnIn", "spawnLink"
    , "__awaitFiber", "awaitPromise", "awaitPromiseExit"
    , "monitor", "awaitMonitor", "demonitor"
    , "sleepFor", "yieldNow", "self"
    , "newScope", "forkIn", "scopeJoin", "scopeCancel"
    ]

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
  bodies <- gets gsBodies
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
    Just tm -> do
      -- A CAF accessor's value is consumed DIRECTLY (cached + returned to a plain
      -- caller), so it must be a real value/closure — NOT a tail position.  Using
      -- 'compile' (not 'compileTail') drains any final application through @kapp@
      -- immediately; otherwise the cache would store an undrained @K_BOUNCE@ (a
      -- deferred tail call only the trampoline inside @kapp@ knows how to run), and
      -- a later 'kapp(op, …)' / 'showInt op' would see a non-value.  A function-shaped
      -- global is unaffected: its body is a 'CLam', a value in both paths.  Only the
      -- lifted @kfn_N@ FUNCTION body (invoked through @kapp@'s trampoline) is tail
      -- position and keeps 'compileTail'.
      (insns, endBlock, operand) <- captured "null" (compile tm)
      emitArity0Accessor ident insns endBlock operand

-- | The leading-lambda arity of a term and the body beneath those binders
-- (mirrors C's 'funcArity').
funcArity :: Term -> (Int, Term)
funcArity = go 0
  where
    go !n (CLam _ _ _ b) = go (n + 1) b
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
  let cacheG = "@" <> ident <> ".cache"
  modify' $ \st ->
    st {gsGlobalsExtra = (cacheG <> " = internal global ptr null, align 8") : gsGlobalsExtra st}
  let def =
        T.unlines $
          [ "define internal ptr @" <> ident <> "() {"
          , "entry:"
          , "  %cached = load ptr, ptr " <> cacheG <> ", align 8"
          , "  %hit = icmp ne ptr %cached, null"
          , "  br i1 %hit, label %ret, label %build"
          , ""
          , "build:"
          ]
            ++ map ("  " <>) buildInsns
            ++ [ "  store ptr " <> operand <> ", ptr " <> cacheG <> ", align 8"
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

-- | The @\@main@ entry point.  Mirrors C's 'emitMain' (C.hs:1280) EXACTLY,
-- including: @krt2_new(0)@ (which calls @krt_init@ internally — there is NO
-- separate @krt_init@ call), @krt2_run_main(kg_main())@, and the
-- success-to-exit-code mapping (0 on success, 1 on failure).
emitMain :: GName -> Gen ()
emitMain g = do
  let ident = cGlobIdent g
  declRuntime "declare ptr @krt2_new(i32)"
  declRuntime "declare ptr @krt2_run_main(ptr)"
  declRuntime "declare i32 @krt2_exit_is_success(ptr)"
  let def =
        T.unlines
          [ "define i32 @main() {"
          , "entry:"
          , "  %rt = call ptr @krt2_new(i32 0)"
          , "  %m = call ptr @" <> ident <> "()"
          , "  %exit = call ptr @krt2_run_main(ptr %m)"
          , "  %ok = call i32 @krt2_exit_is_success(ptr %exit)"
          , "  %fail = icmp eq i32 %ok, 0"
          , "  %code = select i1 %fail, i32 1, i32 0"
          , "  ret i32 %code"
          , "}"
          ]
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
compile :: Term -> Gen Text
compile term = case term of
  CLit l -> compileLit l
  CGlob g -> compileGlob g
  CApp {} -> compileApp term
  CVar i -> compileVar i
  CLam _ _ _ body -> compileLam body
  CLet _ _ _ rhs body -> compileLet rhs body
  -- Milestone J: a recursive local let — the body is in expression position
  -- here, so the body-compiler is plain 'compile'.
  CLetRec _ _ _ rhs body -> compileLetRecWith compile rhs body
  -- §19 suspensions: Delay re-evaluates on force; Memo caches (memo flag).
  CThunkE e -> compileSuspension 0 e
  CLazyE e -> compileSuspension 1 e
  CForceE e -> compileForce e
  CCtor g args -> compileCtor g args
  CIf c t e -> compileIf c t e
  CMatch scrut alts -> compileMatch scrut alts
  CDo lbl items -> compileDo lbl items
  -- Records (Milestone H) — a record VALUE, a name-based projection, and a
  -- precomputed-offset projection.  All three are plain values, so 'compileTail'
  -- routes them here unchanged (its @_ -> compile term@ fallback).
  CRecordV fs -> compileRecord fs
  CProj e f -> compileProj e f
  CProjAt e _ i -> compileProjAt e i
  -- A record TYPE is type-level / quantity-0 erased (§12.2): if one ever reaches
  -- value position it is the unit placeholder, never inspected (mirrors C's
  -- @CRecordT _ -> kunit()@).  Keeps an erased record type from being reported as
  -- an unsupported "record".
  CRecordT _ -> compileUnit
  _ ->
    unsupported "term"
      ("the LLVM backend M0 cannot lower this construct: " <> constructName term)

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
compileTail :: Term -> Gen Text
compileTail term = case term of
  CApp {}
    -- A saturated eta-expanded constructor is a final data value — build it
    -- directly (it cannot bounce or recurse).
    | Just (g, ctorArgs) <- etaCtorApp term -> compileCtor g ctorArgs
    | otherwise -> do
        let (hd, _) = spineOf term
        mp <- case hd of CGlob g -> globPrimName g; _ -> pure Nothing
        case mp of
          -- A prim spine returns a value (no bounce) iff it is the saturated
          -- fast path; otherwise it falls through 'compile' to the kapp chain.
          Just pname | saturatedPrim pname term -> compile term
          _ -> compileTailApp term
  CLet _ _ _ rhs body -> do
    rv <- compile rhs
    env0 <- gets gsEnv
    declRuntime "declare ptr @kpush(ptr, ptr)"
    env1 <- freshReg
    emit (env1 <> " = call ptr @kpush(ptr " <> rv <> ", ptr " <> env0 <> ")")
    modify' $ \g -> g {gsEnv = env1}
    bv <- compileTail body
    modify' $ \g -> g {gsEnv = env0}
    pure bv
  CIf c t e -> compileIfWith compileTail c t e
  CMatch scrut alts -> compileMatchWith compileTail scrut alts
  -- Milestone J: a recursive local let whose BODY is in tail position — thread
  -- the tail-ness through to the body (the body-compiler is 'compileTail') so a
  -- tail self-call inside it still lowers to a @kbounce@ and deep local
  -- recursion stays stack-safe.
  CLetRec _ _ _ rhs body -> compileLetRecWith compileTail rhs body
  -- A force is a value (the forced thunk's result); compile it and return it.
  CForceE e -> compileForce e
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
saturatedPrim :: Text -> Term -> Bool
saturatedPrim pname term =
  let (_, sargs) = spineOf term
      nexpl = length [() | (Expl, _) <- sargs]
   in case primArity pname of
        Just ar -> nexpl == ar
        Nothing -> False

-- | The runtime arity of a lowerable prim (across all three saturated paths).
primArity :: Text -> Maybe Int
primArity pname = case primNativeEntry pname of
  Just (_, ar, _) -> Just ar
  Nothing -> Nothing

-- | Lower a general CLOSURE application in TAIL position: the head + all but the
-- final explicit argument are built EAGERLY with the ordinary @kapp@ chain (the
-- partial-closure spine), and the FINAL application is a @kbounce@ that the
-- driving @kapp@'s trampoline drains — bounding the C stack on tail recursion.
-- An implicit final argument (or no explicit argument at all) cannot bounce by
-- itself, so it falls back to a plain 'compile' of the whole spine.
compileTailApp :: Term -> Gen Text
compileTailApp term = case term of
  CApp Expl f a -> do
    fe <- compile f
    ae <- compileErasableArg a
    declRuntime "declare ptr @kbounce(ptr, ptr)"
    r <- freshReg
    emit (r <> " = call ptr @kbounce(ptr " <> fe <> ", ptr " <> ae <> ")")
    pure r
  _ -> compile term

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
compileLet :: Term -> Term -> Gen Text
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
compileLetRecWith :: (Term -> Gen Text) -> Term -> Term -> Gen Text
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
compileSuspension :: Int -> Term -> Gen Text
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
compileForce :: Term -> Gen Text
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
compileLam :: Term -> Gen Text
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
compileCtor :: GName -> [Term] -> Gen Text
compileCtor g args = do
  tag <- ctorTagId g
  nameG <- internCStr (gKey g)
  let tagOp = T.pack (show tag)
  if null args
    then do
      declRuntime "declare ptr @kctor0(i32, ptr)"
      r <- freshReg
      emit (r <> " = call ptr @kctor0(i32 " <> tagOp <> ", ptr " <> nameG <> ")")
      pure r
    else do
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

-- ── Records (Milestone H) ────────────────────────────────────────────

-- | The unit placeholder operand (@call ptr \@kunit()@) — used for an erased
-- type-level term that reaches value position (e.g. a 'CRecordT').
compileUnit :: Gen Text
compileUnit = do
  declRuntime "declare ptr @kunit()"
  r <- freshReg
  emit (r <> " = call ptr @kunit()")
  pure r

-- | A record VALUE (mirrors C's 'compileRecord').  The fields arrive in canonical
-- lexicographic order — the SAME order the @K_REC@ runtime layout expects — so we
-- preserve it.  The runtime constructor is
--
--   @KValue *krec(int n, const char **names, KValue **vals)@
--
-- which STORES the @names@ pointer without copying (the labels are compile-time
-- literals) and COPIES @vals@ into a GC array (runtime/kappart.c:322).  So:
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
compileRecord :: [(Text, Term)] -> Gen Text
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
compileProj :: Term -> Text -> Gen Text
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
compileProjAt :: Term -> Int -> Gen Text
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
compileIf :: Term -> Term -> Term -> Gen Text
compileIf = compileIfWith compile

-- | 'compileIf' parameterised on how each ARM is compiled: 'compile' for an
-- expression-position @if@, 'compileTail' for a tail-position one (so a tail
-- call inside a branch lowers to @kbounce@).  The condition is always compiled
-- non-tail (it is forced to an @i1@ here), and the arm results meet at a
-- @phi ptr@ over the two arms' predecessor blocks — a @kbounce@ value flows
-- through the phi unchanged.
compileIfWith :: (Term -> Gen Text) -> Term -> Term -> Term -> Gen Text
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
compileMatch :: Term -> [CaseAlt] -> Gen Text
compileMatch = compileMatchWith compile

-- | 'compileMatch' parameterised on how each ALT BODY is compiled: 'compile' for
-- an expression-position @match@, 'compileTail' for a tail-position one (so a
-- tail call inside an alt body lowers to @kbounce@).  A bounce flows through the
-- join @phi@ unchanged and is drained by the caller.  The scrutinee and any
-- guard are always compiled non-tail (they are forced to values here).
compileMatchWith :: (Term -> Gen Text) -> Term -> [CaseAlt] -> Gen Text
compileMatchWith compileBody scrut alts = do
  sv <- compile scrut
  joinL <- freshLabel "match.join."
  -- §17.2.3: an or-pattern whose alternatives list the shared binders in a
  -- different ORDER than the first needs a per-alternative de-Bruijn body
  -- permutation; this backend distributes alternatives over a shared body and
  -- does not perform it, so refuse rather than miscompile (mirrors the C
  -- backend's 'consumeMatch' guard; the interpreter handles this case).
  forM_ alts $ \(CaseAlt pat _ _) ->
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
expandTopOrLL :: CaseAlt -> [CaseAlt]
expandTopOrLL (CaseAlt pat g body) = [CaseAlt p g body | p <- distributePatLL pat]

-- | The or-free patterns a pattern denotes, distributing every nested 'CPOr' as
-- the Cartesian product over its positions (mirrors C's 'distributePat').
distributePatLL :: CorePat -> [CorePat]
distributePatLL = \case
  CPOr ps _ -> concatMap distributePatLL ps
  CPCtor g ps -> [CPCtor g qs | qs <- mapM distributePatLL ps]
  CPTuple ps -> [CPTuple qs | qs <- mapM distributePatLL ps]
  CPRecord fs rest ->
    let (names, pats) = unzip fs
     in [CPRecord (zip names qs) rest | qs <- mapM distributePatLL pats]
  CPInject t p -> [CPInject t q | q <- distributePatLL p]
  CPAs n p -> [CPAs n q | q <- distributePatLL p]
  p -> [p] -- CPWild / CPVar / CPLit / CPInjectRest: no nested or

-- | Whether a pattern contains an or-pattern whose alternatives bind the shared
-- names in a NON-canonical order (a non-identity permutation on some
-- alternative) — these need a per-alternative de Bruijn permutation the shared-
-- body distribution can't express.  Mirrors C's 'orReordered' (C.hs:2617).
orReorderedLL :: CorePat -> Bool
orReorderedLL = \case
  CPOr ps perms -> any (\pm -> pm /= [0 .. length pm - 1]) perms || any orReorderedLL ps
  CPCtor _ ps -> any orReorderedLL ps
  CPTuple ps -> any orReorderedLL ps
  CPRecord fs _ -> any (orReorderedLL . snd) fs
  CPInject _ p -> orReorderedLL p
  CPAs _ p -> orReorderedLL p
  _ -> False

-- | Lower the alternatives of a 'compileMatch' as a test/branch chain.  The
-- chain is linearised so each alt's FAILURE path opens the next alt's block
-- inline (no dangling fall-through): 'compileAlt' is given an @onFail@ action
-- that emits the continuation INTO the current (already-open, unterminated)
-- block.  Returns the @(operand, predecessor-block)@ incomings for the join phi
-- — one per alt that reaches the join, plus the non-exhaustive fallback's
-- (unreachable) @null@ incoming.
compileAlts :: (Term -> Gen Text) -> Text -> Text -> [CaseAlt] -> Gen [(Text, Text)]
compileAlts compileBody sv joinL = go
  where
    go [] = do
      -- No alt matched: abort like the C backend's krt_fail, then feed the join
      -- a placeholder so the phi stays well-formed (this edge is unreachable).
      declRuntime "declare void @krt_fail(ptr)"
      msg <- internCStr "non-exhaustive match"
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
compileAlt :: (Term -> Gen Text) -> Text -> Text -> CaseAlt -> Gen [(Text, Text)] -> Gen [(Text, Text)]
compileAlt compileBody sv joinL (CaseAlt pat mguard body) onFail = do
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
bindAndBody :: (Term -> Gen Text) -> Text -> Text -> CorePat -> Term -> Gen (Text, Text)
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
bodyToJoin :: (Term -> Gen Text) -> Text -> Term -> Gen (Text, Text)
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
patAlwaysMatches :: CorePat -> Bool
patAlwaysMatches = \case
  CPWild -> True
  CPVar _ -> True
  CPAs _ p -> patAlwaysMatches p
  CPTuple ps -> all patAlwaysMatches ps
  CPRecord fs _ -> all (patAlwaysMatches . snd) fs
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
patTestBranch :: Text -> CorePat -> Text -> Gen ()
patTestBranch v pat failL = case pat of
  CPWild -> pure ()
  CPVar _ -> pure ()
  CPAs _ p -> patTestBranch v p failL
  -- Milestone F: a literal pattern — value-equality against the scrutinee via
  -- the SAME runtime call the C backend uses (@klit_eq(v, lit)@, an @int@ truthy
  -- result).  A literal binds no fields ('patBindingsLL' returns @[]@), so this
  -- is purely a test.  An unsupported literal records an error and never matches.
  CPLit l -> do
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
  CPCtor g ps -> do
    tag <- ctorTagId g
    declRuntime "declare i32 @kctor_tagid(ptr)"
    ti <- freshReg
    emit (ti <> " = call i32 @kctor_tagid(ptr " <> v <> ")")
    cond <- freshReg
    emit (cond <> " = icmp eq i32 " <> ti <> ", " <> T.pack (show tag))
    branchOn cond
    -- Tag confirmed: recurse LEFT-TO-RIGHT into each field, each at the C M-C
    -- offset @kctor_arg(v, kctor_argc(v) - nps + i)@.  A field's own test (if
    -- any) short-circuits to the SAME failL.
    let nps = length ps
    forM_ (zip [0 ..] ps) $ \(i, p) -> do
      av <- ctorArgLL v nps i
      patTestBranch av p failL
  CPTuple ps -> do
    -- A tuple IS a record (K_REC); the arity is fixed, but the C backend still
    -- guards on @krec_size@, so mirror that, then recurse into @krec_at(v, i)@.
    let n = length ps
    declRuntime "declare i32 @krec_size(ptr)"
    sz <- freshReg
    emit (sz <> " = call i32 @krec_size(ptr " <> v <> ")")
    cond <- freshReg
    emit (cond <> " = icmp eq i32 " <> sz <> ", " <> T.pack (show n))
    branchOn cond
    forM_ (zip [0 ..] ps) $ \(i, p) -> do
      av <- recAtLL v i
      patTestBranch av p failL
  -- §17.2.5: a record pattern's rest binder always matches; the named fields
  -- determine the test.  Recurse into each @kproj(v, f)@.
  CPRecord pfs _ ->
    forM_ pfs $ \(f, p) -> do
      av <- projNameLL v f
      patTestBranch av p failL
  -- §13 variant pattern: tag test via the runtime's string-tag predicate, then
  -- recurse into the payload.
  CPInject tag p -> do
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
  CPInjectRest _ -> do
    _ <- unsupported "pattern"
      "the LLVM backend does not lower residual-row variant patterns (CPInjectRest); use the C backend"
    branchFalse
  CPOr _ _ -> do
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

-- | A pattern whose fields 'bindPatDo' can push as a single env slot without a
-- shape test: a variable, a wildcard, or an as-pattern over one of those.  Used
-- only by the do-kernel's irrefutable binder fast path.
isVarLike :: CorePat -> Bool
isVarLike = \case
  CPVar _ -> True
  CPWild -> True
  CPAs _ p -> isVarLike p
  _ -> False

-- | Bind a pattern's variables by pushing each projected field onto the env
-- chain ('kpush'), in the SAME left-to-right order the C backend's
-- 'patBindings' uses (so the rightmost binder lands at de Bruijn index 0 and the
-- body's indices line up).  Returns the extended env operand.  Mirrors C's
-- 'bindPatScrut' (boxed path) restricted to the Milestone-C pattern subset.
bindPat :: Text -> CorePat -> Gen Text
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
patBindingsLL :: Text -> CorePat -> Gen [Text]
patBindingsLL = go
  where
    go v = \case
      CPWild -> pure []
      CPLit _ -> pure []
      CPVar _ -> pure [v]
      CPAs _ p -> do rest <- go v p; pure (v : rest)
      CPCtor _ ps -> do
        let nps = length ps
        concat <$> mapM (\(i, p) -> ctorArgLL v nps i >>= \av -> go av p) (zip [0 ..] ps)
      CPTuple ps ->
        concat <$> mapM (\(i, p) -> recAtLL v i >>= \av -> go av p) (zip [0 ..] ps)
      CPRecord pfs mrest -> do
        named <- concat <$> mapM (\(f, p) -> projNameLL v f >>= \av -> go av p) pfs
        case mrest of
          Just nm | not (T.null nm) -> do
            rv <- recWithoutLL v (map fst pfs)
            pure (named ++ [rv])
          _ -> pure named
      CPInject _ p -> variantPayloadLL v >>= \pl -> go pl p
      CPInjectRest _ -> pure [v]
      CPOr _ _ -> pure [] -- only non-binding ors could reach here; deferred anyway

-- | @kctor_arg(v, kctor_argc(v) - nps + i)@ as SSA: read the field count,
-- compute the absolute index, then the field.  Matches C's 'ctorArgExpr' — the
-- M-C offset that drops the leading (non-bound) constructor arguments.
ctorArgLL :: Text -> Int -> Int -> Gen Text
ctorArgLL v nps i = do
  declRuntime "declare i32 @kctor_argc(ptr)"
  declRuntime "declare ptr @kctor_arg(ptr, i32)"
  argc <- freshReg
  emit (argc <> " = call i32 @kctor_argc(ptr " <> v <> ")")
  idx <- freshReg
  -- kctor_argc(v) - nps + i  (nps and i are compile-time constants)
  emit (idx <> " = add i32 " <> argc <> ", " <> T.pack (show (i - nps)))
  r <- freshReg
  emit (r <> " = call ptr @kctor_arg(ptr " <> v <> ", i32 " <> idx <> ")")
  pure r

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
-- A do-block lowers to a @krt2_*@ ACTION TREE — the uniform CPS path the
-- kappart2 CK-machine ('krt2_run_main') drives.  This mirrors the C backend's
-- 'cpsItems' shape (C.hs:3006) rather than its synchronous @kio@ bridge: parity
-- first, one lowering for both the sequential and the (future) suspending case.
-- The whole block compiles to a single 'KValue*' operand — a @krt2_pure@ leaf,
-- or a @krt2_bind@/@krt2_then@ spine whose tail is the block's final action.
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
-- SUPPORTED items (the linear bind/let/action/final subset): 'KBind' (monadic
-- @x <- action@), 'KExpr' (a plain action), 'KLet' (a pure binding — no krt2
-- node), and the terminal item (a final action / @pure e@).  A bind/let whose
-- binder is a constructor/tuple PATTERN is lowered as a bind-to-fresh-var
-- followed by a 'CMatch' (via 'matchAfterBind').  Everything else — the loop
-- family ('KWhile'/'KFor'), 'KVarItem'/'KAssign' (mutable cells),
-- 'KReturn'/'KBreak'/'KContinue' (abrupt control), 'KDefer', 'KIf', 'KUsing',
-- 'KSubDo', 'KLetQ' — is a later milestone and is reported as a clean
-- @E_BACKEND_UNSUPPORTED@ (never miscompiled).
compileDo :: Maybe Text -> [KItem] -> Gen Text
compileDo _lbl items
  -- The optional scope label is only observable through §18.7 defers / labeled
  -- abrupt control, all of which are deferred below; for the linear subset it
  -- has no runtime effect, so it is ignored here (parity with the C CPS path,
  -- which threads it only through 'krt2_doscope').
  | Just bad <- firstUnsupportedItem items = unsupportedDoItem bad
  | otherwise = cpsItemsLL items

-- | The first do-item outside the supported subset, if any — used to fail the
-- WHOLE block closed (a clean unsupported) before emitting a partial tree, so a
-- deferred construct can never be silently dropped.  The supported set is the
-- Milestone-E linear bind/let/action items plus (Milestone F) a do-kernel @if@
-- whose branches are themselves entirely supported (recurse into each branch and
-- the optional else, so an unsupported item nested in a branch is caught here too
-- rather than mis-lowered when the branch is built).
-- Milestone G adds the imperative do-kernel: mutable cells ('KVarItem'/
-- 'KAssign'), the @while@ loop ('KWhile') with an UNLABELED @break@/@continue@
-- ('KBreak'/'KContinue' over 'Nothing'), and early @return@ ('KReturn').  A
-- LABELED loop / @break@ / @continue@, a @while@-@else@, 'KFor', 'KDefer',
-- 'KUsing', 'KSubDo', and 'KLetQ' remain deferred (they fail the block closed).
firstUnsupportedItem :: [KItem] -> Maybe KItem
firstUnsupportedItem = go
  where
    go [] = Nothing
    go (it : rest) = case it of
      KBind {} -> go rest
      KExpr {} -> go rest
      KLet {} -> go rest
      KVarItem {} -> go rest
      KAssign {} -> go rest
      KReturn {} -> go rest
      KBreak Nothing -> go rest
      KContinue Nothing -> go rest
      -- §18.8 while: only the UNLABELED, else-less form is lowered, and its body
      -- must be entirely supported too — recurse into it so a deferred item nested
      -- in the loop is caught here rather than mis-lowered.  (A labeled loop or a
      -- while-else hits the catch-all below and fails the block closed.)  The
      -- condition itself is lowered by 'compileMonadicCond'; the only shape it
      -- cannot handle is an `__runIO` splice over an action outside this backend's
      -- prim coverage, which is reported as a clean unsupported at compile time.
      KWhile Nothing _cond body Nothing ->
        case go body of
          Just bad -> Just bad
          Nothing -> go rest
      KIf alts mels ->
        case msum (map (go . snd) alts) `mplus` (mels >>= go) of
          Just bad -> Just bad
          Nothing -> go rest
      -- Milestone M: a statement-position sub-do is supported — recurse into its
      -- items so a genuinely-unsupported inner item still fails the block closed.
      -- The label is ignored (a labeled sub-scope's break@L/continue@L would show
      -- up as a labeled KBreak/KContinue nested here and be rejected by 'go').
      KSubDo _lbl subItems ->
        case go subItems of
          Just bad -> Just bad
          Nothing -> go rest
      _ -> Just it

-- | Report a do-item this backend cannot yet lower.  Milestone E covered the
-- linear bind/let/action subset; Milestone F the do-kernel @if@; Milestone G the
-- imperative kernel (mutable cells, the UNLABELED @while@/@break@/@continue@, and
-- @return@).  Still deferred: a LABELED loop / break / continue, a @while@-@else@,
-- 'KFor', 'KDefer', 'KUsing', 'KSubDo', and 'KLetQ' — each fails the block closed.
unsupportedDoItem :: KItem -> Gen Text
unsupportedDoItem it =
  unsupported "do-kernel"
    ( "the LLVM backend does not yet lower this do-kernel item (use the C "
        <> "backend): "
        <> doItemKind it
    )

-- | A short label for an unsupported do-item, for the diagnostic.
doItemKind :: KItem -> Text
doItemKind = \case
  KLetQ {} -> "let? (fallible binding)"
  KVarItem {} -> "var (mutable cell)"
  KAssign {} -> "assignment"
  KReturn {} -> "return"
  KBreak (Just l) -> "labeled break@" <> l
  KBreak Nothing -> "break"
  KContinue (Just l) -> "labeled continue@" <> l
  KContinue Nothing -> "continue"
  KWhile (Just l) _ _ _ -> "labeled while loop (@" <> l <> ")"
  KWhile _ _ _ (Just _) -> "while loop with an else block"
  KWhile {} -> "while loop"
  KFor {} -> "for loop"
  KIf {} -> "do-if"
  KDefer {} -> "defer"
  KUsing {} -> "using"
  KSubDo {} -> "statement-position sub-do"
  _ -> "this construct"

-- | Lower a linear do-block to its @krt2_*@ action tree (mirrors C's 'cpsItems',
-- C.hs:3006).  An empty block is @krt2_pure(kunit())@; the FINAL item is the
-- block's action (compiled directly, in tail-ish position — its own value); a
-- non-final bind/action becomes a @krt2_bind@ over a lazily-compiled
-- continuation closure; a non-final let is a pure binding compiled INLINE
-- (extending the env for the rest, then restored).
cpsItemsLL :: [KItem] -> Gen Text
cpsItemsLL items = case items of
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
  [KExpr t] -> compileMonadicAction t
  [KBind _ _ t] -> compileMonadicAction t
  -- FINAL let: a pure binding with no following action is degenerate (the block
  -- must end in an action), but lower it as @pure(value)@ for totality.
  -- A FINAL let.  If its rhs reads `var`s (a splice), it must be a re-runnable
  -- value-action ('compileMonadic' — which already yields an IO action delivering
  -- the value); the pattern binding is moot since nothing follows.  Otherwise the
  -- pure value is bound and `krt2_pure`d.
  [KLet _ _ t] | hasSpliceLL t -> compileMonadic t
  [KLet _ pat t] -> do
    te <- compile t
    declRuntime "declare ptr @krt2_pure(ptr)"
    -- bind the value (so a constructor pattern is still well-typed) then pure it
    _ <- bindPatDo te pat
    r <- freshReg
    emit (r <> " = call ptr @krt2_pure(ptr " <> te <> ")")
    pure r
  -- FINAL do-kernel `if` (Milestone F): the if-action IS the block's result —
  -- lower it to its phi'd action operand and return it directly (no surrounding
  -- bind; the CK-machine drives whichever branch's action the phi selected).
  [KIf alts mels] -> compileDoIf alts mels
  -- A plain ACTION with a following rest: treat as `_ <- action; rest` so REST
  -- stays LAZY inside the continuation closure (NOT krt2_then with an eager rest
  -- operand — that would eagerly build the tail and overflow on IO recursion).
  (KExpr t : rest) -> bindThen t CPWild rest
  -- A monadic bind: `x <- action; rest`.
  (KBind _ pat t : rest) -> bindThen t pat rest
  -- NON-final do-kernel `if` (Milestone F): build the if-action, then sequence
  -- it with REST as `_ <- ifAction; rest` (REST lazy inside a kdo_N closure),
  -- exactly the 'KExpr' shape — the if's own result is discarded (§18.8).
  (KIf alts mels : rest) -> do
    ifAction <- compileDoIf alts mels
    seqActionThen ifAction CPWild rest
  -- A pure LET binding: compile e, kpush, compile REST under the extended env
  -- (restored after).  No krt2 node — the runtime never sees this binding.
  -- A `let` whose rhs reads `var`s (e.g. `let t = addInt a b` in a loop body):
  -- the rhs is a re-runnable value-action; bind its delivered value to @pat@ via
  -- the same lazy continuation machinery as a 'KBind', so REST sees @pat@ at de
  -- Bruijn 0.  The pure (linear) case keeps the cheap build-time `kpush` (no krt2
  -- node — the runtime never sees a splice-free binding).
  (KLet _ pat t : rest) | hasSpliceLL t -> do
    m <- compileMonadic t
    seqActionThen m pat rest
  (KLet _ CPWild t : rest) -> do
    _ <- compile t -- evaluated for its (pure) value; result discarded
    cpsItemsLL rest
  (KLet _ pat t : rest) -> do
    te <- compile t
    env0 <- gets gsEnv
    env1 <- bindPatDo te pat
    modify' $ \g -> g {gsEnv = env1}
    r <- cpsItemsLL rest
    modify' $ \g -> g {gsEnv = env0}
    pure r
  -- ── Milestone G: the imperative do-kernel ──────────────────────────
  -- ── FINAL imperative items (the block's tail action) ──────────────
  -- A FINAL `var` is degenerate (a do-block ends in an action), but the newRef
  -- IS an action — return it directly.  A FINAL assignment is its writeRef
  -- action; a FINAL return/break/continue/while is its own action operand.
  [KVarItem _ e] -> newRefAction e
  [KAssign refT _ rhsT] -> writeRefAction refT rhsT
  [KReturn e] -> returnAction e
  [KBreak Nothing] -> breakAction
  [KContinue Nothing] -> continueAction
  [KWhile Nothing cond body Nothing] -> whileAction cond body
  -- ── NON-final imperative items (sequenced with the rest) ──────────
  -- `var x = e` ≡ `x <- newRef e`: the action is a `newRef` IO node (built via
  -- the prim path), bound like a 'KBind' so the slot at de Bruijn 0 holds the
  -- Ref.  A source `readRef x` (already a `__runIO (readRef x)` splice in Core)
  -- then reads it through 'compileMonadic'; an assignment is 'KAssign'.
  (KVarItem x e : rest) -> do
    refAct <- newRefAction e
    seqActionThen refAct (CPVar x) rest
  -- `x = e` (pure rhs) / `x <- e` (monadic rhs): a `writeRef ref val` IO action,
  -- sequenced like a 'KExpr' (`_ <- writeAction; rest`).  For a monadic rhs the
  -- value is the result of running e first ('emitAssignCont' binds it, then the
  -- continuation writes); for a pure rhs the value is e's compiled operand.
  (KAssign refT monadic rhsT : rest)
    | monadic -> do
        -- `x <- e`: bind e's result, then writeRef ref boundResult; rest.
        rhsAct <- compileMonadic rhsT
        contFn <- emitAssignCont refT rest
        capturedEnv <- gets gsEnv
        declRuntime "declare ptr @kclo(ptr, ptr)"
        declRuntime "declare ptr @krt2_bind(ptr, ptr)"
        k <- freshReg
        emit (k <> " = call ptr @kclo(ptr @" <> contFn <> ", ptr " <> capturedEnv <> ")")
        r <- freshReg
        emit (r <> " = call ptr @krt2_bind(ptr " <> rhsAct <> ", ptr " <> k <> ")")
        pure r
    | otherwise -> do
        writeAct <- writeRefAction refT rhsT
        seqActionThen writeAct CPWild rest
  -- `return e`: an early-return IO action (`krt2_return value`).  Whatever
  -- follows in the items list is dead (return unwinds the fiber), but it is
  -- sequenced uniformly anyway — the CK-machine never delivers past the return.
  (KReturn e : rest) -> do
    retAct <- returnAction e
    seqActionThen retAct CPWild rest
  -- `break` / `continue` (unlabeled): an abrupt-control IO action targeting the
  -- innermost enclosing `krt2_while`.  Like 'KReturn', anything after is dead.
  (KBreak Nothing : rest) -> do
    a <- breakAction
    seqActionThen a CPWild rest
  (KContinue Nothing : rest) -> do
    a <- continueAction
    seqActionThen a CPWild rest
  -- `while cond do body` (unlabeled, no else): `krt2_while(condIO, bodyIO)`,
  -- where condIO re-reads its `var`s each iteration ('compileMonadicCond') and
  -- bodyIO is the body's own action tree ('compileLoopBody').  Sequenced like a
  -- 'KExpr' (`_ <- whileAction; rest`) — the while's normal completion is Unit.
  (KWhile Nothing cond body Nothing : rest) -> do
    whileAct <- whileAction cond body
    seqActionThen whileAct CPWild rest
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
  [KSubDo _lbl subItems] -> cpsItemsLL subItems
  (KSubDo _lbl subItems : rest) -> do
    subAct <- cpsItemsLL subItems
    seqActionThen subAct CPWild rest
  (it : _) -> unsupportedDoItem it

-- | Lower `pat <- action; rest` (or `action; rest` with @pat = CPWild@) as
-- @krt2_bind(action, kclo(@kdo_N, env))@, where @kdo_N@ is a lifted continuation
-- closure that receives the delivered value, binds it to @pat@, and compiles
-- REST as an action tree.  The rest lives INSIDE @kdo_N@ — that laziness is what
-- keeps an IO-recursive do-block stack-safe (the tree is built one bind at a
-- time as the CK-machine runs it, not all at once at build time).
bindThen :: Term -> CorePat -> [KItem] -> Gen Text
bindThen action pat rest = do
  -- The action term may carry `__runIO` `var`-read splices (e.g. a `KExpr`
  -- `printlnString (showInt (readRef i))` inside a loop body); 'compileMonadicAction'
  -- hoists them so the reads re-execute, and is a plain 'compile' when there are
  -- none (so the linear-do path is unchanged).
  m <- compileMonadicAction action
  seqActionThen m pat rest

-- | Sequence an ALREADY-COMPILED action operand @m@ with the rest of the block:
-- @krt2_bind(m, kclo(@kdo_N, env))@ where @kdo_N@ binds the delivered value to
-- @pat@ and lowers REST.  Same machinery as 'bindThen' but the action is a value
-- operand the caller already produced (e.g. a do-kernel @if@'s phi'd action),
-- not a 'Term' to compile.  Keeps REST lazy inside @kdo_N@ for stack safety.
seqActionThen :: Text -> CorePat -> [KItem] -> Gen Text
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
-- ('compileMonadicCond' — it re-reads its `var`s each iteration) and the branch
-- is chosen INSIDE a lifted selector closure that the CK-machine re-invokes with
-- the freshly-evaluated condition value: @krt2_bind(condIO, kclo(@doifsel))@.  The
-- selector @br i1@s on @kas_bool(%cond)@ and RETURNS the taken branch's action
-- (built fresh each invocation), so the choice re-decides every iteration.  This
-- is also correct (just slightly less direct) for a non-loop / recursive do-if,
-- where the containing closure would rebuild the tree each call anyway.
compileDoIf :: [(Term, [KItem])] -> Maybe [KItem] -> Gen Text
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
      -- condIO re-evaluates the guard (re-reading `var`s) each time it runs.
      condIO <- compileMonadicCond cond
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
      pure a
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
emitDoCont :: CorePat -> [KItem] -> Gen Text
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
bindPatDo :: Text -> CorePat -> Gen Text
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

-- ── Milestone G: the imperative do-kernel ────────────────────────────
--
-- Mutable cells, `while` loops, and abrupt control, lowered onto the kappart2
-- CK-machine the do-kernel already uses (NOT the C backend's synchronous
-- `goto`/`krun_io` loop, which is a Phase-2 perf path).  The load-bearing fact:
-- `krt2_while(condIO, bodyIO)` RE-RUNS both action operands every iteration
-- (rt.c OP_WHILE → KK_LOOP), so a `var` read re-evaluates for free PROVIDED the
-- read is an IO ACTION (a `knative_sat(kpf_io_readRef,…)` node whose `kref_get`
-- fires when the CK-machine runs it), not a value frozen at build time.
--
-- A source `var` read arrives in Core as a `__runIO (readRef <ref>)` MONADIC
-- SPLICE buried in an otherwise-pure term (e.g. `ltInt (__runIO (readRef i)) 3`).
-- 'compileMonadic' turns such a term into a re-runnable action by HOISTING each
-- splice into a `krt2_bind` (the read becomes a real action; its delivered value
-- is bound and the pure residual `krt2_pure`d) — the standard monadic-normal-form
-- lift.  A wholly-monadic condition (`while check i`, elaborated to `__runIO
-- actTm`) is just `actTm` directly.

-- | Recognise a @__runIO action@ monadic splice and return the single explicit
-- action argument (mirrors C's 'runIOSplice').  Implicit type arguments are
-- erased.
runIOSpliceLL :: Term -> Maybe Term
runIOSpliceLL t = case spineOf t of
  (CGlob (GName _ "__runIO"), args)
    | [a] <- [x | (Expl, x) <- args] -> Just a
  _ -> Nothing

-- | Shift every FREE de Bruijn index (one at cutoff @c@ or above) in a term by
-- @d@.  Used by 'compileMonadic' when a hoisted splice pushes one fresh env slot
-- under which the pure residual is re-expressed (so the residual's references to
-- the enclosing scope stay correct after the push).  A complete traversal over
-- 'Term' / 'CaseAlt' / 'CorePat', incrementing the cutoff under every binder.
shiftTerm :: Int -> Int -> Term -> Term
shiftTerm d = goT
  where
    goT c = \case
      CVar i -> CVar (if i >= c then i + d else i)
      CGlob g -> CGlob g
      CLam ic q n b -> CLam ic q n (goT (c + 1) b)
      CPi ic q bw n ty b -> CPi ic q bw n (goT c ty) (goT (c + 1) b)
      CApp ic f a -> CApp ic (goT c f) (goT c a)
      CSort u -> CSort u
      CLit l -> CLit l
      CCtor g as -> CCtor g (map (goT c) as)
      CMatch s alts -> CMatch (goT c s) (map (goAlt c) alts)
      CRecordT fs -> CRecordT [(k, goT c v) | (k, v) <- fs]
      CRecordV fs -> CRecordV [(k, goT c v) | (k, v) <- fs]
      CProj e f -> CProj (goT c e) f
      CProjAt e f i -> CProjAt (goT c e) f i
      CVariantT ts -> CVariantT (map (goT c) ts)
      CInject l e -> CInject l (goT c e)
      CLet q n ty rhs body -> CLet q n (goT c ty) (goT c rhs) (goT (c + 1) body)
      CLetRec q n ty rhs body -> CLetRec q n (goT c ty) (goT (c + 1) rhs) (goT (c + 1) body)
      CMeta m -> CMeta m
      CDo lbl items -> CDo lbl (goItems c items)
      CSealE ls e -> CSealE ls (goT c e)
      CSigT ls e -> CSigT ls (goT c e)
      CThunkE e -> CThunkE (goT c e)
      CLazyE e -> CLazyE (goT c e)
      CForceE e -> CForceE (goT c e)
      CIf cc th el -> CIf (goT c cc) (goT c th) (goT c el)
      CQuote q ts -> CQuote q (map (goT c) ts)
    goAlt c (CaseAlt pat mg body) =
      let n = patArity pat
       in CaseAlt pat (goT (c + n) <$> mg) (goT (c + n) body)
    -- KItems run under accumulating binders; shifting do-kernel items here is
    -- only reached if a residual contains a nested do, which the loop corpus
    -- does not produce — a conservative same-cutoff walk keeps it total.
    goItems _ = id

-- | The number of binders a 'CorePat' introduces (for 'shiftTerm''s cutoff under
-- a 'CaseAlt').  Mirrors the left-to-right binder count the match path pushes.
patArity :: CorePat -> Int
patArity = \case
  CPWild -> 0
  CPVar _ -> 1
  CPLit _ -> 0
  CPCtor _ ps -> sum (map patArity ps)
  CPTuple ps -> sum (map patArity ps)
  CPRecord fs _ -> sum (map (patArity . snd) fs)
  CPInject _ p -> patArity p
  CPInjectRest _ -> 0
  CPOr (p : _) _ -> patArity p
  CPOr [] _ -> 0
  CPAs _ p -> 1 + patArity p

-- | Find the leftmost (first-to-evaluate) @__runIO action@ splice that sits at
-- binder depth 0 within @t@ (i.e. not under a local lambda/let/match binder),
-- and return its action together with @t@ rewritten so that occurrence becomes a
-- reference to a freshly-pushed slot: every other free var is shifted by +1 and
-- the splice itself is 'CVar 0'.  'Nothing' when @t@ has no liftable splice (it
-- is then a pure residual).  Splice search follows evaluation order (function
-- before argument) so reads are sequenced as written.
liftFirstSplice :: Term -> Maybe (Term, Term)
liftFirstSplice t0
  | Just _ <- runIOSpliceLL t0 = Nothing -- the WHOLE term is a splice: handled directly
  | otherwise = case go t0 of
      Nothing -> Nothing
      Just (action, residual) -> Just (action, residual)
  where
    -- Returns (action, residual) where residual is @t@ with the found splice
    -- replaced by 'CVar 0' and all of t's own free vars shifted +1.
    go :: Term -> Maybe (Term, Term)
    go t = case runIOSpliceLL t of
      Just action -> Just (action, CVar 0) -- this node IS a splice → slot 0
      Nothing -> case t of
        CApp ic f a -> case go f of
          Just (act, f') -> Just (act, CApp ic f' (shiftTerm 1 0 a))
          Nothing -> case go a of
            Just (act, a') -> Just (act, CApp ic (shiftTerm 1 0 f) a')
            Nothing -> Nothing
        CCtor g as -> goList as (CCtor g)
        CIf c th el -> case go c of
          Just (act, c') -> Just (act, CIf c' (shiftTerm 1 0 th) (shiftTerm 1 0 el))
          Nothing -> Nothing
        _ -> Nothing
    -- Lift the first splice across a list of subterms (left to right), shifting
    -- the untouched siblings +1 and rebuilding via @mk@.
    goList :: [Term] -> ([Term] -> Term) -> Maybe (Term, Term)
    goList xs mk = goAt [] xs
      where
        goAt _ [] = Nothing
        goAt before (x : after) = case go x of
          Just (act, x') ->
            Just (act, mk (map (shiftTerm 1 0) (reverse before) ++ x' : map (shiftTerm 1 0) after))
          Nothing -> goAt (x : before) after

-- | True if a value-position term carries a `__runIO` `var`-read splice (a whole-
-- term splice, or one buried inside a larger pure term), so it must be lowered as
-- a re-runnable IO action via 'compileMonadic' rather than the build-time 'compile'
-- (which would hit the unlowered @__runIO@ primitive).  In the imperative do-kernel
-- a @let@/@var@ rhs over `var`s (e.g. @let t = addInt a b@) is exactly this case.
hasSpliceLL :: Term -> Bool
hasSpliceLL t
  | Just _ <- runIOSpliceLL t = True
  | Just _ <- liftFirstSplice t = True
  | otherwise = False

-- | Compile a value-position term that may carry @__runIO@ monadic splices into
-- a re-runnable IO ACTION yielding the term's value.  The whole-term splice case
-- (@__runIO actTm@, a monadic `while` condition) is the action itself; otherwise
-- each splice is hoisted into a `krt2_bind` (so a `var` read re-executes each
-- time the action runs) and the pure residual is `krt2_pure`d.  This is the
-- monadic-normal-form lift; it reuses the do-kernel's lazy continuation closures
-- ('emitDoCont') so the spine stays bounded.
compileMonadic :: Term -> Gen Text
compileMonadic = compileMonadicAs ResValue

-- | Lower an ACTION-position term that may carry `__runIO` splices to a
-- re-runnable IO action.  Same hoist as 'compileMonadic', but the residual IS
-- itself an action (e.g. `printlnString (showInt (readRef i))`), so it is
-- compiled DIRECTLY — never `krt2_pure`-wrapped (which would give @IO (IO a)@).
compileMonadicAction :: Term -> Gen Text
compileMonadicAction = compileMonadicAs ResAction

-- | Whether the residual of a splice lift is a VALUE (wrap in @krt2_pure@) or an
-- ACTION (compile directly).  A `while` condition / assignment rhs is a value; a
-- `KExpr` / bind action term is an action.
data ResidualKind = ResValue | ResAction

compileMonadicAs :: ResidualKind -> Term -> Gen Text
compileMonadicAs rk t
  | ResAction <- rk, Just action <- runIOSpliceLL t = compile action
  | ResValue <- rk, Just action <- runIOSpliceLL t = compile action
  | otherwise = case liftFirstSplice t of
      Nothing -> case rk of
        ResAction -> compile t -- the residual is the action itself
        ResValue -> do
          -- No splice: a pure value lifted into the IO monad.
          v <- compile t
          declRuntime "declare ptr @krt2_pure(ptr)"
          r <- freshReg
          emit (r <> " = call ptr @krt2_pure(ptr " <> v <> ")")
          pure r
      Just (action, residual) -> do
        -- Bind the splice's action; in the continuation, the delivered value is
        -- pushed at slot 0 and the residual (now an action) is built lazily.
        m <- compile action
        contFn <- emitMonadicCont rk residual
        capturedEnv <- gets gsEnv
        declRuntime "declare ptr @kclo(ptr, ptr)"
        declRuntime "declare ptr @krt2_bind(ptr, ptr)"
        k <- freshReg
        emit (k <> " = call ptr @kclo(ptr @" <> contFn <> ", ptr " <> capturedEnv <> ")")
        r <- freshReg
        emit (r <> " = call ptr @krt2_bind(ptr " <> m <> ", ptr " <> k <> ")")
        pure r

-- | Emit a continuation closure for 'compileMonadicAs': the delivered splice
-- value is pushed at env slot 0 (the 'CVar 0' the residual references) and the
-- residual term is compiled (recursing for any further splices, preserving the
-- residual kind).  The same lifted-`kfn` shape as 'emitDoCont'.
emitMonadicCont :: ResidualKind -> Term -> Gen Text
emitMonadicCont rk residual = do
  fnIdent <- freshLabel "kmc_"
  declRuntime "declare ptr @kpush(ptr, ptr)"
  (bodyInsns, _endBlock, resultOp) <- captured "%cenv" $ do
    env1 <- freshReg
    emit (env1 <> " = call ptr @kpush(ptr %arg, ptr %cenv)")
    modify' $ \g -> g {gsEnv = env1}
    compileMonadicAs rk residual
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

-- | The @newRef e@ IO action for a @var x = e@ (or @x <- newRef e@).  A SPLICE-FREE
-- init is a saturated `newRef` prim application through the existing IO-prim path
-- (@knative_sat(kpf_io_newRef, [e], isio=1)@).  An init that reads `var`s (e.g.
-- @var b = addInt a 3@) is built as a re-runnable value-action via 'compileMonadic',
-- whose delivered value is `newRef`-ed in the continuation — symmetric with
-- 'writeRefAction'.
newRefAction :: Term -> Gen Text
newRefAction e
  | not (hasSpliceLL e) = compilePrimApp "newRef" [(Expl, e)]
  | otherwise = do
      initAct <- compileMonadic e
      contFn <- emitNewRefCont
      capturedEnv <- gets gsEnv
      declRuntime "declare ptr @kclo(ptr, ptr)"
      declRuntime "declare ptr @krt2_bind(ptr, ptr)"
      k <- freshReg
      emit (k <> " = call ptr @kclo(ptr @" <> contFn <> ", ptr " <> capturedEnv <> ")")
      r <- freshReg
      emit (r <> " = call ptr @krt2_bind(ptr " <> initAct <> ", ptr " <> k <> ")")
      pure r

-- | Build a @newRef@ IO action from an already-compiled init-value operand
-- (a direct @knative_sat(kpf_io_newRef, [val], 1)@).
newRefValueAction :: Text -> Gen Text
newRefValueAction valOp = do
  argv <- freshReg
  emit (argv <> " = alloca [1 x ptr], align 8")
  s0 <- freshReg
  emit (s0 <> " = getelementptr inbounds [1 x ptr], ptr " <> argv <> ", i64 0, i64 0")
  emit ("store ptr " <> valOp <> ", ptr " <> s0 <> ", align 8")
  declRuntime "declare ptr @knative_sat(ptr, i32, ptr, i32)"
  declRuntime "declare ptr @kpf_io_newRef(ptr)"
  r <- freshReg
  emit (r <> " = call ptr @knative_sat(ptr @kpf_io_newRef, i32 1, ptr " <> argv <> ", i32 1)")
  pure r

-- | A continuation closure for a splicey @var x = e@: the delivered init value
-- arrives at @%arg@ and is @newRef@-ed as the tail action (the resulting Ref is the
-- bound value).  No env push — @%arg@ is consumed by the newRef.
emitNewRefCont :: Gen Text
emitNewRefCont = do
  fnIdent <- freshLabel "knr_"
  (bodyInsns, _endBlock, resultOp) <- captured "%cenv" (newRefValueAction "%arg")
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

-- | The @writeRef ref val@ IO action for an assignment.  @val@ may itself carry
-- `__runIO` splices (e.g. @addInt (readRef x) 1@), so it is compiled through
-- 'compileMonadic' — but the result must be a plain VALUE for `writeRef`'s second
-- argument, so a splicey rhs is sequenced first via 'compileMonadic' and the
-- write happens in its continuation.  The common case (a rhs with splices) is
-- handled by 'KAssign''s own bind in 'cpsItemsLL'; here we cover the SPLICE-FREE
-- rhs as a single `writeRef` action.
writeRefAction :: Term -> Term -> Gen Text
writeRefAction refT rhsT
  | Nothing <- liftFirstSplice rhsT
  , Nothing <- runIOSpliceLL rhsT =
      -- Splice-free rhs: a single writeRef action over the compiled value.
      compilePrimApp "writeRef" [(Expl, refT), (Expl, rhsT)]
  | otherwise = do
      -- The rhs reads `var`s: build it as an action, bind the value, then write.
      rhsAct <- compileMonadic rhsT
      contFn <- emitAssignCont' refT
      capturedEnv <- gets gsEnv
      declRuntime "declare ptr @kclo(ptr, ptr)"
      declRuntime "declare ptr @krt2_bind(ptr, ptr)"
      k <- freshReg
      emit (k <> " = call ptr @kclo(ptr @" <> contFn <> ", ptr " <> capturedEnv <> ")")
      r <- freshReg
      emit (r <> " = call ptr @krt2_bind(ptr " <> rhsAct <> ", ptr " <> k <> ")")
      pure r

-- | A continuation closure that, given the delivered rhs value at @%arg@, emits
-- @writeRef ref %arg@ as the tail action.  @ref@ is re-compiled inside the
-- closure under the captured env (a `var` ref is just an env read, so this is
-- a `kvar` — cheap and correct).  Used by 'writeRefAction' for a splicey rhs.
emitAssignCont' :: Term -> Gen Text
emitAssignCont' refT = do
  fnIdent <- freshLabel "kwr_"
  -- The captured %cenv IS the enclosing env; the ref term reads from it with no
  -- shift, and the delivered rhs value is %arg (no env push needed).
  (bodyInsns, _endBlock, resultOp) <- captured "%cenv" $ do
    re <- compile refT
    writeRefValueAction re "%arg"
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

-- | Build a @writeRef@ IO action from already-compiled ref and value operands
-- (a direct @knative_sat(kpf_io_writeRef, [ref,val], 1)@), bypassing the prim
-- argument-compilation path since both operands are in hand.
writeRefValueAction :: Text -> Text -> Gen Text
writeRefValueAction refOp valOp = do
  argv <- freshReg
  emit (argv <> " = alloca [2 x ptr], align 8")
  s0 <- freshReg
  emit (s0 <> " = getelementptr inbounds [2 x ptr], ptr " <> argv <> ", i64 0, i64 0")
  emit ("store ptr " <> refOp <> ", ptr " <> s0 <> ", align 8")
  s1 <- freshReg
  emit (s1 <> " = getelementptr inbounds [2 x ptr], ptr " <> argv <> ", i64 0, i64 1")
  emit ("store ptr " <> valOp <> ", ptr " <> s1 <> ", align 8")
  declRuntime "declare ptr @knative_sat(ptr, i32, ptr, i32)"
  declRuntime "declare ptr @kpf_io_writeRef(ptr)"
  r <- freshReg
  emit (r <> " = call ptr @knative_sat(ptr @kpf_io_writeRef, i32 2, ptr " <> argv <> ", i32 1)")
  pure r

-- | A continuation closure for a MONADIC assignment (@x <- e@): the delivered
-- result of running @e@ arrives at @%arg@ and is written to @ref@, then the rest
-- of the block runs.  An assignment introduces NO new env binder (it mutates an
-- existing ref), so @ref@ and the rest read the captured @%cenv@ with no shift;
-- @%arg@ is consumed by the write, not pushed.
emitAssignCont :: Term -> [KItem] -> Gen Text
emitAssignCont refT rest = do
  fnIdent <- freshLabel "kasgk_"
  declRuntime "declare ptr @krt2_then(ptr, ptr)"
  -- The captured %cenv IS the enclosing env: `x <- e` writes to an existing ref,
  -- introducing NO new binder, so both the ref term and `rest` use %cenv with no
  -- shift.  The delivered rhs result (%arg) is written, not bound into the env.
  (bodyInsns, _endBlock, resultOp) <- captured "%cenv" $ do
    re <- compile refT
    writeAct <- writeRefValueAction re "%arg"
    -- _ <- writeRef ref value; rest  (rest sequenced after the write completes;
    -- writeRef has no result to bind, so krt2_then is exact).
    restAct <- cpsItemsLL rest
    r <- freshReg
    emit (r <> " = call ptr @krt2_then(ptr " <> writeAct <> ", ptr " <> restAct <> ")")
    pure r
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

-- | The @return e@ early-exit IO action: @krt2_return(value)@.  When @e@ is a
-- splice-free value it is compiled directly; when it carries `var`-read splices
-- (e.g. @return i@ ≡ @return (__runIO (readRef i))@) the read is sequenced as an
-- action FIRST ('compileMonadic') and the @krt2_return@ runs in its continuation,
-- so the returned value is the freshly-read cell.
returnAction :: Term -> Gen Text
returnAction e
  | Nothing <- liftFirstSplice e
  , Nothing <- runIOSpliceLL e = do
      v <- compile e
      declRuntime "declare ptr @krt2_return(ptr)"
      r <- freshReg
      emit (r <> " = call ptr @krt2_return(ptr " <> v <> ")")
      pure r
  | otherwise = do
      valAct <- compileMonadic e
      contFn <- emitReturnCont
      capturedEnv <- gets gsEnv
      declRuntime "declare ptr @kclo(ptr, ptr)"
      declRuntime "declare ptr @krt2_bind(ptr, ptr)"
      k <- freshReg
      emit (k <> " = call ptr @kclo(ptr @" <> contFn <> ", ptr " <> capturedEnv <> ")")
      r <- freshReg
      emit (r <> " = call ptr @krt2_bind(ptr " <> valAct <> ", ptr " <> k <> ")")
      pure r

-- | A continuation closure that returns @krt2_return(%arg)@ — the delivered value
-- (a freshly-read `var`) is the early-return value.
emitReturnCont :: Gen Text
emitReturnCont = do
  fnIdent <- freshLabel "kret_"
  (bodyInsns, _endBlock, resultOp) <- captured "%cenv" $ do
    declRuntime "declare ptr @krt2_return(ptr)"
    r <- freshReg
    emit (r <> " = call ptr @krt2_return(ptr %arg)")
    pure r
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
whileAction :: Term -> [KItem] -> Gen Text
whileAction cond body = do
  condIO <- compileMonadicCond cond
  bodyIO <- compileLoopBody body
  declRuntime "declare ptr @krt2_while(ptr, ptr)"
  r <- freshReg
  emit (r <> " = call ptr @krt2_while(ptr " <> condIO <> ", ptr " <> bodyIO <> ")")
  pure r

-- | The condition action for a @while@: a re-runnable IO action yielding a Bool.
-- Just 'compileMonadic' — a pure condition lifts its `var` reads into binds and
-- `krt2_pure`s the residual Bool; a monadic `while` condition (`__runIO actTm`)
-- is the action itself.
compileMonadicCond :: Term -> Gen Text
compileMonadicCond = compileMonadic

-- | The body action for a @while@: the body items lowered to a `krt2_*` action
-- tree via 'cpsItemsLL'.  The body runs under the enclosing env (its `var`s are
-- env slots the loop's actions read); 'krt2_while' re-runs this whole action each
-- iteration, and `var` reads inside re-execute because they are IO read actions.
compileLoopBody :: [KItem] -> Gen Text
compileLoopBody body = do
  env0 <- gets gsEnv
  a <- cpsItemsLL body
  modify' $ \g -> g {gsEnv = env0}
  pure a

-- | A short name for the unsupported construct (for the diagnostic detail).
constructName :: Term -> Text
constructName = \case
  CVar {} -> "variable"
  CLam {} -> "lambda"
  CCtor {} -> "constructor"
  CIf {} -> "if"
  CMatch {} -> "match"
  CLet {} -> "let"
  CLetRec {} -> "letrec"
  CDo {} -> "do"
  CRecordV {} -> "record"
  CProj {} -> "projection"
  CProjAt {} -> "projection"
  CInject {} -> "variant-inject"
  CForceE {} -> "force"
  CThunkE {} -> "delay"
  CLazyE {} -> "memo"
  CSealE {} -> "seal"
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
  declRuntime "declare ptr @knative(ptr, i32, ptr, i32)"
  declRuntime ("declare ptr @" <> cfn <> "(ptr)")
  nameG <- internCStr (rns.cSymbol)
  r <- freshReg
  emit (r <> " = call ptr @knative(ptr @" <> cfn <> ", i32 " <> T.pack (show ar)
          <> ", ptr " <> nameG <> ", i32 1)")
  pure r

-- | An application spine: head term plus its arguments with icities
-- (mirrors C's 'spineOf').
spineOf :: Term -> (Term, [(Icit, Term)])
spineOf = go []
  where
    go acc (CApp ic f a) = go ((ic, a) : acc) f
    go acc t = (t, acc)

-- | Compile an application.  A saturated application whose head is a known
-- primitive lowers per its kind: an IO prim to @knative_sat@ (M0, the §2.3
-- lowering); a PURE first-order prim with a direct @kp_*@ helper to a direct
-- positional call (M1, mirroring C's 'primDirect' fast path).  A saturated
-- application whose head is an arity-≥1 global, or an under-/over-saturated
-- prim, is out of Milestone-A scope (general @kapp@/closures are Milestone C)
-- and reported.
compileApp :: Term -> Gen Text
compileApp term
  -- §10.1/P0-A: a saturated application of an ETA-EXPANDED constructor — the
  -- @CApp (… (CLam … (CCtor g [CVar…]))) args@ shape elaboration produces for a
  -- field-carrying constructor occurrence ('etaCtorApp') — beta-reduces to a
  -- direct 'compileCtor'.  This is REQUIRED for Milestone C: a literal @Some 7@
  -- or @Pair a b@ in source arrives here as that redex (only nullary ctors come
  -- through as a bare 'CCtor'), so without it 'match'-on-a-constructed-value and
  -- every field-carrying construction would fall to the unsupported head path.
  | Just (g, ctorArgs) <- etaCtorApp term = compileCtor g ctorArgs
compileApp term = do
  let (hd, sargs) = spineOf term
  case hd of
    CGlob g -> do
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
                explArgs = [a | (Expl, a) <- sargs]
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
compileHostSat :: ResolvedNativeSymbol -> [Term] -> Gen Text
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
  declRuntime "declare ptr @knative_sat(ptr, i32, ptr, i32)"
  declRuntime ("declare ptr @" <> cfn <> "(ptr)")
  r <- freshReg
  emit (r <> " = call ptr @knative_sat(ptr @" <> cfn <> ", i32 "
          <> T.pack (show ar) <> ", ptr " <> argv <> ", i32 1)")
  pure r

-- | The general application path (Milestone D): a curried @kapp@ chain over the
-- compiled head and arguments — @f x y@ ⇒ @kapp(kapp(compile f, compile x),
-- compile y)@ (mirrors C's 'compileAppDefault', C.hs:2262).  An EXPLICIT
-- argument is applied with @kapp@; an IMPLICIT argument to an ERASED head (a
-- prim or constructor, §31.2) is DROPPED, otherwise it is applied with @kappi@
-- (the runtime's implicit-application entry).  A non-application term is just
-- 'compile'd (the recursion base case).
compileAppDefault :: Term -> Gen Text
compileAppDefault = \case
  CApp Expl f a -> do
    fe <- compile f
    ae <- compileErasableArg a -- §31.2: an explicit type-level/staging arg is erased
    declRuntime "declare ptr @kapp(ptr, ptr)"
    r <- freshReg
    emit (r <> " = call ptr @kapp(ptr " <> fe <> ", ptr " <> ae <> ")")
    pure r
  CApp Impl f a -> do
    erased <- isErasedHead f
    if erased
      then compile f -- implicit arg to a prim/constructor: erased (§31.2)
      else do
        fe <- compile f
        ae <- compileErasableArg a
        declRuntime "declare ptr @kappi(ptr, ptr)"
        r <- freshReg
        emit (r <> " = call ptr @kappi(ptr " <> fe <> ", ptr " <> ae <> ")")
        pure r
  t -> compile t

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
isErasedHead :: Term -> Gen Bool
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
headGlob :: Term -> Maybe GName
headGlob = \case
  CGlob g -> Just g
  CApp _ f _ -> headGlob f
  _ -> Nothing

isVPrimValue :: Maybe Value -> Bool
isVPrimValue (Just (VPrim _ _)) = True
isVPrimValue _ = False

-- | Is this argument purely type-level (computationally erased)?  Type-level
-- forms and references to type/trait globals are erasable; everything else is
-- compiled for real.
isErasableArg :: Term -> Gen Bool
isErasableArg = \case
  CSort _ -> pure True
  CPi {} -> pure True
  CVariantT _ -> pure True
  CRecordT _ -> pure True
  CSigT {} -> pure True
  CMeta _ -> pure True
  CQuote {} -> pure True
  CApp _ f _ -> isErasableArg f -- the spine head decides (e.g. @(List a))
  CGlob g -> isTypeGlob g
  _ -> pure False

-- | Compile a value-position argument, erasing it to the @kunit()@ placeholder
-- when it is a type-level / staging term (§12.2, §31.2).
compileErasableArg :: Term -> Gen Text
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
etaCtorApp :: Term -> Maybe (GName, [Term])
etaCtorApp term =
  case spineOf term of
    (hd, sargs)
      | (k, body) <- funcArity hd
      , k >= 1
      , k == length sargs
      , CCtor g fieldVars <- body ->
          (,) g <$> traverse (pick (map snd sargs) k) fieldVars
    _ -> Nothing
  where
    pick args k = \case
      CVar j | j >= 0, j < k -> Just (args !! (k - 1 - j))
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
compilePrimApp :: Text -> [(Icit, Term)] -> Gen Text
compilePrimApp pname sargs
  -- Milestone M: the EXCEPTION ops are NODE-BUILDERS on the uniform CK-machine
  -- path, NOT the synchronous @kpf_io_*@ bridge — they MUST be intercepted here
  -- before the generic 'ioPrimEntry'/@knative_sat@ arm (mirrors how the C
  -- backend special-cases catchIO/finallyIO/throwIO to @krt2_*@ in
  -- 'compileAppGlob', and how this backend would otherwise mis-run a do-block
  -- body through the bridge — the M-I divergence).  See 'compileExnNode'.
  | Just r <- exnNodeBuilder pname = compileExnNode pname r sargs
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
exnNodeBuilder :: Text -> Maybe (Text, Int)
exnNodeBuilder = \case
  "catchIO" -> Just ("krt2_catch", 2)
  "finallyIO" -> Just ("krt2_finally", 2)
  "throwIO" -> Just ("krt2_throw", 1)
  "__reraiseCause" -> Just ("krt2_reraise", 1)
  _ -> Nothing

-- | Lower a saturated exception op to its @krt2_*@ node-builder
-- ('exnNodeBuilder').  Each explicit argument is compiled to an operand
-- (a body/fin to a CK-machine ACTION, a handler to a closure, an err/cause to a
-- value — all via 'compileErasableArg', exactly as the C backend), then the
-- single @call ptr \@krt2_X(...)@ returns the node.  A CURRIED / under- or
-- over-saturated occurrence (rare) is NOT routed here — the caller only reaches
-- 'compilePrimApp' for a SATURATED spine ('saturatedPrim'); a partial one stays
-- a curried @knative@ closure ('compilePrimValue'), where the runtime drives it.
compileExnNode :: Text -> (Text, Int) -> [(Icit, Term)] -> Gen Text
compileExnNode pname (builder, ar) sargs = do
  let explArgs = [a | (Expl, a) <- sargs]
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
compileIoSat :: Text -> Text -> Int -> [(Icit, Term)] -> Gen Text
compileIoSat pname cfn ar sargs = do
  let explArgs = [a | (Expl, a) <- sargs]
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
compilePureDirect :: Text -> Text -> Int -> [(Icit, Term)] -> Gen Text
compilePureDirect pname helper ar sargs = do
  let explArgs = [a | (Expl, a) <- sargs]
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
compilePureWrapper :: Text -> Text -> Int -> [(Icit, Term)] -> Gen Text
compilePureWrapper pname cfn ar sargs = do
  let explArgs = [a | (Expl, a) <- sargs]
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
