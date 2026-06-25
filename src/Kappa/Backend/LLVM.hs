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
  ) where

import Data.Char (isAsciiLower, isAsciiUpper, isDigit, ord)
import Data.List (sort)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Control.Monad (forM_, foldM, unless)
import Control.Monad.State.Strict
import Kappa.Backend.C (BackendError (..), PrimEntry (..), primDirect, primEntries)
import Kappa.Backend.NativeFfi (ResolvedNativeSymbol)
import Kappa.Builtins (builtinCtorTagId, kctUserBase)
import Kappa.Check (CheckState (..))
import Kappa.Core
import Kappa.Eval (GlobalDef (..))
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
  , gsBodies :: !(Map GName Term)
  , gsPrims :: !(Set Text) -- ^ primitive names the linked runtime implements
  , gsDeclSites :: !(Map GName Span)
  , gsCtorTags :: !(Map Text Int) -- ^ Milestone C: USER-constructor gKey -> numeric tag id (@KCT_USER_BASE+i@). Precomputed once ('collectUserCtorTags') so 'compileCtor'/'compileMatch' can emit a literal @i32@ immediate (LLVM has no symbolic enum constant like the C backend's @KT_*@). Builtin ctors are NOT here — they use the fixed 'builtinCtorTagId'.
  , gsBlock :: !Text -- ^ Milestone C: label of the basic block currently being filled. A @phi@ at a control-flow join needs the PREDECESSOR block of each incoming value, which — for a branch that itself emitted control flow (a nested match/if) — is NOT the branch-entry label but whatever block was active when the branch finished. 'compileIf'/'compileMatch' read this after compiling each arm to spell the phi's incoming labels correctly. Updated by 'startBlock'.
  , gsCtorSet :: !(Set GName) -- ^ Milestone D: every declared constructor's gname. An IMPLICIT application whose head is a constructor erases its implicit arg (§31.2); 'isErasedHead' consults this (mirrors C's 'gsCtors' membership test).
  , gsDataSet :: !(Set GName) -- ^ Milestone D: declared data-type / trait gnames — a reference to one in argument position is computationally erased ('isTypeGlob'); mirrors C's @gsDatas@ ∪ @gsTraits@.
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
--     'collectUserCtorTags' deterministically (sorted by gKey).  These never
--     cross a backend boundary, so they need only be self-consistent
--     (construct id == match id); the sorted assignment additionally makes them
--     match the C backend's @KT_*@ enum for debuggability.

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
collectUserCtorTags :: Map GName Term -> Map Text Int
collectUserCtorTags bodies =
  let keys = sort (Set.toList (foldMap userCtorKeys (Map.elems bodies)))
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
-- from the map would be an internal bug ('collectUserCtorTags' walks all bodies
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
generateLL cs mainG ffiPrims _hostSyms =
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
          , gsBodies = csCoreBodies cs
          , gsPrims = Set.union basePrims ffiPrims
          , gsDeclSites = csDeclSites cs
          , gsCtorTags = collectUserCtorTags (csCoreBodies cs)
          , gsBlock = "build"
          , gsCtorSet = Map.keysSet (csCtors cs)
          , gsDataSet = Set.union (Map.keysSet (csDatas cs)) (Map.keysSet (csTraits cs))
          }
      final = execState (drainQueue >> emitMain mainG) st0
   in case reverse (gsErrs final) of
        [] -> Right (assembleLL final)
        errs -> Left errs

-- | The base primitives the @kappart@ runtime implements.  M0 recognised only
-- @printlnString@/@printString@; M1 widens this to the saturated pure
-- first-order prims it lowers (the @kp_*@ direct helpers below).  The full set
-- is owned by 'Kappa.Backend.C' (kept private there); later milestones widen
-- this further as their lowerings land.  A reference to a name outside this set
-- is an honest @E_BACKEND_UNSUPPORTED@.
--
-- INVARIANT: every name here that is not an IO prim ('ioPrimEntry') must have a
-- 'pureDirectEntry' lowering, and vice versa — 'globPrimName' returns a name
-- only when it is in @gsPrims@, and 'compilePrimApp' must then handle it.
basePrims :: Set Text
basePrims =
  Set.fromList $
    ["printlnString", "printString"] -- M0 IO prims
      ++ ["ioPure", "ioBind", "ioThen"] -- Milestone E do-kernel monadic prims
      ++ pureDirectPrims -- M1 pure first-order prims

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
    Nothing ->
      -- No recorded core body: a purely type-level global with no runtime value.
      reportArity0Failure ident
        ("'" <> gKey g <> "' has no recorded core body (the LLVM backend lowers "
          <> "only globals with a runtime value)")
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
  CCtor g args -> compileCtor g args
  CIf c t e -> compileIf c t e
  CMatch scrut alts -> compileMatch scrut alts
  CDo lbl items -> compileDo lbl items
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
  -- Every other form is a value (or a non-bouncing construct): compile it
  -- normally and return it.  A CLam here is a closure value, NOT a bounce.
  _ -> compile term

-- | Is @pname@ a SATURATED-prim application in @term@ (so it returns a value
-- and never bounces)?  Mirrors the C backend's saturated-prim fast-path gate
-- ('compilePrimApp' accepts only the exact arity): the explicit-argument count
-- equals the prim's known arity.  An under-/over-saturated prim spine is a
-- curried closure that goes through the @kapp@ chain (and may bounce) instead.
saturatedPrim :: Text -> Term -> Bool
saturatedPrim pname term =
  let (_, sargs) = spineOf term
      nexpl = length [() | (Expl, _) <- sargs]
   in case (ioPrimEntry pname, pureDirectEntry pname) of
        (Just (_, ar), _) -> nexpl == ar
        (_, Just (_, ar)) -> nexpl == ar
        _ -> False

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
  let def =
        T.unlines $
          [ "define internal ptr @" <> fnIdent <> "(ptr %cenv, ptr %arg) {"
          , "entry:"
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

-- ── Pattern matching (Milestone C) ───────────────────────────────────

-- | A @match@ expression (mirrors C's 'consumeMatch' / 'consumeAlt' chain,
-- specialised to expression position).  The scrutinee is compiled once; each
-- alternative is an @icmp eq i32 <tagid>@ test that branches into a per-alt
-- block which binds the constructor's fields ('kpush' onto 'gsEnv', in pattern
-- order) and compiles the body.  Every alt block branches to a shared join
-- whose @phi ptr@ selects the matched alt's operand.  A fall-through past the
-- last alt calls @krt_fail("non-exhaustive match")@ (mirroring the C backend's
-- @if (!matched) krt_fail(...)@), in an UNREACHABLE-then-branch block that still
-- feeds the join (with a @null@ placeholder) so the phi is well-formed.
--
-- SUPPORTED pattern forms (the subset the C backend's CMatch produces that this
-- milestone lowers): a constructor pattern with var/wildcard field binders
-- ('CPCtor' over 'CPVar'/'CPWild'), a bare var/wildcard catch-all
-- ('CPVar'/'CPWild'), and an as-pattern over those ('CPAs').  Guards are
-- supported (an extra @kas_bool@ test inside the alt).  Literal patterns, tuple/
-- record/variant/or/nested-constructor patterns are left UNSUPPORTED here (a
-- clean 'unsupported' rather than a miscompile) — single-level constructor
-- dispatch is what the data-type corpus needs and what elaboration desugars to.
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
  -- Each alt contributes one (operand, predecessor-block) pair to the phi; the
  -- non-exhaustive fallback contributes an (unreachable) @null@ incoming so the
  -- phi is always well-formed even for a match with no value-producing alt.
  incomings <- compileAlts compileBody sv joinL alts
  startBlock joinL
  r <- freshReg
  let phiArgs = T.intercalate ", " ["[ " <> op <> ", %" <> blk <> " ]" | (op, blk) <- incomings]
  emit (r <> " = phi ptr " <> phiArgs)
  pure r

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
  mtest <- patTestLL sv pat
  case (mtest, mguard) of
    -- Always-matching pattern, no guard: no branch at all — bind and run the
    -- body directly (the C backend's first-match order makes later alts dead).
    (Nothing, Nothing) -> do
      inc <- bindAndBody compileBody sv joinL pat body
      pure [inc]
    -- Otherwise at least one failable test exists; give the failure path a
    -- block so 'onFail' has somewhere to emit.
    _ -> do
      okL <- freshLabel "alt.ok."
      failL <- freshLabel "alt.fail."
      case mtest of
        Just test -> emit ("br i1 " <> test <> ", label %" <> okL <> ", label %" <> failL)
        Nothing -> emit ("br label %" <> okL) -- guarded var/wildcard: guard decides
      -- success: bind, (guard), body
      startBlock okL
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

-- | A boolean ('i1') test that is true iff @pat@ matches scrutinee operand @v@,
-- or 'Nothing' if the pattern always matches (var/wildcard).  Mirrors the C
-- backend's 'patTest' for the Milestone-C subset (single-level constructor
-- dispatch via @kctor_tagid@); other pattern forms are reported unsupported.
patTestLL :: Text -> CorePat -> Gen (Maybe Text)
patTestLL v = \case
  CPWild -> pure Nothing
  CPVar _ -> pure Nothing
  CPAs _ p -> patTestLL v p
  CPCtor g ps
    | all isVarLike ps -> do
        tag <- ctorTagId g
        declRuntime "declare i32 @kctor_tagid(ptr)"
        ti <- freshReg
        emit (ti <> " = call i32 @kctor_tagid(ptr " <> v <> ")")
        cond <- freshReg
        emit (cond <> " = icmp eq i32 " <> ti <> ", " <> T.pack (show tag))
        pure (Just cond)
    | otherwise -> do
        _ <- unsupported "pattern"
          "the LLVM backend (Milestone C) supports constructor patterns whose fields are only variable/wildcard binders (nested constructor/literal sub-patterns are not yet lowered)"
        falseCond
  CPLit _ -> do
    _ <- unsupported "pattern"
      "the LLVM backend (Milestone C) does not yet lower literal patterns (use the C backend)"
    falseCond
  CPTuple _ -> reportUnsupportedPat "tuple"
  CPRecord _ _ -> reportUnsupportedPat "record"
  CPInject _ _ -> reportUnsupportedPat "variant"
  CPInjectRest _ -> reportUnsupportedPat "residual-row variant"
  CPOr _ _ -> reportUnsupportedPat "or"
  where
    falseCond = do
      r <- freshReg
      emit (r <> " = icmp eq i32 0, 1") -- a constant-false i1
      pure (Just r)
    reportUnsupportedPat what = do
      _ <- unsupported "pattern"
        ("the LLVM backend (Milestone C) does not yet lower " <> what <> " patterns (use the C backend)")
      falseCond

-- | A pattern whose fields 'patTestLL' / 'bindPat' handle as a single-level
-- binder: a variable, a wildcard, or an as-pattern over one of those.
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

-- | The field operands a pattern binds, as compiled SSA operands, in matchPat's
-- left-to-right binding order (mirrors C's 'patBindings' for the subset).  A
-- constructor field is projected with @kctor_arg(v, kctor_argc(v) - nps + i)@,
-- exactly as the C backend computes it ('ctorArgExpr').
patBindingsLL :: Text -> CorePat -> Gen [Text]
patBindingsLL = go
  where
    go v = \case
      CPWild -> pure []
      CPVar _ -> pure [v]
      CPAs _ p -> do rest <- go v p; pure (v : rest)
      CPCtor _ ps -> do
        let nps = length ps
        concat <$> mapM (\(i, p) -> ctorArg v nps i >>= \av -> go av p) (zip [0 ..] ps)
      _ -> pure [] -- other forms are rejected in 'patTestLL' before binding
    -- @kctor_arg(v, kctor_argc(v) - nps + i)@ as SSA: read the field count,
    -- compute the absolute index, then the field.  Matches 'ctorArgExpr'.
    ctorArg v nps i = do
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

-- | The first do-item outside the Milestone-E linear subset, if any — used to
-- fail the WHOLE block closed (a clean unsupported) before emitting a partial
-- tree, so a deferred construct can never be silently dropped.
firstUnsupportedItem :: [KItem] -> Maybe KItem
firstUnsupportedItem = go
  where
    go [] = Nothing
    go (it : rest) = case it of
      KBind {} -> go rest
      KExpr {} -> go rest
      KLet {} -> go rest
      _ -> Just it

-- | Report a do-item that is outside Milestone E (the loop family, mutable
-- cells, abrupt control, defer, using, sub-do, let?) as unsupported.
unsupportedDoItem :: KItem -> Gen Text
unsupportedDoItem it =
  unsupported "do-kernel"
    ( "the LLVM backend (Milestone E) lowers only the linear bind/let/action "
        <> "do-kernel subset; this item is a later milestone: "
        <> doItemKind it
    )

-- | A short label for an unsupported do-item, for the diagnostic.
doItemKind :: KItem -> Text
doItemKind = \case
  KLetQ {} -> "let? (fallible binding)"
  KVarItem {} -> "var (mutable cell)"
  KAssign {} -> "assignment"
  KReturn {} -> "return"
  KBreak {} -> "break"
  KContinue {} -> "continue"
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
  [KExpr t] -> compile t
  [KBind _ _ t] -> compile t
  -- FINAL let: a pure binding with no following action is degenerate (the block
  -- must end in an action), but lower it as @pure(value)@ for totality.
  [KLet _ pat t] -> do
    te <- compile t
    declRuntime "declare ptr @krt2_pure(ptr)"
    -- bind the value (so a constructor pattern is still well-typed) then pure it
    _ <- bindPatDo te pat
    r <- freshReg
    emit (r <> " = call ptr @krt2_pure(ptr " <> te <> ")")
    pure r
  -- A plain ACTION with a following rest: treat as `_ <- action; rest` so REST
  -- stays LAZY inside the continuation closure (NOT krt2_then with an eager rest
  -- operand — that would eagerly build the tail and overflow on IO recursion).
  (KExpr t : rest) -> bindThen t CPWild rest
  -- A monadic bind: `x <- action; rest`.
  (KBind _ pat t : rest) -> bindThen t pat rest
  -- A pure LET binding: compile e, kpush, compile REST under the extended env
  -- (restored after).  No krt2 node — the runtime never sees this binding.
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
  (it : _) -> unsupportedDoItem it

-- | Lower `pat <- action; rest` (or `action; rest` with @pat = CPWild@) as
-- @krt2_bind(action, kclo(@kdo_N, env))@, where @kdo_N@ is a lifted continuation
-- closure that receives the delivered value, binds it to @pat@, and compiles
-- REST as an action tree.  The rest lives INSIDE @kdo_N@ — that laziness is what
-- keeps an IO-recursive do-block stack-safe (the tree is built one bind at a
-- time as the CK-machine runs it, not all at once at build time).
bindThen :: Term -> CorePat -> [KItem] -> Gen Text
bindThen action pat rest = do
  m <- compile action
  contFn <- emitDoCont pat rest
  capturedEnv <- gets gsEnv
  declRuntime "declare ptr @kclo(ptr, ptr)"
  declRuntime "declare ptr @krt2_bind(ptr, ptr)"
  k <- freshReg
  emit (k <> " = call ptr @kclo(ptr @" <> contFn <> ", ptr " <> capturedEnv <> ")")
  r <- freshReg
  emit (r <> " = call ptr @krt2_bind(ptr " <> m <> ", ptr " <> k <> ")")
  pure r

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
          , "entry:"
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
  l ->
    unsupported "literal"
      ("the LLVM backend M1 supports String and Int literals, not " <> litName l)

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

litName :: Literal -> Text
litName = \case
  LitInt {} -> "Int"
  LitDouble {} -> "Double"
  LitStr {} -> "String"
  LitScalar {} -> "Char"
  LitByte {} -> "Byte"
  LitBytes {} -> "Bytes"
  LitGrapheme {} -> "Grapheme"

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
      case Map.lookup g globals of
        Just gd | Just (VPrim pname _) <- gdValue gd -> compilePrimValue pname
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
      mp <- globPrimName g
      case mp of
        -- A prim spine: take the saturated direct fast path ('compilePrimApp')
        -- when the explicit-argument count matches the prim's arity; otherwise
        -- (partial / over-application) fall through to the general @kapp@ chain,
        -- where the bare prim is a curried native closure ('compilePrimValue').
        Just pname | saturatedPrim pname term -> compilePrimApp pname sargs
        _ -> compileAppDefault term
    _ -> compileAppDefault term

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
-- position is computationally erased): a declared data type or trait.
isTypeGlob :: GName -> Gen Bool
isTypeGlob g = do
  datas <- gets gsDataSet
  pure (g `Set.member` datas)

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

-- | Lower a saturated application of a known primitive.  IO prims take the M0
-- @knative_sat@ path; PURE first-order prims take the M1 direct @kp_*@ helper
-- path ('compilePureDirect').  This mirrors the C backend's dispatch in
-- 'compileAppGlob' (C.hs:2102–2116): @isio@ ⇒ @knative_sat@, else the QW1
-- positional @primDirect@ call.  Under-/over-saturation, or an unknown prim,
-- is reported as unsupported.
compilePrimApp :: Text -> [(Icit, Term)] -> Gen Text
compilePrimApp pname sargs =
  case ioPrimEntry pname of
    Just (cfn, ar) -> compileIoSat pname cfn ar sargs
    Nothing ->
      case pureDirectEntry pname of
        Just (helper, ar) -> compilePureDirect pname helper ar sargs
        Nothing ->
          unsupported "primitive"
            ("the LLVM backend (Milestone A) does not implement the primitive '"
              <> pname <> "'; use the C backend")

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

-- ── LLVM primitive coverage (the only LLVM-local prim data) ──────────
--
-- The cfn/arity/isIO of every prim, and the @kp_*@ direct-helper subset, are
-- single-sourced in "Kappa.Backend.C" ('primEntries' / 'primDirect'). What is
-- LLVM-specific is only WHICH prims this backend has lowered so far — the two
-- coverage sets below. Every prim lowering ('ioPrimEntry'/'pureDirectEntry'/
-- 'primNativeEntry'/'pureDirectPrims') is a DERIVATION over the shared C tables
-- intersected with these sets, so a lowering can never disagree with the C
-- backend on a prim's entry point, arity, or IO-ness — the two backends emit
-- the identical runtime call for any prim both cover.

-- | The IO prims the LLVM backend has lowered (M0 print + Milestone-E do-kernel
-- monadic prims). Their (entry point, arity, isIO=True) come from 'primEntries'.
llvmIoSet :: Set Text
llvmIoSet =
  Set.fromList
    [ "printlnString", "printString" -- M0 IO prims
    , "ioPure", "ioBind", "ioThen" -- Milestone E do-kernel monadic prims
    ]

-- | The pure first-order prims the LLVM backend has lowered: Milestone A's
-- Integer arithmetic/comparison/@show@, widened in Milestone B to the String
-- ops and Integer bitwise ops. Each has a @kp_*@ direct helper in 'primDirect'
-- and a @kpf_*@ wrapper in 'primEntries'. Deliberately NOT yet covered (their
-- literals are not lowered, so no caller can build an argument): the Double,
-- Scalar (Char), and Byte helpers.
llvmPureSet :: Set Text
llvmPureSet =
  Set.fromList
    [ "addInt", "subInt", "mulInt", "divInt", "modInt", "negInt"
    , "eqInt", "ltInt", "leInt", "showInt"
    , "stringAppend", "eqStr", "ltStr", "showStringLit"
    , "__intAnd", "__intOr", "__intXor"
    ]

-- | The (entry point, arity) of an IO primitive the LLVM backend lowers,
-- derived from the shared 'primEntries' restricted to 'llvmIoSet'. A SATURATED
-- @ioPure@/@ioBind@/@ioThen@ lowers to @knative_sat(kpf_io_*, …, isio=1)@ — the
-- SAME lowering the C backend gives these names.
ioPrimEntry :: Text -> Maybe (Text, Int)
ioPrimEntry name = do
  PrimEntry cfn arity isIO <- Map.lookup name primEntries
  if isIO && name `Set.member` llvmIoSet then Just (cfn, arity) else Nothing

-- | The (direct @kp_*@ helper, arity) of a pure first-order primitive the LLVM
-- backend lowers, derived from the shared 'primDirect' restricted to
-- 'llvmPureSet'. A saturated call emits the identical runtime call in both
-- backends (e.g. @kp_addInt(a,b)@).
pureDirectEntry :: Text -> Maybe (Text, Int)
pureDirectEntry name =
  if name `Set.member` llvmPureSet then primDirect name else Nothing

-- | The names in 'pureDirectEntry' — the pure prims registered into @gsPrims@
-- ('basePrims') so 'globPrimName' recognises them.
pureDirectPrims :: [Text]
pureDirectPrims = Set.toList llvmPureSet

-- | The CURRIED native-closure form of a prim — its @kpf_*@ wrapper entry
-- point, arity, and IO-ness — for the prim set this backend lowers. Used when
-- a prim appears as a VALUE (a bare reference, or a partial/over-saturated
-- application): the prim is built as @knative(\@kpf_*, arity, name, isio)@, the
-- same curried closure the C backend's 'emitPrim' builds. Derived from the
-- shared 'primEntries' restricted to the LLVM coverage sets, so the wrapper
-- symbol/arity/isIO always agree with the C backend.
--
-- NOTE the @kpf_*@ wrapper is DISTINCT from the @kp_*@ direct helper
-- ('pureDirectEntry'): @kp_addInt(a,b)@ is the saturated fast call, whereas
-- @kpf_addInt@ is the @KValue**@-taking wrapper that @knative@ drives one
-- curried argument at a time.
primNativeEntry :: Text -> Maybe (Text, Int, Bool)
primNativeEntry name = do
  PrimEntry cfn arity isIO <- Map.lookup name primEntries
  if name `Set.member` llvmIoSet || name `Set.member` llvmPureSet
    then Just (cfn, arity, isIO)
    else Nothing

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
