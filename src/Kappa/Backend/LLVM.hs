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
import Kappa.Backend.C (BackendError (..))
import Kappa.Backend.NativeFfi (ResolvedNativeSymbol)
import Kappa.Check (CheckState (..))
import Kappa.Core
import Kappa.Eval (GlobalDef (..))
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
  , gsBodies :: !(Map GName Term)
  , gsPrims :: !(Set Text) -- ^ primitive names the linked runtime implements
  , gsDeclSites :: !(Map GName Span)
  , gsCtorTags :: !(Map Text Int) -- ^ Milestone C: USER-constructor gKey -> numeric tag id (@KCT_USER_BASE+i@). Precomputed once ('collectUserCtorTags') so 'compileCtor'/'compileMatch' can emit a literal @i32@ immediate (LLVM has no symbolic enum constant like the C backend's @KT_*@). Builtin ctors are NOT here — they use the fixed 'builtinCtorTagId'.
  , gsBlock :: !Text -- ^ Milestone C: label of the basic block currently being filled. A @phi@ at a control-flow join needs the PREDECESSOR block of each incoming value, which — for a branch that itself emitted control flow (a nested match/if) — is NOT the branch-entry label but whatever block was active when the branch finished. 'compileIf'/'compileMatch' read this after compiling each arm to spell the phi's incoming labels correctly. Updated by 'startBlock'.
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

gKey :: GName -> Text
gKey (GName (ModuleName segs) nm) = T.intercalate "." (segs ++ [nm])

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

-- | The fixed kappart.h @KCT_*@ NUMERIC id for a runtime-built builtin
-- constructor, keyed by gKey, or @Nothing@ for a user constructor.  This pairs
-- 'Kappa.Backend.C.builtinCtorTag' (gKey -> @"KCT_name"@) with the enum's
-- numeric values transcribed from runtime/kappart.h (KCT_OTHER=0, KCT_UNIT=1,
-- then sequential; KCT_USER_BASE=40).  The C backend emits the symbolic @KCT_*@
-- name and lets the C compiler resolve it against the included header; LLVM IR
-- has no symbolic enum constant, so this backend must spell the literal number,
-- and so MUST be kept in sync with the kappart.h enum BY HAND.
builtinCtorTagId :: Text -> Maybe Int
builtinCtorTagId = \case
  "std.prelude.Unit" -> Just 1 -- KCT_UNIT
  "std.prelude.True" -> Just 2 -- KCT_TRUE
  "std.prelude.False" -> Just 3 -- KCT_FALSE
  "std.prelude.::" -> Just 4 -- KCT_CONS
  "std.prelude.Nil" -> Just 5 -- KCT_NIL
  "std.prelude.Some" -> Just 6 -- KCT_SOME
  "std.prelude.None" -> Just 7 -- KCT_NONE
  "__rat" -> Just 8 -- KCT_RAT
  "std.prelude.__EffPure" -> Just 9 -- KCT_EFFPURE
  "std.prelude.__EffOp" -> Just 10 -- KCT_EFFOP
  "std.prelude.Success" -> Just 11 -- KCT_SUCCESS
  "std.prelude.Failure" -> Just 12 -- KCT_FAILURE
  "std.prelude.Fail" -> Just 13 -- KCT_FAIL
  "std.prelude.Interrupt" -> Just 14 -- KCT_INTERRUPT
  "std.prelude.Defect" -> Just 15 -- KCT_DEFECT
  "std.prelude.Both" -> Just 16 -- KCT_BOTH
  "std.prelude.Then" -> Just 17 -- KCT_THEN
  "std.prelude.ROLeft" -> Just 18 -- KCT_RO_LEFT
  "std.prelude.RORight" -> Just 19 -- KCT_RO_RIGHT
  "std.prelude.TOTimedOut" -> Just 20 -- KCT_TO_TIMED_OUT
  "std.prelude.TOExit" -> Just 21 -- KCT_TO_EXIT
  "std.prelude.MkInterruptCause" -> Just 22 -- KCT_MK_INTERRUPT_CAUSE
  "std.prelude.Requested" -> Just 23 -- KCT_IT_REQUESTED
  "std.prelude.ScopeShutdown" -> Just 24 -- KCT_IT_SCOPE_SHUTDOWN
  "std.prelude.TimedOut" -> Just 25 -- KCT_IT_TIMED_OUT
  "std.prelude.RaceLost" -> Just 26 -- KCT_IT_RACE_LOST
  "std.prelude.External" -> Just 27 -- KCT_IT_EXTERNAL
  _ -> Nothing

-- | @KCT_USER_BASE@ from runtime/kappart.h: the first id codegen may assign to
-- a user constructor (the builtin ids above all sit below it).
kctUserBase :: Int
kctUserBase = 40

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

-- | Emit one global's accessor.  M0 supports the arity-0 CAF shape: a
-- memoised @kg_*()@ accessor whose body is the compiled term, cached in a
-- module-level @.cache@ global.  A function global (arity ≥ 1) is out of M0
-- scope and reported.
emitGlobal :: GName -> Gen ()
emitGlobal g = do
  modify' $ \st -> st {gsCur = g}
  bodies <- gets gsBodies
  let ident = cGlobIdent g
  case Map.lookup g bodies of
    Nothing ->
      -- No recorded core body: M0 does not handle type-level erasure; report.
      reportArity0Failure ident
        ("'" <> gKey g <> "' has no recorded core body (M0 supports only "
          <> "arity-0 CAFs over string literals and saturated IO prims)")
    Just tm -> case funcArity tm of
      (n, _) | n >= 1 ->
        reportArity0Failure ident
          ("'" <> gKey g <> "' is a function (arity " <> T.pack (show n)
            <> "); the LLVM backend M0 supports only arity-0 CAFs")
      _ -> do
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
  CLet _ _ _ rhs body -> compileLet rhs body
  CCtor g args -> compileCtor g args
  CIf c t e -> compileIf c t e
  CMatch scrut alts -> compileMatch scrut alts
  _ ->
    unsupported "term"
      ("the LLVM backend M0 cannot lower this construct: " <> constructName term)

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
compileIf c t e = do
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
  tv <- compile t
  thenEnd <- gets gsBlock
  emit ("br label %" <> joinL)
  -- else arm
  startBlock elseL
  ev <- compile e
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
compileMatch scrut alts = do
  sv <- compile scrut
  joinL <- freshLabel "match.join."
  -- Each alt contributes one (operand, predecessor-block) pair to the phi; the
  -- non-exhaustive fallback contributes an (unreachable) @null@ incoming so the
  -- phi is always well-formed even for a match with no value-producing alt.
  incomings <- compileAlts sv joinL alts
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
compileAlts :: Text -> Text -> [CaseAlt] -> Gen [(Text, Text)]
compileAlts sv joinL = go
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
    go (alt : rest) = compileAlt sv joinL alt (go rest)

-- | Lower one alternative.  @onFail@ emits the failure continuation (the next
-- alt, or the non-exhaustive fallback) and returns ITS join incomings; the
-- caller guarantees the block current when @onFail@ runs is open and
-- unterminated.  Structure: an optional pattern-tag test branches to a fresh
-- @fail@ block (where @onFail@ runs) or the @ok@ block; in @ok@ the fields are
-- bound, an optional guard is checked (a failing guard ALSO routes to a fail
-- block running @onFail@), the body is compiled, and control branches to the
-- join.  'gsEnv' is restored after binding so a sibling alt never inherits the
-- binders.  Returns this alt's incomings ++ @onFail@'s.
compileAlt :: Text -> Text -> CaseAlt -> Gen [(Text, Text)] -> Gen [(Text, Text)]
compileAlt sv joinL (CaseAlt pat mguard body) onFail = do
  mtest <- patTestLL sv pat
  case (mtest, mguard) of
    -- Always-matching pattern, no guard: no branch at all — bind and run the
    -- body directly (the C backend's first-match order makes later alts dead).
    (Nothing, Nothing) -> do
      inc <- bindAndBody sv joinL pat body
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
          inc <- bodyToJoin joinL body
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
          inc <- bodyToJoin joinL body
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
bindAndBody :: Text -> Text -> CorePat -> Term -> Gen (Text, Text)
bindAndBody sv joinL pat body = do
  env0 <- gets gsEnv
  env' <- bindPat sv pat
  modify' $ \g -> g {gsEnv = env'}
  inc <- bodyToJoin joinL body
  modify' $ \g -> g {gsEnv = env0}
  pure inc

-- | Compile @body@ in the current (env-extended) block, branch to the join, and
-- report the body's @(operand, predecessor-block)@ for the join phi.  The
-- predecessor is read AFTER compiling the body (a nested match/if leaves a
-- different block active than the body's entry).
bodyToJoin :: Text -> Term -> Gen (Text, Text)
bodyToJoin joinL body = do
  bv <- compile body
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

-- | A bare global reference.  A prelude @prim@ registration / @__prim@ name
-- is a primitive (only meaningful saturated in M0, so a BARE prim is
-- unsupported here); any other global is a CAF: emit a call to its accessor
-- and enqueue it.
compileGlob :: GName -> Gen Text
compileGlob g@(GName m nm)
  | m == primModule = bareUnsupported nm
  | otherwise = do
      globals <- gets gsGlobals
      case Map.lookup g globals of
        Just gd | Just (VPrim pname _) <- gdValue gd -> bareUnsupported pname
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
  where
    bareUnsupported p =
      unsupported "primitive"
        ("the LLVM backend M0 supports a primitive ('" <> p
          <> "') only when fully applied, not as a bare value")

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
        Just pname -> compilePrimApp pname sargs
        Nothing ->
          unsupported "application"
            ("the LLVM backend (Milestone A) cannot lower an application of '"
              <> gKey g <> "' (only saturated IO and pure first-order "
              <> "primitives are supported; general application is Milestone C)")
    _ ->
      unsupported "application"
        "the LLVM backend (Milestone A) cannot lower this application head"

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

-- | The (entry point, arity) of the IO primitives M0 lowers.  A small fixed
-- table — the C backend's full 'primEntries' is private to it; later
-- milestones port more entries as their lowerings land.
ioPrimEntry :: Text -> Maybe (Text, Int)
ioPrimEntry = \case
  "printlnString" -> Just ("kpf_io_printlnString", 1)
  "printString" -> Just ("kpf_io_printString", 1)
  _ -> Nothing

-- | The pure first-order primitives Milestone A lowers, mapping the prim name
-- to its (direct @kp_*@ helper, explicit arity).  A FAITHFUL transliteration of
-- the C backend's 'primDirect' (C.hs:1901–1935) restricted to the prims this
-- milestone needs (arithmetic, integer comparison, and @show@) — every entry
-- here is also a @primDirect@ entry there with the SAME helper symbol and
-- arity, so a saturated call emits the identical runtime call in both backends.
-- (The C backend additionally requires a matching 'primEntries' arity; for
-- these prims the two tables agree, which this table encodes directly.)
--
-- Milestone B widens this from the M1 Integer-only set to every pure-direct
-- @kp_*@ helper whose arguments AND result are restricted to the value types
-- already lowered (Integer, String, Bool): the String ops (@stringAppend@,
-- @eqStr@, @ltStr@, @showStringLit@) and the Integer bitwise ops (@__intAnd@,
-- @__intOr@, @__intXor@).  @eqStr@/@ltStr@ take String args and return a Bool
-- (@kbool@), which is fine even without Bool literals — the Bool is produced
-- by the runtime, not parsed from source.
--
-- Deliberately STILL NOT ported (their literals are not yet lowered, so a
-- caller can never construct an argument): the Double helpers
-- (@addDouble@/…/@showDouble@/@intToDouble@/@floatEq@/@eqDouble@), the Scalar
-- (Char) helpers (@eqScalar@/@ltScalar@/@showScalar@), and the Byte helpers
-- (@eqByte@/@ltByte@).  Every entry here is also a @primDirect@ entry in
-- "Kappa.Backend.C" with the SAME helper symbol and arity, so a saturated call
-- emits the identical runtime call in both backends.
pureDirectEntry :: Text -> Maybe (Text, Int)
pureDirectEntry = \case
  "addInt" -> Just ("kp_addInt", 2)
  "subInt" -> Just ("kp_subInt", 2)
  "mulInt" -> Just ("kp_mulInt", 2)
  "divInt" -> Just ("kp_divInt", 2)
  "modInt" -> Just ("kp_modInt", 2)
  "negInt" -> Just ("kp_negInt", 1)
  "eqInt" -> Just ("kp_eqInt", 2)
  "ltInt" -> Just ("kp_ltInt", 2)
  "leInt" -> Just ("kp_leInt", 2)
  "showInt" -> Just ("kp_showInt", 1)
  -- Milestone B: String ops (args/result are String or Bool).
  "stringAppend" -> Just ("kp_stringAppend", 2)
  "eqStr" -> Just ("kp_eqStr", 2)
  "ltStr" -> Just ("kp_ltStr", 2)
  "showStringLit" -> Just ("kp_showStringLit", 1)
  -- Milestone B: Integer bitwise ops.
  "__intAnd" -> Just ("kp_intAnd", 2)
  "__intOr" -> Just ("kp_intOr", 2)
  "__intXor" -> Just ("kp_intXor", 2)
  _ -> Nothing

-- | The names in 'pureDirectEntry' — the pure prims registered into @gsPrims@
-- ('basePrims') so 'globPrimName' recognises them.
pureDirectPrims :: [Text]
pureDirectPrims =
  [ "addInt", "subInt", "mulInt", "divInt", "modInt", "negInt"
  , "eqInt", "ltInt", "leInt", "showInt"
  , "stringAppend", "eqStr", "ltStr", "showStringLit"
  , "__intAnd", "__intOr", "__intXor"
  ]

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
