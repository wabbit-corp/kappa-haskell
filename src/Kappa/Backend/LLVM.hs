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
-- This module currently implements M0 (hello-world): a Kappa program whose
-- @main@ is a saturated effectful primitive over string literals.  The
-- structural scaffolding (the work queue, the memoised accessor shape, the
-- @\@main@ entry point, the assembled module) mirrors 'Kappa.Backend.C'
-- one-to-one so later milestones (arithmetic, constructors, closures, do)
-- slot in by adding 'compile' arms, not by reworking the frame.
--
-- The single structural difference from C: C nests expressions in one
-- string; LLVM is three-address, so 'compile' returns an SSA OPERAND
-- (a @%reg@, an @\@global@, or @ptr null@) and materialises every
-- sub-result as an instruction first.
module Kappa.Backend.LLVM
  ( generateLL
  ) where

import Data.Char (isAsciiLower, isAsciiUpper, isDigit, ord)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Control.Monad (forM_, unless)
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
  , gsEnv :: !Text -- ^ SSA operand for the current @KEnv*@ (@"ptr null"@ at top level)
  , gsTop :: ![Text] -- ^ completed top-level @define@s, reversed
  , gsDecls :: !(Set Text) -- ^ runtime @declare@ lines (Set-dedup: one fn referenced many times)
  , gsStrs :: ![(Text, Text, Int)] -- ^ string pool: (global name, escaped IR bytes, byte length)
  , gsGlobalsExtra :: ![Text] -- ^ extra module-level globals (e.g. each accessor's @.cache@)
  , gsEmitted :: !(Set GName) -- ^ globals already emitted or enqueued
  , gsQueue :: ![GName] -- ^ globals still to emit
  , gsErrs :: ![BackendError] -- ^ unsupported-construct findings
  , gsCur :: !GName -- ^ definition currently being compiled (for diagnostics)
  , gsGlobals :: !(Map GName GlobalDef)
  , gsBodies :: !(Map GName Term)
  , gsPrims :: !(Set Text) -- ^ primitive names the linked runtime implements
  , gsDeclSites :: !(Map GName Span)
  }

type Gen = State GenState

-- | A fresh SSA register name (@%vN@) — every non-trivial LLVM value must be
-- named; this is the LLVM analogue of C's nested r-values.
freshReg :: Gen Text
freshReg = do
  n <- gets gsFresh
  modify' $ \g -> g {gsFresh = n + 1}
  pure ("%v" <> T.pack (show n))

-- | Prepend an IR instruction to the current basic block.
emit :: Text -> Gen ()
emit s = modify' $ \g -> g {gsInsns = s : gsInsns g}

-- | Add a runtime @declare@ line (idempotent — a Set).
declRuntime :: Text -> Gen ()
declRuntime d = modify' $ \g -> g {gsDecls = Set.insert d (gsDecls g)}

-- | Run a sub-action with a fresh (empty) instruction buffer and the given
-- current-env operand, returning the produced instructions IN ORDER plus the
-- action's result; restores the caller's buffer and env afterwards.  The
-- LLVM analogue of C's 'captured'.
captured :: Text -> Gen a -> Gen ([Text], a)
captured env act = do
  saved <- gets gsInsns
  savedEnv <- gets gsEnv
  modify' $ \g -> g {gsInsns = [], gsEnv = env}
  r <- act
  produced <- gets gsInsns
  modify' $ \g -> g {gsInsns = saved, gsEnv = savedEnv}
  pure (reverse produced, r)

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
          , gsEnv = "ptr null"
          , gsTop = []
          , gsDecls = Set.empty
          , gsStrs = []
          , gsGlobalsExtra = []
          , gsEmitted = Set.singleton mainG
          , gsQueue = [mainG]
          , gsErrs = []
          , gsCur = mainG
          , gsGlobals = csGlobals cs
          , gsBodies = csCoreBodies cs
          , gsPrims = Set.union basePrims ffiPrims
          , gsDeclSites = csDeclSites cs
          }
      final = execState (drainQueue >> emitMain mainG) st0
   in case reverse (gsErrs final) of
        [] -> Right (assembleLL final)
        errs -> Left errs

-- | The base primitives the @kappart@ runtime implements.  M0 only needs to
-- recognise @printlnString@; the full set is owned by 'Kappa.Backend.C'
-- (kept private there), and later milestones can widen this as their prim
-- lowerings land.  A reference to a name outside this set is an honest
-- @E_BACKEND_UNSUPPORTED@.
basePrims :: Set Text
basePrims = Set.fromList ["printlnString", "printString"]

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
        (insns, operand) <- captured "ptr null" (compile tm)
        emitArity0Accessor ident insns operand

-- | The leading-lambda arity of a term and the body beneath those binders
-- (mirrors C's 'funcArity').
funcArity :: Term -> (Int, Term)
funcArity = go 0
  where
    go !n (CLam _ _ _ b) = go (n + 1) b
    go !n t = (n, t)

-- | Emit a memoised arity-0 accessor (the §3.1 IR): a @.cache@ global, a
-- load+null-check fast path, a @build@ block that compiles the term and
-- stores the result, and a @phi@ that returns the cached-or-fresh value.
emitArity0Accessor :: Text -> [Text] -> Text -> Gen ()
emitArity0Accessor ident buildInsns operand = do
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
               , "  %r = phi ptr [ %cached, %entry ], [ " <> operand <> ", %build ]"
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
  (insns, operand) <- captured "ptr null" (unsupported "definition" detail)
  emitArity0Accessor ident insns operand

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

-- ── Term lowering ────────────────────────────────────────────────────

-- | Compile a term: emit any needed instructions into the current basic
-- block and return an SSA OPERAND (@%reg@ / @\@global@ / @ptr null@) for its
-- value.  The three-address discipline is the one structural difference
-- from C's 'compile' (which returns a nested expression string).
--
-- M0 subset: a string literal, a bare global reference, and a saturated
-- application whose head is a known prim or another global.
compile :: Term -> Gen Text
compile term = case term of
  CLit l -> compileLit l
  CGlob g -> compileGlob g
  CApp {} -> compileApp term
  _ ->
    unsupported "term"
      ("the LLVM backend M0 cannot lower this construct: " <> constructName term)

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
  l ->
    unsupported "literal"
      ("the LLVM backend M0 supports only String literals, not " <> litName l)

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
          declRuntime ("declare ptr @" <> ident <> "()") -- forward decl for symmetry
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

-- | Compile an application.  M0: a saturated application whose head is a
-- known IO primitive lowers to @knative_sat@ (the §2.3 lowering); a
-- saturated application whose head is another global is out of M0 scope
-- (no arity-≥1 globals yet) and reported.
compileApp :: Term -> Gen Text
compileApp term = do
  let (hd, sargs) = spineOf term
  case hd of
    CGlob g -> do
      mp <- globPrimName g
      case mp of
        Just pname -> compilePrimApp pname sargs
        Nothing ->
          unsupported "application"
            ("the LLVM backend M0 cannot lower an application of '"
              <> gKey g <> "' (only saturated IO primitives are supported)")
    _ ->
      unsupported "application"
        "the LLVM backend M0 cannot lower this application head"

-- | Lower a saturated application of an IO primitive to @knative_sat@.  For
-- M0 the only prim is @printlnString@ (entry point @kpf_io_printlnString@,
-- arity 1, IO).  Mirrors C's saturated-IO-prim arm (C.hs:2102–2109): build a
-- stack @[N x ptr]@ arg array, store each compiled argument operand, and
-- call @knative_sat(fn, argc, argv, 1)@.
compilePrimApp :: Text -> [(Icit, Term)] -> Gen Text
compilePrimApp pname sargs =
  case ioPrimEntry pname of
    Just (cfn, ar) -> do
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
            ("the LLVM backend M0 supports only a SATURATED application of '"
              <> pname <> "' (got " <> T.pack (show (length explArgs))
              <> " of " <> T.pack (show ar) <> " arguments)")
    Nothing ->
      unsupported "primitive"
        ("the LLVM backend M0 does not implement the primitive '" <> pname
          <> "' (only printlnString/printString in M0); use the C backend")

-- | The (entry point, arity) of the IO primitives M0 lowers.  A small fixed
-- table — the C backend's full 'primEntries' is private to it; later
-- milestones port more entries as their lowerings land.
ioPrimEntry :: Text -> Maybe (Text, Int)
ioPrimEntry = \case
  "printlnString" -> Just ("kpf_io_printlnString", 1)
  "printString" -> Just ("kpf_io_printString", 1)
  _ -> Nothing

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
