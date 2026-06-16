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
  , backendDiagnostics
  , basePrims
  ) where

import Data.Char (isAscii, isAsciiLower, isAsciiUpper, isDigit, ord)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Control.Monad.State.Strict
import Kappa.Check (CheckState (..), CtorInfo (..))
import Kappa.Core
import Kappa.Diagnostic
import Kappa.Eval (GlobalDef (..))
import Kappa.Source (ModuleName (..), Span, noSpan)
import Numeric (showHex)

-- | One reason the native backend cannot compile a definition: the global
-- it occurred in, the unsupported construct, and a human detail.
data BackendError = BackendError
  { beGlobal :: !GName
  , beSpan :: !Span
  , beConstruct :: !Text
  , beDetail :: !Text
  }
  deriving stock (Eq, Show)

-- | Render backend errors as structured diagnostics (§3.1): one
-- @E_BACKEND_UNSUPPORTED@ per unsupported construct, citing the offending
-- definition's declaration site.
backendDiagnostics :: [BackendError] -> Diagnostics
backendDiagnostics = map one
  where
    one be =
      diag SevError StageElaborate "E_BACKEND_UNSUPPORTED" (Just "kappa-hs.backend.unsupported")
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
  , gsTop :: ![Text] -- ^ completed top-level C functions, reversed
  , gsProtos :: ![Text] -- ^ forward declarations, reversed
  , gsEmitted :: !(Set GName) -- ^ globals already emitted or enqueued
  , gsQueue :: ![GName] -- ^ globals still to emit
  , gsErrs :: ![BackendError] -- ^ unsupported-construct findings
  , gsCur :: !GName -- ^ definition currently being compiled (for diagnostics)
  , gsGlobals :: !(Map GName GlobalDef)
  , gsBodies :: !(Map GName Term)
  , gsCtors :: !(Map GName CtorInfo)
  , gsDatas :: !(Set GName)
  , gsTraits :: !(Set GName)
  , gsDeclSites :: !(Map GName Span)
  , gsPrims :: !(Set Text) -- ^ primitive names the linked runtime implements
  , gsLoops :: ![Text] -- ^ break-flag C variable of each enclosing loop
  }

type Gen = State GenState

freshN :: Text -> Gen Text
freshN base = do
  n <- gets gsFresh
  modify' $ \g -> g {gsFresh = n + 1}
  pure (base <> T.pack (show n))

emit :: Text -> Gen ()
emit s = modify' $ \g -> g {gsStmts = s : gsStmts g}

-- | Run an action with a fresh (empty) statement buffer and the given
-- current-env expression, returning the produced statements in order plus
-- the action's result; restores the caller's buffer and env afterwards.
captured :: Text -> Gen a -> Gen ([Text], a)
captured env act = do
  saved <- gets gsStmts
  savedEnv <- gets gsEnv
  modify' $ \g -> g {gsStmts = [], gsEnv = env}
  r <- act
  produced <- gets gsStmts
  modify' $ \g -> g {gsStmts = saved, gsEnv = savedEnv}
  pure (reverse produced, r)

-- | Record an unsupported-construct finding and return a placeholder C
-- expression so error collection can continue.
unsupported :: Text -> Text -> Gen Text
unsupported construct detail = do
  g <- gets gsCur
  sites <- gets gsDeclSites
  let sp = Map.findWithDefault noSpan g sites
  modify' $ \st -> st {gsErrs = BackendError g sp construct detail : gsErrs st}
  pure "kunit()"

-- | Enqueue a global for emission (idempotent).
enqueue :: GName -> Gen ()
enqueue g = do
  seen <- gets gsEmitted
  unless (g `Set.member` seen) $
    modify' $ \st -> st {gsEmitted = Set.insert g (gsEmitted st), gsQueue = g : gsQueue st}

-- ── Names ────────────────────────────────────────────────────────────

-- | Canonical dotted key of a global (used for constructor tag-name
-- comparison and the runtime's well-known constructor spellings).
gKey :: GName -> Text
gKey (GName (ModuleName segs) nm) = T.intercalate "." (segs ++ [nm])

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
        -- emit non-ASCII / control bytes via their UTF-8 octets as \xNN
        | otherwise -> T.concat [octet b | b <- utf8Bytes c]
    octet b = "\\x" <> pad (T.pack (showHex b ""))
    pad s = if T.length s == 1 then "0" <> s else s

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
-- (kappart.c).  Kept in lock-step with that file: emitting a primitive
-- outside this set (plus any FFI extension) is a compile-time
-- 'E_BACKEND_UNSUPPORTED'.
basePrims :: Set Text
basePrims =
  Set.fromList
    [ -- integer
      "addInt", "subInt", "mulInt", "divInt", "modInt", "negInt"
    , "eqInt", "ltInt", "leInt"
      -- double
    , "addDouble", "subDouble", "mulDouble", "divDouble", "negDouble"
    , "eqDouble", "ltDouble", "floatEq"
      -- string / scalar
    , "stringAppend", "eqStr", "ltStr", "eqScalar", "ltScalar", "showInt"
      -- IO
    , "printString", "printlnString", "ioPure", "ioBind", "ioThen"
    , "newRef", "readRef", "writeRef"
    ]

-- | Compile the reachable closure of @main@ to a C translation unit.
-- @ffiPrims@ are the additional primitive names the linked FFI runtime
-- implements (empty for the no-FFI build).  Returns @Left errs@ when any
-- reachable definition uses an unsupported construct (the caller renders
-- these as 'E_BACKEND_UNSUPPORTED'), or @Right csource@ on success.
generateC :: CheckState -> GName -> Set Text -> Either [BackendError] Text
generateC cs mainG ffiPrims =
  let st0 =
        GenState
          { gsFresh = 0
          , gsStmts = []
          , gsEnv = "0"
          , gsTop = []
          , gsProtos = []
          , gsEmitted = Set.singleton mainG
          , gsQueue = [mainG]
          , gsErrs = []
          , gsCur = mainG
          , gsGlobals = csGlobals cs
          , gsBodies = csCoreBodies cs
          , gsCtors = csCtors cs
          , gsDatas = Map.keysSet (csDatas cs)
          , gsTraits = Map.keysSet (csTraits cs)
          , gsDeclSites = csDeclSites cs
          , gsPrims = Set.union basePrims ffiPrims
          , gsLoops = []
          }
      final = execState (drainQueue >> emitMain mainG) st0
   in case reverse (gsErrs final) of
        [] -> Right (assemble final)
        errs -> Left errs

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
  -- A reachable global with no recorded core body (a built-in primitive,
  -- trait dictionary, or derived projection) is honestly unsupported for
  -- now rather than silently approximated by re-quoting its NbE value.
  case Map.lookup g bodies of
    Nothing -> do
      _ <- unsupported "no-core-body"
        ("its body is not available to the native backend (built-in primitive, \
         \trait dictionary, or derived projection)")
      (stmts, _) <- captured "0" (pure ())
      finishGlobal ident stmts "kunit()"
    Just tm -> do
      (stmts, e) <- captured "0" (compile tm)
      finishGlobal ident stmts e

finishGlobal :: Text -> [Text] -> Text -> Gen ()
finishGlobal ident stmts e =
  let fn =
        T.unlines $
          [ "static KValue *" <> ident <> "(void) {"
          , "  static KValue *cache = 0; if (cache) return cache;"
          , "  KEnv *env = 0; (void)env;"
          ]
            ++ map ("  " <>) stmts
            ++ [ "  cache = " <> e <> ";"
               , "  return cache;"
               , "}"
               ]
   in modify' $ \st -> st {gsTop = fn : gsTop st}

-- | The C @main@: initialise the GC and run @main@'s IO action.
emitMain :: GName -> Gen ()
emitMain g =
  let ident = cGlobIdent g
      fn =
        T.unlines
          [ "int main(void) {"
          , "  krt_init();"
          , "  krun_io(" <> ident <> "());"
          , "  return 0;" -- stdio buffers are flushed by the C runtime at exit
          , "}"
          ]
   in modify' $ \st -> st {gsTop = fn : gsTop st}

assemble :: GenState -> Text
assemble st =
  T.unlines $
    [ "/* Generated by the Kappa native backend (Kappa.Backend.C). */"
    , "#include \"kappart.h\""
    , ""
    ]
      ++ reverse (gsProtos st)
      ++ [""]
      ++ reverse (gsTop st)

-- ── Term lowering ────────────────────────────────────────────────────

-- | Compile a term: emit any needed statements into the current buffer and
-- return a C expression (of type @KValue *@) for its value.
compile :: Term -> Gen Text
compile term
  -- §18.3 monadic splice: `__runIO e` runs the embedded IO action inline
  -- and yields its result as an ordinary value (matches runSplices).
  | Just action <- runIOSplice term = do
      ae <- compile action
      pure ("krun_io(" <> ae <> ")")
compile term = case term of
  CVar i -> do
    env <- gets gsEnv
    pure ("kvar(" <> env <> ", " <> T.pack (show i) <> ")")
  CGlob g -> compileGlob g
  CLit l -> compileLit l
  CApp Expl f a -> do
    fe <- compile f
    ae <- compile a
    pure ("kapp(" <> fe <> ", " <> ae <> ")")
  CApp Impl f a -> do
    erased <- isErasedHead f
    if erased
      then compile f -- implicit arg to a prim/constructor: erased (§31.2)
      else do
        fe <- compile f
        typeArg <- isErasableArg a
        ae <- if typeArg then pure "kunit()" else compile a
        pure ("kappi(" <> fe <> ", " <> ae <> ")")
  CLam _ _ _ body -> compileLam body
  CCtor g args -> compileCtor g args
  CIf c t e -> compileIf c t e
  CMatch scrut alts -> compileMatch scrut alts
  CLet _ _ _ rhs body -> compileLet rhs body
  CLetRec _ _ _ rhs body -> compileLetRec rhs body
  CRecordV fs -> compileRecord fs
  CProj e f -> do
    ee <- compile e
    pure ("kproj(" <> ee <> ", " <> cStr f <> ")")
  CDo items -> compileDo items
  -- type-level forms have no runtime value; reaching one in value position
  -- means the supported subset was exceeded.
  CSort _ -> unsupported "CSort" "a sort (Type) appears in value position"
  CPi {} -> unsupported "CPi" "a function type appears in value position"
  CRecordT _ -> unsupported "CRecordT" "a record type appears in value position"
  CVariantT _ -> unsupported "CVariantT" "a variant type appears in value position"
  CInject {} -> unsupported "CInject" "variant injection is not supported by the native backend"
  CMeta _ -> unsupported "CMeta" "an unsolved metavariable reached code generation"
  CSealE {} -> unsupported "CSealE" "sealed packages are not supported by the native backend"
  CSigT {} -> unsupported "CSigT" "signature types are not supported by the native backend"
  CThunkE _ -> unsupported "CThunkE" "thunk suspensions are not supported by the native backend"
  CLazyE _ -> unsupported "CLazyE" "memoised suspensions are not supported by the native backend"
  CForceE _ -> unsupported "CForceE" "force is not supported by the native backend"
  CQuote {} -> unsupported "CQuote" "syntax quotations are not supported by the native backend"

-- | Head global of an application spine, if any.
headGlob :: Term -> Maybe GName
headGlob = \case
  CApp _ f _ -> headGlob f
  CGlob g -> Just g
  CCtor g _ -> Just g
  _ -> Nothing

-- | An application spine: head term plus its arguments with icities.
spineOf :: Term -> (Term, [(Icit, Term)])
spineOf = go []
  where
    go acc (CApp ic f a) = go ((ic, a) : acc) f
    go acc t = (t, acc)

-- | Recognise a @__runIO e@ monadic-splice application (§18.3); returns
-- the single explicit IO-action argument.  Implicit type arguments are
-- ignored (erased).
runIOSplice :: Term -> Maybe Term
runIOSplice t = case spineOf t of
  (hd, args)
    | Just g <- headOf hd
    , gnameText g == "__runIO"
    , [a] <- [x | (Expl, x) <- args] ->
        Just a
  _ -> Nothing
  where
    headOf (CGlob g) = Just g
    headOf _ = Nothing

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
  CMeta _ -> pure True
  CApp _ f _ -> isErasableArg f -- the spine head decides (e.g. @(List a))
  CGlob g -> isTypeGlob g
  _ -> pure False

-- | A global that denotes a type or trait (so a reference to it in
-- argument position is computationally erased): a declared data type or
-- trait, or a global whose kind is a sort (e.g. the builtin @Integer@).
isTypeGlob :: GName -> Gen Bool
isTypeGlob g = do
  datas <- gets gsDatas
  traits <- gets gsTraits
  globals <- gets gsGlobals
  let sortish = case Map.lookup g globals of
        Just gd -> isSortValue (gdType gd)
        Nothing -> False
  pure (g `Set.member` datas || g `Set.member` traits || sortish)

isSortValue :: Value -> Bool
isSortValue (VSort _) = True
isSortValue _ = False

-- | Emit a reference to a runtime primitive, after confirming the linked
-- runtime implements it; an unimplemented primitive is a compile-time
-- 'E_BACKEND_UNSUPPORTED' (never a silent runtime failure).
emitPrim :: Text -> Gen Text
emitPrim name = do
  prims <- gets gsPrims
  if name `Set.member` prims
    then pure ("kprim(" <> cStr name <> ")")
    else unsupported "primitive"
      ("the primitive '" <> name <> "' is not implemented by the native runtime")

compileGlob :: GName -> Gen Text
compileGlob g@(GName m nm)
  | m == primModule = emitPrim nm
  | otherwise = do
      globals <- gets gsGlobals
      ctors <- gets gsCtors
      case Map.lookup g globals of
        -- A prelude `prim` registration: its value is a bare VPrim, so it
        -- maps directly to the runtime primitive of the same name.
        Just gd | Just (VPrim pname _) <- gdValue gd ->
          emitPrim pname
        _ -> case Map.lookup g ctors of
          Just ci ->
            -- A constructor used as a value: nullary builds directly;
            -- positive-arity bare references are not yet supported (they
            -- need eta-expansion into a curried builder).
            if null (ciFields ci)
              then pure ("kctor0(" <> cStr (gKey g) <> ")")
              else unsupported "bare-ctor"
                ("the constructor '" <> nm <> "' is used as a value (not fully applied)")
          Nothing -> do
            enqueue g
            pure (cGlobIdent g <> "()")

compileLit :: Literal -> Gen Text
compileLit = \case
  LitInt n
    | n >= toInteger (minBound :: Int) && n <= toInteger (maxBound :: Int) ->
        pure ("kint(" <> intLit n <> ")")
    | otherwise ->
        unsupported "LitInt-range"
          ("the integer literal " <> T.pack (show n)
             <> " does not fit in the native backend's 64-bit Int")
  LitDouble d -> pure ("kdbl(" <> T.pack (show d) <> ")")
  LitStr s -> pure ("kstr0(" <> cStr s <> ")")
  LitScalar c -> pure ("kchr(" <> T.pack (show (ord c)) <> ")")
  LitByte _ -> unsupported "LitByte" "byte literals are not supported by the native backend"
  LitBytes _ -> unsupported "LitBytes" "byte-sequence literals are not supported by the native backend"
  LitGrapheme _ -> unsupported "LitGrapheme" "grapheme literals are not supported by the native backend"
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

-- | A lambda: lift its body into a fresh top-level closure function and
-- return a @kclo@ capturing the current environment.
compileLam :: Term -> Gen Text
compileLam body = do
  fnName <- freshN "kfn_"
  env <- gets gsEnv
  -- inside the closure, the runtime env is `kpush(arg, captured)`
  (stmts, e) <- captured "kpush(arg, cenv)" (compile body)
  let fn =
        T.unlines $
          [ "static KValue *" <> fnName <> "(KEnv *cenv, KValue *arg) {"
          , "  (void)cenv; (void)arg;"
          ]
            ++ map ("  " <>) stmts
            ++ [ "  return " <> e <> ";"
               , "}"
               ]
  modify' $ \st ->
    st
      { gsTop = fn : gsTop st
      , gsProtos = ("static KValue *" <> fnName <> "(KEnv *, KValue *);") : gsProtos st
      }
  pure ("kclo(" <> fnName <> ", " <> env <> ")")

compileCtor :: GName -> [Term] -> Gen Text
compileCtor g args = do
  argEs <- mapM compile args
  if null argEs
    then pure ("kctor0(" <> cStr (gKey g) <> ")")
    else do
      arr <- freshN "args_"
      emit ("KValue *" <> arr <> "[] = {" <> T.intercalate ", " argEs <> "};")
      pure ("kctor(" <> cStr (gKey g) <> ", " <> T.pack (show (length argEs)) <> ", " <> arr <> ")")

compileRecord :: [(Text, Term)] -> Gen Text
compileRecord fs = do
  valEs <- mapM (compile . snd) fs
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

compileLet :: Term -> Term -> Gen Text
compileLet rhs body = do
  re <- compile rhs
  env <- gets gsEnv
  e2 <- freshN "env_"
  emit ("KEnv *" <> e2 <> " = kpush(" <> re <> ", " <> env <> ");")
  withEnv e2 (compile body)

-- | A local recursive let: allocate the binder cell first, evaluate the
-- rhs with the binder in scope, then back-patch the cell (the rhs is a
-- function whose closure captures the cell but does not read it until
-- applied — see docs/NATIVE_BACKEND.md §5).
compileLetRec :: Term -> Term -> Gen Text
compileLetRec rhs body = do
  env <- gets gsEnv
  e2 <- freshN "env_"
  emit ("KEnv *" <> e2 <> " = kpush(kunit(), " <> env <> ");")
  re <- withEnv e2 (compile rhs)
  emit (e2 <> "->val = " <> re <> ";")
  withEnv e2 (compile body)

withEnv :: Text -> Gen a -> Gen a
withEnv e act = do
  saved <- gets gsEnv
  modify' $ \g -> g {gsEnv = e}
  r <- act
  modify' $ \g -> g {gsEnv = saved}
  pure r

compileIf :: Term -> Term -> Term -> Gen Text
compileIf c t e = do
  ce <- compile c
  env <- gets gsEnv
  r <- freshN "if_"
  emit ("KValue *" <> r <> ";")
  (tStmts, te) <- captured env (compile t)
  (eStmts, ee) <- captured env (compile e)
  emit ("if (kas_bool(" <> ce <> ")) {")
  forM_ tStmts (emit . ("  " <>))
  emit ("  " <> r <> " = " <> te <> ";")
  emit "} else {"
  forM_ eStmts (emit . ("  " <>))
  emit ("  " <> r <> " = " <> ee <> ";")
  emit "}"
  pure r

-- ── Pattern matching ─────────────────────────────────────────────────

compileMatch :: Term -> [CaseAlt] -> Gen Text
compileMatch scrut alts = do
  se <- compile scrut
  sv <- freshN "scrut_"
  emit ("KValue *" <> sv <> " = " <> se <> ";")
  env <- gets gsEnv
  r <- freshN "match_"
  emit ("KValue *" <> r <> " = 0;")
  done <- freshN "matched_"
  emit ("int " <> done <> " = 0;")
  forM_ alts $ \alt -> compileAlt sv env r done alt
  emit ("if (!" <> done <> ") krt_fail(\"non-exhaustive match\");")
  pure r

compileAlt :: Text -> Text -> Text -> Text -> CaseAlt -> Gen ()
compileAlt sv env r done (CaseAlt pat mguard body) = do
  emit ("if (!" <> done <> ") {")
  -- pattern test + bindings produced as a nested block
  (blk, ()) <- captured env $ do
    mtest <- patTest sv pat
    case mtest of
      Nothing -> compileAltBody sv env r done pat mguard body
      Just test -> do
        emit ("if (" <> test <> ") {")
        compileAltBody sv env r done pat mguard body
        emit "}"
  forM_ blk (emit . ("  " <>))
  emit "}"

-- | Bind the pattern variables, evaluate the optional guard, and on a full
-- match compute the body and mark @done@.
compileAltBody :: Text -> Text -> Text -> Text -> CorePat -> Maybe Term -> Term -> Gen ()
compileAltBody sv env r done pat mguard body = do
  -- Bind variables (extends the env) by projecting the scrutinee `sv`.
  -- patTest already verified the constructor/shape; bindings just project.
  env' <- bindPatScrut sv env pat
  case mguard of
    Nothing -> do
      be <- withEnv env' (compile body)
      emit (r <> " = " <> be <> ";")
      emit (done <> " = 1;")
    Just gd -> do
      ge <- withEnv env' (compile gd)
      emit ("if (kas_bool(" <> ge <> ")) {")
      be <- withEnv env' (compile body)
      emit ("  " <> r <> " = " <> be <> ";")
      emit ("  " <> done <> " = 1;")
      emit "}"

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
  CPCtor g ps -> do
    let nps = length ps
    subs <- forM (zip [0 ..] ps) $ \(i, p) ->
      patTest (ctorArgExpr v nps i) p
    let here = "kctor_is(" <> v <> ", " <> cStr (gKey g) <> ")"
    pure (Just (conj (here : [t | Just t <- subs])))
  CPTuple ps -> do
    let n = length ps
    subs <- forM (zip [0 ..] ps) $ \(i, p) ->
      patTest (recAtExpr v i) p
    let szTest = "krec_size(" <> v <> ") == " <> T.pack (show n)
    pure (Just (conj (szTest : [t | Just t <- subs])))
  CPRecord pfs Nothing -> recordTests v pfs
  CPRecord pfs (Just rest)
    | T.null rest -> recordTests v pfs
    | otherwise -> do
        _ <- unsupported "CPRecord-rest" "record patterns with a rest binder are not supported"
        pure (Just "0")
  CPOr ps -> do
    -- Only support or-patterns whose alternatives bind nothing (the common
    -- literal/nullary case); otherwise the branch bindings would differ.
    if all bindsNothing ps
      then do
        subs <- mapM (patTest v) ps
        pure (Just (disj [maybe "1" id t | t <- subs]))
      else do
        _ <- unsupported "CPOr-binding" "or-patterns that bind variables are not supported"
        pure (Just "0")
  CPInject {} -> do
    _ <- unsupported "CPInject" "variant patterns are not supported by the native backend"
    pure (Just "0")
  CPInjectRest {} -> do
    _ <- unsupported "CPInjectRest" "variant residual patterns are not supported by the native backend"
    pure (Just "0")
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
  CPCtor _ ps -> all bindsNothing ps
  CPTuple ps -> all bindsNothing ps
  CPOr ps -> all bindsNothing ps
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
      CPCtor _ ps ->
        let nps = length ps
         in concat [go (ctorArgExpr v nps i) p | (i, p) <- zip [0 ..] ps]
      CPTuple ps -> concat [go (recAtExpr v i) p | (i, p) <- zip [0 ..] ps]
      CPRecord pfs _ ->
        concat [go ("kproj(" <> v <> ", " <> cStr n <> ")") p | (n, p) <- pfs]
      CPOr _ -> [] -- only non-binding or-patterns reach here
      CPInject _ p -> go v p
      CPInjectRest _ -> []

litValue :: Literal -> Gen (Maybe Text)
litValue = \case
  LitInt n
    | n >= toInteger (minBound :: Int) && n <= toInteger (maxBound :: Int) ->
        pure (Just ("kint(" <> cIntLit n <> ")"))
    | otherwise -> do
        _ <- unsupported "CPLit-range" "an integer literal pattern does not fit the 64-bit Int"
        pure Nothing
  LitStr s -> pure (Just ("kstr0(" <> cStr s <> ")"))
  LitScalar c -> pure (Just ("kchr(" <> T.pack (show (ord c)) <> ")"))
  LitDouble d -> pure (Just ("kdbl(" <> T.pack (show d) <> ")"))
  l -> do
    _ <- unsupported "CPLit" ("literal pattern of unsupported kind: " <> T.pack (show l))
    pure Nothing

-- ── do-kernel ────────────────────────────────────────────────────────

-- | Compile a do-block to a suspended IO action (@kio@) whose body runs
-- the scope.  The captured environment is the current one.
compileDo :: [KItem] -> Gen Text
compileDo items = do
  fnName <- freshN "kdo_"
  env <- gets gsEnv
  (stmts, ()) <- captured "cenv" (compileItems Tail items)
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

-- | Whether a scope is in tail position (the do-block body, whose final
-- value is the block's result) or nested (a loop\/if body, run for effect
-- with control flow propagating via C statements).  Both share the same
-- item handling and environment threading — the only differences are the
-- result of a trailing 'KExpr' and the empty-scope fall-through.
data ScopeMode = Tail | Nested
  deriving stock (Eq)

-- | Compile a sequence of do-kernel items, threading the environment
-- through bindings.  Mirrors 'Kappa.Interp.runScope' completion: in 'Tail'
-- position the scope @return@s the last 'KExpr' value (or Unit); in
-- 'Nested' position items run for effect and break\/continue\/return
-- propagate via C statements.  A single traversal serves both modes so the
-- two can never drift (the previous split caused real divergences).
compileItems :: ScopeMode -> [KItem] -> Gen ()
compileItems mode = go
  where
    go [] = case mode of
      Tail -> emit "return kunit();"
      Nested -> pure ()
    go (item : rest) = case item of
      KExpr t -> do
        te <- compile t
        if null rest && mode == Tail
          then emit ("return krun_io(" <> te <> ");")
          else emit ("krun_io(" <> te <> ");") >> go rest
      KLet _ pat t -> do
        te <- compile t
        sv <- freshN "let_"
        emit ("KValue *" <> sv <> " = " <> te <> ";")
        bindAndContinue sv pat
      KBind _ pat t -> do
        te <- compile t
        sv <- freshN "bind_"
        emit ("KValue *" <> sv <> " = krun_io(" <> te <> ");")
        bindAndContinue sv pat
      KReturn t -> do
        te <- compile t
        emit ("return " <> te <> ";")
      KVarItem _ t -> do
        te <- compile t
        ref <- freshN "var_"
        emit ("KValue *" <> ref <> " = kref_new(" <> te <> ");")
        env <- gets gsEnv
        e2 <- freshN "env_"
        emit ("KEnv *" <> e2 <> " = kpush(" <> ref <> ", " <> env <> ");")
        withEnv e2 (go rest)
      KAssign refT monadic rhsT -> do
        rhs <- compile rhsT
        rhsv <-
          if monadic
            then do
              v <- freshN "rhs_"
              emit ("KValue *" <> v <> " = krun_io(" <> rhs <> ");")
              pure v
            else pure rhs
        re <- compile refT
        emit ("kref_set(" <> re <> ", " <> rhsv <> ");")
        go rest
      KIf alts mels -> compileKIf alts mels >> go rest
      KWhile _ml cond bdy mels -> compileLoop (LoopWhile cond) bdy mels >> go rest
      KFor _ml pat src bdy mels -> compileLoop (LoopFor pat src) bdy mels >> go rest
      KBreak Nothing -> emitBreak
      KContinue Nothing -> emit "continue;"
      KBreak (Just _) -> skip "KBreak-labelled" "labelled break"
      KContinue (Just _) -> skip "KContinue-labelled" "labelled continue"
      KLetQ {} -> skip "KLetQ" "let? bindings"
      KDefer _ -> skip "KDefer" "defer"
      KUsing {} -> skip "KUsing" "using"
      where
        skip tag what = do
          _ <- unsupported tag (what <> " is not supported by the native backend")
          go rest
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
          withEnv env' (go rest)

-- | Emit a @break@, marking the enclosing loop's break flag so its @else@
-- block is skipped (§18.8: a loop's else runs only on normal completion).
emitBreak :: Gen ()
emitBreak = do
  loops <- gets gsLoops
  case loops of
    (flag : _) -> emit (flag <> " = 1; break;")
    [] -> emit "break;" -- defensive: break outside a loop is rejected upstream

-- | Like 'bindPat' but threads the concrete scrutinee C-expression
-- through the binding projections.
bindPatScrut :: Text -> Text -> CorePat -> Gen Text
bindPatScrut sv env pat = foldM push env (patBindings sv pat)
  where
    push e valExpr = do
      n <- freshN "env_"
      emit ("KEnv *" <> n <> " = kpush(" <> valExpr <> ", " <> e <> ");")
      pure n

compileKIf :: [(Term, [KItem])] -> Maybe [KItem] -> Gen ()
compileKIf alts mels = go alts
  where
    go [] = case mels of
      Just els -> emitBlock els
      Nothing -> pure ()
    go ((c, body) : more) = do
      ce <- compile c
      emit ("if (kas_bool(" <> ce <> ")) {")
      env <- gets gsEnv
      (blk, ()) <- captured env (compileItems Nested body)
      forM_ blk (emit . ("  " <>))
      emit "}"
      unless (null more && mels == Nothing) $ do
        emit "else {"
        go more
        emit "}"
    emitBlock items = do
      env <- gets gsEnv
      (blk, ()) <- captured env (compileItems Nested items)
      emit "{"
      forM_ blk (emit . ("  " <>))
      emit "}"

-- | The two loop shapes, sharing the body / break-flag / else machinery.
data LoopKind = LoopWhile !Term | LoopFor !CorePat !Term

-- | Compile a @while@\/@for@ loop with correct §18.8 completion: a @break@
-- sets the loop's flag (so the @else@ is skipped); a @continue@ advances
-- (the @for@ increment lives in the loop header, so C @continue@ still
-- advances the cursor); normal exhaustion runs the optional @else@.
compileLoop :: LoopKind -> [KItem] -> Maybe [KItem] -> Gen ()
compileLoop kind body mels = do
  env <- gets gsEnv
  flag <- freshN "brk_"
  emit ("int " <> flag <> " = 0;")
  case kind of
    LoopWhile cond -> do
      (condBlk, ce) <- captured env (compile cond)
      (bodyBlk, ()) <- withLoop flag (captured env (compileItems Nested body))
      emit "while (1) {"
      forM_ condBlk (emit . ("  " <>))
      emit ("  if (!kas_bool(" <> ce <> ")) break;")
      forM_ bodyBlk (emit . ("  " <>))
      emit "}"
    LoopFor pat src -> do
      se <- compile src
      it <- freshN "it_"
      emit ("KValue *" <> it <> " = " <> se <> ";")
      (bodyBlk, ()) <- withLoop flag $ captured env $ do
        elemV <- freshN "elem_"
        emit ("KValue *" <> elemV <> " = kctor_arg(" <> it <> ", 0);")
        e' <- bindPatScrut elemV env pat
        withEnv e' (compileItems Nested body)
      emit ("for (; kis_cons(" <> it <> "); " <> it <> " = kctor_arg(" <> it <> ", 1)) {")
      forM_ bodyBlk (emit . ("  " <>))
      emit "}"
  -- §18.8: the loop's else runs iff the loop completed without a break.
  case mels of
    Just els -> do
      (elsBlk, ()) <- captured env (compileItems Nested els)
      emit ("if (!" <> flag <> ") {")
      forM_ elsBlk (emit . ("  " <>))
      emit "}"
    Nothing -> pure ()

-- | Run an action with @flag@ pushed as the current loop's break flag.
withLoop :: Text -> Gen a -> Gen a
withLoop flag act = do
  saved <- gets gsLoops
  modify' $ \g -> g {gsLoops = flag : saved}
  r <- act
  modify' $ \g -> g {gsLoops = saved}
  pure r

