-- | Runtime interpreter (Spec §32.1: strict, call-by-value,
-- left-to-right evaluation) with the §18.8 do-kernel semantics:
-- completion records, LIFO exit actions run exactly once, loop @else@
-- only on no-break completion, typed IO failures via catch\/finally.
--
-- Output goes through an 'RT' sink so the Appendix T harness can run
-- programs in-process and capture stdout ('runMainCaptured').
module Kappa.Interp
  ( runMain
  , runMainCaptured
  , RunResult (..)
  ) where

import Control.Exception (Exception, throwIO, try)
import Data.IORef
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Kappa.Core
import Kappa.Eval
import Kappa.Pretty (renderTerm, renderValueShallow)
import Kappa.Source (ModuleName (..))
import System.IO (hFlush, stdout)

data RunResult = RunOk | RunFail Text
  deriving stock (Show)

newtype KappaError = KappaError Value
instance Show KappaError where
  show (KappaError v) = "error: " ++ T.unpack (renderValueShallow v)
instance Exception KappaError

data Completion
  = CplNormal Value
  | CplBreak (Maybe Text)
  | CplContinue (Maybe Text)
  | CplReturn Value

-- | Runtime context: evaluation context plus the stdout sink.
data RT = RT
  { rtEC :: !EvalCtx
  , rtEmit :: !(Text -> IO ())
  }

preludeMod :: ModuleName
preludeMod = ModuleName ["std", "prelude"]

prelG :: Text -> GName
prelG = GName preludeMod

unitV :: Value
unitV = VCtor (prelG "Unit") []

-- | Run @main@ (an IO computation) writing to real stdout.
runMain :: Globals -> MetaState -> GName -> IO RunResult
runMain globals metas mainG = do
  let rt = RT (EvalCtx globals metas True) (\t -> TIO.putStr t >> hFlush stdout)
  runMainRT rt mainG

-- | Run @main@ capturing everything written via printString\/printlnString
-- (Appendix T @mode run@ support); returns the result and the output.
runMainCaptured :: Globals -> MetaState -> GName -> IO (RunResult, Text)
runMainCaptured globals metas mainG = do
  buf <- newIORef []
  let rt = RT (EvalCtx globals metas True) (\t -> modifyIORef' buf (t :))
  r <- runMainRT rt mainG
  out <- T.concat . reverse <$> readIORef buf
  pure (r, out)

runMainRT :: RT -> GName -> IO RunResult
runMainRT rt mainG =
  case Map.lookup mainG (globalsMap (ecGlobals (rtEC rt))) of
    Just gd | Just v <- gdValue gd -> do
      r <- try (runIOValue rt v)
      case r of
        Right _ -> pure RunOk
        Left (KappaError e) -> pure (RunFail (renderValueShallow e))
    _ -> pure (RunFail "main is not defined")

-- | Execute a value of IO type to completion.
runIOValue :: RT -> Value -> IO Value
runIOValue rt v = case force (rtEC rt) v of
  VDoV items env -> do
    r <- runScope rt env items
    case r of
      CplNormal x -> pure x
      CplReturn x -> pure x
      -- unreachable for elaborated programs: break/continue outside a
      -- loop body of their own do-scope are rejected at compile time
      -- (E_BREAK_OUTSIDE_LOOP / E_LABEL_UNRESOLVED), and the loop
      -- machinery in 'runScope' consumes in-loop completions.
      CplBreak {} ->
        throwIO (KappaError (VLit (LitStr "internal: break escaped its do-scope")))
      CplContinue {} ->
        throwIO (KappaError (VLit (LitStr "internal: continue escaped its do-scope")))
  VPrim p args -> runPrimIO rt p args
  other -> pure other

-- | Run embedded monadic splices (§18.3): the elaborator marks them as
-- applications of the internal @__runIO@ primitive. The walk is
-- left-to-right, executes each splice exactly once, and does not enter
-- lambda or suspension bodies (splices do not cross those boundaries).
runSplices :: RT -> Value -> IO Value
runSplices rt v0 = case v0 of
  -- scan the RAW value: forcing first would β-reduce past unrun splices
  VPrim "__runIO" (a : restArgs) -> do
    r <- runIOValue rt =<< runSplices rt a
    runSplices rt (foldl (\f x -> vapp ec f Expl x) r restArgs)
  VGlobN g sp
    -- the implicit prefix holds the splice marker's erased type
    -- arguments; only the explicit argument onward matters here
    | gnameText g == "__runIO"
    , (_implPrefix, (Expl, a) : restSp) <- span ((== Impl) . fst) sp -> do
        r <- runIOValue rt =<< runSplices rt a
        runSplices rt (evalApp ec r restSp)
  VGlobN g sp -> do
    sp' <- mapM (\(ic, a) -> (,) ic <$> runSplices rt a) sp
    pure (force ec (VGlobN g sp'))
  VFlex m sp -> do
    sp' <- mapM (\(ic, a) -> (,) ic <$> runSplices rt a) sp
    pure (force ec (VFlex m sp'))
  VPrim p args -> do
    args' <- mapM (runSplices rt) args
    pure (force ec (rebuild p args'))
    where
      rebuild q as = case evalPurePrim q (map (force ec) as) of
        Just r -> r
        Nothing -> VPrim q as
  VCtor g args -> VCtor g <$> mapM (runSplices rt) args
  VRecordV fs -> VRecordV <$> mapM (\(n, a) -> (,) n <$> runSplices rt a) fs
  VInject t a -> VInject t <$> runSplices rt a
  _ -> pure (force ec v0)
  where
    ec = rtEC rt

-- | Evaluate a term and execute its splices.
evalK :: RT -> Env -> Term -> IO Value
evalK rt env t = runSplices rt (eval (rtEC rt) env t)

-- One do-scope: exit actions are scheduled here and run exactly once,
-- LIFO, on every way out (§18.7, §18.8.3).
runScope :: RT -> Env -> [KItem] -> IO Completion
runScope rt env0 items0 = do
  let ec = rtEC rt
  exitsRef <- newIORef []
  let runExits = do
        exits <- readIORef exitsRef
        writeIORef exitsRef []
        sequence_ exits
      leave c = runExits >> pure c

      go :: Env -> [KItem] -> IO Completion
      go _ [] = leave (CplNormal unitV)
      go env (item : rest) = case item of
        KExpr t -> do
          x <- runIOValue rt =<< evalK rt env t
          if null rest then leave (CplNormal x) else go env rest
        KLet _ pat t -> do
          x <- evalK rt env t
          bindOrDie pat x $ \bs -> go (reverse bs ++ env) rest
        KBind _ pat t -> do
          x <- runIOValue rt =<< evalK rt env t
          bindOrDie pat x $ \bs -> go (reverse bs ++ env) rest
        KLetQ pat t mElse -> do
          x <- evalK rt env t
          case matchPat ec pat x of
            Just bs -> go (reverse bs ++ env) rest
            Nothing -> case mElse of
              Just (rp, fe) -> case matchPat ec rp x of
                Just bs -> do
                  r <- runIOValue rt =<< evalK rt (reverse bs ++ env) fe
                  leave (CplNormal r)
                Nothing -> leave =<< throwIO (KappaError (VLit (LitStr "let? else: residue pattern failed")))
              Nothing -> leave =<< throwIO (KappaError (VLit (LitStr "let? pattern failed and no Alternative is available")))
        KVarItem _ t -> do
          ref <- newIORef =<< evalK rt env t
          go (VRef ref : env) rest
        KAssign refT monadic rhsT -> do
          rhs <-
            if monadic
              then runIOValue rt =<< evalK rt env rhsT
              else evalK rt env rhsT
          case force ec (eval ec env refT) of
            VRef ref -> writeIORef ref rhs
            _ -> throwIO (KappaError (VLit (LitStr "assignment target is not a var")))
          go env rest
        KReturn t -> leave . CplReturn =<< evalK rt env t
        KBreak ml -> leave (CplBreak ml)
        KContinue ml -> leave (CplContinue ml)
        KDefer t -> do
          modifyIORef' exitsRef ((() <$ (runIOValue rt =<< evalK rt env t)) :)
          go env rest
        KWhile ml cond body mels -> loopOut =<< whileLoop env ml cond body mels
        KFor ml pat src body mels -> loopOut =<< forLoop env ml pat src body mels
        KIf alts mels -> do
          r <- pickIf env alts mels
          case r of
            CplNormal _ -> go env rest
            other -> leave other
        KUsing {} -> throwIO (KappaError (VLit (LitStr "using is unsupported")))
        where
          loopOut r = case r of
            CplNormal _ -> go env rest
            other -> leave other
          bindOrDie pat x k = case matchPat ec pat x of
            Just bs -> k bs
            Nothing -> leave =<< throwIO (KappaError (VLit (LitStr "irrefutable binding failed at runtime")))

      whileLoop env ml cond body mels = loop
        where
          loop = (asBool <$> evalK rt env cond) >>= \cv -> case cv of
            Just True -> do
              r <- runScope rt env body
              case r of
                CplNormal _ -> loop
                CplContinue l | l `targets` ml -> loop
                CplBreak l | l `targets` ml -> pure (CplNormal unitV)
                other -> pure other
            Just False -> runElse env mels
            Nothing -> throwIO (KappaError (VLit (LitStr "while condition was not a Bool")))

      forLoop env ml pat src body mels = do
        srcV <- evalK rt env src
        loop (listElems srcV)
        where
          loop [] = runElse env mels
          loop (x : xs) = case matchPat ec pat x of
            Nothing -> throwIO (KappaError (VLit (LitStr "for pattern failed")))
            Just bs -> do
              r <- runScope rt (reverse bs ++ env) body
              case r of
                CplNormal _ -> loop xs
                CplContinue l | l `targets` ml -> loop xs
                CplBreak l | l `targets` ml -> pure (CplNormal unitV)
                other -> pure other

      runElse env mels = case mels of
        Just els -> runScope rt env els
        Nothing -> pure (CplNormal unitV)

      pickIf env [] mels = runElse env mels
      pickIf env ((c, body) : more) mels =
        (asBool <$> evalK rt env c) >>= \cv -> case cv of
          Just True -> runScope rt env body
          Just False -> pickIf env more mels
          Nothing -> throwIO (KappaError (VLit (LitStr "if condition was not a Bool")))

      -- Does a break/continue carrying label @l@ target the loop labeled
      -- @ml@ (§18.2.5)? An unlabeled break/continue targets the nearest
      -- enclosing loop (i.e. this one); a labeled one passes through
      -- every loop until it reaches the loop carrying its label.
      targets :: Maybe Text -> Maybe Text -> Bool
      targets Nothing _ = True
      targets (Just l) ml = Just l == ml

      asBool x = case force ec x of
        VCtor (GName _ "True") [] -> Just True
        VCtor (GName _ "False") [] -> Just False
        _ -> Nothing

      listElems x = case force ec x of
        VCtor (GName _ "::") [h, t] -> h : listElems t
        _ -> []

  go env0 items0

-- ── IO primitives ────────────────────────────────────────────────────

runPrimIO :: RT -> Text -> [Value] -> IO Value
runPrimIO rt p rawArgs = do
  args <- mapM (runSplices rt) rawArgs
  runPrimIO' rt p args

runPrimIO' :: RT -> Text -> [Value] -> IO Value
runPrimIO' rt p args = case (p, map (force ec) args) of
  ("printString", [VLit (LitStr s)]) -> rtEmit rt s >> pure unitV
  ("printlnString", [VLit (LitStr s)]) -> rtEmit rt (s <> "\n") >> pure unitV
  ("ioPure", [v]) -> pure v
  ("throwIO", [e]) -> throwIO (KappaError e)
  ("catchIO", [body, handler]) -> do
    r <- try (runIOValue rt body)
    case r of
      Right v -> pure v
      Left (KappaError e) -> runIOValue rt (vapp ec handler Expl e)
  ("finallyIO", [body, fin]) -> do
    r <- try (runIOValue rt body)
    _ <- runIOValue rt fin
    case r of
      Right v -> pure v
      Left err -> throwIO (err :: KappaError)
  ("__runIO", [action]) -> runIOValue rt action
  ("newRef", [v]) -> VRef <$> newIORef v
  ("readRef", [VRef r]) -> readIORef r
  ("writeRef", [VRef r, v]) -> writeIORef r v >> pure unitV
  ("ioBind", [m, k]) -> do
    a <- runIOValue rt m
    runIOValue rt (vapp ec k Expl a)
  ("ioThen", [m, k]) -> do
    _ <- runIOValue rt m
    runIOValue rt k
  _ ->
    throwIO . KappaError . VLit . LitStr $
      "unhandled IO primitive: " <> p <> "/" <> T.pack (show (length args))
        <> " args=" <> T.intercalate " ; " (map (renderTerm . quote ec 0) args)
  where
    ec = rtEC rt
