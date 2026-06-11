-- | Runtime interpreter (Spec §32.1: strict, call-by-value,
-- left-to-right evaluation) with the §18.8 do-kernel semantics:
-- completion records, LIFO exit actions run exactly once, loop @else@
-- only on no-break completion, typed IO failures via catch\/finally.
module Kappa.Interp
  ( runMain
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

preludeMod :: ModuleName
preludeMod = ModuleName ["std", "prelude"]

prelG :: Text -> GName
prelG = GName preludeMod

unitV :: Value
unitV = VCtor (prelG "Unit") []

-- | Run @main@ (an IO computation).
runMain :: Globals -> MetaState -> GName -> IO RunResult
runMain globals metas mainG = do
  let ec = EvalCtx globals metas
  case Map.lookup mainG (globalsMap globals) of
    Just gd | Just v <- gdValue gd -> do
      r <- try (runIOValue ec v)
      case r of
        Right _ -> pure RunOk
        Left (KappaError e) -> pure (RunFail (renderValueShallow e))
    _ -> pure (RunFail "main is not defined")

-- | Execute a value of IO type to completion.
runIOValue :: EvalCtx -> Value -> IO Value
runIOValue ec v = case force ec v of
  VDoV items env -> do
    r <- runScope ec env items
    case r of
      CplNormal x -> pure x
      CplReturn x -> pure x
      _ -> pure unitV
  VPrim p args -> runPrimIO ec p args
  other -> pure other

-- | Run embedded monadic splices (§18.3): the elaborator marks them as
-- applications of the internal @__runIO@ primitive. The walk is
-- left-to-right, executes each splice exactly once, and does not enter
-- lambda or suspension bodies (splices do not cross those boundaries).
runSplices :: EvalCtx -> Value -> IO Value
runSplices ec v0 = case v0 of
  -- scan the RAW value: forcing first would β-reduce past unrun splices
  VPrim "__runIO" (a : restArgs) -> do
    r <- runIOValue ec =<< runSplices ec a
    runSplices ec (foldl (\f x -> vapp ec f Expl x) r restArgs)
  VGlobN g sp
    | gnameText g == "__runIO"
    , (implPrefix, (Expl, a) : restSp) <- span ((== Impl) . fst) sp -> do
        _ <- pure implPrefix -- erased type arguments of the splice marker
        r <- runIOValue ec =<< runSplices ec a
        runSplices ec (evalApp ec r restSp)
  VGlobN g sp -> do
    sp' <- mapM (\(ic, a) -> (,) ic <$> runSplices ec a) sp
    pure (force ec (VGlobN g sp'))
  VFlex m sp -> do
    sp' <- mapM (\(ic, a) -> (,) ic <$> runSplices ec a) sp
    pure (force ec (VFlex m sp'))
  VPrim p args -> do
    args' <- mapM (runSplices ec) args
    pure (force ec (rebuild p args'))
    where
      rebuild q as = case evalPurePrim q (map (force ec) as) of
        Just r -> r
        Nothing -> VPrim q as
  VCtor g args -> VCtor g <$> mapM (runSplices ec) args
  VRecordV fs -> VRecordV <$> mapM (\(n, a) -> (,) n <$> runSplices ec a) fs
  VInject t a -> VInject t <$> runSplices ec a
  _ -> pure (force ec v0)

-- | Evaluate a term and execute its splices.
evalK :: EvalCtx -> Env -> Term -> IO Value
evalK ec env t = runSplices ec (eval ec env t)

-- One do-scope: exit actions are scheduled here and run exactly once,
-- LIFO, on every way out (§18.7, §18.8.3).
runScope :: EvalCtx -> Env -> [KItem] -> IO Completion
runScope ec env0 items0 = do
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
          x <- runIOValue ec =<< evalK ec env t
          if null rest then leave (CplNormal x) else go env rest
        KLet _ pat t -> do
          x <- evalK ec env t
          bindOrDie pat x $ \bs -> go (reverse bs ++ env) rest
        KBind _ pat t -> do
          x <- runIOValue ec =<< evalK ec env t
          bindOrDie pat x $ \bs -> go (reverse bs ++ env) rest
        KLetQ pat t mElse -> do
          x <- evalK ec env t
          case matchPat ec pat x of
            Just bs -> go (reverse bs ++ env) rest
            Nothing -> case mElse of
              Just (rp, fe) -> case matchPat ec rp x of
                Just bs -> do
                  r <- runIOValue ec =<< evalK ec (reverse bs ++ env) fe
                  leave (CplNormal r)
                Nothing -> leave =<< throwIO (KappaError (VLit (LitStr "let? else: residue pattern failed")))
              Nothing -> leave =<< throwIO (KappaError (VLit (LitStr "let? pattern failed and no Alternative is available")))
        KVarItem _ t -> do
          ref <- newIORef =<< evalK ec env t
          go (VRef ref : env) rest
        KAssign refT monadic rhsT -> do
          rhs <-
            if monadic
              then runIOValue ec =<< evalK ec env rhsT
              else evalK ec env rhsT
          case force ec (eval ec env refT) of
            VRef ref -> writeIORef ref rhs
            _ -> throwIO (KappaError (VLit (LitStr "assignment target is not a var")))
          go env rest
        KReturn _ t -> leave . CplReturn =<< evalK ec env t
        KBreak ml -> leave (CplBreak ml)
        KContinue ml -> leave (CplContinue ml)
        KDefer _ t -> do
          modifyIORef' exitsRef ((() <$ (runIOValue ec =<< evalK ec env t)) :)
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
          loop = (asBool <$> evalK ec env cond) >>= \cv -> case cv of
            Just True -> do
              r <- runScope ec env body
              case r of
                CplNormal _ -> loop
                CplContinue l | l `targets` ml -> loop
                CplBreak l | l `targets` ml -> pure (CplNormal unitV)
                other -> pure other
            Just False -> runElse env mels
            Nothing -> throwIO (KappaError (VLit (LitStr "while condition was not a Bool")))

      forLoop env ml pat src body mels = do
        srcV <- evalK ec env src
        loop (listElems srcV)
        where
          loop [] = runElse env mels
          loop (x : xs) = case matchPat ec pat x of
            Nothing -> throwIO (KappaError (VLit (LitStr "for pattern failed")))
            Just bs -> do
              r <- runScope ec (reverse bs ++ env) body
              case r of
                CplNormal _ -> loop xs
                CplContinue l | l `targets` ml -> loop xs
                CplBreak l | l `targets` ml -> pure (CplNormal unitV)
                other -> pure other

      runElse env mels = case mels of
        Just els -> runScope ec env els
        Nothing -> pure (CplNormal unitV)

      pickIf env [] mels = runElse env mels
      pickIf env ((c, body) : more) mels =
        (asBool <$> evalK ec env c) >>= \cv -> case cv of
          Just True -> runScope ec env body
          Just False -> pickIf env more mels
          Nothing -> throwIO (KappaError (VLit (LitStr "if condition was not a Bool")))

      targets _ Nothing = True
      targets l ml = l == ml

      asBool x = case force ec x of
        VCtor (GName _ "True") [] -> Just True
        VCtor (GName _ "False") [] -> Just False
        _ -> Nothing

      listElems x = case force ec x of
        VCtor (GName _ "::") [h, t] -> h : listElems t
        _ -> []

  go env0 items0

-- ── IO primitives ────────────────────────────────────────────────────

intOf :: Value -> Maybe Integer
intOf = \case
  VLit (LitInt n) -> Just n
  _ -> Nothing

runPrimIO :: EvalCtx -> Text -> [Value] -> IO Value
runPrimIO ec p rawArgs = do
  args <- mapM (runSplices ec) rawArgs
  runPrimIO' ec p args

runPrimIO' :: EvalCtx -> Text -> [Value] -> IO Value
runPrimIO' ec p args = case (p, map (force ec) args) of
  ("printString", [VLit (LitStr s)]) -> TIO.putStr s >> hFlush stdout >> pure unitV
  ("printlnString", [VLit (LitStr s)]) -> TIO.putStrLn s >> pure unitV
  ("ioPure", [v]) -> pure v
  ("throwIO", [e]) -> throwIO (KappaError e)
  ("catchIO", [body, handler]) -> do
    r <- try (runIOValue ec body)
    case r of
      Right v -> pure v
      Left (KappaError e) -> runIOValue ec (vapp ec handler Expl e)
  ("finallyIO", [body, fin]) -> do
    r <- try (runIOValue ec body)
    _ <- runIOValue ec fin
    case r of
      Right v -> pure v
      Left err -> throwIO (err :: KappaError)
  ("__runIO", [action]) -> runIOValue ec action
  ("newRef", [v]) -> VRef <$> newIORef v
  ("readRef", [VRef r]) -> readIORef r
  ("writeRef", [VRef r, v]) -> writeIORef r v >> pure unitV
  ("ioBind", [m, k]) -> do
    a <- runIOValue ec m
    runIOValue ec (vapp ec k Expl a)
  ("ioThen", [m, k]) -> do
    _ <- runIOValue ec m
    runIOValue ec k
  _ ->
    throwIO . KappaError . VLit . LitStr $
      "unhandled IO primitive: " <> p <> "/" <> T.pack (show (length args))
        <> " args=" <> T.intercalate " ; " (map (renderTerm . quote ec 0) args)
