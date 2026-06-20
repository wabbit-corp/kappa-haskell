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
  , runMainCapturedValue
  , RunResult (..)
  ) where

import Control.Concurrent (forkIO, yield)
import Control.Concurrent.MVar (newEmptyMVar, readMVar, tryPutMVar)
import qualified Control.Concurrent.STM as STM
import Control.Exception (AsyncException (..), Exception, SomeException, fromException, throwIO, try)
import Data.IORef
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import GHC.Clock (getMonotonicTimeNSec)
import System.IO.Unsafe (unsafePerformIO)
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

-- | §18.1.13: a transaction attempt that must suspend until a TVar it read
-- changes (`retry`/`check False`/`stmAbort`/STM `empty`). Caught by the
-- 'stmAtomically' driver, which parks (via GHC STM) until the global STM
-- write-version advances, then re-runs the transaction.
data RetrySignal = RetrySignal
instance Show RetrySignal where show _ = "STM retry"
instance Exception RetrySignal

-- | §18.1.13 cooperative STM wake signal: a monotonic counter bumped by every
-- 'writeTVar'. A retrying transaction blocks (GHC STM 'retry', which the RTS
-- suspends the fiber on) until this advances — so another fiber writing a
-- TVar wakes the parked transaction (weak fairness via the GHC scheduler).
{-# NOINLINE globalStmVersion #-}
globalStmVersion :: STM.TVar Int
globalStmVersion = unsafePerformIO (STM.newTVarIO 0)

-- | §18.8.2: a fiber's terminal Exit from its run result — Success on normal
-- completion, Failure (Fail e) for a raised Kappa error (isolated from the
-- parent), Failure (Defect …) for any other host exception.
exitOf :: Either SomeException Value -> Value
exitOf (Right v) = VCtor (prelG "Success") [v]
exitOf (Left e) = case fromException e of
  Just (KappaError ev) -> VCtor (prelG "Failure") [VCtor (prelG "Fail") [ev]]
  Nothing ->
    VCtor (prelG "Failure")
      [VCtor (prelG "Defect") [VCtor (prelG "MkDefectInfo") [VLit (LitStr (T.pack (show e)))]]]

-- | §18.1.13 'atomically' on the single agent: run the transaction; if it
-- signals retry, park until the STM write-version advances, then re-run.
stmAtomically :: RT -> Value -> IO Value
stmAtomically rt action = loop
  where
    loop = do
      v0 <- STM.readTVarIO globalStmVersion
      r <- try (runIOValue rt action)
      case r of
        Right val -> pure val
        Left RetrySignal -> do
          STM.atomically (do v <- STM.readTVar globalStmVersion; STM.check (v /= v0))
          loop

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
  let rt = RT (EvalCtx globals metas True mempty) (\t -> TIO.putStr t >> hFlush stdout)
  fst <$> runMainRT rt mainG

-- | Run @main@ capturing everything written via printString\/printlnString
-- (Appendix T @mode run@ support); returns the result and the output.
runMainCaptured :: Globals -> MetaState -> GName -> IO (RunResult, Text)
runMainCaptured globals metas mainG = do
  (r, _, out) <- runMainCapturedValue globals metas mainG
  pure (r, out)

-- | Like 'runMainCaptured', but also returns the entrypoint's final
-- value (when it completed normally), so the test harness can render a
-- non-Unit result like the reference run task does.
runMainCapturedValue :: Globals -> MetaState -> GName -> IO (RunResult, Maybe Value, Text)
runMainCapturedValue globals metas mainG = do
  buf <- newIORef []
  let rt = RT (EvalCtx globals metas True mempty) (\t -> modifyIORef' buf (t :))
  (r, mv) <- runMainRT rt mainG
  out <- T.concat . reverse <$> readIORef buf
  pure (r, mv, out)

runMainRT :: RT -> GName -> IO (RunResult, Maybe Value)
runMainRT rt mainG =
  case Map.lookup mainG (globalsMap (ecGlobals (rtEC rt))) of
    Just gd | Just v <- gdValue gd -> do
      r <- try (runIOValue rt v)
      case r of
        Right x -> pure (RunOk, Just x)
        Left e
          | Just (KappaError ev) <- fromException e ->
              pure (RunFail (renderValueShallow ev), Nothing)
          -- §18.8 resource exhaustion: GHC raises 'StackOverflow' /
          -- 'HeapOverflow' as recoverable async exceptions (the
          -- executable's '-K64m' guard bounds the host stack, so control
          -- DOES return to us here). Classify them as the spec's
          -- 'StackOverflow' / 'OutOfMemory' defects and surface a clean
          -- Kappa runtime diagnostic instead of letting the raw RTS
          -- message escape — this covers strict-accumulating divergence
          -- that outruns the §32.1 force-fuel guard before it can
          -- materialize a '__recursionDepth' marker.
          | Just StackOverflow <- fromException e ->
              pure (RunFail "evaluation exceeded the available stack (StackOverflow)", Nothing)
          | Just HeapOverflow <- fromException e ->
              pure (RunFail "evaluation exhausted the available heap (OutOfMemory)", Nothing)
          | otherwise -> throwIO e
    _ -> pure (RunFail "main is not defined", Nothing)

-- | Execute a value of IO type to completion.
runIOValue :: RT -> Value -> IO Value
runIOValue rt v = case force (rtEC rt) v of
  VDoV lbl items env -> do
    r <- runScope rt [] lbl env items
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

-- | Does the RAW value tree contain an embedded @__runIO@ splice
-- marker? The recursive splice walk re-forces every spine node it
-- rebuilds, so for the overwhelmingly common splice-free value it would
-- re-force each subtree once per ancestor — quadratic to exponential on
-- deep neutral spines (left-nested operator chains in particular). This
-- cheap, force-free structural pre-scan lets 'runSplices' fall straight
-- through to a single 'force' when there is nothing to splice. It mirrors
-- the structural shape of the 'runSplices' walk (same node kinds, same
-- "do not enter lambda/suspension bodies" boundary).
hasSplice :: Value -> Bool
hasSplice = \case
  VPrim "__runIO" (_ : _) -> True
  VGlobN g sp
    | gnameText g == "__runIO"
    , any ((== Expl) . fst) sp -> True
    | otherwise -> any (hasSplice . snd) sp
  VFlex _ sp -> any (hasSplice . snd) sp
  VPrim _ args -> any hasSplice args
  VCtor _ args -> any hasSplice args
  VRecordV fs -> any (hasSplice . snd) fs
  VInject _ a -> hasSplice a
  _ -> False

-- | Run embedded monadic splices (§18.3): the elaborator marks them as
-- applications of the internal @__runIO@ primitive. The walk is
-- left-to-right, executes each splice exactly once, and does not enter
-- lambda or suspension bodies (splices do not cross those boundaries).
runSplices :: RT -> Value -> IO Value
runSplices rt v0
  -- fast path: no embedded splice in the raw tree, so the walk would only
  -- rebuild-and-re-force an unchanged spine. Force once and return.
  | not (hasSplice v0) = pure (force ec v0)
  where
    ec = rtEC rt
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
-- | Run a do-scope. @reg@ maps the labels of enclosing do-scopes to their
-- exit-action queues, so a @defer@L@ (§18.7) registers onto the labeled
-- (possibly outer) scope; @selfLabel@ is this scope's own label, added to
-- the registry visible to nested scopes. Deferred actions run LIFO when the
-- scope they were scheduled onto exits.
runScope :: RT -> [(Text, IORef [IO ()])] -> Maybe Text -> Env -> [KItem] -> IO Completion
runScope rt reg0 selfLabel env0 items0 = do
  let ec = rtEC rt
  exitsRef <- newIORef []
  let reg = case selfLabel of
        Just l -> (l, exitsRef) : reg0
        Nothing -> reg0
      runExits = do
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
        KDefer ml t -> do
          -- §18.7: schedule onto the current scope (Nothing) or the named
          -- enclosing labeled scope; the action's env is captured here but
          -- it runs when the targeted scope unwinds. The label is resolved
          -- at compile time, so a missing entry falls back to this scope.
          let target = case ml of
                Nothing -> exitsRef
                Just l -> fromMaybe exitsRef (lookup l reg)
          modifyIORef' target ((() <$ (runIOValue rt =<< evalK rt env t)) :)
          go env rest
        KWhile ml cond body mels -> loopOut =<< whileLoop env ml cond body mels
        KFor ml pat src body mels -> loopOut =<< forLoop env ml pat src body mels
        KIf alts mels -> do
          r <- pickIf env alts mels
          case r of
            CplNormal _ -> go env rest
            other -> leave other
        -- §19.5: acquire the owned resource, bind `pat` (borrowed) for the
        -- rest of the scope, and attach `release resource` to this scope's
        -- exit queue so it runs LIFO on every exit path (like `defer`).
        KUsing pat acquireT releaseT -> do
          resource <- runIOValue rt =<< evalK rt env acquireT
          releaseFn <- evalK rt env releaseT
          modifyIORef' exitsRef ((() <$ runIOValue rt (vapp ec releaseFn Expl resource)) :)
          bindOrDie pat resource $ \bs -> go (reverse bs ++ env) rest
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
              r <- runScope rt reg ml env body
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
              r <- runScope rt reg ml (reverse bs ++ env) body
              case r of
                CplNormal _ -> loop xs
                CplContinue l | l `targets` ml -> loop xs
                CplBreak l | l `targets` ml -> pure (CplNormal unitV)
                other -> pure other

      runElse env mels = case mels of
        Just els -> runScope rt reg Nothing env els
        Nothing -> pure (CplNormal unitV)

      pickIf env [] mels = runElse env mels
      pickIf env ((c, body) : more) mels =
        (asBool <$> evalK rt env c) >>= \cv -> case cv of
          Just True -> runScope rt reg Nothing env body
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
  -- §23.6: run closed staged code (the closed-code value carries the
  -- staged computation's present-stage value directly)
  ("runCode", [VPrim "__closedCode" [v]]) -> pure v
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
  -- §18.11/§32.2: fork runs the fiber to completion on the single agent,
  -- capturing its terminal Exit (Success v / Failure (Fail e)); the handle
  -- is a cell holding that Exit, retrieved by __awaitFiber. A fiber failure
  -- is isolated here (not propagated to the forking context) and surfaced
  -- via the Exit the parent awaits.
  -- fork spawns a cooperative fiber (a GHC green thread on the single OS
  -- agent — non-threaded RTS ⇒ no parallelism, weak fairness from the RTS
  -- scheduler). The child runs concurrently; its terminal Exit is delivered
  -- through an MVar that await reads. fork does NOT run to completion here.
  ("__forkRun", [action]) -> do
    mv <- newEmptyMVar
    _ <- forkIO $ do
      r <- try (runIOValue rt action) :: IO (Either SomeException Value)
      _ <- tryPutMVar mv (exitOf r)
      pure ()
    pure (VMVar mv)
  -- await PARKS the current fiber on the result MVar until the child
  -- completes (the RTS runs other runnable fibers meanwhile).
  ("__awaitFiber", [VMVar mv]) -> readMVar mv
  -- §18.1.13 STM (single agent): TVars are cells; `atomically` runs the
  -- transaction directly (no concurrent agent ⇒ trivially serializable);
  -- `retry`/`check False`/`stmAbort` abort the transaction.
  ("newTVar", [v]) -> VTVar <$> STM.newTVarIO v
  ("readTVar", [VTVar tv]) -> STM.readTVarIO tv
  -- a write commits and advances the wake-version so any parked (retrying)
  -- transaction is resumed by the GHC STM scheduler.
  ("writeTVar", [VTVar tv, v]) ->
    STM.atomically (STM.writeTVar tv v >> STM.modifyTVar' globalStmVersion (+ 1)) >> pure unitV
  ("atomically", [action]) -> stmAtomically rt action
  ("check", [VCtor (GName _ "True") []]) -> pure unitV
  ("check", [VCtor (GName _ "False") []]) -> throwIO RetrySignal
  ("retry", _) -> throwIO RetrySignal
  ("stmAbort", _) -> throwIO RetrySignal
  -- §18.11 one-shot promises: a cell holding Option (Exit e a) — None until
  -- completed. The first completePromise wins (True); later ones return
  -- False. await reads the stored Exit; awaiting an uncompleted promise with
  -- no other fiber to complete it is a single-agent deadlock (clean error).
  -- a promise is an empty MVar; the first completePromise fills it (True),
  -- later attempts return False; await PARKS on the MVar until completion
  -- (another runnable fiber completes it; the RTS resumes the parked one).
  ("newPromise", _) -> VMVar <$> newEmptyMVar
  ("completePromise", [VMVar mv, exitV]) ->
    (\b -> VCtor (prelG (if b then "True" else "False")) []) <$> tryPutMVar mv exitV
  ("awaitPromiseExit", [VMVar mv]) -> readMVar mv
  ("awaitPromise", [VMVar mv]) -> do
    exitV <- readMVar mv
    case force ec exitV of
      VCtor (GName _ "Success") [v] -> pure v
      VCtor (GName _ "Failure") [c] -> case force ec c of
        VCtor (GName _ "Fail") [e] -> throwIO (KappaError e)
        _ -> throwIO (KappaError (VLit (LitStr "awaitPromise: promise failed with a non-Fail cause")))
      _ -> throwIO (KappaError (VLit (LitStr "awaitPromise: malformed promise Exit")))
  -- §18.1 monotonic timers (single agent): nowMonotonic reads the host
  -- monotonic clock; sleepFor/sleepUntil advance instantly (a single agent
  -- has no other fiber to schedule during a sleep).
  ("nowMonotonic", _) -> (VLit . LitInt . fromIntegral) <$> getMonotonicTimeNSec
  -- sleep parks the fiber cooperatively, yielding to other runnable fibers
  -- (it MUST NOT block the whole agent); monotonic time is approximate here.
  ("sleepFor", [_]) -> yield >> pure unitV
  ("sleepUntil", [_]) -> yield >> pure unitV
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
