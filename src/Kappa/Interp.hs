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

import Control.Concurrent (ThreadId, forkIO, forkIOWithUnmask, killThread, myThreadId, threadDelay, throwTo, yield)
import Control.Concurrent.MVar (MVar, newEmptyMVar, readMVar, tryPutMVar)
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

-- | §18.1.4 fiber interruption / cancellation. Delivered cross-fiber by
-- 'throwTo' (the target fiber is a GHC green thread); the payload is the
-- structured §18.1.2 'InterruptCause' value. The target's outermost 'try'
-- in the fork driver catches it (after its finalizers unwind) and records
-- @Failure (Interrupt cause)@ as the fiber's terminal Exit.
newtype Interrupt = Interrupt Value
instance Show Interrupt where show _ = "fiber interrupt"
instance Exception Interrupt

-- | A re-raised non-typed runtime cause (§18.1.2 Defect / composite) thrown
-- back into host execution by 'reraiseCauseValue' / @__reraiseCause@; carries
-- the original 'Cause' value so 'exitOf' can reconstruct it unchanged.
newtype CauseReraise = CauseReraise Value
instance Show CauseReraise where show _ = "reraised cause"
instance Exception CauseReraise

-- | Build a structured 'InterruptCause' with the given §18.1.2 tag and no
-- initiating fiber (@by = None@) — the form used by runtime-originated
-- interruption (timeout's @TimedOut@, race's @RaceLost@).
interruptCause :: Text -> Value
interruptCause tag =
  VCtor (prelG "MkInterruptCause") [VCtor (prelG tag) [], VCtor (prelG "None") []]

-- | The §18.1.2 'Cause' value carried by a host exception that escaped a
-- fiber/sandbox: typed 'Fail', structured 'Interrupt', a faithfully
-- round-tripped re-raised cause, or a 'Defect' for any other host failure.
causeOf :: SomeException -> Value
causeOf e = case fromException e of
  Just (KappaError ev) -> VCtor (prelG "Fail") [ev]
  Nothing -> case fromException e of
    Just (Interrupt cause) -> VCtor (prelG "Interrupt") [cause]
    Nothing -> case fromException e of
      Just (CauseReraise cause) -> cause
      Nothing ->
        VCtor (prelG "Defect")
          [VCtor (prelG "MkDefectInfo") [VLit (LitStr (T.pack (show e)))]]

-- | Re-raise a §18.1.2 'Cause' value back into host execution: typed 'Fail'
-- becomes a 'KappaError'; every non-typed cause (Interrupt/Defect/composite)
-- is carried verbatim by 'CauseReraise' so it propagates as the same runtime
-- cause (§18.1.4 join, §18.1.6 timeout/race, §18.1.2 unsandbox).
reraiseCauseValue :: Value -> IO a
reraiseCauseValue v = case v of
  VCtor (GName _ "Fail") [ev] -> throwIO (KappaError ev)
  VCtor (GName _ "Interrupt") [cause] -> throwIO (Interrupt cause)
  _ -> throwIO (CauseReraise v)

-- | §18.1.7 fiber-local state. A 'FiberRef' is identified by a counter id;
-- @fiberRefInit@ holds each cell's initial value (the fallback for fibers with
-- no explicit override) and @fiberLocals@ maps each runtime fiber (a GHC
-- ThreadId) to its per-cell overrides. A child inherits a snapshot of the
-- parent's overrides at fork; afterwards the two diverge independently.
{-# NOINLINE fiberRefCounter #-}
fiberRefCounter :: IORef Int
fiberRefCounter = unsafePerformIO (newIORef 0)

{-# NOINLINE fiberRefInit #-}
fiberRefInit :: IORef (Map.Map Int Value)
fiberRefInit = unsafePerformIO (newIORef Map.empty)

{-# NOINLINE fiberLocals #-}
fiberLocals :: IORef (Map.Map ThreadId (Map.Map Int Value))
fiberLocals = unsafePerformIO (newIORef Map.empty)

-- | The current fiber's value for a fiber-local cell: its override if set,
-- else the cell's initial value.
getFiberLocal :: Int -> IO Value
getFiberLocal rid = do
  tid <- myThreadId
  locals <- readIORef fiberLocals
  case Map.lookup tid locals >>= Map.lookup rid of
    Just v -> pure v
    Nothing -> Map.findWithDefault unitV rid <$> readIORef fiberRefInit

-- | Set the current fiber's override for a cell (other cells untouched).
setFiberLocal :: Int -> Value -> IO ()
setFiberLocal rid v = do
  tid <- myThreadId
  modifyIORef' fiberLocals (Map.insertWith Map.union tid (Map.singleton rid v))

-- | Spawn a fiber thread that ALWAYS records its terminal 'Exit' into a fresh
-- MVar, returning the thread id and that cell. The child starts with async
-- exceptions masked and only unmasks inside the 'try' (via 'forkIOWithUnmask'),
-- so an interruption delivered before the handler is installed is still caught
-- and recorded as @Failure (Interrupt …)@ — otherwise the thread could die
-- before filling the cell and a waiter would block forever. The child also
-- inherits a snapshot of the parent's fiber-local overrides (§18.1.7).
spawnExit :: RT -> Value -> IO (ThreadId, MVar Value)
spawnExit rt action = do
  parentTid <- myThreadId
  snap <- Map.findWithDefault Map.empty parentTid <$> readIORef fiberLocals
  mv <- newEmptyMVar
  tid <- forkIOWithUnmask $ \unmask -> do
    childTid <- myThreadId
    modifyIORef' fiberLocals (Map.insert childTid snap)
    r <- try (unmask (runIOValue rt action)) :: IO (Either SomeException Value)
    _ <- tryPutMVar mv (exitOf r)
    pure ()
  pure (tid, mv)

-- | §18.1.4 spawn a cooperative child fiber as a 'VFiber' handle: the ThreadId
-- is the interrupt target, the MVar the await target.
forkFiber :: RT -> Value -> IO Value
forkFiber rt action = uncurry VFiber <$> spawnExit rt action

-- | Deliver a structured interruption to a fiber and block until it has
-- terminated and its finalizers have run (§18.1.4) — by reading its result
-- cell, which 'spawnExit' always fills. The 'yield' first hands the agent to
-- the target so it can reach its interruptible point inside the fork driver's
-- 'try' before the interrupt arrives; combined with the masked setup in
-- 'spawnExit', this guarantees the interrupt is caught and recorded rather than
-- killing a not-yet-started fiber before it can fill its cell.
interruptWait :: ThreadId -> MVar Value -> Value -> IO ()
interruptWait tid mv cause = do
  yield
  throwTo tid (Interrupt cause)
  _ <- readMVar mv
  pure ()

-- | §18.1.8 shut a supervision scope down: interrupt every still-live attached
-- fiber with tag @ScopeShutdown@ and wait until each has terminated. Idempotent
-- — the registry is emptied first, so a repeat shutdown finds nothing.
shutdownScopeReg :: IORef [Value] -> IO ()
shutdownScopeReg reg = do
  fibers <- readIORef reg
  writeIORef reg []
  mapM_ interruptAndWait fibers
  where
    interruptAndWait (VFiber tid mv) = interruptWait tid mv (interruptCause "ScopeShutdown")
    interruptAndWait _ = pure ()

-- | The signed nanosecond magnitude of a (forced) Duration/Instant value
-- (§18.1.6 — both are monotonic nanosecond integers at runtime).
durationNanos :: Value -> Integer
durationNanos (VLit (LitInt n)) = n
durationNanos _ = 0

-- | Convert signed nanoseconds to the microsecond argument 'threadDelay'
-- expects, rounding up so a sub-microsecond positive duration still parks.
nanosToMicros :: Integer -> Int
nanosToMicros ns = fromInteger (max 1 ((ns + 999) `div` 1000))

-- | Whether a (forced) terminal 'Exit' is @Failure (Interrupt cause)@ whose
-- cause carries the @TimedOut@ tag — i.e. the timer beat the computation.
exitTimedOut :: EvalCtx -> Value -> Bool
exitTimedOut ec v = case force ec v of
  VCtor (GName _ "Failure") [c] -> case force ec c of
    VCtor (GName _ "Interrupt") [cause] -> case force ec cause of
      VCtor (GName _ "MkInterruptCause") (tag : _) -> case force ec tag of
        VCtor (GName _ "TimedOut") _ -> True
        _ -> False
      _ -> False
    _ -> False
  _ -> False

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
exitOf (Left e) = VCtor (prelG "Failure") [causeOf e]

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
  -- §18.8/§18.1: the finalizer runs exactly once on EVERY exit path from the
  -- body — normal completion, typed failure, interruption, and defects — then
  -- the original outcome is propagated. (Catches SomeException, not just
  -- KappaError, so a finalizer/release also runs when the body is interrupted.)
  ("finallyIO", [body, fin]) -> do
    r <- try (runIOValue rt body) :: IO (Either SomeException Value)
    _ <- runIOValue rt fin
    case r of
      Right v -> pure v
      Left err -> throwIO err
  ("__runIO", [action]) -> runIOValue rt action
  -- §18.1.4/§18.11: fork spawns a cooperative child fiber (a GHC green thread
  -- on the single OS agent — non-threaded RTS ⇒ no parallelism, weak fairness
  -- from the RTS scheduler). The child runs concurrently; its terminal Exit
  -- (Success v / Failure (Fail e / Interrupt c / Defect …)) is delivered
  -- through an MVar that await reads. A child failure is isolated here (not
  -- propagated to the forking context). fork does NOT run to completion. The
  -- handle (VFiber) carries the child's ThreadId so it can be interrupted.
  -- forkDaemon differs from fork only in structured-scope attachment, which
  -- the single-agent runtime models leniently (§18.1.4).
  ("__forkRun", [action]) -> forkFiber rt action
  ("__forkDaemon", [action]) -> forkFiber rt action
  -- await PARKS the current fiber on the result MVar until the child
  -- terminates (the RTS runs other runnable fibers meanwhile).
  ("__awaitFiber", [VFiber _ mv]) -> readMVar mv
  -- §18.1.4 interruption: deliver a structured InterruptCause to the target
  -- fiber by throwTo. The waiting form blocks until the target has terminated
  -- and all its finalizers have run (readMVar on its result cell); the fork
  -- form returns immediately.
  ("__interruptWait", [cause, VFiber tid mv]) ->
    interruptWait tid mv cause >> pure unitV
  ("__interruptNoWait", [cause, VFiber tid _]) ->
    throwTo tid (Interrupt cause) >> pure unitV
  -- §18.1.5 cede: yield to the scheduler (also an interruption point — GHC
  -- delivers any pending throwTo at the yield).
  ("cede", _) -> yield >> pure unitV
  -- §18.1.2 sandbox: run the action and expose its full terminal Cause in the
  -- typed-error channel — every failure (Fail/Interrupt/Defect) becomes a
  -- typed Fail carrying the Cause value.
  ("sandbox", [action]) -> do
    r <- try (runIOValue rt action)
    case r of
      Right v -> pure v
      Left e -> throwIO (KappaError (causeOf e))
  -- §18.1.2 unsandbox: reverse the exposure — a typed Fail carrying a Cause is
  -- re-raised as that very cause.
  ("unsandbox", [action]) -> do
    r <- try (runIOValue rt action)
    case r of
      Right v -> pure v
      Left (KappaError causeV) -> reraiseCauseValue causeV
  -- §18.1.6 reraise a non-typed runtime cause (used by the typed timeout/race
  -- wrappers when the winning/completed branch ended in interruption/defect).
  ("__reraiseCause", [causeV]) -> reraiseCauseValue causeV
  -- §18.1.6 timeout: race the action against a monotonic timer. A nonpositive
  -- duration fires before the first step (the action is never started). When
  -- the timer wins, the action is interrupted with tag TimedOut and timeout
  -- waits for it to terminate; completion of the action wins ties.
  ("__timeout", [dVal, action]) -> do
    let ns = durationNanos dVal
    if ns <= 0
      then pure (VCtor (prelG "TOTimedOut") [])
      else do
        (tid, mv) <- spawnExit rt action
        timer <- forkIO $ do
          threadDelay (nanosToMicros ns)
          throwTo tid (Interrupt (interruptCause "TimedOut"))
        exitV <- readMVar mv
        killThread timer
        pure $
          if exitTimedOut ec exitV
            then VCtor (prelG "TOTimedOut") []
            else VCtor (prelG "TOExit") [exitV]
  -- §18.1.6 race: run both branches concurrently; the first to terminate
  -- wins, the loser is interrupted with tag RaceLost and race waits for it to
  -- terminate. The left branch wins ties.
  ("__race", [leftIO, rightIO]) -> do
    (ltid, lmv) <- spawnExit rt leftIO
    (rtid, rmv) <- spawnExit rt rightIO
    -- notifier threads report which branch terminated first (they only read
    -- the always-filled result cells, so they cannot deadlock).
    resMV <- newEmptyMVar
    _ <- forkIO (readMVar lmv >>= \ex -> tryPutMVar resMV (True, ex) >> pure ())
    _ <- forkIO (readMVar rmv >>= \ex -> tryPutMVar resMV (False, ex) >> pure ())
    (isLeft, ex) <- readMVar resMV
    if isLeft
      then do
        throwTo rtid (Interrupt (interruptCause "RaceLost"))
        _ <- readMVar rmv
        pure (VCtor (prelG "ROLeft") [ex])
      else do
        throwTo ltid (Interrupt (interruptCause "RaceLost"))
        _ <- readMVar lmv
        pure (VCtor (prelG "RORight") [ex])
  -- §18.1.8 explicit supervision scopes. A scope is a registry of attached
  -- fibers; forkIn attaches, shutdownScope interrupts + drains them, and
  -- withScope brackets a fresh scope with masked shutdown on every exit.
  ("newScope", _) -> VScope <$> newIORef []
  ("forkIn", [VScope reg, action]) -> do
    fib <- forkFiber rt action
    modifyIORef' reg (fib :)
    pure fib
  ("shutdownScope", [VScope reg]) -> shutdownScopeReg reg >> pure unitV
  ("withScope", [useFn]) -> do
    reg <- newIORef []
    r <- try (runIOValue rt (vapp ec useFn Expl (VScope reg))) :: IO (Either SomeException Value)
    shutdownScopeReg reg
    either throwIO pure r
  -- §18.1.8 monitors: a non-destructive observer of a fiber's terminal Exit
  -- (the result cell is read, not consumed, so monitoring is independent of
  -- awaiting). demonitor drops the observation.
  ("monitor", [VFiber _ mv]) -> pure (VMVar mv)
  ("awaitMonitor", [VMVar mv]) -> readMVar mv
  ("demonitor", [_]) -> pure unitV
  -- §18.1.7 fiber-local state.
  ("newFiberRef", [v]) -> do
    rid <- atomicModifyIORef' fiberRefCounter (\n -> (n + 1, n))
    modifyIORef' fiberRefInit (Map.insert rid v)
    pure (VFiberRef rid)
  ("getFiberRef", [VFiberRef rid]) -> getFiberLocal rid
  ("setFiberRef", [VFiberRef rid, v]) -> setFiberLocal rid v >> pure unitV
  -- locallyFiberRef installs a value for the dynamic extent of the body and
  -- restores the previous value on every exit (a masked finalizer).
  ("locallyFiberRef", [VFiberRef rid, v, body]) -> do
    old <- getFiberLocal rid
    setFiberLocal rid v
    r <- try (runIOValue rt body) :: IO (Either SomeException Value)
    setFiberLocal rid old
    either throwIO pure r
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
  -- §18.1.6 sleep parks ONLY the current fiber (interruptible threadDelay on
  -- a non-threaded RTS yields to other runnable fibers — it does not block the
  -- agent; a throwTo wakes it as an interruption point). Nonpositive / past
  -- deadlines return immediately.
  ("sleepFor", [dVal]) -> do
    let ns = durationNanos dVal
    if ns <= 0 then pure unitV else threadDelay (nanosToMicros ns) >> pure unitV
  ("sleepUntil", [tVal]) -> do
    let target = durationNanos tVal
    now <- fromIntegral <$> getMonotonicTimeNSec
    let ns = target - now
    if ns <= 0 then pure unitV else threadDelay (nanosToMicros ns) >> pure unitV
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
