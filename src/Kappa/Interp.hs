{-# LANGUAGE RankNTypes #-}

-- | Runtime interpreter (Spec §32.1: strict, call-by-value,
-- left-to-right evaluation) with the §18.8 do-kernel semantics:
-- completion records, LIFO exit actions run exactly once, loop @else@
-- only on no-break completion, typed IO failures via catch\/finally.
--
-- Note the division of labour with "Kappa.Eval": that module /normalizes/
-- terms for the type checker (pure, compile-time, no side effects); this
-- module actually __runs__ a checked program — it executes @main@, performs
-- real IO, spawns fibers, and drives the do-kernel ('KItem's) to completion.
-- Eval answers "are these two types equal?"; Interp answers "what does this
-- program do?".
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
import Control.Concurrent.MVar (MVar, newEmptyMVar, newMVar, readMVar, tryPutMVar, tryReadMVar, withMVar)
import qualified Control.Concurrent.STM as STM
import Control.Exception (AsyncException (..), Exception, SomeException, fromException, throwIO, try)
import qualified Control.Exception as CE
import Control.Monad (unless, when)
import Data.Array.IO (IOArray)
import qualified Data.Array.IO as IOA
import Data.Bits ((.&.), (.|.), xor)
import Data.IORef
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust)
import GHC.Clock (getMonotonicTimeNSec)
import System.IO.Unsafe (unsafePerformIO)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Kappa.Builtins
import Kappa.AsyncException (throwToAsync)
import Kappa.Core
import Kappa.Eval
import Kappa.Pretty (renderTerm, renderValueShallow)
import System.IO (hFlush, stdout)

data RunResult = RunOk | RunFail Text
  deriving stock (Show)

newtype KappaError = KappaError Value
instance Show KappaError where
  show (KappaError v) = "error: " ++ T.unpack (renderValueShallow v)
instance Exception KappaError

-- | §18.1.13: a transaction attempt that must suspend until shared STM state
-- changes (`retry`/`check False`/`stmAbort`/STM `empty`). Caught by the
-- 'stmAtomically' driver, which discards the attempt journal before parking.
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

atomicReadIORef' :: IORef a -> IO a
atomicReadIORef' ref = atomicModifyIORef' ref $ \x -> (x, x)

atomicModifyIORef_' :: IORef a -> (a -> a) -> IO ()
atomicModifyIORef_' ref f = atomicModifyIORef' ref $ \x -> (f x, ())

-- | Build a structured 'InterruptCause' with the given §18.1.2 tag and no
-- initiating fiber (@by = None@) — the form used by runtime-originated
-- interruption (timeout's @TimedOut@, race's @RaceLost@).
interruptCause :: Text -> Value
interruptCause tag =
  VCtor prelInterruptCause [VCtor (gPrel tag) [], VCtor prelNone []]

-- | The §18.1.2 'Cause' value carried by a host exception that escaped a
-- fiber/sandbox: typed 'Fail', structured 'Interrupt', a faithfully
-- round-tripped re-raised cause, or a 'Defect' for any other host failure.
causeOf :: SomeException -> Value
causeOf e = case fromException e of
  Just (KappaError ev) -> VCtor prelFail [ev]
  Nothing -> case fromException e of
    Just (Interrupt cause) -> VCtor prelInterrupt [cause]
    Nothing -> case fromException e of
      Just (CauseReraise cause) -> cause
      Nothing ->
        -- §28.2 DefectInfo shape: an unclassified host failure is tagged
        -- 'OtherDefect' with its rendered text as the (Some) message.
        VCtor prelDefect
          [ VCtor
              prelDefectInfo
              [ VCtor prelOtherDefect []
              , VCtor prelSome [VLit (LitStr (T.pack (show e)))]
              ]
          ]

interruptCauseOfCause :: Value -> Maybe Value
interruptCauseOfCause = \case
  VCtor g [cause]
    | g == prelInterrupt -> Just cause
  VCtor g [primary, _cleanup]
    | g == prelThen -> interruptCauseOfCause primary
  VCtor g [left, right]
    | g == prelBoth ->
        case interruptCauseOfCause left of
          Just cause -> Just cause
          Nothing -> interruptCauseOfCause right
  _ -> Nothing

interruptCauseOfException :: SomeException -> Maybe Value
interruptCauseOfException e =
  case fromException e of
    Just (Interrupt cause) -> Just cause
    Nothing -> case fromException e of
      Just (CauseReraise cause) -> interruptCauseOfCause cause
      Nothing -> Nothing

-- | Re-raise a §18.1.2 'Cause' value back into host execution: typed 'Fail'
-- becomes a 'KappaError'; every non-typed cause (Interrupt/Defect/composite)
-- is carried verbatim by 'CauseReraise' so it propagates as the same runtime
-- cause (§18.1.4 join, §18.1.6 timeout/race, §18.1.2 unsandbox).
reraiseCauseValue :: Value -> IO a
reraiseCauseValue v = case v of
  VCtor g [ev] | g == prelFail -> throwIO (KappaError ev)
  VCtor g [cause] | g == prelInterrupt -> throwIO (Interrupt cause)
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

-- | §18.1.10 fiber identity. The interpreter keys every per-fiber registry by
-- 'ThreadId'; for a source-visible integer id we assign one lazily on first
-- request (a counter + a 'ThreadId'->'Integer' map). This guarantees the spec's
-- two properties: each fiber gets a unique id for the program run, and the id is
-- STABLE — so @currentFiberId@ (keyed by the running thread) and @fiberId fib@
-- (keyed by the fiber's ThreadId) return the same value for the same fiber. The
-- exact numbering need not match the native runtime's spawn-order ids; only
-- uniqueness + agreement are required (§18.1.10).
{-# NOINLINE fiberIds #-}
fiberIds :: IORef (Map.Map ThreadId Integer)
fiberIds = unsafePerformIO (newIORef Map.empty)

-- | The stable integer id for a fiber's ThreadId, assigning a fresh one on first
-- request. 'atomicModifyIORef'' makes the assign-or-reuse a single atomic step so
-- two fibers racing on the SAME ThreadId can never get distinct ids.
fiberIdOf :: ThreadId -> IO Integer
fiberIdOf tid =
  atomicModifyIORef' fiberIds $ \m -> case Map.lookup tid m of
    Just i -> (m, i)
    Nothing ->
      -- next id = current map size + 1 (ids start at 1, matching the native
      -- runtime's `next_id + 1`); unique because the map only ever grows.
      let i = fromIntegral (Map.size m) + 1
       in (Map.insert tid i m, i)

-- | §18.1.12 / §32.2.5 explicit interruption state. Frames are capabilities,
-- not depth snapshots: each frame has one owner fiber and a stable identity.
-- Restoring suspends only the owner's topmost active frame; stale, repeated,
-- wrong-order, and cross-fiber restores are inert. A child inherits only its
-- parent's effective state as a non-restorable base.
data InterpMaskState
  = MaskInterruptible
  | Masked
  | MaskUninterruptible
  deriving stock (Eq, Ord, Show)

data InterpMaskFrame = InterpMaskFrame
  { imfOwner :: !ThreadId
  , imfState :: !InterpMaskState
  , imfSuspended :: !Bool
  }

data InterpFiberMask = InterpFiberMask
  { ifmBase :: !InterpMaskState
  , ifmFrames :: ![Int]
  }

data InterpMaskRegistry = InterpMaskRegistry
  { imrNextFrame :: !Int
  , imrFibers :: !(Map.Map ThreadId InterpFiberMask)
  , imrFrames :: !(Map.Map Int InterpMaskFrame)
  }

emptyInterpFiberMask :: InterpFiberMask
emptyInterpFiberMask = InterpFiberMask MaskInterruptible []

{-# NOINLINE interpMaskRegistry #-}
interpMaskRegistry :: IORef InterpMaskRegistry
interpMaskRegistry = unsafePerformIO $
  newIORef (InterpMaskRegistry 0 Map.empty Map.empty)

effectiveMaskState :: ThreadId -> InterpMaskRegistry -> InterpMaskState
effectiveMaskState tid registry =
  foldr max (ifmBase fiber) activeStates
  where
    fiber = Map.findWithDefault emptyInterpFiberMask tid (imrFibers registry)
    activeStates =
      [ imfState frame
      | frameId <- ifmFrames fiber
      , Just frame <- [Map.lookup frameId (imrFrames registry)]
      , not (imfSuspended frame)
      ]

currentMaskState :: IO InterpMaskState
currentMaskState = do
  tid <- myThreadId
  effectiveMaskState tid <$> atomicReadIORef' interpMaskRegistry

pushMaskFrame :: InterpMaskState -> IO Int
pushMaskFrame state = do
  tid <- myThreadId
  atomicModifyIORef' interpMaskRegistry $ \registry ->
    let frameId = imrNextFrame registry
        fiber = Map.findWithDefault emptyInterpFiberMask tid (imrFibers registry)
        frame = InterpMaskFrame tid state False
        registry' = registry
          { imrNextFrame = frameId + 1
          , imrFibers = Map.insert tid (fiber {ifmFrames = frameId : ifmFrames fiber})
              (imrFibers registry)
          , imrFrames = Map.insert frameId frame (imrFrames registry)
          }
     in (registry', frameId)

popMaskFrame :: Int -> IO ()
popMaskFrame frameId = do
  tid <- myThreadId
  ok <- atomicModifyIORef' interpMaskRegistry $ \registry ->
    let fiber = Map.findWithDefault emptyInterpFiberMask tid (imrFibers registry)
     in case (ifmFrames fiber, Map.lookup frameId (imrFrames registry)) of
          (top : rest, Just frame)
            | top == frameId && imfOwner frame == tid ->
                let fibers' = Map.insert tid (fiber {ifmFrames = rest}) (imrFibers registry)
                    frames' = Map.delete frameId (imrFrames registry)
                 in (registry {imrFibers = fibers', imrFrames = frames'}, True)
          _ -> (registry, False)
  unless ok $
    throwIO (KappaError (VLit (LitStr "interpreter mask frame stack corruption")))

topmostActiveFrame :: InterpMaskRegistry -> InterpFiberMask -> Maybe Int
topmostActiveFrame registry = go . ifmFrames
  where
    go [] = Nothing
    go (frameId : rest) =
      case Map.lookup frameId (imrFrames registry) of
        Just frame | not (imfSuspended frame) -> Just frameId
        _ -> go rest

suspendMaskFrame :: Int -> IO Bool
suspendMaskFrame frameId = do
  tid <- myThreadId
  atomicModifyIORef' interpMaskRegistry $ \registry ->
    let fiber = Map.findWithDefault emptyInterpFiberMask tid (imrFibers registry)
     in case Map.lookup frameId (imrFrames registry) of
          Just frame
            | imfOwner frame == tid
            , not (imfSuspended frame)
            , topmostActiveFrame registry fiber == Just frameId ->
                let frames' = Map.insert frameId (frame {imfSuspended = True})
                      (imrFrames registry)
                 in (registry {imrFrames = frames'}, True)
          _ -> (registry, False)

reinstateMaskFrame :: Int -> IO ()
reinstateMaskFrame frameId = do
  tid <- myThreadId
  atomicModifyIORef_' interpMaskRegistry $ \registry ->
    case Map.lookup frameId (imrFrames registry) of
      Just frame
        | imfOwner frame == tid && imfSuspended frame ->
            registry
              { imrFrames = Map.insert frameId (frame {imfSuspended = False})
                  (imrFrames registry)
              }
      _ -> registry

withMaskFrame :: InterpMaskState -> IO a -> IO a
withMaskFrame state action = do
  frameId <- pushMaskFrame state
  action `CE.finally` popMaskFrame frameId

withRestoredMaskFrame :: Int -> IO a -> IO a
withRestoredMaskFrame frameId action = do
  suspended <- suspendMaskFrame frameId
  if suspended
    then
      ( do
          state <- currentMaskState
          when (state == MaskInterruptible) $
            interruptCheckpoint ((== MaskInterruptible) <$> currentMaskState)
          action
      ) `CE.finally` reinstateMaskFrame frameId
    else action

registerChildMask :: ThreadId -> InterpMaskState -> IO ()
registerChildMask tid base =
  atomicModifyIORef_' interpMaskRegistry $ \registry ->
    registry
      { imrFibers = Map.insert tid (InterpFiberMask base []) (imrFibers registry)
      }

unregisterFiberMask :: ThreadId -> IO ()
unregisterFiberMask tid =
  atomicModifyIORef_' interpMaskRegistry $ \registry ->
    let fiber = Map.lookup tid (imrFibers registry)
        ownedFrames = maybe [] ifmFrames fiber
     in registry
          { imrFibers = Map.delete tid (imrFibers registry)
          , imrFrames = foldr Map.delete (imrFrames registry) ownedFrames
          }

-- | §18.1.12 / §32.2.5 explicit interruption-point delivery.
--
-- GHC's 'uninterruptibleMask_' / 'mask' correctly DEFER an async exception during
-- an interruptible blocking op (e.g. 'threadDelay'), but they then deliver the held
-- exception at the masked REGION BOUNDARY (when the region is left), which is NOT a
-- Kappa interruption point (§32.2.5: a pending request becomes observable at the
-- next interruption point — a suspension/await/STM-retry/poll — never at a region
-- exit).  Relying on GHC's boundary delivery therefore interrupts a fiber whose
-- whole body was masked, even though there is no interruption point after the exit.
--
-- So the interpreter STOPS relying on GHC boundary delivery and models §32.2.5
-- directly, mirroring the native runtime (rt.c):
--
--   * the fiber body runs fully masked (uninterruptibleMask_ in 'spawnExit'), so
--     GHC never auto-delivers anywhere;
--   * identity-bearing semantic frames determine the effective mask state;
--   * the interrupt primitive RECORDS the cause into 'pendingInterrupt' and an
--     asynchronous host 'throwTo' wakes the target out of a parked point without
--     making @interruptFork@ wait for target acceptance;
--   * an interruption point ('__sleepForNanos', '__awaitFiber', STM-retry park,
--     'cede', the promise/monitor awaits) runs its blocking call through the
--     fiber's stored GHC unmask so the wake lands, then DELIVERS (re-raises) the
--     pending interrupt only when interruptible, and otherwise RE-PARKS (swallows
--     the wake, the flag stays set for the next genuine unmasked point);
--   * 'poll' pierces ordinary masking but is inert under an effective
--     uninterruptible mask.
--
-- This makes whole-body-masked computations drop a pending interrupt (no
-- interruption point after the region exit), while a 'restore'd sub-action stays a
-- real interruption point — exactly the native semantics.

-- | A rank-2 GHC unmask (@forall a. IO a -> IO a@) boxed so it can live in a Map.
newtype Unmask = Unmask (forall a. IO a -> IO a)

data PendingInterruptState = PendingInterruptState
  { pisCause :: !Value
  , pisHostWakeAbsorbed :: !Bool
  }

{-# NOINLINE pendingInterrupt #-}
pendingInterrupt :: IORef (Map.Map ThreadId PendingInterruptState)
pendingInterrupt = unsafePerformIO (newIORef Map.empty)

{-# NOINLINE fiberUnmask #-}
fiberUnmask :: IORef (Map.Map ThreadId Unmask)
fiberUnmask = unsafePerformIO (newIORef Map.empty)

-- | Record a pending interrupt cause for @tid@ (first request wins, §18.1.12).
recordPending :: ThreadId -> Value -> IO ()
recordPending tid cause =
  atomicModifyIORef_' pendingInterrupt $ \m ->
    if Map.member tid m
      then m
      else Map.insert tid (PendingInterruptState cause False) m

-- | Record that the target has accepted the host wake. This distinction avoids
-- synchronously re-raising the logical request while its matching 'throwTo' is
-- still in flight, which would otherwise permit duplicate late delivery.
recordAbsorbedInterrupt :: ThreadId -> Value -> IO ()
recordAbsorbedInterrupt tid cause =
  atomicModifyIORef_' pendingInterrupt $ \m ->
    case Map.lookup tid m of
      Just pending ->
        Map.insert tid (pending {pisHostWakeAbsorbed = True}) m
      Nothing ->
        Map.insert tid (PendingInterruptState cause True) m

-- | This fiber's pending interrupt cause, if any.
takeAbsorbedPendingWhen :: IO Bool -> IO (Maybe Value)
takeAbsorbedPendingWhen allowed = do
  tid <- myThreadId
  canDeliver <- allowed
  if not canDeliver
    then pure Nothing
    else
      atomicModifyIORef' pendingInterrupt $ \m ->
        case Map.lookup tid m of
          Nothing -> (m, Nothing)
          Just pending
            | pisHostWakeAbsorbed pending ->
                (Map.delete tid m, Just (pisCause pending))
          Just _ -> (m, Nothing)

pendingRequestState :: ThreadId -> IO (Maybe PendingInterruptState)
pendingRequestState tid = Map.lookup tid <$> atomicReadIORef' pendingInterrupt

-- | §32.2.6 loop-backedge safe point.  A forked fiber runs FULLY MASKED at the
-- GHC level (spawnExit: uninterruptibleMask_), so a 'throwTo' interrupt lands
-- only at an 'interruptPoint' — and a tight `while`/`for` loop with NO
-- await/sleep/cede/poll inside has none, so it would run to completion ignoring a
-- pending interrupt (the §32.2.6 interruption-observation gap, mirroring the
-- native backends' in-place CK loop / native scalar loop before fix SP).  Calling
-- this at each loop back-edge makes the interrupt observable there: if one is
-- pending AND the fiber is interruptible it is delivered by
-- re-raising it, exactly like the native KK_LOOP / krt2_safepoint back-edge.
-- Keeps interp == native for "a tight loop IS interrupted" / "a masked loop is
-- NOT interrupted mid-loop".
--
-- IMPORTANT (async-exception discipline): the request side ('interruptWait' /
-- '__interruptNoWait') does BOTH recordPending AND request a throwTo wake.  The wake is an
-- ASYNC exception deferred by the fiber's uninterruptibleMask_.  If we merely
-- 'throwIO' the recorded cause here, that deferred async throwTo stays in flight
-- and later fires at the fiber's next interruptible op (e.g. the tryPutMVar in
-- spawnExit, OUTSIDE the mask) — AFTER the exit handler — so it escapes uncaught
-- and the fiber's result MVar is never filled (a waiter then blocks forever).
-- 'interruptPoint' already handles this exactly: it opens the fiber's unmask
-- window so the in-flight async throwTo is delivered (caught as Left), records
-- it, and re-raises once when unmasked (or re-parks when masked — which for a
-- non-blocking checkpoint just means returning Unit, suppression intact).
-- 'CE.allowInterrupt' makes that unmasked window a real host delivery point
-- even when there is no blocking operation at the loop back-edge.  So a loop
-- safe point absorbs the async throwTo and delivers iff unmasked, never leaving
-- a dangling async exception.
loopSafepoint :: IO ()
loopSafepoint =
  interruptCheckpoint ((== MaskInterruptible) <$> currentMaskState)

data SuppressedInterruptPoint
  = RetrySuppressedPoint
  | ReturnFromSuppressedPoint

-- | A genuine interruption point: run the (parking) blocking @block@ through this
-- fiber's GHC unmask so a 'throwTo' wake can land, then decide per §32.2.5:
--
--   * interruptible => DELIVER: re-raise the pending interrupt;
--   * masked        => RE-PARK: swallow the wake and retry @block@
--     (the flag stays set, so a later unmasked point delivers).  This is the
--     native "masked parked sleep re-parks, does not fail/shorten" behavior.
--
-- A point with no fiber unmask registered (the main fiber, before any fork) simply
-- runs @block@ unmasked-as-is and checks the flag after.
interruptPoint :: IO Value -> IO Value
interruptPoint =
  interruptPointWhen RetrySuppressedPoint
    ((== MaskInterruptible) <$> currentMaskState)

interruptCheckpoint :: IO Bool -> IO ()
interruptCheckpoint allowed =
  () <$ interruptPointWhen ReturnFromSuppressedPoint allowed
    (CE.allowInterrupt >> pure unitV)

interruptPointWhen
  :: SuppressedInterruptPoint
  -> IO Bool
  -> IO Value
  -> IO Value
interruptPointWhen suppressed allowed block = do
  tid <- myThreadId
  um <- Map.lookup tid <$> atomicReadIORef' fiberUnmask
  case um of
    Nothing -> block >>= finishWithoutHost tid
    Just (Unmask unmask) -> go unmask
  where
    go unmask = do
      r <- try (unmask block) :: IO (Either Interrupt Value)
      case r of
        Right v -> finish unmask v
        Left (Interrupt cause) -> do
          tid <- myThreadId
          recordAbsorbedInterrupt tid cause
          mc <- takeAbsorbedPendingWhen allowed
          case mc of
            Just pendingCause -> throwIO (Interrupt pendingCause)
            Nothing -> case suppressed of
              RetrySuppressedPoint -> go unmask
              ReturnFromSuppressedPoint -> pure unitV

    finish unmask value = do
      canDeliver <- allowed
      if not canDeliver
        then pure value
        else do
          tid <- myThreadId
          pending <- pendingRequestState tid
          case pending of
            Nothing -> pure value
            Just request
              | pisHostWakeAbsorbed request -> do
                  atomicModifyIORef_' pendingInterrupt (Map.delete tid)
                  throwIO (Interrupt (pisCause request))
              | otherwise -> absorbRequestedWake unmask value

    -- The request side records before calling 'throwTo'. If this fiber observes
    -- that logical request first, wait until the matching host wake has actually
    -- been accepted before re-raising it synchronously. This prevents a second,
    -- late async delivery after the fiber has already published its Exit.
    absorbRequestedWake unmask value = do
      r <- try (unmask (yield >> CE.allowInterrupt >> pure unitV))
        :: IO (Either Interrupt Value)
      case r of
        Left (Interrupt cause) -> do
          tid <- myThreadId
          recordAbsorbedInterrupt tid cause
          finish unmask value
        Right _ -> do
          tid <- myThreadId
          pending <- pendingRequestState tid
          case pending of
            Just request | not (pisHostWakeAbsorbed request) ->
              absorbRequestedWake unmask value
            _ -> finish unmask value

    finishWithoutHost tid value = do
      mc <- takeAbsorbedPendingWhen allowed
      case mc of
        Just cause -> throwIO (Interrupt cause)
        Nothing -> do
          pending <- pendingRequestState tid
          case pending of
            Just request | pisHostWakeAbsorbed request ->
              throwIO (Interrupt (pisCause request))
            _ -> pure value

-- | The current fiber's value for a fiber-local cell: its override if set,
-- else the cell's initial value.
getFiberLocal :: Int -> IO Value
getFiberLocal rid = do
  tid <- myThreadId
  locals <- atomicReadIORef' fiberLocals
  case Map.lookup tid locals >>= Map.lookup rid of
    Just v -> pure v
    Nothing -> Map.findWithDefault unitV rid <$> atomicReadIORef' fiberRefInit

-- | Set the current fiber's override for a cell (other cells untouched).
setFiberLocal :: Int -> Value -> IO ()
setFiberLocal rid v = do
  tid <- myThreadId
  atomicModifyIORef_' fiberLocals (Map.insertWith Map.union tid (Map.singleton rid v))

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
  snap <- Map.findWithDefault Map.empty parentTid <$> atomicReadIORef' fiberLocals
  inheritedMask <- currentMaskState
  mv <- newEmptyMVar
  acknowledged <- newIORef False
  atomicModifyIORef_' (rtFiberObservations rt) ((mv, acknowledged) :)
  ready <- newEmptyMVar
  -- §32.2.5 interp fix: the child runs FULLY MASKED (uninterruptibleMask_), so GHC
  -- never auto-delivers a throwTo at any point — least of all at a masked region's
  -- exit boundary.  Delivery happens ONLY at explicit interruption points
  -- ('interruptPoint' / 'poll'), which open an interruptible window via the stored
  -- 'unmask' (forkIOWithUnmask's restore-to-interruptible).  This makes the
  -- interpreter the faithful oracle for the native runtime's delivery gate.
  tid <- forkIOWithUnmask $ \unmask -> do
    _ <-
      try
        ( CE.uninterruptibleMask_ $ do
            childTid <- myThreadId
            atomicModifyIORef_' (rtFiberLabels rt) (Map.delete childTid)
            atomicModifyIORef_' fiberLocals (Map.insert childTid snap)
            atomicModifyIORef_' fiberUnmask (Map.insert childTid (Unmask unmask))
            registerChildMask childTid inheritedMask
            -- Do not return a source-visible Fiber until the child is registered
            -- and inside the protected driver. A parent-side cede is only a yield,
            -- not a guarantee that the child has reached its handler.
            _ <- tryPutMVar ready ()
            r <- try (runIOValue rt action) :: IO (Either SomeException Value)
            let terminalExit = exitOf r
                -- Once the terminal Exit has been determined, publication to the
                -- result cell is no longer an interruption point. A redundant async
                -- Interrupt can still be in flight from the request side; absorb it
                -- only after the MVar is definitely filled, otherwise awaiters can
                -- block forever.
                publish = do
                  alreadyPublished <- isJust <$> tryReadMVar mv
                  unless alreadyPublished $ do
                    pr <-
                      try
                        ( CE.uninterruptibleMask_ $ do
                            -- per-fiber interruption state is keyed by ThreadId; drop
                            -- it as the fiber ends (ThreadIds can be reused, so a stale
                            -- entry would mis-gate a future fiber).
                            atomicModifyIORef_' fiberUnmask (Map.delete childTid)
                            unregisterFiberMask childTid
                            atomicModifyIORef_' pendingInterrupt (Map.delete childTid)
                            atomicModifyIORef_' (rtFiberLabels rt) (Map.delete childTid)
                            _ <- tryPutMVar mv terminalExit
                            pure ()
                        ) ::
                        IO (Either Interrupt ())
                    case pr of
                      Right () -> pure ()
                      Left _ -> publish
            publish
        ) ::
        IO (Either Interrupt ())
    pure ()
  _ <- readMVar ready
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
  -- §32.2.5: record the pending cause (so a masked target re-parks but keeps the
  -- request) BEFORE the throwTo wake; then block on the result cell until the
  -- target terminates and its finalizers have run.
  recordPending tid cause
  throwTo tid (Interrupt cause)
  _ <- readMVar mv
  pure ()

-- | Mark a terminal fiber observation as acknowledged (§32.2.4). The result
-- MVar is the stable interpreter identity shared by Fiber and Monitor handles.
acknowledgeFiber :: RT -> MVar Value -> IO ()
acknowledgeFiber rt mv = do
  observations <- atomicReadIORef' (rtFiberObservations rt)
  mapM_ (`writeIORef` True) [ack | (cell, ack) <- observations, cell == mv]

-- | §18.1.8 / §32.2.4 shut a supervision scope down. Attached fibers are
-- drained in creation order. Unacknowledged typed failures and defects become
-- UnhandledChildFailure defects; mandatory ScopeShutdown interruptions do not.
shutdownScopeReg :: RT -> IORef [Value] -> IO ()
shutdownScopeReg rt reg = do
  fibers <- atomicModifyIORef' reg $ \fibers0 -> ([], fibers0)
  causes <- mapM finishFiber (reverse fibers)
  case foldr combine Nothing causes of
    Nothing -> pure ()
    Just cause -> throwIO (CauseReraise cause)
  where
    combine Nothing rest = rest
    combine (Just cause) Nothing = Just cause
    combine (Just cause) (Just rest) = Just (VCtor prelBoth [cause, rest])

    finishFiber (VFiber tid mv) = do
      completed <- tryReadMVar mv
      terminal <- case completed of
        Just exit -> pure exit
        Nothing -> interruptWait tid mv (interruptCause "ScopeShutdown") >> readMVar mv
      acknowledged <- fiberAcknowledged mv
      pure $ if acknowledged then Nothing else unhandledCause terminal
    finishFiber _ = pure Nothing

    fiberAcknowledged mv = do
      observations <- atomicReadIORef' (rtFiberObservations rt)
      or <$> mapM readIORef [ack | (cell, ack) <- observations, cell == mv]

    unhandledCause (VCtor exitG [VCtor causeG [_]])
      | exitG == prelFailure
      , causeG == prelFail || causeG == prelDefect =
          Just $ VCtor prelDefect
            [ VCtor prelDefectInfo
                [ VCtor prelUnhandledChildFailure []
                , VCtor prelSome [VLit (LitStr "attached child exit was not acknowledged")]
                ]
            ]
    unhandledCause _ = Nothing

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
  VCtor exitG [c] | exitG == prelFailure -> case force ec c of
    VCtor causeG [cause] | causeG == prelInterrupt -> case force ec cause of
      VCtor interruptG (tag : _) | interruptG == prelInterruptCause -> case force ec tag of
        VCtor tagG _ | tagG == prelTimedOut -> True
        _ -> False
      _ -> False
    _ -> False
  _ -> False

data StmJournal = StmJournal
  { sjWrites :: ![(STM.TVar Value, Value)]
  }

emptyStmJournal :: StmJournal
emptyStmJournal = StmJournal []

journalLookup :: STM.TVar Value -> StmJournal -> Maybe Value
journalLookup tv journal = lookup tv (sjWrites journal)

journalWrite :: STM.TVar Value -> Value -> StmJournal -> StmJournal
journalWrite tv value journal =
  journal {sjWrites = (tv, value) : filter ((/= tv) . fst) (sjWrites journal)}

-- | §18.8.2: a fiber's terminal Exit from its run result — Success on normal
-- completion, Failure (Fail e) for a raised Kappa error (isolated from the
-- parent), Failure (Defect …) for any other host exception.
exitOf :: Either SomeException Value -> Value
exitOf (Right v) = VCtor prelSuccess [v]
exitOf (Left e) = VCtor prelFailure [causeOf e]

-- | §18.1.13 interpreter transaction driver. Each attempt runs against a
-- private write journal while holding the per-run serialization lock. Success
-- publishes the complete journal in one GHC STM commit; retry discards it and
-- parks until another committed transaction advances the version.
stmAtomically :: RT -> Value -> IO Value
stmAtomically rt action = loop
  where
    loop = do
      attempt <- withMVar (rtStmLock rt) $ \_ -> do
        v0 <- STM.readTVarIO (rtStmVersion rt)
        journal <- newIORef emptyStmJournal
        r <- try (runIOValue (rt {rtStmJournal = Just journal}) action)
        case r of
          Right val -> do
            writes <- sjWrites <$> readIORef journal
            unless (null writes) . STM.atomically $ do
              mapM_ (uncurry STM.writeTVar) (reverse writes)
              STM.modifyTVar' (rtStmVersion rt) (+ 1)
            pure (Right val)
          Left RetrySignal -> pure (Left v0)
      case attempt of
        Right val -> pure val
        Left v0 -> do
          -- §32.2.5 STM-retry park is an interruption point: block on the STM
          -- write-version advancing, but deliver a pending interrupt (when
          -- unmasked) / re-park (when masked) via interruptPoint.
          _ <- interruptPoint
                 (STM.atomically (do v <- STM.readTVar (rtStmVersion rt); STM.check (v /= v0)) >> pure unitV)
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
  , rtStmLock :: !(MVar ())
  , rtStmVersion :: !(STM.TVar Int)
  , rtStmJournal :: !(Maybe (IORef StmJournal))
  , rtFiberLabels :: !(IORef (Map.Map ThreadId Value))
  , rtFiberObservations :: !(IORef [(MVar Value, IORef Bool)])
  }

newRT :: EvalCtx -> (Text -> IO ()) -> IO RT
newRT ec emit = do
  stmLock <- newMVar ()
  stmVersion <- STM.newTVarIO 0
  labels <- newIORef Map.empty
  observations <- newIORef []
  pure RT
    { rtEC = ec
    , rtEmit = emit
    , rtStmLock = stmLock
    , rtStmVersion = stmVersion
    , rtStmJournal = Nothing
    , rtFiberLabels = labels
    , rtFiberObservations = observations
    }

unitV :: Value
unitV = VCtor prelUnit []

-- | Run @main@ (an IO computation) writing to real stdout.
runMain :: Globals -> MetaState -> GName -> IO RunResult
runMain globals metas mainG = do
  rt <- newRT (EvalCtx globals metas True mempty) (\t -> TIO.putStr t >> hFlush stdout)
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
  rt <- newRT (EvalCtx globals metas True mempty) (\t -> atomicModifyIORef_' buf (t :))
  (r, mv) <- runMainRT rt mainG
  out <- T.concat . reverse <$> atomicReadIORef' buf
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

-- | Evaluate a term. Monadic splices (§18.3.1) are elaborated into ordinary
-- do-binds before runtime, so interpretation never performs value-position IO
-- extraction while evaluating a pure term. Runtime pure evaluation is still an
-- implementation-defined §32.2.6 safe-point region: outside Kappa masks, a
-- pending fiber interruption may abort long-running pure recursion just as the
-- native backends' scalar-loop safepoints do.
evalK :: RT -> Env -> Term -> IO Value
evalK rt env t =
  interruptPoint (CE.evaluate (force (rtEC rt) (eval (rtEC rt) env t)))

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
      appendCleanup primary cleanup = Just $ case primary of
        Nothing -> cleanup
        Just p ->
          CE.toException (CauseReraise (VCtor prelThen [causeOf p, causeOf cleanup]))
      runExitsFrom primary = do
        exits <- atomicModifyIORef' exitsRef $ \exits0 -> ([], exits0)
        withMaskFrame Masked (loopExits primary exits)
        where
          loopExits acc [] = pure acc
          loopExits acc (exitAction : more) = do
            r <- try exitAction :: IO (Either SomeException ())
            loopExits (either (appendCleanup acc) (const acc) r) more
      runExits = do
        mErr <- runExitsFrom Nothing
        maybe (pure ()) throwIO mErr
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
        KBind _ pat t _ -> do
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
        KVarItem _ _ actT _ -> do
          ref <- runIOValue rt =<< evalK rt env actT
          go (ref : env) rest
        KAssign _ _ _ actT _ -> do
          _ <- runIOValue rt =<< evalK rt env actT
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
          atomicModifyIORef_' target ((() <$ (runIOValue rt =<< evalK rt env t)) :)
          go env rest
        KWhile ml cond body mels -> loopOut =<< whileLoop env ml cond body mels
        KFor ml pat src body mels -> loopOut =<< forLoop env ml pat src body mels
        KIf alts mels -> do
          r <- pickIf env alts mels
          case r of
            CplNormal _ -> go env rest
            other -> leave other
        -- §19.5/§18.8.3: acquire the owned resource MASKED (uninterruptible, so
        -- a born-interrupted fiber cannot land its interrupt between `acquire`
        -- returning and the release being installed — mirroring `bracketM`'s
        -- masked acquire-and-register region, §18.1.12), bind `pat` (borrowed)
        -- for the rest of the scope, and attach `release resource` so it runs
        -- exactly once on EVERY exit path — normal completion, abrupt control,
        -- typed failure, AND interruption. The normal/abrupt path runs it LIFO
        -- with `defer`s via the exit queue. A done-flag keeps it exactly-once
        -- across both normal exit and the scope-level exception drain below
        -- (§18.7). Unlike `defer`, this owns the quantity-`1` resource directly
        -- (it is not a source rewrite to `defer`, §19.5).
        KUsing pat acquireT releaseT -> do
          -- §32.2.5: raise the EXPLICIT mask depth for acquire (an interruption
          -- point inside it is suppressed), mirroring bracketM's masked acquire.
          resource <- withMaskFrame Masked (runIOValue rt =<< evalK rt env acquireT)
          releaseFn <- evalK rt env releaseT
          releasedRef <- newIORef False
          let release = do
                first <- atomicModifyIORef' releasedRef $ \done -> (True, not done)
                when first $ do
                  () <$ withMaskFrame Masked (runIOValue rt (vapp ec releaseFn Expl resource))
          atomicModifyIORef_' exitsRef (release :)
          bindOrDie pat resource $ \bs ->
            go (reverse bs ++ env) rest
        -- §18.8.3.1: a transparent nested do-scope. It runs as a child scope
        -- (its own exit-action frame and label) sharing the current label
        -- registry @reg@ — so its own `defer` runs at its exit while
        -- `defer@outerLabel` still reaches the enclosing frame — but any abrupt
        -- completion (break/continue/return targeting an enclosing construct)
        -- propagates outward through this scope's own exit unwinding.
        KSubDo subLbl subItems -> do
          r <- runScope rt reg subLbl env subItems
          case r of
            CplNormal x -> if null rest then leave (CplNormal x) else go env rest
            other -> leave other
        where
          loopOut r = case r of
            CplNormal _ -> go env rest
            other -> leave other
          bindOrDie pat x k = case matchPat ec pat x of
            Just bs -> k bs
            Nothing -> leave =<< throwIO (KappaError (VLit (LitStr "irrefutable binding failed at runtime")))

      whileLoop env ml cond body mels = loop
        where
          -- §32.2.6: a safe point at the loop back-edge — observe a pending
          -- interrupt here so a tight non-ceding loop is interruptible (interp ==
          -- native).  Masked => no-op (suppression holds).
          evalCond = case cond of
            KCondPure t -> evalK rt env t
            KCondAction t -> runIOValue rt =<< evalK rt env t

          loop = loopSafepoint >> (asBool <$> evalCond) >>= \cv -> case cv of
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
          -- §32.2.6 loop-backedge safe point (see whileLoop): observe a pending
          -- interrupt before each element so a long `for` is interruptible too.
          loop (x : xs) = loopSafepoint >> case matchPat ec pat x of
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
        VCtor g [] | g == prelTrue -> Just True
        VCtor g [] | g == prelFalse -> Just False
        _ -> Nothing

      listElems x = case force ec x of
        VCtor g [h, t] | g == prelCons -> h : listElems t
        _ -> []

  r <- try (go env0 items0) :: IO (Either SomeException Completion)
  case r of
    Right c -> pure c
    Left err -> do
      mErr <- runExitsFrom (Just err)
      throwIO (fromMaybe err mErr)

-- ── IO primitives ────────────────────────────────────────────────────

runPrimIO :: RT -> Text -> [Value] -> IO Value
runPrimIO rt p rawArgs =
  runPrimIO' rt p (forceArgs rawArgs)
  where
    ec = rtEC rt
    forceArgs = \case
      [] -> []
      a : as ->
        let a' = force ec a
         in a' `seq` a' : forceArgs as

runMaskPrimitive :: RT -> InterpMaskState -> Value -> IO Value
runMaskPrimitive rt state body = do
  frameId <- pushMaskFrame state
  let restore = VPrim "__restore" [VLit (LitInt (fromIntegral frameId))]
  runIOValue rt (vapp (rtEC rt) body Expl restore)
    `CE.finally` popMaskFrame frameId

runPrimIO' :: RT -> Text -> [Value] -> IO Value
runPrimIO' rt p args = case (p, args) of
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
    _ <- withMaskFrame Masked (runIOValue rt fin)
    case r of
      Right v -> pure v
      Left err -> throwIO err
  -- §18.1.4 onExit: like finallyIO, but the handler RECEIVES the body's
  -- reconstructed terminal 'Exit' (Success v on normal completion; Failure
  -- (Fail e / Interrupt c / Defect …) on the failing paths). Runs on EVERY exit;
  -- the body's outcome is preserved afterward. The oracle for the runtime's
  -- OP_ONEXIT_FIN reason-carrying finalizer.
  ("onExit", [body, handler]) -> do
    r <- try (runIOValue rt body) :: IO (Either SomeException Value)
    _ <- withMaskFrame Masked (runIOValue rt (vapp ec handler Expl (exitOf r)))
    either throwIO pure r
  -- §18.1.4 onInterrupt: the handler runs ONLY when the body exits via
  -- interruption, receiving the 'InterruptCause'. Other exits (normal, typed
  -- failure, defect) skip the handler. The oracle for OP_ONINT_FIN.
  ("onInterrupt", [body, handler]) -> do
    r <- try (runIOValue rt body) :: IO (Either SomeException Value)
    case r of
      Left e | Just cause <- interruptCauseOfException e ->
        withMaskFrame Masked (runIOValue rt (vapp ec handler Expl cause)) >> throwIO e
      _ -> either throwIO pure r
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
  ("__awaitFiber", [VFiber _ mv]) -> do
    terminal <- interruptPoint (readMVar mv)
    acknowledgeFiber rt mv
    pure terminal
  -- §18.1.4 interruption: deliver a structured InterruptCause to the target
  -- fiber by throwTo. The waiting form blocks until the target has terminated
  -- and all its finalizers have run (readMVar on its result cell); the fork
  -- form returns immediately.
  ("__interruptWait", [cause, VFiber tid mv]) ->
    interruptWait tid mv cause >> pure unitV
  ("__interruptNoWait", [cause, VFiber tid _]) -> do
    -- §32.2.5: RECORD the pending cause on the target, then launch a non-blocking
    -- host wake. The target's interruptPoint decides whether
    -- to deliver (unmasked) or re-park (masked).  Recording first means a wake that
    -- races the target into a park still finds the flag at the next point.
    recordPending tid cause
    throwToAsync tid (Interrupt cause) >> pure unitV
  -- Same as __interruptNoWait, only differently typed (free result channel); used
  -- by `disconnect`'s onInterrupt finalizer (PRIMITIVES #5).
  ("__interruptForkAny", [cause, VFiber tid _]) -> do
    recordPending tid cause
    throwToAsync tid (Interrupt cause) >> pure unitV
  -- §18.1.5 cede: yield to the scheduler (also an interruption point — GHC
  -- delivers any pending throwTo at the yield).
  -- §18.1.5 cede yields to the scheduler and is an interruption point: after the
  -- yield, deliver a pending interrupt if this fiber is unmasked (else keep it
  -- pending — cede does not re-park).
  ("cede", _) ->
    interruptPointWhen ReturnFromSuppressedPoint
      ((== MaskInterruptible) <$> currentMaskState)
      (yield >> CE.allowInterrupt >> pure unitV)
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
      then pure (VCtor prelTOTimedOut [])
      else do
        (tid, mv) <- spawnExit rt action
        timer <- forkIO $ do
          threadDelay (nanosToMicros ns)
          throwTo tid (Interrupt (interruptCause "TimedOut"))
        exitV <- readMVar mv
        killThread timer
        pure $
          if exitTimedOut ec exitV
            then VCtor prelTOTimedOut []
            else VCtor prelTOExit [exitV]
  -- §18.1.6 race: run both branches concurrently; the first to terminate
  -- wins, the loser is interrupted with tag RaceLost and race waits for it to
  -- terminate. The left branch wins ties. An already-complete left action is
  -- observable before either scheduler agent runs, so resolve it directly
  -- while still starting and draining the right branch. This removes host
  -- thread scheduling from the canonical @race (ioPure a) (ioPure b)@ tie.
  ("__race", [VPrim "ioPure" [leftValue], rightIO]) -> do
    (rtid, rmv) <- spawnExit rt rightIO
    interruptWait rtid rmv (interruptCause "RaceLost")
    pure (VCtor prelROLeft [VCtor prelSuccess [leftValue]])
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
        pure (VCtor prelROLeft [ex])
      else do
        throwTo ltid (Interrupt (interruptCause "RaceLost"))
        _ <- readMVar lmv
        pure (VCtor prelRORight [ex])
  -- §18.1.8 explicit supervision scopes. A scope is a registry of attached
  -- fibers; forkIn attaches, shutdownScope interrupts + drains them, and
  -- withScope brackets a fresh scope with masked shutdown on every exit.
  ("newScope", _) -> VScope <$> newIORef []
  ("forkIn", [VScope reg, action]) -> do
    fib <- forkFiber rt action
    atomicModifyIORef_' reg (fib :)
    pure fib
  ("shutdownScope", [VScope reg]) -> shutdownScopeReg rt reg >> pure unitV
  ("withScope", [useFn]) -> do
    reg <- newIORef []
    body <- try (runIOValue rt (vapp ec useFn Expl (VScope reg))) :: IO (Either SomeException Value)
    cleanup <- try (withMaskFrame Masked (shutdownScopeReg rt reg)) :: IO (Either SomeException ())
    case (body, cleanup) of
      (Right value, Right ()) -> pure value
      (Left primary, Right ()) -> throwIO primary
      (Right _, Left finalizer) -> throwIO finalizer
      (Left primary, Left finalizer) ->
        throwIO (CauseReraise (VCtor prelThen [causeOf primary, causeOf finalizer]))
  -- §18.1.12 interruption masking. The host thread remains physically masked;
  -- these semantic frames decide where explicit interruption points deliver.
  ("uninterruptible", [body]) ->
    withMaskFrame MaskUninterruptible (runIOValue rt body)
  -- `poll` pierces ordinary masking, but is inert while the effective state is
  -- uninterruptible (§18.1.12).
  ("poll", _) ->
    interruptPointWhen ReturnFromSuppressedPoint
      ((/= MaskUninterruptible) <$> currentMaskState)
      (CE.allowInterrupt >> pure unitV)
  ("__mask", [f]) -> runMaskPrimitive rt Masked f
  ("__uninterruptibleMask", [f]) ->
    runMaskPrimitive rt MaskUninterruptible f
  -- A restore capability names its exact frame. Invalid/stale/repeated,
  -- wrong-order, and cross-fiber uses execute the action under the current state.
  ("__restore", [VLit (LitInt rawFrameId), act]) ->
    withRestoredMaskFrame (fromInteger rawFrameId) (runIOValue rt act)
  -- §18.1.12 rank-2 adapter `__restoreAt raw act` (what the surface `mask` hands
  -- its body, see Prelude `__restoreAt`): forward `act` to the captured raw
  -- restore. The mask primitive captured the exact frame identity, while the
  -- elaborator COERCES
  -- it to the rank-2 type `forall y. IO e y -> IO e y` — i.e. `\{y} -> __restore`
  -- — so `raw` carries a LEADING ERASED type binder. Peel it with a type
  -- placeholder (`y` is RuntimeErased, §31.2), then apply the action and run
  -- (rebuilding `VPrim "__restore" [frame, act]`, which the `__restore` case above
  -- authenticates). This mirrors the native lowering
  -- (a bare `kapp(raw, act)`, where the kunit type slot was already absorbed by
  -- the wrapper), keeping interp == C == LLVM.
  ("__restoreAt", [raw, act]) ->
    runIOValue rt (vapp ec (vapp ec raw Impl (VSort LZero)) Expl act)
  -- §18.1.11 source-level blocking bridge. The interpreter runs on GHC green
  -- threads, so it has no scheduler-worker monopolization to avoid; executing
  -- the body directly is the sequential oracle for success/failure/interruption.
  ("blocking", [body]) -> runIOValue rt body
  -- §18.1.8 monitors: a non-destructive observer of a fiber's terminal Exit
  -- (the result cell is read, not consumed, so monitoring is independent of
  -- awaiting). demonitor drops the observation.
  ("monitor", [VFiber _ mv]) -> pure (VMVar mv)
  ("awaitMonitor", [VMVar mv]) -> do
    terminal <- interruptPoint (readMVar mv)
    acknowledgeFiber rt mv
    pure terminal
  ("demonitor", [_]) -> pure unitV
  -- §18.1.7 fiber-local state.
  ("newFiberRef", [v]) -> do
    rid <- atomicModifyIORef' fiberRefCounter (\n -> (n + 1, n))
    atomicModifyIORef_' fiberRefInit (Map.insert rid v)
    pure (VFiberRef rid)
  ("getFiberRef", [VFiberRef rid]) -> getFiberLocal rid
  ("setFiberRef", [VFiberRef rid, v]) -> setFiberLocal rid v >> pure unitV
  -- §18.1.7 modifyFiberRef: atomic get-apply-set on the current fiber's cell,
  -- returning the NEW value. A FiberRef is per-fiber, so the read-modify-write
  -- is trivially atomic on the single agent. The oracle for OP_MODIFY_FIBER_REF.
  ("modifyFiberRef", [VFiberRef rid, f]) -> do
    old <- getFiberLocal rid
    let new = force ec (vapp ec f Expl old)  -- f : a -> a is pure (matches runtime's eager kapp)
    setFiberLocal rid new
    pure new
  -- locallyFiberRef installs a value for the dynamic extent of the body and
  -- restores the previous value on every exit (a masked finalizer).
  ("locallyFiberRef", [VFiberRef rid, v, body]) -> do
    old <- getFiberLocal rid
    setFiberLocal rid v
    r <- try (runIOValue rt body) :: IO (Either SomeException Value)
    withMaskFrame Masked (setFiberLocal rid old)
    either throwIO pure r
  -- §18.1.13 STM: TVar reads and writes inside an attempt consult its private
  -- journal. The outer atomically driver commits or discards the whole journal.
  ("newTVar", [v]) -> VTVar <$> STM.newTVarIO v
  ("readTVar", [VTVar tv]) -> case rtStmJournal rt of
    Just journalRef -> do
      journal <- readIORef journalRef
      maybe (STM.readTVarIO tv) pure (journalLookup tv journal)
    Nothing -> throwIO . KappaError . VLit . LitStr $ "readTVar escaped atomically"
  ("writeTVar", [VTVar tv, v]) -> case rtStmJournal rt of
    Just journalRef -> atomicModifyIORef_' journalRef (journalWrite tv v) >> pure unitV
    Nothing -> throwIO . KappaError . VLit . LitStr $ "writeTVar escaped atomically"
  ("atomically", [action]) -> stmAtomically rt action
  ("check", [VCtor g []]) | g == prelTrue -> pure unitV
  ("check", [VCtor g []]) | g == prelFalse -> throwIO RetrySignal
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
    (\b -> VCtor (prelBoolV b) []) <$> tryPutMVar mv exitV
  ("awaitPromiseExit", [VMVar mv]) -> interruptPoint (readMVar mv)
  ("awaitPromise", [VMVar mv]) -> do
    exitV <- interruptPoint (readMVar mv)
    case force ec exitV of
      VCtor exitG [v] | exitG == prelSuccess -> pure v
      VCtor exitG [c] | exitG == prelFailure -> case force ec c of
        VCtor causeG [e] | causeG == prelFail -> throwIO (KappaError e)
        _ -> throwIO (KappaError (VLit (LitStr "awaitPromise: promise failed with a non-Fail cause")))
      _ -> throwIO (KappaError (VLit (LitStr "awaitPromise: malformed promise Exit")))
  -- §18.11 non-blocking peek: pollPromise returns Some Exit iff completed (None
  -- otherwise) WITHOUT parking; isDonePromise returns the Bool. tryReadMVar
  -- never blocks. The oracle for OP_POLL_PROMISE / OP_IS_DONE_PROMISE.
  ("pollPromise", [VMVar mv]) -> do
    m <- tryReadMVar mv
    pure $ case m of
      Just exitV -> VCtor prelSome [exitV]
      Nothing -> VCtor prelNone []
  ("isDonePromise", [VMVar mv]) ->
    (\m -> VCtor (prelBoolV (isJust m)) []) <$> tryReadMVar mv
  -- §18.1 monotonic timers (single agent): nowMonotonic reads the host
  -- monotonic clock; sleepFor/sleepUntil advance instantly (a single agent
  -- has no other fiber to schedule during a sleep).
  -- §18.1 the two irreducible time prims take/return raw ns Ints; the typed
  -- Duration/Instant wrappers (incl. sleepUntil) are the std.time .kp fragment.
  ("__nowNanos", _) -> (VLit . LitInt . fromIntegral) <$> getMonotonicTimeNSec
  -- §18.1.10 fiber identity. The raw integer id is delivered here; the FiberId
  -- (MkFiberId) wrapper is the std.prelude surface (cf. nowMonotonic/Instant).
  -- currentFiberId reports the running fiber's id; fiberId reports a target's.
  ("__currentFiberId", _) -> (VLit . LitInt) <$> (myThreadId >>= fiberIdOf)
  ("__fiberId", [VFiber tid _]) -> (VLit . LitInt) <$> fiberIdOf tid
  ("__getFiberLabel", _) -> do
    tid <- myThreadId
    Map.findWithDefault (VCtor prelNone []) tid <$> atomicReadIORef' (rtFiberLabels rt)
  ("__setFiberLabel", [label]) -> do
    tid <- myThreadId
    atomicModifyIORef_' (rtFiberLabels rt) (Map.insert tid label)
    pure unitV
  ("__locallyFiberLabel", [label, body]) -> do
    tid <- myThreadId
    labels <- atomicReadIORef' (rtFiberLabels rt)
    let old = Map.lookup tid labels
    atomicModifyIORef_' (rtFiberLabels rt) (Map.insert tid label)
    result <- try (runIOValue rt body) :: IO (Either SomeException Value)
    withMaskFrame Masked . atomicModifyIORef_' (rtFiberLabels rt) $
      maybe (Map.delete tid) (Map.insert tid) old
    either throwIO pure result
  -- §18.1.6 sleep parks ONLY the current fiber (interruptible threadDelay on
  -- a non-threaded RTS yields to other runnable fibers — it does not block the
  -- agent; a throwTo wakes it as an interruption point). Nonpositive returns now.
  ("__sleepForNanos", [VLit (LitInt ns)]) ->
    if ns <= 0
      then pure unitV
      -- §32.2.5 interruption point: the masked fiber-level keeps threadDelay from
      -- being auto-interrupted; interruptPoint opens the interruptible window so an
      -- interrupt wakes the sleep, then DELIVERS if unmasked / RE-PARKS (full
      -- duration) if masked.  unitV after the (possibly re-parked) full sleep.
      else interruptPoint (threadDelay (nanosToMicros ns) >> pure unitV)
  ("__ioNewRef", [v]) -> VRef <$> newIORef v
  ("__ioReadRef", [VRef r]) -> readIORef r
  ("__ioWriteRef", [VRef r, v]) -> writeIORef r v >> pure unitV
  -- MUTABLE-ARRAY-DESIGN: the SEQUENTIAL ORACLE for the boxed mutable array.
  -- A fixed-length IOArray of boxed Values is the interpreter analogue of the
  -- runtime's K_ARRAY slab: O(1) in-place get/set, length stored in the bounds.
  -- The forall (e a) element type is erased, so the prim sees only value args;
  -- the index/size arrive as plain Int literals (the surface passes natToInt).
  -- Out-of-bounds traps via KappaError — the runtime floor (§6 tier 3), the same
  -- Defect channel the native krt_fail raises; the proof-carrying surface op
  -- never hits it, and the Option surface op guards it.
  ("__newArray", [VLit (LitInt n), initv]) -> do
    let len = fromInteger n :: Int
    when (len < 0) (throwIO (KappaError (VLit (LitStr "__newArray: negative length"))))
    arr <- IOA.newArray (0, len - 1) initv :: IO (IOArray Int Value)
    pure (VArr len arr)
  ("__arrayRead", [VArr len arr, VLit (LitInt i)]) -> do
    let ix = fromInteger i :: Int
    if ix < 0 || ix >= len
      then throwIO (KappaError (VLit (LitStr "__arrayRead: index out of range")))
      else IOA.readArray arr ix
  ("__arrayWrite", [VArr len arr, VLit (LitInt i), v]) -> do
    let ix = fromInteger i :: Int
    if ix < 0 || ix >= len
      then throwIO (KappaError (VLit (LitStr "__arrayWrite: index out of range")))
      else IOA.writeArray arr ix v >> pure unitV
  -- §29.1 std.atomic. Interpreter fibers are GHC threads, so AtomicRef
  -- read-modify-write operations must use IORef's atomic modifier as the oracle
  -- for the native boxed atomic-cell operations. Memory-order arguments still
  -- carry no observable interpreter effect beyond the operation's required
  -- atomicity.
  ("__newAtomicRef", [v]) -> VRef <$> newIORef v
  ("__atomicLoad", [_order, VRef r]) -> atomicModifyIORef' r (\old -> (old, old))
  ("__atomicStore", [_order, VRef r, v]) -> atomicModifyIORef' r (\_old -> (v, unitV))
  ("__atomicExchange", [_order, VRef r, v]) -> atomicModifyIORef' r (\old -> (v, old))
  -- strong compare-exchange: perform the swap and return the WITNESSED old value
  -- (the matched expected on success, the actual current on failure).  On the
  -- single agent the read-compare-write is one indivisible step.  The std.atomic
  -- wrapper reconstructs Exchanged/NotExchanged from witnessed==expected, exactly
  -- as the native path does — this keeps the oracle and the runtime identical.
  -- The order arg is now an Integer code; the single agent ignores it.
  ("__atomicCompareExchange", [_succ, _fail, VRef r, expected, desired]) -> do
    atomicModifyIORef' r $ \current ->
      if convertible ec 0 (force ec current) (force ec expected)
        then (desired, current)
        else (current, current)
  -- fetch-* return the OLD value (AtomicInteger gates these to integer cells).
  ("__atomicFetchAdd", [_order, VRef r, VLit (LitInt n)]) -> atomicFetchInt r (+ n)
  ("__atomicFetchSub", [_order, VRef r, VLit (LitInt n)]) -> atomicFetchInt r (subtract n)
  ("__atomicFetchAnd", [_order, VRef r, VLit (LitInt n)]) -> atomicFetchInt r (.&. n)
  ("__atomicFetchOr",  [_order, VRef r, VLit (LitInt n)]) -> atomicFetchInt r (.|. n)
  ("__atomicFetchXor", [_order, VRef r, VLit (LitInt n)]) -> atomicFetchInt r (`xor` n)
  ("ioBind", [m, k]) -> do
    a <- runIOValue rt m
    runIOValue rt (vapp ec k Expl a)
  ("ioThen", [m, k]) -> do
    _ <- runIOValue rt m
    runIOValue rt k
  -- §18.1.13 STM monad bind/pure: STM actions run via runIOValue inside
  -- 'stmAtomically's retry loop, so they sequence exactly like ioBind/ioPure.
  ("stmBind", [m, k]) -> do
    a <- runIOValue rt m
    runIOValue rt (vapp ec k Expl a)
  ("stmPure", [v]) -> pure v
  ("stmOrElse", [left, right]) -> do
    case rtStmJournal rt of
      Nothing -> throwIO . KappaError . VLit . LitStr $ "stmOrElse escaped atomically"
      Just journalRef -> do
        snapshot <- readIORef journalRef
        first <- try (runIOValue rt left) :: IO (Either RetrySignal Value)
        case first of
          Right value -> pure value
          Left RetrySignal -> writeIORef journalRef snapshot >> runIOValue rt right
  _ ->
    throwIO . KappaError . VLit . LitStr $
      "unhandled IO primitive: " <> p <> "/" <> T.pack (show (length args))
        <> " args=" <> T.intercalate " ; " (map (renderTerm . quote ec 0) args)
  where
    ec = rtEC rt
    -- §29.1 fetch-modify: atomically transform the cell and return the OLD value
    -- (matching the native fetch-* return convention).
    atomicFetchInt r f = do
      res <- atomicModifyIORef' r $ \old ->
        case force ec old of
          VLit (LitInt o) -> (VLit (LitInt (f o)), Right (VLit (LitInt o)))
          _ -> (old, Left (KappaError (VLit (LitStr "atomicFetch: cell is not an Integer"))))
      either throwIO pure res
