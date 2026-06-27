{-# OPTIONS_GHC -threaded #-}
-- xlang/pingpong reference — GHC (-O2). Savina Ping-Pong: two threads exchange
-- N messages over a pair of MVars; print the count of completed round-trips.
--
-- Idiomatic-but-fair: forkIO + two MVars used as synchronous one-shot mailboxes
-- (takeMVar/putMVar rendezvous) — the natural Haskell shape and the closest
-- analogue of Kappa's one-shot-promise handoff, not hyper-tuned. N is HARDCODED
-- = 1000000 to match every impl + expected.txt. Built with the threaded RTS so
-- the two threads run on the M:N scheduler (apples-to-apples with the fibers).
module Main where


import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (newEmptyMVar, takeMVar, putMVar)
import Control.Monad (forM_)

-- N = 1000000
n :: Int
n = 1000000

main :: IO ()
main = do
  toPong <- newEmptyMVar -- ping -> pong
  toPing <- newEmptyMVar -- pong -> ping
  done   <- newEmptyMVar
  -- pong thread: receive a ping, reply, N times.
  _ <- forkIO $ do
    forM_ [1 .. n] $ \_ -> do
      _ <- takeMVar toPong
      putMVar toPing (1 :: Int)
    putMVar done n
  -- ping role (main thread): send, await reply, N times.
  forM_ [1 .. n] $ \_ -> do
    putMVar toPong (1 :: Int)
    _ <- takeMVar toPing
    pure ()
  count <- takeMVar done
  print count
