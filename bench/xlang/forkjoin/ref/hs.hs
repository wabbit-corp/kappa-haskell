-- xlang/forkjoin reference — GHC (-O2), idiomatic forkIO fork-join.
-- Savina Fork-Join: spawn N threads, each runs a small modular-integer CPU task
-- seeded by its index and atomically accumulates its result; the parent joins
-- all (via a QSemN barrier) and prints the checksum.  N HARDCODED = 100000.
--
-- Methodology: idiomatic-but-fair — one lightweight `forkIO` thread per fiber,
-- an atomicModifyIORef' lock-free accumulator, and a QSemN to join.  Not
-- hand-tuned; mirrors the Kappa port's one-fiber-per-task structure.
--
-- NOTE on parallelism: the xbench harness builds this with plain `ghc -O2`
-- (no `-threaded`), so it links the SINGLE-capability (non-threaded) RTS — the
-- forkIO threads run cooperatively on one OS thread.  The checksum is identical
-- either way (it is order-independent); only the timing reflects single-core
-- cooperative scheduling rather than true multicore fork-join.
module Main where

import Control.Concurrent (forkIO)
import Control.Concurrent.QSemN (newQSemN, signalQSemN, waitQSemN)
import Control.Monad (forM_)
import Data.IORef (newIORef, atomicModifyIORef', readIORef)
import Data.Int (Int64)

-- per-fiber CPU task: modular integer mixing loop, `k` steps, seeded by acc.
task :: Int64 -> Int64 -> Int64
task acc k
  | k <= 0    = acc
  | otherwise = task ((acc * 1000003 + k) `mod` 2147483647) (k - 1)

n :: Int
n = 100000 -- N HARDCODED = 100000 fibers

main :: IO ()
main = do
  total <- newIORef (0 :: Int64)
  sem <- newQSemN 0
  forM_ [0 .. fromIntegral n - 1 :: Int64] $ \i ->
    forkIO $ do
      let !v = task (i + 1) 200
      atomicModifyIORef' total (\t -> (t + v, ()))
      signalQSemN sem 1
  waitQSemN sem n
  readIORef total >>= print
