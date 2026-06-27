-- xlang/skynet reference — GHC (-O2), forkIO + MVar. N HARDCODED = 1000000.
--
-- Classic skynet: a root spawns 10 children, each spawns 10, ... down to
-- 1_000_000 leaf threads, each returning its ordinal; the sums fold back up the
-- tree. Total = sum 0..999999 = 499999500000.
--
-- Methodology: idiomatic-but-fair — one lightweight Haskell thread (forkIO) per
-- node, each child handing its result back over a per-child MVar; the parent
-- forks all `div` children, then collects. NOT hyper-tuned (no STM batching, no
-- async library, no chunked work-stealing). Built with -O2. This is the GHC
-- green-thread headline to compare against Go goroutines and Kappa fork/await.
--
-- NOTE: the runner builds with `ghc -O2` and runs the bare binary (no +RTS
-- flags), so this exercises the default single-capability RTS scheduler — the
-- fair apples-to-apples comparison against the other single-runtime ports.
module Main where

import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)

skynet :: Int -> Int -> Int -> IO Int
skynet num size div'
  | size == 1 = return num
  | otherwise = do
      let step = size `div` div'
      mvars <- mapM
        (\i -> do
           m <- newEmptyMVar
           _ <- forkIO (skynet (num + i * step) step div' >>= putMVar m)
           return m)
        [0 .. div' - 1]
      sums <- mapM takeMVar mvars
      return (sum sums)

main :: IO ()
main = do
  -- N = 1000000 leaf threads (size), branching factor 10.
  total <- skynet 0 1000000 10
  print total
