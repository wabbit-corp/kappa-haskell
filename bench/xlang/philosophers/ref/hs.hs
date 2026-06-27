-- xlang/philosophers reference — GHC (-O2). N = 20 philosophers, M = 100000 rounds.
--
-- Savina Dining-Philosophers over STM. GHC has real STM, so this is the closest
-- 1:1 to the Kappa port: each fork is a `TVar Bool` (True = free); a philosopher
-- picks up BOTH forks in a single `atomically` transaction (read both, `check`
-- both free via `retry`, mark both taken) — all-or-nothing, hence deadlock-free.
-- Eating bumps a shared `TVar Int` meal counter atomically; forkIO spawns the N
-- philosophers, and a per-philosopher "done" TVar is awaited to join them.
-- Total meals = N*M = 2000000, printed on one line.
--
-- Methodology: idiomatic Control.Concurrent.STM, ghc -O2. Not hand-tuned.
module Main where

import Control.Concurrent (forkIO)
import Control.Concurrent.STM
import Control.Monad (forM, forM_, replicateM, when)

n :: Int
n = 20 -- philosophers (and forks)

m :: Int
m = 100000 -- rounds per philosopher

-- Atomic two-fork pickup: both must be free, then both become taken.
acquire :: TVar Bool -> TVar Bool -> STM ()
acquire l r = do
  lf <- readTVar l
  rf <- readTVar r
  check (lf && rf)
  writeTVar l False
  writeTVar r False

release :: TVar Bool -> TVar Bool -> STM ()
release l r = do
  writeTVar l True
  writeTVar r True

philosopher :: TVar Int -> TVar Bool -> TVar Bool -> TVar Bool -> IO ()
philosopher meals l r done = do
  let loop 0 = atomically (writeTVar done True)
      loop k = do
        atomically (acquire l r)
        atomically (modifyTVar' meals (+ 1)) -- eat
        atomically (release l r)
        loop (k - 1)
  loop m

main :: IO ()
main = do
  forks <- replicateM n (newTVarIO True)
  meals <- newTVarIO 0
  dones <- replicateM n (newTVarIO False)
  forM_ [0 .. n - 1] $ \i -> do
    let l = forks !! i
        r = forks !! ((i + 1) `mod` n)
    _ <- forkIO (philosopher meals l r (dones !! i))
    return ()
  -- Join: wait until every philosopher has flagged done.
  atomically $ forM_ dones $ \d -> do
    f <- readTVar d
    check f
  total <- readTVarIO meals
  print total
