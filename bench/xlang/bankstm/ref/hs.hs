-- xlang/bankstm reference — GHC (-O2), STM. Savina Bank-Transaction.
--
-- K = 1000 accounts (each a TVar Int), M = 1000000 concurrent random transfers
-- across W = 4 forkIO worker threads. Each transfer runs `atomically` debiting
-- one account and crediting another — GHC's optimistic STM, the direct analogue
-- of the Kappa port. The moved amount is conserved, so the printed total is the
-- deterministic invariant K*INIT regardless of interleaving (the Savina
-- conservation assertion), keeping stdout byte-identical across all impls.
--
-- N is HARDCODED. Methodology: idiomatic STM (-O2, -threaded -rtsopts with the
-- runner's flags as given); NOT a hand-tuned single-TVar or IORef+atomicModify
-- variant. Accounts live in a boxed Array of TVars for O(1) random access.
--
-- NOTE the runner builds with `ghc -O2` (no -threaded). Without -threaded the
-- forkIO threads are cooperatively scheduled on one OS thread; STM semantics and
-- the conserved total are identical — only wall-clock parallelism differs. This
-- is recorded in the report (a -threaded build would use multiple cores).
module Main where

import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import Control.Concurrent.STM (TVar, atomically, newTVarIO, readTVar, readTVarIO, writeTVar)
import Control.Monad (forM_, replicateM)
import Data.Array (Array, listArray, (!))
import Data.Int (Int64)

kAccounts, mTransfers, wWorkers, initBal :: Int
kAccounts = 1000     -- HARDCODED N: accounts
mTransfers = 1000000 -- HARDCODED N: transfers
wWorkers = 4         -- worker threads
initBal = 1000       -- starting balance per account

-- Park-Miller MINSTD LCG, state in (0, 2^31-1) — matches the Kappa port.
lcg :: Int64 -> Int64
lcg s = (s * 16807) `mod` 2147483647

worker :: Array Int (TVar Int64) -> Int -> Int64 -> IO ()
worker accts cnt = go cnt
  where
    k64 = fromIntegral kAccounts :: Int64
    go 0 _ = pure ()
    go n s =
      let s1 = lcg s
          s2 = lcg s1
          i = fromIntegral (s1 `mod` k64)
          j = fromIntegral (s2 `mod` k64)
       in do
            atomically $ do
              let a = accts ! i
                  b = accts ! j
              av <- readTVar a
              writeTVar a (av - 1)
              bv <- readTVar b
              writeTVar b (bv + 1)
            go (n - 1) s2

main :: IO ()
main = do
  tvs <- replicateM kAccounts (newTVarIO (fromIntegral initBal :: Int64))
  let accts = listArray (0, kAccounts - 1) tvs
      perW = mTransfers `div` wWorkers
      seeds = [1, 1000003, 2000029, 3000071] :: [Int64]
  dones <- mapM (const newEmptyMVar) seeds
  forM_ (zip seeds dones) $ \(seed, d) ->
    forkIO (worker accts perW seed >> putMVar d ())
  mapM_ takeMVar dones
  total <- sum <$> mapM readTVarIO (map (accts !) [0 .. kAccounts - 1])
  print total
