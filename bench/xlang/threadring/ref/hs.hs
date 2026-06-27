-- xlang/threadring reference — GHC (-O2). Idiomatic forkIO + MVar mailboxes.
-- N = 503 ring nodes, HOPS = 1000000 (both HARDCODED; must match every impl).
--
-- CLBG / Savina thread-ring: 503 lightweight threads form a ring; each owns an
-- MVar mailbox and BLOCKS (takeMVar) until the token arrives, then forwards it
-- decremented to the next node. The thread that takes a 0 token prints its
-- 1-based id. Winner = (HOPS mod N) + 1 = (1000000 mod 503) + 1 = 37.
--
-- Methodology: idiomatic blocking MVars + forkIO (one Haskell green thread per
-- ring node), compiled with -O2 (the harness invocation). The non-threaded RTS
-- runs all green threads on one OS thread, which is the fair single-agent analog
-- of the Kappa port. NOT the hyper-tuned CLBG entry.
module Main where

import Control.Concurrent (forkIO)
import Control.Concurrent.MVar
import Control.Monad (forM, forM_)
import Data.Array (listArray, (!))

n :: Int
n = 503 -- ring size

hops :: Int
hops = 1000000 -- initial token value

main :: IO ()
main = do
  -- One empty mailbox per ring node, in an immutable array for O(1) indexing.
  boxList <- forM [0 .. n - 1] (const newEmptyMVar) :: IO [MVar Int]
  let boxes = listArray (0, n - 1) boxList
  done <- newEmptyMVar
  forM_ [0 .. n - 1] $ \i -> do
    let inbox = boxes ! i
        next = boxes ! ((i + 1) `mod` n)
        loop = do
          v <- takeMVar inbox
          if v <= 0
            then putMVar done (i + 1) -- report 1-based id
            else putMVar next (v - 1) >> loop
    _ <- forkIO loop
    return ()
  putMVar (boxes ! 0) hops -- inject the token at ring node 1
  winner <- takeMVar done
  print winner
