-- xlang/fannkuch reference — GHC (-O2). N HARDCODED = 11.
--
-- Fannkuch-redux (CLBG): over every permutation of 1..N, count prefix-reversals
-- ("pancake flips") to bring 1 to the front; report the max flip count and a
-- checksum (sum of (-1)^permindex * flips).
--
-- Methodology: idiomatic clean Haskell using a mutable unboxed ST array
-- (STUArray Int Int) for the permutation buffers — a fair like-for-like
-- int-array port of the canonical single-threaded fannkuch-redux walk. This is
-- NOT the multi-threaded / hand-tuned fastest CLBG entry.
--
-- Reference answer for N=11: checksum 556355, Pfannkuchen(11) = 51.
module Main where

import Control.Monad (when)
import Control.Monad.ST (ST, runST)
import Data.Array.ST (STUArray, newArray, newListArray, readArray, writeArray)
import Data.STRef

n :: Int
n = 11 -- HARDCODED

fannkuch :: (Int, Int)
fannkuch = runST $ do
  perm  <- newArray (0, n - 1) 0          :: ST s (STUArray s Int Int)
  perm1 <- newListArray (0, n - 1) [0 .. n - 1] :: ST s (STUArray s Int Int)
  count <- newArray (0, n - 1) 0          :: ST s (STUArray s Int Int)

  checksum <- newSTRef (0 :: Int)
  maxflips <- newSTRef (0 :: Int)
  permcount <- newSTRef (0 :: Int)
  rRef <- newSTRef n

  let rotatePrefix r = do
        first <- readArray perm1 0
        mapM_ (\i -> readArray perm1 (i + 1) >>= writeArray perm1 i) [0 .. r - 1]
        writeArray perm1 r first

      reverseHead = do
        k <- readArray perm 0
        if k == 0
          then return (0 :: Int)
          else do
            let rev lo hi = when (lo < hi) $ do
                  a <- readArray perm lo
                  b <- readArray perm hi
                  writeArray perm lo b
                  writeArray perm hi a
                  rev (lo + 1) (hi - 1)
            rev 0 k
            rest <- reverseHead
            return (1 + rest)

      loop = do
        r0 <- readSTRef rRef
        let settle r
              | r /= 1    = writeArray count (r - 1) r >> settle (r - 1)
              | otherwise = return ()
        settle r0
        writeSTRef rRef 1

        mapM_ (\i -> readArray perm1 i >>= writeArray perm i) [0 .. n - 1]
        flips <- reverseHead
        modifySTRef' maxflips (max flips)
        pc <- readSTRef permcount
        modifySTRef' checksum (+ (if even pc then flips else negate flips))

        let advance = do
              r <- readSTRef rRef
              if r == n
                then return ()
                else do
                  rotatePrefix r
                  c <- readArray count r
                  writeArray count r (c - 1)
                  if c - 1 > 0
                    then return ()
                    else writeSTRef rRef (r + 1) >> advance
        advance
        modifySTRef' permcount (+ 1)
        rEnd <- readSTRef rRef
        if rEnd == n then return () else loop

  loop
  cs <- readSTRef checksum
  mf <- readSTRef maxflips
  return (cs, mf)

main :: IO ()
main = do
  let (cs, mf) = fannkuch
  putStrLn (show cs)
  putStrLn ("Pfannkuchen(" ++ show n ++ ") = " ++ show mf)
