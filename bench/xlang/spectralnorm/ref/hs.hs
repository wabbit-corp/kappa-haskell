-- xlang/spectralnorm reference — GHC (-O2).  N HARDCODED = 5500.
--
-- Spectral norm (CLBG): largest singular value of the infinite matrix
--   A(i,j) = 1 / ((i+j)*(i+j+1)/2 + i + 1)
-- via the power method: 10 iterations of v = (A^T A) u, then
--   sqrt ((u . v) / (v . v)).
--
-- Idiomatic + clean: an unboxed Data.Array.Unboxed vector, textbook
-- A/At/AtA helpers, single-threaded (NOT the parallel CLBG entry).
-- Prints 9 decimals via Numeric.showFFloat.
module Main where

import Data.Array.Unboxed
import Numeric (showFFloat)

-- N = 5500
n :: Int
n = 5500

-- A(i,j) = 1 / ((i+j)(i+j+1)/2 + i + 1)
matA :: Int -> Int -> Double
matA i j = 1.0 / fromIntegral ((ij * (ij + 1)) `div` 2 + i + 1)
  where ij = i + j

type Vec = UArray Int Double

-- w = A v
mulAv :: Vec -> Vec
mulAv v = listArray (0, n - 1)
  [ sum [ matA i j * (v ! j) | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]

-- w = A^T v
mulAtv :: Vec -> Vec
mulAtv v = listArray (0, n - 1)
  [ sum [ matA j i * (v ! j) | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]

-- w = A^T A v
mulAtAv :: Vec -> Vec
mulAtAv = mulAtv . mulAv

main :: IO ()
main = do
  let u0 = listArray (0, n - 1) (replicate n 1.0) :: Vec
      step (u, _) = let v = mulAtAv u in (mulAtAv v, v)
      (u, v) = iterate step (u0, u0) !! 10
      vBv = sum [ (u ! i) * (v ! i) | i <- [0 .. n - 1] ]
      vv  = sum [ (v ! i) * (v ! i) | i <- [0 .. n - 1] ]
  putStrLn (showFFloat (Just 9) (sqrt (vBv / vv)) "")
