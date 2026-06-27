-- xlang/mandelbrot reference — GHC (-O2).  N HARDCODED = 4000.
--
-- CLBG Mandelbrot: render the NxN portable-bitmap (PBM) of the Mandelbrot set,
-- 8 pixels packed MSB-first per byte, then fold the packed bytes into a single
-- 64-bit rolling checksum so the program prints ONE line (we time compute, not
-- I/O).  See ref/c.c for the algorithm + bit-identity note: the iteration uses
-- explicit `let` temporaries (no a*b+c) so GHC emits separately-rounded Double
-- ops matching the other languages.  The checksum is an explicitly-MODULAR
-- rolling hash (mod 2^31-1) so it matches Kappa's arbitrary-precision Integer
-- (no machine-word wraparound); see ref/c.c for the rationale.  GHC `Int` is
-- 64-bit here, more than enough for the < 2.1e15 intermediate products.
{-# LANGUAGE BangPatterns #-}
module Main where

n :: Int
n = 4000      -- image is N x N

iters :: Int
iters = 50    -- mandelbrot iteration count

modulus :: Int
modulus = 2147483647    -- 2^31 - 1; rolling-hash modulus (portable)

-- Iterate Z <- Z^2 + C for `iters` steps; return Zr*Zr+Zi*Zi after the last.
mag :: Double -> Double -> Double
mag cr ci = go 0.0 0.0 iters
  where
    go :: Double -> Double -> Int -> Double
    go !zr !zi 0 = zr * zr + zi * zi
    go !zr !zi k =
      let !zr2  = zr * zr
          !zi2  = zi * zi
          !zrzi = zr * zi
          !zr'  = zr2 - zi2 + cr
          !zi'  = zrzi + zrzi + ci   -- 2*zr*zi, no FMA fusion
      in go zr' zi' (k - 1)

main :: IO ()
main = print (rowLoop 0 0)
  where
    rowLoop :: Int -> Int -> Int
    rowLoop !py !chk
      | py >= n   = chk
      | otherwise =
          let !ci = 2.0 * fromIntegral py / fromIntegral n - 1.0
          in rowLoop (py + 1) (colLoop py 0 0 0 ci chk)

    -- pack `n` pixels of row py, 8 MSB-first per byte, folding into chk.
    colLoop :: Int -> Int -> Int -> Int -> Double -> Int -> Int
    colLoop !py !px !nbits !byteAcc !ci !chk
      | px >= n =
          if nbits /= 0
            then let !byteAcc' = byteAcc * (2 ^ (8 - nbits))
                 in (chk * 1000003 + byteAcc') `mod` modulus
            else chk
      | otherwise =
          let !cr      = 2.0 * fromIntegral px / fromIntegral n - 1.5
              !m       = mag cr ci
              !inside  = if m <= 4.0 then 1 else 0 :: Int
              !byteAcc'= byteAcc * 2 + inside
              !nbits'  = nbits + 1
          in if nbits' == 8
               then colLoop py (px + 1) 0 0 ci ((chk * 1000003 + byteAcc') `mod` modulus)
               else colLoop py (px + 1) nbits' byteAcc' ci chk
