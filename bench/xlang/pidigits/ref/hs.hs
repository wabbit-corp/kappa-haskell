-- xlang/pidigits reference — GHC (-O2; Integer is GMP-backed). N HARDCODED = 5000.
--
-- CLBG pidigits: digits of pi via Gibbons' unbounded spigot, driven as a stream
-- of linear fractional transformations over a (q,r,t,k,n,l) state in Integer
-- (GHC's arbitrary-precision integer = GMP). Output is the standard CLBG layout:
-- 10 digits per line, each line tagged "\t:<count>" with the running digit
-- count; a short final line is left-padded with spaces.
--
-- Idiomatic-but-fair: a clean strict transcription. Each step is a PARALLEL
-- assignment (every new value uses the OLD q,r,t,k,n,l), expressed naturally by
-- binding a fresh state tuple. Output is built with a ByteString Builder so the
-- work measured is the bignum loop, not String I/O. NOT the hand-unrolled CLBG
-- entry.
module Main (main) where

import qualified Data.ByteString.Builder as B
import qualified Data.ByteString.Lazy as L
import Data.Char (intToDigit)
import System.IO (stdout)

n0 :: Int
n0 = 5000 -- HARDCODED digit count

type St = (Integer, Integer, Integer, Integer, Integer, Integer)

-- One spigot step: either emits digit n (Left d) or produces the next term
-- (Right ()), along with the new state. Every RHS uses the OLD state.
step :: St -> (Either Int (), St)
step (q, r, t, k, n, l)
  | 4 * q + r - t < n * t =
      let q' = 10 * q
          r' = 10 * (r - n * t)
          n' = (10 * (3 * q + r)) `div` t - 10 * n
      in (Left (fromInteger n), (q', r', t, k, n', l))
  | otherwise =
      let q' = q * k
          r' = (2 * q + r) * l
          t' = t * l
          k' = k + 1
          n' = (q * (7 * k + 2) + r * l) `div` (t * l)
          l' = l + 2
      in (Right (), (q', r', t', k', n', l'))

render :: Int -> B.Builder
render count = go (1, 0, 1, 1, 3, 3) 0 0 mempty
  where
    go st !emitted !col !lineAcc
      | emitted == count =
          if col == 0
            then mempty
            else lineAcc <> B.byteString (pad col) <> tag emitted
      | otherwise =
          case step st of
            (Right (), st') -> go st' emitted col lineAcc
            (Left d, st') ->
              let emitted' = emitted + 1
                  col'      = col + 1
                  acc'      = lineAcc <> B.char7 (intToDigit d)
              in if col' == 10
                   then (acc' <> tag emitted') <> go st' emitted' 0 mempty
                   else go st' emitted' col' acc'
    tag c = B.char7 '\t' <> B.char7 ':' <> B.intDec c <> B.char7 '\n'
    -- left-pad a short final line with spaces (no-op at N=5000)
    pad col = L.toStrict (L.replicate (fromIntegral (10 - col)) 32)

main :: IO ()
main = L.hPut stdout (B.toLazyByteString (render n0))
