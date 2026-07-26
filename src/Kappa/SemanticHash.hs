module Kappa.SemanticHash
  ( sha256Hex
  , canonicalIdentityHex
  ) where

import Data.Bits
  ( complement
  , rotateR
  , shiftL
  , shiftR
  , xor
  , (.&.)
  , (.|.)
  )
import qualified Data.ByteString as BS
import Data.List (foldl')
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Word (Word32, Word64, Word8)
import Numeric (showHex)

-- | SHA-256 over UTF-8 text. Semantic digests are lookup/check hints; callers
-- that decide equality must retain and compare the canonical identity bytes.
sha256Hex :: Text -> Text
sha256Hex =
  T.concat . map word32Hex . sha256Words . TE.encodeUtf8

-- | Lossless hexadecimal serialization of a domain-separated UTF-8 identity.
-- Unlike a digest this is injective and is therefore suitable as authority
-- for semantic equality.
canonicalIdentityHex :: Text -> Text -> Text
canonicalIdentityHex domain payload =
  T.concat
    [ byteHex byte
    | byte <- BS.unpack (TE.encodeUtf8 ("KAPPA:v1:" <> domain <> "\0" <> payload))
    ]

sha256Words :: BS.ByteString -> [Word32]
sha256Words input =
  foldl' compress initialHash (chunksOf 64 (pad input))

pad :: BS.ByteString -> [Word8]
pad bytes =
  BS.unpack bytes
    ++ [0x80]
    ++ replicate zeroCount 0
    ++ word64Bytes bitLength
  where
    bitLength = fromIntegral (BS.length bytes) * 8 :: Word64
    zeroCount = (56 - ((BS.length bytes + 1) `mod` 64)) `mod` 64

compress :: [Word32] -> [Word8] -> [Word32]
compress state block =
  zipWith (+) state [a, b, c, d, e, f, g, h]
  where
    schedule0 = map word32FromBytes (chunksOf 4 block)
    schedule = extendSchedule schedule0 16
    [a, b, c, d, e, f, g, h] =
      foldl' roundStep state (zip roundConstants schedule)

    roundStep [a0, b0, c0, d0, e0, f0, g0, h0] (constant, word) =
      [ temp1 + temp2
      , a0
      , b0
      , c0
      , d0 + temp1
      , e0
      , f0
      , g0
      ]
      where
        temp1 = h0 + bigSigma1 e0 + choose e0 f0 g0 + constant + word
        temp2 = bigSigma0 a0 + majority a0 b0 c0
    roundStep _ _ = error "sha256: invalid compression state"

extendSchedule :: [Word32] -> Int -> [Word32]
extendSchedule words0 index
  | index >= 64 = words0
  | otherwise =
      let next =
            smallSigma1 (words0 !! (index - 2))
              + words0 !! (index - 7)
              + smallSigma0 (words0 !! (index - 15))
              + words0 !! (index - 16)
       in extendSchedule (words0 ++ [next]) (index + 1)

choose, majority :: Word32 -> Word32 -> Word32 -> Word32
choose x y z = (x .&. y) `xor` (complement x .&. z)
majority x y z = (x .&. y) `xor` (x .&. z) `xor` (y .&. z)

bigSigma0, bigSigma1, smallSigma0, smallSigma1 :: Word32 -> Word32
bigSigma0 x = rotateR x 2 `xor` rotateR x 13 `xor` rotateR x 22
bigSigma1 x = rotateR x 6 `xor` rotateR x 11 `xor` rotateR x 25
smallSigma0 x = rotateR x 7 `xor` rotateR x 18 `xor` shiftR x 3
smallSigma1 x = rotateR x 17 `xor` rotateR x 19 `xor` shiftR x 10

word32FromBytes :: [Word8] -> Word32
word32FromBytes [a, b, c, d] =
  shiftL (fromIntegral a) 24
    .|. shiftL (fromIntegral b) 16
    .|. shiftL (fromIntegral c) 8
    .|. fromIntegral d
word32FromBytes _ = error "sha256: invalid word"

word64Bytes :: Word64 -> [Word8]
word64Bytes word =
  [ fromIntegral (shiftR word shift .&. 0xff)
  | shift <- [56, 48 .. 0]
  ]

word32Hex :: Word32 -> Text
word32Hex word = T.pack (replicate (8 - length digits) '0' ++ digits)
  where
    digits = showHex word ""

byteHex :: Word8 -> Text
byteHex byte = T.pack (replicate (2 - length digits) '0' ++ digits)
  where
    digits = showHex byte ""

chunksOf :: Int -> [a] -> [[a]]
chunksOf _ [] = []
chunksOf size values =
  let (chunk, rest) = splitAt size values
   in chunk : chunksOf size rest

initialHash :: [Word32]
initialHash =
  [ 0x6a09e667
  , 0xbb67ae85
  , 0x3c6ef372
  , 0xa54ff53a
  , 0x510e527f
  , 0x9b05688c
  , 0x1f83d9ab
  , 0x5be0cd19
  ]

roundConstants :: [Word32]
roundConstants =
  [ 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5
  , 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
  , 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3
  , 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
  , 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc
  , 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
  , 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7
  , 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
  , 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13
  , 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
  , 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3
  , 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
  , 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5
  , 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
  , 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208
  , 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
  ]
