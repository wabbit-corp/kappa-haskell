{-# LANGUAGE BangPatterns #-}

module Kappa.SemanticHash
  ( sha256Hex
  , sha256BytesHex
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
import Control.Monad (forM_)
import Control.Monad.ST (ST, runST)
import Data.Array.ST (STUArray, newArray, readArray, writeArray)
import Data.Array.Unboxed (UArray, (!), listArray)
import qualified Data.ByteString as BS
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Word (Word32, Word64, Word8)
import Numeric (showHex)

-- | SHA-256 over UTF-8 text. Semantic digests are lookup/check hints; callers
-- that decide equality must retain and compare the canonical identity bytes.
sha256Hex :: Text -> Text
sha256Hex =
  renderHash . sha256State . TE.encodeUtf8

-- | SHA-256 over exact bytes. Artifact integrity must not reinterpret an
-- arbitrary binary payload as source text before hashing it.
sha256BytesHex :: BS.ByteString -> Text
sha256BytesHex = renderHash . sha256State

-- | Lossless hexadecimal serialization of a domain-separated UTF-8 identity.
-- Unlike a digest this is injective and is therefore suitable as authority
-- for semantic equality.
canonicalIdentityHex :: Text -> Text -> Text
canonicalIdentityHex domain payload =
  T.concat
    [ byteHex byte
    | byte <- BS.unpack (TE.encodeUtf8 ("KAPPA:v1:" <> domain <> "\0" <> payload))
    ]

type HashState =
  (Word32, Word32, Word32, Word32, Word32, Word32, Word32, Word32)

sha256State :: BS.ByteString -> HashState
sha256State input = go initialHash 0
  where
    bytes = pad input
    byteCount = BS.length bytes
    go !state !offset
      | offset >= byteCount = state
      | otherwise = go (compress bytes offset state) (offset + 64)

pad :: BS.ByteString -> BS.ByteString
pad bytes =
  BS.concat
    [ bytes
    , BS.singleton 0x80
    , BS.replicate zeroCount 0
    , BS.pack (word64Bytes bitLength)
    ]
  where
    bitLength = fromIntegral (BS.length bytes) * 8 :: Word64
    zeroCount = (56 - ((BS.length bytes + 1) `mod` 64)) `mod` 64

compress :: BS.ByteString -> Int -> HashState -> HashState
compress bytes blockOffset initial@(h0, h1, h2, h3, h4, h5, h6, h7) =
  addState initial final
  where
    final = runST $ do
      schedule <- buildSchedule bytes blockOffset
      let rounds !index !state
            | index >= 64 = pure state
            | otherwise = do
                word <- readArray schedule index
                rounds (index + 1) (roundStep state (roundConstants ! index) word)
      rounds 0 (h0, h1, h2, h3, h4, h5, h6, h7)

buildSchedule :: BS.ByteString -> Int -> ST s (STUArray s Int Word32)
buildSchedule bytes blockOffset = do
  schedule <- newArray (0, 63) 0
  forM_ [0 .. 15] $ \index ->
    writeArray schedule index
      (word32FromBytesAt bytes (blockOffset + index * 4))
  forM_ [16 .. 63] $ \index -> do
    word2 <- readArray schedule (index - 2)
    word7 <- readArray schedule (index - 7)
    word15 <- readArray schedule (index - 15)
    word16 <- readArray schedule (index - 16)
    writeArray schedule index
      (smallSigma1 word2 + word7 + smallSigma0 word15 + word16)
  pure schedule

roundStep :: HashState -> Word32 -> Word32 -> HashState
roundStep (!a, !b, !c, !d, !e, !f, !g, !h) !constant !word =
  (temp1 + temp2, a, b, c, d + temp1, e, f, g)
  where
    temp1 = h + bigSigma1 e + choose e f g + constant + word
    temp2 = bigSigma0 a + majority a b c

addState :: HashState -> HashState -> HashState
addState
  (!a0, !b0, !c0, !d0, !e0, !f0, !g0, !h0)
  (!a1, !b1, !c1, !d1, !e1, !f1, !g1, !h1) =
    ( a0 + a1
    , b0 + b1
    , c0 + c1
    , d0 + d1
    , e0 + e1
    , f0 + f1
    , g0 + g1
    , h0 + h1
    )

choose, majority :: Word32 -> Word32 -> Word32 -> Word32
choose x y z = (x .&. y) `xor` (complement x .&. z)
majority x y z = (x .&. y) `xor` (x .&. z) `xor` (y .&. z)

bigSigma0, bigSigma1, smallSigma0, smallSigma1 :: Word32 -> Word32
bigSigma0 x = rotateR x 2 `xor` rotateR x 13 `xor` rotateR x 22
bigSigma1 x = rotateR x 6 `xor` rotateR x 11 `xor` rotateR x 25
smallSigma0 x = rotateR x 7 `xor` rotateR x 18 `xor` shiftR x 3
smallSigma1 x = rotateR x 17 `xor` rotateR x 19 `xor` shiftR x 10

word32FromBytesAt :: BS.ByteString -> Int -> Word32
word32FromBytesAt bytes offset =
  shiftL (fromIntegral a) 24
    .|. shiftL (fromIntegral b) 16
    .|. shiftL (fromIntegral c) 8
    .|. fromIntegral d
  where
    a = BS.index bytes offset
    b = BS.index bytes (offset + 1)
    c = BS.index bytes (offset + 2)
    d = BS.index bytes (offset + 3)

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

renderHash :: HashState -> Text
renderHash (a, b, c, d, e, f, g, h) =
  T.concat (map word32Hex [a, b, c, d, e, f, g, h])

initialHash :: HashState
initialHash =
  ( 0x6a09e667
  , 0xbb67ae85
  , 0x3c6ef372
  , 0xa54ff53a
  , 0x510e527f
  , 0x9b05688c
  , 0x1f83d9ab
  , 0x5be0cd19
  )

roundConstants :: UArray Int Word32
roundConstants =
  listArray (0, 63)
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
