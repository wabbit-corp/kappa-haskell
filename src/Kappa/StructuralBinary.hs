{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Compact structural serialization for compiler-generated, versioned
-- artifacts. The caller supplies the semantic schema version; this codec
-- records algebraic constructor indices and fields without source names.
-- Decoding is type-directed and rejects invalid tags, trailing bytes, and
-- malformed UTF-8.
module Kappa.StructuralBinary
  ( encodeStructuralBinary
  , decodeStructuralBinary
  ) where

import Data.Binary.Get
import Data.Binary.Put
import Data.Bits ((.&.))
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import Data.Data
  ( Data
  , constrIndex
  , dataTypeOf
  , fromConstrM
  , gmapQ
  , indexConstr
  , maxConstrIndex
  )
import qualified Data.Data as Data
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Type.Equality ((:~:) (Refl))
import Data.Typeable (eqT)
import Data.Word (Word8, Word32, Word64)
import Numeric.Natural (Natural)

encodeStructuralBinary :: Data a => a -> BS.ByteString
encodeStructuralBinary = BL.toStrict . runPut . putData

decodeStructuralBinary :: Data a => BS.ByteString -> Either Text a
decodeStructuralBinary bytes =
  case runGetOrFail getData (BL.fromStrict bytes) of
    Left (_, offset, message) ->
      Left
        ( "invalid structural artifact at byte "
            <> T.pack (show offset)
            <> ": "
            <> T.pack message
        )
    Right (remaining, _, value)
      | BL.null remaining -> Right value
      | otherwise -> Left "invalid structural artifact: trailing bytes"

putData :: forall a. Data a => a -> Put
putData value
  | Just bytes <- castData value = putBytes bytes
  | Just text <- castData value = putText text
  | Just string <- castData value = putText (T.pack string)
  | Just integer <- castData value = putSignedInteger integer
  | Just integer <- castData value = putSignedInteger (toInteger (integer :: Int))
  | Just natural <- castData value = putUnsignedInteger (toInteger (natural :: Natural))
  | Just word <- castData value = putVarWord64 (fromIntegral (word :: Word8))
  | Just word <- castData value = putVarWord64 (fromIntegral (word :: Word32))
  | Just word <- castData value = putVarWord64 (word :: Word64)
  | Just character <- castData value = putVarWord64 (fromIntegral (fromEnum (character :: Char)))
  | Just boolean <- castData value = putWord8 (if boolean then 1 else 0)
  | Just number <- castData value = putDoublebe (number :: Double)
  | Just number <- castData value = putFloatbe (number :: Float)
  | otherwise = do
      putVarWord64 (fromIntegral (constrIndex (toConstrData value)))
      sequence_ (gmapQ putData value)
  where
    castData :: forall b. Data b => a -> Maybe b
    castData = Data.cast
    toConstrData = Data.toConstr

getData :: forall a. Data a => Get a
getData
  | Just Refl <- eqT @a @BS.ByteString = getBytePayload
  | Just Refl <- eqT @a @Text = getText
  | Just Refl <- eqT @a @String = T.unpack <$> getText
  | Just Refl <- eqT @a @Integer = getSignedInteger
  | Just Refl <- eqT @a @Int = checkedIntegral "Int" =<< getSignedInteger
  | Just Refl <- eqT @a @Natural = fromInteger <$> getUnsignedInteger
  | Just Refl <- eqT @a @Word8 = checkedIntegral "Word8" . toInteger =<< getVarWord64
  | Just Refl <- eqT @a @Word32 = checkedIntegral "Word32" . toInteger =<< getVarWord64
  | Just Refl <- eqT @a @Word64 = getVarWord64
  | Just Refl <- eqT @a @Char = do
      codepoint <- getVarWord64
      if codepoint <= 0x10ffff
        then pure (toEnum (fromIntegral codepoint))
        else fail "invalid Unicode code point"
  | Just Refl <- eqT @a @Bool = do
      tag <- getWord8
      case tag of
        0 -> pure False
        1 -> pure True
        _ -> fail "invalid Bool tag"
  | Just Refl <- eqT @a @Double = getDoublebe
  | Just Refl <- eqT @a @Float = getFloatbe
  | otherwise = do
      index <- fromIntegral <$> getVarWord64
      let dataType = dataTypeOf (undefined :: a)
      if index <= 0 || index > maxConstrIndex dataType
        then fail "invalid algebraic constructor index"
        else fromConstrM getData (indexConstr dataType index)

putText :: Text -> Put
putText = putBytes . TE.encodeUtf8

putBytes :: BS.ByteString -> Put
putBytes bytes = do
  putVarWord64 (fromIntegral (BS.length bytes))
  putByteString bytes

getText :: Get Text
getText = do
  bytes <- getBytePayload
  either (fail . show) pure (TE.decodeUtf8' bytes)

getBytePayload :: Get BS.ByteString
getBytePayload = do
  length' <- getVarWord64
  if length' > fromIntegral (maxBound :: Int)
    then fail "byte payload exceeds host bounds"
    else getByteString (fromIntegral length')

putSignedInteger :: Integer -> Put
putSignedInteger integer =
  putUnsignedInteger
    (if integer >= 0 then 2 * integer else 2 * negate integer - 1)

getSignedInteger :: Get Integer
getSignedInteger = do
  encoded <- getUnsignedInteger
  pure
    ( if even encoded
        then encoded `div` 2
        else negate ((encoded + 1) `div` 2)
    )

putUnsignedInteger :: Integer -> Put
putUnsignedInteger integer
  | integer < 0 = error "putUnsignedInteger: negative input"
  | otherwise = go integer
  where
    go remaining
      | remaining < 0x80 = putWord8 (fromIntegral remaining)
      | otherwise = do
          putWord8 (fromIntegral (remaining `mod` 0x80) + 0x80)
          go (remaining `div` 0x80)

getUnsignedInteger :: Get Integer
getUnsignedInteger = go 0 0
  where
    go shift accumulator
      | shift > 16384 = fail "unbounded integer encoding is too large"
      | otherwise = do
          byte <- getWord8
          let payload = toInteger (byte .&. 0x7f)
              next = accumulator + payload * (2 ^ shift)
          if byte .&. 0x80 == 0
            then pure next
            else go (shift + 7) next

putVarWord64 :: Word64 -> Put
putVarWord64 = putUnsignedInteger . toInteger

getVarWord64 :: Get Word64
getVarWord64 = checkedIntegral "Word64" =<< getUnsignedInteger

checkedIntegral :: forall a. (Integral a, Bounded a) => String -> Integer -> Get a
checkedIntegral label integer
  | integer < toInteger (minBound :: a) || integer > toInteger (maxBound :: a) =
      fail (label <> " value is out of range")
  | otherwise = pure (fromInteger integer)
