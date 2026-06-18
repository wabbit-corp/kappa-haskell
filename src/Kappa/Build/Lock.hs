-- | The build lockfile (@kappa.lock@) and path-dependency content
-- identity (§36.23.2, §36.4). A path dependency has no registry/digest
-- pin, so its reproducibility identity is an implementation-defined
-- content digest of its source (§36.23.2 "implementation-defined content
-- identity"). The lockfile records the resolved path-dependency closure
-- (each package's project-relative path + content identity) so a later
-- build can detect drift (§3.2.15 reproducibility).
--
-- The digest is a fast non-cryptographic content hash (FNV-1a 64) over a
-- length-prefixed, path-sorted encoding of the package's source files —
-- the framing is injective (file/path boundaries are unambiguous), so it
-- is a sound change-detection identity, though not a security primitive.
module Kappa.Build.Lock
  ( LockEntry (..)
  , contentId
  , renderLock
  , parseLock
  , lockWellFormed
  ) where

import Data.Bits (shiftR, xor)
import qualified Data.ByteString as BS
import Data.List (foldl', sortOn)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Encoding (encodeUtf8)
import Data.Word (Word64, Word8)
import Numeric (showHex)

-- | One resolved dependency in the lockfile. @leKind@ is @"path"@,
-- @"git"@, or @"registry"@; @leKey@ is the dependency's stable locator (a
-- project-relative path, a git URL, or the registry package name); @leId@
-- is its immutable identity (a content digest for a path dependency, the
-- resolved commit SHA for a git dependency, or @version+content-digest@
-- for a registry dependency).
data LockEntry = LockEntry
  { leKind :: !Text
  , leKey :: !Text
  , leId :: !Text
  }
  deriving stock (Eq, Show)

-- | The content identity of a package: a digest over its source files
-- (each contributing its package-relative path and its bytes), in a
-- canonical (path-sorted) order so the identity is independent of
-- enumeration order. Each path and each content blob is length-prefixed
-- so the byte stream is unambiguously decodable (no cross-file or
-- path/content boundary aliasing).
contentId :: [(FilePath, BS.ByteString)] -> Text
contentId files =
  let sorted = sortOn fst files
      h = foldl' step (hashChunk fnvOffset (lenBytes (length sorted))) sorted
   in T.pack (pad16 (showHex h ""))
  where
    step acc (p, bytes) = hashChunk (hashChunk acc (encodeUtf8 (T.pack p))) bytes
    pad16 s = replicate (16 - length s) '0' ++ s

-- | FNV-1a over a length-prefixed chunk (8-byte big-endian length, then
-- the bytes) — the length prefix makes concatenation injective.
hashChunk :: Word64 -> BS.ByteString -> Word64
hashChunk acc chunk = hashBytes (hashBytes acc (lenBytes (BS.length chunk))) chunk

lenBytes :: Int -> BS.ByteString
lenBytes n = BS.pack [fromIntegral (fromIntegral n `shiftR` (8 * i) :: Word64) | i <- [7, 6 .. 0]]

fnvOffset :: Word64
fnvOffset = 14695981039346656037

fnvPrime :: Word64
fnvPrime = 1099511628211

hashByte :: Word64 -> Word8 -> Word64
hashByte acc b = (acc `xor` fromIntegral b) * fnvPrime

hashBytes :: Word64 -> BS.ByteString -> Word64
hashBytes = BS.foldl' hashByte

-- ── lockfile format ──────────────────────────────────────────────────

lockHeader :: Text
lockHeader = "# kappa.lock v1 (generated; records resolved path-dependency content identities)"

-- | A content line is @<kind> <id> <key>@. The kind and identity come
-- first (tokens with no spaces) so the key (a path, which may contain
-- spaces) is the remainder of the line verbatim.
renderLock :: [LockEntry] -> Text
renderLock entries =
  T.unlines
    ( lockHeader
        : [ leKind e <> " " <> leId e <> " " <> leKey e
          | e <- sortOn (\e -> (leKey e, leKind e)) entries
          ]
    )

-- | Parse a lockfile into entries (sorted), ignoring blank lines and @#@
-- comments. Malformed content lines are dropped here; use 'lockWellFormed'
-- to detect them.
parseLock :: Text -> [LockEntry]
parseLock txt =
  sortOn (\e -> (leKey e, leKind e)) [e | Just e <- map parseLine (contentLines txt)]

-- | True iff every content (non-blank, non-comment) line is a valid
-- entry — used to distinguish an absent lock from a corrupt one.
lockWellFormed :: Text -> Bool
lockWellFormed txt = all (\l -> parseLine l /= Nothing) (contentLines txt)

contentLines :: Text -> [Text]
contentLines txt =
  [ ln
  | raw <- T.lines txt
  , let ln = T.strip raw
  , not (T.null ln)
  , not ("#" `T.isPrefixOf` ln)
  ]

-- | The dependency kinds that may appear in a lockfile. Keep in sync with
-- the lock entries produced by "Kappa.Build.Plan" (path/git/registry/url).
lockKinds :: [Text]
lockKinds = ["path", "git", "registry", "url"]

parseLine :: Text -> Maybe LockEntry
parseLine ln =
  let (k, r1) = T.breakOn " " ln
      (i, r2) = T.breakOn " " (T.drop 1 r1)
      key = T.drop 1 r2
   in if k `elem` lockKinds && not (T.null i) && not (T.null key)
        then Just (LockEntry k key i)
        else Nothing
