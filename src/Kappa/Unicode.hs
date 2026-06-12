-- | Unicode text algorithms over the embedded UCD tables
-- ("Kappa.UnicodeData", UCD 15.0.0): normalization (§29.4),
-- extended-grapheme-cluster segmentation (§6.5, UAX #29), and the
-- optional source-hygiene scans (§3.1.12).
--
-- Precision notes (documented per §29.4 "the implementation MUST
-- document the Unicode version used"):
--
--   * NFC\/NFD\/NFKC\/NFKD use the full canonical\/compatibility
--     decomposition tables, canonical reordering, and primary-composite
--     recomposition with the standard composition exclusions and Hangul
--     handled algorithmically — complete UAX #15 behavior for UCD 15.0.0.
--   * Grapheme segmentation implements UAX #29 GB1–GB13\/GB999 with
--     class data derived as described in tools\/gen-unicode-data.py
--     (Extended_Pictographic and the Prepend Indic component are
--     vendored snapshots of the 15.0 data files).
--   * 'wordChunks' and 'sentenceChunks' are documented simple
--     approximations (whitespace words; terminator-punctuation
--     sentences), not UAX #29 word\/sentence segmentation.
module Kappa.Unicode
  ( unicodeVersionTriple
  , NormForm (..)
  , normalizeText
  , graphemeClusters
  , isSingleGrapheme
  , wordChunks
  , sentenceChunks
  , isBidiControl
  , confusableWithAscii
  , isNfcQuick
  ) where

import Data.Char (chr, ord)
import qualified Data.IntMap.Strict as IM
import Data.List (sortBy)
import qualified Data.Map.Strict as Map
import Data.Ord (comparing)
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.UnicodeData

unicodeVersionTriple :: (Int, Int, Int)
unicodeVersionTriple = unicodeDataVersion

-- ── Normalization (UAX #15) ──────────────────────────────────────────

data NormForm = NFC | NFD | NFKC | NFKD
  deriving stock (Eq, Show)

cccMap :: IM.IntMap Int
cccMap = IM.fromList combiningClassTable

ccc :: Char -> Int
ccc c = IM.findWithDefault 0 (ord c) cccMap

canonMap :: IM.IntMap [Char]
canonMap = IM.fromList [(cp, map chr cs) | (cp, cs) <- canonicalDecompTable]

compatMap :: IM.IntMap [Char]
compatMap = IM.fromList [(cp, map chr cs) | (cp, cs) <- compatDecompTable]

compMap :: Map.Map (Int, Int) Int
compMap = Map.fromList compositionTable

-- Hangul constants (UAX #15 §3.12)
sBase, lBase, vBase, tBase, vCount, tCount, nCount, sCount :: Int
sBase = 0xAC00
lBase = 0x1100
vBase = 0x1161
tBase = 0x11A7
vCount = 21
tCount = 28
nCount = vCount * tCount
sCount = 11172

isHangulSyllable :: Char -> Bool
isHangulSyllable c = let n = ord c in n >= sBase && n < sBase + sCount

decomposeHangul :: Char -> [Char]
decomposeHangul c =
  let sIndex = ord c - sBase
      l = lBase + sIndex `div` nCount
      v = vBase + (sIndex `mod` nCount) `div` tCount
      t = tBase + sIndex `mod` tCount
   in chr l : chr v : [chr t | t /= tBase]

decomposeChar :: Bool -> Char -> [Char]
decomposeChar compat c
  | isHangulSyllable c = decomposeHangul c
  | compat, Just d <- IM.lookup (ord c) compatMap = d
  | Just d <- IM.lookup (ord c) canonMap = d
  | otherwise = [c]

-- Canonical ordering: stable sort of each maximal run of nonzero-ccc
-- characters by combining class.
canonicalOrder :: [Char] -> [Char]
canonicalOrder [] = []
canonicalOrder cs =
  case span ((== 0) . ccc) cs of
    (starters, []) -> starters
    (starters, rest) ->
      let (marks, rest') = span ((/= 0) . ccc) rest
       in starters ++ sortBy (comparing ccc) marks ++ canonicalOrder rest'

-- Primary composition (UAX #15 §3.11, D117): after full decomposition
-- and canonical ordering, combine each starter with following
-- non-blocked characters.
composeChars :: [Char] -> [Char]
composeChars [] = []
composeChars (c0 : rest0) = go c0 [] rest0
  where
    go starter pending [] = starter : reverse pending
    go starter pending (c : cs)
      | ccc c == 0 && null pending
      , Just comp <- composePair starter c =
          go comp [] cs
      | not (blocked pending c)
      , ccc c /= 0
      , Just comp <- composePair starter c =
          go comp pending cs
      | ccc c == 0 =
          (starter : reverse pending) ++ go c [] cs
      | otherwise = go starter (c : pending) cs
    blocked pending c = case pending of
      [] -> False
      (p : _) -> ccc p >= ccc c

composePair :: Char -> Char -> Maybe Char
composePair a b
  -- Hangul LV / LVT composition
  | la >= lBase && la < lBase + 19
  , lb >= vBase && lb < vBase + vCount =
      Just (chr (sBase + ((la - lBase) * vCount + (lb - vBase)) * tCount))
  | la >= sBase && la < sBase + sCount
  , (la - sBase) `mod` tCount == 0
  , lb > tBase && lb < tBase + tCount =
      Just (chr (la + (lb - tBase)))
  | otherwise = chr <$> Map.lookup (la, lb) compMap
  where
    la = ord a
    lb = ord b

normalizeText :: NormForm -> Text -> Text
normalizeText form t =
  let compat = form == NFKC || form == NFKD
      decomposed = canonicalOrder (concatMap (fullDecompose compat) (T.unpack t))
   in T.pack $
        if form == NFC || form == NFKC
          then composeChars decomposed
          else decomposed
  where
    -- tables are fully expanded; one step suffices except for compat
    -- entries whose expansion contains canonically decomposable chars
    fullDecompose compat c = case decomposeChar compat c of
      [c'] | c' == c -> [c]
      ds -> concatMap (fullDecompose compat) ds

-- | Fast NFC pre-check for source-hygiene scanning: all characters
-- below U+0300 are NFC-stable starters with no decomposition.
isNfcQuick :: Text -> Bool
isNfcQuick t
  | T.all (< '\x0300') t = True
  | otherwise = normalizeText NFC t == t

-- ── Grapheme cluster segmentation (UAX #29) ─────────────────────────

gcbMap :: Map.Map Int (Int, Int)
gcbMap = Map.fromList [(lo, (hi, cls)) | (lo, hi, cls) <- gcbRangeTable]

data GcbClass
  = GcOther
  | GcCR
  | GcLF
  | GcControl
  | GcExtend
  | GcZWJ
  | GcRI
  | GcPrepend
  | GcSpacingMark
  | GcExtPict
  | GcL
  | GcV
  | GcT
  | GcLV
  | GcLVT
  deriving stock (Eq)

gcbOf :: Char -> GcbClass
gcbOf c
  -- Hangul jamo and syllables, algorithmically
  | (n >= 0x1100 && n <= 0x115F) || (n >= 0xA960 && n <= 0xA97C) = GcL
  | (n >= 0x1160 && n <= 0x11A7) || (n >= 0xD7B0 && n <= 0xD7C6) = GcV
  | (n >= 0x11A8 && n <= 0x11FF) || (n >= 0xD7CB && n <= 0xD7FB) = GcT
  | isHangulSyllable c = if (n - sBase) `mod` tCount == 0 then GcLV else GcLVT
  | otherwise = case Map.lookupLE n gcbMap of
      Just (_, (hi, cls)) | n <= hi -> classOf cls
      _ -> GcOther
  where
    n = ord c
    classOf = \case
      1 -> GcCR
      2 -> GcLF
      3 -> GcControl
      4 -> GcExtend
      5 -> GcZWJ
      6 -> GcRI
      7 -> GcPrepend
      8 -> GcSpacingMark
      9 -> GcExtPict
      _ -> GcOther

-- Segmentation state for the lookback-sensitive rules: GB11 (emoji ZWJ
-- sequences) and GB12/13 (regional-indicator pairs).
data SegState = SegState
  { ssPictExtend :: !Bool -- tail matches ExtPict Extend* (GB11)
  , ssPictZWJ :: !Bool -- tail matches ExtPict Extend* ZWJ (GB11)
  , ssRiRun :: !Int -- parity counter of preceding RI characters
  }

-- | Split text into extended grapheme clusters (UAX #29, GB1–GB999).
graphemeClusters :: Text -> [Text]
graphemeClusters t = go (T.unpack t)
  where
    go [] = []
    go (c : cs) =
      let (cluster, rest) = grow (gcbOf c) (initState (gcbOf c)) [c] cs
       in T.pack (reverse cluster) : go rest

    initState cls =
      SegState
        { ssPictExtend = cls == GcExtPict
        , ssPictZWJ = False
        , ssRiRun = if cls == GcRI then 1 else 0
        }

    grow _ _ acc [] = (acc, [])
    grow prevCls st acc (c : cs)
      | breakBetween prevCls st cls = (acc, c : cs)
      | otherwise = grow cls (step cls st) (c : acc) cs
      where
        cls = gcbOf c

    step cls st =
      SegState
        { ssPictExtend = case cls of
            GcExtPict -> True
            GcExtend -> ssPictExtend st
            _ -> False
        , ssPictZWJ = cls == GcZWJ && ssPictExtend st
        , ssRiRun = if cls == GcRI then ssRiRun st + 1 else 0
        }

    breakBetween prevCls st cls
      -- GB3: CR x LF
      | prevCls == GcCR && cls == GcLF = False
      -- GB4 / GB5
      | prevCls `elem` [GcControl, GcCR, GcLF] = True
      | cls `elem` [GcControl, GcCR, GcLF] = True
      -- GB6/7/8: Hangul
      | prevCls == GcL && cls `elem` [GcL, GcV, GcLV, GcLVT] = False
      | prevCls `elem` [GcLV, GcV] && cls `elem` [GcV, GcT] = False
      | prevCls `elem` [GcLVT, GcT] && cls == GcT = False
      -- GB9 / GB9a / GB9b
      | cls == GcExtend || cls == GcZWJ = False
      | cls == GcSpacingMark = False
      | prevCls == GcPrepend = False
      -- GB11: ExtPict Extend* ZWJ x ExtPict
      | prevCls == GcZWJ && cls == GcExtPict && ssPictZWJ st = False
      -- GB12/GB13: do not break between RI when an odd number of
      -- regional indicators precedes the break point
      | prevCls == GcRI && cls == GcRI = even (ssRiRun st)
      -- GB999
      | otherwise = True

-- | Exactly one extended grapheme cluster (the §6.5 @g@ handler test).
isSingleGrapheme :: Text -> Bool
isSingleGrapheme t = case graphemeClusters t of
  [_] -> True
  _ -> False

-- ── Word / sentence chunks (documented approximations, §29.4) ────────

wordChunks :: Text -> [Text]
wordChunks = T.words

sentenceChunks :: Text -> [Text]
sentenceChunks t0 = filter (not . T.null) (map T.strip (go t0))
  where
    go t
      | T.null t = []
      | otherwise =
          case T.findIndex (`elem` (".!?" :: String)) t of
            Nothing -> [t]
            Just i ->
              let (s, rest) = T.splitAt (i + 1) t
               in s : go rest

-- ── Source hygiene scans (§3.1.12 optional warnings) ─────────────────

-- | Bidirectional control characters (UAX #9 explicit formatting plus
-- the implicit marks and ALM).
isBidiControl :: Char -> Bool
isBidiControl c =
  c == '\x061C'
    || c == '\x200E'
    || c == '\x200F'
    || (c >= '\x202A' && c <= '\x202E')
    || (c >= '\x2066' && c <= '\x2069')

-- | A small homoglyph skeleton: non-ASCII letters visually identical to
-- an ASCII letter in common fonts (Cyrillic and Greek lookalikes). Used
-- by the optional confusable-identifier warning; deliberately
-- conservative so ordinary non-Latin identifiers (e.g. @λ@) never warn.
confusableWithAscii :: Char -> Maybe Char
confusableWithAscii c = lookup c table
  where
    table =
      -- Cyrillic lowercase / uppercase
      [ ('\x0430', 'a'), ('\x0435', 'e'), ('\x043E', 'o'), ('\x0440', 'p')
      , ('\x0441', 'c'), ('\x0443', 'y'), ('\x0445', 'x'), ('\x0455', 's')
      , ('\x0456', 'i'), ('\x0458', 'j'), ('\x051B', 'q'), ('\x051D', 'w')
      , ('\x0410', 'A'), ('\x0412', 'B'), ('\x0415', 'E'), ('\x041A', 'K')
      , ('\x041C', 'M'), ('\x041D', 'H'), ('\x041E', 'O'), ('\x0420', 'P')
      , ('\x0421', 'C'), ('\x0422', 'T'), ('\x0425', 'X')
      , -- Greek lookalikes
        ('\x03BF', 'o'), ('\x0391', 'A'), ('\x0392', 'B'), ('\x0395', 'E')
      , ('\x0396', 'Z'), ('\x0397', 'H'), ('\x0399', 'I'), ('\x039A', 'K')
      , ('\x039C', 'M'), ('\x039D', 'N'), ('\x039F', 'O'), ('\x03A1', 'P')
      , ('\x03A4', 'T'), ('\x03A5', 'Y'), ('\x03A7', 'X')
      ]
