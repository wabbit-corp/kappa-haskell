-- | Minimal ECMAScript-style regular expressions for
-- @assertDiagnosticMatch@ (Spec §T.5.1).
--
-- Supported subset (sufficient for the conformance corpora): literal
-- characters, @.@, character classes @[...]@ (ranges, negation, and the
-- @\\d \\w \\s@ shorthands), grouping @(...)@ (capturing and @(?:...)@
-- alike, no backreferences), alternation @|@, the quantifiers @* + ?@
-- and bounded @{m}, {m,}, {m,n}@ (all greedy, with backtracking), the
-- anchors @^@ and @$@, the word-boundary assertions @\\b@ and @\\B@,
-- and identity escapes for punctuation. Matching is a search: the
-- pattern may match anywhere in the subject (anchor explicitly with
-- @^...$@ for a whole-string match).
module Kappa.Regex
  ( Regex
  , compileRegex
  , regexSearch
  ) where

import Data.Char (chr, isAlphaNum, isDigit, isSpace)
import Data.Text (Text)
import qualified Data.Text as T

-- ── AST ──────────────────────────────────────────────────────────────

newtype Regex = Regex Node

data Node
  = NChar !Char
  | NAny -- ^ @.@ — any character except a line terminator
  | NClass !Bool ![ClassItem] -- ^ negated?, members
  | NSeq ![Node]
  | NAlt ![Node]
  | NRepeat !Node !Int !(Maybe Int) -- ^ greedy @{m,n}@; @* + ?@ desugar here
  | NBol
  | NEol
  | NWordB !Bool -- ^ @\\b@ (True) \/ @\\B@ (False)

data ClassItem
  = CIChar !Char
  | CIRange !Char !Char
  | CIDigit !Bool -- ^ @\\d@ \/ @\\D@
  | CIWord !Bool -- ^ @\\w@ \/ @\\W@
  | CISpace !Bool -- ^ @\\s@ \/ @\\S@

-- ── Parser ───────────────────────────────────────────────────────────

-- | Compile a pattern; 'Left' is a human-readable syntax error.
compileRegex :: Text -> Either Text Regex
compileRegex pat = do
  (n, restT) <- parseAlt (T.unpack pat)
  case restT of
    [] -> Right (Regex n)
    (c : _) -> Left ("unexpected '" <> T.singleton c <> "' in pattern")

type P a = Either Text (a, String)

parseAlt :: String -> P Node
parseAlt s0 = do
  (first, s1) <- parseSeq s0
  go [first] s1
  where
    go acc ('|' : s) = do
      (n, s') <- parseSeq s
      go (n : acc) s'
    go [one] s = Right (one, s)
    go acc s = Right (NAlt (reverse acc), s)

parseSeq :: String -> P Node
parseSeq = go []
  where
    go acc s = case s of
      [] -> stop acc s
      (')' : _) -> stop acc s
      ('|' : _) -> stop acc s
      _ -> do
        (n, s1) <- parseAtom s
        (n', s2) <- parseQuant n s1
        go (n' : acc) s2
    stop [one] s = Right (one, s)
    stop acc s = Right (NSeq (reverse acc), s)

parseQuant :: Node -> String -> P Node
parseQuant n s = case s of
  ('*' : r) -> Right (NRepeat n 0 Nothing, r)
  ('+' : r) -> Right (NRepeat n 1 Nothing, r)
  ('?' : r) -> Right (NRepeat n 0 (Just 1), r)
  ('{' : r)
    | Just (lo, mhi, r') <- braces r -> Right (NRepeat n lo mhi, r')
  _ -> Right (n, s)
  where
    -- {m}, {m,}, {m,n}; anything else is a literal brace (ECMAScript)
    braces r = do
      (lo, r1) <- digits r
      case r1 of
        ('}' : r2) -> Just (lo, Just lo, r2)
        (',' : '}' : r2) -> Just (lo, Nothing, r2)
        (',' : r2) -> do
          (hi, r3) <- digits r2
          case r3 of
            ('}' : r4) -> Just (lo, Just hi, r4)
            _ -> Nothing
        _ -> Nothing
    digits r = case span isDigit r of
      ("", _) -> Nothing
      (ds, r') ->
        -- parse through Integer and range-check: a count that overflows
        -- Int is not a well-formed quantifier bound, so (per ECMAScript)
        -- the brace run is treated as a literal, not silently wrapped.
        let v = read ds :: Integer
         in if v > toInteger (maxBound :: Int)
              then Nothing
              else Just (fromInteger v :: Int, r')

parseAtom :: String -> P Node
parseAtom s = case s of
  [] -> Left "dangling quantifier or empty atom"
  ('^' : r) -> Right (NBol, r)
  ('$' : r) -> Right (NEol, r)
  ('.' : r) -> Right (NAny, r)
  ('(' : '?' : ':' : r) -> group r
  ('(' : r) -> group r
  ('[' : r) -> parseClass r
  ('\\' : c : r) -> (,r) <$> escape c
  ('\\' : []) -> Left "trailing backslash"
  ('*' : _) -> Left "quantifier '*' with nothing to repeat"
  ('+' : _) -> Left "quantifier '+' with nothing to repeat"
  ('?' : _) -> Left "quantifier '?' with nothing to repeat"
  (c : r) -> Right (NChar c, r)
  where
    group r = do
      (n, r1) <- parseAlt r
      case r1 of
        (')' : r2) -> Right (n, r2)
        _ -> Left "unterminated group"

escape :: Char -> Either Text Node
escape c = case c of
  'b' -> Right (NWordB True)
  'B' -> Right (NWordB False)
  'd' -> Right (NClass False [CIDigit True])
  'D' -> Right (NClass False [CIDigit False])
  'w' -> Right (NClass False [CIWord True])
  'W' -> Right (NClass False [CIWord False])
  's' -> Right (NClass False [CISpace True])
  'S' -> Right (NClass False [CISpace False])
  'n' -> Right (NChar '\n')
  't' -> Right (NChar '\t')
  'r' -> Right (NChar '\r')
  'f' -> Right (NChar '\f')
  'v' -> Right (NChar '\v')
  '0' -> Right (NChar '\0')
  _ -> Right (NChar c) -- identity escape (punctuation etc.)

parseClass :: String -> P Node
parseClass s0 =
  let (neg, s1) = case s0 of
        ('^' : r) -> (True, r)
        _ -> (False, s0)
   in go neg [] s1 True
  where
    go _ _ [] _ = Left "unterminated character class"
    go neg acc (']' : r) first
      | first = go neg (CIChar ']' : acc) r False
      | otherwise = Right (NClass neg (reverse acc), r)
    go neg acc s _ = do
      (item, r) <- classAtom s
      case r of
        ('-' : r1@(c : _))
          | c /= ']'
          , CIChar lo <- item -> do
              (hi, r2) <- classAtom r1
              case hi of
                CIChar hiC -> go neg (CIRange lo hiC : acc) r2 False
                _ -> Left "invalid range endpoint in character class"
        _ -> go neg (item : acc) r False
    classAtom ('\\' : c : r) = case c of
      'd' -> Right (CIDigit True, r)
      'D' -> Right (CIDigit False, r)
      'w' -> Right (CIWord True, r)
      'W' -> Right (CIWord False, r)
      's' -> Right (CISpace True, r)
      'S' -> Right (CISpace False, r)
      'n' -> Right (CIChar '\n', r)
      't' -> Right (CIChar '\t', r)
      'r' -> Right (CIChar '\r', r)
      'b' -> Right (CIChar (chr 8), r)
      _ -> Right (CIChar c, r)
    classAtom ('\\' : []) = Left "trailing backslash in character class"
    classAtom (c : r) = Right (CIChar c, r)
    classAtom [] = Left "unterminated character class"

-- ── Matcher ──────────────────────────────────────────────────────────

-- | Cursor: previous character (for anchors\/word boundaries) and the
-- remaining input.
data Cur = Cur !(Maybe Char) !String

-- | Unanchored search over the subject text.
regexSearch :: Regex -> Text -> Bool
regexSearch (Regex n) subject = any try starts
  where
    str = T.unpack subject
    starts = scanl step (Cur Nothing str) str
    step (Cur _ s) _ = case s of
      (c : r) -> Cur (Just c) r
      [] -> Cur Nothing []
    try cur = matchNode n cur (const True)

matchNode :: Node -> Cur -> (Cur -> Bool) -> Bool
matchNode node cur@(Cur prev s) k = case node of
  NChar c -> case s of
    (x : r) | x == c -> k (Cur (Just x) r)
    _ -> False
  NAny -> case s of
    (x : r) | x /= '\n' && x /= '\r' -> k (Cur (Just x) r)
    _ -> False
  NClass neg items -> case s of
    (x : r) | classMember items x /= neg -> k (Cur (Just x) r)
    _ -> False
  NSeq ns -> matchSeq ns cur k
  NAlt ns -> any (\alt -> matchNode alt cur k) ns
  NRepeat inner lo mhi -> matchRepeat inner lo mhi cur k
  NBol -> prev == Nothing && k cur
  NEol -> null s && k cur
  NWordB want -> (isBoundary == want) && k cur
    where
      isBoundary = isWordC prev /= isWordC (headM s)
      headM (x : _) = Just x
      headM [] = Nothing
      isWordC = maybe False (\c -> isAlphaNum c || c == '_')

matchSeq :: [Node] -> Cur -> (Cur -> Bool) -> Bool
matchSeq [] cur k = k cur
matchSeq (n : ns) cur k = matchNode n cur (\cur' -> matchSeq ns cur' k)

-- Greedy bounded repetition with backtracking. A zero-width inner match
-- terminates the recursion (no progress, no further repetition).
matchRepeat :: Node -> Int -> Maybe Int -> Cur -> (Cur -> Bool) -> Bool
matchRepeat inner lo mhi cur k = go 0 cur
  where
    go i c@(Cur _ s)
      | maybe False (i >=) mhi = k c
      | otherwise =
          let more =
                matchNode inner c $ \c'@(Cur _ s') ->
                  length s' < length s && go (i + 1) c'
              stop = i >= lo && k c
           in more || stop

classMember :: [ClassItem] -> Char -> Bool
classMember items c = any member items
  where
    member = \case
      CIChar x -> c == x
      CIRange lo hi -> lo <= c && c <= hi
      CIDigit pos -> isDigit c == pos
      CIWord pos -> (isAlphaNum c || c == '_') == pos
      CISpace pos -> isSpace c == pos
