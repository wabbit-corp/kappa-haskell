-- | Parser monad: a backtracking state monad over the token stream.
--
-- Alternation ('<|>') fully backtracks (state is restored on failure);
-- the grammar is written with explicit lookahead where ambiguity would
-- otherwise cause re-parsing blowups. Soft newlines (inside brackets,
-- §5.4) are skipped implicitly except when comprehension-clause parsing
-- requests them.
module Kappa.Parser.Monad
  ( P
  , PErr (..)
  , runP
  , parseFail
  , parseFailAt
  , peekToken
  , peekTokenAt
  , anyToken
  , satisfy
  , token
  , currentSpan
  , lastSpan
  , try
  , lookAheadIs
  , optionMaybe
  , many1
  , sepBy
  , sepBy1
  , keepSoftNewlines
  , hideSoftNewlines
  , noNamedBlock
  , namedBlockOk
  , withExtraStops
  , clearExtraStops
  , extraStops
  , noEq
  , eqAllowed
  , recordRecovered
  , recoveredSoFar
  , pendingTokens
  , skipPast
  , eof
  ) where

import Control.Applicative (Alternative (..))
import Data.Text (Text)
import Kappa.Diagnostic (Diagnostic)
import Kappa.Source (Pos (..), Span (..))
import Kappa.Token

data PState = PState
  { psToks :: ![Located]
  , psLast :: !Span
  , psSoftNL :: !Bool -- ^ True = soft newlines are significant
  , psEqOk :: !Bool -- ^ may '=' join an operator chain here? (§11.4.1)
  , psStopExtra :: ![Text] -- ^ context-sensitive stop keywords (§5.2)
  , psNoNamedBlock :: !Bool -- ^ suppress named-block arguments (§20.7 group keys)
  , psRecovered :: ![Diagnostic]
  }

-- | Parse error: position, message, expected alternatives.
data PErr = PErr
  { peSpan :: !Span
  , peMessage :: !Text
  , peExpected :: ![Text]
  }
  deriving stock (Show)

newtype P a = P {unP :: PState -> Either PErr (a, PState)}

instance Functor P where
  fmap f (P g) = P (fmap (\(a, s) -> (f a, s)) . g)

instance Applicative P where
  pure a = P (\s -> Right (a, s))
  P pf <*> P pa = P $ \s -> do
    (f, s1) <- pf s
    (a, s2) <- pa s1
    pure (f a, s2)

instance Monad P where
  P pa >>= k = P $ \s -> do
    (a, s1) <- pa s
    unP (k a) s1

instance Alternative P where
  empty = P $ \s -> Left (PErr (psLast s) "parse error" [])
  P pa <|> P pb = P $ \s -> case pa s of
    Right r -> Right r
    Left e1 -> case pb s of
      Right r -> Right r
      Left e2 -> Left (mergeErr e1 e2)

-- Prefer the error that progressed further into the input.
mergeErr :: PErr -> PErr -> PErr
mergeErr e1 e2
  | spanStart (peSpan e2) > spanStart (peSpan e1) = e2
  | spanStart (peSpan e1) > spanStart (peSpan e2) = e1
  | otherwise = e1 {peExpected = peExpected e1 <> peExpected e2}

runP :: P a -> [Located] -> Either PErr (a, [Diagnostic])
runP (P f) toks =
  case f (PState toks startSpan False True [] False []) of
    Left e -> Left e
    Right (a, s) -> Right (a, reverse (psRecovered s))
  where
    startSpan = case toks of
      (Located _ sp : _) -> sp
      [] -> Span "<empty>" (Pos 1 1) (Pos 1 1)

parseFail :: Text -> P a
parseFail msg = P $ \s -> Left (PErr (currentSpanOf s) msg [])

parseFailAt :: Span -> Text -> P a
parseFailAt sp msg = P $ \_ -> Left (PErr sp msg [])

currentSpanOf :: PState -> Span
currentSpanOf s = case visibleToks s of
  (Located _ sp : _) -> sp
  [] -> psLast s

-- | Token stream view with soft newlines elided (unless requested).
visibleToks :: PState -> [Located]
visibleToks s
  | psSoftNL s = psToks s
  | otherwise = dropSoft (psToks s)
  where
    dropSoft (Located (TokNewline True) _ : rest) = dropSoft rest
    dropSoft ts = ts

peekToken :: P Token
peekToken = P $ \s -> case visibleToks s of
  (Located t _ : _) -> Right (t, s)
  [] -> Right (TokEOF, s)

-- | Peek @n@ tokens ahead (0-based) in the visible stream.
peekTokenAt :: Int -> P Token
peekTokenAt n = P $ \s ->
  let go 0 (Located t _ : _) = t
      go k (_ : rest) = go (k - 1) (skipSoft s rest)
      go _ [] = TokEOF
      skipSoft st ts
        | psSoftNL st = ts
        | otherwise = dropWhile isSoft ts
      isSoft (Located (TokNewline True) _) = True
      isSoft _ = False
   in Right (go n (visibleToks s), s)

anyToken :: P Located
anyToken = P $ \s -> case visibleToks s of
  (l : rest) -> Right (l, s {psToks = rest, psLast = locSpan l})
  [] -> Left (PErr (psLast s) "unexpected end of input" [])

satisfy :: Text -> (Token -> Maybe a) -> P a
satisfy what f = P $ \s -> case visibleToks s of
  (Located t sp : rest) -> case f t of
    Just a -> Right (a, s {psToks = rest, psLast = sp})
    Nothing -> Left (PErr sp ("expected " <> what <> ", found " <> tokenDescr t) [what])
  [] -> Left (PErr (psLast s) ("expected " <> what <> " at end of input") [what])

token :: Token -> P ()
token t = satisfy (tokenDescr t) (\t' -> if t == t' then Just () else Nothing)

currentSpan :: P Span
currentSpan = P $ \s -> Right (currentSpanOf s, s)

lastSpan :: P Span
lastSpan = P $ \s -> Right (psLast s, s)

-- | Backtracking: on failure, input is restored (our '<|>' already
-- restores; 'try' exists for documentation and error-position control).
try :: P a -> P a
try (P f) = P f

lookAheadIs :: P a -> P Bool
lookAheadIs (P f) = P $ \s -> case f s of
  Right _ -> Right (True, s)
  Left _ -> Right (False, s)

optionMaybe :: P a -> P (Maybe a)
optionMaybe p = (Just <$> p) <|> pure Nothing

many1 :: P a -> P [a]
many1 p = (:) <$> p <*> many p

sepBy :: P a -> P sep -> P [a]
sepBy p sep = sepBy1 p sep <|> pure []

sepBy1 :: P a -> P sep -> P [a]
sepBy1 p sep = (:) <$> p <*> many (sep *> p)

-- | Run a parser with soft newlines visible (comprehension clauses).
keepSoftNewlines :: P a -> P a
keepSoftNewlines (P f) = P $ \s -> do
  (a, s') <- f s {psSoftNL = True}
  pure (a, s' {psSoftNL = psSoftNL s})

-- | Run a parser with soft newlines hidden again: bracketed
-- sub-expressions inside comprehension clauses are ordinary bracketed
-- syntax, so their internal newlines are soft (§5.4).
hideSoftNewlines :: P a -> P a
hideSoftNewlines (P f) = P $ \s -> do
  (a, s') <- f s {psSoftNL = False}
  pure (a, s' {psSoftNL = psSoftNL s})

-- | Suppress named-block arguments @f { x = 1 }@ while parsing a
-- position followed by a block-shaped clause body (§20.7 group keys).
noNamedBlock :: P a -> P a
noNamedBlock (P f) = P $ \s -> do
  (a, s') <- f s {psNoNamedBlock = True}
  pure (a, s' {psNoNamedBlock = psNoNamedBlock s})

-- | May a named-block argument be parsed here?
namedBlockOk :: P Bool
namedBlockOk = P $ \s -> Right (not (psNoNamedBlock s), s)

-- | Activate additional context-sensitive stop keywords while a clause
-- context is open (comprehension bodies, @decreases ... by@). Restored
-- on exit, so the keywords stay ordinary identifiers elsewhere (§5.2).
withExtraStops :: [Text] -> P a -> P a
withExtraStops ks (P f) = P $ \s -> do
  (a, s') <- f s {psStopExtra = ks <> psStopExtra s}
  pure (a, s' {psStopExtra = psStopExtra s})

-- | Deactivate context-sensitive stop keywords: bracketed sub-expressions
-- close the clause context, so soft keywords are identifiers again.
clearExtraStops :: P a -> P a
clearExtraStops (P f) = P $ \s -> do
  (a, s') <- f s {psStopExtra = []}
  pure (a, s' {psStopExtra = psStopExtra s})

-- | The currently active context-sensitive stop keywords.
extraStops :: P [Text]
extraStops = P $ \s -> Right (psStopExtra s, s)

-- | Parse with '=' excluded from operator chains: used for annotation
-- positions where '=' terminates the enclosing binding instead of
-- denoting propositional equality (§11.4.1 vs §9.1).
noEq :: P a -> P a
noEq (P f) = P $ \s -> do
  (a, s') <- f s {psEqOk = False}
  pure (a, s' {psEqOk = psEqOk s})

eqAllowed :: P Bool
eqAllowed = P $ \s -> Right (psEqOk s, s)

recordRecovered :: Diagnostic -> P ()
recordRecovered d = P $ \s -> Right ((), s {psRecovered = d : psRecovered s})

-- | The recovered diagnostics recorded so far (newest first).
recoveredSoFar :: P [Diagnostic]
recoveredSoFar = P $ \s -> Right (psRecovered s, s)

-- | The not-yet-consumed token stream (for recovery look-ahead).
pendingTokens :: P [Located]
pendingTokens = P $ \s -> Right (psToks s, s)

-- | Declaration-level recovery: drop tokens until the predicate holds at
-- nesting depth zero (tracking INDENT\/DEDENT and brackets), consuming
-- the offending region.
skipPast :: (Token -> Bool) -> P ()
skipPast stopAt = P $ \s -> Right ((), s {psToks = go (0 :: Int) (psToks s)})
  where
    go _ [] = []
    go depth ts@(Located t _ : rest)
      | depth <= 0, stopAt t = ts
      | otherwise = case t of
          TokIndent -> go (depth + 1) rest
          TokDedent -> go (depth - 1) rest
          TokEOF -> ts
          _ -> go depth rest

eof :: P ()
eof = P $ \s -> case visibleToks s of
  [] -> Right ((), s)
  (Located TokEOF _ : _) -> Right ((), s)
  (Located t sp : _) -> Left (PErr sp ("expected end of file, found " <> tokenDescr t) [])
