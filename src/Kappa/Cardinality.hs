-- | Canonical symbolic cardinalities (§30.2.7A).
--
-- Cardinality expressions are analysis objects, not source terms or equality
-- proofs. 'CardIndex' stores a total stable Nat KCore term in its lexical
-- context; open variables are therefore represented by De Bruijn indices and
-- remain stable under alpha-renaming. Smart constructors keep addition and
-- multiplication flattened, sorted, and constant-folded with exact 'Natural'
-- arithmetic.
module Kappa.Cardinality
  ( CardConstraint (..)
  , CardExpr (..)
  , CardUpper (..)
  , SymbolicCardinalitySummary (..)
  , cardLiteral
  , cardIndex
  , cardAdd
  , cardMul
  , cardPowLiteral
  , cardGuardedSub
  , cardIf
  , normalizeCardExpr
  , renderCardExpr
  , cardinalityIdentity
  , parseCardExpr
  ) where

import Data.Char (isAlpha, isAlphaNum, isDigit)
import Data.List (partition, sortOn)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Core (Term)
import Kappa.Pretty (renderTerm)
import Kappa.SemanticHash (canonicalIdentityHex)
import Numeric.Natural (Natural)

data CardConstraint
  = CardLe !CardExpr !CardExpr
  deriving stock (Eq, Show)

data CardExpr
  = CardLiteral !Natural
  | CardIndex !Term
  | CardAdd !CardExpr !CardExpr
  | CardMul !CardExpr !CardExpr
  | CardPowLiteral !CardExpr !Natural
  | CardGuardedSub !CardExpr !CardExpr
  | CardIf !CardConstraint !CardExpr !CardExpr
  deriving stock (Eq, Show)

data CardUpper
  = FiniteCardinality !CardExpr
  | UnboundedCardinality
  deriving stock (Eq, Show)

data SymbolicCardinalitySummary
  = NoSymbolicCardinality
  | ExactCardinality !CardExpr
  | SymbolicBounds !CardExpr !CardUpper
  deriving stock (Eq, Show)

cardLiteral :: Natural -> CardExpr
cardLiteral = CardLiteral

cardIndex :: Term -> CardExpr
cardIndex = CardIndex

cardAdd :: CardExpr -> CardExpr -> CardExpr
cardAdd left right = normalizeSum [left, right]

cardMul :: CardExpr -> CardExpr -> CardExpr
cardMul left right = normalizeProduct [left, right]

cardPowLiteral :: CardExpr -> Natural -> CardExpr
cardPowLiteral base exponent = normalizeCardExpr (CardPowLiteral base exponent)

cardGuardedSub :: CardExpr -> CardExpr -> CardExpr
cardGuardedSub left right = normalizeCardExpr (CardGuardedSub left right)

cardIf :: CardConstraint -> CardExpr -> CardExpr -> CardExpr
cardIf constraint yes no = normalizeCardExpr (CardIf constraint yes no)

normalizeCardExpr :: CardExpr -> CardExpr
normalizeCardExpr = \case
  literal@CardLiteral {} -> literal
  index@CardIndex {} -> index
  CardAdd left right -> normalizeSum [left, right]
  CardMul left right -> normalizeProduct [left, right]
  CardPowLiteral base exponent ->
    case (normalizeCardExpr base, exponent) of
      (_, 0) -> CardLiteral 1
      (normalized, 1) -> normalized
      (CardLiteral value, power) -> CardLiteral (value ^ power)
      (normalized, power) -> CardPowLiteral normalized power
  CardGuardedSub left right ->
    case (normalizeCardExpr left, normalizeCardExpr right) of
      (CardLiteral lhs, CardLiteral rhs)
        | rhs <= lhs -> CardLiteral (lhs - rhs)
      (lhs, rhs)
        | lhs == rhs -> CardLiteral 0
        | otherwise -> CardGuardedSub lhs rhs
  CardIf constraint yes no ->
    let normalizedConstraint = normalizeConstraint constraint
        normalizedYes = normalizeCardExpr yes
        normalizedNo = normalizeCardExpr no
     in if normalizedYes == normalizedNo
          then normalizedYes
          else case normalizedConstraint of
            CardLe (CardLiteral lhs) (CardLiteral rhs) ->
              if lhs <= rhs then normalizedYes else normalizedNo
            _ -> CardIf normalizedConstraint normalizedYes normalizedNo

normalizeConstraint :: CardConstraint -> CardConstraint
normalizeConstraint (CardLe left right) =
  CardLe (normalizeCardExpr left) (normalizeCardExpr right)

normalizeSum :: [CardExpr] -> CardExpr
normalizeSum expressions =
  rebuild CardAdd (literalTerms ++ orderedTerms)
  where
    flattened = concatMap flattenAdd (map normalizeCardExpr expressions)
    (literals, terms) = partition isLiteral flattened
    literalTotal = sum [value | CardLiteral value <- literals]
    literalTerms = [CardLiteral literalTotal | literalTotal /= 0 || null terms]
    orderedTerms = sortOn canonicalPayload [term | term <- terms, term /= CardLiteral 0]
    rebuild _ [only] = only
    rebuild constructor (first : rest) = foldl constructor first rest
    rebuild _ [] = CardLiteral 0

normalizeProduct :: [CardExpr] -> CardExpr
normalizeProduct expressions
  | any (== CardLiteral 0) flattened = CardLiteral 0
  | otherwise = rebuild CardMul (literalTerms ++ orderedTerms)
  where
    flattened = concatMap flattenMul (map normalizeCardExpr expressions)
    (literals, terms) = partition isLiteral flattened
    literalTotal = product [value | CardLiteral value <- literals]
    literalTerms = [CardLiteral literalTotal | literalTotal /= 1 || null terms]
    orderedTerms = sortOn canonicalPayload [term | term <- terms, term /= CardLiteral 1]
    rebuild _ [only] = only
    rebuild constructor (first : rest) = foldl constructor first rest
    rebuild _ [] = CardLiteral 1

flattenAdd :: CardExpr -> [CardExpr]
flattenAdd (CardAdd left right) = flattenAdd left ++ flattenAdd right
flattenAdd expression = [expression]

flattenMul :: CardExpr -> [CardExpr]
flattenMul (CardMul left right) = flattenMul left ++ flattenMul right
flattenMul expression = [expression]

isLiteral :: CardExpr -> Bool
isLiteral CardLiteral {} = True
isLiteral _ = False

-- | Canonical machine-oriented serialization. It intentionally renders
-- 'CardIndex' through canonical Core pretty-printing rather than a source
-- spelling.
canonicalPayload :: CardExpr -> Text
canonicalPayload = \case
  CardLiteral value -> "lit(" <> T.pack (show value) <> ")"
  CardIndex term -> "idx(" <> renderTerm term <> ")"
  CardAdd left right -> "add(" <> canonicalPayload left <> "," <> canonicalPayload right <> ")"
  CardMul left right -> "mul(" <> canonicalPayload left <> "," <> canonicalPayload right <> ")"
  CardPowLiteral base exponent ->
    "pow(" <> canonicalPayload base <> "," <> T.pack (show exponent) <> ")"
  CardGuardedSub left right ->
    "sub(" <> canonicalPayload left <> "," <> canonicalPayload right <> ")"
  CardIf constraint yes no ->
    "if(" <> canonicalConstraint constraint <> "," <> canonicalPayload yes <> "," <> canonicalPayload no <> ")"

canonicalConstraint :: CardConstraint -> Text
canonicalConstraint (CardLe left right) =
  "le(" <> canonicalPayload left <> "," <> canonicalPayload right <> ")"

renderCardExpr :: CardExpr -> Text
renderCardExpr = go 0 . normalizeCardExpr
  where
    go precedence = \case
      CardLiteral value -> T.pack (show value)
      CardIndex term -> renderTerm term
      CardAdd left right ->
        parenthesize (precedence > 1) (go 1 left <> " + " <> go 1 right)
      CardMul left right ->
        parenthesize (precedence > 2) (go 2 left <> " * " <> go 2 right)
      CardPowLiteral base exponent ->
        parenthesize (precedence > 3) (go 3 base <> " ^ " <> T.pack (show exponent))
      CardGuardedSub left right ->
        parenthesize (precedence > 1) (go 1 left <> " - " <> go 2 right)
      CardIf (CardLe left right) yes no ->
        parenthesize
          (precedence > 0)
          ("if " <> go 0 left <> " <= " <> go 0 right
            <> " then " <> go 0 yes <> " else " <> go 0 no)
    parenthesize True text = "(" <> text <> ")"
    parenthesize False text = text

cardinalityIdentity :: CardExpr -> Text
cardinalityIdentity =
  canonicalIdentityHex "Cardinality" . canonicalPayload . normalizeCardExpr

-- | Parse the Appendix-T readable cardinality grammar into the same typed AST
-- used by compiler queries. Identifier resolution is supplied by the caller as
-- scope-indexed KCore Nat terms; unknown names are rejected.
parseCardExpr :: Map Text Term -> Text -> Either Text CardExpr
parseCardExpr indexes source = do
  tokens <- tokenize source
  (expression, rest) <- parseExpression tokens
  case rest of
    [] -> Right (normalizeCardExpr expression)
    token : _ -> Left ("unexpected cardinality token '" <> token <> "'")
  where
    parseExpression ("if" : rest) = do
      (left, afterLeft) <- parseAdditive rest
      afterLe <- expect "<=" afterLeft
      (right, afterRight) <- parseAdditive afterLe
      afterThen <- expect "then" afterRight
      (yes, afterYes) <- parseExpression afterThen
      afterElse <- expect "else" afterYes
      (no, afterNo) <- parseExpression afterElse
      Right (cardIf (CardLe left right) yes no, afterNo)
    parseExpression tokens = parseAdditive tokens

    parseAdditive tokens = do
      (first, rest) <- parseMultiplicative tokens
      continue first rest
      where
        continue accumulated ("+" : more) = do
          (next, rest) <- parseMultiplicative more
          continue (cardAdd accumulated next) rest
        continue accumulated ("-" : more) = do
          (next, rest) <- parseMultiplicative more
          continue (cardGuardedSub accumulated next) rest
        continue accumulated rest = Right (accumulated, rest)

    parseMultiplicative tokens = do
      (first, rest) <- parseAtom tokens
      continue first rest
      where
        continue accumulated ("*" : more) = do
          (next, rest) <- parseAtom more
          continue (cardMul accumulated next) rest
        continue accumulated rest = Right (accumulated, rest)

    parseAtom ("(" : rest) = do
      (expression, afterExpression) <- parseExpression rest
      afterClose <- expect ")" afterExpression
      Right (expression, afterClose)
    parseAtom (token : rest)
      | T.all isDigit token
      , not (T.null token) =
          Right (cardLiteral (read (T.unpack token)), rest)
      | Just term <- Map.lookup token indexes =
          Right (cardIndex term, rest)
      | otherwise = Left ("unknown cardinality index '" <> token <> "'")
    parseAtom [] = Left "expected cardinality expression"

    expect wanted (actual : rest)
      | wanted == actual = Right rest
    expect wanted _ = Left ("expected cardinality token '" <> wanted <> "'")

tokenize :: Text -> Either Text [Text]
tokenize = go . T.unpack
  where
    go [] = Right []
    go (character : rest)
      | character == ' ' || character == '\t' || character == '\n' || character == '\r' =
          go rest
      | isAlpha character || character == '_' =
          let (suffix, remaining) = span (\c -> isAlphaNum c || c == '_' || c == '\'') rest
           in (T.pack (character : suffix) :) <$> go remaining
      | isDigit character =
          let (suffix, remaining) = span isDigit rest
           in (T.pack (character : suffix) :) <$> go remaining
      | character == '<'
      , '=' : remaining <- rest =
          ("<=" :) <$> go remaining
      | character `elem` ("()+-*" :: String) =
          (T.singleton character :) <$> go rest
      | otherwise =
          Left ("invalid cardinality character '" <> T.singleton character <> "'")
