-- | Token types produced by the lexer (Spec §5–§6).
--
-- Keywords are soft (§5.2): the lexer emits them as 'TokIdent' and the
-- parser decides keyword-ness contextually. The two exceptions are
-- @let?@ and @for?@, which §5.5.1 requires to be recognized as single
-- tokens; they are emitted as 'TokIdent' with the literal text @let?@ /
-- @for?@.
module Kappa.Token
  ( Token (..)
  , Located (..)
  , StrFragment (..)
  , StringLit (..)
  , QuotedLit (..)
  , tokenDescr
  ) where

import Data.Text (Text)
import Data.Word (Word8)
import Kappa.Source (Span)

-- | One fragment of a (possibly interpolated) string literal (§6.3.4.4).
-- The payload of 'FragInterp'/'FragInterpFmt' is the raw expression source
-- text, re-parsed by the parser at its recorded span.
data StrFragment
  = FragLit !Text
  | FragInterp !Text !Span
  | FragInterpFmt !Text !Span !Text
  deriving stock (Eq, Show)

-- | A string literal of any family (§6.3.1–§6.3.5).
data StringLit = StringLit
  { slPrefix :: !(Maybe Text)
  -- ^ Prefixed-string handler name, e.g. @f@ in @f"..."@.
  , slHashes :: !Int
  -- ^ Raw-string hash count; 0 for ordinary strings.
  , slMultiline :: !Bool
  , slFragments :: ![StrFragment]
  -- ^ Decoded (escape-processed) for ordinary strings; verbatim for raw.
  -- Adjacent 'FragLit's merged; empty lits omitted except @[FragLit ""]@
  -- for the empty literal.
  }
  deriving stock (Eq, Show)

-- | A single-quoted literal (§6.4–§6.5), carrying the decoded views of
-- the @QuotedLiteral@ payload record.
data QuotedLit = QuotedLit
  { qlPrefix :: !(Maybe Text)
  , qlSourceBody :: !Text
  , qlText :: !(Maybe Text)
  , qlBytes :: !(Maybe [Word8])
  }
  deriving stock (Eq, Show)

data Token
  = TokIdent !Text
  -- ^ Identifier or soft keyword (including @let?@ / @for?@).
  | TokBacktick !Text
  -- ^ Backtick-quoted identifier; payload is the unquoted text.
  | TokInt !Integer !(Maybe Text)
  -- ^ Integer literal (lexically nonnegative) and optional suffix.
  | TokFloat !Double !(Maybe Text)
  | TokString !StringLit
  | TokQuoted !QuotedLit
  | TokOperator !Text
  -- ^ Operator token (maximal munch, §5.5.1), e.g. @==@, @::@, @..<@.
  | TokArrow      -- ^ @->@
  | TokBackArrow  -- ^ @<-@
  | TokEquals     -- ^ @=@
  | TokColon      -- ^ @:@
  | TokDot        -- ^ @.@
  | TokAt         -- ^ @\@@
  | TokTilde      -- ^ @~@
  | TokBar        -- ^ @|@
  | TokBackslash  -- ^ @\\@
  | TokQDot       -- ^ @?.@
  | TokElvis      -- ^ @?:@
  | TokHole !Text -- ^ named hole @?name@
  | TokLParen | TokRParen
  | TokLBracket | TokRBracket
  | TokLBrace | TokRBrace
  | TokVariantOpen | TokVariantClose   -- ^ @(|@ / @|)@
  | TokSetOpen | TokSetClose           -- ^ @{|@ / @|}@
  | TokEffOpen | TokEffClose           -- ^ @<[@ / @]>@
  | TokComma
  | TokQuoteBrace -- ^ syntax quote opener @'{@ (§21.1)
  | TokSplice     -- ^ splice opener @$(@ (§21.2)
  | TokBang       -- ^ monadic splice @!@ (§18.3) when prefix-adjacent
  | TokError
  -- ^ Recovered lexical error (e.g. unterminated backtick identifier):
  -- the diagnostic is already recorded; the parser never accepts this.
  | TokNewline !Bool
  -- ^ End of a logical line. The flag is 'True' when the newline occurred
  -- inside brackets ("soft"): no INDENT\/DEDENT accompanies it (§5.4).
  | TokIndent
  | TokDedent
  | TokEOF
  deriving stock (Eq, Show)

data Located = Located
  { locTok :: !Token
  , locSpan :: !Span
  }
  deriving stock (Show)

-- | Human-readable token description for parse errors.
tokenDescr :: Token -> Text
tokenDescr = \case
  TokIdent t -> "'" <> t <> "'"
  TokBacktick t -> "`" <> t <> "`"
  TokInt {} -> "integer literal"
  TokFloat {} -> "float literal"
  TokString {} -> "string literal"
  TokQuoted {} -> "quoted literal"
  TokOperator t -> "operator '" <> t <> "'"
  TokArrow -> "'->'"
  TokBackArrow -> "'<-'"
  TokEquals -> "'='"
  TokColon -> "':'"
  TokDot -> "'.'"
  TokAt -> "'@'"
  TokTilde -> "'~'"
  TokBar -> "'|'"
  TokBackslash -> "'\\'"
  TokQDot -> "'?.'"
  TokElvis -> "'?:'"
  TokHole t -> "hole '?" <> t <> "'"
  TokLParen -> "'('"
  TokRParen -> "')'"
  TokLBracket -> "'['"
  TokRBracket -> "']'"
  TokLBrace -> "'{'"
  TokRBrace -> "'}'"
  TokVariantOpen -> "'(|'"
  TokVariantClose -> "'|)'"
  TokSetOpen -> "'{|'"
  TokSetClose -> "'|}'"
  TokEffOpen -> "'<['"
  TokEffClose -> "']>'"
  TokComma -> "','"
  TokQuoteBrace -> "quote '{"
  TokSplice -> "'$('"
  TokBang -> "'!'"
  TokError -> "invalid token"
  TokNewline _ -> "end of line"
  TokIndent -> "indent"
  TokDedent -> "dedent"
  TokEOF -> "end of file"
