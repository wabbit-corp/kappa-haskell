-- | Token types produced by the lexer (Spec §5–§6): the flat vocabulary
-- the parser consumes. No logic lives here, so it is a good first file to
-- read. (Codebase orientation and a reading order: docs/CONCEPTS.md.)
--
-- Notable: keywords are __soft__ (§5.2). The lexer keeps no keyword list and
-- emits words like @let@ or @match@ as ordinary 'TokIdent's; the parser
-- decides keyword-ness from context, so @match@ stays usable as an
-- identifier. The only forced single-token spellings are @let?@ \/ @for?@
-- (§5.5.1), also emitted as 'TokIdent' carrying that literal text.
module Kappa.Token
  ( Token (..)
  , Located (..)
  , StrFragment (..)
  , StringLit (..)
  , QuotedLit (..)
  , tokenDescr
  ) where

import Data.Data (Data)
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
  deriving stock (Eq, Show, Data)

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
  deriving stock (Eq, Show, Data)

-- | A single-quoted literal (§6.4–§6.5), carrying the decoded views of
-- the @QuotedLiteral@ payload record.
data QuotedLit = QuotedLit
  { qlPrefix :: !(Maybe Text)
  , qlSourceBody :: !Text
  , qlText :: !(Maybe Text)
  , qlBytes :: !(Maybe [Word8])
  }
  deriving stock (Eq, Show, Data)

-- | The token vocabulary. Grouped below into families (names\/literals,
-- reserved punctuation, brackets, metaprogramming, layout) purely for
-- reading; the order is not significant.
data Token
  = -- Names and literals --------------------------------------------------
    TokIdent !Text
  -- ^ Identifier or soft keyword (including @let?@ / @for?@).
  | TokBacktick !Text
  -- ^ Backtick-quoted identifier; payload is the unquoted text.
  | TokInt !Integer !(Maybe Text)
  -- ^ Integer literal (lexically nonnegative) and optional suffix.
  | TokFloat !Double !(Maybe Text)
  | TokString !StringLit
  | TokQuoted !QuotedLit
  -- Operators and reserved punctuation ----------------------------------
  -- Most punctuation is just 'TokOperator', but a handful of forms are so
  -- structural (arrows, binders, the layout-significant ones) that the
  -- lexer gives them their own constructor so the parser needn't re-match text.
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
  -- Optional-chaining sigils and holes ----------------------------------
  | TokQDot       -- ^ @?.@
  | TokElvis      -- ^ @?:@
  | TokHole !Text -- ^ named hole @?name@
  -- Brackets and delimiters ---------------------------------------------
  | TokLParen | TokRParen
  | TokLBracket | TokRBracket
  | TokLBrace | TokRBrace
  | TokVariantOpen | TokVariantClose   -- ^ @(|@ / @|)@
  | TokSetOpen | TokSetClose           -- ^ @{|@ / @|}@
  | TokEffOpen | TokEffClose           -- ^ @<[@ / @]>@
  | TokComma
  -- Metaprogramming (quoting and splicing, §21) -------------------------
  | TokQuoteBrace -- ^ syntax quote opener @'{@ (§21.1)
  | TokSplice     -- ^ splice opener @$(@ (§21.2)
  | TokQuoteSplice -- ^ in-quote splice opener @${@ (§21.1)
  | TokBang       -- ^ monadic splice @!@ (§18.3) when prefix-adjacent
  -- Errors and layout ---------------------------------------------------
  -- Layout tokens are synthesized by the lexer from indentation, Python-style:
  -- the source has no braces, so 'TokIndent'\/'TokDedent'\/'TokNewline' stand
  -- in for the block structure the parser needs.
  | TokError
  -- ^ Recovered lexical error (e.g. unterminated backtick identifier):
  -- the diagnostic is already recorded; the parser never accepts this.
  | TokNewline !Bool
  -- ^ End of a logical line. The flag is 'True' when the newline occurred
  -- inside brackets ("soft"): no INDENT\/DEDENT accompanies it (§5.4).
  | TokIndent
  | TokDedent
  | TokEOF
  deriving stock (Eq, Show, Data)

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
  TokQuoteSplice -> "'${'"
  TokBang -> "'!'"
  TokError -> "invalid token"
  TokNewline _ -> "end of line"
  TokIndent -> "indent"
  TokDedent -> "dedent"
  TokEOF -> "end of file"
