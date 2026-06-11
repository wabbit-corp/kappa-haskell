-- | Source positions, spans, and origins (Spec §3.1.5, §37.8).
--
-- Positions are 1-based in both line and column; columns count Unicode
-- scalar values. A 'Span' is half-open in offset terms but stores inclusive
-- start and exclusive end positions, which matches the rendering convention
-- used by the human-readable diagnostic renderer.
module Kappa.Source
  ( Pos (..)
  , Span (..)
  , ModuleName (..)
  , moduleNameText
  , SourceFile (..)
  , mkSourceFile
  , spanUnion
  , posBefore
  , noSpan
  , lineAt
  ) where

import Data.Text (Text)
import qualified Data.Text as T

-- | A source position: 1-based line, 1-based column (in Unicode scalars).
data Pos = Pos
  { posLine :: !Int
  , posCol :: !Int
  }
  deriving stock (Eq, Ord, Show)

-- | A contiguous source range within one file. @spanEnd@ is exclusive.
data Span = Span
  { spanFile :: !FilePath
  , spanStart :: !Pos
  , spanEnd :: !Pos
  }
  deriving stock (Eq, Ord, Show)

-- | A dotted module name such as @std.prelude@ (Spec §8.1).
newtype ModuleName = ModuleName [Text]
  deriving stock (Eq, Ord, Show)

moduleNameText :: ModuleName -> Text
moduleNameText (ModuleName segs) = T.intercalate "." segs

-- | A loaded source file together with its line index (for diagnostics).
data SourceFile = SourceFile
  { sfPath :: !FilePath
  , sfText :: !Text
  , sfLines :: ![Text]
  }
  deriving stock (Show)

mkSourceFile :: FilePath -> Text -> SourceFile
mkSourceFile path txt = SourceFile path txt (T.lines txt)

-- | The 1-based line @n@ of a file, or empty if out of range.
lineAt :: SourceFile -> Int -> Text
lineAt sf n = case drop (n - 1) (sfLines sf) of
  l : _ -> l
  [] -> ""

-- | Smallest span covering both arguments (assumes same file).
spanUnion :: Span -> Span -> Span
spanUnion a b =
  Span
    (spanFile a)
    (min (spanStart a) (spanStart b))
    (max (spanEnd a) (spanEnd b))

posBefore :: Pos -> Pos -> Bool
posBefore = (<)

-- | A placeholder span for synthesized constructs (e.g. prelude builtins).
noSpan :: Span
noSpan = Span "<builtin>" (Pos 0 0) (Pos 0 0)
