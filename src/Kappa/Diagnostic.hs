-- | Structured diagnostics (Spec §3.1).
--
-- A diagnostic is a typed record (§3.1.1); the human-readable output is a
-- rendering of that record (§1, §3.1.8). Codes are stable symbolic
-- identifiers (§3.1.2); families use the @kappa.*@ dotted spelling. Of the
-- optional §3.1.1 fields this implementation models notes and helps; the
-- related-origin list, sub-span labels and machine payload have no
-- producer or renderer here and are deliberately not represented.
module Kappa.Diagnostic
  ( Severity (..)
  , Stage (..)
  , DiagnosticCode
  , DiagnosticFamily
  , Diagnostic (..)
  , diag
  , withNote
  , withHelp
  , isError
  , Diagnostics
  , hasErrors
  , renderDiagnostic
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Source (Pos (..), Span (..))

data Severity = SevError | SevWarning | SevNote | SevInfo
  deriving stock (Eq, Ord, Show)

-- | Compilation stage that produced the diagnostic (§3.1.1 @stage@).
data Stage
  = StageLex
  | StageParse
  | StageImports
  | StageDeclShapes
  | StageResolve
  | StageElaborate
  | StageRuntime
  deriving stock (Eq, Ord, Show)

-- | Stable symbolic code, e.g. @E_TYPE_EQUALITY_MISMATCH@ (§3.1.2).
type DiagnosticCode = Text

-- | Standardized dotted family, e.g. @kappa.type.mismatch@ (§3.1.2).
type DiagnosticFamily = Text

-- | Diagnostic record per §3.1.1 (implemented subset).
data Diagnostic = Diagnostic
  { dCode :: !DiagnosticCode
  , dFamily :: !(Maybe DiagnosticFamily)
  , dSeverity :: !Severity
  , dStage :: !Stage
  , dPrimary :: !Span
  , dMessage :: !Text
  , dNotes :: ![Text]
  , dHelps :: ![Text]
  }
  deriving stock (Show)

-- | Construct a minimal diagnostic; refine with the @with*@ combinators.
diag :: Severity -> Stage -> DiagnosticCode -> Maybe DiagnosticFamily -> Span -> Text -> Diagnostic
diag sev stage code fam sp msg =
  Diagnostic
    { dCode = code
    , dFamily = fam
    , dSeverity = sev
    , dStage = stage
    , dPrimary = sp
    , dMessage = msg
    , dNotes = []
    , dHelps = []
    }

withNote :: Text -> Diagnostic -> Diagnostic
withNote n d = d {dNotes = dNotes d ++ [n]}

withHelp :: Text -> Diagnostic -> Diagnostic
withHelp h d = d {dHelps = dHelps d ++ [h]}

isError :: Diagnostic -> Bool
isError d = dSeverity d == SevError

type Diagnostics = [Diagnostic]

hasErrors :: Diagnostics -> Bool
hasErrors = any isError

-- | The canonical human-readable rendering (§3.1.8), shared by the CLI
-- and the Appendix T harness:
--
-- > path:line:col: severity[CODE] (family): message
-- >   note: ...
-- >   help: ...
renderDiagnostic :: Diagnostic -> Text
renderDiagnostic d =
  let Span f (Pos l c) _ = dPrimary d
      sev = case dSeverity d of
        SevError -> "error"
        SevWarning -> "warning"
        SevNote -> "note"
        SevInfo -> "info"
      tshow = T.pack . show
   in T.pack f <> ":" <> tshow l <> ":" <> tshow c <> ": "
        <> sev <> "[" <> dCode d <> "]"
        <> maybe "" (\fam -> " (" <> fam <> ")") (dFamily d)
        <> ": " <> dMessage d
        <> T.concat (map ("\n  note: " <>) (dNotes d))
        <> T.concat (map ("\n  help: " <>) (dHelps d))
