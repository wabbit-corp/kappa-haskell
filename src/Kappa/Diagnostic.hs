-- | Structured diagnostics (Spec §3.1).
--
-- A diagnostic is a typed record (§3.1.1); human-readable and JSON output
-- are renderings of the same record (§1, §3.1.8, §3.1.9). Codes are stable
-- symbolic identifiers (§3.1.2); families use the @kappa.*@ dotted spelling.
module Kappa.Diagnostic
  ( Severity (..)
  , Stage (..)
  , DiagnosticCode
  , DiagnosticFamily
  , RelatedRole (..)
  , relatedRoleText
  , Related (..)
  , DiagLabel (..)
  , Diagnostic (..)
  , diag
  , withNote
  , withHelp
  , withLabel
  , withRelated
  , isError
  , Diagnostics
  , hasErrors
  , sortDiagnostics
  ) where

import Data.List (sortOn)
import Data.Text (Text)
import Kappa.Source (Span)

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

-- | Stable symbolic code, e.g. @E_TYPE_MISMATCH@ (§3.1.2).
type DiagnosticCode = Text

-- | Standardized dotted family, e.g. @kappa.type.mismatch@ (§3.1.2).
type DiagnosticFamily = Text

-- | Standardized related-origin roles (§3.1.1A).
data RelatedRole
  = RoleDefinitionSite
  | RoleDeclarationSite
  | RoleSignatureSite
  | RoleUseSite
  | RoleCallSite
  | RoleBinderSite
  | RoleFieldDeclarationSite
  | RoleConstructorDeclarationSite
  | RoleTraitDeclarationSite
  | RoleInstanceDeclarationSite
  | RoleImplicitCandidateSite
  | RoleSelectedCandidateSite
  | RoleRejectedCandidateSite
  | RoleImportSite
  | RoleExportSite
  | RoleFeatureGateSite
  | RoleDesugaredFrom
  | RoleObligationIntroducedHere
  | RoleObligationRequiredHere
  | RoleConsumedHere
  | RoleUsedAfterConsume
  | RoleFixTarget
  deriving stock (Eq, Ord, Show)

relatedRoleText :: RelatedRole -> Text
relatedRoleText = \case
  RoleDefinitionSite -> "definition-site"
  RoleDeclarationSite -> "declaration-site"
  RoleSignatureSite -> "signature-site"
  RoleUseSite -> "use-site"
  RoleCallSite -> "call-site"
  RoleBinderSite -> "binder-site"
  RoleFieldDeclarationSite -> "field-declaration-site"
  RoleConstructorDeclarationSite -> "constructor-declaration-site"
  RoleTraitDeclarationSite -> "trait-declaration-site"
  RoleInstanceDeclarationSite -> "instance-declaration-site"
  RoleImplicitCandidateSite -> "implicit-candidate-site"
  RoleSelectedCandidateSite -> "selected-candidate-site"
  RoleRejectedCandidateSite -> "rejected-candidate-site"
  RoleImportSite -> "import-site"
  RoleExportSite -> "export-site"
  RoleFeatureGateSite -> "feature-gate-site"
  RoleDesugaredFrom -> "desugared-from"
  RoleObligationIntroducedHere -> "obligation-introduced-here"
  RoleObligationRequiredHere -> "obligation-required-here"
  RoleConsumedHere -> "consumed-here"
  RoleUsedAfterConsume -> "used-after-consume"
  RoleFixTarget -> "fix-target"

-- | A related origin with a stable role (§3.1.1A).
data Related = Related
  { relSpan :: !Span
  , relRole :: !RelatedRole
  , relMessage :: !(Maybe Text)
  }
  deriving stock (Show)

-- | A labelled sub-span rendered inside source snippets.
data DiagLabel = DiagLabel
  { lblSpan :: !Span
  , lblText :: !Text
  }
  deriving stock (Show)

-- | Diagnostic record per §3.1.1. @payload@ is rendered as a JSON object of
-- family-specific key\/value pairs.
data Diagnostic = Diagnostic
  { dCode :: !DiagnosticCode
  , dFamily :: !(Maybe DiagnosticFamily)
  , dSeverity :: !Severity
  , dStage :: !Stage
  , dPrimary :: !Span
  , dMessage :: !Text
  , dLabels :: ![DiagLabel]
  , dNotes :: ![Text]
  , dHelps :: ![Text]
  , dRelated :: ![Related]
  , dPayload :: ![(Text, Text)]
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
    , dLabels = []
    , dNotes = []
    , dHelps = []
    , dRelated = []
    , dPayload = []
    }

withNote :: Text -> Diagnostic -> Diagnostic
withNote n d = d {dNotes = dNotes d ++ [n]}

withHelp :: Text -> Diagnostic -> Diagnostic
withHelp h d = d {dHelps = dHelps d ++ [h]}

withLabel :: Span -> Text -> Diagnostic -> Diagnostic
withLabel sp t d = d {dLabels = dLabels d ++ [DiagLabel sp t]}

withRelated :: Span -> RelatedRole -> Maybe Text -> Diagnostic -> Diagnostic
withRelated sp role msg d = d {dRelated = dRelated d ++ [Related sp role msg]}

isError :: Diagnostic -> Bool
isError d = dSeverity d == SevError

type Diagnostics = [Diagnostic]

hasErrors :: Diagnostics -> Bool
hasErrors = any isError

-- | Deterministic primary-position order (file, then start position).
sortDiagnostics :: Diagnostics -> Diagnostics
sortDiagnostics = sortOn (\d -> (spanKey (dPrimary d)))
  where
    spanKey sp = (show sp)
