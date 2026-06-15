-- | Structured diagnostics (Spec §3.1).
--
-- A diagnostic is a typed record (§3.1.1); the human-readable output and
-- the JSON output are two renderings of that one record (§1, §3.1.8,
-- §3.1.1). Codes are stable symbolic identifiers (§3.1.2); families use
-- the @kappa.*@ dotted spelling.
--
-- The record models the §3.1.1 conceptual fields: @schemaVersion@,
-- @code@, @family@, @severity@, @stage@, @phase@, @primary@, @message@,
-- @labels@, @notes@, @helps@, @fixes@, @related@ (§3.1.1A), @payload@
-- (§3.1.9), @explain@, and @suppressed@ (§3.1.10/§3.1.11). The
-- machine-readable JSON producer ('renderDiagnosticJson') exposes fields
-- observationally equivalent to that list; the human renderer
-- ('renderDiagnostic') is the default surface (§3.1.8).
module Kappa.Diagnostic
  ( Severity (..)
  , Stage (..)
  , DiagnosticCode
  , DiagnosticFamily
  , RelatedRole (..)
  , relatedRoleText
  , RelatedOrigin (..)
  , related
  , Payload (..)
  , noPayload
  , payloadKind
  , withPayloadField
  , FixApplicability (..)
  , fixApplicabilityText
  , SourceEdit (..)
  , DiagnosticFix (..)
  , Suppressed (..)
  , Diagnostic (..)
  , schemaVersion
  , diag
  , withNote
  , withHelp
  , withRelated
  , withRelateds
  , withPayload
  , withFix
  , withSuppressed
  , isError
  , Diagnostics
  , hasErrors
  , renderDiagnostic
  , renderDiagnosticJson
  , renderDiagnosticsJson
  ) where

import Data.Char (ord)
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

-- | The JSON schema version this implementation emits (§3.1.1
-- @schemaVersion@). Incremented when the payload schema changes
-- incompatibly (§3.1.2A).
schemaVersion :: Int
schemaVersion = 1

-- ── Related origins (§3.1.1A) ────────────────────────────────────────

-- | Standardized related-origin roles (§3.1.1A). Spellings are the
-- normative dashed spellings from the §3.1.1A list; preserving these is
-- a MUST. Implementations MAY add roles, so this enum carries the subset
-- this implementation populates plus a 'RoleOther' escape for any
-- additional stable spelling.
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
  | RoleMacroInvocationSite
  | RoleMacroDefinitionSite
  | RoleGeneratedSite
  | RoleDesugaredFrom
  | RoleObligationIntroducedHere
  | RoleObligationRequiredHere
  | RoleObligationBlockedHere
  | RoleNormalizationBlockedHere
  | RoleFlowFactIntroducedHere
  | RoleFlowFactUsedHere
  | RoleBorrowStart
  | RoleBorrowConflict
  | RoleBorrowEscapeSite
  | RoleConsumedHere
  | RoleUsedAfterConsume
  | RoleFixTarget
  | RoleExpectedTypeSource
  | RoleOther !Text
  deriving stock (Eq, Show)

-- | The §3.1.1A stable wire spelling for a role.
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
  RoleMacroInvocationSite -> "macro-invocation-site"
  RoleMacroDefinitionSite -> "macro-definition-site"
  RoleGeneratedSite -> "generated-site"
  RoleDesugaredFrom -> "desugared-from"
  RoleObligationIntroducedHere -> "obligation-introduced-here"
  RoleObligationRequiredHere -> "obligation-required-here"
  RoleObligationBlockedHere -> "obligation-blocked-here"
  RoleNormalizationBlockedHere -> "normalization-blocked-here"
  RoleFlowFactIntroducedHere -> "flow-fact-introduced-here"
  RoleFlowFactUsedHere -> "flow-fact-used-here"
  RoleBorrowStart -> "borrow-start"
  RoleBorrowConflict -> "borrow-conflict"
  RoleBorrowEscapeSite -> "borrow-escape-site"
  RoleConsumedHere -> "consumed-here"
  RoleUsedAfterConsume -> "used-after-consume"
  RoleFixTarget -> "fix-target"
  -- §3.1.1A: "the source origin of the expected type when available" —
  -- an implementation-added role spelling, namespaced so it cannot be
  -- mistaken for one of the normative spellings above.
  RoleExpectedTypeSource -> "expected-type-source"
  RoleOther t -> t

-- | A related origin (§3.1.1A): a secondary source location that
-- explains a multi-site relationship, with a stable role and an optional
-- human message.
data RelatedOrigin = RelatedOrigin
  { roOrigin :: !Span
  , roRole :: !RelatedRole
  , roMessage :: !(Maybe Text)
  }
  deriving stock (Show)

-- | Convenience constructor for a related origin.
related :: RelatedRole -> Span -> Text -> RelatedOrigin
related role sp msg = RelatedOrigin sp role (Just msg)

-- ── Payloads (§3.1.9) ────────────────────────────────────────────────

-- | A structured family-specific payload (§3.1.9). The only mandatory
-- field is @kind@; everything else is a flat list of string-valued
-- entries, which covers the standardized expected/actual,
-- name.unresolved, etc. fields this implementation populates. Tools must
-- ignore unknown fields (§3.1.9), so additional entries are always safe.
data Payload = Payload
  { pKind :: !Text
  , pFields :: ![(Text, Text)]
  }
  deriving stock (Show)

-- | The empty/absent payload: kind @"none"@ with no fields. Used until a
-- producer attaches a family payload.
noPayload :: Payload
noPayload = Payload "none" []

-- | A payload with only its @kind@ set.
payloadKind :: Text -> Payload
payloadKind k = Payload k []

-- | Append one key/value to a payload.
withPayloadField :: Text -> Text -> Payload -> Payload
withPayloadField k v p = p {pFields = pFields p ++ [(k, v)]}

-- ── Fix-its (§3.1.6) ─────────────────────────────────────────────────

data FixApplicability
  = FixMachineApplicable
  | FixMaybeApplicable
  | FixPlaceholder
  | FixUnsafe
  | FixNotMachineApplicable
  deriving stock (Eq, Show)

fixApplicabilityText :: FixApplicability -> Text
fixApplicabilityText = \case
  FixMachineApplicable -> "machine-applicable"
  FixMaybeApplicable -> "maybe-applicable"
  FixPlaceholder -> "placeholder"
  FixUnsafe -> "unsafe"
  FixNotMachineApplicable -> "not-machine-applicable"

-- | A single source edit (§3.1.6 @SourceEdit@): replace the text covered
-- by @seRange@ in @seFile@ with @seReplacement@.
data SourceEdit = SourceEdit
  { seFile :: !FilePath
  , seRange :: !Span
  , seReplacement :: !Text
  }
  deriving stock (Show)

-- | A fix-it (§3.1.6 @DiagnosticFix@): a titled, applicability-tagged set
-- of source edits applied atomically.
data DiagnosticFix = DiagnosticFix
  { dfTitle :: !Text
  , dfApplicability :: !FixApplicability
  , dfEdits :: ![SourceEdit]
  }
  deriving stock (Show)

-- ── Suppressed summaries (§3.1.10/§3.1.11) ───────────────────────────

-- | A summary of a cascade-suppressed diagnostic (§3.1.11): retained so
-- tooling can show it on request without re-emitting it as an
-- independent error.
data Suppressed = Suppressed
  { suCode :: !DiagnosticCode
  , suFamily :: !(Maybe DiagnosticFamily)
  , suPrimary :: !Span
  , suMessage :: !Text
  }
  deriving stock (Show)

-- ── The diagnostic record (§3.1.1) ───────────────────────────────────

-- | Diagnostic record per §3.1.1.
data Diagnostic = Diagnostic
  { dCode :: !DiagnosticCode
  , dFamily :: !(Maybe DiagnosticFamily)
  , dSeverity :: !Severity
  , dStage :: !Stage
  , dPrimary :: !Span
  , dMessage :: !Text
  , dNotes :: ![Text]
  , dHelps :: ![Text]
  , dRelated :: ![RelatedOrigin]
  , dPayload :: !Payload
  , dFixes :: ![DiagnosticFix]
  , dSuppressed :: ![Suppressed]
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
    , dRelated = []
    , dPayload = noPayload
    , dFixes = []
    , dSuppressed = []
    }

withNote :: Text -> Diagnostic -> Diagnostic
withNote n d = d {dNotes = dNotes d ++ [n]}

withHelp :: Text -> Diagnostic -> Diagnostic
withHelp h d = d {dHelps = dHelps d ++ [h]}

withRelated :: RelatedOrigin -> Diagnostic -> Diagnostic
withRelated r d = d {dRelated = dRelated d ++ [r]}

withRelateds :: [RelatedOrigin] -> Diagnostic -> Diagnostic
withRelateds rs d = d {dRelated = dRelated d ++ rs}

withPayload :: Payload -> Diagnostic -> Diagnostic
withPayload p d = d {dPayload = p}

withFix :: DiagnosticFix -> Diagnostic -> Diagnostic
withFix f d = d {dFixes = dFixes d ++ [f]}

withSuppressed :: [Suppressed] -> Diagnostic -> Diagnostic
withSuppressed ss d = d {dSuppressed = dSuppressed d ++ ss}

isError :: Diagnostic -> Bool
isError d = dSeverity d == SevError

type Diagnostics = [Diagnostic]

hasErrors :: Diagnostics -> Bool
hasErrors = any isError

severityText :: Severity -> Text
severityText = \case
  SevError -> "error"
  SevWarning -> "warning"
  SevNote -> "note"
  SevInfo -> "info"

stageText :: Stage -> Text
stageText = \case
  StageLex -> "lex"
  StageParse -> "parse"
  StageImports -> "imports"
  StageDeclShapes -> "decl-shapes"
  StageResolve -> "resolve"
  StageElaborate -> "elaborate"
  StageRuntime -> "runtime"

-- ── Human-readable rendering (§3.1.8) ────────────────────────────────

-- | The canonical human-readable rendering (§3.1.8), shared by the CLI
-- and the Appendix T harness:
--
-- > path:line:col: severity[CODE] (family): message
-- >   note: ...
-- >   help: ...
-- >   related: ROLE at path:line:col: ...
-- >   fix: title [applicability]
-- >   suppressed: CODE at path:line:col: ...
--
-- §3.1.8 requires severity, code, message, primary range (when
-- available), and notes/help/fixes (when present). §3.1.1A requires the
-- human renderer to show at least one related origin whenever a
-- non-presentational related origin is present.
renderDiagnostic :: Diagnostic -> Text
renderDiagnostic d =
  T.concat $
    [ renderPos (dPrimary d) <> ": "
        <> severityText (dSeverity d) <> "[" <> dCode d <> "]"
        <> maybe "" (\fam -> " (" <> fam <> ")") (dFamily d)
        <> ": " <> dMessage d
    ]
      ++ map ("\n  note: " <>) (dNotes d)
      ++ map ("\n  help: " <>) (dHelps d)
      ++ map renderRelated (dRelated d)
      ++ map renderFix (dFixes d)
      ++ map renderSuppressed (dSuppressed d)
  where
    renderRelated r =
      "\n  related: " <> relatedRoleText (roRole r)
        <> " at " <> renderPos (roOrigin r)
        <> maybe "" (": " <>) (roMessage r)
    renderFix f =
      "\n  fix: " <> dfTitle f <> " [" <> fixApplicabilityText (dfApplicability f) <> "]"
    renderSuppressed s =
      "\n  suppressed: " <> suCode s <> " at " <> renderPos (suPrimary s)
        <> ": " <> suMessage s

renderPos :: Span -> Text
renderPos (Span f (Pos l c) _) = T.pack f <> ":" <> tshow l <> ":" <> tshow c

tshow :: Show a => a -> Text
tshow = T.pack . show

-- ── Machine-readable JSON rendering (§3.1.1) ─────────────────────────

-- | Render a diagnostic as one JSON object (§3.1.1). The producer is
-- hand-written over @text@ — no external JSON dependency — and exposes
-- fields observationally equivalent to the §3.1.1 conceptual record.
renderDiagnosticJson :: Diagnostic -> Text
renderDiagnosticJson d = jObject (diagPairs d)

-- | Render a list of diagnostics as a JSON array (§3.1.1, one object per
-- diagnostic). Tools consume this stream rather than parsing prose.
renderDiagnosticsJson :: Diagnostics -> Text
renderDiagnosticsJson ds = jArray (map renderDiagnosticJson ds)

diagPairs :: Diagnostic -> [(Text, Text)]
diagPairs d =
  [ ("schemaVersion", jInt schemaVersion)
  , ("code", jStr (dCode d))
  , ("family", maybe jNull jStr (dFamily d))
  , ("severity", jStr (severityText (dSeverity d)))
  , ("stage", jStr (stageText (dStage d)))
  , ("phase", jNull)
  , ("primary", spanJson (dPrimary d))
  , ("message", jStr (dMessage d))
  , ("labels", jArray (map noteLabel (dNotes d)))
  , ("notes", jArray (map jStr (dNotes d)))
  , ("helps", jArray (map jStr (dHelps d)))
  , ("fixes", jArray (map fixJson (dFixes d)))
  , ("related", jArray (map relatedJson (dRelated d)))
  , ("payload", payloadJson (dPayload d))
  , ("explain", jStr (dCode d))
  , ("suppressed", jArray (map suppressedJson (dSuppressed d)))
  ]
  where
    -- §3.1.5: notes double as the implementation's source-range labels
    -- on the primary span — exposed here so a tool sees a non-empty
    -- @labels@ list without a separate sub-span producer.
    noteLabel n = jObject [("span", spanJson (dPrimary d)), ("message", jStr n)]

spanJson :: Span -> Text
spanJson (Span f (Pos sl sc) (Pos el ec)) =
  jObject
    [ ("file", jStr (T.pack f))
    , ("startLine", jInt sl)
    , ("startCol", jInt sc)
    , ("endLine", jInt el)
    , ("endCol", jInt ec)
    ]

relatedJson :: RelatedOrigin -> Text
relatedJson r =
  jObject
    [ ("origin", spanJson (roOrigin r))
    , ("role", jStr (relatedRoleText (roRole r)))
    , ("message", maybe jNull jStr (roMessage r))
    ]

payloadJson :: Payload -> Text
payloadJson p =
  jObject (("kind", jStr (pKind p)) : [(k, jStr v) | (k, v) <- pFields p])

fixJson :: DiagnosticFix -> Text
fixJson f =
  jObject
    [ ("title", jStr (dfTitle f))
    , ("applicability", jStr (fixApplicabilityText (dfApplicability f)))
    , ("edits", jArray (map editJson (dfEdits f)))
    ]

editJson :: SourceEdit -> Text
editJson e =
  jObject
    [ ("file", jStr (T.pack (seFile e)))
    , ("range", spanJson (seRange e))
    , ("replacement", jStr (seReplacement e))
    ]

suppressedJson :: Suppressed -> Text
suppressedJson s =
  jObject
    [ ("code", jStr (suCode s))
    , ("family", maybe jNull jStr (suFamily s))
    , ("primary", spanJson (suPrimary s))
    , ("message", jStr (suMessage s))
    ]

-- ── A minimal hand-written JSON encoder (boot packages only) ─────────

jNull :: Text
jNull = "null"

jInt :: Int -> Text
jInt = tshow

jStr :: Text -> Text
jStr s = "\"" <> T.concatMap esc s <> "\""
  where
    esc c = case c of
      '"' -> "\\\""
      '\\' -> "\\\\"
      '\n' -> "\\n"
      '\r' -> "\\r"
      '\t' -> "\\t"
      _
        | ord c < 0x20 -> "\\u" <> pad4 (T.pack (showHex (ord c)))
        | otherwise -> T.singleton c
    pad4 t = T.replicate (4 - T.length t) "0" <> t

showHex :: Int -> String
showHex n
  | n < 16 = [d n]
  | otherwise = showHex (n `div` 16) ++ [d (n `mod` 16)]
  where
    d x
      | x < 10 = toEnum (ord '0' + x)
      | otherwise = toEnum (ord 'a' + x - 10)

jArray :: [Text] -> Text
jArray xs = "[" <> T.intercalate "," xs <> "]"

jObject :: [(Text, Text)] -> Text
jObject kvs = "{" <> T.intercalate "," [jStr k <> ":" <> v | (k, v) <- kvs] <> "}"
