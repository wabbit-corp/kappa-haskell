{-# LANGUAGE PatternSynonyms #-}

-- | Appendix T standard test harness.
--
-- Implements the §T.3 directive syntax, the §T.4 configuration subset
-- (@mode check@\/@mode run@, the @interpreter@ backend profile, the
-- @runTask@ and @pipelineTrace@ capabilities), the §T.5.1 diagnostic
-- assertions (including @assertDiagnosticMatch@ over a small
-- ECMAScript-style regex engine and @assertDiagnosticExplainExists@
-- over the §3.1.2A registry), §T.5.2 type\/shape assertions, §T.5.4 run
-- assertions (including golden stdout\/stderr files), §T.5.5 portable
-- trace counts, with §T.8 result classification (pass \/ fail \/
-- unsupported \/ harnessError).
--
-- Test forms (§T.2): single-file inline tests; directory suites (a
-- directory containing @suite.ktest@ and\/or @main.kp@ is one suite;
-- all its @.kp@ files are compiled together); incremental step suites
-- are recognized but classified unsupported (this implementation keeps
-- no Chapter 34 session state, so it does not claim the @incremental@
-- capability). Other directory arguments recurse over @**/*.kp@. See
-- TESTING.md for the supported subset and deliberate approximations.
module Kappa.TestHarness
  ( Outcome (..)
  , TestReport (..)
  , Summary (..)
  , runTestFile
  , runTestPath
  , runTestSuitePath
  , summarize
  , reportLine
  ) where

import Control.Applicative ((<|>))
import Control.Exception (SomeException, evaluate, try)
import Control.Monad (filterM)
import Control.Monad.State.Strict qualified as State
import Data.Char (isAlphaNum, isDigit, isLower)
import Data.List (find, isPrefixOf, isSuffixOf, nub, sort, sortOn)
import Data.Maybe (fromMaybe, listToMaybe, mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Encoding.Error as TEE
import qualified Data.ByteString as BS
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Numeric.Natural (Natural)
import Text.Read (readMaybe)
import Kappa.Builtins (prelNat)
import Kappa.Backend.IR
  ( BackendFieldStorage (..)
  , BackendIRViolation (..)
  , BackendNodeId (..)
  , BackendRepresentationDecision (..)
  , BackendRepresentationSubject (..)
  , BackendSourceFieldIdentity (..)
  , KBackendIR (..)
  , kbackendRepresentationCertificates
  , lowerKBackendIRForCapabilities
  , validateKBackendIR
  )
import qualified Kappa.Backend.Repr as Repr
import Kappa.Check
  ( AuditRecord (..)
  , CheckState (..)
  , CtorInfo (..)
  , DataInfo (..)
  , UnsafeConfig (..)
  , checkModule
  , declarationTypesConvertibleAtUse
  , defaultUnsafeConfig
  , exactNaturalRepresentationForState
  , inhabitanceSummaryForState
  , ordinalRepresentationForState
  , recursiveSchemaEdgeRecorded
  , refinementRepresentationForState
  , scriptUnsafeConfig
  , selectedUniverseEvidenceRecorded
  , symbolicCardinalityForState
  , UniverseInferenceClass (..)
  , UniverseInferenceRecord (..)
  , universeInferenceRecord
  )
import Kappa.Core
import Kappa.CoreText
import Kappa.CoreOps (foldTerm)
import Kappa.Cardinality
  ( normalizeCardExpr
  , parseCardExpr
  , renderCardExpr
  )
import Kappa.Diagnostic
import Kappa.Eval (EvalCtx (..), GlobalDef (..), Globals (..), eval, force, quote)
import Kappa.Explain (codeNames, explainExists)
import Kappa.Interp (RunResult (..), runMainCapturedValue)
import Kappa.Inhabitance
  ( InhabitancePurpose (..)
  , InhabitanceSummary (Empty, Subsingleton, Contractible, Unknown)
  , canonicalizeFinite
  )
import Kappa.Level
  ( ConstraintOrigin (..)
  , LevelConstraint (..)
  , PrincipalInferenceOutcome (..)
  , assumptionsConsistent
  , emptyAssumptions
  , inferPrincipalLevelsFor
  , insertAssumption
  , normalizeLevel
  , proveLevelLeq
  , renderLevel
  , SolveResult (..)
  )
import Kappa.Lexer (lexSource)
import Kappa.Parser (parseModule)
import Kappa.NominalVariance
  ( NominalCumulativitySummary (..)
  , stableNominalHash
  , verifyNominalCumulativitySummary
  )
import Kappa.Pipeline (CompiledUnit (..), compileFiles, compileFilesIn, compileFilesWithConfig, importScopeForWithConfig, loadSourceFile, moduleNameRelTo)
import Kappa.Pretty (renderTerm)
import Kappa.Regex (Regex, compileRegex, regexSearch)
import Kappa.Representation
  ( OrdinalRepresentationCertificate (..)
  , RefinementRepresentationCertificate (..)
  , RepresentationContext (..)
  , representationTypeIdentity
  )
import Kappa.Resolve (FixityEnv, defaultFixities, fixitiesOf, resolveModule)
import Kappa.Source (ModuleName (..), Pos (..), Span (..))
import Kappa.Syntax
import Kappa.Token (Located (..), StrFragment (..), StringLit (..), Token (..))
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory)
import System.FilePath (makeRelative, takeDirectory, (</>))
import System.Timeout (timeout)

-- ── Public types ─────────────────────────────────────────────────────

data Outcome = Pass | Fail | Unsupported | HarnessError
  deriving stock (Eq, Show)

data TestReport = TestReport
  { trPath :: !FilePath
  , trOutcome :: !Outcome
  , trDetail :: !Text -- ^ empty for passes
  }

data Summary = Summary
  { sPass :: !Int
  , sFail :: !Int
  , sUnsupported :: !Int
  , sHarnessError :: !Int
  }

summarize :: [TestReport] -> Summary
summarize = foldr step (Summary 0 0 0 0)
  where
    step r s = case trOutcome r of
      Pass -> s {sPass = sPass s + 1}
      Fail -> s {sFail = sFail s + 1}
      Unsupported -> s {sUnsupported = sUnsupported s + 1}
      HarnessError -> s {sHarnessError = sHarnessError s + 1}

reportLine :: TestReport -> Text
reportLine r = label (trOutcome r) <> " " <> T.pack (trPath r) <> detail
  where
    label = \case
      Pass -> "PASS"
      Fail -> "FAIL"
      Unsupported -> "UNSUPPORTED"
      HarnessError -> "HARNESS-ERROR"
    detail
      | T.null (trDetail r) = ""
      | otherwise = " (" <> trDetail r <> ")"

-- ── Directive model ──────────────────────────────────────────────────

data Sev = SError | SWarning | SNote | SInfo
  deriving stock (Eq)

toSeverity :: Sev -> Severity
toSeverity = \case
  SError -> SevError
  SWarning -> SevWarning
  SNote -> SevNote
  SInfo -> SevInfo

data Assertion
  = ANoErrors
  | ANoWarnings
  | AErrorCount !Int
  | AWarningCount !Int
  | ADiag !Sev !Text
  | ADiagNext !Sev !Text !Int -- ^ target line resolved at scan time
  | ADiagAt !Text !Sev !Text !Int !(Maybe Int)
  | ADiagAtRange !Text !Sev !Text !Int !Int !Int !Int
  | ADiagMatch !Text !Regex -- ^ original pattern text + compiled form
  | ADiagFamily !Sev !Text
  | ADiagPayload !Sev !Text !Text !Text -- ^ §T.5.1: sev code-or-family json-pointer expected-json
  | ADiagLabel !Sev !Text !Text -- ^ §T.5.1: sev code-or-family role
  | ADiagRelated !Sev !Text !Text -- ^ §T.5.1: sev code-or-family role
  | ADiagFix !Sev !Text !Text -- ^ §T.5.1: sev code-or-family applicability
  | ADiagFixCount !Sev !Text !Int -- ^ §T.5.1: sev code-or-family n
  | AFixCompiles !Sev !Text -- ^ §T.5.1: apply first machine-applicable fix, recompile, expect no errors
  | ASuppressed !Text !Text -- ^ §T.5.1: primary-code-or-family suppressed-code-or-family
  | AExplainExists !Text -- ^ §3.1.2A registry lookup, code or family
  | AErrorCodes ![Text] -- ^ x-compatible: exact multiset of error codes
  | AEval !Text !Text -- ^ x-compatible: evaluate a global, compare rendering
  | AEvalError !Text !Text -- ^ x-compatible: evaluation fails, message contains
  | AParamQuantities !Text ![Text] -- ^ x-compatible: binder prefixes of a let
  | ADeclDescriptors ![Text] -- ^ x-compatible: decl kind+name descriptors
  | ATraitMembers !Text ![Text] -- ^ x-compatible: trait member names in order
  | AExecute !Text !Text -- ^ x-compatible: run an IO global, compare result rendering
  | ARunStdout !Text !Text -- ^ x-compatible: run an IO global, compare trimmed stdout
  | AInoutParams !Text ![Text] -- ^ x-compatible: inout parameter names of a let
  | ADoItemDescriptors !Text ![Text] -- ^ x-compatible: do-item shapes of a let body
  | ATokenTexts ![Text] -- ^ x-compatible: token source texts occur in this file
  | ATokenKinds ![Text] -- ^ x-compatible: token kinds occur in this file
  | AModuleName !Text -- ^ x-compatible: this file's module-header name
  | AModuleAttrs ![Text] -- ^ x-compatible: module attributes present
  | ADataCtors !Text ![Text] -- ^ x-compatible: data type's constructor names in order
  | AType !Text !Text
  | ADeclKinds ![Text]
  | AFileDeclKinds !Text ![Text] -- ^ path is suite-root relative
  | AStdout !Text
  | AStdoutContains !Text
  | AStderrContains !Text
  | AStdoutFile !Text
  | AStderrFile !Text
  | AExitCode !Int
  | ATraceCount !Text !Text !Text !Int -- ^ event subject relop n
  | AStageDumpEquals !Text !Text !Text -- ^ checkpoint, expected path, effective format
  | AStageDumpRoundTrips !Text
  | AKCoreParses !Text
  | AKCoreRoundTrips !Text
  | AKCoreRejects !Text !Text
  | AKCoreSchemaCertificateValid !Text !Text
  | AKCoreSemanticHashEquals !Text !Text
  | AKCoreLevelEvidence !Text !Text ![Int]
  | ALevelNormalForm !Text !Text
  | ALevelEntails !Bool !Text !Text
  | ALevelSolve !Text
  | ALevelSolveClass !Text
  | APrincipalUniverse !Text !Text
  | AUniverseInferenceClass !Text !Text
  | ARecursiveSchemaEdge !Text !Text !Text
  | ASelectedEvidence !Text !Text
  | AUniverseRole !Text !Int !UniverseVariance
  | ASchemaCertificateValid !Text
  | ASchemaLiftPresent !Text
  | ASchemaLiftCount !Int
  | ASemanticHashDiffers !Text !Text
  | ASemanticHashDiffersFrom !Text
  | ASemanticHashEquals !Text !Text
  | ASemanticHashEqualsFrom !Text
  | AInterfaceContainsUniverseRoles !Text !Text ![UniverseVariance]
  | AInterfaceContainsCurrentUniverseRoles !Text ![UniverseVariance]
  | ATotal !Text
  | AArithmeticCertificatesValid
  | AArithmeticCertificateMutationsReject
  | ATerminationCertificateMutationsReject
  | ARepresentationCertificateMutationsReject
  | AInhabitance !InhabitancePurpose !InhabitanceSummary !Text
  | ASymbolicCardinality !Text !Text
  | AOrdinalRepresentation !Text !Text
  | AExactNaturalRepresentation !Text
  | ARefinementRepresentation !Text !Text
  | ARepresentationClass !Text !Text
  | ARuntimeFieldAbsent !Text !Text
  | AAuditLedger ![Text] -- ^ §4.7: facility names present in the audit ledger, in order

-- One scanned directive, already classified.
data Scanned
  = SMode !Text
  | SEntry !Text
  | SScriptMode -- ^ §T.4 scriptMode: no §8.1 path-derived module names
  | SBackend !Text -- ^ §T.4 backend profile selection (compile\/run only)
  | SConfigNoop -- ^ accepted configuration with no harness effect
  | SUnsafeConfig !(UnsafeConfig -> UnsafeConfig) -- ^ §4.2 build-config flag toggle
  | SUnsupported !Text -- ^ §T.8 unsupported (requires unmet, x- extension, …)
  | SConfigKey !Text !Text -- ^ §T.6 (key, value) of a configuration directive, for duplicate-key conflict detection
  | SStdinFile !Text -- ^ §T.4 stdinFile <path>: must be a readable suite-relative file (checked in IO)
  | SSources ![Text] -- ^ §T.4 ordered, exhaustive suite source list
  | SStageDump !Text !Text -- ^ §T.5.3 checkpoint and suite-relative expected path
  | SAssert !Assertion

-- ── Directive scanning (§T.3) ────────────────────────────────────────

declKindNames :: [Text]
declKindNames =
  [ "import", "export", "fixity", "signature", "let", "data", "type"
  , "trait", "instance", "derive", "effect", "pattern", "expect"
  ]

-- KCore is materialized as canonical KCoreText. Other conceptual Chapter 34
-- checkpoints remain fail-closed until their serializers exist; naming one in
-- an assertion is a harness error rather than a silent unsupported result.
--
-- @assertDiagnosticFixCompiles@ is implemented against the §3.1.6 fix
-- records (apply the first machine-applicable fix, recompile, assert no
-- errors) — see 'AFixCompiles'. No standard directive remains downgraded
-- to a non-§T.8 @unsupported@.

-- §T.4 portable capabilities this harness provides. @runTask@: programs
-- are executed in-process by the tree-walking interpreter. @
-- pipelineTrace@: portable (event, subject) counts are recorded for
-- parse\/buildKFrontIR\/lowerKCore. @stageDumps@ currently materializes the
-- KCore checkpoint as KCoreText. Not provided: @incremental@ (no session
-- state survives between suite roots).
--
-- The corpus's nonstandard capability names are provided as documented
-- compatibility extensions (§T.1): @legacyCharAlias@ — the prelude
-- defines the §28.5 sanctioned @type Char = UnicodeScalar@ alias — and
-- @unicodeSourceWarnings@ — the §3.1.3 optional source-hygiene
-- warnings (W_UNICODE_BIDI_CONTROL, W_UNICODE_CONFUSABLE_IDENTIFIER,
-- W_UNICODE_NON_NORMALIZED_SOURCE_TEXT) are emitted by the pipeline.
supportedCapabilities :: [Text]
supportedCapabilities =
  [ "runTask", "pipelineTrace", "stageDumps", "kcoreText"
  , "arithmeticCertificates"
  , "symbolicCardinality"
  , "representationQueries"
  , "mutualNominalVariance"
  , "legacyCharAlias", "unicodeSourceWarnings"
  ]

-- §T.5.5 portable trace vocabulary.
traceEventNames :: [Text]
traceEventNames =
  [ "parse", "buildKFrontIR", "advancePhase", "emitInterface", "lowerKCore"
  , "evaluateElaboration", "lowerKBackendIR", "lowerTarget", "reuse", "verify"
  ]

traceSubjectNames :: [Text]
traceSubjectNames =
  [ "file", "declaration", "module", "interface", "KCoreUnit"
  , "KBackendIRUnit", "targetUnit"
  ]

traceRelops :: [Text]
traceRelops = ["=", "!=", "<", "<=", ">", ">="]

-- | Scan all directive lines and inline markers. Returns scanned
-- directives in file order and harness errors.
scanDirectives :: Text -> ([Scanned], [Text])
scanDirectives src =
  let lns = zip [1 :: Int ..] (T.lines src)
      results = map (scanLine lns) lns
   in (concat [ss | (ss, _) <- results], concat [es | (_, es) <- results])

scanLine :: [(Int, Text)] -> (Int, Text) -> ([Scanned], [Text])
scanLine allLines (lno, line)
  | "--!!" `T.isPrefixOf` stripped =
      ([], ["line " <> tshow lno <> ": inline '--!!' marker requires source text on the same line (§T.3)"])
  | "--!" `T.isPrefixOf` stripped =
      let body = T.strip (T.drop 3 stripped)
       in parseDirective allLines lno body
  | Just codes <- inlineMarker line =
      -- same-line counterpart of assertDiagnosticNext (§T.5.1); each code
      -- must denote a real diagnostic code (§T.5.1: numeric/unregistered
      -- spellings are ill-typed, hence a harness error, §T.3)
      case [why | c <- codes, Just why <- [invalidCodeReason c]] of
        [] -> ([SAssert (ADiagNext (sevOfCode c) c lno) | c <- codes], [])
        (why : _) -> ([], ["line " <> tshow lno <> ": inline marker " <> why])
  | otherwise = ([], [])
  where
    stripped = T.stripStart line
    -- Inline codes default to severity error per §T.5.1; W_-prefixed
    -- codes match warnings (pragmatic extension, see TESTING.md).
    sevOfCode c = if "W_" `T.isPrefixOf` c then SWarning else SError

-- | Detect an inline @--!!@ marker after ordinary source text.
inlineMarker :: Text -> Maybe [Text]
inlineMarker line =
  case T.breakOn "--!!" line of
    (pre, rest)
      | T.null rest -> Nothing
      | T.null preStripped -> Nothing
      | "--" `T.isPrefixOf` preStripped -> Nothing
      | otherwise ->
          case T.words (T.drop 4 rest) of
            [] -> Nothing
            codes -> Just codes
      where
        preStripped = T.stripStart pre

parseDirective :: [(Int, Text)] -> Int -> Text -> ([Scanned], [Text])
parseDirective allLines lno body =
  case T.words body of
    [] -> bad "empty directive"
    (name : args) -> dispatch name args
  where
    rest = T.strip (T.drop (T.length (T.takeWhile (/= ' ') body)) body)
    bad msg = ([], ["line " <> tshow lno <> ": " <> msg])
    ok d = ([d], [])
    unsup why = ok (SUnsupported why)
    -- §T.6: a configuration directive also contributes its (key, value)
    -- to the suite's configuration so that a later duplicate key with a
    -- conflicting value can make the suite ill-formed.
    cfg key val d = ([SConfigKey key val, d], [])

    dispatch name args = case name of
      "mode" -> case args of
        ["check"] -> cfg "mode" "check" (SMode "check")
        ["run"] -> cfg "mode" "run" (SMode "run")
        ["interface"] -> cfg "mode" "interface" (SMode "interface")
        ["analyze"] -> cfg "mode" "analyze" (SUnsupported "mode analyze is not supported")
        -- mode compile: the interpreter's executable form is the
        -- evaluated KCore global environment; compiling runs the full
        -- pipeline through that lowering without executing an entry
        ["compile"] -> cfg "mode" "compile" (SMode "compile")
        _ -> bad "malformed 'mode' directive"
      -- packageMode/scriptMode are two values of the §T.4 "module-naming
      -- mode" configuration key; specifying both is a conflicting
      -- duplicate (§T.6).
      "packageMode" | null args -> cfg "moduleMode" "package" SConfigNoop
      "scriptMode" | null args -> cfg "moduleMode" "script" SScriptMode
      "backend" -> case args of
        ["interpreter"] -> cfg "backend" "interpreter" SConfigNoop -- the only provided profile
        -- §T.4: 'backend <profile>' selects the profile for 'compile'
        -- and 'run' tests only; whether it makes the test unsupported
        -- is decided once the effective mode is known
        [p] -> cfg "backend" p (SBackend p)
        _ -> bad "malformed 'backend' directive"
      "noPrelude" | null args ->
        cfg "implicit_prelude" "false" (SUnsafeConfig (\c -> c {implicitPrelude = False}))
      "entry" -> case args of
        [q] -> cfg "entry" q (SEntry q)
        _ -> bad "malformed 'entry' directive"
      -- §T.4 runArgs/stdinFile: this implementation's run task has no
      -- argv or standard-input surface (the prelude exposes no primitive
      -- that observes either; see Interp.runPrimIO'), so the program's
      -- observable behavior is identical to the §T.4 defaults (empty
      -- argument list, empty standard input). We therefore *honor* these
      -- standard directives rather than downgrading them to the
      -- non-§T.8 'unsupported': we validate them (a malformed runArgs
      -- string literal or an unreadable stdinFile is a harness error,
      -- §T.3/§T.8) and otherwise accept them as configuration. No program
      -- can spuriously pass: one that needs argv/stdin cannot even be
      -- written without an unresolved name (E_NAME_UNRESOLVED).
      "runArgs"
        | T.null rest -> cfg "runArgs" "" SConfigNoop -- default: empty list
        | otherwise -> case parseStringLiterals rest of
            Just lits -> cfg "runArgs" (T.intercalate "\0" lits) SConfigNoop
            Nothing -> bad "malformed string literal in 'runArgs' directive"
      "stdinFile" -> case args of
        [p] -> cfg "stdinFile" p (SStdinFile p)
        _ -> bad "malformed 'stdinFile' directive"
      "dumpFormat" -> case args of
        ["json"] -> cfg "dumpFormat" "json" SConfigNoop
        ["sexpr"] -> cfg "dumpFormat" "sexpr" SConfigNoop
        ["kcore"] -> cfg "dumpFormat" "kcore" SConfigNoop
        _ -> bad "malformed 'dumpFormat' directive"
      "canonicalDumps" | null args -> cfg "canonicalDumps" "true" SConfigNoop
      "sources"
        | not (null args) -> ok (SSources args)
        | otherwise -> bad "malformed 'sources' directive"
      "requires" -> case args of
        ["mode", "package"] -> ok SConfigNoop -- met: packageMode is the default
        ["mode", "script"] -> unsup "requires mode script: scriptMode unsupported"
        ["backend", "interpreter"] -> ok SConfigNoop -- met (§T.4)
        ("backend" : p) -> unsup ("requires backend " <> T.unwords p <> ": not provided")
        ["capability", c]
          | c `elem` supportedCapabilities -> ok SConfigNoop
          | otherwise -> unsup ("requires capability " <> c <> ": not provided")
        _ -> bad "malformed 'requires' directive"
      "assertNoErrors" -> noArgs ANoErrors
      "assertNoWarnings" -> noArgs ANoWarnings
      "assertErrorCount" -> withCount AErrorCount
      "assertWarningCount" -> withCount AWarningCount
      "assertDiagnostic" -> withSevCode ADiag
      "assertDiagnosticNext" -> nextAssert
      "assertDiagnosticHere" -> nextAssert -- deprecated alias (§T.5.1)
      "assertDiagnosticFamily" -> withSevCode ADiagFamily
      -- §T.5.1 structured-diagnostic assertions over the machine-readable
      -- record (not the rendered prose).
      "assertDiagnosticPayload" -> case args of
        (sevT : cf : ptr : exprToks)
          | Just sev <- parseSev sevT, not (null exprToks) ->
              requireCode cf (ok (SAssert (ADiagPayload sev cf ptr (T.unwords exprToks))))
        _ -> bad "malformed 'assertDiagnosticPayload' directive"
      "assertDiagnosticLabel" -> case args of
        [sevT, cf, role] | Just sev <- parseSev sevT ->
          requireCode cf (ok (SAssert (ADiagLabel sev cf role)))
        _ -> bad "malformed 'assertDiagnosticLabel' directive"
      "assertDiagnosticRelated" -> case args of
        [sevT, cf, role] | Just sev <- parseSev sevT ->
          requireCode cf (ok (SAssert (ADiagRelated sev cf role)))
        _ -> bad "malformed 'assertDiagnosticRelated' directive"
      "assertDiagnosticFix" -> case args of
        [sevT, cf, appl] | Just sev <- parseSev sevT ->
          requireCode cf (ok (SAssert (ADiagFix sev cf appl)))
        _ -> bad "malformed 'assertDiagnosticFix' directive"
      "assertDiagnosticFixCount" -> case args of
        [sevT, cf, nT] | Just sev <- parseSev sevT, Just n <- parseNat nT ->
          requireCode cf (ok (SAssert (ADiagFixCount sev cf n)))
        _ -> bad "malformed 'assertDiagnosticFixCount' directive"
      "assertSuppressedDiagnostic" -> case args of
        [primary, supp] ->
          requireCode primary (requireCode supp (ok (SAssert (ASuppressed primary supp))))
        _ -> bad "malformed 'assertSuppressedDiagnostic' directive"
      -- §T.5.1: apply the first machine-applicable fix of the first
      -- matching diagnostic and recompile under the same configuration.
      "assertDiagnosticFixCompiles" -> case args of
        [sevT, cf] | Just sev <- parseSev sevT ->
          requireCode cf (ok (SAssert (AFixCompiles sev cf)))
        _ -> bad "malformed 'assertDiagnosticFixCompiles' directive"
      "assertStageDump" -> case args of
        [chk, "equals", path] -> ok (SStageDump chk path)
        _ -> bad "malformed 'assertStageDump' directive (expected '<checkpoint> equals <path>')"
      "assertStageDumpRoundTrips" -> case args of
        [checkpoint] -> ok (SAssert (AStageDumpRoundTrips checkpoint))
        _ -> bad "malformed 'assertStageDumpRoundTrips' directive"
      "assertKCoreParses" -> case args of
        [path] -> ok (SAssert (AKCoreParses path))
        _ -> bad "malformed 'assertKCoreParses' directive"
      "assertKCoreRoundTrips" -> case args of
        [path] -> ok (SAssert (AKCoreRoundTrips path))
        _ -> bad "malformed 'assertKCoreRoundTrips' directive"
      "assertKCoreRejects" -> case args of
        [path, code] -> requireCode code (ok (SAssert (AKCoreRejects path code)))
        _ -> bad "malformed 'assertKCoreRejects' directive"
      "assertKCoreSchemaCertificateValid" -> case args of
        [path, family] -> ok (SAssert (AKCoreSchemaCertificateValid path family))
        _ -> bad "malformed 'assertKCoreSchemaCertificateValid' directive"
      "assertKCoreSemanticHashEquals" -> case args of
        [left, right] -> ok (SAssert (AKCoreSemanticHashEquals left right))
        _ -> bad "malformed 'assertKCoreSemanticHashEquals' directive"
      "assertKCoreLevelEvidence" -> case args of
        [path, certificate, "dependencies", dependencyText]
          | Just dependencies <- parseCommaNats dependencyText ->
              ok (SAssert (AKCoreLevelEvidence path certificate dependencies))
        _ -> bad "malformed 'assertKCoreLevelEvidence' directive"
      "assertLevelNormalForm" ->
        case splitDirectiveInfix " equals " rest of
          Just (left, right) -> ok (SAssert (ALevelNormalForm left right))
          Nothing -> bad "malformed 'assertLevelNormalForm' directive"
      "assertLevelEntails" -> levelEntailment True
      "assertLevelDoesNotEntail" -> levelEntailment False
      "assertLevelSolve"
        | validSolveDirective True rest -> ok (SAssert (ALevelSolve rest))
        | otherwise -> bad "malformed 'assertLevelSolve' directive"
      "assertLevelSolveClass"
        | validSolveDirective False rest -> ok (SAssert (ALevelSolveClass rest))
        | otherwise -> bad "malformed 'assertLevelSolveClass' directive"
      "assertPrincipalUniverse" -> case args of
        declaration : levelTokens | not (null levelTokens) ->
          ok (SAssert (APrincipalUniverse declaration (T.unwords levelTokens)))
        _ -> bad "malformed 'assertPrincipalUniverse' directive"
      "assertUniverseInferenceClass" -> case args of
        [declaration, inferenceClass]
          | inferenceClass `elem`
              [ "SolvedPrincipal"
              , "Unsatisfiable"
              , "NoPointwiseLeastSolution"
              , "OutsidePortableInferenceFragment"
              , "BlockedByUnselectedMetas"
              ] -> ok (SAssert (AUniverseInferenceClass declaration inferenceClass))
        _ -> bad "malformed 'assertUniverseInferenceClass' directive"
      "assertRecursiveSchemaEdge" -> case args of
        [caller, callee, relation] -> ok (SAssert (ARecursiveSchemaEdge caller callee relation))
        _ -> bad "malformed 'assertRecursiveSchemaEdge' directive"
      "assertSelectedEvidence" ->
        case splitLastWord rest of
          Just (goal, evidence) -> ok (SAssert (ASelectedEvidence goal evidence))
          Nothing -> bad "malformed 'assertSelectedEvidence' directive"
      "assertUniverseRole" -> case args of
        [family, indexText, roleText]
          | Just index <- parseNat indexText
          , Just role <- parseUniverseVariance roleText ->
              ok (SAssert (AUniverseRole family index role))
        _ -> bad "malformed 'assertUniverseRole' directive"
      "assertSchemaCertificateValid" -> case args of
        [family] -> ok (SAssert (ASchemaCertificateValid family))
        _ -> bad "malformed 'assertSchemaCertificateValid' directive"
      "assertSchemaLiftPresent" -> case args of
        [family] -> ok (SAssert (ASchemaLiftPresent family))
        _ -> bad "malformed 'assertSchemaLiftPresent' directive"
      "assertSchemaLiftCount" -> case args of
        [countText] | Just count <- parseNat countText -> ok (SAssert (ASchemaLiftCount count))
        _ -> bad "malformed 'assertSchemaLiftCount' directive"
      "assertSemanticHashDiffers" -> case args of
        [left, right] -> ok (SAssert (ASemanticHashDiffers left right))
        _ -> bad "malformed 'assertSemanticHashDiffers' directive"
      "assertSemanticHashDiffersFrom" -> case args of
        [target] -> ok (SAssert (ASemanticHashDiffersFrom target))
        _ -> bad "malformed 'assertSemanticHashDiffersFrom' directive"
      "assertSemanticHashEquals" -> case args of
        [target] -> ok (SAssert (ASemanticHashEqualsFrom target))
        [left, right] -> ok (SAssert (ASemanticHashEquals left right))
        _ -> bad "malformed 'assertSemanticHashEquals' directive"
      "assertInterfaceContainsUniverseRoles" -> case args of
        (family : roleTokens)
          | Just roles <- parseUniverseVarianceList (T.unwords roleTokens) ->
              ok (SAssert (AInterfaceContainsCurrentUniverseRoles family roles))
        (path : family : roleTokens)
          | Just roles <- parseUniverseVarianceList (T.unwords roleTokens) ->
              ok (SAssert (AInterfaceContainsUniverseRoles path family roles))
        _ -> bad "malformed 'assertInterfaceContainsUniverseRoles' directive"
      "assertTotal" -> case args of
        [declaration] -> ok (SAssert (ATotal declaration))
        _ -> bad "malformed 'assertTotal' directive"
      -- §T.5.2 Nat/Fin/refinement assertions are parsed here and evaluated
      -- below through production analysis, certificate replay, and verified
      -- KBackendIR queries. Capability checks apply only to representation
      -- classes the selected backend profile does not advertise.
      "assertArithmeticCertificatesValid"
        | null args -> ok (SAssert AArithmeticCertificatesValid)
        | otherwise -> bad "malformed 'assertArithmeticCertificatesValid' directive"
      "assertArithmeticCertificateMutationsReject"
        | null args ->
            ok (SAssert AArithmeticCertificateMutationsReject)
        | otherwise ->
            bad "malformed 'assertArithmeticCertificateMutationsReject' directive"
      "assertTerminationCertificateMutationsReject"
        | null args ->
            ok (SAssert ATerminationCertificateMutationsReject)
        | otherwise ->
            bad "malformed 'assertTerminationCertificateMutationsReject' directive"
      "assertRepresentationCertificateMutationsReject"
        | null args ->
            ok (SAssert ARepresentationCertificateMutationsReject)
        | otherwise ->
            bad "malformed 'assertRepresentationCertificateMutationsReject' directive"
      "assertInhabitance" ->
        case splitDirectiveInfix " for " rest of
          Just (summary, ty)
            | [purposeText, summaryText] <- T.words summary
            , Just purpose <- parseInhabitancePurpose purposeText
            , Just expected <- parseInhabitanceSummary summaryText
            , not (T.null (T.strip ty)) ->
                ok (SAssert (AInhabitance purpose expected (T.strip ty)))
          _ -> bad "malformed 'assertInhabitance' directive"
      "assertSymbolicCardinality" ->
        case splitDirectiveInfix " for " rest of
          Just (expected, ty)
            | not (T.null (T.strip expected))
            , not (T.null (T.strip ty)) ->
                ok (SAssert (ASymbolicCardinality (T.strip expected) (T.strip ty)))
          _ -> bad "malformed 'assertSymbolicCardinality' directive"
      "assertOrdinalRepresentation" ->
        case splitDirectiveInfix " for " rest of
          Just (expected, ty)
            | not (T.null (T.strip expected))
            , not (T.null (T.strip ty)) ->
                ok (SAssert (AOrdinalRepresentation (T.strip expected) (T.strip ty)))
          _ -> bad "malformed 'assertOrdinalRepresentation' directive"
      "assertExactNaturalRepresentation" ->
        case args of
          "for" : ty
            | not (null ty) ->
                ok (SAssert (AExactNaturalRepresentation (T.unwords ty)))
          _ -> bad "malformed 'assertExactNaturalRepresentation' directive"
      "assertRefinementRepresentation" ->
        case splitDirectiveInfix " for " rest of
          Just (baseTy, refinedTy)
            | not (T.null (T.strip baseTy))
            , not (T.null (T.strip refinedTy)) ->
                ok (SAssert (ARefinementRepresentation (T.strip baseTy) (T.strip refinedTy)))
          _ -> bad "malformed 'assertRefinementRepresentation' directive"
      "assertRepresentationClass" -> case args of
        declaration : representation
          | not (null representation) ->
              ok
                (SAssert
                  (ARepresentationClass declaration (T.unwords representation)))
        _ -> bad "malformed 'assertRepresentationClass' directive"
      "assertRuntimeFieldAbsent" -> case args of
        [declaration, field]
          | not (T.null declaration), not (T.null field) ->
              ok (SAssert (ARuntimeFieldAbsent declaration field))
        _ -> bad "malformed 'assertRuntimeFieldAbsent' directive"
      "assertDiagnosticMatch"
        | T.null rest -> bad "malformed 'assertDiagnosticMatch' directive (empty pattern)"
        | otherwise -> case compileRegex rest of
            Right re -> ok (SAssert (ADiagMatch rest re))
            Left err -> bad ("invalid 'assertDiagnosticMatch' pattern: " <> err)
      "assertDiagnosticExplainExists" -> case args of
        -- the assertion's whole purpose is to query whether an explanation
        -- exists, so an *unregistered* spelling legitimately FAILs rather
        -- than being ill-typed; only a purely numeric code is malformed.
        [cf]
          | T.all isDigit cf && not (T.null cf) ->
              bad ("directive 'assertDiagnosticExplainExists': '" <> cf
                     <> "' is a purely numeric code, which is not a valid standard-harness diagnostic code (§T.5.1)")
          | otherwise -> ok (SAssert (AExplainExists cf))
        _ -> bad "malformed 'assertDiagnosticExplainExists' directive"
      "assertDiagnosticAt" -> case args of
        [p, sevT, code, lnT]
          | Just sev <- parseSev sevT, Just n <- parseNat lnT ->
              requireCode code (ok (SAssert (ADiagAt p sev code n Nothing)))
        [p, sevT, code, lnT, colT]
          | Just sev <- parseSev sevT, Just n <- parseNat lnT, Just c <- parseNat colT ->
              requireCode code (ok (SAssert (ADiagAt p sev code n (Just c))))
        [p, sevT, code, slT, scT, "-", elT, ecT]
          | Just sev <- parseSev sevT
          , Just sl <- parseNat slT, Just sc <- parseNat scT
          , Just el <- parseNat elT, Just ec <- parseNat ecT ->
              requireCode code (ok (SAssert (ADiagAtRange p sev code sl sc el ec)))
        _ -> bad "malformed 'assertDiagnosticAt' directive"
      "assertType" -> case args of
        (nm : tyToks) | not (null tyToks) -> ok (SAssert (AType nm (T.unwords tyToks)))
        _ -> bad "malformed 'assertType' directive"
      "assertDeclKinds" ->
        case parseKindList rest of
          Just kinds -> ok (SAssert (ADeclKinds kinds))
          Nothing -> bad "malformed 'assertDeclKinds' kind list"
      "assertFileDeclKinds" -> case T.words rest of
        (p : kindToks) | not (null kindToks) ->
          case parseKindList (T.unwords kindToks) of
            Just kinds -> ok (SAssert (AFileDeclKinds p kinds))
            Nothing -> bad "malformed 'assertFileDeclKinds' kind list"
        _ -> bad "malformed 'assertFileDeclKinds' directive"
      "assertStdout" -> withString AStdout
      "assertStdoutContains" -> withString AStdoutContains
      "assertStderrContains" -> withString AStderrContains
      "assertStdoutFile" -> withPath AStdoutFile
      "assertStderrFile" -> withPath AStderrFile
      "assertExitCode" -> withCount AExitCode
      "assertTraceCount" -> case args of
        [ev, subj, rel, nT]
          | Just n <- parseNat nT
          , rel `elem` traceRelops ->
              if ev `elem` traceEventNames && subj `elem` traceSubjectNames
                then ok (SAssert (ATraceCount ev subj rel n))
                else bad "non-portable event or subject in 'assertTraceCount' (§T.5.5)"
        _ -> bad "malformed 'assertTraceCount' directive"
      -- §T.7 cross-step assertions: syntax is validated, but the
      -- incremental capability is not provided, so the suite using
      -- them classifies unsupported (the 'requires capability
      -- incremental' gate, when present, is reported first).
      "assertStepNoErrors" -> stepAssert 1
      "assertStepErrorCount" -> stepAssert 2
      "assertStepWarningCount" -> stepAssert 2
      "assertStepTraceCount" -> case args of
        [stepT, ev, subj, rel, nT]
          | Just _ <- parseNat stepT
          , Just _ <- parseNat nT
          , rel `elem` traceRelops
          , ev `elem` traceEventNames
          , subj `elem` traceSubjectNames ->
              unsup "cross-step assertions need capability 'incremental', which is not provided (§T.7)"
        _ -> bad "malformed 'assertStepTraceCount' directive"
      -- compatibility extensions for the external fixture corpus
      "assertDiagnosticCodes" ->
        let codes = map T.strip (T.splitOn "," rest)
         in if null codes || any T.null codes
              then bad "malformed 'assertDiagnosticCodes' code list"
              else case [why | c <- codes, Just why <- [invalidCodeReason c]] of
                (why : _) -> bad ("directive 'assertDiagnosticCodes': " <> why)
                [] -> ok (SAssert (AErrorCodes codes))
      "assertEval" -> evalAssert
      -- compatibility configuration: the corpus gates its 'unsafeConsume'
      -- linear sink behind this directive; this prelude always provides
      -- the sink (§T.1 permits nonstandard directives), so it is a no-op
      "allow_unsafe_consume" | null args -> ok SConfigNoop
      -- §4.2 build-level gating: enable an unsafe/debug facility for this
      -- suite (defaults are all-disabled, package mode).
      "allow_unhiding" | null args -> ok (SUnsafeConfig (\c -> c {allowUnhiding = True}))
      "allow_clarify" | null args -> ok (SUnsafeConfig (\c -> c {allowClarify = True}))
      "allow_assert_terminates" | null args -> ok (SUnsafeConfig (\c -> c {allowAssertTerminates = True}))
      "allow_assert_reducible" | null args -> ok (SUnsafeConfig (\c -> c {allowAssertReducible = True}))
      "allow_unsafe_assert_proof" | null args -> ok (SUnsafeConfig (\c -> c {allowUnsafeAssertProof = True}))
      "allow_debug_introspection" | null args -> ok (SUnsafeConfig (\c -> c {allowDebugIntrospection = True}))
      -- §4.7: assert the unsafe/debug audit ledger lists exactly these
      -- facility names (in order). With no args, the ledger must be empty.
      "assertAuditLedger" -> ok (SAssert (AAuditLedger args))
      "assertParameterQuantities" -> case args of
        (nm : qs) | not (null qs) -> ok (SAssert (AParamQuantities nm qs))
        _ -> bad "malformed 'assertParameterQuantities' directive"
      -- compatibility extensions: run a named IO entrypoint regardless
      -- of mode and compare the final value / captured stdout
      "assertExecute" -> case T.words rest of
        (nm : more) | not (null more) -> ok (SAssert (AExecute nm (T.unwords more)))
        _ -> bad "malformed 'assertExecute' directive"
      "assertRunStdout" -> case T.words rest of
        (nm : more) | not (null more) -> ok (SAssert (ARunStdout nm (T.unwords more)))
        _ -> bad "malformed 'assertRunStdout' directive"
      "assertInoutParameters" -> case map (T.filter (/= ',')) (T.words rest) of
        (nm : ps) | not (null ps), all (not . T.null) ps ->
          ok (SAssert (AInoutParams nm ps))
        _ -> bad "malformed 'assertInoutParameters' directive"
      "assertDoItemDescriptors" -> case T.words rest of
        (nm : _ : _) ->
          let descPart = T.strip (T.drop (T.length nm) (T.stripStart rest))
              descs = map (T.unwords . T.words) (T.splitOn "," descPart)
           in if not (null descs) && all (not . T.null) descs
                then ok (SAssert (ADoItemDescriptors nm descs))
                else bad "malformed 'assertDoItemDescriptors' descriptor list"
        _ -> bad "malformed 'assertDoItemDescriptors' directive"
      "assertContainsTokenTexts" -> tokenTextsAssert
      "x-assertContainsTokenTexts" -> tokenTextsAssert
      -- supported x- extension directives (§T.3 allows a harness to
      -- implement extension directives; unsupported ones classify the
      -- test unsupported below)
      "x-assertContainsTokenKinds" ->
        let kinds = map T.strip (T.splitOn "," rest)
         in if not (null kinds) && all (`elem` map fst portableTokenKinds) kinds
              then ok (SAssert (ATokenKinds kinds))
              else bad "malformed or unknown token kind in 'x-assertContainsTokenKinds'"
      "x-assertModule" -> case args of
        [mn] -> ok (SAssert (AModuleName mn))
        _ -> bad "malformed 'x-assertModule' directive"
      "x-assertModuleAttributes" ->
        let attrs = map T.strip (T.splitOn "," rest)
         in if not (null attrs) && all (not . T.null) attrs
              then ok (SAssert (AModuleAttrs attrs))
              else bad "malformed 'x-assertModuleAttributes' directive"
      "x-assertDataConstructors" -> case T.words rest of
        (tn : _ : _) ->
          let ctorPart = T.strip (T.drop (T.length tn) (T.stripStart rest))
              ctors = map T.strip (T.splitOn "," ctorPart)
           in if all (not . T.null) ctors
                then ok (SAssert (ADataCtors tn ctors))
                else bad "malformed 'x-assertDataConstructors' constructor list"
        _ -> bad "malformed 'x-assertDataConstructors' directive"
      "x-assertEval" -> evalAssert
      "assertEvalErrorContains" -> evalErrAssert
      "x-assertEvalErrorContains" -> evalErrAssert
      "x-assertDeclDescriptors" ->
        let entries = map (T.unwords . T.words) (T.splitOn "," rest)
         in if not (null entries) && all (not . T.null) entries
              then ok (SAssert (ADeclDescriptors entries))
              else bad "malformed 'x-assertDeclDescriptors' descriptor list"
      "x-assertTraitMembers" -> case T.words rest of
        (tn : _ : _) ->
          let memberPart = T.strip (T.drop (T.length tn) (T.stripStart rest))
              members = map T.strip (T.splitOn "," memberPart)
           in if all (not . T.null) members
                then ok (SAssert (ATraitMembers tn members))
                else bad "malformed 'x-assertTraitMembers' member list"
        _ -> bad "malformed 'x-assertTraitMembers' directive"
      _
        | "x-" `T.isPrefixOf` name ->
            unsup ("extension directive '" <> name <> "' is not supported")
        | otherwise ->
            -- §T.3: any unknown non-extension directive is a harness
            -- error (this covers other implementations' private
            -- directives, which are not part of Appendix T)
            bad ("unknown directive '" <> name <> "' is not defined by Appendix T (§T.3)")
      where
        evalAssert = case T.words rest of
          (nm : more) | not (null more) -> ok (SAssert (AEval nm (T.unwords more)))
          _ -> bad ("malformed '" <> name <> "' directive")
        evalErrAssert = case T.words rest of
          (nm : more) | not (null more) -> ok (SAssert (AEvalError nm (T.unwords more)))
          _ -> bad ("malformed '" <> name <> "' directive")
        tokenTextsAssert =
          let toks = map T.strip (T.splitOn "," rest)
           in if not (null toks) && all (not . T.null) toks
                then ok (SAssert (ATokenTexts toks))
                else bad ("malformed '" <> name <> "' token list")
        noArgs a
          | null args = ok (SAssert a)
          | otherwise = bad ("directive '" <> name <> "' takes no arguments")
        levelEntailment expected =
          case splitDirectiveInfix " <= " rest of
            Just (left, right) -> ok (SAssert (ALevelEntails expected left right))
            Nothing -> bad ("malformed '" <> name <> "' directive")
        withCount f = case args of
          [nT] | Just n <- parseNat nT -> ok (SAssert (f n))
          _ -> bad ("malformed '" <> name <> "' directive")
        -- §T.5.1: the code/family argument must be a real code or family;
        -- a numeric or unregistered spelling is an ill-typed argument and
        -- thus a harness error (§T.3), not a satisfiable assertion.
        requireCode code k = case invalidCodeReason code of
          Just why -> bad ("directive '" <> name <> "': " <> why)
          Nothing -> k
        withSevCode f = case args of
          [sevT, code] | Just sev <- parseSev sevT ->
            requireCode code (ok (SAssert (f sev code)))
          _ -> bad ("malformed '" <> name <> "' directive")
        nextAssert = case args of
          [sevT, code]
            | Just sev <- parseSev sevT ->
                requireCode code $
                  case targetLineAfter allLines lno of
                    Just t -> ok (SAssert (ADiagNext sev code t))
                    Nothing -> bad "assertDiagnosticNext has no following source line"
          _ -> bad ("malformed '" <> name <> "' directive")
        withString f = case parseStringLiteral rest of
          Just s -> ok (SAssert (f s))
          Nothing -> bad ("malformed string literal in '" <> name <> "' directive")
        withPath f = case args of
          [p] -> ok (SAssert (f p))
          _ -> bad ("malformed '" <> name <> "' directive")
        stepAssert n
          | length args == n && all (\a -> parseNat a /= Nothing) args =
              unsup "cross-step assertions need capability 'incremental', which is not provided (§T.7)"
          | otherwise = bad ("malformed '" <> name <> "' directive")

parseKindList :: Text -> Maybe [Text]
parseKindList t =
  let kinds = map T.strip (T.splitOn "," t)
   in if not (null kinds) && all (`elem` declKindNames) kinds && all (not . T.null) kinds
        then Just kinds
        else Nothing

-- | First following line that is nonblank, not comment-only, and not a
-- directive line (§T.5.1).
targetLineAfter :: [(Int, Text)] -> Int -> Maybe Int
targetLineAfter allLines lno =
  case [n | (n, l) <- allLines, n > lno, isSourceLine l] of
    (n : _) -> Just n
    [] -> Nothing
  where
    isSourceLine l =
      let s = T.stripStart l
       in not (T.null s) && not ("--" `T.isPrefixOf` s)

parseSev :: Text -> Maybe Sev
parseSev = \case
  "error" -> Just SError
  "warning" -> Just SWarning
  "note" -> Just SNote
  "info" -> Just SInfo
  _ -> Nothing

-- | §T.5.1 code validity. A directive's @<code>@ "denotes a diagnostic
-- code as defined by §3.1"; "purely numeric codes are not valid
-- standard-harness diagnostic codes." An assertion naming a code that is
-- purely numeric, or that names no code or family this implementation
-- can ever produce or recognize, is an *ill-typed directive argument*
-- and therefore a harness error (§T.3), not a satisfiable assertion that
-- merely fails. We accept a spelling that (a) the §3.1.2A registry knows
-- as a code or family, or (b) is a recognized §3.1.4 portable alias of a
-- code this implementation emits; everything else (numbers, typos,
-- another implementation's private codes we cannot match) is malformed.
-- Returns @Just reason@ when the spelling is *not* a valid code.
invalidCodeReason :: Text -> Maybe Text
invalidCodeReason c
  | T.null c = Just "empty diagnostic code"
  | T.all isDigit c =
      Just ("'" <> c <> "' is a purely numeric code, which is not a valid standard-harness diagnostic code (§T.5.1)")
  | validCodeSpelling c = Nothing
  | otherwise =
      Just ("'" <> c <> "' is not a registered diagnostic code or family (§3.1.2A); the assertion is ill-typed (§T.5.1)")

-- | A @<code-or-family>@ spelling the harness can match: a registered
-- §3.1.2A code or family (via 'explainExists'), or a recognized §3.1.4
-- portable-alias spelling.
validCodeSpelling :: Text -> Bool
validCodeSpelling c = explainExists c || portableAlias c /= Nothing

parseNat :: Text -> Maybe Int
parseNat t
  | not (T.null t) && T.all isDigit t =
      -- parse through Integer and range-check: a directive count that
      -- overflows Int is malformed, not silently wrapped to a negative.
      let v = read (T.unpack t) :: Integer
       in if v > toInteger (maxBound :: Int) then Nothing else Just (fromInteger v)
  | otherwise = Nothing

parseNatural :: Text -> Maybe Natural
parseNatural text
  | not (T.null text)
  , T.all isDigit text =
      readMaybe (T.unpack text)
  | otherwise = Nothing

parseInhabitancePurpose :: Text -> Maybe InhabitancePurpose
parseInhabitancePurpose = \case
  "SourceReachability" -> Just SourceReachability
  "Completion" -> Just Completion
  "RuntimeShape" -> Just RuntimeShape
  "Optimization" -> Just Optimization
  _ -> Nothing

parseInhabitanceSummary :: Text -> Maybe InhabitanceSummary
parseInhabitanceSummary = \case
  "Empty" -> Just Empty
  "Subsingleton" -> Just Subsingleton
  "Contractible" -> Just Contractible
  "Unknown" -> Just Unknown
  summary -> do
    cardinalityText <- T.stripPrefix "Finite(" summary >>= T.stripSuffix ")"
    cardinality <- parseNatural cardinalityText
    if cardinality >= 2
      then Just (canonicalizeFinite cardinality)
      else Nothing

parseCommaNats :: Text -> Maybe [Int]
parseCommaNats text =
  let pieces = map T.strip (T.splitOn "," text)
   in if null pieces || any T.null pieces
        then Nothing
        else traverse parseNat pieces

splitDirectiveInfix :: Text -> Text -> Maybe (Text, Text)
splitDirectiveInfix separator input =
  let (left, suffix) = T.breakOn separator input
      right = T.drop (T.length separator) suffix
   in if T.null suffix || T.null (T.strip left) || T.null (T.strip right)
        then Nothing
        else Just (T.strip left, T.strip right)

splitLastWord :: Text -> Maybe (Text, Text)
splitLastWord input =
  case reverse (T.words input) of
    evidence : reversedGoal@(_ : _) ->
      Just (T.unwords (reverse reversedGoal), evidence)
    _ -> Nothing

validSolveDirective :: Bool -> Text -> Bool
validSolveDirective expectsAssignments input =
  case splitDirectiveInfix " where " input of
    Just (selected, rest)
      | bracketed selected ->
          if expectsAssignments
            then case splitDirectiveInfix " gives " rest of
              Just (constraints, assignments) -> bracketed constraints && bracketed assignments
              Nothing -> False
            else case splitLastWord rest of
              Just (constraints, outcome) ->
                bracketed constraints
                  && outcome `elem`
                    [ "SolvedPrincipal"
                    , "Unsatisfiable"
                    , "NoPointwiseLeastSolution"
                    , "OutsidePortableInferenceFragment"
                    , "BlockedByUnselectedMetas"
                    ]
              Nothing -> False
    _ -> False
  where
    bracketed text = "[" `T.isPrefixOf` T.strip text && "]" `T.isSuffixOf` T.strip text

data FixtureLevelToken
  = FLWord !Text
  | FLMeta !Text
  | FLNat !Integer
  | FLPlus
  | FLLeftParen
  | FLRightParen
  deriving stock (Eq, Show)

data FixtureLevelParserState = FixtureLevelParserState
  { flpTokens :: ![FixtureLevelToken]
  , flpMetas :: !(Map.Map Text Int)
  , flpNextMeta :: !Int
  }

type FixtureLevelParser = State.StateT FixtureLevelParserState (Either Text)

parseFixtureLevels :: [Text] -> Either Text [Level]
parseFixtureLevels inputs = fst <$> parseFixtureLevelsWithMetas inputs

parseFixtureLevelsWithMetas :: [Text] -> Either Text ([Level], Map.Map Text Int)
parseFixtureLevelsWithMetas inputs = do
  (levels, finalState) <- State.runStateT (traverse parseOne inputs) initialState
  pure (levels, flpMetas finalState)
  where
    initialState = FixtureLevelParserState [] Map.empty 0
    parseOne input = do
      tokens <- fixtureLift (tokenizeFixtureLevel input)
      State.modify' (\state -> state {flpTokens = tokens})
      level <- parseFixtureLevelExpr
      remaining <- State.gets flpTokens
      case remaining of
        [] -> pure level
        token : _ -> fixtureFail ("unexpected token " <> tshow token <> " in '" <> input <> "'")

tokenizeFixtureLevel :: Text -> Either Text [FixtureLevelToken]
tokenizeFixtureLevel = go . T.unpack
  where
    go [] = Right []
    go (character : rest)
      | character == ' ' || character == '\t' = go rest
      | character == '+' = (FLPlus :) <$> go rest
      | character == '(' = (FLLeftParen :) <$> go rest
      | character == ')' = (FLRightParen :) <$> go rest
      | character == '?' =
          let (name, suffix) = span wordCharacter rest
           in if null name
                then Left "a level metavariable '?' must be followed by an identifier"
                else (FLMeta (T.pack name) :) <$> go suffix
      | character >= '0' && character <= '9' =
          let (digits, suffix) = span (\c -> c >= '0' && c <= '9') (character : rest)
           in (FLNat (read digits) :) <$> go suffix
      | wordCharacter character =
          let (word, suffix) = span wordCharacter (character : rest)
           in (FLWord (T.pack word) :) <$> go suffix
      | otherwise = Left ("unsupported character '" <> T.singleton character <> "' in level assertion")
    wordCharacter character =
      character == '_' || character == '.' || character == '#' || character == 'ω'
        || (character >= 'a' && character <= 'z')
        || (character >= 'A' && character <= 'Z')
        || (character >= '0' && character <= '9')

parseFixtureLevelExpr :: FixtureLevelParser Level
parseFixtureLevelExpr = do
  first <- parseFixtureLevelApplication
  continue first
  where
    continue left = fixturePeek >>= \case
      Just FLPlus -> fixturePop >> parseFixtureLevelApplication >>= continue . levelAdd left
      _ -> pure left

parseFixtureLevelApplication :: FixtureLevelParser Level
parseFixtureLevelApplication = do
  headLevel <- parseFixtureLevelPrefix
  arguments <- parseArguments
  pure $ case arguments of
    [] -> headLevel
    _ -> LNeutral (NeutralLevelSymbol "$apply" (headLevel : arguments))
  where
    parseArguments = fixturePeek >>= \case
      Just token | fixtureStartsAtom token -> (:) <$> parseFixtureLevelPrefix <*> parseArguments
      _ -> pure []

parseFixtureLevelPrefix :: FixtureLevelParser Level
parseFixtureLevelPrefix = fixturePeek >>= \case
  Just (FLWord "succ") -> fixturePop >> levelSucc <$> parseFixtureLevelPrefix
  Just (FLWord "max") -> fixturePop >> levelMax <$> parseFixtureLevelPrefix <*> parseFixtureLevelPrefix
  _ -> parseFixtureLevelAtom

parseFixtureLevelAtom :: FixtureLevelParser Level
parseFixtureLevelAtom = fixturePop >>= \case
  FLNat value -> pure (finiteLevel value)
  FLWord "omega" -> pure LOmega
  FLWord "ω" -> pure LOmega
  FLWord name -> pure (LNeutral (NeutralLevelSymbol ("fixture:" <> name) []))
  FLMeta name -> do
    known <- State.gets (Map.lookup name . flpMetas)
    case known of
      Just meta -> pure (LMeta meta)
      Nothing -> do
        meta <- State.gets flpNextMeta
        State.modify' $ \state ->
          state
            { flpMetas = Map.insert name meta (flpMetas state)
            , flpNextMeta = meta + 1
            }
        pure (LMeta meta)
  FLLeftParen -> do
    level <- parseFixtureLevelExpr
    fixturePop >>= \case
      FLRightParen -> pure level
      token -> fixtureFail ("expected ')', found " <> tshow token)
  token -> fixtureFail ("expected level atom, found " <> tshow token)

fixtureStartsAtom :: FixtureLevelToken -> Bool
fixtureStartsAtom = \case
  FLWord _ -> True
  FLMeta _ -> True
  FLNat _ -> True
  FLLeftParen -> True
  _ -> False

fixturePeek :: FixtureLevelParser (Maybe FixtureLevelToken)
fixturePeek = State.gets (listToMaybe . flpTokens)

fixturePop :: FixtureLevelParser FixtureLevelToken
fixturePop = do
  tokens <- State.gets flpTokens
  case tokens of
    [] -> fixtureFail "unexpected end of level expression"
    token : rest -> State.modify' (\state -> state {flpTokens = rest}) >> pure token

fixtureFail :: Text -> FixtureLevelParser a
fixtureFail detail = State.StateT (const (Left detail))

fixtureLift :: Either Text a -> FixtureLevelParser a
fixtureLift result = State.StateT $ \state -> (, state) <$> result

checkFixtureLevelSolve :: Text -> Either Text AssertResult
checkFixtureLevelSolve directive = do
  (targets, constraints, expectedAssignments) <- parseFixtureSolve True directive
  let outcome = inferPrincipalLevelsFor targets constraints
  case outcome of
    SolvedPrincipal assignments ->
      pure $ requireFixture
        (all (\(meta, expected) -> Map.lookup meta assignments == Just (normalizeLevel expected)) expectedAssignments)
        ("principal assignments are " <> tshow assignments <> ", expected " <> tshow expectedAssignments)
    other -> pure (AssertFail ("level inference returned " <> fixtureOutcomeName other <> ", expected SolvedPrincipal"))

checkFixtureLevelSolveClass :: Text -> Either Text AssertResult
checkFixtureLevelSolveClass directive = do
  (targets, constraints, expectedClass) <- parseFixtureSolveClass directive
  let actual = fixtureOutcomeName (inferPrincipalLevelsFor targets constraints)
  pure (requireFixture (actual == expectedClass) ("level inference returned " <> actual <> ", expected " <> expectedClass))

parseFixtureSolve :: Bool -> Text -> Either Text (Set.Set Int, [LevelConstraint], [(Int, Level)])
parseFixtureSolve _ directive = do
  (selectedText, rest) <- maybe (Left "missing 'where'") Right (splitDirectiveInfix " where " directive)
  (constraintsText, assignmentsText) <- maybe (Left "missing 'gives'") Right (splitDirectiveInfix " gives " rest)
  selectedNames <- parseMetaList selectedText
  constraintPairs <- parseConstraintList constraintsText
  assignmentPairs <- parseAssignmentList assignmentsText
  let expressionTexts = map ("?" <>) selectedNames
        ++ concat [[lhs, rhs] | (lhs, rhs) <- constraintPairs]
        ++ map snd assignmentPairs
  (levels, metaMap) <- parseFixtureLevelsWithMetas expressionTexts
  let selectedCount = length selectedNames
      constraintCount = length constraintPairs
      selectedLevels = take selectedCount levels
      constraintLevels = take (2 * constraintCount) (drop selectedCount levels)
      expectedLevels = drop (selectedCount + 2 * constraintCount) levels
      targets = Set.fromList [meta | LMeta meta <- selectedLevels]
      constraints =
        [ LevelConstraint index lhs rhs (ConstraintOrigin "Appendix T level assertion" "assertLevelSolve") emptyAssumptions
        | (index, [lhs, rhs]) <- zip [0 ..] (chunksOfTwo constraintLevels)
        ]
      expected =
        [ (meta, level)
        | ((name, _), level) <- zip assignmentPairs expectedLevels
        , Just meta <- [Map.lookup name metaMap]
        ]
  if length targets /= length selectedNames || length expected /= length assignmentPairs
    then Left "a selected or assigned metavariable is malformed"
    else pure (targets, constraints, expected)

parseFixtureSolveClass :: Text -> Either Text (Set.Set Int, [LevelConstraint], Text)
parseFixtureSolveClass directive = do
  (selectedText, rest) <- maybe (Left "missing 'where'") Right (splitDirectiveInfix " where " directive)
  (constraintsText, expectedClass) <- maybe (Left "missing inference outcome") Right (splitLastWord rest)
  selectedNames <- parseMetaList selectedText
  constraintPairs <- parseConstraintList constraintsText
  let expressionTexts = map ("?" <>) selectedNames ++ concat [[lhs, rhs] | (lhs, rhs) <- constraintPairs]
  (levels, _) <- parseFixtureLevelsWithMetas expressionTexts
  let selectedCount = length selectedNames
      targets = Set.fromList [meta | LMeta meta <- take selectedCount levels]
      constraints =
        [ LevelConstraint index lhs rhs (ConstraintOrigin "Appendix T level assertion" "assertLevelSolveClass") emptyAssumptions
        | (index, [lhs, rhs]) <- zip [0 ..] (chunksOfTwo (drop selectedCount levels))
        ]
  if length targets /= length selectedNames
    then Left "a selected metavariable is malformed"
    else pure (targets, constraints, expectedClass)

parseMetaList :: Text -> Either Text [Text]
parseMetaList input = do
  body <- stripFixtureBrackets input
  traverse parseMeta (splitTopLevelCommas body)
  where
    parseMeta item =
      case T.stripPrefix "?" (T.strip item) of
        Just name | not (T.null name) -> Right name
        _ -> Left ("expected metavariable in '" <> item <> "'")

parseConstraintList :: Text -> Either Text [(Text, Text)]
parseConstraintList input = do
  body <- stripFixtureBrackets input
  traverse parseConstraint (splitTopLevelCommas body)
  where
    parseConstraint item =
      maybe (Left ("expected '<=' in constraint '" <> item <> "'")) Right
        (splitDirectiveInfix " <= " item)

parseAssignmentList :: Text -> Either Text [(Text, Text)]
parseAssignmentList input = do
  body <- stripFixtureBrackets input
  traverse parseAssignment (splitTopLevelCommas body)
  where
    parseAssignment item = do
      (metaText, value) <- maybe (Left ("expected '=' in assignment '" <> item <> "'")) Right
        (splitDirectiveInfix " = " item)
      name <- case T.stripPrefix "?" metaText of
        Just value' | not (T.null value') -> Right value'
        _ -> Left ("expected metavariable in assignment '" <> item <> "'")
      pure (name, value)

stripFixtureBrackets :: Text -> Either Text Text
stripFixtureBrackets input =
  case T.stripPrefix "[" (T.strip input) >>= T.stripSuffix "]" of
    Just body -> Right body
    Nothing -> Left ("expected bracketed list, found '" <> input <> "'")

splitTopLevelCommas :: Text -> [Text]
splitTopLevelCommas input
  | T.null (T.strip input) = []
  | otherwise = map (T.strip . T.pack . reverse) . reverse $ finish depth current pieces
  where
    (depth, current, pieces) = foldl step (0 :: Int, [], []) (T.unpack input)
    step (nesting, chars, chunks) character = case character of
      '(' -> (nesting + 1, character : chars, chunks)
      ')' -> (nesting - 1, character : chars, chunks)
      ',' | nesting == 0 -> (nesting, [], chars : chunks)
      _ -> (nesting, character : chars, chunks)
    finish _ chars chunks = chars : chunks

chunksOfTwo :: [a] -> [[a]]
chunksOfTwo [] = []
chunksOfTwo (left : right : rest) = [left, right] : chunksOfTwo rest
chunksOfTwo [_] = []

fixtureOutcomeName :: PrincipalInferenceOutcome -> Text
fixtureOutcomeName = \case
  SolvedPrincipal _ -> "SolvedPrincipal"
  Unsatisfiable -> "Unsatisfiable"
  NoPointwiseLeastSolution _ -> "NoPointwiseLeastSolution"
  OutsidePortableInferenceFragment -> "OutsidePortableInferenceFragment"
  BlockedByUnselectedMetas -> "BlockedByUnselectedMetas"

requireFixture :: Bool -> Text -> AssertResult
requireFixture condition detail = if condition then AssertOk else AssertFail detail

parseUniverseVariance :: Text -> Maybe UniverseVariance
parseUniverseVariance = \case
  "invariant" -> Just Invariant
  "covariant" -> Just Covariant
  "irrelevant" -> Just Irrelevant
  _ -> Nothing

parseUniverseVarianceList :: Text -> Maybe [UniverseVariance]
parseUniverseVarianceList source = do
  body <- T.stripPrefix "[" (T.strip source) >>= T.stripSuffix "]"
  if T.null (T.strip body)
    then pure []
    else mapM (parseUniverseVariance . T.strip) (T.splitOn "," body)

-- | Non-interpolated Kappa string literal (§T.3): @"..."@ with §6.3.1
-- escapes.
parseStringLiteral :: Text -> Maybe Text
parseStringLiteral t0 = do
  t1 <- T.stripPrefix "\"" (T.strip t0)
  go t1 []
  where
    go t acc = case T.uncons t of
      Nothing -> Nothing -- unterminated
      Just ('"', restT)
        | T.null (T.strip restT) -> Just (T.pack (reverse acc))
        | otherwise -> Nothing -- trailing junk after the closing quote
      Just ('\\', restT) -> do
        (c, restT') <- unescape restT
        go restT' (c : acc)
      Just (c, restT) -> go restT (c : acc)
    unescape t = case T.uncons t of
      Just ('n', r) -> Just ('\n', r)
      Just ('t', r) -> Just ('\t', r)
      Just ('r', r) -> Just ('\r', r)
      Just ('0', r) -> Just ('\0', r)
      Just ('b', r) -> Just ('\b', r)
      Just ('f', r) -> Just ('\f', r)
      Just ('\\', r) -> Just ('\\', r)
      Just ('"', r) -> Just ('"', r)
      Just ('\'', r) -> Just ('\'', r)
      Just ('$', r) -> Just ('$', r)
      Just ('u', r) | Just ('{', r1) <- T.uncons r -> do
        let (hs, r2) = T.span isHexDigit r1
        r3 <- T.stripPrefix "}" r2
        if T.null hs || T.length hs > 6
          then Nothing
          else Just (toEnum (hexVal hs), r3)
      _ -> Nothing
    isHexDigit c = isDigit c || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')
    hexVal = T.foldl' (\a c -> a * 16 + digit c) 0
    digit c
      | isDigit c = fromEnum c - fromEnum '0'
      | c >= 'a' && c <= 'f' = fromEnum c - fromEnum 'a' + 10
      | otherwise = fromEnum c - fromEnum 'A' + 10

-- | A whitespace-separated sequence of §T.3 string literals (the
-- @runArgs <stringLiteral>...@ argument list). Each literal uses the
-- same non-interpolated grammar as 'parseStringLiteral'. Returns Nothing
-- if any literal is malformed or non-literal junk appears between them.
parseStringLiterals :: Text -> Maybe [Text]
parseStringLiterals = go . T.stripStart
  where
    go t
      | T.null t = Just []
      | otherwise = do
          (lit, rest) <- oneLiteral t
          (lit :) <$> go (T.stripStart rest)
    oneLiteral t0 = do
      t1 <- T.stripPrefix "\"" t0
      scan t1 []
    scan t acc = case T.uncons t of
      Nothing -> Nothing -- unterminated
      Just ('"', restT) -> Just (T.pack (reverse acc), restT)
      Just ('\\', restT) -> do
        (c, restT') <- unesc restT
        scan restT' (c : acc)
      Just (c, restT) -> scan restT (c : acc)
    unesc t = case T.uncons t of
      Just ('n', r) -> Just ('\n', r)
      Just ('t', r) -> Just ('\t', r)
      Just ('r', r) -> Just ('\r', r)
      Just ('0', r) -> Just ('\0', r)
      Just ('b', r) -> Just ('\b', r)
      Just ('f', r) -> Just ('\f', r)
      Just ('\\', r) -> Just ('\\', r)
      Just ('"', r) -> Just ('"', r)
      Just ('\'', r) -> Just ('\'', r)
      Just ('$', r) -> Just ('$', r)
      Just ('u', r) | Just ('{', r1) <- T.uncons r -> do
        let (hs, r2) = T.span isHex r1
        r3 <- T.stripPrefix "}" r2
        if T.null hs || T.length hs > 6 then Nothing else Just (toEnum (hexV hs), r3)
      _ -> Nothing
    isHex c = isDigit c || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')
    hexV = T.foldl' (\a c -> a * 16 + d c) 0
    d c
      | isDigit c = fromEnum c - fromEnum '0'
      | c >= 'a' && c <= 'f' = fromEnum c - fromEnum 'a' + 10
      | otherwise = fromEnum c - fromEnum 'A' + 10

-- ── Test execution ───────────────────────────────────────────────────

readSourceFile :: FilePath -> IO Text
readSourceFile path = do
  bytes <- BS.readFile path
  pure (TE.decodeUtf8With TEE.lenientDecode bytes)

-- | Run one @.kp@ test file (§T.2 single-file inline test). The suite
-- root for relative paths is the containing directory (§T.2).
runTestFile :: FilePath -> IO TestReport
runTestFile path = guardExceptions path $ do
  (src, preDiags) <- loadSourceFile path
  runSuiteWith False path (takeDirectory path) [(path, src)] Nothing preDiags

-- | Run a §T.2 directory suite: all @.kp@ files under the root compiled
-- together, directives gathered from @suite.ktest@ plus every file.
runSuiteDir :: FilePath -> IO TestReport
runSuiteDir dir = guardExceptions dir $ do
  files <- collectKp dir
  loaded <- mapM loadSourceFile files
  let srcs = map fst loaded
      preDiags = concatMap snd loaded
      ktestPath = dir </> "suite.ktest"
  hasKtest <- doesFileExist ktestPath
  mktest <-
    if hasKtest
      then Just . (,) ktestPath <$> readSourceFile ktestPath
      else pure Nothing
  runSuite dir dir (zip files srcs) mktest preDiags

guardExceptions :: FilePath -> IO TestReport -> IO TestReport
guardExceptions label act = do
  r <- try act
  case r of
    Right rep -> pure rep
    Left (e :: SomeException) ->
      pure (TestReport label HarnessError ("internal exception: " <> firstLine (T.pack (show e))))
  where
    firstLine = T.takeWhile (/= '\n')

-- | Shared suite driver. @files@ are the compilation roots; directives
-- come from the optional @suite.ktest@ and from each file (§T.6).
runSuite :: FilePath -> FilePath -> [(FilePath, Text)] -> Maybe (FilePath, Text) -> Diagnostics -> IO TestReport
runSuite = runSuiteWith True

-- single-file tests are script-mode (§8.1 package path rules off)
runSuiteWith :: Bool -> FilePath -> FilePath -> [(FilePath, Text)] -> Maybe (FilePath, Text) -> Diagnostics -> IO TestReport
runSuiteWith packageMode label root files mktest preDiags = do
  let sources = maybe [] (: []) mktest ++ files
      scans = [(p, src, scanDirectives src) | (p, src) <- sources]
      scanErrs = concat [es | (_, _, (_, es)) <- scans]
      scanned = [(p, src, s) | (p, src, (ss, _)) <- scans, s <- ss]
  if null files
    then pure (TestReport label HarnessError "suite contains no .kp files")
    else
      if not (null scanErrs)
        then pure (TestReport label HarnessError (T.intercalate "; " scanErrs))
        else do
          let modes = [m | (_, _, SMode m) <- scanned]
              entries = [e | (_, _, SEntry e) <- scanned]
              unsups = [u | (_, _, SUnsupported u) <- scanned]
              backends = [b | (_, _, SBackend b) <- scanned]
              asserts =
                [(p, src, a) | (p, src, SAssert a) <- scanned]
                  ++ [ (p, src, AStageDumpEquals checkpoint expectedPath (stageDumpFormat selectedDumpFormat expectedPath))
                     | (p, src, SStageDump checkpoint expectedPath) <- scanned
                     ]
              scripted = not (null [() | (_, _, SScriptMode) <- scanned])
              stdinFiles = [p | (_, _, SStdinFile p) <- scanned]
              sourceDirectives = [paths | (_, _, SSources paths) <- scanned]
              -- §T.6: the same configuration key specified more than once
              -- with different values makes the suite ill-formed.
              configPairs = [(k, v) | (_, _, SConfigKey k v) <- scanned]
              selectedDumpFormat = fromMaybe "json" (lookup "dumpFormat" configPairs)
              configConflict =
                listToMaybe
                  [ k
                  | k <- dedup (map fst configPairs)
                  , length (dedup [v | (k', v) <- configPairs, k' == k]) > 1
                  ]
              runArgsConfigured = any ((== "runArgs") . fst) configPairs
              -- §4.2: package mode defaults all unsafe/debug settings to
              -- false; script mode MAY default them to true (this
              -- implementation does). Explicit allow_* directives then
              -- layer on top of that base.
              unsafeBase = if scripted then scriptUnsafeConfig else defaultUnsafeConfig
              unsafeCfg = foldl' (\c f -> f c) unsafeBase [f | (_, _, SUnsafeConfig f) <- scanned]
              mode = case modes of m : _ -> m; [] -> "check"
              relativeSources = map (T.pack . makeRelative root . fst) files
              selectedFiles = case sourceDirectives of
                [paths] -> mapMaybe (\path -> find ((== path) . T.pack . makeRelative root . fst) files) paths
                _ -> files
              sourceProblem = case sourceDirectives of
                [] -> Nothing
                [paths]
                  | length paths /= length (dedup paths) -> Just "'sources' lists the same source more than once"
                  | sort paths /= sort relativeSources ->
                      Just ("'sources' must list every .kp suite source exactly once; found " <> T.unwords paths <> ", expected " <> T.unwords relativeSources)
                  | otherwise -> Nothing
                _ -> Just "'sources' may be specified only once per suite"
          -- §T.4: a stdinFile path must name a readable suite-relative
          -- file (§T.8: an unreadable required file is a harness error).
          missingStdin <-
            if mode == "run"
              then filterM (fmap not . doesFileExist . (root </>) . T.unpack) stdinFiles
              else pure []
          case () of
            _ | Just k <- configConflict ->
                  pure (TestReport label HarnessError ("configuration key '" <> k <> "' is specified more than once with conflicting values; the suite is ill-formed (§T.6)"))
              | length (dedup modes) > 1 ->
                  pure (TestReport label HarnessError "conflicting 'mode' directives (§T.6)")
              | runArgsConfigured && mode /= "run" ->
                  pure (TestReport label HarnessError "'runArgs' is valid only for mode run (§T.4)")
              | not (null stdinFiles) && mode /= "run" ->
                  pure (TestReport label HarnessError "'stdinFile' is valid only for mode run (§T.4)")
              | (p : _) <- missingStdin ->
                  pure (TestReport label HarnessError ("stdinFile '" <> p <> "' is not a readable suite file (§T.4, §T.8)"))
              | Just detail <- sourceProblem ->
                  pure (TestReport label HarnessError detail)
              | (u : _) <- unsups ->
                  pure (TestReport label Unsupported u)
              | otherwise -> do
                  -- §T.4: 'backend <profile>' selects the backend for
                  -- 'compile' and 'run' tests; a foreign profile makes
                  -- those tests unsupported, while a default-mode
                  -- 'check' test is unaffected by backend selection
                  case backends of
                    (b : _) | mode `elem` ["compile", "run"] ->
                      pure (TestReport label Unsupported ("backend " <> b <> " is not provided"))
                    _ ->
                      if not (null entries) && mode /= "run"
                        then pure (TestReport label HarnessError "'entry' is valid only for mode run (§T.4)")
                        else executeSuite unsafeCfg (packageMode && not scripted) label root selectedFiles mode entries asserts preDiags
  where
    dedup = foldr (\x xs -> if x `elem` xs then xs else x : xs) []
    stageDumpFormat configured path
      | ".json" `T.isSuffixOf` path = "json"
      | ".sexpr" `T.isSuffixOf` path = "sexpr"
      | ".kcore" `T.isSuffixOf` path = "kcore"
      | otherwise = configured

data RunInfo = RunInfo
  { riStdout :: !Text
  , riStderr :: !Text
  , riExitCode :: !Int
  }

isPreludeInternalDiagnostic :: Diagnostic -> Bool
isPreludeInternalDiagnostic d =
  let f = spanFile (dPrimary d)
   in f == "<std.prelude>" || "<std." `isPrefixOf` f

executeSuite ::
  UnsafeConfig -> Bool -> FilePath -> FilePath -> [(FilePath, Text)] -> Text -> [Text] ->
  [(FilePath, Text, Assertion)] -> Diagnostics -> IO TestReport
executeSuite unsafeCfg packageMode label root files mode entries asserts preDiags = do
  -- the suite root is the §8.1 source root for module-path derivation;
  -- 'compileWith' captures this suite's exact build configuration so the
  -- @assertDiagnosticFixCompiles@ recheck recompiles identically.
  let compileWith srcs =
        if unsafeCfg /= defaultUnsafeConfig
          then compileFilesWithConfig unsafeCfg packageMode root srcs
          else if packageMode
            then compileFilesIn root srcs
            else compileFiles srcs
      cu0 = compileWith files
      -- mode compile: the per-module Term->Value lowering into the
      -- interpreter's runtime representation is this implementation's
      -- backend-IR stage; it is recorded once per module (§T.5.5)
      cu =
        if mode == "compile"
          then cu0 {cuTrace = cuTrace cu0 ++ [("lowerKBackendIR", "module") | ("lowerKCore", "module") <- cuTrace cu0]}
          else cu0
      allDiags = preDiags ++ cuDiags cu
      preludeErrs = [d | d <- allDiags, isError d, isPreludeInternalDiagnostic d]
      diags = [d | d <- allDiags, not (isPreludeInternalDiagnostic d)]
  if not (null preludeErrs)
    then
      pure
        ( TestReport label HarnessError
            ( "prelude failed to compile (implementation bug): "
                <> T.intercalate "; " (map renderDiagnostic (take 3 preludeErrs))
            )
        )
    else do
      mRun <-
        if mode == "run"
          then Just <$> doRun cu diags
          else pure Nothing
      let backendIr =
            if mode == "compile" || mode == "run"
              then
                Just
                  ( lowerKBackendIRForCapabilities
                      (Set.fromList supportedCapabilities)
                      (cuState cu)
                  )
              else Nothing
      results <-
        mapM
          (\(p, s, a) ->
            checkAssertion
              compileWith root p s files cu diags mRun backendIr a)
          asserts
      let fails = [d | AssertFail d <- results]
          herrs = [d | AssertHarnessError d <- results]
      pure $
        if not (null herrs)
          then TestReport label HarnessError (T.intercalate "; " herrs)
          else
            if null fails
              then TestReport label Pass ""
              else TestReport label Fail (T.intercalate "; " fails)
  where
    doRun cu diags
      | hasErrors diags =
          pure (RunInfo "" (T.unlines (map renderDiagnostic diags)) 1)
      | otherwise = do
          let st = cuState cu
              entryName = case entries of
                (e : _) -> snd (splitQualified e)
                [] -> "main"
          case entryGlobal cu entryName of
            Nothing -> pure (RunInfo "" ("error: entrypoint '" <> entryName <> "' is not defined") 1)
            Just mainG -> do
              mres <-
                timeout runTimeoutMicros $
                  runMainCapturedValue (Globals (csGlobals st)) (csMetas st) mainG
              case mres of
                Nothing -> pure (RunInfo "" "error: test timed out" 1)
                Just (RunOk, mv, out) ->
                  -- a non-Unit entry result is rendered to stdout, like
                  -- the reference run task (e.g. @let main = 42@)
                  let ec = EvalCtx (Globals (csGlobals st)) (csMetas st) True mempty
                      extra = case mv of
                        Just v
                          | not (isUnitValue ec v) ->
                              renderEvalValue ec v <> "\n"
                        _ -> ""
                   in pure (RunInfo (out <> extra) "" 0)
                Just (RunFail msg, _, out) ->
                  pure (RunInfo out ("runtime failure: " <> msg) 1)

-- | Resolve the run entrypoint: the compiled unit's own module first,
-- then any non-prelude module in the accumulated state.
entryGlobal :: CompiledUnit -> Text -> Maybe GName
entryGlobal cu entryName =
  let st = cuState cu
      own = GName (cuModule cu) entryName
      others =
        [ g
        | g@(GName m n) <- Map.keys (csGlobals st)
        , n == entryName
        , m /= ModuleName ["std", "prelude"]
        ]
   in if Map.member own (csGlobals st)
        then Just own
        else case others of
          (g : _) -> Just g
          [] -> Nothing

-- | Resolve an assertEval subject: the module of the directive's own
-- file wins (§T.6 directives assert about their file), then the
-- 'entryGlobal' search.
evalGlobal :: CompiledUnit -> Maybe ModuleName -> Text -> Maybe GName
evalGlobal cu mmod nm =
  case mmod of
    Just mn
      | Map.member (GName mn nm) (csGlobals (cuState cu)) -> Just (GName mn nm)
    _ -> entryGlobal cu nm

-- | The module a suite file defines: its header when present, else the
-- §8.1 path-derived name relative to the suite root.
moduleForFile :: FilePath -> FilePath -> Text -> Maybe ModuleName
moduleForFile root path src
  | ".kp" `isSuffixOf` path = Just (fromMaybe (moduleNameRelTo root path) headerName)
  | otherwise = Nothing -- suite.ktest: no module of its own
  where
    headerName = listToMaybe
      [ ModuleName (T.splitOn "." m)
      | l <- take 20 (T.lines src)
      , not ("--" `T.isPrefixOf` T.stripStart l)
      , (pre, _kw : rest) <- [break (== "module") (T.words l)]
      , all ("@" `T.isPrefixOf`) pre
      , (m : _) <- [rest]
      ]

runTimeoutMicros :: Int
runTimeoutMicros = 30 * 1000 * 1000

-- ── Assertion evaluation ─────────────────────────────────────────────

data AssertResult = AssertOk | AssertFail !Text | AssertHarnessError !Text

-- force an 'AssertResult' (and its message) to normal form
forceResult :: AssertResult -> AssertResult
forceResult r = case r of
  AssertOk -> r
  AssertFail t -> T.length t `seq` r
  AssertHarnessError t -> T.length t `seq` r

assertKCoreRoundTripText :: (Text -> Either KCoreTextError KCoreFile) -> Text -> Text -> AssertResult
assertKCoreRoundTripText parseVerified subject source =
  case parseVerified source of
    Left err -> AssertFail (subject <> " does not verify: " <> kcteCode err <> ": " <> kcteMessage err)
    Right first ->
      let canonical = printCanonicalKCoreText first
       in case parseVerified canonical of
            Left err -> AssertFail (subject <> " canonical reparse failed: " <> kcteCode err <> ": " <> kcteMessage err)
            Right second
              | printCanonicalKCoreText second /= canonical ->
                  AssertFail (subject <> " is not byte-stable under canonical reprint")
              | semanticHashKCoreText second /= semanticHashKCoreText first ->
                  AssertFail (subject <> " changed semantic hash across round trip")
              | otherwise -> AssertOk

checkAssertion ::
  ([(FilePath, Text)] -> CompiledUnit) ->
  FilePath -> FilePath -> Text -> [(FilePath, Text)] -> CompiledUnit ->
  Diagnostics -> Maybe RunInfo -> Maybe KBackendIR -> Assertion -> IO AssertResult
checkAssertion compileWith root path src files cu diags mRun mBackendIr = \case
  ANoErrors ->
    countErrorsIs 0
  ANoWarnings ->
    countIs "warnings" 0 (length warnings)
  AErrorCount n ->
    countErrorsIs n
  AWarningCount n ->
    countIs "warnings" n (length warnings)
  ADiag sev code ->
    require
      (any (\d -> dSeverity d == toSeverity sev && matchCF code d) diags)
      ("no diagnostic " <> describe sev code <> " was produced" <> sawCodes)
  ADiagNext sev code line ->
    require
      ( any
          ( \d ->
              dSeverity d == toSeverity sev
                && matchCF code d
                && spanFile (dPrimary d) == path
                && posLine (spanStart (dPrimary d)) == line
          )
          diags
      )
      ("no diagnostic " <> describe sev code <> " on line " <> tshow line <> sawCodes)
  ADiagAt p sev code line mcol ->
    require
      ( any
          ( \d ->
              dSeverity d == toSeverity sev
                && matchCF code d
                && T.pack (spanFile (dPrimary d)) `endsWithPath` p
                && posLine (spanStart (dPrimary d)) == line
                && maybe True (== posCol (spanStart (dPrimary d))) mcol
          )
          diags
      )
      ("no diagnostic " <> describe sev code <> " at " <> p <> ":" <> tshow line)
  ADiagAtRange p sev code sl sc el ec ->
    require
      ( any
          ( \d ->
              dSeverity d == toSeverity sev
                && matchCF code d
                && T.pack (spanFile (dPrimary d)) `endsWithPath` p
                && spanStart (dPrimary d) == Pos sl sc
                && spanEnd (dPrimary d) == Pos el ec
          )
          diags
      )
      ( "no diagnostic " <> describe sev code <> " at " <> p <> ":"
          <> tshow sl <> ":" <> tshow sc <> "-" <> tshow el <> ":" <> tshow ec
      )
  ADiagMatch pat re ->
    require
      (any (regexSearch re . dMessage) diags)
      ("no diagnostic message matches /" <> pat <> "/" <> sawMessages)
  ADiagFamily sev fam ->
    require
      (any (\d -> dSeverity d == toSeverity sev && dFamily d == Just fam) diags)
      ("no diagnostic with family " <> fam <> " was produced")
  ADiagPayload sev cf ptr expected ->
    let cand = [d | d <- diags, dSeverity d == toSeverity sev, matchCF cf d]
     in require
          (any (\d -> payloadPointer ptr d == Just (jsonScalarText expected)) cand)
          ( "no " <> sevText sev <> " diagnostic matching " <> cf
              <> " has payload " <> ptr <> " = " <> expected
              <> " (saw: " <> T.intercalate "; " [ptr <> "=" <> maybe "<absent>" id (payloadPointer ptr d) | d <- cand] <> ")"
          )
  ADiagLabel sev cf role ->
    require
      (any (\d -> dSeverity d == toSeverity sev && matchCF cf d && labelHasRole role d) diags)
      ("no " <> sevText sev <> " diagnostic matching " <> cf <> " has a label with role " <> role)
  ADiagRelated sev cf role ->
    require
      (any (\d -> dSeverity d == toSeverity sev && matchCF cf d
              && any ((== role) . relatedRoleText . roRole) (dRelated d)) diags)
      ( "no " <> sevText sev <> " diagnostic matching " <> cf
          <> " has a related origin with role " <> role
          <> " (saw roles: " <> T.intercalate ", "
               [relatedRoleText (roRole r) | d <- diags, dSeverity d == toSeverity sev, matchCF cf d, r <- dRelated d]
          <> ")"
      )
  ADiagFix sev cf appl ->
    require
      (any (\d -> dSeverity d == toSeverity sev && matchCF cf d
              && any ((== appl) . fixApplicabilityText . dfApplicability) (dFixes d)) diags)
      ("no " <> sevText sev <> " diagnostic matching " <> cf <> " has a fix with applicability " <> appl)
  ADiagFixCount sev cf n ->
    let cand = [d | d <- diags, dSeverity d == toSeverity sev, matchCF cf d]
     in require
          (any ((== n) . length . dFixes) cand)
          ("no " <> sevText sev <> " diagnostic matching " <> cf <> " has exactly " <> tshow n <> " fixes")
  AFixCompiles sev cf ->
    -- §T.5.1: take the first machine-applicable fix of the first matching
    -- diagnostic (in the deterministic fix ordering), apply its edits to
    -- the suite source, recompile under the same configuration, and
    -- succeed iff the recompilation produces no error diagnostics.
    case [ (d, f)
         | d <- diags, dSeverity d == toSeverity sev, matchCF cf d
         , f <- take 1 [fx | fx <- dFixes d, dfApplicability fx == FixMachineApplicable]
         ] of
      [] ->
        pure (AssertFail ("no " <> sevText sev <> " diagnostic matching " <> cf
                            <> " has a machine-applicable fix to apply"))
      ((_, fix) : _) ->
        case applyFixToFiles files (dfEdits fix) of
          Left err -> pure (AssertHarnessError ("assertDiagnosticFixCompiles: " <> err))
          Right files' ->
            let cu' = compileWith files'
                ds' = [d | d <- cuDiags cu', not (isPreludeInternalDiagnostic d)]
             in require
                  (not (hasErrors ds'))
                  ( "applying fix " <> tshow (dfTitle fix) <> " still leaves errors: "
                      <> T.intercalate ", " [dCode d | d <- ds', isError d]
                  )
  ASuppressed primary supp ->
    require
      (any (\d -> matchCFAny primary d && any (suppMatches supp) (dSuppressed d)) diags)
      ("no diagnostic matching " <> primary <> " suppresses a diagnostic matching " <> supp)
  AExplainExists cf ->
    require
      (explainExists cf)
      ("no registered explanation for diagnostic code or family '" <> cf <> "' (§3.1.2A)")
  AErrorCodes codes ->
    require
      (codesMatchUpTo codes errors)
      ( "error codes are [" <> T.intercalate ", " (map dCode errors)
          <> "], expected [" <> T.intercalate ", " codes <> "]"
      )
  AEval nm expected -> do
    -- evaluation may legitimately be deep; guard with the run timeout
    let mmod = moduleForFile root path src
    mr <- timeout runTimeoutMicros (evaluate (forceResult (assertEval cu mmod nm expected)))
    pure (fromMaybe (AssertFail ("assertEval: evaluation of '" <> nm <> "' timed out")) mr)
  AEvalError nm sub -> do
    let mmod = moduleForFile root path src
    mr <- timeout runTimeoutMicros (evaluate (forceResult (assertEvalError cu mmod nm sub)))
    pure (fromMaybe (AssertFail ("assertEvalErrorContains: evaluation of '" <> nm <> "' timed out")) mr)
  ADeclDescriptors entries -> pure (assertDeclDescriptors path src entries)
  ATokenKinds kinds -> pure (assertTokenKinds path src kinds)
  AModuleName mn -> pure (assertModuleName path src mn)
  AModuleAttrs attrs -> pure (assertModuleAttrs path src attrs)
  ADataCtors tn ctors -> pure (assertDataCtors path src tn ctors)
  AParamQuantities nm qs -> pure (assertParamQuantities path src nm qs)
  ATraitMembers tn ms -> pure (assertTraitMembers path src tn ms)
  AExecute nm expected -> execEntry "assertExecute" nm $ \st mv _out ->
    case mv of
      Just v ->
        let ec = EvalCtx (Globals (csGlobals st)) (csMetas st) True mempty
            rendered = renderEvalValue ec v
         in require
              (rendered == T.strip expected)
              ( "assertExecute: '" <> nm <> "' executed to " <> rendered
                  <> ", expected " <> T.strip expected
              )
      Nothing -> pure (AssertFail ("assertExecute: '" <> nm <> "' produced no value"))
  ARunStdout nm expected -> execEntry "assertRunStdout" nm $ \_st _mv out ->
    require
      (T.strip (normalizeLF out) == T.strip (normalizeLF expected))
      ( "assertRunStdout: '" <> nm <> "' wrote " <> tshow (normalizeLF out)
          <> ", expected " <> tshow (T.strip (normalizeLF expected))
      )
  AInoutParams nm ps -> pure (assertInoutParams path src nm ps)
  ADoItemDescriptors nm descs -> pure (assertDoItemDescriptors path src nm descs)
  ATokenTexts toks -> pure (assertTokenTexts path src toks)
  AType nm tyExpr -> pure (assertType path src cu nm tyExpr)
  AAuditLedger expected ->
    -- §4.7: structured audit query — the ledger MUST be machine-readable
    -- structured data, not parsed diagnostic prose. We read it directly
    -- off the compiled unit's state.
    let actual = map arFacility (csAuditLedger (cuState cu))
     in require
          (actual == expected)
          ( "audit ledger facilities are [" <> T.intercalate ", " actual
              <> "], expected [" <> T.intercalate ", " expected <> "] (§4.7)"
          )
  ADeclKinds kinds -> pure (assertDeclKinds "assertDeclKinds" path src kinds)
  AFileDeclKinds p kinds ->
    case [(fp, fsrc) | (fp, fsrc) <- files, T.pack fp `endsWithPath` p] of
      ((fp, fsrc) : _) -> pure (assertDeclKinds "assertFileDeclKinds" fp fsrc kinds)
      [] -> do
        -- fall back to the suite root on disk (§T.5.2 path resolution)
        let fp = root </> T.unpack p
        exists <- doesFileExist fp
        if exists
          then do
            fsrc <- readSourceFile fp
            pure (assertDeclKinds "assertFileDeclKinds" fp fsrc kinds)
          else
            pure (AssertHarnessError ("assertFileDeclKinds: no suite file '" <> p <> "'"))
  AStdout expected -> withRun $ \ri ->
    let actual = normalizeLF (riStdout ri)
        want = normalizeLF expected
     in require
          (actual == want)
          ("stdout mismatch: expected " <> tshow want <> ", got " <> tshow actual)
  AStdoutContains expected -> withRun $ \ri ->
    require
      (normalizeLF expected `T.isInfixOf` normalizeLF (riStdout ri))
      ("stdout does not contain " <> tshow (normalizeLF expected))
  AStderrContains expected -> withRun $ \ri ->
    require
      (normalizeLF expected `T.isInfixOf` normalizeLF (riStderr ri))
      ("stderr does not contain " <> tshow (normalizeLF expected))
  AStdoutFile p -> goldenCompare p "stdout" riStdout
  AStderrFile p -> goldenCompare p "stderr" riStderr
  AExitCode n -> withRun $ \ri ->
    require
      (riExitCode ri == n)
      ("exit code was " <> tshow (riExitCode ri) <> ", expected " <> tshow n)
  ATraceCount ev subj rel n ->
    let actual = length [() | (e, s) <- cuTrace cu, e == ev, s == subj]
        holds = case rel of
          "=" -> actual == n
          "!=" -> actual /= n
          "<" -> actual < n
          "<=" -> actual <= n
          ">" -> actual > n
          ">=" -> actual >= n
          _ -> False -- unreachable: validated at scan time
     in require
          holds
          ( "trace count " <> ev <> "/" <> subj <> " is " <> tshow actual
              <> ", expected " <> rel <> " " <> tshow n
          )
  AStageDumpEquals checkpoint relative format
    | checkpoint /= "KCore" ->
        pure (AssertHarnessError ("assertStageDump names unknown or unmaterialized checkpoint '" <> checkpoint <> "'"))
    | format /= "kcore" ->
        pure (AssertHarnessError ("assertStageDump KCore requires KCoreText in this harness; select dumpFormat kcore or use a .kcore golden"))
    | not (null errors) ->
        pure (AssertFail "assertStageDump KCore: the suite has compile errors")
    | otherwise -> withKCoreFile relative $ \expected -> do
        let st = cuState cu
            ec = EvalCtx (Globals (csGlobals st)) (csMetas st) False mempty
        pure $ case renderKCoreModule (cuModule cu) ec (csGlobals st) (csCoreBodies st) checkpointDataInterfaces checkpointConstructorInterfaces checkpointRepresentationCertificates of
          Left err -> AssertFail ("generated KCore stage dump could not be emitted: " <> kcteCode err <> ": " <> kcteMessage err)
          Right actual -> case (parseKCore actual, parseKCore expected) of
            (Left err, _) -> AssertFail ("generated KCore stage dump does not verify: " <> kcteCode err <> ": " <> kcteMessage err)
            (_, Left err) -> AssertFail ("KCore golden does not verify: " <> kcteCode err <> ": " <> kcteMessage err)
            (Right actualCore, Right expectedCore)
              | printCanonicalKCoreText actualCore == printCanonicalKCoreText expectedCore -> AssertOk
              | otherwise -> AssertFail ("canonical KCore stage dump does not match golden file " <> relative)
  AStageDumpRoundTrips checkpoint
    | checkpoint /= "KCore" ->
        pure (AssertHarnessError ("assertStageDumpRoundTrips names unknown checkpoint '" <> checkpoint <> "'"))
    | not (null errors) ->
        pure (AssertFail "assertStageDumpRoundTrips KCore: the suite has compile errors")
    | otherwise ->
        let st = cuState cu
            ec = EvalCtx (Globals (csGlobals st)) (csMetas st) False mempty
         in pure $ case renderKCoreModule (cuModule cu) ec (csGlobals st) (csCoreBodies st) checkpointDataInterfaces checkpointConstructorInterfaces checkpointRepresentationCertificates of
              Left err -> AssertFail ("generated KCore stage dump could not be emitted: " <> kcteCode err <> ": " <> kcteMessage err)
              Right dump -> assertKCoreRoundTripText parseKCore "generated KCore stage dump" dump
  AKCoreParses relative -> withKCoreFile relative $ \contents ->
    pure $ case parseKCore contents of
      Right _ -> AssertOk
      Left err -> AssertFail ("assertKCoreParses: " <> kcteCode err <> ": " <> kcteMessage err)
  AKCoreRoundTrips relative -> withKCoreFile relative $ \contents ->
    pure (assertKCoreRoundTripText parseKCore ("KCore file " <> relative) contents)
  AKCoreRejects relative expectedCode -> withKCoreFile relative $ \contents ->
    pure $ case parseKCore contents of
      Left err
        | kcteCode err == expectedCode -> AssertOk
        | otherwise ->
            AssertFail
              ( "assertKCoreRejects: rejected with " <> kcteCode err
                  <> ", expected " <> expectedCode <> ": " <> kcteMessage err
              )
      Right _ -> AssertFail ("assertKCoreRejects: " <> relative <> " was accepted")
  AKCoreSchemaCertificateValid relative family -> withKCoreFile relative $ \contents ->
    pure $ case parseKCore contents of
      Left err ->
        AssertFail
          ( "assertKCoreSchemaCertificateValid: " <> relative <> " does not verify: "
              <> kcteCode err <> ": " <> kcteMessage err
          )
      Right core ->
        if kcoreHasValidSchemaCertificate core family
          then AssertOk
          else AssertFail ("no independently verified schema certificate for " <> family <> " occurs in " <> relative)
  AKCoreSemanticHashEquals left right ->
    withKCoreFile left $ \leftContents ->
      withKCoreFile right $ \rightContents ->
        pure $ case (parseKCore leftContents, parseKCore rightContents) of
          (Left err, _) -> AssertFail (left <> " does not verify: " <> kcteCode err <> ": " <> kcteMessage err)
          (_, Left err) -> AssertFail (right <> " does not verify: " <> kcteCode err <> ": " <> kcteMessage err)
          (Right leftCore, Right rightCore) ->
            requirePure
              (semanticHashKCoreText leftCore == semanticHashKCoreText rightCore)
              ("KCore semantic hashes differ for " <> left <> " and " <> right)
  AKCoreLevelEvidence relative certificate dependencies ->
    withKCoreFile relative $ \contents ->
      pure $ case parseKCore contents of
        Left err -> AssertFail (relative <> " does not verify: " <> kcteCode err <> ": " <> kcteMessage err)
        Right core ->
          requirePure
            (kcoreLevelCertificateDependencies core certificate == Just dependencies)
            ("level certificate " <> certificate <> " does not use canonical dependencies " <> tshow dependencies)
  ALevelNormalForm leftText rightText ->
    pure $ case parseFixtureLevels [leftText, rightText] of
      Left detail -> AssertHarnessError ("assertLevelNormalForm: " <> detail)
      Right [left, right] ->
        requirePure
          (normalizeLevel left == normalizeLevel right)
          ("normal forms differ: " <> renderLevel (normalizeLevel left) <> " vs " <> renderLevel (normalizeLevel right))
      Right _ -> AssertHarnessError "assertLevelNormalForm: internal arity mismatch"
  ALevelEntails expected leftText rightText ->
    pure $ case parseFixtureLevels [leftText, rightText] of
      Left detail -> AssertHarnessError ("level entailment assertion: " <> detail)
      Right [left, right] ->
        let result = proveLevelLeq emptyAssumptions left right
            accepted
              | expected = result == Proved
              | otherwise =
                  result /= Proved
                    && assumptionsConsistent
                         (insertAssumption (levelSucc right) left emptyAssumptions)
         in requirePure
              accepted
              ("level judgment " <> renderLevel left <> " <= " <> renderLevel right
                <> if expected
                     then " is not entailed"
                     else " has no satisfiable strict refutation")
      Right _ -> AssertHarnessError "level entailment assertion: internal arity mismatch"
  ALevelSolve directive ->
    pure $ either AssertHarnessError id (checkFixtureLevelSolve directive)
  ALevelSolveClass directive ->
    pure $ either AssertHarnessError id (checkFixtureLevelSolveClass directive)
  APrincipalUniverse declaration expectedText ->
    pure $ case (universeInferenceRecord (cuState cu) declaration, parseFixtureLevels [expectedText]) of
      (Nothing, _) -> AssertFail ("no declaration-boundary universe inference result is recorded for " <> declaration)
      (_, Left detail) -> AssertHarnessError ("assertPrincipalUniverse: " <> detail)
      (Just record, Right [expected])
        | uirClass record /= InferenceSolvedPrincipal ->
            AssertFail
              ("universe inference for " <> declaration <> " is " <> renderInferenceClass (uirClass record)
                <> ", expected SolvedPrincipal")
        | otherwise ->
            let actual = nub (map normalizeLevel (Map.elems (uirPrincipalAssignments record)))
             in requirePure
                  (actual == [normalizeLevel expected])
                  ("principal universe for " <> declaration <> " is "
                    <> T.intercalate ", " (map renderLevel actual)
                    <> ", expected " <> renderLevel (normalizeLevel expected))
      (_, Right _) -> AssertHarnessError "assertPrincipalUniverse: internal arity mismatch"
  AUniverseInferenceClass declaration expected ->
    pure $ case universeInferenceRecord (cuState cu) declaration of
      Nothing -> AssertFail ("no declaration-boundary universe inference result is recorded for " <> declaration)
      Just record ->
        requirePure
          (renderInferenceClass (uirClass record) == expected)
          ("universe inference for " <> declaration <> " is " <> renderInferenceClass (uirClass record)
            <> ", expected " <> expected)
  ARecursiveSchemaEdge caller callee relation ->
    pure $ requirePure
      (recursiveSchemaEdgeRecorded (cuState cu) caller callee relation)
      ("no checked recursive schema edge " <> caller <> " -> " <> callee <> " (" <> relation <> ") was recorded")
  ASelectedEvidence goal evidence ->
    pure $ requirePure
      (selectedUniverseEvidenceRecorded (cuState cu) goal evidence)
      ("universe role inference did not record selected evidence " <> evidence <> " for " <> goal)
  AUniverseRole family index expectedRole ->
    pure $ case nominalSummaryFor cu family of
      Nothing -> AssertFail ("no nominal cumulativity summary is available for " <> family)
      Just summary ->
        case ncsRoles summary `atMay` index of
          Just actual | actual == expectedRole -> AssertOk
          Just actual -> AssertFail ("universe role " <> tshow index <> " of " <> family <> " is " <> varianceText actual <> ", expected " <> varianceText expectedRole)
          Nothing -> AssertFail ("universe role index " <> tshow index <> " is outside the role vector of " <> family)
  ASchemaCertificateValid family ->
    pure $ case nominalSummaryFor cu family of
      Just summary | verifyNominalCumulativitySummary summary -> AssertOk
      Just _ -> AssertFail ("nominal action certificate for " <> family <> " fails independent replay")
      Nothing -> AssertFail ("no nominal action certificate is available for " <> family)
  ASchemaLiftPresent family ->
    pure $
      requirePure
        (any ((== normalizedFamilyName family) . normalizedFamilyName . gnameText) (schemaLiftFamilies cu))
        ("no verified KCore schemaLift of " <> family <> " is present")
  ASchemaLiftCount expectedCount ->
    let actualCount = length (schemaLiftFamilies cu)
     in pure $ requirePure (actualCount == expectedCount)
          ("verified KCore schemaLift count is " <> tshow actualCount <> ", expected " <> tshow expectedCount)
  ASemanticHashDiffers left right -> do
    leftUnit <- compileSuiteFile left
    rightUnit <- compileSuiteFile right
    pure $ compareCompiledUnits "assertSemanticHashDiffers" leftUnit rightUnit $ \leftCompiled rightCompiled ->
      requirePure
        (nominalInterfaceHash leftCompiled /= nominalInterfaceHash rightCompiled)
        ("semantic hashes are equal for " <> left <> " and " <> right)
  ASemanticHashDiffersFrom target -> do
    targetUnit <- compileSuiteFile target
    pure $ case targetUnit of
      Left detail -> AssertHarnessError detail
      Right targetCompiled
        | hasErrors (cuDiags cu) || hasErrors (cuDiags targetCompiled) ->
            AssertFail "assertSemanticHashDiffersFrom: one of the compared artifacts does not compile"
        | otherwise ->
            requirePure
              (nominalInterfaceHash cu /= nominalInterfaceHash targetCompiled)
              ("semantic hash is equal to " <> target)
  ASemanticHashEquals left right -> do
    leftUnit <- compileSuiteFile left
    rightUnit <- compileSuiteFile right
    pure $ compareCompiledUnits "assertSemanticHashEquals" leftUnit rightUnit $ \leftCompiled rightCompiled ->
      requirePure
        (nominalInterfaceHash leftCompiled == nominalInterfaceHash rightCompiled)
        ("semantic hashes differ for " <> left <> " and " <> right)
  ASemanticHashEqualsFrom target -> do
    targetUnit <- compileSuiteFile target
    pure $ case targetUnit of
      Left detail -> AssertHarnessError detail
      Right targetCompiled
        | hasErrors (cuDiags cu) || hasErrors (cuDiags targetCompiled) ->
            AssertFail "assertSemanticHashEquals: one of the compared artifacts does not compile"
        | otherwise ->
            requirePure
              (nominalInterfaceHash cu == nominalInterfaceHash targetCompiled)
              ("semantic hash differs from " <> target)
  AInterfaceContainsUniverseRoles relative family expectedRoles -> do
    compiled <- compileSuiteFile relative
    pure $ case compiled of
      Left detail -> AssertHarnessError detail
      Right unit
        | hasErrors (cuDiags unit) -> AssertFail ("interface source " <> relative <> " does not compile")
        | otherwise -> case interfaceArtifactRoles unit family of
            Left detail -> AssertFail ("interface artifact for " <> relative <> " is invalid: " <> detail)
            Right (Just roles) | roles == expectedRoles -> AssertOk
            Right (Just roles) -> AssertFail ("interface roles for " <> family <> " are " <> renderRoles roles <> ", expected " <> renderRoles expectedRoles)
            Right Nothing -> AssertFail ("interface artifact contains no nominal summary for " <> family)
  AInterfaceContainsCurrentUniverseRoles family expectedRoles ->
    pure $ case interfaceArtifactRoles cu family of
      Left detail -> AssertFail ("current interface artifact is invalid: " <> detail)
      Right (Just roles) | roles == expectedRoles -> AssertOk
      Right (Just roles) -> AssertFail ("interface roles for " <> family <> " are " <> renderRoles roles <> ", expected " <> renderRoles expectedRoles)
      Right Nothing -> AssertFail ("interface artifact contains no nominal summary for " <> family)
  ATotal declaration ->
    pure $ case assertionGlobal declaration of
      Nothing -> AssertFail ("assertTotal: no typed declaration resolves as " <> declaration)
      Just (_, definition)
        | gdReducible definition -> AssertOk
        | otherwise ->
            AssertFail
              ( "assertTotal: " <> declaration
                  <> " is not verified conversion-safe by the checker"
              )
  AArithmeticCertificatesValid ->
    pure $ case renderCheckpointKCore of
      Left detail ->
        AssertFail
          ("assertArithmeticCertificatesValid: KCore emission failed: " <> detail)
      Right dump ->
        case parseKCore dump of
          Left err ->
            AssertFail
              ( "assertArithmeticCertificatesValid: generated KCore does not verify: "
                  <> kcteCode err <> ": " <> kcteMessage err
              )
          Right _ ->
            -- §15.8.7 permits small derivations to remain ordinary proof
            -- terms. The assertion validates every certificate that is
            -- present; it does not require the compiler to cross the compact
            -- certificate threshold for this particular fixture.
            assertKCoreRoundTripText
              parseKCore
              "generated arithmetic-certificate KCore"
              dump
  AArithmeticCertificateMutationsReject ->
    pure
      (assertCertificateMutationsReject
        "assertArithmeticCertificateMutationsReject"
        "E_KCORE_ARITHMETIC_CERTIFICATE_INVALID"
        kcoreArithmeticCertificateMutationCases)
  ATerminationCertificateMutationsReject ->
    pure
      (assertCertificateMutationsReject
        "assertTerminationCertificateMutationsReject"
        "E_KCORE_TEXT_INVALID"
        kcoreTerminationCertificateMutationCases)
  ARepresentationCertificateMutationsReject ->
    pure
      (assertCertificateMutationsReject
        "assertRepresentationCertificateMutationsReject"
        "E_KCORE_REPRESENTATION_CERTIFICATE_INVALID"
        kcoreRepresentationCertificateMutationCases)
  AInhabitance purpose expected tyExpr ->
    pure $ case elaborateQueryType [] tyExpr of
      Left detail -> AssertFail ("assertInhabitance: " <> detail)
      Right (queryState, _, queryType) ->
        let actual = inhabitanceSummaryForState queryState purpose queryType
         in requirePure
              (actual == expected)
              ( "assertInhabitance: " <> tyExpr <> " has " <> tshow actual
                  <> " for " <> T.pack (show purpose)
                  <> ", expected " <> tshow expected
              )
  ASymbolicCardinality expectedText tyExpr ->
    pure $
      let indexes = queryIndexNames expectedText tyExpr
          depth = length indexes
          indexTerms =
            Map.fromList
              [ (name, CVar (depth - ordinal - 1))
              | (ordinal, name) <- zip [0 :: Int ..] indexes
              ]
       in case parseCardExpr indexTerms expectedText of
            Left detail ->
              AssertFail ("assertSymbolicCardinality: invalid expected expression: " <> detail)
            Right expected ->
              case elaborateQueryType indexes tyExpr of
                Left detail -> AssertFail ("assertSymbolicCardinality: " <> detail)
                Right (queryState, queryDepth, queryType) ->
                  case symbolicCardinalityForState queryState queryDepth queryType of
                    Nothing ->
                      AssertFail
                        ( "assertSymbolicCardinality: no exact symbolic cardinality for "
                            <> tyExpr
                            <> " (normalized as "
                            <> renderTerm
                              ( quote
                                  (EvalCtx (Globals (csGlobals queryState)) (csMetas queryState) False mempty)
                                  queryDepth
                                  queryType
                              )
                            <> ")"
                        )
                    Just actual ->
                      requirePure
                        (normalizeCardExpr actual == normalizeCardExpr expected)
                        ( "assertSymbolicCardinality: " <> tyExpr <> " has "
                            <> renderCardExpr actual <> ", expected "
                            <> renderCardExpr expected
                        )
  AOrdinalRepresentation expectedText tyExpr ->
    pure $
      let indexes = queryIndexNames expectedText tyExpr
          depth = length indexes
          context = representationQueryContext indexes
          indexTerms =
            Map.fromList
              [ (name, CVar (depth - ordinal - 1))
              | (ordinal, name) <- zip [0 :: Int ..] indexes
              ]
       in case parseCardExpr indexTerms expectedText of
            Left detail ->
              AssertFail
                ("assertOrdinalRepresentation: invalid expected expression: " <> detail)
            Right expected ->
              case elaborateQueryType indexes tyExpr of
                Left detail -> AssertFail ("assertOrdinalRepresentation: " <> detail)
                Right (queryState, queryDepth, queryType) ->
                  case
                    ordinalRepresentationForState
                      queryState
                      context
                      queryDepth
                      queryType
                  of
                    Nothing ->
                      AssertFail
                        ("assertOrdinalRepresentation: no verified certificate for " <> tyExpr)
                    Just certificate ->
                      requirePure
                        ( normalizeCardExpr (orcCardinalityExpression certificate)
                            == normalizeCardExpr expected
                        )
                        ( "assertOrdinalRepresentation: " <> tyExpr <> " has "
                            <> renderCardExpr (orcCardinalityExpression certificate)
                            <> ", expected " <> renderCardExpr expected
                        )
  AExactNaturalRepresentation tyExpr ->
    pure $
      case elaborateQueryType [] tyExpr of
        Left detail -> AssertFail ("assertExactNaturalRepresentation: " <> detail)
        Right (queryState, queryDepth, queryType) ->
          case
            exactNaturalRepresentationForState
              queryState
              (representationQueryContext [])
              queryDepth
              queryType
          of
            Nothing ->
              AssertFail
                ("assertExactNaturalRepresentation: no verified certificate for " <> tyExpr)
            Just _ -> AssertOk
  ARefinementRepresentation baseTyExpr tyExpr ->
    pure $
      let indexes = queryIndexNames baseTyExpr tyExpr
          context = representationQueryContext indexes
       in case elaborateQueryType indexes baseTyExpr of
            Left detail ->
              AssertFail
                ("assertRefinementRepresentation: base type " <> detail)
            Right (baseState, baseDepth, baseType) ->
              case elaborateQueryType indexes tyExpr of
                Left detail -> AssertFail ("assertRefinementRepresentation: " <> detail)
                Right (queryState, queryDepth, queryType) ->
                  case
                    refinementRepresentationForState
                      queryState
                      context
                      queryDepth
                      queryType
                  of
                    Nothing ->
                      AssertFail
                        ("assertRefinementRepresentation: no verified certificate for " <> tyExpr)
                    Just certificate ->
                      let expectedBase =
                            quote
                              ( EvalCtx
                                  (Globals (csGlobals baseState))
                                  (csMetas baseState)
                                  False
                                  mempty
                              )
                              baseDepth
                              baseType
                          expectedIdentity =
                            representationTypeIdentity context expectedBase
                       in requirePure
                            (rrcBaseTypeIdentity certificate == expectedIdentity)
                            ( "assertRefinementRepresentation: " <> tyExpr
                                <> " records base " <> renderTerm (rrcBaseType certificate)
                                <> ", expected " <> baseTyExpr
                            )
  ARepresentationClass requested expected ->
    pure $ case verifiedRepresentationDecision requested of
      Left detail -> AssertFail ("assertRepresentationClass: " <> detail)
      Right decision ->
        let actual = Repr.renderVerifiedRepresentationClass (brdClass decision)
         in requirePure
              (actual == expected)
              ( requested <> " has representation " <> actual
                  <> ", expected " <> expected
              )
  ARuntimeFieldAbsent requested field ->
    pure $ case verifiedRepresentationDecision requested of
      Left detail -> AssertFail ("assertRuntimeFieldAbsent: " <> detail)
      Right decision ->
        requirePure
          ( any
              (\identity ->
                bsfiName identity == field
                  && backendFieldIsErased identity)
              (brdErasedFields decision)
          )
          ( requested <> " retains source field " <> field
              <> " or has no verified erasure justification for it"
          )
  where
    checkpointState = cuState cu
    -- The verifier's external environment is an import environment. The
    -- monolithic checker state also contains the module currently serialized;
    -- feeding those declarations back as imports creates a real stable-id
    -- collision and masks whether the artifact is source-free. Keep the full
    -- environment for emission, but verify against imports only.
    checkpointGlobals =
      Map.filterWithKey
        (\(GName owner _) _ -> owner /= cuModule cu)
        (csGlobals checkpointState)
    checkpointImportedConstructors =
      Map.filterWithKey
        (\(GName owner _) _ -> owner /= cuModule cu)
        checkpointConstructorInterfaces
    checkpointImportedDataInterfaces =
      Map.filterWithKey
        (\(GName owner _) _ -> owner /= cuModule cu)
        checkpointDataInterfaces
    checkpointEval = EvalCtx (Globals checkpointGlobals) (csMetas checkpointState) False mempty
    parseKCore =
      parseAndVerifyKCoreTextWithEnvironment
        checkpointEval
        checkpointGlobals
        checkpointImportedDataInterfaces
        checkpointImportedConstructors
    checkpointDataInterfaces =
      Map.map
        (\DataInfo {..} -> KCoreDataInfo diCtors diParamCount)
        (csDatas checkpointState)
    checkpointConstructorInterfaces =
      Map.map
        (\CtorInfo {..} ->
           KCoreConstructorInfo
             ciData
             ciUniverses
             ciType
             ciSourceFields)
        (csCtors checkpointState)
    renderCheckpointKCore =
      firstKCoreError $
        renderKCoreModule
          (cuModule cu)
          (EvalCtx (Globals (csGlobals checkpointState)) (csMetas checkpointState) False mempty)
          (csGlobals checkpointState)
          (csCoreBodies checkpointState)
          checkpointDataInterfaces
          checkpointConstructorInterfaces
          checkpointRepresentationCertificates
    assertCertificateMutationsReject
      directive
      expectedCode
      mutationCases =
        case renderCheckpointKCore of
          Left detail ->
            AssertFail (directive <> ": KCore emission failed: " <> detail)
          Right dump ->
            case parseKCore dump of
              Left err ->
                AssertFail
                  ( directive <> ": generated KCore does not verify: "
                      <> kcteCode err <> ": " <> kcteMessage err
                  )
              Right core ->
                case mutationCases core of
                  Left detail ->
                    AssertFail (directive <> ": " <> detail)
                  Right cases ->
                    case mapMaybe checkMutation cases of
                      [] -> AssertOk
                      failures ->
                        AssertFail
                          ( directive <> ": "
                              <> T.intercalate "; " failures
                          )
      where
        checkMutation (label, mutant) =
          case parseKCore mutant of
            Left err
              | kcteCode err == expectedCode -> Nothing
              | otherwise ->
                  Just
                    ( label <> " rejected with " <> kcteCode err
                        <> ", expected " <> expectedCode
                    )
            Right _ -> Just (label <> " mutation was accepted")
    checkpointRepresentationCertificates =
      kbackendRepresentationCertificates
        ( lowerKBackendIRForCapabilities
            (Set.fromList supportedCapabilities)
            checkpointState
        )
    errors = filter isError diags
    warnings = filter (\d -> dSeverity d == SevWarning) diags
    require b detail = pure (if b then AssertOk else AssertFail detail)
    requirePure b detail = if b then AssertOk else AssertFail detail
    verifiedRepresentationDecision requested = do
      backendIr <-
        maybe
          (Left "requires mode compile or mode run")
          Right
          mBackendIr
      case validateKBackendIR backendIr of
        violation : _ ->
          Left
            ( "final KBackendIR is invalid: "
                <> gnameText (bivBody violation)
                <> "@"
                <> backendNodeText (bivNode violation)
                <> " "
                <> bivCode violation
                <> ": "
                <> bivMessage violation
            )
        [] -> do
          subject <-
            maybe
              (Left ("no declaration or source field resolves as " <> requested))
              Right
              (representationSubject backendIr requested)
          maybe
            (Left ("final KBackendIR has no representation decision for " <> requested))
            Right
            (Map.lookup subject (kbirRepresentations backendIr))
    backendNodeText (BackendNodeId node) = T.pack (show node)
    representationSubject backendIr requested =
      ( BackendDeclarationSubject . fst
          <$> assertionGlobal requested
      )
        <|> do
          let (ownerText, fieldName) = splitSubjectField requested
          identity <-
            listToMaybe
              [ field
              | field <- Map.keys (kbirSourceFields backendIr)
              , bsfiName field == fieldName
              , sourceOwnerMatches ownerText (bsfiOwner field)
              ]
          pure (BackendConstructorFieldSubject identity)
    splitSubjectField requested =
      case T.breakOnEnd "." requested of
        ("", _) -> ("", requested)
        (prefix, field) -> (T.dropEnd 1 prefix, field)
    sourceOwnerMatches requested owner =
      requested == gnameText owner
        || requested == snd (splitQualified (gnameText owner))
    backendFieldIsErased identity =
      case mBackendIr >>= Map.lookup identity . kbirSourceFields of
        Just BackendFieldErased {} -> True
        _ -> False
    atMay values index = case drop index values of
      value : _ | index >= 0 -> Just value
      _ -> Nothing
    renderInferenceClass = \case
      InferenceSolvedPrincipal -> "SolvedPrincipal"
      InferenceUnsatisfiable -> "Unsatisfiable"
      InferenceNoPointwiseLeastSolution -> "NoPointwiseLeastSolution"
      InferenceOutsidePortableInferenceFragment -> "OutsidePortableInferenceFragment"
      InferenceBlockedByUnselectedMetas -> "BlockedByUnselectedMetas"
    normalizedFamilyName name = fromMaybe name (T.stripPrefix "(" name >>= T.stripSuffix ")")
    assertionGlobal declaration =
      let state = cuState cu
          (qualifiedModule, baseName) = splitQualified declaration
          candidates =
            [ GName (cuModule cu) declaration
            , GName (cuModule cu) baseName
            ]
              ++ [GName (ModuleName segments) baseName | Just segments <- [qualifiedModule]]
              ++ [global | Just global <- [Map.lookup declaration (csScope state)]]
              ++ [global | Just global <- [Map.lookup baseName (csScope state)]]
       in listToMaybe
            [ (global, definition)
            | global <- candidates
            , Just definition <- [Map.lookup global (csGlobals state)]
            ]
    elaborateQueryType indexes tyExpr =
      case parseModule "<type-query>" querySource of
        Left _ -> Left ("type does not parse: " <> tyExpr)
        Right (queryModule, _) ->
          let fixities = fileFixities path src
              (resolvedModule, _) = resolveModule fixities queryModule
              state0 =
                (cuState cu)
                  { csModule = cuModule cu
                  , csScope = queryScope
                  , csDiags = []
                  , csScopeNameCache = Nothing
                  }
              (state1, diagnostics) = checkModule state0 resolvedModule
              probe = GName (cuModule cu) "__assert_type_query_probe"
           in if hasErrors diagnostics
                then Left
                  ( "type does not elaborate: " <> tyExpr <> " ("
                      <> T.intercalate ", " [dCode diagnostic | diagnostic <- diagnostics, isError diagnostic]
                      <> ")"
                  )
                else case Map.lookup probe (csGlobals state1) >>= gdValue of
                  Just querySchema ->
                    case applyQueryIndexes state1 querySchema of
                      Just queryType -> Right (state1, length indexes, queryType)
                      Nothing -> Left ("type-query telescope does not match its Nat indices: " <> tyExpr)
                  Nothing -> Left ("type query produced no transparent type value: " <> tyExpr)
      where
        querySource =
          "type __assert_type_query_probe"
            <> T.concat [" (" <> index <> " : Nat)" | index <- indexes]
            <> " = " <> tyExpr <> "\n"
        queryScope = case parseModule path src of
          Right (originModule, _) -> importScopeForWithConfig (csUnsafe (cuState cu)) (cuState cu) originModule
          Left _ -> csScope (cuState cu)
        applyQueryIndexes state value =
          go 0 value
          where
            evaluation = EvalCtx (Globals (csGlobals state)) (csMetas state) False mempty
            go ordinal current
              | ordinal == length indexes = Just current
              | otherwise =
                  case force evaluation current of
                    VLam _ _ _ (Closure environment body) ->
                      go
                        (ordinal + 1)
                        (eval evaluation (VRigid ordinal [] : environment) body)
                    _ -> Nothing
    queryIndexNames expectedText tyExpr =
      nub
        [ identifier
        | identifier <- textIdentifiers tyExpr
        , isLower (T.head identifier)
        , identifier `elem` textIdentifiers expectedText
        ]
    representationQueryContext indexes =
      RepresentationContext
        { rcBinderTypes = replicate (length indexes) (CGlob prelNat)
        , rcUniverseConstraints = []
        }
    textIdentifiers =
      map T.pack . wordsBy (not . identifierCharacter) . T.unpack
      where
        identifierCharacter character =
          isAlphaNum character || character == '_' || character == '\''
        wordsBy separator = filter (not . null) . foldr step [[]]
          where
            step character (current : rest)
              | separator character = [] : current : rest
              | otherwise = (character : current) : rest
            step _ [] = []
    nominalSummaryFor unit family =
      listToMaybe
        [ summary
        | (global, definition) <- Map.toAscList (csGlobals (cuState unit))
        , normalizedFamilyName (gnameText global) == normalizedFamilyName family
        , Just summary <- [gdNominalSummary definition]
        ]
    interfaceArtifactRoles unit family = do
      let state = cuState unit
          matchingOwners =
            [ owner
            | (GName owner name, definition) <- Map.toAscList (csGlobals state)
            , normalizedFamilyName name == normalizedFamilyName family
            , Just summary <- [gdNominalSummary definition]
            , verifyNominalCumulativitySummary summary
            ]
          ownModule = case matchingOwners of
            owner : _ -> owner
            [] -> cuModule unit
          fullEval = EvalCtx (Globals (csGlobals state)) (csMetas state) False mempty
          importedGlobals = Map.filterWithKey (\(GName owner _) _ -> owner /= ownModule) (csGlobals state)
          importedConstructors =
            Map.map
              (\CtorInfo {..} ->
                KCoreConstructorInfo
                  ciData
                  ciUniverses
                  ciType
                  ciSourceFields)
              (Map.filterWithKey (\(GName owner _) _ -> owner /= ownModule) (csCtors state))
          dataInterfaces = Map.map (\DataInfo {..} -> KCoreDataInfo diCtors diParamCount) (csDatas state)
          importedDataInterfaces =
            Map.filterWithKey
              (\(GName owner _) _ -> owner /= ownModule)
              dataInterfaces
          constructorInterfaces =
            Map.map
              (\CtorInfo {..} ->
                KCoreConstructorInfo
                  ciData
                  ciUniverses
                  ciType
                  ciSourceFields)
              (csCtors state)
          importedEval = EvalCtx (Globals importedGlobals) (csMetas state) False mempty
      dump <-
        firstKCoreError $
          renderKCoreModule
            ownModule
            fullEval
            (csGlobals state)
            (csCoreBodies state)
            dataInterfaces
            constructorInterfaces
            ( kbackendRepresentationCertificates
                ( lowerKBackendIRForCapabilities
                    (Set.fromList supportedCapabilities)
                    state
                )
            )
      artifact <-
        firstKCoreError $
          parseAndVerifyKCoreTextWithEnvironment
            importedEval
            importedGlobals
            importedDataInterfaces
            importedConstructors
            dump
      pure (kcoreNominalRoles artifact family)
    firstKCoreError = either (Left . (\err -> kcteCode err <> ": " <> kcteMessage err)) Right
    schemaLiftFamilies unit =
      concat
        [ foldTerm
            (\case CSchemaLift family _ _ _ _ _ _ _ _ -> [family]; _ -> [])
            (const [])
            body
        | body <- Map.elems (csCoreBodies (cuState unit))
        ]
    nominalInterfaceHash unit =
      stableNominalHash . T.pack . show $
        [ (gKey global, summary)
        | (global@(GName owner _), definition) <- Map.toAscList (csGlobals (cuState unit))
        , owner == cuModule unit
        , Just summary <- [gdNominalSummary definition]
        ]
    compileSuiteFile relative =
      case [(file, source) | (file, source) <- files, makeRelative root file == T.unpack relative] of
        [source] -> pure (Right (compileWith [source]))
        [] -> pure (Left ("suite source '" <> relative <> "' does not exist"))
        _ -> pure (Left ("suite source '" <> relative <> "' is ambiguous"))
    compareCompiledUnits assertion left right action = case (left, right) of
      (Left detail, _) -> AssertHarnessError detail
      (_, Left detail) -> AssertHarnessError detail
      (Right leftUnit, Right rightUnit)
        | hasErrors (cuDiags leftUnit) || hasErrors (cuDiags rightUnit) ->
            AssertFail (assertion <> ": one of the compared sources does not compile")
        | otherwise -> action leftUnit rightUnit
    varianceText = \case
      Invariant -> "invariant"
      Covariant -> "covariant"
      Irrelevant -> "irrelevant"
    renderRoles roles = "[" <> T.intercalate "," (map varianceText roles) <> "]"
    withKCoreFile relative action = do
      let file = root </> T.unpack relative
      exists <- doesFileExist file
      if exists
        then readSourceFile file >>= action
        else pure (AssertHarnessError ("unreadable KCoreText file '" <> relative <> "' (§T.8)"))
    countIs what n actual =
      require (actual == n) ("expected " <> tshow n <> " " <> what <> ", got " <> tshow actual)
    -- error-count mismatches cite the first error, which makes failure
    -- triage over a large corpus far more informative
    countErrorsIs n =
      let actual = length errors
          firstE = case errors of
            (d : _)
              | actual /= n ->
                  "; first error: " <> dCode d <> " " <> tshow (dMessage d)
                    <> " at line " <> tshow (posLine (spanStart (dPrimary d)))
            _ -> ""
       in require (actual == n) ("expected " <> tshow n <> " errors, got " <> tshow actual <> firstE)
    describe sev code = sevText sev <> "[" <> code <> "]"
    sevText = \case
      SError -> "error"
      SWarning -> "warning"
      SNote -> "note"
      SInfo -> "info"
    sawCodes
      | null diags = " (no diagnostics)"
      | otherwise =
          " (saw: "
            <> T.intercalate ", " [dCode d <> "@" <> tshow (posLine (spanStart (dPrimary d))) | d <- diags]
            <> ")"
    sawMessages
      | null diags = " (no diagnostics)"
      | otherwise =
          " (saw: "
            <> T.intercalate "; " (take 3 [tshow (dMessage d) | d <- diags])
            <> ")"
    withRun k = case mRun of
      Just ri -> k ri
      Nothing -> pure (AssertHarnessError "run assertion outside mode run (§T.5.4)")
    -- compatibility executions (assertExecute / assertRunStdout) run a
    -- named IO global directly, independent of @mode run@
    execEntry what nm k
      | not (null errors) =
          pure (AssertFail (what <> ": the suite has compile errors"))
      | otherwise = case entryGlobal cu (snd (splitQualified nm)) of
          Nothing -> pure (AssertFail (what <> ": '" <> nm <> "' is not a defined global"))
          Just g -> do
            let st = cuState cu
            mres <-
              timeout runTimeoutMicros $
                runMainCapturedValue (Globals (csGlobals st)) (csMetas st) g
            case mres of
              Nothing -> pure (AssertFail (what <> ": execution of '" <> nm <> "' timed out"))
              Just (RunOk, mv, out) -> k st mv out
              Just (RunFail msg, _, _) ->
                pure (AssertFail (what <> ": runtime failure: " <> msg))
    goldenCompare p what sel = withRun $ \ri -> do
      let fp = root </> T.unpack p
      exists <- doesFileExist fp
      if not exists
        then pure (AssertHarnessError ("unreadable golden file '" <> p <> "' (§T.8)"))
        else do
          expected <- readSourceFile fp
          let actual = normalizeLF (sel ri)
              want = normalizeLF expected
          if actual == want
            then pure AssertOk
            else
              pure
                ( AssertFail
                    ( what <> " does not match golden file " <> p
                        <> ": expected " <> tshow want <> ", got " <> tshow actual
                    )
                )
    endsWithPath actual rel = actual == rel || ("/" <> rel) `T.isSuffixOf` actual

-- | §3.1/§3.1.2A code matching: a directive's @<code>@ matches a
-- diagnostic when it equals the rendered code or the diagnostic's
-- portable alias (an implementation may expose either spelling). For a
-- §3.1.4-listed condition the alias is the normative cross-
-- implementation comparison key (see 'Explain.requiredAliasTable'):
-- when the asserted spelling is another implementation's code it matches
-- iff both spellings resolve to the same §3.1.4 portable alias. There
-- are no implementation-defined spelling tolerances — a code §3.1.4 does
-- not standardize is compared verbatim — so a fixture pinning a
-- materially different required code than this implementation emits is
-- reported as a mismatch, never silently reconciled. The diagnostic
-- count is also compared exactly by 'codesMatchUpTo'.
diagHasCode :: Text -> Diagnostic -> Bool
diagHasCode code d =
  code `elem` ours
    || maybe False (`elem` ours) (portableAlias code)
  where
    ours = codeNames (dCode d)

-- | §T.5.1 @code-or-family@ matching for the structured assertions: a
-- spelling beginning with @kappa.@ is a standardized family; otherwise
-- it is a diagnostic code (code matching takes priority on ties).
matchCF :: Text -> Diagnostic -> Bool
matchCF cf d
  | "kappa." `T.isPrefixOf` cf = dFamily d == Just cf
  | otherwise = diagHasCode cf d

-- | Like 'matchCF' but also accepts a §3.2 family even when not spelled
-- with the @kappa.@ prefix — used for the suppressed-summary code, where
-- a fixture may name the family directly.
matchCFAny :: Text -> Diagnostic -> Bool
matchCFAny cf d = matchCF cf d || dFamily d == Just cf

-- | §3.1.5: this implementation's labels are the diagnostic's notes
-- anchored on the primary span. The only standardized label "role" they
-- carry is presentational ("note"), so a label-role assertion matches
-- when the requested role is @note@ and the diagnostic has at least one
-- note, or when a related origin carries the requested role.
labelHasRole :: Text -> Diagnostic -> Bool
labelHasRole role d =
  (role == "note" && not (null (dNotes d)))
    || any ((== role) . relatedRoleText . roRole) (dRelated d)

-- | Does a suppressed summary match a @code-or-family@ spelling?
suppMatches :: Text -> Suppressed -> Bool
suppMatches cf s
  | "kappa." `T.isPrefixOf` cf = suFamily s == Just cf
  | otherwise = cf `elem` codeNames (suCode s) || maybe False (`elem` codeNames (suCode s)) (portableAlias cf)

-- | §T.5.1 RFC-6901-style payload lookup, restricted to the shallow
-- pointers this implementation's payloads use: @/payload/<key>@ (or the
-- shorthand @/<key>@), plus the top-level @/family@, @/code@,
-- @/severity@, and @/message@. Returns the field's text value, or
-- Nothing when the pointer does not resolve.
payloadPointer :: Text -> Diagnostic -> Maybe Text
payloadPointer ptr d =
  case T.splitOn "/" (T.dropWhile (== '/') ptr) of
    ["payload", "kind"] -> Just (pKind (dPayload d))
    ["payload", k] -> lookup k (pFields (dPayload d))
    ["kind"] -> Just (pKind (dPayload d))
    ["family"] -> dFamily d
    ["code"] -> Just (dCode d)
    ["severity"] -> Just (severityToText (dSeverity d))
    ["message"] -> Just (dMessage d)
    [k] -> lookup k (pFields (dPayload d)) -- shorthand: bare payload key
    _ -> Nothing
  where
    severityToText = \case
      SevError -> "error"
      SevWarning -> "warning"
      SevNote -> "note"
      SevInfo -> "info"

-- | Parse an @expected-json@ scalar from a directive into its text value:
-- a JSON string @"x"@ yields @x@; a bare token yields itself. (Objects
-- and arrays are not used by the payloads this harness asserts.)
jsonScalarText :: Text -> Text
jsonScalarText t0 =
  let t = T.strip t0
   in case T.stripPrefix "\"" t >>= \r -> T.stripSuffix "\"" r of
        Just inner -> inner
        Nothing -> t

-- | Exact multiset comparison of expected codes against emitted errors,
-- where each expected spelling may match either the rendered code or
-- its portable alias. Small lists; simple backtracking matching.
codesMatchUpTo :: [Text] -> [Diagnostic] -> Bool
codesMatchUpTo codes diags0
  | length codes /= length diags0 = False
  | otherwise = go codes diags0
  where
    go [] [] = True
    go [] _ = False
    go (c : cs) ds =
      or
        [ go cs (before ++ after)
        | (before, d : after) <- splits ds
        , diagHasCode c d
        ]
    splits ds = [(take i ds, drop i ds) | i <- [0 .. length ds - 1]]

normalizeLF :: Text -> Text
normalizeLF = T.replace "\r" "\n" . T.replace "\r\n" "\n"

-- | @assertEval name expected@ (compatibility extension): evaluate a
-- global definition to a value and compare a canonical rendering with
-- the expected text.
assertEval :: CompiledUnit -> Maybe ModuleName -> Text -> Text -> AssertResult
assertEval cu mmod nm expected =
  case evalGlobal cu mmod nm >>= \g -> Map.lookup g (csGlobals (cuState cu)) of
    Nothing -> AssertFail ("assertEval: '" <> nm <> "' is not a defined global")
    Just gd -> case gdValue gd of
      Nothing -> AssertFail ("assertEval: '" <> nm <> "' has no value (signature only)")
      Just v ->
        let st = cuState cu
            ec = EvalCtx (Globals (csGlobals st)) (csMetas st) True mempty
            rendered = renderEvalValue ec v
         in if rendered == T.strip expected
              || renderEvalValueWith True ec v == T.strip expected
              then AssertOk
              else
                AssertFail
                  ("assertEval: '" <> nm <> "' evaluates to " <> rendered
                     <> ", expected " <> T.strip expected)

-- | @x-assertEvalErrorContains name substring@ (compatibility
-- extension): evaluating the global must fail at runtime with a message
-- containing the substring. Runtime failures surface in the pure
-- evaluator as stuck primitive applications whose reduction is
-- undefined (division by zero, @std.testing.failNow@).
assertEvalError :: CompiledUnit -> Maybe ModuleName -> Text -> Text -> AssertResult
assertEvalError cu mmod nm sub =
  case evalGlobal cu mmod nm >>= \g -> Map.lookup g (csGlobals (cuState cu)) of
    Nothing -> AssertFail ("assertEvalErrorContains: '" <> nm <> "' is not a defined global")
    Just gd -> case gdValue gd of
      Nothing -> AssertFail ("assertEvalErrorContains: '" <> nm <> "' has no value (signature only)")
      Just v ->
        let st = cuState cu
            ec = EvalCtx (Globals (csGlobals st)) (csMetas st) True mempty
         in case findRuntimeError ec (64 :: Int) v of
              Just msg
                | sub `T.isInfixOf` msg -> AssertOk
                | otherwise ->
                    AssertFail
                      ("evaluation of '" <> nm <> "' failed with " <> tshow msg
                         <> ", expected a message containing " <> tshow sub)
              Nothing ->
                AssertFail
                  ("'" <> nm <> "' evaluated without a runtime error (expected message containing "
                     <> tshow sub <> ")")
  where
    findRuntimeError ec = go
      where
        go 0 _ = Nothing
        go fuel v = case force ec v of
          VPrim "__recursionDepth" _ ->
            Just "evaluation exceeded the maximum recursion depth"
          VPrim "failNow" (a : _)
            | VLit (LitStr m) <- force ec a -> Just m
          VPrim p [_, b]
            | p == "divInt" || p == "modInt"
            , VLit (LitInt 0) <- force ec b ->
                Just "Division by zero"
          VPrim "intToNat" [a]
            | VLit (LitInt n) <- force ec a
            , n < 0 ->
                Just ("intToNat: " <> T.pack (show n) <> " has no Nat image")
          VPrim _ args -> firstJust (map (go (fuel - 1)) args)
          VCtor _ args -> firstJust (map (go (fuel - 1)) args)
          VRecordV fs -> firstJust (map (go (fuel - 1) . snd) fs)
          VInject _ x -> go (fuel - 1) x
          _ -> Nothing
    firstJust ms = case [m | Just m <- ms] of
      (m : _) -> Just m
      [] -> Nothing

-- | Unit results (the normal completion of an IO program) produce no
-- run-task output.
isUnitValue :: EvalCtx -> Value -> Bool
isUnitValue ec v = case force ec v of
  VCtor (GName _ "Unit") [] -> True
  VRecordV [] -> True
  _ -> False

-- Canonical value rendering for 'assertEval' (literals bare, strings
-- quoted, constructor applications in juxtaposition form).
renderEvalValue :: EvalCtx -> Value -> Text
renderEvalValue = renderEvalValueWith False

-- | The Boolean selects the corpus-compatible "loose" list rendering:
-- infix cons chains are never parenthesized, even in constructor
-- argument position (the external corpus' formatter writes
-- @Some 1 :: Nil@ for @Some (1 :: Nil)@).
renderEvalValueWith :: Bool -> EvalCtx -> Value -> Text
renderEvalValueWith looseCons ec = go (32 :: Int) RTop
  where
    go :: Int -> RenderPos -> Value -> Text
    go 0 _ _ = "…"
    go fuel pos v = case force ec v of
      VLit (LitInt n) -> tshow n
      VLit (LitDouble d)
        -- canonical numeric rendering: integral doubles print bare
        | not (isNaN d || isInfinite d)
        , d == fromInteger (round d :: Integer) ->
            tshow (round d :: Integer)
        | otherwise -> tshow d
      VLit (LitStr s) -> tshow s
      VLit (LitScalar c) -> tshow c
      VCtor (GName _ "Unit") [] -> "()"
      VRecordV [] -> "()"
      VCtor g [] -> gnameText g
      -- list cells render infix: 1 :: 2 :: Nil, parenthesized when an
      -- application argument or a left operand (precedence-aware)
      VCtor (GName _ "::") [h, t] ->
        parenIf (not looseCons && pos /= RTop) (go (fuel - 1) ROpLeft h <> " :: " <> go (fuel - 1) RTop t)
      VCtor g args ->
        -- constructor applications need parens only in argument position
        parenIf (pos == RArg) (T.unwords (gnameText g : map (go (fuel - 1) RArg) args))
      VRecordV fs ->
        "(" <> T.intercalate ", " [n <> " = " <> go (fuel - 1) RTop x | (n, x) <- fs] <> ")"
      VInject _ x -> go (fuel - 1) pos x
      other -> renderTerm (quote ec 0 other)
    parenIf b t = if b then "(" <> t <> ")" else t

-- rendering position for 'renderEvalValue': top level, application
-- argument, or left operand of an infix cell
data RenderPos = RTop | RArg | ROpLeft
  deriving stock (Eq)

-- | @assertType name typeExpr@ (§T.5.2): elaborate the expected type in
-- the compiled unit's state through a synthetic signature declaration
-- (checked in the origin file's module with the origin file's import
-- scope) and compare ordinary freshened occurrences of both declaration
-- interfaces up to checker-level definitional equality.
--
-- If the expected type does not parse or does not elaborate in this
-- implementation, the assertion cannot be satisfied and the test
-- *fails* (with a precise reason); the directive itself is well-formed,
-- so this is not a harness error (§T.8).
assertType :: FilePath -> Text -> CompiledUnit -> Text -> Text -> AssertResult
assertType path src cu nm tyExpr =
  case lookupTarget of
    Nothing -> AssertFail ("name '" <> nm <> "' does not resolve to a typed declaration")
    Just (targetName, gd) ->
      case elabExpected of
        Left err -> AssertFail err
        Right (st', probeNameGlobal, probeTy) ->
          let ec = EvalCtx (Globals (csGlobals st')) (csMetas st') False mempty
              actualR = renderTerm (quote ec 0 (gdType gd))
              probeR = renderTerm (quote ec 0 probeTy)
           in if declarationTypesConvertibleAtUse st' targetName probeNameGlobal
                -- Retain the legacy recovery for equal unresolved ordinary
                -- metas. Hidden universe parameters are handled by the
                -- schema-aware occurrence comparison above.
                || stripMetaIds actualR == stripMetaIds probeR
                then AssertOk
                else
                  AssertFail
                    ("type of '" <> nm <> "' is " <> actualR <> ", expected " <> probeR)
  where
    st = cuState cu
    originParse = parseModule path src
    -- the assertion is file-relative: resolve in the origin file's module
    originMod = case originParse of
      Right (m, _) | Just mp <- modHeader m -> ModuleName (modPathName mp)
      _ -> cuModule cu
    (qualMod, baseName) = splitQualified nm
    lookupTarget =
      let candidates =
            [GName originMod nm, GName (cuModule cu) nm]
              ++ [GName (ModuleName qm) baseName | Just qm <- [qualMod]]
              ++ [g | Just g <- [Map.lookup nm (csScope st)]]
       in case [(candidate, gd) | candidate <- candidates, Just gd <- [Map.lookup candidate (csGlobals st)]] of
            (resolved : _) -> Just resolved
            [] -> Nothing
    probeName = "__assert_type_probe"
    -- The probe sees the same unqualified scope as the origin file:
    -- prelude plus that file's imports over the accumulated state.
    probeScope = case originParse of
      Right (m, _) -> importScopeForWithConfig (csUnsafe st) st m
      Left _ -> csScope st
    elabExpected =
      case parseModule "<assertType>" (probeName <> " : " <> tyExpr <> "\n") of
        Left _ -> Left ("assertType: expected type does not parse: " <> tyExpr)
        Right (m, _) ->
          let fixities = fileFixities path src
              (m', _) = resolveModule fixities m
              -- Resetting csScope/csModule invalidates the §3.2.2 in-scope
              -- name cache, which is keyed on the import scope and module.
              st0 = st {csModule = originMod, csScope = probeScope, csDiags = [], csScopeNameCache = Nothing}
              (st1, ds0) = checkModule st0 m'
              -- the probe is deliberately definitionless; §9.1
              -- satisfaction does not apply to it
              ds = [d | d <- ds0, dCode d /= "E_SIGNATURE_UNSATISFIED"]
           in if hasErrors ds
                then
                  Left
                    ( "assertType: expected type does not elaborate: " <> tyExpr
                        <> case [dMessage d | d <- ds, isError d] of
                          (msg : _) -> " (" <> msg <> ")"
                          [] -> ""
                    )
                else case Map.lookup (GName originMod probeName) (csGlobals st1) of
                  Just probe -> Right (st1, GName originMod probeName, gdType probe)
                  Nothing -> Left "assertType: internal probe failure"

-- Fixity environment of the test file itself (its own fixity decls
-- participate in the expected-type parse), over the prelude defaults.
fileFixities :: FilePath -> Text -> FixityEnv
fileFixities path src =
  case parseModule path src of
    Right (m, _) -> Map.unionWith (++) (fixitiesOf (modDecls m)) defaultFixities
    Left _ -> defaultFixities

splitQualified :: Text -> (Maybe [Text], Text)
splitQualified t = case T.splitOn "." t of
  [x] -> (Nothing, x)
  segs -> (Just (init segs), last segs)

-- | @assertDeclKinds@ \/ @assertFileDeclKinds@ (§T.5.2): compare
-- top-level declaration kinds in source order (module header excluded).
assertDeclKinds :: Text -> FilePath -> Text -> [Text] -> AssertResult
assertDeclKinds which path src expected =
  case parseModule path src of
    Left _ -> AssertFail (which <> ": file does not parse")
    Right (m, _) ->
      let actual = map declKind (modDecls m)
       in if actual == expected
            then AssertOk
            else
              AssertFail
                ( which <> ": decl kinds are [" <> T.intercalate ", " actual
                    <> "], expected [" <> T.intercalate ", " expected <> "]"
                )

-- | @x-assertDeclDescriptors@ (compatibility extension): like
-- 'assertDeclKinds' but each entry also carries the declared name (and
-- explicit modifiers), e.g. @signature value, let value, trait Show@.
assertDeclDescriptors :: FilePath -> Text -> [Text] -> AssertResult
assertDeclDescriptors path src expected =
  case parseModule path src of
    Left _ -> AssertFail "x-assertDeclDescriptors: file does not parse"
    Right (m, _) ->
      let actual = map declDescriptor (modDecls m)
          norm = map (T.unwords . T.words)
       in if norm actual == norm expected
            then AssertOk
            else
              AssertFail
                ( "x-assertDeclDescriptors: decl descriptors are ["
                    <> T.intercalate ", " actual
                    <> "], expected [" <> T.intercalate ", " expected <> "]"
                )

-- | @assertParameterQuantities name q1 q2 ...@ (compatibility
-- extension): the named let definition's explicit parameters carry
-- exactly these §12.1.1 binder prefixes, rendered @0@\/@1@\/@ω@\/@<=1@\/
-- @>=1@\/@&@\/@&[r]@ (quantity before borrow marker; bare default is ω).
assertParamQuantities :: FilePath -> Text -> Text -> [Text] -> AssertResult
assertParamQuantities path src nm expected =
  case parseModule path src of
    Left _ -> AssertFail "assertParameterQuantities: file does not parse"
    Right (m, _) ->
      case [ld | DLet _ ld _ <- modDecls m, (nameText <$> ldName ld) == Just nm] of
        [] -> AssertFail ("assertParameterQuantities: no let '" <> nm <> "' in this file")
        (ld : _) ->
          let actual = map binderPrefixText [b | b <- ldBinders ld, not (bImplicit b)]
           in if actual == expected
                then AssertOk
                else
                  AssertFail
                    ( "assertParameterQuantities: '" <> nm <> "' parameters are ["
                        <> T.intercalate ", " actual
                        <> "], expected [" <> T.intercalate ", " expected <> "]"
                    )
  where
    binderPrefixText b
      -- an inout parameter elaborates at quantity 1 (§18.9.3)
      | bInout b = "1"
      | otherwise =
          let BinderPrefix _ mq mb = bPrefix b
              qt = case mq of
                Nothing -> ""
                Just QZero -> "0"
                Just QOne -> "1"
                Just QOmega -> "ω"
                Just QAtMostOne -> "<=1"
                Just QAtLeastOne -> ">=1"
                Just (QTerm _) -> "<quantity-expression>"
              bt = case mb of
                Nothing -> ""
                Just (BorrowMark Nothing) -> "&"
                Just (BorrowMark (Just r)) -> "&[" <> nameText r <> "]"
           in case qt <> bt of
                "" -> "ω"
                t -> t

-- | @assertInoutParameters name p1[, p2 ...]@ (compatibility extension):
-- the named let's @inout@-marked explicit parameter names, in order
-- (§18.9.2).
assertInoutParams :: FilePath -> Text -> Text -> [Text] -> AssertResult
assertInoutParams path src nm expected =
  case parseModule path src of
    Left _ -> AssertFail "assertInoutParameters: file does not parse"
    Right (m, _) ->
      case [ld | DLet _ ld _ <- modDecls m, (nameText <$> ldName ld) == Just nm] of
        [] -> AssertFail ("assertInoutParameters: no let '" <> nm <> "' in this file")
        (ld : _) ->
          let actual = [nameText n | b <- ldBinders ld, bInout b, Just n <- [bName b]]
           in if actual == expected
                then AssertOk
                else
                  AssertFail
                    ( "assertInoutParameters: '" <> nm <> "' inout parameters are ["
                        <> T.intercalate ", " actual
                        <> "], expected [" <> T.intercalate ", " expected <> "]"
                    )

-- | @assertDoItemDescriptors name d1, d2, ...@ (compatibility
-- extension): shape descriptors of the named let's do-block items, in
-- order (§18.2 do-item forms: @let x@, @using x@, @var x@,
-- @expression@, ...).
assertDoItemDescriptors :: FilePath -> Text -> Text -> [Text] -> AssertResult
assertDoItemDescriptors path src nm expected =
  case parseModule path src of
    Left _ -> AssertFail "assertDoItemDescriptors: file does not parse"
    Right (m, _) ->
      case [ld | DLet _ ld _ <- modDecls m, (nameText <$> ldName ld) == Just nm] of
        [] -> AssertFail ("assertDoItemDescriptors: no let '" <> nm <> "' in this file")
        (ld : _) -> case doItemsOf (ldBody ld) of
          Nothing ->
            AssertFail ("assertDoItemDescriptors: the body of '" <> nm <> "' is not a do block")
          Just items ->
            let actual = map doItemDescriptor items
             in if actual == expected
                  then AssertOk
                  else
                    AssertFail
                      ( "assertDoItemDescriptors: '" <> nm <> "' items are ["
                          <> T.intercalate ", " actual
                          <> "], expected [" <> T.intercalate ", " expected <> "]"
                      )
  where
    doItemsOf = \case
      EDo _ items _ -> Just items
      EAscription e _ _ -> doItemsOf e
      _ -> Nothing
    doItemDescriptor = \case
      DoBind lb -> "let " <> prefixedHead (lbPrefix lb) (lbPattern lb)
      DoLet lb -> "let " <> prefixedHead (lbPrefix lb) (lbPattern lb)
      DoLetQ p _ _ _ -> "let? " <> patHeadText p
      DoVar n _ _ _ -> "var " <> nameText n
      DoAssign n _ _ _ -> "assign " <> nameText n
      DoExpr _ -> "expression"
      DoUsing _ p _ _ -> "using " <> patHeadText p
      DoDefer {} -> "defer"
      DoReturn {} -> "return"
      DoBreak {} -> "break"
      DoContinue {} -> "continue"
      DoWhile {} -> "while"
      DoFor {} -> "for"
      DoIf {} -> "if"
      DoDecl {} -> "declaration"
    patHeadText = \case
      PVar n -> nameText n
      PTyped p _ _ -> patHeadText p
      PAs n _ -> nameText n
      _ -> "_"
    -- an explicit quantity/borrow prefix is part of the descriptor
    -- (e.g. "let 1 file", "let & borrowed")
    prefixedHead (BinderPrefix _ mq mb) p =
      let qt = case mq of
            Nothing -> ""
            Just QZero -> "0"
            Just QOne -> "1"
            Just QOmega -> "ω"
            Just QAtMostOne -> "<=1"
            Just QAtLeastOne -> ">=1"
            Just (QTerm _) -> "<quantity-expression>"
          bt = case mb of
            Nothing -> ""
            Just (BorrowMark Nothing) -> "&"
            Just (BorrowMark (Just r)) -> "&[" <> nameText r <> "]"
          pre = qt <> bt
       in if T.null pre then patHeadText p else pre <> " " <> patHeadText p

-- | @assertContainsTokenTexts t1, t2, ...@ (compatibility extension):
-- each text occurs as the source text of some lexed token of this file.
assertTokenTexts :: FilePath -> Text -> [Text] -> AssertResult
assertTokenTexts path src wanted =
  case lexSource path src of
    Left _ -> AssertFail "assertContainsTokenTexts: file does not lex"
    Right (_, toks) ->
      let texts = [sliceSpan src (locSpan t) | t <- toks]
          missing = [w | w <- wanted, w `notElem` texts]
       in if null missing
            then AssertOk
            else
              AssertFail
                ( "assertContainsTokenTexts: no token has source text "
                    <> T.intercalate ", " (map tshow missing)
                )

-- | The portable token-kind names of the @x-assertContainsTokenKinds@
-- compatibility extension, mapped onto this lexer's token shapes.
portableTokenKinds :: [(Text, Located -> Bool)]
portableTokenKinds =
  [ ("Identifier", \t -> case locTok t of TokIdent {} -> True; _ -> False)
  , ("IntegerLiteral", \t -> case locTok t of TokInt {} -> True; _ -> False)
  , ("FloatLiteral", \t -> case locTok t of TokFloat {} -> True; _ -> False)
  , ("StringLiteral", \t -> case locTok t of TokString {} -> True; _ -> False)
  , ("CharacterLiteral", \t -> case locTok t of TokQuoted {} -> True; _ -> False)
  , ("LeftParen", \t -> case locTok t of TokLParen -> True; _ -> False)
  , ("RightParen", \t -> case locTok t of TokRParen -> True; _ -> False)
  , ("Operator", \t -> case locTok t of TokOperator {} -> True; _ -> False)
  , ("Indent", \t -> case locTok t of TokIndent -> True; _ -> False)
  , ("Dedent", \t -> case locTok t of TokDedent -> True; _ -> False)
  , -- this lexer keeps an interpolated string as ONE token carrying its
    -- fragments; the segment kinds map onto the fragment structure
    ("InterpolatedStringStart", interpolated)
  , ("InterpolatedStringEnd", interpolated)
  , ("InterpolationStart", interpolated)
  , ("InterpolationEnd", interpolated)
  , ("StringTextSegment", hasTextFragment)
  ]
  where
    interpolated t = case locTok t of
      TokString sl -> any isInterp (slFragments sl)
      _ -> False
    hasTextFragment t = case locTok t of
      TokString sl -> any isText (slFragments sl)
      _ -> False
    isInterp = \case
      FragInterp {} -> True
      FragInterpFmt {} -> True
      FragLit {} -> False
    isText = \case
      FragLit {} -> True
      _ -> False

-- | @x-assertContainsTokenKinds@ (compatibility extension): at least
-- one token of each named kind occurs in this file.
assertTokenKinds :: FilePath -> Text -> [Text] -> AssertResult
assertTokenKinds path src wanted =
  case lexSource path src of
    Left _ -> AssertFail "x-assertContainsTokenKinds: file does not lex"
    Right (_, toks) ->
      let missing =
            [ k
            | k <- wanted
            , Just pr <- [lookup k portableTokenKinds]
            , not (any pr toks)
            ]
       in if null missing
            then AssertOk
            else
              AssertFail
                ("x-assertContainsTokenKinds: no token of kind "
                   <> T.intercalate ", " missing)

-- | @x-assertModule@ (compatibility extension): the module-header name
-- of this file.
assertModuleName :: FilePath -> Text -> Text -> AssertResult
assertModuleName path src expected =
  case parseModule path src of
    Left _ -> AssertFail "x-assertModule: file does not parse"
    Right (m, _) -> case modHeader m of
      Just mp
        | T.intercalate "." (modPathName mp) == expected -> AssertOk
        | otherwise ->
            AssertFail
              ( "x-assertModule: module is '"
                  <> T.intercalate "." (modPathName mp)
                  <> "', expected '" <> expected <> "'"
              )
      Nothing -> AssertFail "x-assertModule: file has no module header"

-- | @x-assertModuleAttributes@ (compatibility extension).
assertModuleAttrs :: FilePath -> Text -> [Text] -> AssertResult
assertModuleAttrs path src expected =
  case parseModule path src of
    Left _ -> AssertFail "x-assertModuleAttributes: file does not parse"
    Right (m, _) ->
      let actual = map nameText (modAttrs m)
          missing = [a | a <- expected, a `notElem` actual]
       in if null missing
            then AssertOk
            else
              AssertFail
                ("x-assertModuleAttributes: missing attribute(s) "
                   <> T.intercalate ", " missing)

-- | @x-assertDataConstructors@ (compatibility extension): the named
-- data declaration's constructor names, in declaration order.
assertDataCtors :: FilePath -> Text -> Text -> [Text] -> AssertResult
assertDataCtors path src tn expected =
  case parseModule path src of
    Left _ -> AssertFail "x-assertDataConstructors: file does not parse"
    Right (m, _) ->
      case [dd | DData _ dd _ <- modDecls m, nameText (ddName dd) == tn] of
        (dd : _) ->
          let actual = map (nameText . cdName) (ddCtors dd)
           in if actual == expected
                then AssertOk
                else
                  AssertFail
                    ( "x-assertDataConstructors: '" <> tn <> "' has constructors ["
                        <> T.intercalate ", " actual
                        <> "], expected [" <> T.intercalate ", " expected <> "]"
                    )
        [] -> AssertFail ("x-assertDataConstructors: no data declaration '" <> tn <> "' in this file")

-- | Erase metavariable ids from a rendered type (@?m123@ → @?m@), so
-- that distinct-but-unconstrained metas compare equal in 'assertType'.
stripMetaIds :: Text -> Text
stripMetaIds t = case T.breakOn "?m" t of
  (pre, rest)
    | T.null rest -> pre
    | otherwise ->
        pre <> "?m" <> stripMetaIds (T.dropWhile isDigit (T.drop 2 rest))

-- | The source slice covered by a span (1-based line\/column positions).
sliceSpan :: Text -> Span -> Text
sliceSpan src sp =
  let ls = T.splitOn "\n" src
      Pos sl sc = spanStart sp
      Pos el ec = spanEnd sp
      lineAt i = if i >= 1 && i <= length ls then ls !! (i - 1) else ""
   in if sl == el
        then T.take (ec - sc) (T.drop (sc - 1) (lineAt sl))
        else
          T.intercalate "\n" $
            [T.drop (sc - 1) (lineAt sl)]
              ++ [lineAt i | i <- [sl + 1 .. el - 1]]
              ++ [T.take (ec - 1) (lineAt el)]

-- | Apply a §3.1.6 fix's source edits to the matching suite files
-- (@assertDiagnosticFixCompiles@). Edits are grouped by file and applied
-- within each file in descending start position so earlier edits do not
-- shift the offsets of later ones; overlapping edits or an edit on a
-- range we cannot resolve are reported as a harness error. An edit whose
-- file is not among the suite sources (e.g. a generated-only synthetic
-- origin) is rejected — §T.5.1 forbids marking such a fix
-- machine-applicable, so encountering one means the record is malformed.
applyFixToFiles :: [(FilePath, Text)] -> [SourceEdit] -> Either Text [(FilePath, Text)]
applyFixToFiles files edits = foldl' step (Right files) (byFile edits)
  where
    byFile es = [(f, [e | e <- es, seFile e == f]) | f <- distinct (map seFile es)]
    distinct = foldr (\x xs -> if x `elem` xs then xs else x : xs) []
    step (Left e) _ = Left e
    step (Right fs) (f, es) =
      case lookup f fs of
        Nothing -> Left ("fix edits a file outside the suite: " <> T.pack f)
        Just src -> do
          src' <- applyEdits src es
          Right [(fp, if fp == f then src' else s) | (fp, s) <- fs]
    applyEdits src es = do
      spans <- mapM (\e -> (,) <$> offsetsOf src (seRange e) <*> pure (seReplacement e)) es
      let ascending = sortOn (\((s, _), _) -> s) spans
      validateNonOverlapping ascending
      -- descending by start offset, so splices keep earlier indices valid
      let ordered = reverse ascending
      pure (foldl' splice src ordered)
    splice s ((a, b), repl) = T.take a s <> repl <> T.drop b s
    validateNonOverlapping [] = Right ()
    validateNonOverlapping [((a, b), _)]
      | a <= b = Right ()
      | otherwise = Left "fix edit range end precedes start"
    validateNonOverlapping (((a, b), _) : rest@(((c, _), _) : _))
      | a > b = Left "fix edit range end precedes start"
      | c < b = Left "fix contains overlapping edits"
      | otherwise = validateNonOverlapping rest
    -- 1-based (line, col) span → (startOffset, endOffset) char indices.
    offsetsOf src sp =
      let Pos sl sc = spanStart sp
          Pos el ec = spanEnd sp
       in do
            a <- offsetOf src sl sc
            b <- offsetOf src el ec
            if a <= b
              then Right (a, b)
              else Left "fix edit range end precedes start"
    offsetOf src ln col =
      let ls = T.splitOn "\n" src
       in if ln >= 1 && ln <= length ls
            then
              case drop (ln - 1) ls of
                (line : _) ->
                  if col >= 1 && col <= T.length line + 1
                    then Right (sum (map ((+ 1) . T.length) (take (ln - 1) ls)) + (col - 1))
                    else Left "fix edit range falls outside the source file"
                [] -> Left "fix edit range falls outside the source file"
            else Left "fix edit range falls outside the source file"

-- | @x-assertTraitMembers Trait m1, m2@ (compatibility extension):
-- the named trait declares exactly these member names, in order.
assertTraitMembers :: FilePath -> Text -> Text -> [Text] -> AssertResult
assertTraitMembers path src tn expected =
  case parseModule path src of
    Left _ -> AssertFail "x-assertTraitMembers: file does not parse"
    Right (m, _) ->
      case [td | DTrait _ td _ <- modDecls m, nameText (trName td) == tn] of
        [] -> AssertFail ("x-assertTraitMembers: no trait '" <> tn <> "' in this file")
        (td : _) ->
          let actual = dedupe [n | Just n <- map memberName (trMembers td)]
           in if actual == expected
                then AssertOk
                else
                  AssertFail
                    ( "x-assertTraitMembers: trait '" <> tn <> "' members are ["
                        <> T.intercalate ", " actual
                        <> "], expected [" <> T.intercalate ", " expected <> "]"
                    )
  where
    memberName = \case
      TraitSig n _ _ -> Just (nameText n)
      TraitDefault ld _ -> nameText <$> ldName ld
    dedupe = foldr (\x acc -> x : filter (/= x) acc) []

-- | Decl descriptor rendering for @x-assertDeclDescriptors@: explicit
-- modifiers, the decl kind, and the declared name (import\/export
-- specs render in source-like form).
declDescriptor :: Decl -> Text
declDescriptor d = case d of
  DSig mods n _ _ -> modsPrefix mods <> "signature " <> nameText n
  DLet mods ld _ -> modsPrefix mods <> "let" <> nameSuffix (ldName ld)
  DData mods dd _ -> modsPrefix mods <> "data " <> nameText (ddName dd)
  DTypeAlias mods n _ _ _ _ -> modsPrefix mods <> "type " <> nameText n
  DTrait mods td _ -> modsPrefix mods <> "trait " <> nameText (trName td)
  DInstance {} -> "instance"
  DDerive {} -> "derive"
  DEffect mods ed _ -> modsPrefix mods <> "effect " <> nameText (effName ed)
  DFixity (FixityDecl k _ op) _ -> "fixity " <> fixityWord k <> " " <> nameText op
  DImport specs _ -> "import " <> T.intercalate " | " (map renderSpec specs)
  DExport specs _ -> "export " <> T.intercalate " | " (map renderSpec specs)
  DExpect mods form _ -> modsPrefix mods <> "expect " <> expectNm form
  DPattern mods ld _ -> modsPrefix mods <> "pattern" <> nameSuffix (ldName ld)
  DProjection mods n _ _ _ _ -> modsPrefix mods <> "projection " <> nameText n
  DTopSplice {} -> "splice"
  DUnsafeAssert k inner _ -> unsafeAssertWord k <> " " <> declDescriptor inner
  where
    nameSuffix = maybe "" (\n -> " " <> nameText n)
    unsafeAssertWord = \case
      AssertTerminates -> "assertTerminates"
      AssertReducible -> "assertReducible"
      AssertTotal -> "assertTotal"
    modsPrefix mods = vis <> opq
      where
        vis = case dmVisibility mods of
          VisPublic -> "public "
          VisPrivate -> "private "
          VisDefault -> ""
        opq = if dmOpaque mods then "opaque " else ""
    -- the corpus's descriptor keeps the fixity CLASS only (the
    -- associativity is not part of the descriptor)
    fixityWord = \case
      InfixN -> "infix"
      InfixL -> "infix"
      InfixR -> "infix"
      Prefix -> "prefix"
      Postfix -> "postfix"
    expectNm = \case
      ExpectTerm n _ -> nameText n
      ExpectType n _ _ -> nameText n
      ExpectData n _ _ -> nameText n
      ExpectTrait n _ _ -> nameText n
    renderSpec = \case
      ImportModule r Nothing -> renderRef r
      ImportModule r (Just a) -> renderRef r <> " as " <> nameText a
      ImportItems r items -> renderRef r <> ".(" <> T.intercalate " + " (map renderItem items) <> ")"
      ImportAll r _ -> renderRef r <> ".*"
      ImportSingleton r n -> renderRef r <> "." <> nameText n
    renderRef = \case
      RefPath mp -> T.intercalate "." (modPathName mp)
      RefUrl u _ -> "\"" <> u <> "\""
    renderItem it =
      T.unwords
        ( ["unhide" | iiUnhide it]
            ++ ["clarify" | iiClarify it]
            ++ maybe [] (\k -> [selWord k]) (iiKind it)
            ++ [nameText (iiName it) <> (if iiCtorAll it then "(..)" else "")]
        )
        <> maybe "" (\a -> " as " <> nameText a) (iiAlias it)
    selWord = \case
      SelTerm -> "term"
      SelType -> "type"
      SelTrait -> "trait"
      SelCtor -> "ctor"
      SelEffectLabel -> "effect label"
      SelModule -> "module"

declKind :: Decl -> Text
declKind = \case
  DSig {} -> "signature"
  DLet {} -> "let"
  DData {} -> "data"
  DTypeAlias {} -> "type"
  DTrait {} -> "trait"
  DInstance {} -> "instance"
  DDerive {} -> "derive"
  DEffect {} -> "effect"
  DFixity {} -> "fixity"
  DImport {} -> "import"
  DExport {} -> "export"
  DExpect {} -> "expect"
  DPattern {} -> "pattern"
  DProjection {} -> "projection"
  DTopSplice {} -> "splice"
  DUnsafeAssert _ inner _ -> declKind inner

-- ── Tree walking ─────────────────────────────────────────────────────

-- | Run a path: a @.kp@ file is a single-file inline test; a directory
-- containing @step0@ or @incremental.ktest@ is one incremental step
-- suite (§T.7); a directory that declares itself a suite root with
-- @suite.ktest@ or @main.kp@ is one directory suite (§T.2) compiled as a
-- single unit (at any depth), as is a directory named directly that
-- contains @.kp@ files; any other directory recurses, running each
-- directly-contained @.kp@ file as a single-file inline test.
-- Prints one result line per test.
runTestPath :: FilePath -> IO [TestReport]
runTestPath = runTestPathAt True

-- | Run a path as exactly one suite (the @kappa test --suite@ form):
-- the directory is the §T.2 suite root even when its @.kp@ files all
-- live in subdirectories, so one fixture is always one result.
runTestSuitePath :: FilePath -> IO [TestReport]
runTestSuitePath root = do
  isDir <- doesDirectoryExist root
  if not isDir
    then emitReport (runTestFile root)
    else do
      incr <- isIncrementalRoot root
      emitReport (if incr then runIncrementalDir root else runSuiteDir root)

emitReport :: IO TestReport -> IO [TestReport]
emitReport act = do
  rep <- act
  putStrLn (T.unpack (reportLine rep))
  pure [rep]

runTestPathAt :: Bool -> FilePath -> IO [TestReport]
runTestPathAt topLevel root = do
  isDir <- doesDirectoryExist root
  if not isDir
    then emitOne (runTestFile root)
    else do
      incr <- isIncrementalRoot root
      if incr
        then emitOne (runIncrementalDir root)
        else do
          suite <- isSuiteRoot topLevel root
          if suite
            then emitOne (runSuiteDir root)
            else do
              entries <- sort <$> listDirectory root
              let paths = [root </> e | e <- entries]
              dirs <- filterM doesDirectoryExist paths
              let files = [p | p <- paths, ".kp" `isSuffixOf` p, p `notElem` dirs]
              fileReps <- concat <$> mapM (emitOne . runTestFile) files
              dirReps <- concat <$> mapM (runTestPathAt False) dirs
              pure (fileReps ++ dirReps)
  where
    emitOne = emitReport

-- | §T.2 form 3: a directory with @step0@\/@step1@\/… subdirectories
-- (and optionally @incremental.ktest@) is one incremental step suite.
isIncrementalRoot :: FilePath -> IO Bool
isIncrementalRoot dir = do
  hasStep0 <- doesDirectoryExist (dir </> "step0")
  hasKtest <- doesFileExist (dir </> "incremental.ktest")
  pure (hasStep0 || hasKtest)

-- | Incremental step suites need Chapter 34 session reuse, which this
-- implementation does not keep: the @incremental@ capability is not
-- claimed (§T.4), so these suites classify as unsupported — via their
-- own @requires@ directives when present, otherwise directly. Scan
-- errors in @incremental.ktest@ still surface as harness errors.
runIncrementalDir :: FilePath -> IO TestReport
runIncrementalDir dir = guardExceptions dir $ do
  let ktestPath = dir </> "incremental.ktest"
  hasKtest <- doesFileExist ktestPath
  scanned <-
    if hasKtest
      then scanDirectives <$> readSourceFile ktestPath
      else pure ([], [])
  case scanned of
    (_, errs@(_ : _)) ->
      pure (TestReport dir HarnessError (T.intercalate "; " errs))
    (ss, []) ->
      pure $ case [u | SUnsupported u <- ss] of
        (u : _) -> TestReport dir Unsupported u
        [] ->
          TestReport dir Unsupported
            "incremental step suites require capability 'incremental', which this harness does not provide (§T.4, §T.7)"

-- | §T.2: a directory suite is "a directory containing one or more
-- @.kp@ source files and optionally a file named @suite.ktest@". A
-- directory is taken to be *one* directory suite — compiled as a single
-- unit per §T.2 — when it declares itself a suite root by carrying a
-- @suite.ktest@ or @main.kp@, at any depth of the recursive walk; or
-- when it is the directory the user named directly (@topLevel@) and it
-- directly contains @.kp@ files. A bare directory of @.kp@ files reached
-- *during* the recursive descent is treated as a collection of
-- single-file inline tests (§T.2 form 1): these files are independent
-- inline tests with their own directives, not co-compiled modules, so
-- co-compiling them as one unit would conflate unrelated tests and
-- collide their top-level definitions. (Incremental roots are detected
-- earlier and take precedence.) The @--suite@ entrypoint
-- ('runTestSuitePath') forces the whole-directory reading when a caller
-- really does mean one suite spanning subdirectories.
isSuiteRoot :: Bool -> FilePath -> IO Bool
isSuiteRoot topLevel dir = do
  hasKtest <- doesFileExist (dir </> "suite.ktest")
  hasMain <- doesFileExist (dir </> "main.kp")
  direct <-
    if topLevel && not (hasKtest || hasMain)
      then do
        entries <- listDirectory dir
        pure (any (".kp" `isSuffixOf`) entries)
      else pure False
  pure (hasKtest || hasMain || direct)

collectKp :: FilePath -> IO [FilePath]
collectKp root = sortOn relKey <$> go root
  where
    relKey = map (\c -> if c == '\\' then '/' else c) . makeRelative root
    go dir = do
      entries <- sort <$> listDirectory dir
      let paths = [dir </> e | e <- entries]
      dirs <- filterM doesDirectoryExist paths
      let files = [p | p <- paths, ".kp" `isSuffixOf` p, p `notElem` dirs]
      rest <- concat <$> mapM go dirs
      pure (files ++ rest)

tshow :: Show a => a -> Text
tshow = T.pack . show
