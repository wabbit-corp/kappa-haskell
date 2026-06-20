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

import Control.Exception (SomeException, evaluate, try)
import Control.Monad (filterM)
import Data.Char (isDigit)
import Data.List (foldl', isSuffixOf, sort, sortOn)
import Data.Maybe (fromMaybe, listToMaybe, mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Encoding.Error as TEE
import qualified Data.ByteString as BS
import qualified Data.Map.Strict as Map
import Kappa.Check (AuditRecord (..), CheckState (..), UnsafeConfig (..), checkModule, defaultUnsafeConfig, scriptUnsafeConfig)
import Kappa.Core
import Kappa.Diagnostic
import Kappa.Eval (EvalCtx (..), GlobalDef (..), Globals (..), convertible, force, quote)
import Kappa.Explain (codeNames, explainExists)
import Kappa.Interp (RunResult (..), runMainCapturedValue)
import Kappa.Lexer (lexSource)
import Kappa.Parser (parseModule)
import Kappa.Pipeline (CompiledUnit (..), compileFiles, compileFilesIn, compileFilesWithConfig, importScopeFor, loadSourceFile, moduleNameRelTo)
import Kappa.Pretty (renderTerm)
import Kappa.Regex (Regex, compileRegex, regexSearch)
import Kappa.Resolve (FixityEnv, defaultFixities, fixitiesOf, resolveModule)
import Kappa.Source (ModuleName (..), Pos (..), Span (..))
import Kappa.Syntax
import Kappa.Token (Located (..), StrFragment (..), StringLit (..), Token (..))
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory)
import System.FilePath (takeDirectory, (</>))
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
  | SStageDump !Text -- ^ §T.5.3 assertStageDump of an unservable checkpoint: ill-formed unless 'requires capability stageDumps' gates it
  | SAssert !Assertion

-- ── Directive scanning (§T.3) ────────────────────────────────────────

declKindNames :: [Text]
declKindNames =
  [ "import", "export", "fixity", "signature", "let", "data", "type"
  , "trait", "instance", "derive", "effect", "pattern", "expect"
  ]

-- This implementation produces no Chapter 34 stage-dump checkpoint
-- vocabulary, so @assertStageDump <checkpoint> …@ names a checkpoint the
-- harness cannot serve. Per §T.5.3 ("`<checkpoint>` must name a valid
-- compiler checkpoint") read against §T.8 (which reserves @unsupported@
-- for unmet @requires@ or unsupported @x-@ directives only), the faithful
-- classification of an *un-gated* @assertStageDump@ is a harness error,
-- not a silent downgrade. A suite that wants the soft outcome gates with
-- @requires capability stageDumps@, which is reported @unsupported@
-- earlier (§T.4). Handled explicitly in 'dispatch'.
--
-- @assertDiagnosticFixCompiles@ is implemented against the §3.1.6 fix
-- records (apply the first machine-applicable fix, recompile, assert no
-- errors) — see 'AFixCompiles'. No standard directive remains downgraded
-- to a non-§T.8 @unsupported@.

-- §T.4 portable capabilities this harness provides. @runTask@: programs
-- are executed in-process by the tree-walking interpreter. @
-- pipelineTrace@: portable (event, subject) counts are recorded for
-- parse\/buildKFrontIR\/lowerKCore. Not provided: @stageDumps@ (no
-- Chapter 34 checkpoint serialization) and @incremental@ (no session
-- state survives between suite roots).
--
-- The corpus's nonstandard capability names are provided as documented
-- compatibility extensions (§T.1): @legacyCharAlias@ — the prelude
-- defines the §28.5 sanctioned @type Char = UnicodeScalar@ alias — and
-- @unicodeSourceWarnings@ — the §3.1.3 optional source-hygiene
-- warnings (W_UNICODE_BIDI_CONTROL, W_UNICODE_CONFUSABLE_IDENTIFIER,
-- W_UNICODE_NON_NORMALIZED_SOURCE_TEXT) are emitted by the pipeline.
supportedCapabilities :: [Text]
supportedCapabilities = ["runTask", "pipelineTrace", "legacyCharAlias", "unicodeSourceWarnings"]

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
        _ -> bad "malformed 'dumpFormat' directive"
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
      -- §T.5.3: this implementation serializes no Chapter 34 stage-dump
      -- checkpoints, so any <checkpoint> names one the harness cannot
      -- serve. §T.5.3 requires <checkpoint> to "name a valid compiler
      -- checkpoint"; an un-gated assertion of an unservable checkpoint is
      -- ill-formed (§T.8 reserves 'unsupported' for requires/x-).
      "assertStageDump" -> case args of
        [chk, "equals", _path] -> ok (SStageDump chk)
        _ -> bad "malformed 'assertStageDump' directive (expected '<checkpoint> equals <path>')"
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
  runSuite dir dir (orderByImports (zip files srcs)) mktest preDiags

-- | Order suite files so that imported modules compile first (light
-- textual scan of @module@ headers and @import@ lines; cycles keep the
-- original order).
orderByImports :: [(FilePath, Text)] -> [(FilePath, Text)]
orderByImports files
  | length files < 2 = files
  | otherwise = go [] (map describe files)
  where
    describe f@(_, src) = (headerModule src, importedModules src, f)
    allMods = mapMaybe (\(m, _, _) -> m) (map describe files)
    go _ [] = []
    go done rest =
      case break ready rest of
        (_, []) -> [f | (_, _, f) <- rest] -- cyclic or unresolvable: keep order
        (pre, (m, _, f) : post) ->
          f : go (maybe done (: done) m) (pre ++ post)
      where
        ready (_, imps, _) =
          all (\i -> i `elem` done || i `notElem` allMods) imps
    headerModule src =
      case [ws | l <- take 10 (T.lines src), let ws = T.words l, "module" `elem` ws] of
        (ws : _) -> case drop 1 (dropWhile (/= "module") ws) of
          (m : _) -> Just m
          [] -> Nothing
        [] -> Nothing
    importedModules src =
      [ T.dropWhileEnd (== '.') (T.takeWhile (\c -> c /= '*' && c /= '(' && c /= ' ') m)
      | l <- T.lines src
      , Just rest0 <- [T.stripPrefix "import " (T.stripStart l)]
      , let m = T.strip rest0
      , not (T.null m)
      ]

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
              asserts = [(p, src, a) | (p, src, SAssert a) <- scanned]
              scripted = not (null [() | (_, _, SScriptMode) <- scanned])
              stdinFiles = [p | (_, _, SStdinFile p) <- scanned]
              stageDumps = [c | (_, _, SStageDump c) <- scanned]
              -- §T.6: the same configuration key specified more than once
              -- with different values makes the suite ill-formed.
              configPairs = [(k, v) | (_, _, SConfigKey k v) <- scanned]
              configConflict =
                listToMaybe
                  [ k
                  | k <- dedup (map fst configPairs)
                  , length (dedup [v | (k', v) <- configPairs, k' == k]) > 1
                  ]
              -- §4.2: package mode defaults all unsafe/debug settings to
              -- false; script mode MAY default them to true (this
              -- implementation does). Explicit allow_* directives then
              -- layer on top of that base.
              unsafeBase = if scripted then scriptUnsafeConfig else defaultUnsafeConfig
              unsafeCfg = foldl' (\c f -> f c) unsafeBase [f | (_, _, SUnsafeConfig f) <- scanned]
          -- §T.4: a stdinFile path must name a readable suite-relative
          -- file (§T.8: an unreadable required file is a harness error).
          missingStdin <- filterM (fmap not . doesFileExist . (root </>) . T.unpack) stdinFiles
          case () of
            _ | Just k <- configConflict ->
                  pure (TestReport label HarnessError ("configuration key '" <> k <> "' is specified more than once with conflicting values; the suite is ill-formed (§T.6)"))
              | length (dedup modes) > 1 ->
                  pure (TestReport label HarnessError "conflicting 'mode' directives (§T.6)")
              | (p : _) <- missingStdin ->
                  pure (TestReport label HarnessError ("stdinFile '" <> p <> "' is not a readable suite file (§T.4, §T.8)"))
              -- a 'requires capability stageDumps' gate (an SUnsupported)
              -- is honored first, so a *gated* assertStageDump is
              -- unsupported; an *un-gated* one names a checkpoint this
              -- implementation cannot serve and is ill-formed (§T.5.3).
              | not (null unsups) ->
                  pure (TestReport label Unsupported (head unsups))
              | (c : _) <- stageDumps ->
                  pure (TestReport label HarnessError ("assertStageDump names checkpoint '" <> c <> "', which this implementation does not provide; gate with 'requires capability stageDumps' for an unsupported result (§T.5.3, §T.8)"))
              | otherwise -> do
                  let mode = case modes of m : _ -> m; [] -> "check"
                  -- §T.4: 'backend <profile>' selects the backend for
                  -- 'compile' and 'run' tests; a foreign profile makes
                  -- those tests unsupported, while a default-mode
                  -- 'check' test is unaffected by backend selection
                  if not (null backends) && mode `elem` ["compile", "run"]
                    then pure (TestReport label Unsupported ("backend " <> head backends <> " is not provided"))
                    else
                      if not (null entries) && mode /= "run"
                        then pure (TestReport label HarnessError "'entry' is valid only for mode run (§T.4)")
                        else executeSuite unsafeCfg (packageMode && not scripted) label root files mode entries asserts preDiags
  where
    dedup = foldr (\x xs -> if x `elem` xs then xs else x : xs) []

data RunInfo = RunInfo
  { riStdout :: !Text
  , riStderr :: !Text
  , riExitCode :: !Int
  }

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
      filePaths = map fst files
      allDiags = preDiags ++ cuDiags cu
      preludeErrs = [d | d <- allDiags, isError d, spanFile (dPrimary d) `notElem` filePaths]
      diags = [d | d <- allDiags, spanFile (dPrimary d) `elem` filePaths]
  if not (null preludeErrs)
    then pure (TestReport label HarnessError "prelude failed to compile (implementation bug)")
    else do
      mRun <-
        if mode == "run"
          then Just <$> doRun cu diags
          else pure Nothing
      results <- mapM (\(p, s, a) -> checkAssertion compileWith root p s files cu diags mRun a) asserts
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

checkAssertion ::
  ([(FilePath, Text)] -> CompiledUnit) ->
  FilePath -> FilePath -> Text -> [(FilePath, Text)] -> CompiledUnit ->
  Diagnostics -> Maybe RunInfo -> Assertion -> IO AssertResult
checkAssertion compileWith root path src files cu diags mRun = \case
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
      (any (\d -> dSeverity d == toSeverity sev && diagHasCode code d) diags)
      ("no diagnostic " <> describe sev code <> " was produced" <> sawCodes)
  ADiagNext sev code line ->
    require
      ( any
          ( \d ->
              dSeverity d == toSeverity sev
                && diagHasCode code d
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
                && diagHasCode code d
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
                && diagHasCode code d
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
                fps = map fst files'
                ds' = [d | d <- cuDiags cu', spanFile (dPrimary d) `elem` fps]
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
  where
    errors = filter isError diags
    warnings = filter (\d -> dSeverity d == SevWarning) diags
    require b detail = pure (if b then AssertOk else AssertFail detail)
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
-- scope) and compare with the declaration's recorded type up to
-- definitional equality ('convertible').
--
-- If the expected type does not parse or does not elaborate in this
-- implementation, the assertion cannot be satisfied and the test
-- *fails* (with a precise reason); the directive itself is well-formed,
-- so this is not a harness error (§T.8).
assertType :: FilePath -> Text -> CompiledUnit -> Text -> Text -> AssertResult
assertType path src cu nm tyExpr =
  case lookupTarget of
    Nothing -> AssertFail ("name '" <> nm <> "' does not resolve to a typed declaration")
    Just gd ->
      case elabExpected of
        Left err -> AssertFail err
        Right (st', probeTy) ->
          let ec = EvalCtx (Globals (csGlobals st')) (csMetas st') False mempty
              actualR = renderTerm (quote ec 0 (gdType gd))
              probeR = renderTerm (quote ec 0 probeTy)
           in if convertible ec 0 (gdType gd) probeTy
                -- distinct unsolved metas in equal positions (e.g. the
                -- inferred error parameter of a one-argument 'IO a'
                -- assertion) still count as the same expected type
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
       in case mapMaybe (`Map.lookup` csGlobals st) candidates of
            (gd : _) -> Just gd
            [] -> Nothing
    probeName = "__assert_type_probe"
    -- The probe sees the same unqualified scope as the origin file:
    -- prelude plus that file's imports over the accumulated state.
    probeScope = case originParse of
      Right (m, _) -> importScopeFor st m
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
                  Just probe -> Right (st1, gdType probe)
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
          let BinderPrefix mq mb = bPrefix b
              qt = case mq of
                Nothing -> ""
                Just QZero -> "0"
                Just QOne -> "1"
                Just QOmega -> "ω"
                Just QAtMostOne -> "<=1"
                Just QAtLeastOne -> ">=1"
                Just (QTerm n) -> nameText n
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
      DoVar n _ _ -> "var " <> nameText n
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
    prefixedHead (BinderPrefix mq mb) p =
      let qt = case mq of
            Nothing -> ""
            Just QZero -> "0"
            Just QOne -> "1"
            Just QOmega -> "ω"
            Just QAtMostOne -> "<=1"
            Just QAtLeastOne -> ">=1"
            Just (QTerm n) -> nameText n
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
      -- descending by start offset, so splices keep earlier indices valid
      let ordered = reverse (sortOn (\((s, _), _) -> s) spans)
      pure (foldl' splice src ordered)
    splice s ((a, b), repl) = T.take a s <> repl <> T.drop b s
    -- 1-based (line, col) span → (startOffset, endOffset) char indices.
    offsetsOf src sp =
      let Pos sl sc = spanStart sp
          Pos el ec = spanEnd sp
       in (,) <$> offsetOf src sl sc <*> offsetOf src el ec
    offsetOf src ln col =
      let ls = T.splitOn "\n" src
       in if ln >= 1 && ln <= length ls
            then Right (sum (map ((+ 1) . T.length) (take (ln - 1) ls)) + (col - 1))
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
collectKp dir = do
  entries <- sort <$> listDirectory dir
  let paths = [dir </> e | e <- entries]
  dirs <- filterM doesDirectoryExist paths
  let files = [p | p <- paths, ".kp" `isSuffixOf` p, p `notElem` dirs]
  rest <- concat <$> mapM collectKp dirs
  pure (files ++ rest)

tshow :: Show a => a -> Text
tshow = T.pack . show
