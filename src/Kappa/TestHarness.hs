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
import Data.List (isSuffixOf, sort)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Encoding.Error as TEE
import qualified Data.ByteString as BS
import qualified Data.Map.Strict as Map
import Kappa.Check (CheckState (..), checkModule)
import Kappa.Core
import Kappa.Diagnostic
import Kappa.Eval (EvalCtx (..), GlobalDef (..), Globals (..), convertible, force, quote)
import Kappa.Explain (codeNames, explainExists)
import Kappa.Interp (RunResult (..), runMainCapturedValue)
import Kappa.Parser (parseModule)
import Kappa.Pipeline (CompiledUnit (..), compileFiles, compileFilesIn, importScopeFor)
import Kappa.Pretty (renderTerm)
import Kappa.Regex (Regex, compileRegex, regexSearch)
import Kappa.Resolve (FixityEnv, defaultFixities, fixitiesOf, resolveModule)
import Kappa.Source (ModuleName (..), Pos (..), Span (..))
import Kappa.Syntax
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
  | AExplainExists !Text -- ^ §3.1.2A registry lookup, code or family
  | AErrorCodes ![Text] -- ^ x-compatible: exact multiset of error codes
  | AEval !Text !Text -- ^ x-compatible: evaluate a global, compare rendering
  | AEvalError !Text !Text -- ^ x-compatible: evaluation fails, message contains
  | ADeclDescriptors ![Text] -- ^ x-compatible: decl kind+name descriptors
  | ATraitMembers !Text ![Text] -- ^ x-compatible: trait member names in order
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

-- One scanned directive, already classified.
data Scanned
  = SMode !Text
  | SEntry !Text
  | SConfigNoop -- ^ accepted configuration with no harness effect
  | SUnsupported !Text -- ^ §T.8 unsupported (requires unmet, x- extension, …)
  | SAssert !Assertion

-- ── Directive scanning (§T.3) ────────────────────────────────────────

declKindNames :: [Text]
declKindNames =
  [ "import", "export", "fixity", "signature", "let", "data", "type"
  , "trait", "instance", "derive", "effect", "pattern", "expect"
  ]

-- Standard directives whose subject matter this implementation does not
-- produce at all: structured-diagnostic payloads, labels, related
-- origins, fix-its, suppression summaries, and Chapter 34 stage dumps.
-- Diagnostic records here carry none of those fields, so the assertions
-- could never be satisfied; the test exercises an unsupported feature
-- and is classified unsupported (§T.8) rather than failed. Documented
-- in TESTING.md.
structuredUnsupported :: [Text]
structuredUnsupported =
  [ "assertDiagnosticPayload"
  , "assertDiagnosticLabel"
  , "assertDiagnosticRelated"
  , "assertDiagnosticFix"
  , "assertDiagnosticFixCount"
  , "assertDiagnosticFixCompiles"
  , "assertSuppressedDiagnostic"
  , "assertStageDump"
  ]

-- §T.4 portable capabilities this harness provides. @runTask@: programs
-- are executed in-process by the tree-walking interpreter. @
-- pipelineTrace@: portable (event, subject) counts are recorded for
-- parse\/buildKFrontIR\/lowerKCore. Not provided: @stageDumps@ (no
-- Chapter 34 checkpoint serialization) and @incremental@ (no session
-- state survives between suite roots).
supportedCapabilities :: [Text]
supportedCapabilities = ["runTask", "pipelineTrace"]

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
      -- same-line counterpart of assertDiagnosticNext (§T.5.1)
      ([SAssert (ADiagNext (sevOfCode c) c lno) | c <- codes], [])
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

    dispatch name args = case name of
      "mode" -> case args of
        ["check"] -> ok (SMode "check")
        ["run"] -> ok (SMode "run")
        ["analyze"] -> unsup "mode analyze is not supported"
        ["compile"] -> unsup "mode compile is not supported (no backends)"
        _ -> bad "malformed 'mode' directive"
      "packageMode" -> ok SConfigNoop -- the default (§T.4)
      "scriptMode" -> unsup "scriptMode is not supported"
      "backend" -> case args of
        ["interpreter"] -> ok SConfigNoop -- the only provided profile
        [p] -> unsup ("backend " <> p <> " is not provided")
        _ -> bad "malformed 'backend' directive"
      "entry" -> case args of
        [q] -> ok (SEntry q)
        _ -> bad "malformed 'entry' directive"
      "runArgs" -> unsup "runArgs is not supported"
      "stdinFile" -> unsup "stdinFile is not supported"
      "dumpFormat" -> case args of
        ["json"] -> ok SConfigNoop
        ["sexpr"] -> ok SConfigNoop
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
      "assertDiagnosticMatch"
        | T.null rest -> bad "malformed 'assertDiagnosticMatch' directive (empty pattern)"
        | otherwise -> case compileRegex rest of
            Right re -> ok (SAssert (ADiagMatch rest re))
            Left err -> bad ("invalid 'assertDiagnosticMatch' pattern: " <> err)
      "assertDiagnosticExplainExists" -> case args of
        [cf] -> ok (SAssert (AExplainExists cf))
        _ -> bad "malformed 'assertDiagnosticExplainExists' directive"
      "assertDiagnosticAt" -> case args of
        [p, sevT, code, lnT]
          | Just sev <- parseSev sevT, Just n <- parseNat lnT ->
              ok (SAssert (ADiagAt p sev code n Nothing))
        [p, sevT, code, lnT, colT]
          | Just sev <- parseSev sevT, Just n <- parseNat lnT, Just c <- parseNat colT ->
              ok (SAssert (ADiagAt p sev code n (Just c)))
        [p, sevT, code, slT, scT, "-", elT, ecT]
          | Just sev <- parseSev sevT
          , Just sl <- parseNat slT, Just sc <- parseNat scT
          , Just el <- parseNat elT, Just ec <- parseNat ecT ->
              ok (SAssert (ADiagAtRange p sev code sl sc el ec))
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
         in if not (null codes) && all (not . T.null) codes
              then ok (SAssert (AErrorCodes codes))
              else bad "malformed 'assertDiagnosticCodes' code list"
      "assertEval" -> evalAssert
      -- supported x- extension directives (§T.3 allows a harness to
      -- implement extension directives; unsupported ones classify the
      -- test unsupported below)
      "x-assertEval" -> evalAssert
      "x-assertEvalErrorContains" -> case T.words rest of
        (nm : more) | not (null more) -> ok (SAssert (AEvalError nm (T.unwords more)))
        _ -> bad "malformed 'x-assertEvalErrorContains' directive"
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
        | name `elem` structuredUnsupported ->
            unsup ("directive '" <> name <> "' asserts structured-diagnostic/stage-dump data this implementation does not produce")
        | otherwise ->
            -- §T.3: any unknown non-extension directive is a harness
            -- error (this covers other implementations' private
            -- directives, which are not part of Appendix T)
            bad ("unknown directive '" <> name <> "' is not defined by Appendix T (§T.3)")
      where
        evalAssert = case T.words rest of
          (nm : more) | not (null more) -> ok (SAssert (AEval nm (T.unwords more)))
          _ -> bad ("malformed '" <> name <> "' directive")
        noArgs a
          | null args = ok (SAssert a)
          | otherwise = bad ("directive '" <> name <> "' takes no arguments")
        withCount f = case args of
          [nT] | Just n <- parseNat nT -> ok (SAssert (f n))
          _ -> bad ("malformed '" <> name <> "' directive")
        withSevCode f = case args of
          [sevT, code] | Just sev <- parseSev sevT -> ok (SAssert (f sev code))
          _ -> bad ("malformed '" <> name <> "' directive")
        nextAssert = case args of
          [sevT, code]
            | Just sev <- parseSev sevT ->
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

parseNat :: Text -> Maybe Int
parseNat t
  | not (T.null t) && T.all isDigit t = Just (read (T.unpack t))
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

-- ── Test execution ───────────────────────────────────────────────────

readSourceFile :: FilePath -> IO Text
readSourceFile path = do
  bytes <- BS.readFile path
  pure (TE.decodeUtf8With TEE.lenientDecode bytes)

-- | Run one @.kp@ test file (§T.2 single-file inline test). The suite
-- root for relative paths is the containing directory (§T.2).
runTestFile :: FilePath -> IO TestReport
runTestFile path = guardExceptions path $ do
  src <- readSourceFile path
  runSuiteWith False path (takeDirectory path) [(path, src)] Nothing

-- | Run a §T.2 directory suite: all @.kp@ files under the root compiled
-- together, directives gathered from @suite.ktest@ plus every file.
runSuiteDir :: FilePath -> IO TestReport
runSuiteDir dir = guardExceptions dir $ do
  files <- collectKp dir
  srcs <- mapM readSourceFile files
  let ktestPath = dir </> "suite.ktest"
  hasKtest <- doesFileExist ktestPath
  mktest <-
    if hasKtest
      then Just . (,) ktestPath <$> readSourceFile ktestPath
      else pure Nothing
  runSuite dir dir (orderByImports (zip files srcs)) mktest

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
runSuite :: FilePath -> FilePath -> [(FilePath, Text)] -> Maybe (FilePath, Text) -> IO TestReport
runSuite = runSuiteWith True

-- single-file tests are script-mode (§8.1 package path rules off)
runSuiteWith :: Bool -> FilePath -> FilePath -> [(FilePath, Text)] -> Maybe (FilePath, Text) -> IO TestReport
runSuiteWith packageMode label root files mktest = do
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
              asserts = [(p, src, a) | (p, src, SAssert a) <- scanned]
          case () of
            _ | length (dedup modes) > 1 ->
                  pure (TestReport label HarnessError "conflicting 'mode' directives (§T.6)")
              | not (null unsups) ->
                  pure (TestReport label Unsupported (head unsups))
              | otherwise -> do
                  let mode = case modes of m : _ -> m; [] -> "check"
                  if not (null entries) && mode /= "run"
                    then pure (TestReport label HarnessError "'entry' is valid only for mode run (§T.4)")
                    else executeSuite packageMode label root files mode entries asserts
  where
    dedup = foldr (\x xs -> if x `elem` xs then xs else x : xs) []

data RunInfo = RunInfo
  { riStdout :: !Text
  , riStderr :: !Text
  , riExitCode :: !Int
  }

executeSuite ::
  Bool -> FilePath -> FilePath -> [(FilePath, Text)] -> Text -> [Text] ->
  [(FilePath, Text, Assertion)] -> IO TestReport
executeSuite packageMode label root files mode entries asserts = do
  -- the suite root is the §8.1 source root for module-path derivation
  let cu =
        if packageMode
          then compileFilesIn root files
          else compileFiles files
      filePaths = map fst files
      allDiags = cuDiags cu
      preludeErrs = [d | d <- allDiags, isError d, spanFile (dPrimary d) `notElem` filePaths]
      diags = [d | d <- allDiags, spanFile (dPrimary d) `elem` filePaths]
  if not (null preludeErrs)
    then pure (TestReport label HarnessError "prelude failed to compile (implementation bug)")
    else do
      mRun <-
        if mode == "run"
          then Just <$> doRun cu diags
          else pure Nothing
      results <- mapM (\(p, s, a) -> checkAssertion root p s files cu diags mRun a) asserts
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
                  let ec = EvalCtx (Globals (csGlobals st)) (csMetas st) True
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
  FilePath -> FilePath -> Text -> [(FilePath, Text)] -> CompiledUnit ->
  Diagnostics -> Maybe RunInfo -> Assertion -> IO AssertResult
checkAssertion root path src files cu diags mRun = \case
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
    mr <- timeout runTimeoutMicros (evaluate (forceResult (assertEval cu nm expected)))
    pure (fromMaybe (AssertFail ("assertEval: evaluation of '" <> nm <> "' timed out")) mr)
  AEvalError nm sub -> do
    mr <- timeout runTimeoutMicros (evaluate (forceResult (assertEvalError cu nm sub)))
    pure (fromMaybe (AssertFail ("assertEvalErrorContains: evaluation of '" <> nm <> "' timed out")) mr)
  ADeclDescriptors entries -> pure (assertDeclDescriptors path src entries)
  ATraitMembers tn ms -> pure (assertTraitMembers path src tn ms)
  AType nm tyExpr -> pure (assertType path src cu nm tyExpr)
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
-- required portable alias (an implementation may expose either).
diagHasCode :: Text -> Diagnostic -> Bool
diagHasCode code d = code `elem` codeNames (dCode d)

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
assertEval :: CompiledUnit -> Text -> Text -> AssertResult
assertEval cu nm expected =
  case entryGlobal cu nm >>= \g -> Map.lookup g (csGlobals (cuState cu)) of
    Nothing -> AssertFail ("assertEval: '" <> nm <> "' is not a defined global")
    Just gd -> case gdValue gd of
      Nothing -> AssertFail ("assertEval: '" <> nm <> "' has no value (signature only)")
      Just v ->
        let st = cuState cu
            ec = EvalCtx (Globals (csGlobals st)) (csMetas st) True
            rendered = renderEvalValue ec v
         in if rendered == T.strip expected
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
assertEvalError :: CompiledUnit -> Text -> Text -> AssertResult
assertEvalError cu nm sub =
  case entryGlobal cu nm >>= \g -> Map.lookup g (csGlobals (cuState cu)) of
    Nothing -> AssertFail ("assertEvalErrorContains: '" <> nm <> "' is not a defined global")
    Just gd -> case gdValue gd of
      Nothing -> AssertFail ("assertEvalErrorContains: '" <> nm <> "' has no value (signature only)")
      Just v ->
        let st = cuState cu
            ec = EvalCtx (Globals (csGlobals st)) (csMetas st) True
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
          VPrim "failNow" (a : _)
            | VLit (LitStr m) <- force ec a -> Just m
          VPrim p [_, b]
            | p == "divInt" || p == "modInt"
            , VLit (LitInt 0) <- force ec b ->
                Just "Division by zero"
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
renderEvalValue ec = go (32 :: Int) False
  where
    go :: Int -> Bool -> Value -> Text
    go 0 _ _ = "…"
    go fuel nested v = case force ec v of
      VLit (LitInt n) -> tshow n
      VLit (LitDouble d) -> tshow d
      VLit (LitStr s) -> tshow s
      VLit (LitScalar c) -> tshow c
      VCtor (GName _ "Unit") [] -> "()"
      VRecordV [] -> "()"
      VCtor g [] -> gnameText g
      -- list cells render infix and unparenthesized: 1 :: 2 :: Nil
      VCtor (GName _ "::") [h, t] ->
        go (fuel - 1) True h <> " :: " <> go (fuel - 1) False t
      VCtor g args ->
        parenIf nested (T.unwords (gnameText g : map (go (fuel - 1) True) args))
      VRecordV fs ->
        "(" <> T.intercalate ", " [n <> " = " <> go (fuel - 1) False x | (n, x) <- fs] <> ")"
      VInject _ x -> go (fuel - 1) nested x
      other -> renderTerm (quote ec 0 other)
    parenIf b t = if b then "(" <> t <> ")" else t

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
          let ec = EvalCtx (Globals (csGlobals st')) (csMetas st') False
           in if convertible ec 0 (gdType gd) probeTy
                then AssertOk
                else
                  AssertFail
                    ( "type of '" <> nm <> "' is "
                        <> renderTerm (quote ec 0 (gdType gd))
                        <> ", expected "
                        <> renderTerm (quote ec 0 probeTy)
                    )
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
              st0 = st {csModule = originMod, csScope = probeScope, csDiags = []}
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
  where
    nameSuffix = maybe "" (\n -> " " <> nameText n)
    modsPrefix mods = vis <> opq
      where
        vis = case dmVisibility mods of
          VisPublic -> "public "
          VisPrivate -> "private "
          VisDefault -> ""
        opq = if dmOpaque mods then "opaque " else ""
    fixityWord = \case
      InfixN -> "infix"
      InfixL -> "infix left"
      InfixR -> "infix right"
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

-- ── Tree walking ─────────────────────────────────────────────────────

-- | Run a path: a @.kp@ file is a single-file inline test; a directory
-- containing @step0@ or @incremental.ktest@ is one incremental step
-- suite (§T.7); a directory containing @suite.ktest@ or @main.kp@ is
-- one directory suite (§T.2), as is a directory given directly as the
-- argument that contains @.kp@ files; any other directory recurses.
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
