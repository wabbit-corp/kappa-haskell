-- | Appendix T standard test harness.
--
-- Implements the §T.3 directive syntax, the §T.4 configuration subset
-- (@mode check@\/@mode run@), the §T.5.1 diagnostic assertions, §T.5.2
-- type\/shape assertions and §T.5.4 run assertions, with §T.8 result
-- classification (pass \/ fail \/ unsupported \/ harnessError).
--
-- Two §T.2 test forms are supported: single-file inline tests, and
-- directory suites (a directory containing @suite.ktest@ and\/or
-- @main.kp@ is one suite; all its @.kp@ files are compiled together).
-- Other directory arguments recurse over @**/*.kp@. See TESTING.md for
-- the supported subset and deliberate approximations.
module Kappa.TestHarness
  ( Outcome (..)
  , TestReport (..)
  , Summary (..)
  , runTestFile
  , runTestPath
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
import Kappa.Interp (RunResult (..), runMainCaptured)
import Kappa.Parser (parseModule)
import Kappa.Pipeline (CompiledUnit (..), compileFiles, compileSourceWithPrelude)
import Kappa.Pretty (renderTerm)
import Kappa.Resolve (FixityEnv, defaultFixities, fixitiesOf, resolveModule)
import Kappa.Source (ModuleName (..), Pos (..), Span (..))
import Kappa.Syntax
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory)
import System.FilePath ((</>))
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
  | ADiagFamily !Sev !Text
  | AErrorCodes ![Text] -- ^ x-compatible: exact multiset of error codes
  | AEval !Text !Text -- ^ x-compatible: evaluate a global, compare rendering
  | AType !Text !Text
  | ADeclKinds ![Text]
  | AStdout !Text
  | AStdoutContains !Text
  | AStderrContains !Text
  | AExitCode !Int

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

-- Standard directives we recognize but do not implement: per TESTING.md
-- these classify the test as unsupported rather than failing it.
unimplementedDirectives :: [Text]
unimplementedDirectives =
  [ "assertDiagnosticAt" -- only the range form; handled separately
  , "assertDiagnosticMatch"
  , "assertDiagnosticPayload"
  , "assertDiagnosticLabel"
  , "assertDiagnosticRelated"
  , "assertDiagnosticFix"
  , "assertDiagnosticFixCount"
  , "assertDiagnosticFixCompiles"
  , "assertDiagnosticExplainExists"
  , "assertSuppressedDiagnostic"
  , "assertStdoutFile"
  , "assertStderrFile"
  , "assertStageDump"
  , "assertTraceCount"
  , "assertFileDeclKinds"
  ]

-- Non-standard directives used by another implementation's fixture
-- corpus (not in Appendix T). They are treated like x- extensions:
-- the test is classified unsupported, not a harness error.
foreignDirectives :: [Text]
foreignDirectives =
  [ "assertRunStdout"
  , "assertExecute"
  , "assertEvalErrorContains"
  , "assertParameterQuantities"
  , "assertDoItemDescriptors"
  , "assertInoutParameters"
  , "assertContainsTokenTexts"
  , "allow_unsafe_consume"
  ]

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
      "backend" -> unsup "backend profiles are not supported"
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
        ("backend" : _) -> unsup "requires backend: no backends"
        ("capability" : c) -> unsup ("requires capability " <> T.unwords c <> ": not provided")
        _ -> bad "malformed 'requires' directive"
      "assertNoErrors" -> noArgs ANoErrors
      "assertNoWarnings" -> noArgs ANoWarnings
      "assertErrorCount" -> withCount AErrorCount
      "assertWarningCount" -> withCount AWarningCount
      "assertDiagnostic" -> withSevCode ADiag
      "assertDiagnosticNext" -> nextAssert
      "assertDiagnosticHere" -> nextAssert -- deprecated alias (§T.5.1)
      "assertDiagnosticFamily" -> withSevCode ADiagFamily
      "assertDiagnosticAt"
        | "-" `elem` args -> unsup "assertDiagnosticAt range form is not supported"
        | otherwise -> case args of
            [p, sevT, code, lnT]
              | Just sev <- parseSev sevT, Just n <- parseNat lnT ->
                  ok (SAssert (ADiagAt p sev code n Nothing))
            [p, sevT, code, lnT, colT]
              | Just sev <- parseSev sevT, Just n <- parseNat lnT, Just c <- parseNat colT ->
                  ok (SAssert (ADiagAt p sev code n (Just c)))
            _ -> bad "malformed 'assertDiagnosticAt' directive"
      "assertType" -> case args of
        (nm : tyToks) | not (null tyToks) -> ok (SAssert (AType nm (T.unwords tyToks)))
        _ -> bad "malformed 'assertType' directive"
      "assertDeclKinds" ->
        let kinds = map T.strip (T.splitOn "," rest)
         in if not (null kinds) && all (`elem` declKindNames) kinds && all (not . T.null) kinds
              then ok (SAssert (ADeclKinds kinds))
              else bad "malformed 'assertDeclKinds' kind list"
      "assertStdout" -> withString AStdout
      "assertStdoutContains" -> withString AStdoutContains
      "assertStderrContains" -> withString AStderrContains
      "assertExitCode" -> withCount AExitCode
      -- compatibility extensions for the external fixture corpus
      "assertDiagnosticCodes" ->
        let codes = map T.strip (T.splitOn "," rest)
         in if not (null codes) && all (not . T.null) codes
              then ok (SAssert (AErrorCodes codes))
              else bad "malformed 'assertDiagnosticCodes' code list"
      "assertEval" -> case T.words rest of
        (nm : more) | not (null more) -> ok (SAssert (AEval nm (T.unwords more)))
        _ -> bad "malformed 'assertEval' directive"
      _
        | "x-" `T.isPrefixOf` name ->
            unsup ("extension directive '" <> name <> "' is not supported")
        | name `elem` unimplementedDirectives ->
            unsup ("directive '" <> name <> "' is not implemented by this harness")
        | name `elem` foreignDirectives ->
            unsup ("non-standard directive '" <> name <> "' is not supported")
        | otherwise -> bad ("unknown standard directive '" <> name <> "'")
      where
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

-- | Run one @.kp@ test file (§T.2 single-file inline test).
runTestFile :: FilePath -> IO TestReport
runTestFile path = guardExceptions path $ do
  src <- readSourceFile path
  runSuite path [(path, src)] Nothing

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
  runSuite dir (orderByImports (zip files srcs)) mktest

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
runSuite :: FilePath -> [(FilePath, Text)] -> Maybe (FilePath, Text) -> IO TestReport
runSuite label files mktest = do
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
                    else executeSuite label files mode entries asserts
  where
    dedup = foldr (\x xs -> if x `elem` xs then xs else x : xs) []

data RunInfo = RunInfo
  { riStdout :: !Text
  , riStderr :: !Text
  , riExitCode :: !Int
  }

executeSuite ::
  FilePath -> [(FilePath, Text)] -> Text -> [Text] -> [(FilePath, Text, Assertion)] -> IO TestReport
executeSuite label files mode entries asserts = do
  let cu = case files of
        [(p, s)] -> compileSourceWithPrelude p s
        _ -> compileFiles files
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
      results <- mapM (\(p, s, a) -> checkAssertion p s cu diags mRun a) asserts
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
                  runMainCaptured (Globals (csGlobals st)) (csMetas st) mainG
              case mres of
                Nothing -> pure (RunInfo "" "error: test timed out" 1)
                Just (RunOk, out) -> pure (RunInfo out "" 0)
                Just (RunFail msg, out) ->
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
  FilePath -> Text -> CompiledUnit -> Diagnostics -> Maybe RunInfo -> Assertion -> IO AssertResult
checkAssertion path src cu diags mRun = \case
  ANoErrors ->
    countIs "errors" 0 (length errors)
  ANoWarnings ->
    countIs "warnings" 0 (length warnings)
  AErrorCount n ->
    countIs "errors" n (length errors)
  AWarningCount n ->
    countIs "warnings" n (length warnings)
  ADiag sev code ->
    require
      (any (\d -> dSeverity d == toSeverity sev && dCode d == code) diags)
      ("no diagnostic " <> describe sev code <> " was produced" <> sawCodes)
  ADiagNext sev code line ->
    require
      ( any
          ( \d ->
              dSeverity d == toSeverity sev
                && dCode d == code
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
                && dCode d == code
                && T.pack (spanFile (dPrimary d)) `endsWithPath` p
                && posLine (spanStart (dPrimary d)) == line
                && maybe True (== posCol (spanStart (dPrimary d))) mcol
          )
          diags
      )
      ("no diagnostic " <> describe sev code <> " at " <> p <> ":" <> tshow line)
  ADiagFamily sev fam ->
    require
      (any (\d -> dSeverity d == toSeverity sev && dFamily d == Just fam) diags)
      ("no diagnostic with family " <> fam <> " was produced")
  AErrorCodes codes ->
    let actual = sort (map dCode errors)
     in require
          (actual == sort codes)
          ( "error codes are [" <> T.intercalate ", " (map dCode errors)
              <> "], expected [" <> T.intercalate ", " codes <> "]"
          )
  AEval nm expected -> do
    -- evaluation may legitimately be deep; guard with the run timeout
    mr <- timeout runTimeoutMicros (evaluate (forceResult (assertEval cu nm expected)))
    pure (fromMaybe (AssertFail ("assertEval: evaluation of '" <> nm <> "' timed out")) mr)
  AType nm tyExpr -> pure (assertType path src cu nm tyExpr)
  ADeclKinds kinds -> pure (assertDeclKinds path src kinds)
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
  AExitCode n -> withRun $ \ri ->
    require
      (riExitCode ri == n)
      ("exit code was " <> tshow (riExitCode ri) <> ", expected " <> tshow n)
  where
    errors = filter isError diags
    warnings = filter (\d -> dSeverity d == SevWarning) diags
    require b detail = pure (if b then AssertOk else AssertFail detail)
    countIs what n actual =
      require (actual == n) ("expected " <> tshow n <> " " <> what <> ", got " <> tshow actual)
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
    withRun k = case mRun of
      Just ri -> k ri
      Nothing -> pure (AssertHarnessError "run assertion outside mode run (§T.5.4)")
    endsWithPath actual rel = actual == rel || ("/" <> rel) `T.isSuffixOf` actual

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
-- and compare with the declaration's recorded type up to definitional
-- equality ('convertible').
assertType :: FilePath -> Text -> CompiledUnit -> Text -> Text -> AssertResult
assertType path src cu nm tyExpr =
  case lookupTarget of
    Nothing -> AssertFail ("name '" <> nm <> "' does not resolve to a typed declaration")
    Just gd ->
      case elabExpected of
        Left err -> AssertHarnessError err
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
    -- the assertion is file-relative: resolve in the origin file's module
    originMod = case parseModule path src of
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
    elabExpected =
      case parseModule "<assertType>" (probeName <> " : " <> tyExpr <> "\n") of
        Left _ -> Left ("assertType: expected type does not parse: " <> tyExpr)
        Right (m, _) ->
          let fixities = fileFixities path src
              (m', _) = resolveModule fixities m
              st0 = st {csModule = originMod, csDiags = []}
              (st1, ds) = checkModule st0 m'
           in if hasErrors ds
                then Left ("assertType: expected type is ill-formed: " <> tyExpr)
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

-- | @assertDeclKinds@ (§T.5.2): compare top-level declaration kinds in
-- source order (module header excluded).
assertDeclKinds :: FilePath -> Text -> [Text] -> AssertResult
assertDeclKinds path src expected =
  case parseModule path src of
    Left _ -> AssertFail "assertDeclKinds: file does not parse"
    Right (m, _) ->
      let actual = map declKind (modDecls m)
       in if actual == expected
            then AssertOk
            else
              AssertFail
                ( "decl kinds are [" <> T.intercalate ", " actual
                    <> "], expected [" <> T.intercalate ", " expected <> "]"
                )

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
-- containing @suite.ktest@ or @main.kp@ is one directory suite (§T.2),
-- as is a directory given directly as the argument that contains @.kp@
-- files; any other directory recurses. Prints one result line per test.
runTestPath :: FilePath -> IO [TestReport]
runTestPath = runTestPathAt True

runTestPathAt :: Bool -> FilePath -> IO [TestReport]
runTestPathAt topLevel root = do
  isDir <- doesDirectoryExist root
  if not isDir
    then emitOne (runTestFile root)
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
    emitOne act = do
      rep <- act
      putStrLn (T.unpack (reportLine rep))
      pure [rep]

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
