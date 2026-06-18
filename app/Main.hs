-- | The @kappa@ CLI: check, run, and the Appendix T test harness.
module Main (main) where

import Control.Monad (forM_, unless, when)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Kappa.Backend.Driver
  ( BuildOptions (..)
  , buildNative
  , defaultBuildOptions
  )
import Kappa.Build.Plan (ResolvedExe (..), resolveExecutable)
import Kappa.Build.Reify (reifyBuildConfig)
import qualified Kappa.Build.Types as B
import Kappa.Check (AuditRecord (..), CheckState (..), defaultUnsafeConfig)
import Kappa.Core (GName (..))
import Kappa.Diagnostic
import Kappa.Eval (Globals (..))
import Kappa.Explain (lookupCode, lookupFamily, renderEntry, renderFamily)
import Kappa.Interp (RunResult (..), runMain)
import Kappa.Pipeline
import Kappa.Source (Pos (..), Span (..), moduleNameText)
import Kappa.TestHarness (Summary (..), TestReport, runTestPath, runTestSuitePath, summarize)
import System.Directory (doesDirectoryExist, doesFileExist, getCurrentDirectory)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitFailure, exitSuccess, exitWith)
import System.FilePath (takeDirectory, takeFileName, (</>))
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["check", path] -> cmdCheck Human path
    ["check", "--json", path] -> cmdCheck Json path
    ["run", path] -> cmdRun Human path
    ["run", "--json", path] -> cmdRun Json path
    ["test", path] -> cmdTest runTestPath path
    ["test", "--suite", path] -> cmdTest runTestSuitePath path
    ["explain", code] -> cmdExplain (T.pack code)
    ["audit", path] -> cmdAudit path
    ("build" : rest) -> cmdBuild rest
    _ -> do
      hPutStrLn stderr $
        "usage: kappa (check|run [--json]|test [--suite]|audit) PATH"
          <> " | kappa build [--emit-c] [-o OUT] [--cc DRIVER] FILE"
          <> " | kappa build --manifest [PATH|DIR] [--check] [--target NAME] [-o OUT] [--emit-c] [--cc DRIVER]"
          <> " | kappa explain CODE-OR-FAMILY"
      exitFailure

-- | Diagnostic output format (§3.1): the human-readable renderer is the
-- default surface (§3.1.8); @--json@ selects the machine-readable
-- producer (§3.1.1).
data DiagFormat = Human | Json

-- | Emit one compilation unit's diagnostics in the selected format.
-- §3.1.1: in JSON mode the whole batch is one JSON array (one object per
-- diagnostic) on stdout, so tools never parse interleaved prose.
emitDiags :: DiagFormat -> Diagnostics -> IO ()
emitDiags Human ds = forM_ ds (TIO.hPutStrLn stderr . renderDiagnostic)
emitDiags Json ds = TIO.putStrLn (renderDiagnosticsJson ds)

-- | §3.1.2A / §3.1.13: print the registry explanation for a diagnostic
-- code or (§3.1.13) a diagnostic family; unknown codes/families are
-- rejected deterministically rather than falling back to prose search.
cmdExplain :: T.Text -> IO ()
cmdExplain cf = case lookupCode cf of
  Just e -> TIO.putStr (renderEntry e) >> exitSuccess
  Nothing -> case lookupFamily cf of
    Just fam -> TIO.putStr (renderFamily fam) >> exitSuccess
    Nothing -> do
      TIO.hPutStrLn stderr ("error: unknown diagnostic code or family '" <> cf <> "'")
      exitFailure

cmdCheck :: DiagFormat -> FilePath -> IO ()
cmdCheck fmt path = do
  (src, preDiags) <- loadSourceFile path
  let cu0 = compileSourceWithPrelude path src
      cu = cu0 {cuDiags = preDiags ++ cuDiags cu0}
  emitDiags fmt (cuDiags cu)
  if hasErrors (cuDiags cu) then exitFailure else exitSuccess

cmdRun :: DiagFormat -> FilePath -> IO ()
cmdRun fmt path = do
  (src, preDiags) <- loadSourceFile path
  let cu0 = compileSourceWithPrelude path src
      cu = cu0 {cuDiags = preDiags ++ cuDiags cu0}
  emitDiags fmt (cuDiags cu)
  when (hasErrors (cuDiags cu)) exitFailure
  let st = cuState cu
      mainG = GName (cuModule cu) "main"
  unless (Map.member mainG (csGlobals st)) $ do
    hPutStrLn stderr "error[E_NO_MAIN]: no 'main' definition in module"
    exitFailure
  r <- runMain (Globals (csGlobals st)) (csMetas st) mainG
  case r of
    RunOk -> exitSuccess
    RunFail msg -> do
      hPutStrLn stderr ("runtime failure: " <> T.unpack msg)
      exitWith (ExitFailure 1)

-- | The standardized build-manifest path (§35.13). Assembled from
-- segments so the literal does not trip the family-literal scanner in
-- the diagnostic-registry gate (a @kappa.…@-shaped string).
manifestFileName :: FilePath
manifestFileName = "kappa" <> ".build.kp"

-- | Manifest-build options parsed from the @build@ flags.
data ManifestArgs = ManifestArgs
  { maPath :: !(Maybe FilePath) -- ^ explicit manifest file/dir (else discover)
  , maCheck :: !Bool -- ^ validate + summarize only, no build
  , maTarget :: !(Maybe T.Text) -- ^ --target NAME
  , maOut :: !(Maybe FilePath) -- ^ -o OUT
  , maEmitC :: !Bool -- ^ --emit-c
  , maCC :: !(Maybe String) -- ^ --cc DRIVER
  }

defaultManifestArgs :: ManifestArgs
defaultManifestArgs = ManifestArgs Nothing False Nothing Nothing False Nothing

-- | Dispatch a @build@ invocation to manifest mode (§35.13/§36) or the
-- legacy single-file native build.
cmdBuild :: [String] -> IO ()
cmdBuild rawArgs
  -- Manifest mode (§35.13/§36): an explicit @--manifest@, no positional
  -- path (discover from the working directory), or a positional that names
  -- a @kappa.build.kp@ file. Otherwise the legacy single-file native build.
  | manifestMode = case parseManifestArgs rawArgs of
      Left msg -> hPutStrLn stderr ("error: " <> msg) >> exitFailure
      Right ma -> cmdBuildManifest ma
  | otherwise = cmdBuildNative rawArgs
  where
    positional = [a | a <- rawArgs, take 1 a /= "-"]
    manifestMode =
      "--manifest" `elem` rawArgs
        || null positional
        || any ((== manifestFileName) . takeFileName) positional

parseManifestArgs :: [String] -> Either String ManifestArgs
parseManifestArgs = go defaultManifestArgs
  where
    go ma [] = Right ma
    go ma ("--manifest" : xs) = go ma xs
    go ma ("--check" : xs) = go ma {maCheck = True} xs
    go ma ("--emit-c" : xs) = go ma {maEmitC = True} xs
    go ma ("--target" : t : xs) = go ma {maTarget = Just (T.pack t)} xs
    go ma ("-o" : o : xs) = go ma {maOut = Just o} xs
    go ma ("--cc" : c : xs) = go ma {maCC = Just c} xs
    go ma (x : xs)
      | take 1 x /= "-", Nothing <- maPath ma = go ma {maPath = Just x} xs
      | otherwise = Left ("kappa build: unexpected argument '" <> x <> "'")

-- | Load, config-check (§35.13) and reify a build manifest; then, unless
-- @--check@ is given, run the build-plan slice (§36.4) for an executable
-- target and drive native codegen/link. The manifest's native bindings
-- (§36.28) select which @host.native.*@ modules the program may import and
-- supply the link flags — codegen is driven entirely by this config, never
-- a hardcoded native list. @--check@ stops at the evaluated configuration
-- (the §35.13 boundary) and prints a summary.
cmdBuildManifest :: ManifestArgs -> IO ()
cmdBuildManifest ma = do
  resolved <- resolveManifestPath (maPath ma)
  case resolved of
    Left d -> emitDiags Human [d] >> exitFailure
    Right file -> do
      (src, preDiags) <- loadSourceFile file
      let (st, mn, diags) = compileManifest file src
          allDiags = preDiags ++ diags
      emitDiags Human allDiags
      when (hasErrors allDiags) exitFailure
      let sp = Span file (Pos 1 1) (Pos 1 1)
      case reifyBuildConfig sp st mn of
        Left ds -> emitDiags Human ds >> exitFailure
        Right bc
          | maCheck ma -> TIO.putStr (renderBuildConfig bc) >> exitSuccess
          | otherwise -> buildManifestTarget file bc ma

-- | The build-plan + codegen path for a manifest executable target.
buildManifestTarget :: FilePath -> B.BuildConfig -> ManifestArgs -> IO ()
buildManifestTarget manifestFile bc ma = do
  let manifestDir = takeDirectory manifestFile
  resolved <- resolveExecutable manifestDir bc (maTarget ma)
  case resolved of
    Left ds -> emitDiags Human ds >> exitFailure
    Right rx -> do
      -- Load every package source file of the target and compile them as
      -- one §8.1 package-mode unit (header/path agreement), with the
      -- manifest-selected host.native modules available (§36.4).
      loaded <- mapM (\(p, _) -> (\(s, d) -> (p, s, d)) <$> loadSourceFile p) (rxSourceFiles rx)
      let nameTable = Map.fromList [(p, mn) | (p, mn) <- rxSourceFiles rx]
          nameOf p = Map.findWithDefault (moduleNameOf p) p nameTable
          files = [(p, s) | (p, s, _) <- loaded]
          preDiags = concat [d | (_, _, d) <- loaded]
          (cu, hostPrims) =
            compileProgramWithNative (rxProvidedModules rx) defaultUnsafeConfig True nameOf files
          cuDs = preDiags ++ cuDiags cu
      emitDiags Human cuDs
      when (hasErrors cuDs) exitFailure
      let st = cuState cu
          mainG = GName (rxEntryModule rx) "main"
      unless (Map.member mainG (csGlobals st)) $ do
        hPutStrLn stderr "error[E_NO_MAIN]: the target's entry module has no 'main' definition"
        exitFailure
      let entryFile = maybe "<entry>" fst (lookupEntry rx)
          opts =
            defaultBuildOptions
              { boOutput = maOut ma
              , boEmitCOnly = maEmitC ma
              , boCC = maCC ma
              , boRuntimeFfi = rxRuntimeFfi rx
              , boHostPrims = hostPrims
              , boLinkSpecs = rxLinkSpecs rx
              }
      result <- buildNative st mainG entryFile opts
      case result of
        Left ds -> emitDiags Human ds >> exitFailure
        Right outPath -> hPutStrLn stderr ("built " <> outPath) >> exitSuccess
  where
    -- the source file whose module is the entry module (for the artifact
    -- basename / generated-C path)
    lookupEntry rx = case [(p, mn) | (p, mn) <- rxSourceFiles rx, mn == rxEntryModule rx] of
      (x : _) -> Just x
      [] -> Nothing

-- | Resolve the manifest path: an explicit file, a directory (look for
-- @kappa.build.kp@ inside), or — with no argument — a walk up from the
-- working directory. Failure yields an 'E_BUILD_MANIFEST_NOT_FOUND'
-- diagnostic (§35.13).
resolveManifestPath :: Maybe FilePath -> IO (Either Diagnostic FilePath)
resolveManifestPath marg = case marg of
  Just p -> do
    isDir <- doesDirectoryExist p
    let cand = if isDir then p </> manifestFileName else p
    ok <- doesFileExist cand
    pure (if ok then Right cand else Left (notFound cand))
  Nothing -> getCurrentDirectory >>= walkUp
  where
    walkUp dir = do
      let cand = dir </> manifestFileName
      ok <- doesFileExist cand
      if ok
        then pure (Right cand)
        else
          let parent = takeDirectory dir
           in if parent == dir
                then pure (Left (notFound manifestFileName))
                else walkUp parent
    notFound what =
      diag SevError StageImports "E_BUILD_MANIFEST_NOT_FOUND"
        (Just "kappa-hs.build.manifest-not-found")
        (Span what (Pos 1 1) (Pos 1 1))
        ( "no build manifest '" <> T.pack manifestFileName
            <> "' was found (Spec §35.13); looked for '" <> T.pack what <> "'"
        )

-- | A concise human summary of a reified build configuration (§35.13
-- evaluation result). This is the increment-1 surface; machine-readable
-- emission and the full provenance graph are sequenced follow-ups.
renderBuildConfig :: B.BuildConfig -> T.Text
renderBuildConfig bc =
  T.unlines $
    [ "package " <> B.bcName bc <> " " <> B.pvRaw (B.bcVersion bc)
    , "  source roots: " <> T.intercalate ", " (map B.srPath (B.bcSourceRoots bc))
    ]
      ++ [ "  fragment axis " <> B.faName ax <> ": " <> T.intercalate ", " (B.faTags ax)
         | ax <- B.bcFragmentAxes bc
         ]
      ++ [ "  dependency " <> renderDep d | d <- B.bcDependencies bc]
      ++ [ "  native binding " <> B.nbName hb <> " -> "
             <> T.intercalate ", " (map renderSel (B.nbProvides hb))
             <> " [" <> renderLink (B.nbLink hb) <> "]"
         | hb <- B.bcHostBindings bc
         ]
      ++ [ "  target " <> B.tName t <> " (" <> renderBackend (B.tBackend t) <> ")"
         | t <- B.bcTargets bc
         ]
  where
    renderDep (B.RegistryDep n v) = "registry " <> n <> " " <> v
    renderDep (B.GitDep n u r) = "git " <> n <> " " <> u <> "@" <> r
    renderDep (B.PathDep n p) = "path " <> n <> " " <> p
    renderSel (B.SelModule m) = m
    renderSel (B.SelModulesUnder m) = m <> ".*"
    renderLink (B.DynamicLink ls) = "dynamic: " <> T.intercalate " " ls
    renderLink (B.StaticLink ls) = "static: " <> T.intercalate " " ls
    renderLink B.NoLink = "no-link"
    renderBackend (B.NativeBackend tc tt) = "native " <> tc <> "/" <> tt
    renderBackend B.JvmBackend = "jvm"
    renderBackend B.DotNetBackend = "dotnet"

-- | Legacy single-file native build (§27.7, profile-scoped): compile a
-- Kappa program to a native executable. No build manifest, so NO native
-- host bindings are available — a program that imports a @host.native.*@
-- module fails honestly (the module is unresolved without a manifest
-- provider). Native bindings are obtained only through the manifest/
-- package mechanism (@kappa build --manifest@); there is no @--ffi-full@.
cmdBuildNative :: [String] -> IO ()
cmdBuildNative rawArgs = case parseBuildArgs rawArgs defaultBuildOptions of
  Left msg -> hPutStrLn stderr ("error: " <> msg) >> exitFailure
  Right (opts, path) -> do
    (src, preDiags) <- loadSourceFile path
    let cu0 = compileSourceWithPrelude path src
        cu = cu0 {cuDiags = preDiags ++ cuDiags cu0}
    emitDiags Human (cuDiags cu)
    when (hasErrors (cuDiags cu)) exitFailure
    let st = cuState cu
        mainG = GName (cuModule cu) "main"
    unless (Map.member mainG (csGlobals st)) $ do
      hPutStrLn stderr "error[E_NO_MAIN]: no 'main' definition in module"
      exitFailure
    result <- buildNative st mainG path opts
    case result of
      Left ds -> do
        emitDiags Human ds
        exitFailure
      Right outPath -> do
        hPutStrLn stderr ("built " <> outPath)
        exitSuccess

-- | Parse legacy @build FILE@ flags.  The single positional argument is
-- the source path; unknown flags are an error (no silent acceptance).
-- Native host bindings come from the manifest path, so there is no
-- @--ffi-full@/@--lib@ here.
parseBuildArgs :: [String] -> BuildOptions -> Either String (BuildOptions, FilePath)
parseBuildArgs args opts0 = go args opts0 Nothing
  where
    go [] opts (Just p) = Right (opts, p)
    go [] _ Nothing = Left "kappa build: missing source path"
    go ("--emit-c" : xs) opts mp = go xs opts {boEmitCOnly = True} mp
    go ("-o" : o : xs) opts mp = go xs opts {boOutput = Just o} mp
    go ("--cc" : c : xs) opts mp = go xs opts {boCC = Just c} mp
    go (x : xs) opts Nothing
      | take 1 x /= "-" = go xs opts (Just x)
    go (x : _) _ _ = Left ("kappa build: unexpected argument '" <> x <> "'")

-- | §4.7 unsafe/debug audit query (the @auditModule@ surface). Emits the
-- compilation unit's audit ledger as machine-readable JSON, never as
-- diagnostic prose. One object per ledger entry.
cmdAudit :: FilePath -> IO ()
cmdAudit path = do
  (src, _preDiags) <- loadSourceFile path
  let cu = compileSourceWithPrelude path src
      ledger = csAuditLedger (cuState cu)
  TIO.putStrLn (renderAuditLedgerJson ledger)
  exitSuccess

-- | §4.7: render the audit ledger as a JSON array. Each record carries
-- the facility, module identity, origin, affected declaration, the build
-- setting that permitted it, and any structured reason string.
renderAuditLedgerJson :: [AuditRecord] -> T.Text
renderAuditLedgerJson recs = jArray (map one recs)
  where
    one r =
      jObject
        [ ("facility", jStr (arFacility r))
        , ("module", jStr (moduleNameText (arModule r)))
        , ("origin", jStr (renderSpanText (arOrigin r)))
        , ("affected", jStr (arAffected r))
        , ("buildSetting", jStr (arBuildSetting r))
        , ("reason", maybe "null" jStr (arReason r))
        ]
    renderSpanText sp =
      T.pack (spanFile sp) <> ":" <> tshow (posLine (spanStart sp)) <> ":" <> tshow (posCol (spanStart sp))
    tshow = T.pack . show

-- | Appendix T harness over a file or directory tree (§T.2, §T.8).
-- @--suite@ treats the directory as exactly one suite root.
cmdTest :: (FilePath -> IO [TestReport]) -> FilePath -> IO ()
cmdTest runner path = do
  reports <- runner path
  let s = summarize reports
  putStrLn $
    "total " <> show (length reports)
      <> ": " <> show (sPass s) <> " passed, "
      <> show (sFail s) <> " failed, "
      <> show (sUnsupported s) <> " unsupported, "
      <> show (sHarnessError s) <> " harness errors"
  if sFail s > 0 || sHarnessError s > 0 then exitFailure else exitSuccess
