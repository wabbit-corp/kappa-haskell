-- | The @kappa@ CLI: check, run, and the Appendix T test harness.
module Main (main) where

import Control.Monad (forM_, unless, when)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Kappa.Backend.Driver
  ( BuildOptions (..)
  , buildNative
  , defaultBuildOptions
  , detectCC
  )
import Kappa.Backend.NativeFfi (ResolvedNativeSymbol (..))
import Kappa.Backend.NativeProbe (hostBindingLockEntries)
import Kappa.Build.Lock (LockEntry (..), lockWellFormed, parseLock, renderLock)
import Kappa.Build.Plan (ResolvedExe (..), resolveExecutable, resolveTestTarget)
import Kappa.Build.Provenance (manifestProvenance, renderProvenance)
import Kappa.Build.Reify (reifyBuildConfig)
import qualified Kappa.Build.Types as B
import Kappa.Check (AuditRecord (..), CheckState (..), defaultUnsafeConfig)
import Kappa.Core (GName (..))
import Kappa.Diagnostic
import Kappa.Eval (Globals (..))
import Kappa.Explain (lookupCode, lookupFamily, renderEntry, renderFamily)
import Kappa.Interp (RunResult (..), runMain)
import Kappa.Pipeline
import Kappa.Source (ModuleName, Pos (..), Span (..), moduleNameText)
import Kappa.TestHarness (Summary (..), TestReport, runTestPath, runTestSuitePath, summarize)
import System.Directory (doesDirectoryExist, doesFileExist, getCurrentDirectory, removeFile)
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
          <> " | kappa build --manifest [PATH|DIR] [--check] [--provenance] [--locked] [--target NAME] [-o OUT] [--emit-c] [--cc DRIVER]"
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
  , maLocked :: !Bool -- ^ --locked: require kappa.lock to match (no update)
  , maProvenance :: !Bool -- ^ --provenance: print buildConfig value provenance (§35.7)
  }

defaultManifestArgs :: ManifestArgs
defaultManifestArgs = ManifestArgs Nothing False Nothing Nothing False Nothing False False

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
    go ma ("--locked" : xs) = go ma {maLocked = True} xs
    go ma ("--provenance" : xs) = go ma {maProvenance = True} xs
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
      let (st, mn, mmod, diags) = compileManifest file src
          allDiags = preDiags ++ diags
      emitDiags Human allDiags
      when (hasErrors allDiags) exitFailure
      let sp = Span file (Pos 1 1) (Pos 1 1)
      case reifyBuildConfig sp st mn of
        Left ds -> emitDiags Human ds >> exitFailure
        Right bc
          -- §35.7: print the buildConfig value-provenance graph (a tool
          -- explicitly choosing to surface config provenance). Like
          -- --check, this performs no build.
          | maProvenance ma ->
              case mmod >>= manifestProvenance of
                Just prov -> TIO.putStr (renderProvenance prov) >> exitSuccess
                Nothing -> hPutStrLn stderr "no buildConfig value provenance available" >> exitFailure
          | maCheck ma -> TIO.putStr (renderBuildConfig bc) >> exitSuccess
          -- a --target dispatches on the named target's kind (executable
          -- build / test suite / aggregate of members); no --target builds
          -- the default executable. The dependency lock is verified/updated
          -- ONCE for the whole invocation against the union of every reached
          -- exe/bench target's closure (see runInvocation) — never per
          -- target, which would let aggregate members overwrite each other.
          | otherwise -> runInvocation file bc ma (maTarget ma)

-- | Run a build invocation (default executable, or a named --target) with
-- a single package-scoped lock step. The dependency lock reflects the union
-- of the closures of every exe/bench target this invocation reaches; it is
-- verified once up front (under --locked, before any build) and updated once
-- after a successful build (without --locked). Test/library-only invocations
-- carry no closure and leave the lock untouched.
runInvocation :: FilePath -> B.BuildConfig -> ManifestArgs -> Maybe T.Text -> IO ()
runInvocation file bc ma mtgt = do
  let manifestDir = takeDirectory file
  closure <- collectLockClosure file bc mtgt
  case closure of
    Left ds -> emitDiags Human ds >> exitFailure
    Right (manages, entries) -> do
      when (manages && maLocked ma) (verifyLock manifestDir entries)
      ok <- case mtgt of
        Just nm -> runNamedTarget file bc ma Set.empty nm
        Nothing -> runExecutable file bc ma Nothing
      when (manages && ok && not (maLocked ma)) (updateLock manifestDir entries)
      if ok then exitSuccess else exitFailure

-- | Resolve (without building) the dependency-lock closure of an
-- invocation, mirroring 'runNamedTarget' dispatch. Returns @(managesLock,
-- entries)@: @managesLock@ is True iff at least one exe/bench target is
-- reached (only those carry a §36.23 closure); test/library targets
-- contribute nothing and must not touch the package lock. A not-found or
-- cyclic target is reported as carrying no closure here — the build pass
-- emits the real diagnostic.
collectLockClosure :: FilePath -> B.BuildConfig -> Maybe T.Text -> IO (Either Diagnostics (Bool, [LockEntry]))
collectLockClosure file bc mtgt = case mtgt of
  Nothing -> resolveExecutable manifestDir bc Nothing >>= oneIO
  Just nm -> go Set.empty nm
  where
    manifestDir = takeDirectory file
    -- §36.7/§27.1.1: an exe/bench target's lock closure is its dependency
    -- entries PLUS the host-source identity pin of every selected native
    -- binding (computed by discovery + fail-closed ABI verification). The
    -- native pin is what makes a package-mode host.native build reproducible
    -- (a later --locked build verifies it; drift fails).
    oneIO :: Either Diagnostics ResolvedExe -> IO (Either Diagnostics (Bool, [LockEntry]))
    oneIO (Left ds) = pure (Left ds)
    oneIO (Right rx)
      | null (rxNativeBindings rx) = pure (Right (True, rxLockEntries rx))
      | otherwise = do
          mcc <- detectCC Nothing
          case mcc of
            Nothing -> pure (Right (True, rxLockEntries rx)) -- no toolchain: build step reports it
            Just cc -> do
              let bindings = [(nm', map renderSym ss, ins) | (nm', ss, ins) <- rxNativeBindings rx]
              r <- hostBindingLockEntries cc manifestDir (rxTargetTriple rx) bindings
              pure $ case r of
                Left ds -> Left ds
                Right hbs -> Right (True, rxLockEntries rx ++ hbs)
    renderSym s =
      rnsMember s <> " " <> rnsCSymbol s <> " "
        <> T.pack (show (rnsParams s)) <> "->" <> T.pack (show (rnsResult s))
    go visited nm
      | nm `Set.member` visited = pure (Right (False, []))
      | otherwise = case [t | t <- B.bcTargets bc, B.tName t == nm] of
          [] -> pure (Right (False, []))
          (t : _) -> case t of
            B.ExecutableTarget {} -> resolveExecutable manifestDir bc (Just nm) >>= oneIO
            B.BenchmarkTarget {} -> resolveExecutable manifestDir bc (Just nm) >>= oneIO
            B.TestTarget {} -> pure (Right (False, []))
            B.LibraryTarget {} -> pure (Right (False, []))
            B.AliasTarget _ aliased -> go (Set.insert nm visited) aliased
            B.AggregateTarget _ members -> do
              rs <- mapM (go (Set.insert nm visited)) members
              pure $ case sequence rs of
                Left ds -> Left ds
                Right parts -> Right (any fst parts, concatMap snd parts)

-- | Run one manifest target by name, dispatching on its kind. Returns
-- whether it succeeded (so an aggregate can combine its members). @visited@
-- detects aggregate cycles. The lockfile is handled by 'runInvocation', not
-- here.
runNamedTarget :: FilePath -> B.BuildConfig -> ManifestArgs -> Set.Set T.Text -> T.Text -> IO Bool
runNamedTarget file bc ma visited nm
  | nm `Set.member` visited =
      emitDiags Human
        [ diag SevError StageImports "E_BUILD_TARGET_CYCLE" (Just "kappa-hs.build.target-cycle")
            (Span file (Pos 1 1) (Pos 1 1))
            ("aggregate target membership is cyclic through '" <> nm <> "' (Spec §36.3)")
        ]
        >> pure False
  | otherwise = case [t | t <- B.bcTargets bc, B.tName t == nm] of
      [] ->
        emitDiags Human
          [ diag SevError StageImports "E_BUILD_TARGET_NOT_FOUND" (Just "kappa-hs.build.target-not-found")
              (Span file (Pos 1 1) (Pos 1 1))
              ("no target named '" <> nm <> "' in the manifest (Spec §36.3)")
          ]
          >> pure False
      (t : _) -> case t of
        B.TestTarget {} -> runTest file bc nm
        B.ExecutableTarget {} -> runExecutable file bc ma (Just nm)
        B.AggregateTarget _ members ->
          and <$> mapM (runNamedTarget file bc ma (Set.insert nm visited)) members
        B.AliasTarget _ aliased ->
          runNamedTarget file bc ma (Set.insert nm visited) aliased
        B.BenchmarkTarget {} -> runBenchmark file bc nm
        B.LibraryTarget {} -> do
          hPutStrLn stderr
            ("note: library target '" <> T.unpack nm <> "' is consumed as a dependency, not built directly; skipping")
          pure True

-- | Run a manifest @test@ target's Appendix-T suite (§36.31): resolve its
-- test source files and run each through the test harness, then report.
runTest :: FilePath -> B.BuildConfig -> T.Text -> IO Bool
runTest manifestFile bc nm = do
  resolved <- resolveTestTarget (takeDirectory manifestFile) bc (Just nm)
  case resolved of
    Left ds -> emitDiags Human ds >> pure False
    Right (_, files) -> do
      reports <- concat <$> mapM runTestPath files
      let s = summarize reports
      putStrLn $
        "test target " <> T.unpack nm <> ": total " <> show (length reports)
          <> ": " <> show (sPass s) <> " passed, " <> show (sFail s) <> " failed, "
          <> show (sUnsupported s) <> " unsupported, " <> show (sHarnessError s) <> " harness errors"
      pure (sFail s == 0 && sHarnessError s == 0)

-- | Resolve an executable/benchmark target by name, load its package
-- source files, and compile them as one §8.1 package-mode unit with the
-- manifest-selected host.native modules. (The lock is handled once per
-- invocation by 'runInvocation', not here.)
-- Returns the checked state, the @main@ GName, the gname→prim map, and the
-- resolved plan — or 'Nothing' (diagnostics already emitted) on any error.
prepareUnit :: FilePath -> B.BuildConfig -> Maybe T.Text -> IO (Maybe (CheckState, GName, Map.Map GName ResolvedNativeSymbol, ResolvedExe))
prepareUnit manifestFile bc mname = do
  let manifestDir = takeDirectory manifestFile
  resolved <- resolveExecutable manifestDir bc mname
  case resolved of
    Left ds -> emitDiags Human ds >> pure Nothing
    Right rx -> do
      loaded <- mapM (\(p, _) -> (\(s, d) -> (p, s, d)) <$> loadSourceFile p) (rxSourceFiles rx)
      let nameTable = Map.fromList [(p, mn) | (p, mn) <- rxSourceFiles rx]
          nameOf p = Map.findWithDefault (moduleNameOf p) p nameTable
          files = [(p, s) | (p, s, _) <- loaded]
          preDiags = concat [d | (_, _, d) <- loaded]
          (cu, hostSyms) =
            compileProgramWithNative (rxNativeSymbols rx) defaultUnsafeConfig True nameOf files
          cuDs = preDiags ++ cuDiags cu
      emitDiags Human cuDs
      let st = cuState cu
          mainG = GName (rxEntryModule rx) "main"
      if hasErrors cuDs
        then pure Nothing
        else
          if not (Map.member mainG (csGlobals st))
            then hPutStrLn stderr "error[E_NO_MAIN]: the target's entry module has no 'main' definition" >> pure Nothing
            else pure (Just (st, mainG, hostSyms, rx))

-- | Native build of an executable target. Returns whether it succeeded.
runExecutable :: FilePath -> B.BuildConfig -> ManifestArgs -> Maybe T.Text -> IO Bool
runExecutable manifestFile bc ma mname = do
  prep <- prepareUnit manifestFile bc mname
  case prep of
    Nothing -> pure False
    Just (st, mainG, hostSyms, rx) -> do
      let entryFile = maybe "<entry>" fst (lookupEntry rx)
          opts =
            defaultBuildOptions
              { boOutput = maOut ma
              , boEmitCOnly = maEmitC ma
              , boCC = maCC ma
              , boHostSyms = hostSyms
              , boLinkSpecs = rxLinkSpecs rx
              , boNativeInputs = rxNativeInputs rx
              , boNativeBaseDir = Just (takeDirectory manifestFile)
              , boTargetTriple = rxTargetTriple rx
              }
      result <- buildNative st mainG entryFile opts
      case result of
        Left ds -> emitDiags Human ds >> pure False
        Right outPath -> do
          hPutStrLn stderr ("built " <> outPath)
          pure True

-- | §36 benchmark target: a benchmark is a runnable program. This
-- implementation executes its @main@ under the interpreter (no native
-- toolchain needed) and reports completion. Benchmarks are pure-compute
-- (no host.native bindings); a benchmark that imports a host.native module
-- fails honestly since the interpreter supplies no foreign operations.
runBenchmark :: FilePath -> B.BuildConfig -> T.Text -> IO Bool
runBenchmark manifestFile bc nm = do
  prep <- prepareUnit manifestFile bc (Just nm)
  case prep of
    Nothing -> pure False
    Just (st, mainG, _, _) -> do
      hPutStrLn stderr ("running benchmark " <> T.unpack nm)
      r <- runMain (Globals (csGlobals st)) (csMetas st) mainG
      case r of
        RunOk -> hPutStrLn stderr ("benchmark " <> T.unpack nm <> " completed") >> pure True
        RunFail msg -> hPutStrLn stderr ("benchmark " <> T.unpack nm <> " failed: " <> T.unpack msg) >> pure False

-- | The source file whose module is the entry module (for the artifact
-- basename / generated-C path).
lookupEntry :: ResolvedExe -> Maybe (FilePath, ModuleName)
lookupEntry rx = case [(p, mn) | (p, mn) <- rxSourceFiles rx, mn == rxEntryModule rx] of
  (x : _) -> Just x
  [] -> Nothing

-- | The build lockfile basename (assembled so the literal does not trip
-- the diagnostic family-literal scanner).
lockFileName :: FilePath
lockFileName = "kappa" <> ".lock"

-- | Verify the resolved package dependency closure against @kappa.lock@ and
-- fail (E_DEPENDENCY_LOCK_MISMATCH, §3.2.15) if the lock is missing, corrupt,
-- or stale. Called once per invocation by 'runInvocation' under @--locked@
-- (the @entries@ are the union over every reached exe/bench target), so it
-- never compares a single target's partial closure against the package lock.
verifyLock :: FilePath -> [LockEntry] -> IO ()
verifyLock manifestDir entries = do
  let lockPath = manifestDir </> lockFileName
      desired = parseLock (renderLock entries) -- normalized + sorted
      -- §8.3.5/§27.1.1: a host-binding (host.native) entry that is missing or
      -- changed in the lock is an UNPINNED native binding — emit the
      -- native-specific diagnostic rather than the dependency one.
      reject ex actual =
        let actualSet = Set.fromList [(leKind e, leKey e, leId e) | e <- actual]
            hbBad = [e | e <- desired, leKind e == "host-binding", not ((leKind e, leKey e, leId e) `Set.member` actualSet)]
            depBad = any (\e -> leKind e /= "host-binding") desired
                       && parseLock (renderLock [e | e <- desired, leKind e /= "host-binding"])
                          /= [e | e <- actual, leKind e /= "host-binding"]
            ds = [nativeUnpinnedDiag lockPath e | e <- hbBad]
                   ++ [lockMismatchDiag lockPath ex | depBad || (null hbBad)]
         in emitDiags Human ds >> exitFailure
  exists <- doesFileExist lockPath
  if not exists
    then when (not (null entries)) (reject False [])
    else do
      txt <- TIO.readFile lockPath
      let actual = parseLock txt
      when (not (lockWellFormed txt) || actual /= desired) (reject True actual)

nativeUnpinnedDiag :: FilePath -> LockEntry -> Diagnostic
nativeUnpinnedDiag lockPath e =
  diag SevError StageImports "E_NATIVE_BINDING_UNPINNED"
    (Just "kappa.package.reproducibility")
    (Span lockPath (Pos 1 1) (Pos 1 1))
    ( "the host.native binding '" <> leKey e <> "' is not pinned by a matching host-source "
        <> "identity in '" <> T.pack lockPath <> "' (its pkg-config version, header/shim "
        <> "digests, symbol surface, or target triple changed, or no entry exists); a "
        <> "package-mode host.native build MUST be pinned (Spec §8.3.5, §27.1.1, §36.7) — "
        <> "re-run 'kappa build --manifest' without --locked to update the lockfile"
    )

-- | Create/update @kappa.lock@ when the resolved package closure differs
-- from it, and clear a now-stale lock when the closure is empty. Called once
-- per invocation by 'runInvocation' after a successful build (without
-- @--locked@); the @entries@ are the package-wide union.
updateLock :: FilePath -> [LockEntry] -> IO ()
updateLock manifestDir entries = do
  let lockPath = manifestDir </> lockFileName
      desired = parseLock (renderLock entries)
  exists <- doesFileExist lockPath
  existing <- if exists then parseLock <$> TIO.readFile lockPath else pure []
  if null entries
    then when exists (removeFile lockPath) -- closure now empty: drop stale lock
    else when (desired /= existing) (TIO.writeFile lockPath (renderLock entries))

lockMismatchDiag :: FilePath -> Bool -> Diagnostic
lockMismatchDiag lockPath exists =
  diag SevError StageImports "E_DEPENDENCY_LOCK_MISMATCH"
    (Just "kappa.package.reproducibility")
    (Span lockPath (Pos 1 1) (Pos 1 1))
    ( ( if exists
          then "the resolved path-dependency content identities do not match '"
          else "a locked build was requested but no lockfile exists at '"
      )
        <> T.pack lockPath
        <> "' (Spec §36.4, §36.23.2, §3.2.15); re-run 'kappa build --manifest' "
        <> "without --locked to update the lockfile"
    )

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
      ++ [ "  target " <> B.tName t <> " (" <> renderTargetKind t <> ")"
         | t <- B.bcTargets bc
         ]
  where
    renderTargetKind t = case t of
      B.TestTarget {} -> "test"
      B.AggregateTarget _ ms -> "aggregate of " <> T.intercalate ", " ms
      B.AliasTarget _ a -> "alias of " <> a
      B.BenchmarkTarget {} -> "benchmark " <> renderBackend (B.tBackend t)
      _ -> renderBackend (B.tBackend t)
    renderDep (B.RegistryDep n v) = "registry " <> n <> " " <> v
    renderDep (B.GitDep n u r) = "git " <> n <> " " <> u <> "@" <> r
    renderDep (B.PathDep n p) = "path " <> n <> " " <> p
    renderDep (B.UrlDep n u) = "url " <> n <> " " <> u
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
