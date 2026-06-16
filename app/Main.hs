-- | The @kappa@ CLI: check, run, and the Appendix T test harness.
module Main (main) where

import Control.Monad (forM_, unless, when)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Kappa.Backend.Driver
  ( BuildOptions (..)
  , FfiUnit (..)
  , buildNative
  , defaultBuildOptions
  )
import Kappa.Check (AuditRecord (..), CheckState (..))
import Kappa.Core (GName (..))
import Kappa.Diagnostic
import Kappa.Eval (Globals (..))
import Kappa.Explain (lookupCode, lookupFamily, renderEntry, renderFamily)
import Kappa.Interp (RunResult (..), runMain)
import Kappa.Pipeline
import Kappa.Source (Pos (..), Span (..), moduleNameText)
import Kappa.TestHarness (Summary (..), TestReport, runTestPath, runTestSuitePath, summarize)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitFailure, exitSuccess, exitWith)
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
          <> " | kappa build [--emit-c] [-o OUT] [--cc DRIVER] [--ffi-full]"
          <> " [--lib FLAG]... PATH"
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

-- | Native backend (§27.7, profile-scoped): compile a Kappa program to a
-- native executable.  Runs the ordinary front end first and refuses to
-- proceed on any error (the backend never compiles rejected code); then
-- lowers @main@'s reachable closure to C and invokes the C toolchain.
-- See docs/NATIVE_BACKEND.md.
cmdBuild :: [String] -> IO ()
cmdBuild rawArgs = case parseBuildArgs rawArgs defaultBuildOptions of
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

-- | Parse @build@ flags.  The single positional argument is the source
-- path; unknown flags are an error (no silent acceptance).
parseBuildArgs :: [String] -> BuildOptions -> Either String (BuildOptions, FilePath)
parseBuildArgs args opts0 = go args opts0 Nothing
  where
    go [] opts (Just p) = Right (opts, p)
    go [] _ Nothing = Left "kappa build: missing source path"
    go ("--emit-c" : xs) opts mp = go xs opts {boEmitCOnly = True} mp
    go ("--ffi-full" : xs) opts mp = go xs opts {boFfiUnit = FfiFull} mp
    go ("-o" : o : xs) opts mp = go xs opts {boOutput = Just o} mp
    go ("--cc" : c : xs) opts mp = go xs opts {boCC = Just c} mp
    go ("--lib" : l : xs) opts mp = go xs opts {boExtraLibs = boExtraLibs opts ++ [l]} mp
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
