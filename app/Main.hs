-- | The @kappa@ CLI: check, run, and the Appendix T test harness.
module Main (main) where

import Control.Monad (forM_, unless, when)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Kappa.Check (CheckState (..))
import Kappa.Core (GName (..))
import Kappa.Diagnostic
import Kappa.Eval (Globals (..))
import Kappa.Explain (lookupCode, renderEntry)
import Kappa.Interp (RunResult (..), runMain)
import Kappa.Pipeline
import Kappa.TestHarness (Summary (..), TestReport, runTestPath, runTestSuitePath, summarize)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitFailure, exitSuccess, exitWith)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["check", path] -> cmdCheck path
    ["run", path] -> cmdRun path
    ["test", path] -> cmdTest runTestPath path
    ["test", "--suite", path] -> cmdTest runTestSuitePath path
    ["explain", code] -> cmdExplain (T.pack code)
    _ -> do
      hPutStrLn stderr "usage: kappa (check|run|test [--suite]) PATH | kappa explain CODE"
      exitFailure

-- | §3.1.2A: print the registry explanation for a diagnostic code;
-- unknown codes are rejected deterministically.
cmdExplain :: T.Text -> IO ()
cmdExplain code = case lookupCode code of
  Just e -> TIO.putStr (renderEntry e) >> exitSuccess
  Nothing -> do
    TIO.hPutStrLn stderr ("error: unknown diagnostic code '" <> code <> "'")
    exitFailure

cmdCheck :: FilePath -> IO ()
cmdCheck path = do
  (src, preDiags) <- loadSourceFile path
  let cu0 = compileSourceWithPrelude path src
      cu = cu0 {cuDiags = preDiags ++ cuDiags cu0}
  forM_ (cuDiags cu) (TIO.hPutStrLn stderr . renderDiagnostic)
  if hasErrors (cuDiags cu) then exitFailure else exitSuccess

cmdRun :: FilePath -> IO ()
cmdRun path = do
  (src, preDiags) <- loadSourceFile path
  let cu0 = compileSourceWithPrelude path src
      cu = cu0 {cuDiags = preDiags ++ cuDiags cu0}
  forM_ (cuDiags cu) (TIO.hPutStrLn stderr . renderDiagnostic)
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
