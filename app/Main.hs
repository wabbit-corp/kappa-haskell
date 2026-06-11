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
import Kappa.Interp (RunResult (..), runMain)
import Kappa.Pipeline
import Kappa.Source
import Kappa.TestHarness (Summary (..), runTestPath, summarize)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitFailure, exitSuccess, exitWith)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["check", path] -> cmdCheck path
    ["run", path] -> cmdRun path
    ["test", path] -> cmdTest path
    _ -> do
      hPutStrLn stderr "usage: kappa (check|run|test) PATH"
      exitFailure

renderDiag :: Diagnostic -> String
renderDiag d =
  let Span f (Pos l c) _ = dPrimary d
      sev = case dSeverity d of
        SevError -> "error"
        SevWarning -> "warning"
        SevNote -> "note"
        SevInfo -> "info"
      notes = concatMap (\n -> "\n  note: " <> T.unpack n) (dNotes d)
      helps = concatMap (\h -> "\n  help: " <> T.unpack h) (dHelps d)
   in f <> ":" <> show l <> ":" <> show c <> ": " <> sev <> "[" <> T.unpack (dCode d) <> "]"
        <> maybe "" (\fam -> " (" <> T.unpack fam <> ")") (dFamily d)
        <> ": " <> T.unpack (dMessage d)
        <> notes
        <> helps

cmdCheck :: FilePath -> IO ()
cmdCheck path = do
  src <- TIO.readFile path
  let cu = compileSourceWithPrelude path src
  forM_ (cuDiags cu) (hPutStrLn stderr . renderDiag)
  if hasErrors (cuDiags cu) then exitFailure else exitSuccess

cmdRun :: FilePath -> IO ()
cmdRun path = do
  src <- TIO.readFile path
  let cu = compileSourceWithPrelude path src
  forM_ (cuDiags cu) (hPutStrLn stderr . renderDiag)
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
cmdTest :: FilePath -> IO ()
cmdTest path = do
  reports <- runTestPath path
  let s = summarize reports
  putStrLn $
    "total " <> show (length reports)
      <> ": " <> show (sPass s) <> " passed, "
      <> show (sFail s) <> " failed, "
      <> show (sUnsupported s) <> " unsupported, "
      <> show (sHarnessError s) <> " harness errors"
  if sFail s > 0 || sHarnessError s > 0 then exitFailure else exitSuccess
