-- | Cabal test-suite driver: runs the Appendix T conformance tree
-- under @tests/conformance@ through the in-process harness.
module Main (main) where

import Kappa.TestHarness (Summary (..), runTestPath, summarize)
import System.Directory (doesDirectoryExist)
import System.Exit (exitFailure)
import System.IO (BufferMode (..), hSetBuffering, stdout)

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  let root = "tests/conformance"
  exists <- doesDirectoryExist root
  if not exists
    then do
      putStrLn ("missing conformance tree: " <> root)
      exitFailure
    else do
      reports <- runTestPath root
      let s = summarize reports
      putStrLn $
        "total " <> show (length reports)
          <> ": " <> show (sPass s) <> " passed, "
          <> show (sFail s) <> " failed, "
          <> show (sUnsupported s) <> " unsupported, "
          <> show (sHarnessError s) <> " harness errors"
      if sFail s > 0 || sHarnessError s > 0
        then exitFailure
        else pure ()
