-- | Cabal test-suite driver: runs the Appendix T conformance tree
-- under @tests/conformance@ through the in-process harness, then
-- cross-checks the §3.1.2A diagnostic code registry against every
-- diagnostic code spelled in the implementation sources.
module Main (main) where

import Data.Char (isAsciiUpper, isDigit)
import Data.List (isSuffixOf, nub, sort)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Kappa.Explain (explainExists)
import Kappa.TestHarness (Summary (..), runTestPath, summarize)
import System.Directory (doesDirectoryExist, listDirectory)
import System.Exit (exitFailure)
import System.IO (BufferMode (..), hSetBuffering, stdout)

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  regOk <- registryComplete
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
      if sFail s > 0 || sHarnessError s > 0 || not regOk
        then exitFailure
        else pure ()

-- | §3.1.2A: "A diagnostic emitted in ordinary user-facing compilation
-- MUST NOT use an unregistered code." Every @\"E_...\"@ \/ @\"W_...\"@
-- string literal in the sources (emit sites and alias tables alike)
-- must be present in the 'Kappa.Explain' registry.
registryComplete :: IO Bool
registryComplete = do
  files <- haskellSources ["src/Kappa", "src/Kappa/Parser", "app"]
  codes <- concat <$> mapM (fmap codeLiterals . TIO.readFile) files
  let missing = sort (nub [c | c <- codes, not (explainExists c)])
  if null missing
    then pure True
    else do
      putStrLn "diagnostic codes missing from the §3.1.2A registry (Kappa.Explain):"
      mapM_ (putStrLn . ("  " <>) . T.unpack) missing
      pure False

haskellSources :: [FilePath] -> IO [FilePath]
haskellSources dirs =
  fmap concat . sequence $
    [ do
        ok <- doesDirectoryExist d
        if ok
          then map ((d <> "/") <>) . filter (".hs" `isSuffixOf`) <$> listDirectory d
          else pure []
    | d <- dirs
    ]

-- | All double-quoted string literals of shape @E_CODE@ \/ @W_CODE@.
codeLiterals :: T.Text -> [T.Text]
codeLiterals = go
  where
    go t = case T.breakOn "\"" t of
      (_, rest)
        | T.null rest -> []
        | otherwise ->
            let body = T.drop 1 rest
                (lit, rest') = T.breakOn "\"" body
             in [lit | isCode lit] ++ go (T.drop 1 rest')
    isCode c =
      (("E_" `T.isPrefixOf` c) || ("W_" `T.isPrefixOf` c))
        && T.length c > 2
        && T.all (\ch -> isAsciiUpper ch || isDigit ch || ch == '_') c
