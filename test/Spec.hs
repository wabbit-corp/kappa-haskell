-- | Cabal test-suite driver: runs the Appendix T conformance tree
-- under @tests/conformance@ through the in-process harness, then
-- cross-checks the §3.1.2A diagnostic code registry against every
-- diagnostic code spelled in the implementation sources.
module Main (main) where

import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.List (isSuffixOf, nub, sort)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Kappa.Explain (ExplainEntry (..), explainExists, registry)
import Kappa.TestHarness (Summary (..), runTestPath, summarize)
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory)
import System.Exit (exitFailure)
import System.IO (BufferMode (..), hSetBuffering, stdout)

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  regOk0 <- registryComplete
  famOk <- familiesHygienic
  let regOk = regOk0 && famOk
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

-- | §3.1.2/§3.1.2A family-namespace hygiene: the @kappa.@ namespace is
-- reserved for the specification, so every family literal in the
-- sources that begins with @kappa.@ must be a spelling Spec.md itself
-- defines; implementation-defined families must use this
-- implementation's reserved prefix (@kappa-hs.@); and every family
-- spelled at an emission site must be carried by some registry entry.
familiesHygienic :: IO Bool
familiesHygienic = do
  files <- haskellSources ["src/Kappa", "src/Kappa/Parser", "app"]
  fams <- concat <$> mapM (fmap familyLiterals . TIO.readFile) files
  hasSpec <- doesFileExist "docs/Spec.md"
  specFams <-
    if hasSpec
      then specFamilyTokens <$> TIO.readFile "docs/Spec.md"
      else pure []
  let emitted = sort (nub fams)
      squatting =
        [ f | f <- emitted, "kappa." `T.isPrefixOf` f
        , hasSpec, f `notElem` specFams
        ]
      misprefixed =
        [ f | f <- emitted
        , not ("kappa." `T.isPrefixOf` f)
        , not ("kappa-hs." `T.isPrefixOf` f)
        ]
      unregistered =
        [f | f <- emitted, not (any ((== Just f) . eeFamily) registry)]
      bad =
        [ (m, fs)
        | (m, fs) <-
            [ ("families squatting the reserved kappa. namespace without a Spec.md spelling:", squatting)
            , ("families outside both kappa. and the kappa-hs. implementation prefix:", misprefixed)
            , ("families at emission sites missing from the §3.1.2A registry (Kappa.Explain):", unregistered)
            ]
        , not (null fs)
        ]
  if null bad
    then pure True
    else do
      mapM_
        (\(m, fs) -> putStrLn m >> mapM_ (putStrLn . ("  " <>) . T.unpack) fs)
        bad
      pure False

-- | Every @kappa.…@ dotted token spelled anywhere in Spec.md (the
-- standardized family spellings, plus harmless non-family tokens that
-- never collide with emitted families).
specFamilyTokens :: T.Text -> [T.Text]
specFamilyTokens = go
  where
    go t = case T.breakOn "kappa." t of
      (_, rest)
        | T.null rest -> []
        | otherwise ->
            let tok = T.dropWhileEnd (`elem` (".-" :: String)) (T.takeWhile famChar rest)
             in tok : go (T.drop 6 rest)

-- | All double-quoted string literals that are family spellings
-- (@kappa.…@ or @kappa-hs.…@).
familyLiterals :: T.Text -> [T.Text]
familyLiterals = go
  where
    go t = case T.breakOn "\"" t of
      (_, rest)
        | T.null rest -> []
        | otherwise ->
            let body = T.drop 1 rest
                (lit, rest') = T.breakOn "\"" body
             in [lit | isFam lit] ++ go (T.drop 1 rest')
    isFam f =
      (("kappa." `T.isPrefixOf` f) || ("kappa-hs." `T.isPrefixOf` f))
        && T.all famChar f
        && f `notElem` ["kappa.", "kappa-hs."] -- bare prefix-test literals

famChar :: Char -> Bool
famChar ch = isAsciiLower ch || isDigit ch || ch == '.' || ch == '-'

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

-- | All double-quoted string literals of shape @E_CODE@ \/ @W_CODE@,
-- plus the spec-spelled @KAPPA_…@ codes of §22 shape reflection.
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
      any
        (\p -> p `T.isPrefixOf` c && T.length c > T.length p)
        ["E_", "W_", "KAPPA_"]
        && T.all (\ch -> isAsciiUpper ch || isDigit ch || ch == '_') c
