-- | Native-backend build driver: turn an elaborated 'CheckState' into a
-- native executable by generating C (via "Kappa.Backend.C"), locating the
-- @kappart@ runtime, detecting a C toolchain, and invoking it.
--
-- The driver never compiles code the front end rejected, and it surfaces
-- both unsupported-construct findings ('E_BACKEND_UNSUPPORTED') and C
-- toolchain failures as structured diagnostics.  See docs/NATIVE_BACKEND.md.
module Kappa.Backend.Driver
  ( BuildOptions (..)
  , FfiUnit (..)
  , defaultBuildOptions
  , buildNative
  ) where

import qualified Data.Text as T
import qualified Data.Set as Set
import qualified Data.Text.IO as TIO
import Kappa.Backend.C (backendDiagnostics, generateC)
import Kappa.Backend.Ffi (ffiPrimNames)
import Kappa.Check (CheckState)
import Kappa.Core (GName)
import Kappa.Diagnostic
import Kappa.Source (Pos (..), Span (..))
import System.Directory
  ( createDirectoryIfMissing
  , doesFileExist
  , findExecutable
  , getCurrentDirectory
  , makeAbsolute
  )
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath (takeDirectory, takeFileName, (</>))
import System.Process (readProcessWithExitCode)

-- | Which FFI runtime unit to link: the no-FFI stub, or the full
-- POSIX-sockets + sqlite3 unit needed by the HTTP demo.
data FfiUnit = FfiStub | FfiFull
  deriving stock (Eq, Show)

data BuildOptions = BuildOptions
  { boOutput :: !(Maybe FilePath) -- ^ output path (default: input basename)
  , boEmitCOnly :: !Bool -- ^ write the generated C and stop
  , boCC :: !(Maybe String) -- ^ explicit C driver override
  , boExtraLibs :: ![String] -- ^ extra linker flags, e.g. ["-lsqlite3"]
  , boFfiUnit :: !FfiUnit
  , boWorkDir :: !(Maybe FilePath) -- ^ directory for generated artifacts
  }

defaultBuildOptions :: BuildOptions
defaultBuildOptions =
  BuildOptions
    { boOutput = Nothing
    , boEmitCOnly = False
    , boCC = Nothing
    , boExtraLibs = []
    , boFfiUnit = FfiStub
    , boWorkDir = Nothing
    }

-- | Build a native executable for @mainG@.  On success returns the path to
-- the produced artifact (the executable, or the generated @.c@ under
-- @--emit-c@).  On failure returns structured diagnostics.
buildNative :: CheckState -> GName -> FilePath -> BuildOptions -> IO (Either Diagnostics FilePath)
buildNative cs mainG inputPath opts =
  let ffiPrims = case boFfiUnit opts of
        FfiStub -> Set.empty
        FfiFull -> ffiPrimNames
   in case generateC cs mainG ffiPrims of
    Left errs -> pure (Left (backendDiagnostics errs))
    Right csource -> do
      mruntime <- findRuntimeDir
      case mruntime of
        Nothing -> pure (Left [toolDiag noRuntimeMsg])
        Just runtimeDir -> do
          workDir <- maybe (pure (takeDirectory inputPath)) pure (boWorkDir opts)
          createDirectoryIfMissing True workDir
          let base = dropExtensionSafe (takeFileName inputPath)
              cPath = workDir </> (base ++ ".kappa.c")
          TIO.writeFile cPath csource
          if boEmitCOnly opts
            then pure (Right cPath)
            else linkExecutable cs mainG opts runtimeDir cPath base workDir

linkExecutable
  :: CheckState -> GName -> BuildOptions -> FilePath -> FilePath -> String -> FilePath
  -> IO (Either Diagnostics FilePath)
linkExecutable _cs _mainG opts runtimeDir cPath base workDir = do
  mcc <- detectCC (boCC opts)
  case mcc of
    Nothing -> pure (Left [toolDiag noCcMsg])
    Just (ccExe, ccLead) -> do
      let outPath = maybe (workDir </> base) id (boOutput opts)
          ffiSrc = case boFfiUnit opts of
            FfiStub -> runtimeDir </> "kappart_ffi_stub.c"
            FfiFull -> runtimeDir </> "kappart_ffi.c"
          args =
            ccLead
              ++ [ "-std=c11"
                 -- Disable FP contraction (no implicit FMA fusion) so the
                 -- backend's unboxed double arithmetic rounds per-operation
                 -- exactly like the interpreter's (and the boxed kp_*Double
                 -- prims), making native ≡ interpreter for Double bit-for-bit
                 -- regardless of the -O level (R2.2 / §27 semantics).
                 , "-ffp-contract=off"
                 , "-I", runtimeDir
                 , cPath
                 , runtimeDir </> "kappart.c"
                 , ffiSrc
                 , "-lgc"
                 , "-lgmp" -- unbounded Integer (§6); see docs/NATIVE_BACKEND.md
                 ]
              ++ boExtraLibs opts
              ++ ["-o", outPath]
      (ec, out, err) <- readProcessWithExitCode ccExe args ""
      case ec of
        ExitSuccess -> pure (Right outPath)
        ExitFailure n ->
          pure (Left [toolDiag (ccFailMsg ccExe n (out ++ err))])

-- ── Toolchain / runtime discovery ────────────────────────────────────

-- | Detect a C driver.  Order: explicit @--cc@, then @$KAPPA_CC@ (may be
-- multi-word, e.g. @"zig cc"@), then @zig@ → @zig cc@, then @cc@, @gcc@,
-- @clang@.  Returns @(executable, leading-args)@.
detectCC :: Maybe String -> IO (Maybe (String, [String]))
detectCC explicit = do
  envCC <- lookupEnv "KAPPA_CC"
  let candidates =
        [explicit | Just _ <- [explicit]]
          ++ [envCC | Just _ <- [envCC]]
  case [c | Just c <- candidates] of
    (c : _) -> pure (splitCC c)
    [] -> do
      mzig <- findExecutable "zig"
      case mzig of
        Just z -> pure (Just (z, ["cc"]))
        Nothing -> firstExe ["cc", "gcc", "clang"]
  where
    firstExe [] = pure Nothing
    firstExe (x : xs) = do
      m <- findExecutable x
      case m of
        Just p -> pure (Just (p, []))
        Nothing -> firstExe xs

-- | Split a (possibly multi-word) driver spec into executable + leading
-- args (e.g. @"zig cc"@ → @("zig", ["cc"])@).
splitCC :: String -> Maybe (String, [String])
splitCC s = case words s of
  [] -> Nothing
  (x : xs) -> Just (x, xs)

-- | Locate the @kappart@ runtime directory: @$KAPPA_RUNTIME_DIR@, then a
-- @runtime/@ holding @kappart.h@ found by walking up from the CWD.
findRuntimeDir :: IO (Maybe FilePath)
findRuntimeDir = do
  menv <- lookupEnv "KAPPA_RUNTIME_DIR"
  case menv of
    Just d -> do
      ok <- doesFileExist (d </> "kappart.h")
      pure (if ok then Just d else Nothing)
    Nothing -> do
      cwd <- getCurrentDirectory
      walkUp cwd
  where
    walkUp dir = do
      let cand = dir </> "runtime"
      ok <- doesFileExist (cand </> "kappart.h")
      if ok
        then Just <$> makeAbsolute cand
        else
          let parent = takeDirectory dir
           in if parent == dir then pure Nothing else walkUp parent

-- ── helpers ──────────────────────────────────────────────────────────

dropExtensionSafe :: FilePath -> FilePath
dropExtensionSafe f = case break (== '.') f of
  (b, _) | not (null b) -> b
  _ -> f

toolDiag :: T.Text -> Diagnostic
toolDiag msg =
  diag SevError StageElaborate "E_BACKEND_TOOLCHAIN" (Just "kappa-hs.backend.toolchain")
    (Span "<native-backend>" (Pos 1 1) (Pos 1 1))
    msg

noRuntimeMsg :: T.Text
noRuntimeMsg =
  "could not locate the kappart runtime: set $KAPPA_RUNTIME_DIR to the \
  \directory containing kappart.h, or run from a checkout containing runtime/ \
  \(Spec §27.7 backends are profile-scoped; see docs/NATIVE_BACKEND.md)"

noCcMsg :: T.Text
noCcMsg =
  "no C toolchain found: set $KAPPA_CC (e.g. to 'zig cc' or 'cc'), or install \
  \one of zig, cc, gcc, clang on PATH (see docs/NATIVE_BACKEND.md §7)"

ccFailMsg :: String -> Int -> String -> T.Text
ccFailMsg cc n output =
  "the C toolchain (" <> T.pack cc <> ") failed with exit code " <> T.pack (show n)
    <> (if null output then "" else ":\n" <> T.pack (trimOutput output))
  where
    -- keep the diagnostic bounded; show the tail (where the real error is)
    trimOutput o
      | length o <= 4000 = o
      | otherwise = "...\n" ++ drop (length o - 4000) o

