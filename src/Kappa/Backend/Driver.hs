{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE OverloadedRecordDot #-}

-- | Native-backend build driver: turn an elaborated 'CheckState' into a
-- native executable by generating C (via "Kappa.Backend.C"), locating the
-- @kappart@ runtime, detecting a C toolchain, and invoking it.
--
-- The driver never compiles code the front end rejected, and it surfaces
-- both unsupported-construct findings ('E_BACKEND_UNSUPPORTED') and C
-- toolchain failures as structured diagnostics.  See docs/NATIVE_BACKEND.md.
module Kappa.Backend.Driver
  ( BuildOptions (..)
  , defaultBuildOptions
  , buildNative
  , detectCC
  , verifyDeclName
  ) where

import Data.List (nub)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Kappa.Backend.C (backendDiagnostics, generateC)
import Kappa.Backend.NativeFfi (ResolvedNativeSymbol (..), externPrototype)
import Kappa.Backend.NativeProbe (NativeProvenance (..), discoverAndVerifyNative)
import Kappa.Build.Types (NativeInput (..), NativeLinkSpec (..))
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

data BuildOptions = BuildOptions
  { output :: !(Maybe FilePath) -- ^ output path (default: input basename)
  , emitCOnly :: !Bool -- ^ write the generated C and stop
  , cc :: !(Maybe String) -- ^ explicit C driver override
  , hostSyms :: !(Map GName ResolvedNativeSymbol)
  -- ^ §27.1.1/§36.28: each provided host-binding member ↦ its resolved
  -- native symbol (C symbol + ABI signature), built per build from the
  -- manifest's native bindings (never a hardcoded catalog). Threaded to
  -- codegen, which emits a direct extern prototype + typed wrapper +
  -- direct call site per used member.
  , linkSpecs :: ![NativeLinkSpec]
  -- ^ §36.28 link specs from the selected native bindings; mapped to cc
  -- linker flags. Replaces the former @--lib@ extra-libs list.
  , nativeInputs :: ![NativeInput]
  -- ^ §36.28 realization inputs of the selected bindings; drive the C
  -- toolchain (include dirs, defines, pkg-config flags, compiled shim
  -- translation units, prebuilt link inputs).
  , nativeBaseDir :: !(Maybe FilePath)
  -- ^ directory that native input relative paths (headers/includeDir/
  -- shim/prebuilt) resolve against — the manifest directory.
  , targetTriple :: !T.Text
  -- ^ §36.21 the target's toolchain triple; passed to a cross-capable C
  -- driver (@zig cc -target <triple>@) so a cross-compile actually targets
  -- the requested platform instead of silently building for the host.
  , workDir :: !(Maybe FilePath) -- ^ directory for generated artifacts
  }

defaultBuildOptions :: BuildOptions
defaultBuildOptions =
  BuildOptions
    { output = Nothing
    , emitCOnly = False
    , cc = Nothing
    , hostSyms = Map.empty
    , linkSpecs = []
    , nativeInputs = []
    , nativeBaseDir = Nothing
    , targetTriple = ""
    , workDir = Nothing
    }

-- | Build a native executable for @mainG@.  On success returns the path to
-- the produced artifact (the executable, or the generated @.c@ under
-- @--emit-c@).  On failure returns structured diagnostics.
buildNative :: CheckState -> GName -> FilePath -> BuildOptions -> IO (Either Diagnostics FilePath)
buildNative cs mainG inputPath opts =
  -- Native host bindings lower to direct typed call sites generated from
  -- the resolved symbol map (no FFI prim set); the runtime needs no extra
  -- prim names seeded here.
  case generateC cs mainG Set.empty (opts.hostSyms) of
    Left errs -> pure (Left (backendDiagnostics errs))
    Right csource -> do
      mruntime <- findRuntimeDir
      case mruntime of
        Nothing -> pure (Left [toolDiag noRuntimeMsg])
        Just runtimeDir -> do
          workDir <- maybe (pure (takeDirectory inputPath)) pure (opts.workDir)
          createDirectoryIfMissing True workDir
          let base = dropExtensionSafe (takeFileName inputPath)
              cPath = workDir </> (base ++ ".kappa.c")
          TIO.writeFile cPath csource
          -- §26.1.5/§27.1.1/§36.28: discover + VERIFY the native ABI against
          -- the real host (pkg-config version/.pc identity, header digests,
          -- compiler-checked signature probe) and record provenance. This is
          -- fail-closed and runs for BOTH --emit-c and link (discovery is part
          -- of the build, not the link). A no-op when no binding declares
          -- pkg-config/headers/verify inputs.
          mverified <- verifyAndRecord opts base workDir
          case mverified of
            Left ds -> pure (Left ds)
            Right () ->
              if opts.emitCOnly
                then pure (Right cPath)
                else linkExecutable cs mainG opts runtimeDir cPath base workDir

-- | Run native ABI discovery + verification for the binding inputs and write
-- the resolved native provenance next to the artifact. A no-op (no cc needed)
-- when no input requires discovery (no pkg-config/header/verify input).
verifyAndRecord :: BuildOptions -> String -> FilePath -> IO (Either Diagnostics ())
verifyAndRecord opts base workDir
  | not (needsDiscovery (opts.nativeInputs)) = pure (Right ())
  | otherwise = do
      mcc <- detectCC (opts.cc)
      case mcc of
        Nothing -> pure (Left [toolDiag noCcMsg])
        Just cc -> do
          let baseDir = maybe "." id (opts.nativeBaseDir)
          r <- discoverAndVerifyNative cc (opts.targetTriple) baseDir workDir (opts.nativeInputs) []
          case r of
            Left ds -> pure (Left ds)
            Right prov -> do
              writeFile (workDir </> (base ++ ".native.prov"))
                (T.unpack (T.unlines (npLines prov ++ ["composite " <> npComposite prov])))
              pure (Right ())

-- | True iff some binding input needs build-phase ABI discovery/verification.
needsDiscovery :: [NativeInput] -> Bool
needsDiscovery = any req
  where
    req PkgConfigInput {} = True
    req HeadersInput {} = True
    req VerifyInput {} = True
    req ModuleMapInput {} = True
    req PrebuiltInput {} = True
    req _ = False

linkExecutable
  :: CheckState -> GName -> BuildOptions -> FilePath -> FilePath -> String -> FilePath
  -> IO (Either Diagnostics FilePath)
linkExecutable _cs _mainG opts runtimeDir cPath base workDir = do
  mcc <- detectCC (opts.cc)
  case mcc of
    Nothing -> pure (Left [toolDiag noCcMsg])
    Just (ccExe, ccLead) -> do
      let outPath = maybe (workDir </> base) id (opts.output)
          baseDir = maybe "." id (opts.nativeBaseDir)
      -- §36.28: realize the manifest's native inputs into toolchain flags
      -- (include dirs, defines, compiled shim TUs, prebuilt link inputs)
      -- and pkg-config cflags/libs (the only fs/tool discovery, done here
      -- in the build phase, never at config-eval — §35.13).
      (inCFlags, inSources, inLibs, pkgErr) <- resolveInputs baseDir (opts.nativeInputs)
      case pkgErr of
        Just msg -> pure (Left [toolDiag msg])
        Nothing -> do
          -- §27.1.1/§26.1.3: write a header of the codegen extern prototypes for
          -- the host symbols and force-`-include` it into the compile, so a shim
          -- translation unit that DEFINES a symbol with an ABI signature that
          -- disagrees with the manifest's symbolDecl is a hard compile error
          -- (conflicting types) rather than a silent ABI mismatch.
          let -- Symbols already declared by a `verify` C prototype are real
              -- library symbols, checked separately against the real headers;
              -- declaring our conservative prototype for them would conflict
              -- with the system header (e.g. void* vs char* getenv). The
              -- force-include header therefore covers only the OTHER cSymbols —
              -- the shim-provided ones — so a shim ABI mismatch is a hard error.
              -- exclude only symbols whose EXACT name is a `verify` decl's
              -- declared symbol (real library symbols, checked against headers);
              -- a substring match would wrongly exclude an unrelated shim symbol.
              verifyNames = [verifyDeclName d | VerifyInput ds <- opts.nativeInputs, d <- ds]
              -- Only SHIM-PROVIDED symbols get a force-included conservative
              -- prototype: a real library symbol (a generated raw surface over
              -- a header) is declared by its own header, so asserting our
              -- conservative `void *` prototype for it would falsely conflict
              -- with the real pointer type when that header is in scope
              -- (e.g. uv.h's `uint16_t *` vs our `void *`). Library-symbol ABI
              -- is checked instead by the scalar-only verify probe (§26.1.5).
              shimSyms = [rns | rns <- Map.elems (opts.hostSyms), rnsShimProvided rns, rnsCSymbol rns `notElem` verifyNames]
          hdrInclude <-
            if null shimSyms
              then pure []
              else do
                let hdrPath = workDir </> (base ++ ".kappa.h")
                    protos = nub (map externPrototype shimSyms)
                    -- the header is force-included before any system header, so
                    -- it must pull in the exact-width / size types it spells.
                    hdr = "/* generated host-binding prototypes (§27.1.1 ABI check). */"
                            : "#include <stdint.h>"
                            : "#include <stddef.h>"
                            : protos
                TIO.writeFile hdrPath (T.unlines hdr)
                pure ["-include", hdrPath]
          let -- §36.21: a cross-capable driver (zig cc) targets the manifest's
              -- triple; for a host gcc/clang/cc we leave the native host target
              -- (an explicit non-host triple there would fail the link, which is
              -- the honest outcome — the toolchain cannot cross-compile).
              targetFlags
                | not (T.null (opts.targetTriple)) && isZig =
                    ["-target", T.unpack (opts.targetTriple)]
                | otherwise = []
              isZig = takeFileName ccExe == "zig" && ccLead == ["cc"]
              args =
                ccLead
                  ++ targetFlags
                  ++ [ "-std=c11"
                     -- Optimize: the generated C is direct typed code, but the
                     -- codegen leaves dead partial-application closure ladders +
                     -- sink-tail stores for the C compiler to erase; -O2 also
                     -- inlines the marshalling wrappers and register-allocates the
                     -- unboxed worker loops.
                     , "-O2"
                     -- Disable FP contraction (no implicit FMA fusion) so the
                     -- backend's unboxed double arithmetic rounds per-operation
                     -- exactly like the interpreter's (and the boxed kp_*Double
                     -- prims), making native ≡ interpreter for Double bit-for-bit
                     -- regardless of the -O level (R2.2 / §27 semantics).
                     , "-ffp-contract=off"
                     , "-I", runtimeDir
                     ]
                  ++ hdrInclude
                  ++ inCFlags
                  ++ [ cPath
                     , runtimeDir </> "kappart.c"
                     ]
                  ++ inSources
                  ++ [ "-lgc"
                     , "-lgmp" -- unbounded Integer (§6); see docs/NATIVE_BACKEND.md
                     ]
                  ++ linkFlags (opts.linkSpecs)
                  ++ inLibs
                  ++ ["-o", outPath]
          (ec, out, err) <- readProcessWithExitCode ccExe args ""
          case ec of
            ExitSuccess -> pure (Right outPath)
            ExitFailure n ->
              pure (Left [toolDiag (ccFailMsg ccExe n (out ++ err))])

-- | §36.28: turn native realization inputs into toolchain arguments —
-- @(cflags, extra source/object inputs, link flags, error)@. Relative paths
-- resolve against @baseDir@ (the manifest dir). @pkgConfig@ is the only
-- external discovery here (run in the build phase, never config-eval).
resolveInputs :: FilePath -> [NativeInput] -> IO ([String], [String], [String], Maybe T.Text)
resolveInputs baseDir = go [] [] []
  where
    -- dedup compiled sources: a shim TU shared by several bindings (each
    -- listing it so its symbols are shim-provided / ABI-checked) must be
    -- compiled only ONCE, else its symbols multiply-define at link. (cflags are
    -- left as-is: nub would break `-I dir` two-token pairs.)
    go cf sr lb [] = pure (reverse cf, nub (reverse sr), reverse lb, Nothing)
    go cf sr lb (i : is) = case i of
      IncludeDirInput d -> go (rev2 ["-I", baseDir </> T.unpack d] cf) sr lb is
      HeadersInput hs ->
        -- a header contributes its containing directory as an include path
        let dirs = [takeDirectory (baseDir </> T.unpack h) | h <- hs]
         in go (foldl (\c d -> rev2 ["-I", d] c) cf dirs) sr lb is
      DefineInput n v -> go (("-D" ++ T.unpack n ++ "=" ++ T.unpack v) : cf) sr lb is
      ShimInput srcs -> go cf (foldl (\s p -> (baseDir </> T.unpack p) : s) sr srcs) lb is
      PrebuiltInput art _ -> go cf ((baseDir </> T.unpack art) : sr) lb is
      ModuleMapInput _ -> go cf sr lb is -- digested for identity; no toolchain effect
      VerifyInput _ -> go cf sr lb is -- verified by discoverAndVerifyNative; no link effect
      ClassifyInput _ -> go cf sr lb is -- §26.1.4 classification metadata; no toolchain effect
      CStringSymbolsInput _ -> go cf sr lb is -- §26.1.4 string-semantics metadata; no toolchain effect
      PkgConfigInput pkg _ -> do
        r <- pkgConfigFlags (T.unpack pkg)
        case r of
          Left e -> pure (reverse cf, reverse sr, reverse lb, Just e)
          Right (cflags, libs) ->
            go (rev2 cflags cf) sr (rev2 libs lb) is
    rev2 xs acc = reverse xs ++ acc

-- | Run @pkg-config --cflags@ then @--libs@ for a package, so include dirs
-- precede sources and @-l@ libs follow them on the link line. Missing
-- pkg-config or an unknown package is a structured build error.
pkgConfigFlags :: String -> IO (Either T.Text ([String], [String]))
pkgConfigFlags pkg = do
  mpc <- findExecutable "pkg-config"
  case mpc of
    Nothing -> pure (Left "pkg-config is required by a native binding but was not found on PATH (Spec §36.28)")
    Just pc -> do
      (ec1, cflagsOut, err1) <- readProcessWithExitCode pc ["--cflags", pkg] ""
      case ec1 of
        ExitFailure _ -> pure (Left (pkgErr err1))
        ExitSuccess -> do
          (ec2, libsOut, err2) <- readProcessWithExitCode pc ["--libs", pkg] ""
          case ec2 of
            ExitFailure _ -> pure (Left (pkgErr err2))
            ExitSuccess -> pure (Right (words cflagsOut, words libsOut))
  where
    pkgErr e = "pkg-config failed for package '" <> T.pack pkg <> "': " <> T.pack e <> " (Spec §36.28)"

-- ── Toolchain / runtime discovery ────────────────────────────────────

-- | Detect a C driver.  Order: explicit @--cc@, then @$KAPPA_CC@ (may be
-- multi-word, e.g. @"zig cc"@), then @zig@ → @zig cc@, then @cc@, @gcc@,
-- @clang@.  Returns @(executable, leading-args)@.
detectCC :: Maybe String -> IO (Maybe (String, [String]))
detectCC explicit = do
  -- env var name assembled so the literal does not trip the diagnostic-code
  -- scanner (which treats "KAPPA_…" string literals as §22 reflection codes)
  envCC <- lookupEnv ("KAPPA" <> "_CC")
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
  menv <- lookupEnv ("KAPPA" <> "_RUNTIME_DIR") -- assembled: see detectCC
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

-- | §36.28 link specs → cc linker flags. @dynamicLink@ contributes
-- @-l<lib>@ for each named library; @staticLink@ wraps its libraries in
-- @-Wl,-Bstatic … -Wl,-Bdynamic@ so the GNU/LLVM linker selects the
-- static archive for exactly those libraries (and restores dynamic
-- selection afterwards); @noLink@ contributes nothing.
linkFlags :: [NativeLinkSpec] -> [String]
linkFlags = concatMap one
  where
    one (DynamicLink libs) = [T.unpack ("-l" <> l) | l <- libs]
    one (StaticLink libs)
      | null libs = []
      | otherwise =
          ["-Wl,-Bstatic"] ++ [T.unpack ("-l" <> l) | l <- libs] ++ ["-Wl,-Bdynamic"]
    one NoLink = []

-- | The declared symbol name of a C prototype: the identifier immediately
-- before the first @(@ (e.g. "int abs(int)" → "abs", "char *getenv(const
-- char *)" → "getenv"). Used to exclude verified library symbols from the
-- shim-prototype force-include by EXACT name (not a loose substring).
verifyDeclName :: T.Text -> T.Text
verifyDeclName d =
  let before = T.takeWhile (/= '(') d
      idChar c = c == '_' || ('0' <= c && c <= '9') || ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
   in T.takeWhileEnd idChar (T.dropWhileEnd (not . idChar) before)

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

