-- | Native ABI discovery + verification + provenance (§26.1.5, §27.1.1,
-- §36.28). This is the build-phase realization of a manifest's native
-- binding inputs — it is the ONLY place that touches pkg-config, the real
-- headers, and the C toolchain to PROVE that the binding's declared host
-- ABI matches the real host, and to record the identity inputs that affect
-- the generated interface (§36.6A reproducibility).
--
-- It performs, fail-closed:
--   * pkg-config discovery — @--exists@, @--modversion@, @--atleast-version@
--     (enforces a manifest @minVersion@), @--cflags@/@--libs@, and locates +
--     hashes the actual @.pc@ file (Spec §36.28 pkg-config provider identity);
--   * header location + hashing — each declared header is found on the
--     resolved include path and hashed (§27.1.1 header digests);
--   * signature verification — a probe translation unit @#include@s the real
--     headers and redeclares each @verify@ C prototype; the C compiler rejects
--     any declaration incompatible with the real header (conflicting types),
--     so the manifest's symbol surface is CHECKED against the real ABI rather
--     than trusted (§26.1.5/§36.28);
-- and returns a 'NativeProvenance' recording every identity input (pkg-config
-- package+version+.pc digest, header digests, verified decls, defines, target)
-- for the build's provenance + lockfile.
module Kappa.Backend.NativeProbe
  ( NativeProvenance (..)
  , discoverAndVerifyNative
  , hostBindingLockEntries
  ) where

import qualified Data.ByteString as BS
import Data.List (nub)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Encoding (encodeUtf8)
import Kappa.Build.Lock (LockEntry (..), contentId)
import Kappa.Build.Types (NativeInput (..))
import Kappa.Diagnostic
import Kappa.Source (Pos (..), Span (..))
import Control.Exception (catch, SomeException)
import System.Directory (doesFileExist, findExecutable, pathIsSymbolicLink, removeFile)
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath (isAbsolute, splitDirectories, splitSearchPath, (</>))
import System.Process (readProcessWithExitCode)

-- | The recorded identity of a build's resolved native bindings: ordered,
-- human-readable identity lines plus a single composite content digest over
-- them (so a change to any input — pkg-config version, a header's bytes, a
-- verified declaration, a define — changes the build's native identity).
data NativeProvenance = NativeProvenance
  { npLines :: ![Text]
  , npComposite :: !Text
  }
  deriving stock (Eq, Show)

-- | Run discovery + verification for the selected bindings' inputs. On any
-- failure (pkg-config missing / version too old / header missing / a declared
-- signature that disagrees with the real header) returns a fail-closed
-- diagnostic. @cc@ is the detected C driver @(exe, leadingArgs)@; @baseDir@ is
-- the manifest directory (header/relative paths resolve against it); @workDir@
-- holds the generated probe TU.
discoverAndVerifyNative
  :: (String, [String]) -> FilePath -> FilePath -> [NativeInput]
  -> IO (Either Diagnostics NativeProvenance)
discoverAndVerifyNative (ccExe, ccLead) baseDir workDir inputs = do
  let pkgs = [(p, mv) | PkgConfigInput p mv <- inputs]
      hdrs = concat [hs | HeadersInput hs <- inputs]
      incDirs = [d | IncludeDirInput d <- inputs]
      defines = [(n, v) | DefineInput n v <- inputs]
      decls = concat [ds | VerifyInput ds <- inputs]
  -- 1. pkg-config discovery (version identity + flags), fail-closed.
  epkg <- runAll (map (pkgConfig) pkgs)
  case epkg of
    Left ds -> pure (Left ds)
    Right pkgResults -> do
      let pkgCflags = concat [c | PkgInfo {piCflags = c} <- pkgResults]
          pkgLines = concatMap pkgProvLines pkgResults
      -- 2. header location + hashing on the resolved include path.
      let cflagIncs = [drop 2 f | f <- pkgCflags, take 2 f == "-I"]
          searchDirs = nub (baseDir : map (resolve baseDir) incDirs ++ cflagIncs ++ systemIncludeDirs)
      ehdr <- runAll [locateHash searchDirs (T.unpack h) | h <- hdrs]
      case ehdr of
        Left ds -> pure (Left ds)
        Right hdrResults -> do
          -- 3. signature verification: a probe TU that includes the real
          -- headers and redeclares each verify decl; cc rejects a mismatch.
          let defLines = [T.pack ("-D" <> T.unpack n <> "=" <> T.unpack v) | (n, v) <- defines]
          ever <- verifyDecls ccExe ccLead workDir baseDir searchDirs pkgCflags (map T.unpack defLines) hdrs decls
          case ever of
            Left ds -> pure (Left ds)
            Right verLines -> do
              -- 4. module-map digests (§27.1.1 host-source identity input).
              let moduleMaps = concat [ms | ModuleMapInput ms <- inputs]
              emm <- runAll [digestRel baseDir "module-map" (T.unpack m) | m <- moduleMaps]
              -- 5. prebuilt artifacts: digest + VERIFY any declared expected
              -- identity, fail-closed (§36.28/§36.6 — never trust unverified bytes).
              eprebuilt <- runAll [verifyPrebuilt baseDir a e | PrebuiltInput a e <- inputs]
              case (emm, eprebuilt) of
                (Left ds, _) -> pure (Left ds)
                (_, Left ds) -> pure (Left ds)
                (Right mmLines, Right pbLines) -> do
                  let allLines =
                        pkgLines
                          ++ [hdrLine r | r <- hdrResults]
                          ++ verLines
                          ++ mmLines
                          ++ pbLines
                          ++ ["define " <> n <> "=" <> v | (n, v) <- defines]
                      composite = contentId [("native-identity", encodeLines allLines)]
                  pure (Right (NativeProvenance allLines composite))
  where
    encodeLines ls = BS.intercalate (BS.singleton 10) (map encodeUtf8 ls)

-- ── pkg-config ─────────────────────────────────────────────────────────

data PkgInfo = PkgInfo
  { piName :: !Text
  , piVersion :: !Text
  , piPcPath :: !(Maybe FilePath)
  , piPcDigest :: !(Maybe Text)
  , piCflags :: ![String]
  , piLibs :: ![String]
  }

pkgProvLines :: PkgInfo -> [Text]
pkgProvLines pi_ =
  [ "pkg-config " <> piName pi_ <> " version=" <> piVersion pi_
      <> maybe "" (\d -> " pc-digest=" <> d) (piPcDigest pi_)
      <> maybe "" (\p -> " pc=" <> T.pack p) (piPcPath pi_)
  ]

pkgConfig :: (Text, Maybe Text) -> IO (Either Diagnostics PkgInfo)
pkgConfig (pkg, mMin) = do
  mpc <- findExecutable "pkg-config"
  case mpc of
    Nothing ->
      pure (Left [pErr ("pkg-config is required by native binding package '" <> pkg <> "' but was not found on PATH")])
    Just pc -> do
      let p = T.unpack pkg
      (ecEx, _, _) <- readProcessWithExitCode pc ["--exists", p] ""
      case ecEx of
        ExitFailure _ ->
          pure (Left [pErr ("pkg-config could not find package '" <> pkg <> "' (no .pc on PKG_CONFIG_PATH)")])
        ExitSuccess -> do
          -- minVersion: pkg-config itself is authoritative (--atleast-version)
          minOk <- case mMin of
            Nothing -> pure (Right ())
            Just mn -> do
              (ec, _, _) <- readProcessWithExitCode pc ["--atleast-version=" <> T.unpack mn, p] ""
              pure $ case ec of
                ExitSuccess -> Right ()
                ExitFailure _ -> Left mn
          case minOk of
            Left mn -> do
              (_, vout, _) <- readProcessWithExitCode pc ["--modversion", p] ""
              pure (Left [pErr ("native binding package '" <> pkg <> "' resolves to version " <> T.strip (T.pack vout) <> " but the manifest requires at least " <> mn <> " (Spec §36.28)")])
            Right () -> do
              (_, vout, _) <- readProcessWithExitCode pc ["--modversion", p] ""
              (_, cfl, _) <- readProcessWithExitCode pc ["--cflags", p] ""
              (_, lbs, _) <- readProcessWithExitCode pc ["--libs", p] ""
              (mPath, mDig) <- locatePc p
              pure $ Right PkgInfo
                { piName = pkg
                , piVersion = T.strip (T.pack vout)
                , piPcPath = mPath
                , piPcDigest = mDig
                , piCflags = words cfl
                , piLibs = words lbs
                }

-- | Locate the package's @.pc@ file on @PKG_CONFIG_PATH@ + standard dirs and
-- hash its bytes (the pkg-config provider identity input, §36.28). Returns
-- @(Nothing, Nothing)@ if not locatable (the package version still pins it).
locatePc :: String -> IO (Maybe FilePath, Maybe Text)
locatePc pkg = do
  menv <- lookupEnv "PKG_CONFIG_PATH"
  let envDirs = maybe [] splitSearchPath menv
      dirs = envDirs ++ pkgConfigStdDirs
      cands = [d </> (pkg <> ".pc") | d <- dirs]
  found <- firstExisting cands
  case found of
    Nothing -> pure (Nothing, Nothing)
    Just p -> do
      bs <- BS.readFile p
      pure (Just p, Just (contentId [(p, bs)]))

pkgConfigStdDirs :: [FilePath]
pkgConfigStdDirs =
  [ "/usr/lib/pkgconfig", "/usr/lib/x86_64-linux-gnu/pkgconfig"
  , "/usr/lib64/pkgconfig", "/usr/share/pkgconfig"
  , "/usr/local/lib/pkgconfig", "/usr/local/share/pkgconfig"
  ]

-- ── headers ──────────────────────────────────────────────────────────

data HdrInfo = HdrInfo {hiName :: !Text, hiPath :: !FilePath, hiDigest :: !Text}

hdrLine :: HdrInfo -> Text
hdrLine h = "header " <> hiName h <> " digest=" <> hiDigest h <> " path=" <> T.pack (hiPath h)

-- | Find a header on the search path and hash its bytes; a header that is
-- declared but cannot be located is a fail-closed build error.
locateHash :: [FilePath] -> FilePath -> IO (Either Diagnostics HdrInfo)
locateHash dirs name = do
  found <- firstExisting [d </> name | d <- dirs]
  case found of
    Nothing ->
      pure (Left [pErr ("native binding header '" <> T.pack name <> "' was not found on the resolved include path (Spec §27.1.1)")])
    Just p -> do
      bs <- BS.readFile p
      pure (Right (HdrInfo (T.pack name) p (contentId [(p, bs)])))

-- | Digest a package-relative file (module map, …) into an identity line,
-- fail-closed if it escapes the package root, is a symlink, or is missing
-- (§36.11 path hardening, §27.1.1 identity input).
digestRel :: FilePath -> Text -> FilePath -> IO (Either Diagnostics Text)
digestRel baseDir kind rel = do
  esafe <- safeWithinRoot baseDir rel
  case esafe of
    Left e -> pure (Left [pErr e])
    Right p -> do
      ok <- doesFileExist p
      if ok
        then do bs <- BS.readFile p; pure (Right (kind <> " " <> T.pack rel <> " digest=" <> contentId [(rel, bs)]))
        else pure (Left [pErr ("native binding " <> kind <> " '" <> T.pack rel <> "' was not found (Spec §27.1.1)")])

-- | §36.28/§36.6: digest a prebuilt artifact and, when the manifest declares
-- an expected identity, compare it — a mismatch is fail-closed (never link an
-- artifact whose bytes do not match the pinned identity).
verifyPrebuilt :: FilePath -> Text -> Maybe Text -> IO (Either Diagnostics Text)
verifyPrebuilt baseDir art mexp = do
  esafe <- safeWithinRoot baseDir (T.unpack art)
  case esafe of
    Left e -> pure (Left [pErr e])
    Right p -> do
      ok <- doesFileExist p
      if not ok
        then pure (Left [pErr ("prebuilt native artifact '" <> art <> "' was not found (Spec §36.28)")])
        else do
          bs <- BS.readFile p
          let dig = contentId [(T.unpack art, bs)]
          case mexp of
            Just expected
              | expected /= dig ->
                  pure (Left [pErr ("prebuilt native artifact '" <> art <> "' has identity " <> dig
                                      <> " but the manifest declares expected identity " <> expected
                                      <> " (Spec §36.28/§36.6)")])
            _ -> pure (Right ("prebuilt " <> art <> " digest=" <> dig
                                <> maybe "" (const " (expected-verified)") mexp))

-- | Resolve a package-relative path within the root, rejecting @..@ escapes
-- and symlinks (§36.11). Returns the absolute path or a diagnostic message.
safeWithinRoot :: FilePath -> FilePath -> IO (Either Text FilePath)
safeWithinRoot baseDir rel
  | isAbsolute rel || ".." `elem` splitDirectories rel =
      pure (Left ("native binding path '" <> T.pack rel <> "' escapes the package root (Spec §36.11)"))
  | otherwise = do
      let p = baseDir </> rel
      sym <- pathIsSymbolicLink p `catch` \(_ :: SomeException) -> pure False
      if sym
        then pure (Left ("native binding path '" <> T.pack rel <> "' is a symlink (unpinnable, Spec §36.11)"))
        else pure (Right p)

-- ── signature verification ─────────────────────────────────────────────

-- | Compile a probe TU that includes the real headers and redeclares each
-- @verify@ prototype; cc rejects a declaration incompatible with the real
-- header (so the symbol surface is verified against the real ABI). Returns
-- the verified-decl provenance lines, or a fail-closed diagnostic with the
-- compiler output.
verifyDecls
  :: String -> [String] -> FilePath -> FilePath -> [FilePath] -> [String] -> [String] -> [Text] -> [Text]
  -> IO (Either Diagnostics [Text])
verifyDecls ccExe ccLead workDir baseDir searchDirs pkgCflags defFlags hdrs decls
  | null decls = pure (Right [])
  | otherwise = do
      let probePath = workDir </> "native-abi-probe.c"
          probe =
            T.unlines $
              ["/* generated ABI verification probe (Kappa.Backend.NativeProbe). */"]
                ++ ["#include <" <> h <> ">" | h <- hdrs]
                ++ ["extern " <> d <> ";" | d <- decls]
      writeFile probePath (T.unpack probe)
      let iflags = concat [["-I", d] | d <- nub (baseDir : searchDirs)]
          args = ccLead ++ ["-std=c11", "-fsyntax-only"] ++ iflags ++ pkgCflags ++ defFlags ++ [probePath]
      (ec, out, err) <- readProcessWithExitCode ccExe args ""
      removeFile probePath `catch` \(_ :: SomeException) -> pure ()
      case ec of
        ExitSuccess -> pure (Right ["verified-decl " <> d | d <- decls])
        ExitFailure _ ->
          pure (Left [pErr ("a native binding 'verify' declaration does not match the real header ABI (Spec §26.1.5/§36.28):\n" <> T.pack (trim (out ++ err)))])
  where
    trim s = if length s <= 3000 then s else "...\n" ++ drop (length s - 3000) s

-- ── helpers ────────────────────────────────────────────────────────────

systemIncludeDirs :: [FilePath]
systemIncludeDirs = ["/usr/include", "/usr/local/include"]

resolve :: FilePath -> Text -> FilePath
resolve base t = base </> T.unpack t

firstExisting :: [FilePath] -> IO (Maybe FilePath)
firstExisting [] = pure Nothing
firstExisting (x : xs) = do
  ok <- doesFileExist x
  if ok then pure (Just x) else firstExisting xs

-- | Run a list of fallible IO actions, collecting the first failure (so a
-- build surfaces a single, precise native-ABI diagnostic) or all successes.
runAll :: [IO (Either Diagnostics a)] -> IO (Either Diagnostics [a])
runAll = go []
  where
    go acc [] = pure (Right (reverse acc))
    go acc (m : ms) = do
      r <- m
      case r of
        Left ds -> pure (Left ds)
        Right a -> go (a : acc) ms

pErr :: Text -> Diagnostic
pErr msg =
  diag SevError StageElaborate "E_BUILD_NATIVE_ABI" (Just "kappa-hs.build.native-abi")
    (Span "<native-binding>" (Pos 1 1) (Pos 1 1))
    msg

-- | §36.7/§27.1.1: compute the per-binding host-source identity lock entries.
-- For each selected native binding this runs the same discovery + fail-closed
-- ABI verification ('discoverAndVerifyNative') and digests the binding's shim
-- sources, then composites the pkg-config/header/verified-decl identity with
-- the binding's declared symbol surface and the target triple into a single
-- content id. The result is a @host-binding@ 'LockEntry' (key = binding name)
-- so a package-mode build PINS — and a later @--locked@ build VERIFIES — every
-- input that can affect the generated host module interface / ABI.
hostBindingLockEntries
  :: (String, [String]) -> FilePath -> Text -> [(Text, [Text], [NativeInput])]
  -> IO (Either Diagnostics [LockEntry])
hostBindingLockEntries cc baseDir triple = goB []
  where
    goB acc [] = pure (Right (reverse acc))
    goB acc ((name, symLines, inputs) : rest) = do
      ev <- discoverAndVerifyNative cc baseDir baseDir inputs
      case ev of
        Left ds -> pure (Left ds)
        Right prov -> do
          shims <- shimDigestLines baseDir inputs
          let idLines =
                npLines prov
                  ++ shims
                  ++ ["symbol " <> s | s <- symLines]
                  ++ ["target-triple " <> triple]
                  -- §26.1.3: the adapter mode participates in host-binding
                  -- identity. The zig native profile realizes only native.direct
                  -- (the sole mode the manifest schema can select today), so it is
                  -- a constant identity input here.
                  ++ ["adapter native.direct"]
              cid = contentId [("host-binding:" <> T.unpack name, encU (T.intercalate "\n" idLines))]
          goB (LockEntry "host-binding" name cid : acc) rest
    encU = encodeUtf8

-- | Digest each shim source's content (§27.1.1 shim-source digests) so a shim
-- edit forces a repin. A missing shim is a fail-closed build error elsewhere
-- (the C toolchain), so here a missing file simply contributes a sentinel.
shimDigestLines :: FilePath -> [NativeInput] -> IO [Text]
shimDigestLines baseDir inputs =
  fmap concat . mapM one $ [s | ShimInput ss <- inputs, s <- ss] ++ [a | PrebuiltInput a _ <- inputs]
  where
    one rel = do
      let p = baseDir </> T.unpack rel
      ok <- doesFileExist p
      if ok
        then do bs <- BS.readFile p; pure ["shim " <> rel <> " digest=" <> contentId [(p, bs)]]
        else pure ["shim " <> rel <> " digest=<missing>"]
