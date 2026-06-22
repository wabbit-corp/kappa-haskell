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
  , crossTargetFlags
  , safeWithinRoot
  ) where

import qualified Data.ByteString as BS
import Data.List (nub)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Encoding (encodeUtf8)
import Kappa.Backend.Capabilities (nativeRuntimeCapabilities)
import Kappa.Build.Lock (LockEntry (..), contentId)
import Kappa.Build.Types (FfiClass (..), NativeInput (..))
import Kappa.Diagnostic
import Kappa.Source (Pos (..), Span (..))
import Control.Exception (catch, SomeException)
import System.Directory (canonicalizePath, doesFileExist, findExecutable, pathIsSymbolicLink, removeFile)
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath (isAbsolute, splitDirectories, splitSearchPath, takeFileName, (</>))
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
-- | §26.1.3: the @-target@ flags for the declared triple, when the driver is a
-- cross-capable @zig cc@. A host gcc/clang/cc cannot retarget, so preprocessing
-- and ABI verification then reflect the host (which the realized configurations
-- keep equal to the declared target); for a zig cross-build these flags make
-- the header preprocess/verify for the actual target ABI, matching the link.
crossTargetFlags :: (String, [String]) -> Text -> [String]
crossTargetFlags (ccExe, ccLead) triple
  | not (T.null triple) && takeFileName ccExe == "zig" && ccLead == ["cc"] =
      ["-target", T.unpack triple]
  | otherwise = []

discoverAndVerifyNative
  :: (String, [String]) -> Text -> FilePath -> FilePath -> [NativeInput] -> [Text]
  -> IO (Either Diagnostics NativeProvenance)
discoverAndVerifyNative cc@(ccExe, ccLead) triple baseDir workDir inputs extraExterns = do
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
              tflags = crossTargetFlags cc triple
          ever <- verifyDecls ccExe ccLead tflags workDir baseDir searchDirs pkgCflags (map T.unpack defLines) hdrs decls extraExterns
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
                          -- §26.1.4/§27.6: the foreign-call classification the
                          -- binding's raw declarations carry (default nonblocking),
                          -- plus the native profile's advertised capability set.
                          ++ ["foreign-call-classification " <> classifyText inputs]
                          ++ ["backend-capabilities " <> T.intercalate "," nativeRuntimeCapabilities]
                          -- §26.1.4: which symbols' char* are proven C strings
                          -- (affects the generated surface), an identity input.
                          ++ ["cstring-symbols " <> T.intercalate "," (concat [ss | CStringSymbolsInput ss <- inputs])]
                      composite = contentId [("native-identity", encodeLines allLines)]
                  pure (Right (NativeProvenance allLines composite))
  where
    encodeLines ls = BS.intercalate (BS.singleton 10) (map encodeUtf8 ls)

-- | §26.1.4/§27.6: the foreign-call classification a binding declares (the last
-- 'ClassifyInput' wins; default @nonblocking@ for a direct native call).
classifyText :: [NativeInput] -> Text
classifyText inputs = case [c | ClassifyInput c <- inputs] of
  [] -> "nonblocking"
  cs -> render (last cs)
  where
    render FfiNonblocking = "nonblocking"
    render FfiBlocking = "blocking"
    render FfiBlockingCancellable = "blocking-cancellable"

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
      -- §36.28/§36.7: the RESOLVED pkg-config cflags (include dirs + defines
      -- that drive header preprocessing, hence the generated surface) and libs
      -- (the link inputs) are both host-source identity inputs.
      <> " cflags=" <> T.pack (unwords (piCflags pi_))
      <> " libs=" <> T.pack (unwords (piLibs pi_))
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
  , "/opt/homebrew/lib/pkgconfig", "/opt/homebrew/share/pkgconfig"
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

-- | Resolve a package-relative path within the root, rejecting @..@ escapes,
-- absolute paths, leaf symlinks, AND symlinked-directory traversal that would
-- resolve outside the package root (§36.11). Returns the absolute path or a
-- diagnostic message.
safeWithinRoot :: FilePath -> FilePath -> IO (Either Text FilePath)
safeWithinRoot baseDir rel
  | isAbsolute rel || ".." `elem` splitDirectories rel =
      pure (Left ("native binding path '" <> T.pack rel <> "' escapes the package root (Spec §36.11)"))
  | otherwise = do
      let p = baseDir </> rel
      sym <- pathIsSymbolicLink p `catch` \(_ :: SomeException) -> pure False
      if sym
        then pure (Left ("native binding path '" <> T.pack rel <> "' is a symlink (unpinnable, Spec §36.11)"))
        else do
          -- follow any intermediate symlinks and confirm the real path is still
          -- under the package root (a symlinked subdirectory cannot escape it).
          root <- canonicalizePath baseDir `catch` \(_ :: SomeException) -> pure baseDir
          canon <- canonicalizePath p `catch` \(_ :: SomeException) -> pure p
          if splitDirectories root `isPathPrefixOf` splitDirectories canon
            then pure (Right p)
            else pure (Left ("native binding path '" <> T.pack rel <> "' resolves outside the package root (symlink escape, Spec §36.11)"))
  where
    isPathPrefixOf pre full = pre == take (length pre) full

-- ── signature verification ─────────────────────────────────────────────

-- | Compile a probe TU that includes the real headers and redeclares each
-- @verify@ prototype; cc rejects a declaration incompatible with the real
-- header (so the symbol surface is verified against the real ABI). Returns
-- the verified-decl provenance lines, or a fail-closed diagnostic with the
-- compiler output.
verifyDecls
  :: String -> [String] -> [String] -> FilePath -> FilePath -> [FilePath] -> [String] -> [String] -> [Text] -> [Text] -> [Text]
  -> IO (Either Diagnostics [Text])
verifyDecls ccExe ccLead tflags workDir baseDir searchDirs pkgCflags defFlags hdrs decls extraExterns
  | null decls && null extraExterns = pure (Right [])
  | otherwise = do
      let probePath = workDir </> "native-abi-probe.c"
          objPath = workDir </> "native-abi-probe.o"
          undefs = ["#ifdef " <> n <> "\n#undef " <> n <> "\n#endif" | n <- verifiedNames]
          probe =
            T.unlines $
              [ "/* generated ABI verification probe (Kappa.Backend.NativeProbe). */"
              , "#include <stdint.h>" -- the conservative externs spell exact-width / size types
              , "#include <stddef.h>"
              ]
                ++ ["#include <" <> h <> ">" | h <- hdrs]
                ++ undefs
                -- §26.1.5: author-declared real prototypes, AND the conservative
                -- prototypes of all-scalar symbolDecls (extraExterns) — both are
                -- checked against the real header, so a declared width/signedness
                -- that disagrees with the installed header is a hard error.
                ++ ["extern " <> d <> ";" | d <- decls]
                ++ extraExterns
      writeFile probePath (T.unpack probe)
      let iflags = concat [["-I", d] | d <- nub (baseDir : searchDirs)]
          -- compile to a throwaway object (NOT -fsyntax-only, which the
          -- zig-cc driver rejects); this still performs full type checking.
          args = ccLead ++ tflags ++ ["-std=c11", "-c", "-o", objPath] ++ iflags ++ pkgCflags ++ defFlags ++ [probePath]
      (ec, out, err) <- readProcessWithExitCode ccExe args ""
      removeFile probePath `catch` \(_ :: SomeException) -> pure ()
      removeFile objPath `catch` \(_ :: SomeException) -> pure ()
      case ec of
        ExitFailure _ ->
          pure (Left [pErr ("a native binding declaration does not match the real header ABI (Spec §26.1.5/§36.28):\n" <> T.pack (trim (out ++ err)))])
        ExitSuccess -> do
          -- §26.1.5: a `verify` redeclaration only PROVES the ABI when the
          -- symbol is actually declared by an included header. A lone
          -- `extern <decl>;` with no header that declares the symbol is
          -- self-consistent C and verifies nothing (the redeclaration would
          -- agree with any fabricated prototype). Require header coverage: a
          -- probe that takes the address of each verified symbol with NO
          -- local extern in scope — an undeclared identifier is then a hard
          -- error, so a fabricated ABI for a symbol no included header
          -- declares is rejected fail-closed rather than linked.
          covRes <- coverageProbe
          case covRes of
            Left ds -> pure (Left ds)
            Right () -> pure (Right ["verified-decl " <> d | d <- decls])
  where
    trim s = if length s <= 3000 then s else "...\n" ++ drop (length s - 3000) s
    -- symbol name of a C prototype: the identifier just before the first '('.
    protoSym :: Text -> Text
    protoSym d =
      let idChar c = c == '_' || ('0' <= c && c <= '9') || ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
          before = T.takeWhile (/= '(') d
       in T.takeWhileEnd idChar (T.dropWhileEnd (not . idChar) before)
    verifiedNames = nub (filter (not . T.null) (map protoSym (decls ++ extraExterns)))
    coverageProbe = do
      if null verifiedNames
        then pure (Right ())
        else do
          let covPath = workDir </> "native-abi-coverage.c"
              covObj = workDir </> "native-abi-coverage.o"
              refs = ["  syms[" <> T.pack (show i) <> "] = (void *)(&" <> n <> ");" | (i, n) <- zip [0 :: Int ..] verifiedNames]
              cov =
                T.unlines $
                  [ "/* generated header-coverage probe (Kappa.Backend.NativeProbe). */"
                  , "#include <stdint.h>"
                  , "#include <stddef.h>"
                  ]
                    ++ ["#include <" <> h <> ">" | h <- hdrs]
                    ++ ["#ifdef " <> n <> "\n#undef " <> n <> "\n#endif" | n <- verifiedNames]
                    ++ [ "void *kappa_abi_coverage(void);"
                       , "void *kappa_abi_coverage(void) {"
                       , "  void *syms[" <> T.pack (show (length verifiedNames)) <> "];"
                       ]
                    ++ refs
                    ++ ["  return syms[0];", "}"]
              iflags = concat [["-I", d] | d <- nub (baseDir : searchDirs)]
              args = ccLead ++ tflags ++ ["-std=c11", "-c", "-o", covObj] ++ iflags ++ pkgCflags ++ defFlags ++ [covPath]
          writeFile covPath (T.unpack cov)
          (ec, out, err) <- readProcessWithExitCode ccExe args ""
          removeFile covPath `catch` \(_ :: SomeException) -> pure ()
          removeFile covObj `catch` \(_ :: SomeException) -> pure ()
          case ec of
            ExitSuccess -> pure (Right ())
            ExitFailure _ ->
              pure (Left [pErr ("a native binding `verify` declaration cannot be checked against the real ABI: no included header declares the symbol, so the redeclaration verifies nothing (Spec §26.1.5/§36.28). Add the header that declares it (or provide the symbol via a shim).\n" <> T.pack (trim (out ++ err)))])

-- ── helpers ────────────────────────────────────────────────────────────

systemIncludeDirs :: [FilePath]
systemIncludeDirs =
  [ "/usr/include"
  , "/usr/local/include"
  , "/opt/homebrew/include"
  , "/Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk/usr/include"
  , "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/include"
  ]

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
  :: (String, [String]) -> FilePath -> Text -> [(Text, [Text], [NativeInput], [Text])]
  -> IO (Either Diagnostics [LockEntry])
hostBindingLockEntries cc baseDir triple = goB []
  where
    goB acc [] = pure (Right (reverse acc))
    goB acc ((name, symLines, inputs, scalarExterns) : rest) = do
      -- §26.1.5: verify the binding's all-scalar symbolDecls against the real
      -- headers too (their conservative C prototypes), so a declared scalar
      -- width that disagrees with the installed header is fail-closed.
      ev <- discoverAndVerifyNative cc triple baseDir baseDir inputs scalarExterns
      case ev of
        Left ds -> pure (Left ds)
        Right prov -> do
          shims <- shimDigestLines baseDir inputs
          let idLines =
                -- §36.7:39604/:39637: the entry's schema identity — a schema
                -- change invalidates the pin (the digest changes → repin),
                -- so an entry is never reused under an incompatible schema.
                ("schema host-source-v1" : npLines prov)
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
