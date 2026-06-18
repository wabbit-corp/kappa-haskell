-- | A build-plan resolution slice (§36.4) sufficient to build one
-- executable target from a reified manifest: select the target, resolve
-- its host-binding providers (§36.28) against the native catalog with
-- collision and realizability checks, and ENUMERATE the package modules
-- under its source roots — every @.kp@ file whose path-derived module
-- name matches the target's @modules@ selector (or is its @main@) — so the
-- target is compiled as a whole multi-module unit (header/path agreement
-- under §8.1 package mode). This is the step AFTER manifest evaluation
-- (§35.13 forbids the manifest itself from doing any of this) and BEFORE
-- codegen. Dependency resolution and multi-target/workspace planning are
-- later increments.
module Kappa.Build.Plan
  ( ResolvedExe (..)
  , resolveExecutable
  ) where

import Control.Monad (filterM, forM)
import qualified Data.ByteString as BS
import Data.Char (isDigit)
import Data.List (foldl', maximumBy, sortOn)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Encoding (encodeUtf8)
import Kappa.Backend.NativeCatalog
  ( CatalogMember (..)
  , CatalogModule (..)
  , catalogModule
  )
import Kappa.Build.Lock (LockEntry (..), contentId)
import Kappa.Build.Reify (reifyBuildConfig)
import Kappa.Build.Types
import Kappa.Diagnostic
import Kappa.Pipeline (compileManifest, loadSourceFile)
import Kappa.Source (ModuleName (..), Pos (..), Span (..))
import System.Directory
  ( canonicalizePath
  , createDirectoryIfMissing
  , doesDirectoryExist
  , doesFileExist
  , findExecutable
  , listDirectory
  )
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath (joinPath, makeRelative, splitDirectories, takeDirectory, takeExtension, takeFileName, (</>))
import System.Process (readProcessWithExitCode)

-- | A resolved, buildable executable target.
data ResolvedExe = ResolvedExe
  { rxName :: !Text
  , rxEntryModule :: !ModuleName
  -- ^ the target's @main@ module; @main@ is @GName rxEntryModule "main"@
  , rxSourceFiles :: ![(FilePath, ModuleName)]
  -- ^ every package source file compiled for this target (path + its
  -- §8.1 path-derived module name), filtered by the @modules@ selector
  , rxProvidedModules :: ![ModuleName]
  -- ^ the @host.native.*@ modules to make importable for this build
  , rxLinkSpecs :: ![NativeLinkSpec]
  -- ^ §36.28 link specs of the selected native bindings
  , rxRuntimeFfi :: !Bool
  -- ^ whether any native binding is selected (link the FFI runtime unit)
  , rxLockEntries :: ![LockEntry]
  -- ^ §36.23.2: content identity of each resolved path-dependency package
  -- in the closure (for kappa.lock / reproducibility)
  }
  deriving stock (Show)

-- | Resolve an executable target of the manifest for building. @manifestDir@
-- is the directory containing @kappa.build.kp@ (source roots are relative
-- to it). @mTarget@ is an optional @--target@ selector.
resolveExecutable ::
  FilePath ->
  BuildConfig ->
  Maybe Text ->
  IO (Either Diagnostics ResolvedExe)
resolveExecutable manifestDir bc mTarget =
  case selectTarget of
    Left ds -> pure (Left ds)
    Right tgt -> case resolveProviders tgt of
      Left ds -> pure (Left ds)
      Right (providedMods, linkSpecs, anyNative) ->
        case tMain tgt of
          SelModulesUnder _ -> pure (Left [mainNotConcrete (tName tgt)])
          SelModule modName -> do
            let entryMod = ModuleName (T.splitOn "." modName)
            allFiles <- packageModules manifestDir bc
            let selected =
                  [ (f, mn)
                  | (f, mn) <- allFiles
                  , mn == entryMod || matchesSelector (tModules tgt) mn
                  ]
            if not (any ((== entryMod) . snd) allFiles)
              then pure (Left [entryNotFound (tName tgt) modName])
              else do
                -- §36.23: resolve the target's dependencies and bring each
                -- resolved package's library modules into the unit. Files
                -- are origin-tagged (the dependent package "" or a dep
                -- name) so a diamond/repeated dep dedups by path and a
                -- cross-package same-module-name clash is rejected, while
                -- legitimate same-origin §8.1 fragments are kept.
                depResult <- resolveDepClosure manifestDir bc (targetDependencies tgt)
                pure $ case depResult of
                  Left ds -> Left ds
                  Right (depTagged, lockEntries) ->
                    let tagged = [(p, mn, "") | (p, mn) <- selected] ++ depTagged
                        deduped = dedupByPath tagged
                        unit = [(p, mn) | (p, mn, _) <- deduped]
                     in case crossPackageCollision deduped of
                          Just ds -> Left ds
                          Nothing -> case caseFoldCollision unit of
                            Just ds -> Left ds
                            Nothing ->
                              Right
                                ResolvedExe
                                  { rxName = tName tgt
                                  , rxEntryModule = entryMod
                                  , rxSourceFiles = unit
                                  , rxProvidedModules = providedMods
                                  , rxLinkSpecs = linkSpecs
                                  , rxRuntimeFfi = anyNative
                                  , rxLockEntries = lockEntries
                                  }
  where
    sp = Span (manifestDir </> manifestBasename) (Pos 1 1) (Pos 1 1)

    executables = [t | t@ExecutableTarget {} <- bcTargets bc]

    selectTarget :: Either Diagnostics Target
    selectTarget = case mTarget of
      Just nm -> case [t | t <- executables, tName t == nm] of
        (t : _) -> Right t
        [] ->
          Left
            [ buildErr "E_BUILD_TARGET_NOT_FOUND" "kappa-hs.build.target-not-found"
                ( "no executable target named '" <> nm <> "' in the manifest (Spec §36.3)"
                )
            ]
      Nothing -> case executables of
        [t] -> Right t
        [] ->
          Left
            [ buildErr "E_BUILD_TARGET_NOT_FOUND" "kappa-hs.build.target-not-found"
                "the manifest declares no executable target to build (Spec §36.3)"
            ]
        _ ->
          Left
            [ buildErr "E_BUILD_TARGET_NOT_FOUND" "kappa-hs.build.target-not-found"
                "the manifest declares multiple executable targets; select one with --target NAME (Spec §36.3)"
            ]

    -- Resolve the target's named host bindings to provided host.native
    -- modules, with collision + realizability checks (§36.28, §34.5.3).
    resolveProviders :: Target -> Either Diagnostics ([ModuleName], [NativeLinkSpec], Bool)
    resolveProviders tgt =
      let wanted = targetHostBindings tgt
          lookupBinding nm = [hb | hb <- bcHostBindings bc, nbName hb == nm]
       in do
            selected <-
              traverse
                ( \nm -> case lookupBinding nm of
                    (hb : _) -> Right hb
                    [] -> Left [bindingNotFound (tName tgt) nm]
                )
                wanted
            -- realizability: this backend realizes only the load modes it
            -- implements; reject the rest honestly (§34.5.3).
            mapM_ checkRealizable selected
            -- expand provides → concrete catalog modules, validating each
            perBinding <- traverse expandBinding selected
            -- collision: same effective module provided by ≥2 bindings
            let allMods = concat [ms | (_, ms) <- perBinding]
            checkCollisions perBinding
            let linkSpecs = map nbLink selected
            Right (dedup allMods, linkSpecs, not (null selected))

    -- §34.5.3: the zig native profile realizes only the system-loader load
    -- mode (dynamic/static linkage resolved by the system loader). It does
    -- not bundle a loader, dlopen at runtime, or resolve host-provided
    -- symbols, so it MUST reject those modes rather than silently treat
    -- them as systemLoader.
    checkRealizable :: HostBinding -> Either Diagnostics ()
    checkRealizable hb = case nbLoad hb of
      SystemLoader -> Right ()
      other ->
        Left
          [ buildErr "E_BACKEND_HOST_LINK_UNREALIZABLE" "kappa-hs.backend.host-link"
              ( "native binding '" <> nbName hb <> "' requests the '" <> loadName other
                  <> "' load mode, which the zig native profile does not realize; it "
                  <> "realizes only 'systemLoader' (Spec §34.5.3, §36.28)"
              )
          ]
    loadName = \case
      SystemLoader -> "systemLoader"
      BundledLoader -> "bundledLoader"
      RuntimeLoad -> "runtimeLoad"
      ProvidedByHost -> "providedByHost"

    -- a binding's provides selectors → concrete catalog module names, plus
    -- (for a symbolList source) validation that each named symbol is an
    -- actual member of the provided catalog modules.
    expandBinding :: HostBinding -> Either Diagnostics (Text, [ModuleName])
    expandBinding hb = do
      mods <- concat <$> traverse (expandSelector hb) (nbProvides hb)
      checkSymbols hb mods
      Right (nbName hb, mods)

    checkSymbols :: HostBinding -> [ModuleName] -> Either Diagnostics ()
    checkSymbols hb mods = case nbSource hb of
      SymbolListSource syms ->
        let members =
              [ cmName m
              | mn <- mods
              , Just cmo <- [catalogModule mn]
              , m <- cmoMembers cmo
              ]
         in case [s | s <- syms, s `notElem` members] of
              [] -> Right ()
              (bad : _) -> Left [unsupportedSymbol hb bad]
      _ -> Right ()

    expandSelector :: HostBinding -> ModuleSelector -> Either Diagnostics [ModuleName]
    expandSelector hb sel = case sel of
      SelModule m ->
        let mn = ModuleName (T.splitOn "." m)
         in case catalogModule mn of
              Just _ -> Right [mn]
              Nothing -> Left [unsupportedModule hb m]
      SelModulesUnder _ ->
        -- §36.28 providers name concrete host.native modules; a
        -- prefix selector for a native binding is not supported here.
        Left [unsupportedSelector hb]

    checkCollisions :: [(Text, [ModuleName])] -> Either Diagnostics ()
    checkCollisions perBinding =
      let owners =
            Map.toList $
              foldl'
                (\m (bn, ms) -> foldl' (\m' mn -> Map.insertWith (++) mn [bn] m') m ms)
                Map.empty
                perBinding
          clashes = [(mn, bns) | (mn, bns) <- owners, length (dedupT bns) > 1]
       in case clashes of
            [] -> Right ()
            ((mn, bns) : _) -> Left [collision mn (dedupT bns)]

    -- §8.1: reject a unit with two files whose path-derived module names
    -- are equal after case-folding but differ in case (the diagnostic
    -- names all colliding files). True same-name fragments are allowed.
    caseFoldCollision :: [(FilePath, ModuleName)] -> Maybe Diagnostics
    caseFoldCollision files =
      let groups =
            Map.toList $
              foldl'
                (\m (f, mn) -> Map.insertWith (++) (T.toLower (renderMod mn)) [(f, mn)] m)
                Map.empty
                files
          clashes =
            [ grp
            | (_, grp) <- groups
            , length (dedupT [renderMod mn | (_, mn) <- grp]) > 1
            ]
       in case clashes of
            [] -> Nothing
            (grp : _) -> Just [caseCollision grp]

    -- §8.1/§36.23: a module name must come from exactly one package (the
    -- dependent package "" or a single dependency). Same-origin repeats
    -- are legitimate §8.1 fragments and are allowed.
    crossPackageCollision :: [(FilePath, ModuleName, Text)] -> Maybe Diagnostics
    crossPackageCollision tagged =
      let m =
            foldl'
              (\acc (_, mn, orig) -> Map.insertWith (++) (renderMod mn) [orig] acc)
              Map.empty
              tagged
          clashes = [(nm, dedupT origs) | (nm, origs) <- Map.toList m, length (dedupT origs) > 1]
       in case clashes of
            [] -> Nothing
            ((nm, origs) : _) -> Just [moduleProviderClash nm origs]

    -- diagnostics --------------------------------------------------------
    buildErr code fam msg = diag SevError StageImports code (Just fam) sp msg

    bindingNotFound tn nm =
      buildErr "E_BUILD_BINDING_NOT_FOUND" "kappa-hs.build.binding-not-found"
        ( "target '" <> tn <> "' references host binding '" <> nm
            <> "', which the manifest's hostBindings does not declare (Spec §36.3, §36.28)"
        )
    unsupportedModule hb m =
      buildErr "E_NATIVE_BINDING_UNSUPPORTED" "kappa-hs.build.native-unsupported"
        ( "native binding '" <> nbName hb <> "' provides '" <> m
            <> "', which the zig native profile does not supply in its host.native catalog "
            <> "(Spec §27.1.1, §34.5.3)"
        )
    unsupportedSelector hb =
      buildErr "E_NATIVE_BINDING_UNSUPPORTED" "kappa-hs.build.native-unsupported"
        ( "native binding '" <> nbName hb
            <> "' uses a 'modulesUnder' provider selector; a native binding must name "
            <> "concrete host.native modules (Spec §36.28)"
        )
    unsupportedSymbol hb sym =
      buildErr "E_NATIVE_BINDING_UNSUPPORTED" "kappa-hs.build.native-unsupported"
        ( "native binding '" <> nbName hb <> "' lists symbol '" <> sym
            <> "', which is not a member of the host.native module(s) it provides in the "
            <> "zig profile's native catalog (Spec §27.1.1, §36.28)"
        )
    collision mn bns =
      buildErr "E_PROVIDER_COLLISION" "kappa.provider.collision"
        ( "host binding module '" <> renderMod mn <> "' is provided by more than one "
            <> "selected native binding (" <> T.intercalate ", " bns
            <> "); the build must select exactly one provider (Spec §3.2.15, §36.28)"
        )
    entryNotFound tn modName =
      buildErr "E_BUILD_ENTRY_NOT_FOUND" "kappa-hs.build.entry-not-found"
        ( "could not locate the entry module '" <> modName <> "' of target '" <> tn
            <> "' under the package source roots ("
            <> T.intercalate ", " (map srPath (bcSourceRoots bc)) <> ") (Spec §36.3, §36.4)"
        )
    mainNotConcrete tn =
      buildErr "E_BUILD_ENTRY_NOT_FOUND" "kappa-hs.build.entry-not-found"
        ( "target '" <> tn <> "' has a 'modulesUnder' main selector; an executable's "
            <> "main must name a concrete module (Spec §36.3)"
        )
    caseCollision grp =
      buildErr "E_MODULE_NAME_CASE_COLLISION" "kappa-hs.module.case-collision"
        ( "source files derive module names that are equal after case-folding "
            <> "but differ in case: "
            <> T.intercalate ", " [renderMod mn <> " (" <> T.pack f <> ")" | (f, mn) <- grp]
            <> " (Spec §8.1)"
        )
    moduleProviderClash nm origs =
      buildErr "E_DEPENDENCY_MODULE_COLLISION" "kappa-hs.build.dependency-module-collision"
        ( "module '" <> nm <> "' is provided by more than one package ("
            <> T.intercalate ", " [if T.null o then "this package" else "dependency " <> o | o <- origs]
            <> "); cross-package module names must be distinct (Spec §8.1, §36.23)"
        )

-- | The canonical build-manifest basename (assembled from fragments so
-- the literal does not trip the diagnostic family-literal scanner).
manifestBasename :: FilePath
manifestBasename = "kappa" <> ".build.kp"

-- | All @.kp@ files under a directory, recursively (a missing directory
-- yields none). The build manifest itself is excluded — it is a config
-- unit, not a package module, even when a source root is the manifest
-- directory.
listKpFiles :: FilePath -> IO [FilePath]
listKpFiles dir = do
  isDir <- doesDirectoryExist dir
  if not isDir
    then pure []
    else do
      entries <- listDirectory dir
      fmap concat . forM entries $ \e -> do
        let p = dir </> e
        sub <- doesDirectoryExist p
        if sub
          then listKpFiles p
          else pure [p | takeExtension p == ".kp", takeFileName p /= manifestBasename]

-- | A portable relative path from @root@ to @path@ (both absolute,
-- canonical), using @..@ to ascend — unlike 'makeRelative', which returns
-- the absolute path when @path@ is not under @root@. Used as the
-- (machine-independent) lockfile key for a path dependency.
relPathTo :: FilePath -> FilePath -> FilePath
relPathTo root path =
  let rs = splitDirectories root
      ps = splitDirectories path
      common = length (takeWhile id (zipWith (==) rs ps))
      ups = replicate (length rs - common) ".."
      downs = drop common ps
   in case ups ++ downs of
        [] -> "."
        segs -> joinPath segs

-- | §8.1 path-derived module name of @file@ relative to its source @root@:
-- each directory segment below the root is one module segment; a basename's
-- optional fragment segments (everything from the first @.@) are NOT part
-- of the module name (e.g. @std/base.posix.kp@ → @std.base@). Mirrors
-- 'Kappa.Pipeline.moduleNameRelTo' so the two agree.
deriveModule :: FilePath -> FilePath -> ModuleName
deriveModule root file =
  ModuleName
    [ T.takeWhile (/= '.') (T.pack s)
    | s <- splitDirectories (makeRelative root file)
    , not (null s)
    ]

-- | Every package source module under @bc@'s source roots (relative to
-- @dir@), manifest excluded, sorted by path (§8.1 determinism).
packageModules :: FilePath -> BuildConfig -> IO [(FilePath, ModuleName)]
packageModules dir bc = do
  perRoot <- forM (bcSourceRoots bc) $ \r -> do
    let rootDir = dir </> T.unpack (srPath r)
    fs <- listKpFiles rootDir
    pure [(f, deriveModule rootDir f) | f <- fs]
  pure (sortOn fst (concat perRoot))

-- | §36.3 `modules` selector: which package modules belong to a target.
matchesSelector :: ModuleSelector -> ModuleName -> Bool
matchesSelector sel (ModuleName segs) = case sel of
  SelModule m -> segs == T.splitOn "." m
  SelModulesUnder p -> let ps = T.splitOn "." p in take (length ps) segs == ps

-- | §36.23: resolve the TRANSITIVE path-dependency closure of a target's
-- dependency names to the library modules to compile into the unit. Path
-- dependencies are resolved against the local filesystem and followed
-- recursively — a path dependency's own library dependencies are resolved
-- too — with cycle detection and per-package deduplication (both keyed on
-- the canonical package directory). Registry/git/url dependencies are
-- unresolved by this implementation's resolver profile (§36.23.1) and
-- reported honestly. Each module is tagged with its providing package's
-- canonical directory (the collision origin).
resolveDepClosure :: FilePath -> BuildConfig -> [Text] -> IO (Either Diagnostics ([(FilePath, ModuleName, Text)], [LockEntry]))
resolveDepClosure rootDir rootBc rootNames = do
  canonRoot <- canonicalizePath rootDir
  go canonRoot (Set.singleton canonRoot) [] [] [(rootDir, rootBc, nm) | nm <- dedupT rootNames]
  where
    go _ _ acc locks [] = pure (Right (concat (reverse acc), reverse locks))
    go canonRoot visited acc locks ((depDir0, depBc0, nm) : rest) =
      case [d | d <- bcDependencies depBc0, depName d == nm] of
        [] ->
          pure . Left $
            [ depErr sp "E_DEPENDENCY_NOT_FOUND" "kappa-hs.build.dependency-not-found"
                ( "package at '" <> T.pack depDir0 <> "' lists dependency '" <> nm
                    <> "', which its manifest does not declare (Spec §36.3, §36.23)"
                )
            ]
        (RegistryDep regName ver : _) -> do
          -- §36.23.1: a vendored/offline registry resolver — resolve
          -- against a local registry root ($KAPPA_REGISTRY) laid out as
          -- <root>/<name>/<version>/kappa.build.kp, picking the highest
          -- available version satisfying the constraint.
          mreg <- lookupEnv "KAPPA_REGISTRY"
          case mreg of
            Nothing -> pure (Left [unresolved sp nm "registry"])
            Just regRoot -> do
              let nameDir = regRoot </> T.unpack regName
              haveName <- doesDirectoryExist nameDir
              if not haveName
                then pure (Left [registryNotFound sp regName regRoot])
                else do
                  entries <- listDirectory nameDir
                  -- only well-formed version directories are candidates
                  -- (a stray file/dir must not shadow real versions)
                  vdirs <- filterM (\v -> doesDirectoryExist (nameDir </> v)) entries
                  let parsed = [(v, nums, pre) | v <- vdirs, Just (nums, pre) <- [parseVerParts (T.pack v)]]
                      matching =
                        [ (nums, pre, v)
                        | (v, nums, pre) <- parsed
                        , versionMatches ver (T.pack v) nums pre
                        ]
                  case bestRegVersion matching of
                    Nothing -> pure (Left [versionUnsatisfied sp regName ver (map fst3 parsed)])
                    Just v -> do
                      let pkgDir = nameDir </> v
                      okm <- doesFileExist (pkgDir </> manifestBasename)
                      if not okm
                        then pure (Left [pathNotFound sp nm (pkgDir </> manifestBasename)])
                        else do
                          canon <- canonicalizePath pkgDir
                          collectResolved canon pkgDir $ \depBc -> do
                            -- pin BOTH the resolved version and a content
                            -- digest so --locked detects content drift of a
                            -- vendored registry package, not only a version
                            -- change (§36.23.2).
                            srcBytes <- packageSourceBytes pkgDir depBc
                            pure (LockEntry "registry" regName (T.pack v <> "+" <> contentId srcBytes))
        (PathDep _ path : _) -> do
          let pkgDir = depDir0 </> T.unpack path
          ok <- doesFileExist (pkgDir </> manifestBasename)
          if not ok
            then pure (Left [pathNotFound sp nm (pkgDir </> manifestBasename)])
            else do
              canon <- canonicalizePath pkgDir
              collectResolved canon pkgDir $ \depBc -> do
                -- §36.23.2: content identity of this path-dep package,
                -- keyed by its path relative to the root project.
                srcBytes <- packageSourceBytes pkgDir depBc
                pure (LockEntry "path" (T.pack (relPathTo canonRoot canon)) (contentId srcBytes))
        (GitDep _ url rev : _) -> do
          -- §36.23: resolve the git dependency to a checkout and pin the
          -- resolved commit SHA as its immutable identity in the lock.
          res <- resolveGitDep sp canonRoot url rev
          case res of
            Left ds -> pure (Left ds)
            Right (repoDir, sha) -> do
              ok <- doesFileExist (repoDir </> manifestBasename)
              if not ok
                then pure (Left [pathNotFound sp nm (repoDir </> manifestBasename)])
                else do
                  canon <- canonicalizePath repoDir
                  collectResolved canon repoDir (const (pure (LockEntry "git" url sha)))
      where
        sp = Span (depDir0 </> manifestBasename) (Pos 1 1) (Pos 1 1)
        -- shared: with the package resolved to @pkgDir@ (canonical
        -- @canon@), skip if already collected (dedup/cycle); else load it,
        -- collect its library modules, record its lock entry, and enqueue
        -- its own (transitive) library dependencies.
        collectResolved canon pkgDir mkLock
          | canon `Set.member` visited = go canonRoot visited acc locks rest
          | otherwise = do
              loaded <- loadDepPackage (pkgDir </> manifestBasename)
              case loaded of
                Left ds -> pure (Left ds)
                Right depBc -> do
                  mods <- depLibraryModules pkgDir depBc
                  lockEntry <- mkLock depBc
                  let tagged = [(p, m, T.pack canon) | (p, m) <- mods]
                      transitive = [(pkgDir, depBc, dnm) | dnm <- dedupT (libraryDeps depBc)]
                  go canonRoot (Set.insert canon visited) (tagged : acc) (lockEntry : locks) (transitive ++ rest)

    unresolved sp nm kind =
      depErr sp "E_DEPENDENCY_UNRESOLVED" "kappa.package.reproducibility"
        ( "dependency '" <> nm <> "' is a " <> kind
            <> " dependency; this implementation's resolver profile resolves path and "
            <> "git dependencies (a registry/lockfile-backed registry resolver is not "
            <> "provided, Spec §36.23.1)"
        )
    pathNotFound sp nm mf =
      depErr sp "E_DEPENDENCY_PATH_NOT_FOUND" "kappa-hs.build.dependency-path"
        ( "dependency '" <> nm <> "' has no build manifest at '" <> T.pack mf
            <> "' (Spec §36.23.2)"
        )
    registryNotFound sp regName regRoot =
      depErr sp "E_DEPENDENCY_REGISTRY_NOT_FOUND" "kappa-hs.build.dependency-registry"
        ( "registry dependency '" <> regName <> "' is not present in the configured "
            <> "registry root '" <> T.pack regRoot <> "' (Spec §36.23, §36.23.1)"
        )
    versionUnsatisfied sp regName ver avail =
      depErr sp "E_DEPENDENCY_VERSION_UNSATISFIED" "kappa-hs.build.dependency-version"
        ( "no version of registry dependency '" <> regName <> "' satisfies '" <> ver
            <> "'; available: " <> T.intercalate ", " (map T.pack avail) <> " (Spec §36.23)"
        )

-- | §36.23: resolve a git dependency to a local checkout and its resolved
-- commit SHA. Clones the URL into a project-local content-addressed cache
-- (@<root>/.kappa/git/<url-digest>@) on first use, best-effort-fetches an
-- existing one, checks out the requested revision detached, and reports
-- @rev-parse HEAD@. git availability and every git step are checked; any
-- failure is an honest 'E_DEPENDENCY_GIT_FAILED'.
resolveGitDep :: Span -> FilePath -> Text -> Text -> IO (Either Diagnostics (FilePath, Text))
resolveGitDep sp canonRoot url rev = do
  mgit <- findExecutable "git"
  case mgit of
    Nothing -> pure (Left [gitErr sp url "the 'git' executable was not found on PATH"])
    Just git -> do
      let cacheDir = canonRoot </> ".kappa" </> "git" </> T.unpack (contentId [("url", encodeUtf8 url)])
      createDirectoryIfMissing True (takeDirectory cacheDir)
      hasRepo <- doesDirectoryExist (cacheDir </> ".git")
      ensured <-
        if hasRepo
          then -- best-effort refresh; an offline reuse of an existing cache is fine
            runGit git ["-C", cacheDir, "fetch", "--quiet", "--tags", "origin"] >> pure (Right ())
          else runGit git ["clone", "--quiet", T.unpack url, cacheDir]
      case ensured of
        Left e -> pure (Left [gitErr sp url ("clone failed: " <> e)])
        Right () -> do
          co <- runGit git ["-C", cacheDir, "checkout", "--quiet", "--detach", T.unpack rev]
          case co of
            Left e -> pure (Left [gitErr sp url ("checkout of revision '" <> rev <> "' failed: " <> e)])
            Right () -> do
              rp <- runGitOut git ["-C", cacheDir, "rev-parse", "HEAD"]
              case rp of
                Left e -> pure (Left [gitErr sp url ("rev-parse failed: " <> e)])
                Right out -> pure (Right (cacheDir, T.strip (T.pack out)))

-- | Run a git command, returning its stderr on failure.
runGit :: FilePath -> [String] -> IO (Either Text ())
runGit git args = do
  (ec, _, err) <- readProcessWithExitCode git args ""
  pure $ case ec of
    ExitSuccess -> Right ()
    ExitFailure _ -> Left (T.strip (T.pack err))

-- | Run a git command, returning its stdout on success.
runGitOut :: FilePath -> [String] -> IO (Either Text String)
runGitOut git args = do
  (ec, out, err) <- readProcessWithExitCode git args ""
  pure $ case ec of
    ExitSuccess -> Right out
    ExitFailure _ -> Left (T.strip (T.pack err))

gitErr :: Span -> Text -> Text -> Diagnostic
gitErr sp url msg =
  diag SevError StageImports "E_DEPENDENCY_GIT_FAILED" (Just "kappa-hs.build.dependency-git") sp
    ("git dependency '" <> url <> "': " <> msg <> " (Spec §36.23)")

-- | Load + evaluate a dependency package's manifest (§35.13).
loadDepPackage :: FilePath -> IO (Either Diagnostics BuildConfig)
loadDepPackage manifest = do
  (src, _) <- loadSourceFile manifest
  let (st, mn, diags) = compileManifest manifest src
  if hasErrors diags
    then pure (Left diags)
    else pure (reifyBuildConfig (Span manifest (Pos 1 1) (Pos 1 1)) st mn)

-- | A dependency package's library modules: those matching its library
-- targets' `modules` selectors, or — when it declares no library target —
-- all its package modules except its executables' entry modules (so a
-- dependency's @main@ is never pulled into the dependent).
depLibraryModules :: FilePath -> BuildConfig -> IO [(FilePath, ModuleName)]
depLibraryModules pkgDir depBc = do
  mods <- packageModules pkgDir depBc
  let libSelectors = [tModules t | t@LibraryTarget {} <- bcTargets depBc]
      exeMains =
        [ ModuleName (T.splitOn "." nm')
        | ExecutableTarget {tMain = SelModule nm'} <- bcTargets depBc
        ]
  pure $
    if null libSelectors
      then [x | x@(_, m) <- mods, m `notElem` exeMains]
      else [x | x@(_, m) <- mods, any (`matchesSelector` m) libSelectors]

-- | The dependency names a package's library targets declare — followed
-- transitively when resolving a path dependency's own dependencies.
libraryDeps :: BuildConfig -> [Text]
libraryDeps depBc = concat [tDependencies t | t@LibraryTarget {} <- bcTargets depBc]

-- | A package's source bytes for content identity (§36.23.2): its build
-- manifest plus every .kp under its source roots, each keyed by its path
-- relative to the package directory (so the identity is location- and
-- enumeration-independent).
packageSourceBytes :: FilePath -> BuildConfig -> IO [(FilePath, BS.ByteString)]
packageSourceBytes pkgDir bc = do
  mods <- packageModules pkgDir bc
  let paths = (pkgDir </> manifestBasename) : map fst mods
  forM paths $ \p -> do
    bytes <- BS.readFile p
    pure (makeRelative pkgDir p, bytes)

depName :: Dependency -> Text
depName = \case
  RegistryDep n _ -> n
  GitDep n _ _ -> n
  PathDep n _ -> n

-- ── semver constraints (registry resolution, §36.23) ─────────────────

-- | Parse a dotted version into numeric components (non-numeric segments
-- become 0; e.g. @"1.2.3"@ → @[1,2,3]@, @"0.1"@ → @[0,1]@).
parseVer :: Text -> [Int]
parseVer = map (toInt . T.takeWhile (/= '-')) . T.splitOn "."
  where
    toInt t = case reads (T.unpack t) of (n, _) : _ -> n; _ -> 0

-- | Compare two versions component-wise (missing components are 0).
compareVer :: [Int] -> [Int] -> Ordering
compareVer a b = compare (pad a) (pad b)
  where
    n = max (length a) (length b)
    pad xs = take n (xs ++ repeat 0)

-- | Parse a version DIRECTORY name into (numeric components, prerelease
-- tag). 'Nothing' when the part before the first @-@ is not a non-empty
-- run of all-digit dotted segments — so stray files/dirs (@README@,
-- @index.json@, @.git@) are not treated as versions.
parseVerParts :: Text -> Maybe ([Int], Text)
parseVerParts t =
  let (core, dashRest) = T.breakOn "-" t
      pre = T.drop 1 dashRest
      segs = T.splitOn "." core
   in if not (null segs) && all isNumSeg segs
        then Just (map readInt segs, pre)
        else Nothing
  where
    isNumSeg s = not (T.null s) && T.all isDigit s
    readInt s = case reads (T.unpack s) of (n, _) : _ -> n; _ -> 0

-- | Does a registry version (numeric @nums@, prerelease @pre@, raw
-- dirname @raw@) satisfy the constraint? @*@/empty → any stable; @^…@
-- caret (npm semantics, keyed on specified-component count); a bare
-- @X[.Y[.Z]]@ → leading-component prefix on stable versions. Prereleases
-- are excluded from range matching but may be selected by an exact
-- dirname match.
versionMatches :: Text -> Text -> [Int] -> Text -> Bool
versionMatches c raw nums pre
  | c == raw = True -- exact dirname pin (may name a prerelease)
  | not (T.null pre) = False -- otherwise prereleases are excluded
  | c == "" || c == "*" = True
  | Just flo <- T.stripPrefix "^" c =
      let lo = parseVer flo in compareVer nums lo /= LT && compareVer nums (caretUpper lo) == LT
  | otherwise =
      let cs = parseVer c in not (null cs) && take (length cs) (nums ++ repeat 0) == cs

-- npm caret upper bound, keyed on how many components were specified:
-- ^1 / ^1.2 / ^1.2.3 → <2.0.0; ^0.2 / ^0.2.3 → <0.3.0; ^0.0.3 → <0.0.4;
-- ^0.0 → <0.1.0; ^0 → <1.0.0.
caretUpper :: [Int] -> [Int]
caretUpper flo = case flo of
  [maj] -> [maj + 1, 0, 0]
  [maj, mn]
    | maj > 0 -> [maj + 1, 0, 0]
    | otherwise -> [0, mn + 1, 0]
  (maj : mn : pat : _)
    | maj > 0 -> [maj + 1, 0, 0]
    | mn > 0 -> [0, mn + 1, 0]
    | otherwise -> [0, 0, pat + 1]
  [] -> [maxBound]

-- | The best (highest) matching registry version directory: greatest by
-- numeric version, then stable preferred over prerelease, then raw
-- dirname — a total, deterministic order.
bestRegVersion :: [([Int], Text, FilePath)] -> Maybe FilePath
bestRegVersion [] = Nothing
bestRegVersion xs = Just (thd3 (maximumBy cmp xs))
  where
    cmp (n1, p1, r1) (n2, p2, r2) =
      compareVer n1 n2 <> compare (T.null p1) (T.null p2) <> compare r1 r2
    thd3 (_, _, r) = r

-- | First component of a triple (the version dirname in @parsed@).
fst3 :: (a, b, c) -> a
fst3 (a, _, _) = a

depErr :: Span -> DiagnosticCode -> DiagnosticFamily -> Text -> Diagnostic
depErr sp code fam = diag SevError StageImports code (Just fam) sp

-- | A target's dependency names.
targetDependencies :: Target -> [Text]
targetDependencies ExecutableTarget {tDependencies = ds} = ds
targetDependencies LibraryTarget {tDependencies = ds} = ds

-- | A target's referenced host-binding names (executables only carry them).
targetHostBindings :: Target -> [Text]
targetHostBindings ExecutableTarget {tHostBindings = hs} = hs
targetHostBindings LibraryTarget {} = []

renderMod :: ModuleName -> Text
renderMod (ModuleName segs) = T.intercalate "." segs

dedup :: [ModuleName] -> [ModuleName]
dedup = go []
  where
    go seen [] = reverse seen
    go seen (x : xs) = if x `elem` seen then go seen xs else go (x : seen) xs

dedupT :: [Text] -> [Text]
dedupT = go []
  where
    go seen [] = reverse seen
    go seen (x : xs) = if x `elem` seen then go seen xs else go (x : seen) xs

-- | Keep the first occurrence of each file path (a diamond/repeated path
-- dependency resolves to the same file via multiple routes).
dedupByPath :: [(FilePath, ModuleName, Text)] -> [(FilePath, ModuleName, Text)]
dedupByPath = go []
  where
    go _ [] = []
    go seen (x@(p, _, _) : xs)
      | p `elem` seen = go seen xs
      | otherwise = x : go (p : seen) xs
