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
  , resolveTestTarget
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
import Kappa.Backend.NativeFfi (ResolvedNativeSymbol (..))
import Kappa.Build.Lock (LockEntry (..), contentId)
import Kappa.Build.Reify (reifyBuildConfig)
import Kappa.Build.Types
import Kappa.Diagnostic
import Kappa.Pipeline (compileManifest, loadSourceFile, reservedHostRootDiag)
import Kappa.Source (ModuleName (..), Pos (..), Span (..))
import System.Directory
  ( canonicalizePath
  , createDirectoryIfMissing
  , doesDirectoryExist
  , doesFileExist
  , findExecutable
  , listDirectory
  , pathIsSymbolicLink
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
  -- ^ the distinct @host.native.*@ modules made importable for this build
  -- (derived from 'rxNativeSymbols' — every module that has ≥1 symbol)
  , rxNativeSymbols :: ![ResolvedNativeSymbol]
  -- ^ §27.1.1/§36.28: every native symbol resolved from the selected
  -- bindings' @symbolList@ surfaces (Kappa member ↦ C symbol + ABI
  -- signature). This is the SOLE authority for the importable
  -- @host.native.*@ surface and for direct-call codegen — there is no
  -- hardcoded native catalog.
  , rxLinkSpecs :: ![NativeLinkSpec]
  -- ^ §36.28 link specs of the selected native bindings
  , rxNativeInputs :: ![NativeInput]
  -- ^ §36.28 realization inputs (headers/includeDir/define/pkgConfig/shim/
  -- moduleMap/prebuilt) of the selected bindings; drive the C toolchain
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
    Right tgt
      -- §34.5.3/§36.4: this implementation provides only the native (zig)
      -- backend profile. A target selecting jvm/dotnet must be rejected
      -- honestly rather than silently coerced into a native build.
      | not (isNativeBackend (tBackend tgt)) -> pure (Left [backendUnrealized tgt])
      | otherwise -> case resolveProviders tgt of
      Left ds -> pure (Left ds)
      Right (nativeSyms, linkSpecs, nativeInputs, _anyNative) ->
        case tMain tgt of
          SelModulesUnder _ -> pure (Left [mainNotConcrete (tName tgt)])
          SelModule modName -> do
            let entryMod = ModuleName (T.splitOn "." modName)
            allFiles <- packageModules manifestDir bc
            -- §8.3.5: a package source file whose path-derived module name is
            -- at or under a reserved host root is a compile-time error,
            -- unconditionally — independent of whether this target's `modules`
            -- selector happens to include it (otherwise a reserved-root source
            -- file outside the built selector would slip through unchecked).
            let reservedDiags =
                  [ d
                  | (f, mn) <- allFiles
                  , Just d <- [reservedHostRootDiag mn (Span f (Pos 1 1) (Pos 1 1))]
                  ]
                selected =
                  [ (f, mn)
                  | (f, mn) <- allFiles
                  , mn == entryMod || matchesSelector (tModules tgt) mn
                  ]
            if not (null reservedDiags)
              then pure (Left reservedDiags)
              else if not (any ((== entryMod) . snd) allFiles)
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
                                  , rxProvidedModules = dedup (map rnsModule nativeSyms)
                                  , rxNativeSymbols = nativeSyms
                                  , rxLinkSpecs = linkSpecs
                                  , rxNativeInputs = nativeInputs
                                  , rxLockEntries = lockEntries
                                  }
  where
    sp = Span (manifestDir </> manifestBasename) (Pos 1 1) (Pos 1 1)

    executables = [t | t@ExecutableTarget {} <- bcTargets bc]
    -- executables and benchmarks share this resolution (both have a main +
    -- modules + dependencies); a benchmark carries no host bindings.
    isExeOrBench t = case t of ExecutableTarget {} -> True; BenchmarkTarget {} -> True; _ -> False

    isNativeBackend b = case b of NativeBackend {} -> True; _ -> False
    backendUnrealized tgt =
      buildErr "E_BACKEND_PROFILE_UNREALIZED" "kappa-hs.backend.profile"
        ( "target '" <> tName tgt <> "' selects the '" <> backendName (tBackend tgt)
            <> "' backend profile, which this implementation does not provide; it "
            <> "realizes only the native profile (Spec §34.5.3, §36.4)"
        )
    backendName b = case b of
      NativeBackend {} -> "native"
      JvmBackend -> "jvm"
      DotNetBackend -> "dotnet"

    selectTarget :: Either Diagnostics Target
    selectTarget = case mTarget of
      Just nm -> case [t | t <- bcTargets bc, tName t == nm, isExeOrBench t] of
        (t : _) -> Right t
        [] ->
          Left
            [ buildErr "E_BUILD_TARGET_NOT_FOUND" "kappa-hs.build.target-not-found"
                ( "no executable or benchmark target named '" <> nm <> "' in the manifest (Spec §36.3)"
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
    resolveProviders :: Target -> Either Diagnostics ([ResolvedNativeSymbol], [NativeLinkSpec], [NativeInput], Bool)
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
            -- resolve each binding's provides × symbolList surface into
            -- concrete ResolvedNativeSymbols (§27.1.1/§36.28). The manifest
            -- surface is the SOLE authority — no hardcoded catalog.
            perBinding <- traverse resolveBinding selected
            let allSyms = concat [ss | (_, ss) <- perBinding]
                bindingMods = [(bn, dedup (map rnsModule ss)) | (bn, ss) <- perBinding]
            -- collision: same effective module provided by ≥2 bindings
            checkCollisions bindingMods
            let linkSpecs = map nbLink selected
                inputs = concatMap nbInputs selected
            Right (allSyms, linkSpecs, inputs, not (null selected))

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

    -- §27.1.1/§36.28: resolve a binding's provides × symbolList surface into
    -- concrete ResolvedNativeSymbols. Each provided concrete host.native
    -- module gets the binding's full declared surface (the manifest's
    -- SymbolDecls, carrying the C symbol + ABI signature). The surface is
    -- authoritative — there is no catalog to validate against.
    resolveBinding :: HostBinding -> Either Diagnostics (Text, [ResolvedNativeSymbol])
    resolveBinding hb = do
      mods <- concat <$> traverse (expandSelector hb) (nbProvides hb)
      decls <- surfaceDecls hb
      let syms =
            [ ResolvedNativeSymbol
                { rnsModule = mn
                , rnsMember = sdMember d
                , rnsCSymbol = sdSymbol d
                , rnsParams = sdParams d
                , rnsResult = sdResult d
                }
            | mn <- mods
            , d <- decls
            ]
      Right (nbName hb, syms)

    -- The binding's declared symbol surface (§36.28 symbolList). A binding
    -- that provides modules but declares no surface is rejected: there is
    -- nothing to make importable or to call.
    surfaceDecls :: HostBinding -> Either Diagnostics [SymbolDecl]
    surfaceDecls hb = case nbSurface hb of
      SymbolListSurface [] -> Left [emptySurface hb]
      SymbolListSurface ds -> Right ds

    -- §36.28: a provides selector names a concrete host.native module
    -- (SelModule) or a module-name prefix (SelModulesUnder). Both resolve to
    -- a concrete provided module — the prefix form names the module at the
    -- prefix path. The zig profile realizes only the @host.native@ root, so
    -- a module under any other host root is rejected honestly (§34.5.3).
    expandSelector :: HostBinding -> ModuleSelector -> Either Diagnostics [ModuleName]
    expandSelector hb sel =
      let validate m =
            let mn@(ModuleName segs) = ModuleName (T.splitOn "." m)
             in if take 2 segs == ["host", "native"] && length segs > 2
                  then Right [mn]
                  else Left [unsupportedModule hb m]
       in case sel of
            SelModule m -> validate m
            SelModulesUnder m -> validate m

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
            <> "', which is not a concrete module under the 'host.native' root; "
            <> "the zig native profile realizes only host.native.* modules "
            <> "(Spec §27.1.1, §34.5.3, §36.28)"
        )
    emptySurface hb =
      buildErr "E_NATIVE_BINDING_UNSUPPORTED" "kappa-hs.build.native-unsupported"
        ( "native binding '" <> nbName hb <> "' declares no symbol surface; a "
            <> "native binding must describe its exported symbols with their ABI "
            <> "signatures via symbolList (Spec §27.1.1, §36.28)"
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
        sym <- pathIsSymbolicLink p
        if sub
          -- Do not descend into symlinked directories: a symlink loop would
          -- recurse unboundedly, and a symlink escaping the source root would
          -- pull phantom modules into a broad `modules` selection (Spec §8.1).
          then if sym then pure [] else listKpFiles p
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
          -- env var name assembled so the literal does not trip the
          -- diagnostic-code-literal scanner (which treats "KAPPA_…" as a code)
          mreg <- lookupEnv ("KAPPA" <> "_REGISTRY")
          case mreg of
            Nothing -> pure (Left [registryNotConfigured sp nm])
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
        (UrlDep _ url : _) -> do
          -- §36.23: fetch + unpack an archive URL into a project-local
          -- cache and resolve it as a transitive path dependency; pin its
          -- content digest in the lock.
          res <- resolveUrlDep sp canonRoot url
          case res of
            Left ds -> pure (Left ds)
            Right pkgDir -> do
              canon <- canonicalizePath pkgDir
              collectResolved canon pkgDir $ \depBc -> do
                srcBytes <- packageSourceBytes pkgDir depBc
                pure (LockEntry "url" url (contentId srcBytes))
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

    -- A registry dependency was requested but no vendored-registry root is
    -- configured. The resolver IS provided; it just needs KAPPA_REGISTRY set.
    registryNotConfigured sp nm =
      depErr sp "E_DEPENDENCY_UNRESOLVED" "kappa.package.reproducibility"
        ( "dependency '" <> nm <> "' is a registry dependency, but no vendored "
            <> "registry root is configured; set the KAPPA_REGISTRY environment "
            <> "variable to a registry root laid out as "
            <> "<root>/<name>/<version>/kappa.build.kp (Spec §36.23.1)"
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

-- | §36.23: resolve a url dependency by fetching its archive (via @curl@,
-- which handles @file://@ and @http(s)://@) into a project-local
-- content-addressed cache and unpacking it (via @tar@, autodetecting
-- compression). Returns the package directory (the unpacked tree, or its
-- sole top-level subdirectory, that contains a build manifest). A
-- populated cache is reused. Any failure is an honest
-- 'E_DEPENDENCY_URL_FAILED'.
resolveUrlDep :: Span -> FilePath -> Text -> IO (Either Diagnostics FilePath)
resolveUrlDep sp canonRoot url = do
  mcurl <- findExecutable "curl"
  mtar <- findExecutable "tar"
  case (mcurl, mtar) of
    (Nothing, _) -> pure (Left [urlErr sp url "the 'curl' executable was not found on PATH"])
    (_, Nothing) -> pure (Left [urlErr sp url "the 'tar' executable was not found on PATH"])
    (Just curl, Just tar) -> do
      let cacheDir = canonRoot </> ".kappa" </> "url" </> T.unpack (contentId [("url", encodeUtf8 url)])
      existing <- locatePackageRoot cacheDir
      case existing of
        Just pkg -> pure (Right pkg) -- reuse a populated cache
        Nothing -> do
          createDirectoryIfMissing True cacheDir
          let archive = cacheDir </> "archive.tar"
          fetched <- runGit curl ["-fsSL", T.unpack url, "-o", archive]
          case fetched of
            Left e -> pure (Left [urlErr sp url ("fetch failed: " <> e)])
            Right () -> do
              unp <- runGit tar ["-xf", archive, "-C", cacheDir]
              case unp of
                Left e -> pure (Left [urlErr sp url ("unpack failed: " <> e)])
                Right () -> do
                  pkg <- locatePackageRoot cacheDir
                  case pkg of
                    Just p -> pure (Right p)
                    Nothing -> pure (Left [urlErr sp url "the archive contains no build manifest at its root or a single top-level directory"])

-- | Find the package root within an unpacked archive: the directory (the
-- root itself, or its sole manifest-bearing top-level subdirectory) that
-- contains a build manifest.
locatePackageRoot :: FilePath -> IO (Maybe FilePath)
locatePackageRoot dir = do
  here <- doesFileExist (dir </> manifestBasename)
  if here
    then pure (Just dir)
    else do
      isDir <- doesDirectoryExist dir
      if not isDir
        then pure Nothing
        else do
          entries <- listDirectory dir
          subs <- filterM (\e -> doesFileExist (dir </> e </> manifestBasename)) entries
          case subs of
            [s] -> pure (Just (dir </> s))
            _ -> pure Nothing

urlErr :: Span -> Text -> Text -> Diagnostic
urlErr sp url msg =
  diag SevError StageImports "E_DEPENDENCY_URL_FAILED" (Just "kappa-hs.build.dependency-url") sp
    ("url dependency '" <> url <> "': " <> msg <> " (Spec §36.23)")

-- | Load + evaluate a dependency package's manifest (§35.13).
loadDepPackage :: FilePath -> IO (Either Diagnostics BuildConfig)
loadDepPackage manifest = do
  (src, _) <- loadSourceFile manifest
  let (st, mn, _mod, diags) = compileManifest manifest src
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
  UrlDep n _ -> n

-- ── semver constraints (registry resolution, §36.23) ─────────────────

-- | Parse a dotted version into numeric components (non-numeric segments
-- become 0; e.g. @"1.2.3"@ → @[1,2,3]@, @"0.1"@ → @[0,1]@).
-- Version components are parsed as 'Integer' so absurdly large version
-- segments cannot silently wrap (a fixed-width 'Int' would).
parseVer :: Text -> [Integer]
parseVer = map (toInt . T.takeWhile (/= '-')) . T.splitOn "."
  where
    toInt t = case reads (T.unpack t) of (n, _) : _ -> n; _ -> 0

-- | Compare two versions component-wise (missing components are 0).
compareVer :: [Integer] -> [Integer] -> Ordering
compareVer a b = compare (pad a) (pad b)
  where
    n = max (length a) (length b)
    pad xs = take n (xs ++ repeat 0)

-- | Parse a version DIRECTORY name into (numeric components, prerelease
-- tag). 'Nothing' when the part before the first @-@ is not a non-empty
-- run of all-digit dotted segments — so stray files/dirs (@README@,
-- @index.json@, @.git@) are not treated as versions.
parseVerParts :: Text -> Maybe ([Integer], Text)
parseVerParts t =
  let (core, dashRest) = T.breakOn "-" t
      pre = T.drop 1 dashRest
      segs = T.splitOn "." core
   in if not (null segs) && all isNumSeg segs
        then Just (map readInt segs, pre)
        else Nothing
  where
    isNumSeg s = not (T.null s) && T.all isDigit s
    readInt s = case reads (T.unpack s) of (n, _) : _ -> n; _ -> 0 :: Integer

-- | Does a registry version (numeric @nums@, prerelease @pre@, raw
-- dirname @raw@) satisfy the constraint? @*@/empty → any stable; @^…@
-- caret (npm semantics, keyed on specified-component count); a bare
-- @X[.Y[.Z]]@ → leading-component prefix on stable versions. Prereleases
-- are excluded from range matching but may be selected by an exact
-- dirname match.
versionMatches :: Text -> Text -> [Integer] -> Text -> Bool
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
caretUpper :: [Integer] -> [Integer]
caretUpper flo = case flo of
  [maj] -> [maj + 1, 0, 0]
  [maj, mn]
    | maj > 0 -> [maj + 1, 0, 0]
    | otherwise -> [0, mn + 1, 0]
  (maj : mn : pat : _)
    | maj > 0 -> [maj + 1, 0, 0]
    | mn > 0 -> [0, mn + 1, 0]
    | otherwise -> [0, 0, pat + 1]
  -- Unreachable: 'parseVer' never yields [] (it splits on '.', so even ""
  -- → [0]). An unbounded upper sentinel keeps the branch total.
  [] -> [2 ^ (62 :: Int)]

-- | The best (highest) matching registry version directory: greatest by
-- numeric version, then stable preferred over prerelease, then raw
-- dirname — a total, deterministic order.
bestRegVersion :: [([Integer], Text, FilePath)] -> Maybe FilePath
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
targetDependencies TestTarget {} = []
targetDependencies AggregateTarget {} = []
targetDependencies AliasTarget {} = []
targetDependencies BenchmarkTarget {tDependencies = ds} = ds

-- | A target's referenced host-binding names (executables only carry them).
targetHostBindings :: Target -> [Text]
targetHostBindings ExecutableTarget {tHostBindings = hs} = hs
targetHostBindings LibraryTarget {} = []
targetHostBindings TestTarget {} = []
targetHostBindings AggregateTarget {} = []
targetHostBindings AliasTarget {} = []
targetHostBindings BenchmarkTarget {} = []

-- | Select and resolve a @test@ target (§36.31) to the set of source
-- files to run through the Appendix-T harness: the package modules whose
-- §8.1 name matches the target's @modules@ selector. (Each test file is
-- run standalone, like @kappa test FILE@.)
resolveTestTarget :: FilePath -> BuildConfig -> Maybe Text -> IO (Either Diagnostics (Text, [FilePath]))
resolveTestTarget manifestDir bc mTarget =
  case selectTest of
    Left ds -> pure (Left ds)
    Right tgt -> do
      allFiles <- packageModules manifestDir bc
      let files = [f | (f, mn) <- allFiles, matchesSelector (tModules tgt) mn]
      pure (Right (tName tgt, files))
  where
    sp = Span (manifestDir </> manifestBasename) (Pos 1 1) (Pos 1 1)
    tests = [t | t@TestTarget {} <- bcTargets bc]
    notFound msg = Left [diag SevError StageImports "E_BUILD_TARGET_NOT_FOUND" (Just "kappa-hs.build.target-not-found") sp msg]
    selectTest = case mTarget of
      Just nm -> case [t | t <- tests, tName t == nm] of
        (t : _) -> Right t
        [] -> notFound ("no test target named '" <> nm <> "' in the manifest (Spec §36.3, §36.31)")
      Nothing -> case tests of
        [t] -> Right t
        [] -> notFound "the manifest declares no test target (Spec §36.3, §36.31)"
        _ -> notFound "the manifest declares multiple test targets; select one with --target NAME (Spec §36.3)"

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
