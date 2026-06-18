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

import Control.Monad (forM)
import Data.List (foldl', sortOn)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Backend.NativeCatalog
  ( CatalogMember (..)
  , CatalogModule (..)
  , catalogModule
  )
import Kappa.Build.Types
import Kappa.Diagnostic
import Kappa.Source (ModuleName (..), Pos (..), Span (..))
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (makeRelative, splitDirectories, takeExtension, takeFileName, (</>))

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
            allFiles <- enumerateSources
            let selected =
                  [ (f, mn)
                  | (f, mn) <- allFiles
                  , mn == entryMod || matchesSelector (tModules tgt) mn
                  ]
            pure $
              if not (any ((== entryMod) . snd) allFiles)
                then Left [entryNotFound (tName tgt) modName]
                else case caseFoldCollision selected of
                  Just ds -> Left ds
                  Nothing ->
                    Right
                      ResolvedExe
                        { rxName = tName tgt
                        , rxEntryModule = entryMod
                        , rxSourceFiles = selected
                        , rxProvidedModules = providedMods
                        , rxLinkSpecs = linkSpecs
                        , rxRuntimeFfi = anyNative
                        }
  where
    sp = Span (manifestDir </> "kappa.build.kp") (Pos 1 1) (Pos 1 1)

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

    -- §36.4: every .kp under each source root, paired with its §8.1
    -- path-derived module name (relative to that root). A file belongs to
    -- exactly one root (the one it is found under).
    enumerateSources :: IO [(FilePath, ModuleName)]
    enumerateSources = do
      perRoot <- forM (bcSourceRoots bc) $ \r -> do
        let rootDir = manifestDir </> T.unpack (srPath r)
        fs <- listKpFiles rootDir
        pure [(f, deriveModule rootDir f) | f <- fs]
      -- §8.1: sort by path so fragment-merge/diagnostic order and the
      -- artifact representative are deterministic (independent of the
      -- OS directory-listing order).
      pure (sortOn fst (concat perRoot))

    -- §36.3 `modules` selector: which package modules belong to the target.
    matchesSelector :: ModuleSelector -> ModuleName -> Bool
    matchesSelector sel (ModuleName segs) = case sel of
      SelModule m -> segs == T.splitOn "." m
      SelModulesUnder p -> let ps = T.splitOn "." p in take (length ps) segs == ps

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
