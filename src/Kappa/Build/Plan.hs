-- | A minimal build-plan resolution slice (§36.4) sufficient to build one
-- executable target from a reified manifest: select the target, resolve
-- its host-binding providers (§36.28) against the native catalog with
-- collision and realizability checks, and locate its entry module under
-- the package source roots. This is the step AFTER manifest evaluation
-- (§35.13 forbids the manifest itself from doing any of this) and BEFORE
-- codegen. Full source-root enumeration, dependency resolution, and
-- multi-target/workspace planning are later increments.
module Kappa.Build.Plan
  ( ResolvedExe (..)
  , resolveExecutable
  ) where

import Data.List (foldl')
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
import System.Directory (doesFileExist)
import System.FilePath ((<.>), (</>))

-- | A resolved, buildable executable target.
data ResolvedExe = ResolvedExe
  { rxName :: !Text
  , rxEntryFile :: !FilePath
  -- ^ the located @.kp@ source file for the target's main module
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
          SelModule modName -> do
            mEntry <- locateEntry modName
            pure $ case mEntry of
              Nothing -> Left [entryNotFound (tName tgt) modName]
              Just f ->
                Right
                  ResolvedExe
                    { rxName = tName tgt
                    , rxEntryFile = f
                    , rxProvidedModules = providedMods
                    , rxLinkSpecs = linkSpecs
                    , rxRuntimeFfi = anyNative
                    }
          SelModulesUnder _ ->
            pure (Left [mainNotConcrete (tName tgt)])
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

    locateEntry :: Text -> IO (Maybe FilePath)
    locateEntry modName =
      let rel = foldr (</>) "" (map T.unpack (T.splitOn "." modName)) <.> "kp"
          candidates = [manifestDir </> T.unpack (srPath r) </> rel | r <- bcSourceRoots bc]
       in firstExisting candidates

    firstExisting [] = pure Nothing
    firstExisting (f : fs) = do
      ok <- doesFileExist f
      if ok then pure (Just f) else firstExisting fs

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
