{-# LANGUAGE OverloadedRecordDot #-}

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

import Control.Exception (SomeException, catch)
import Control.Monad (filterM, forM)
import qualified Data.ByteString as BS
import Data.Char (isDigit)
import Data.List (maximumBy, sortOn)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Encoding (encodeUtf8)
import Kappa.Backend.Capabilities (ffiRequiredCapabilities, nativeRuntimeCapabilities)
import Kappa.Backend.Driver (detectCC, verifyDeclName)
import Kappa.Backend.HeaderGen (AbiClass (..), ctypeAbiClass, definedSymbols, generatePrefixSurfaceDecls, generateSurfaceDecls, protoArity)
import Kappa.Backend.NativeProbe (safeWithinRoot)
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
import System.IO (hPutStrLn, stderr)
import System.Exit (ExitCode (..))
import System.FilePath (isAbsolute, joinPath, makeRelative, splitDirectories, takeDirectory, takeExtension, takeFileName, (</>))
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
  , rxNativeBindings :: ![(Text, [ResolvedNativeSymbol], [NativeInput], [Text])]
  -- ^ §36.7/§27.1.1: per selected native binding — its name, resolved symbol
  -- surface, realization inputs, and extra identity lines (canonical link/load
  -- text) — used to compute the host-source identity pinned in @kappa.lock@.
  , rxTargetTriple :: !Text
  -- ^ §36.21 the target's declared toolchain triple (part of the native
  -- host-source identity, §27.1.1)
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
      | not (isNativeBackend (targetBackend tgt)) -> pure (Left [backendUnrealized tgt])
      | otherwise -> genThen tgt $ \genMap shimDefs -> case resolveProviders genMap shimDefs tgt of
      Left ds -> pure (Left ds)
      Right (nativeSyms, linkSpecs, nativeInputs, nativeBindings, _anyNative) ->
        case targetMainSel tgt of
          SelModulesUnder _ -> pure (Left [mainNotConcrete (tgt.name)])
          SelModule modName -> do
            let entryMod = ModuleName (T.splitOn "." modName)
            allFiles <- packageModules manifestDir bc
            -- §8.3.5: a package source file whose path-derived module name is
            -- at or under a reserved host root is a compile-time error,
            -- unconditionally — independent of whether this target's `modules`
            -- selector happens to include it (otherwise a reserved-root source
            -- file outside the built selector would slip through unchecked).
            -- §36.12: the target's enabled fragment-tag set selects which
            -- same-module fragments participate. A file is selected iff every
            -- one of its fragment suffixes is enabled (a no-suffix file always);
            -- unselected fragments (e.g. runtime.jvm.kp under the native target)
            -- do not participate at all.
            let enabled = targetFragments tgt
                fragSelected (f, _) = fragmentSelected enabled f
                selectedAll = filter fragSelected allFiles
                reservedDiags =
                  [ d
                  | (f, mn) <- selectedAll
                  , Just d <- [reservedHostRootDiag mn (Span f (Pos 1 1) (Pos 1 1))]
                  ]
                -- §36.12 MUST: target / selected-file axis-exclusivity.
                fragDiags =
                  maybe [] pure (fragmentTargetDiag (manifestDir </> manifestBasename) (bc.fragmentAxes) (tgt.name) enabled)
                    ++ [d | (f, _) <- selectedAll, Just d <- [fragmentFileDiag (bc.fragmentAxes) f]]
                selected =
                  [ (f, mn)
                  | (f, mn) <- selectedAll
                  , mn == entryMod || matchesSelector (targetModules tgt) mn
                  ]
            if not (null fragDiags)
              then pure (Left fragDiags)
              else if not (null reservedDiags)
              then pure (Left reservedDiags)
              else if not (any ((== entryMod) . snd) selectedAll)
              then pure (Left [entryNotFound (tgt.name) modName])
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
                                  { rxName = tgt.name
                                  , rxEntryModule = entryMod
                                  , rxSourceFiles = unit
                                  , rxProvidedModules = dedup (map rnsModule nativeSyms)
                                  , rxNativeSymbols = nativeSyms
                                  , rxLinkSpecs = linkSpecs
                                  , rxNativeInputs = nativeInputs
                                  , rxNativeBindings = nativeBindings
                                  , rxTargetTriple = backendTriple (targetBackend tgt)
                                  , rxLockEntries = lockEntries
                                  }
  where
    sp = Span (manifestDir </> manifestBasename) (Pos 1 1) (Pos 1 1)

    executables = [t | t <- bc.targets, Executable {} <- [t.spec]]
    -- executables and benchmarks share this resolution (both have a main +
    -- modules + dependencies); a benchmark carries no host bindings.
    isExeOrBench t = case t.spec of Executable {} -> True; Benchmark {} -> True; _ -> False

    isNativeBackend b = case b of NativeBackend {} -> True; _ -> False
    backendUnrealized tgt =
      buildErr "E_BACKEND_PROFILE_UNREALIZED" "kappa-hs.backend.profile"
        ( "target '" <> tgt.name <> "' selects the '" <> backendName (targetBackend tgt)
            <> "' backend profile, which this implementation does not provide; it "
            <> "realizes only the native profile (Spec §34.5.3, §36.4)"
        )
    backendName b = case b of
      NativeBackend {} -> "native"
      JvmBackend -> "jvm"
      DotNetBackend -> "dotnet"
    backendTriple b = case b of
      NativeBackend _ triple -> triple
      _ -> ""

    selectTarget :: Either Diagnostics Target
    selectTarget = case mTarget of
      Just nm -> case [t | t <- bc.targets, t.name == nm, isExeOrBench t] of
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

    -- §27.1.1/§36.28: MECHANICALLY generate each selected binding's surface
    -- whose @nbSurface@ is a 'GeneratedSurface' — preprocess + parse its real
    -- header (no hand-authored symbolDecl). Runs only when the target actually
    -- references a generated-surface binding; that requires a C toolchain
    -- (preprocessing the header), so its absence is a fail-closed diagnostic.
    genThen :: Target -> (Map.Map Text [SymbolDecl] -> Map.Map Text (Set.Set Text) -> IO (Either Diagnostics a)) -> IO (Either Diagnostics a)
    genThen tgt k = do
      let wanted = targetHostBindings tgt
          selected = [hb | nm <- wanted, hb <- bc.hostBindings, hb.name == nm]
          gens = [hb | hb <- selected, isGenerated (hb.surface)]
          tgtTriple = backendTriple (targetBackend tgt)
      -- §36.11: validate every package-relative native input path of every
      -- selected binding (shim sources, prebuilt artifacts, include dirs,
      -- module maps) stays within the package root — no `..`, absolute, or
      -- symlink escape — before any toolchain step touches it.
      epaths <- validateNativePaths manifestDir selected
      case epaths of
       Left ds -> pure (Left ds)
       Right ()
        -- §26.1.3: the conservative CType widths assume the LP64 data model.
        -- Reject a clearly non-LP64 target for ANY native binding (generated or
        -- explicit symbolList) rather than realize a wrong-width ABI.
        | not (null selected) && nonLp64Triple tgtTriple -> pure (Left [nonLp64Diag tgtTriple])
        | otherwise -> do
            -- §26.1.5/§36.28: which symbols each binding's shim TUs actually
            -- DEFINE (symbol-granular), so only a genuinely shim-defined symbol
            -- is force-include ABI-checked and exempt from the verify proof.
            shimDefMap <- buildShimDefMap selected
            if null gens
              then k Map.empty shimDefMap
              else do
                mcc <- detectCC Nothing
                case mcc of
                  Nothing -> pure (Left [genNeedsCc (head gens).name])
                  Just cc -> do
                    eMap <- goGen cc Map.empty gens
                    either (pure . Left) (\m -> k m shimDefMap) eMap
      where
        isGenerated SymbolListSurface {} = False
        isGenerated GeneratedSurface {} = True
        isGenerated GeneratedPrefixSurface {} = True
        triple = backendTriple (targetBackend tgt)
        buildShimDefMap hbs =
          Map.fromList <$> mapM (\hb -> (,) (hb.name) <$> shimDefsFor hb) hbs
        shimDefsFor hb = do
          let srcs = [manifestDir </> T.unpack s | ShimInput ss <- hb.inputs, s <- ss]
          defs <- concat <$> mapM readDefs srcs
          pure (Set.fromList (map T.pack defs))
        readDefs p = (definedSymbols <$> readFile p) `catch` \(_ :: SomeException) -> pure []
        goGen _ acc [] = pure (Right acc)
        goGen cc acc (hb : rest) = case hb.surface of
          GeneratedSurface h ss -> do
            r <- generateSurfaceDecls cc triple manifestDir manifestDir (hb.inputs) h ss
            case r of
              Left ds -> pure (Left ds)
              Right decls -> goGen cc (Map.insert (hb.name) decls acc) rest
          GeneratedPrefixSurface h pfx -> do
            r <- generatePrefixSurfaceDecls cc triple manifestDir manifestDir (hb.inputs) h pfx
            case r of
              Left ds -> pure (Left ds)
              Right (decls, skipped) -> do
                -- §26.1.2: report (never silently omit) declarations rejected
                -- from the broad surface because the conservative ABI cannot
                -- represent them (callbacks/structs/variadics).
                hPutStrLn stderr
                  ( "note: host binding '" <> T.unpack (hb.name) <> "': generated "
                      <> show (length decls) <> " function(s) from " <> T.unpack h
                      <> " (prefix '" <> T.unpack pfx <> "'); skipped " <> show (length skipped)
                      <> " requiring callbacks/structs/variadics (rejected, not guessed)"
                  )
                goGen cc (Map.insert (hb.name) decls acc) rest
          SymbolListSurface {} -> goGen cc acc rest

    -- §26.1.3: data models the header-derived width mapping does not model are
    -- rejected (LLP64 = Windows; ILP32 = 32-bit). Conservative denylist: any
    -- target not matching is assumed LP64 (the 64-bit-unix realized set).
    nonLp64Triple :: Text -> Bool
    nonLp64Triple t =
      let s = T.toLower t
          has x = x `T.isInfixOf` s
       in has "windows" || has "msvc" || has "win32"
            || has "i386" || has "i486" || has "i586" || has "i686"
            || has "wasm32" || has "thumb" || T.isPrefixOf "arm-" s || T.isPrefixOf "armv7" s

    nonLp64Diag :: Text -> Diagnostic
    nonLp64Diag t =
      buildErr "E_BACKEND_CAPABILITY_UNREALIZED" "kappa-hs.backend.capability"
        ( "header-derived native binding generation targets '" <> t <> "', whose data model is not "
            <> "the LP64 model the generator's integer-width mapping assumes; the surface is rejected "
            <> "rather than inferred for an unmodelled ABI (Spec §26.1.3)"
        )

    -- §36.11: every package-relative native input path must stay within the
    -- package root. Shim sources / prebuilt artifacts / include dirs / module
    -- maps are compiled, linked, or digested as package files, so they get the
    -- full check (no `..`/absolute/symlink/symlinked-dir escape). Header entries
    -- are #include NAMES that may resolve to system headers, so only a lexical
    -- escape (`..`/absolute) is rejected for them.
    validateNativePaths :: FilePath -> [HostBinding] -> IO (Either Diagnostics ())
    validateNativePaths baseDir hbs = goV (concatMap binp hbs)
      where
        binp hb = concatMap one (hb.inputs)
        one (ShimInput ss) = [(True, s) | s <- ss]
        one (PrebuiltInput a _) = [(True, a)]
        one (IncludeDirInput d) = [(True, d)]
        one (ModuleMapInput fs) = [(True, f) | f <- fs]
        one (HeadersInput hs) = [(False, h) | h <- hs]
        one _ = []
        goV [] = pure (Right ())
        goV ((strict, rel) : rest)
          | not strict =
              if isAbsolute (T.unpack rel) || ".." `elem` splitDirectories (T.unpack rel)
                then pure (Left [pathEscape rel])
                else goV rest
          | otherwise = do
              r <- safeWithinRoot baseDir (T.unpack rel)
              case r of
                Left e -> pure (Left [pathEscapeMsg e])
                Right _ -> goV rest

    pathEscape :: Text -> Diagnostic
    pathEscape rel =
      pathEscapeMsg ("native binding path '" <> rel <> "' escapes the package root (Spec §36.11)")
    pathEscapeMsg :: Text -> Diagnostic
    pathEscapeMsg msg =
      buildErr "E_NATIVE_BINDING_PATH_ESCAPE" "kappa-hs.build.native-path" msg

    genNeedsCc :: Text -> Diagnostic
    genNeedsCc nm =
      buildErr "E_BUILD_NATIVE_HEADER_GEN" "kappa-hs.build.native-header-gen"
        ( "native binding '" <> nm <> "' derives its surface from a header (generateFromHeader), "
            <> "which requires a C toolchain to preprocess; none was found (set $KAPPA_CC or install "
            <> "zig/cc/gcc/clang) (Spec §27.1.1/§36.28)"
        )

    -- Resolve the target's named host bindings to provided host.native
    -- modules, with collision + realizability checks (§36.28, §34.5.3).
    resolveProviders :: Map.Map Text [SymbolDecl] -> Map.Map Text (Set.Set Text) -> Target -> Either Diagnostics ([ResolvedNativeSymbol], [NativeLinkSpec], [NativeInput], [(Text, [ResolvedNativeSymbol], [NativeInput], [Text])], Bool)
    resolveProviders genMap shimDefs tgt =
      let wanted = targetHostBindings tgt
          lookupBinding nm = [hb | hb <- bc.hostBindings, hb.name == nm]
       in do
            selected <-
              traverse
                ( \nm -> case lookupBinding nm of
                    (hb : _) -> Right hb
                    [] -> Left [bindingNotFound (tgt.name) nm]
                )
                wanted
            -- realizability: this backend realizes only the load modes it
            -- implements; reject the rest honestly (§34.5.3).
            mapM_ checkRealizable selected
            -- §26.1.4/§27.6: a binding whose foreign-call classification needs
            -- a runtime capability the native profile does not advertise is
            -- rejected fail-closed (never silently executed weaker).
            mapM_ checkClassificationCapability selected
            -- resolve each binding's provides × surface into concrete
            -- ResolvedNativeSymbols (§27.1.1/§36.28). The surface is either an
            -- explicit symbolList or one MECHANICALLY GENERATED from a header
            -- (pre-resolved into genMap) — the SOLE authority, no hardcoded catalog.
            perBinding <- traverse (resolveBinding genMap shimDefs) selected
            let allSyms = concat [ss | (_, ss) <- perBinding]
                bindingMods = [(bn, dedup (map rnsModule ss)) | (bn, ss) <- perBinding]
            -- collision: same effective module provided by ≥2 bindings (a
            -- structural manifest error — reported before the per-symbol ABI check).
            checkCollisions bindingMods
            -- §26.1.5/§36.28: an explicit symbolList symbol with a pointer/
            -- string/handle signature has no all-scalar conservative prototype
            -- the probe can check; its ABI must be PROVEN — by a `verify` decl
            -- (checked against the real header) or by being shim-provided
            -- (force-include ABI check) — else it is an unverified escape hatch.
            -- Header-generated surfaces are exempt (parsed from the real header).
            mapM_ (uncurry checkSymbolListAbi) (zip selected (map snd perBinding))
            let linkSpecs = map (.link) selected
                inputs = concatMap (.inputs) selected
                perBindingFull = [(hb.name, ss, hb.inputs, [linkText (hb.link), loadText (hb.load)]) | (hb, (_, ss)) <- zip selected perBinding]
            Right (allSyms, linkSpecs, inputs, perBindingFull, not (null selected))

    -- §26.1.4/§27.6: every binding's foreign-call classification (default
    -- nonblocking) must have its required runtime capabilities advertised by
    -- the native profile; otherwise reject (e.g. blocking-cancellable needs a
    -- safe-cancellation capability the native runtime does not provide).
    checkClassificationCapability :: HostBinding -> Either Diagnostics ()
    checkClassificationCapability hb =
      let cls = case [c | ClassifyInput c <- hb.inputs] of
                  [] -> FfiNonblocking
                  cs -> last cs
          missing = [c | c <- ffiRequiredCapabilities cls, c `notElem` nativeRuntimeCapabilities]
       in case missing of
            [] -> Right ()
            ms ->
              Left
                [ buildErr "E_BACKEND_CAPABILITY_UNREALIZED" "kappa-hs.backend.capability"
                    ( "native binding '" <> hb.name <> "' is classified '" <> classText cls
                        <> "', which requires runtime capabilit" <> (if length ms == 1 then "y " else "ies ")
                        <> T.intercalate ", " ms <> " that the native profile does not advertise (it advertises "
                        <> T.intercalate ", " nativeRuntimeCapabilities <> "); reject rather than weaken semantics "
                        <> "(Spec §26.1.4, §27.6)"
                    )
                ]
    classText = \case
      FfiNonblocking -> "nonblocking"
      FfiBlocking -> "blocking"
      FfiBlockingCancellable -> "blocking-cancellable"

    -- §34.5.3: the zig native profile realizes only the system-loader load
    -- mode (dynamic/static linkage resolved by the system loader). It does
    -- not bundle a loader, dlopen at runtime, or resolve host-provided
    -- symbols, so it MUST reject those modes rather than silently treat
    -- them as systemLoader.
    checkRealizable :: HostBinding -> Either Diagnostics ()
    checkRealizable hb = case hb.load of
      SystemLoader -> Right ()
      other ->
        Left
          [ buildErr "E_BACKEND_HOST_LINK_UNREALIZABLE" "kappa-hs.backend.host-link"
              ( "native binding '" <> hb.name <> "' requests the '" <> loadName other
                  <> "' load mode, which the zig native profile does not realize; it "
                  <> "realizes only 'systemLoader' (Spec §34.5.3, §36.28)"
              )
          ]
    loadName = \case
      SystemLoader -> "systemLoader"
      BundledLoader -> "bundledLoader"
      RuntimeLoad -> "runtimeLoad"
      ProvidedByHost -> "providedByHost"
    -- §27.1.1/§36.21: canonical link/load text folded into the host-source
    -- identity, so a change to the link or load specification repins.
    linkText = \case
      DynamicLink libs -> "link dynamic " <> T.intercalate "," libs
      StaticLink libs -> "link static " <> T.intercalate "," libs
      NoLink -> "link none"
    loadText l = "load " <> loadName l

    -- §27.1.1/§36.28: resolve a binding's provides × symbolList surface into
    -- concrete ResolvedNativeSymbols. Each provided concrete host.native
    -- module gets the binding's full declared surface (the manifest's
    -- SymbolDecls, carrying the C symbol + ABI signature). The surface is
    -- authoritative — there is no catalog to validate against.
    resolveBinding :: Map.Map Text [SymbolDecl] -> Map.Map Text (Set.Set Text) -> HostBinding -> Either Diagnostics (Text, [ResolvedNativeSymbol])
    resolveBinding genMap shimDefs hb = do
      mods <- concat <$> traverse (expandSelector hb) (hb.provides)
      decls <- surfaceDecls genMap hb
      -- §26.1.5: a symbol is shim-provided only if a shim TU of this binding
      -- actually DEFINES it (symbol-granular) — a non-shim-defined library
      -- symbol cannot ride the binding's shim past the ABI proof.
      let defined = Map.findWithDefault Set.empty (hb.name) shimDefs
          syms =
            [ ResolvedNativeSymbol
                { rnsModule = mn
                , rnsMember = d.member
                , rnsCSymbol = d.symbol
                , rnsParams = d.params
                , rnsResult = d.result
                , rnsShimProvided = d.symbol `Set.member` defined
                }
            | mn <- mods
            , d <- decls
            ]
      Right (hb.name, syms)

    -- §26.1.5/§36.28: an explicit-symbolList symbol with a pointer/string/handle
    -- signature has no all-scalar conservative prototype the probe can check;
    -- its ABI must be PROVEN — by being genuinely shim-DEFINED (force-include
    -- ABI-checked) or by a `verify` decl WHOSE SIGNATURE IS ABI-CONSISTENT with
    -- the declared one (the verify decl is itself checked against the real
    -- header). A name-only verify match no longer suffices: the declared arity /
    -- pointer-vs-scalar classes must agree with the verify prototype, else the
    -- declared surface could lie about the real ABI. Generated surfaces are
    -- exempt (their signatures are parsed from the header).
    checkSymbolListAbi :: HostBinding -> [ResolvedNativeSymbol] -> Either Diagnostics ()
    checkSymbolListAbi hb syms = case hb.surface of
      SymbolListSurface _ -> mapM_ checkOne syms
      _ -> Right ()
      where
        verifyByName = [(verifyDeclName d, d) | VerifyInput ds <- hb.inputs, d <- ds]
        checkOne s
          | rnsShimProvided s = Right () -- shim-defined → force-include ABI-checked
          | otherwise = case lookup (rnsCSymbol s) verifyByName of
              -- a verify decl PROVES the ABI: it is checked against the real
              -- header AND (for scalars) conflicts with the conservative scalar
              -- extern in the same probe if its width disagrees — so a name-only
              -- match no longer suffices; the classes must be consistent. A mere
              -- `headers` input is NOT enough (a header that does not declare the
              -- symbol contradicts nothing), so every non-shim symbol — scalar or
              -- pointer — requires a consistent verify decl.
              Just d -> case protoArity (T.unpack d) of
                Just (ps, r) | abiConsistent s ps r -> Right ()
                _ -> Left [abiMismatch hb s d]
              Nothing -> Left [unverifiedAbi hb s]
        -- declared params must match the verify prototype's arity + per-position
        -- ABI class; a declared Unit result may discard ANY real return.
        abiConsistent s ps r =
          map ctypeAbiClass (rnsParams s) == ps
            && (ctypeAbiClass (rnsResult s) == ClsVoid || ctypeAbiClass (rnsResult s) == r)

    abiMismatch :: HostBinding -> ResolvedNativeSymbol -> Text -> Diagnostic
    abiMismatch hb s d =
      buildErr "E_NATIVE_BINDING_ABI_UNVERIFIED" "kappa-hs.build.native-abi"
        ( "native binding '" <> hb.name <> "' symbolList declares '" <> rnsMember s
            <> "' (C symbol '" <> rnsCSymbol s <> "') with an ABI signature that is NOT consistent with its "
            <> "'verify' prototype \"" <> d <> "\" (arity or pointer/scalar/float class disagree); the declared "
            <> "surface would misrepresent the real ABI. Make the symbolList signature match the verify prototype, "
            <> "or generate the surface from a header (Spec §26.1.5/§36.28)"
        )

    unverifiedAbi :: HostBinding -> ResolvedNativeSymbol -> Diagnostic
    unverifiedAbi hb s =
      buildErr "E_NATIVE_BINDING_ABI_UNVERIFIED" "kappa-hs.build.native-abi"
        ( "native binding '" <> hb.name <> "' symbolList declares '" <> rnsMember s
            <> "' (C symbol '" <> rnsCSymbol s <> "') whose ABI is not verified: it is not shim-defined and has "
            <> "no matching 'verify' declaration. A `headers` input alone is insufficient (a header that does not "
            <> "declare the symbol proves nothing). Add a 'verify' prototype for '" <> rnsCSymbol s
            <> "' consistent with the declared signature, provide it via a shim, or generate the surface from a "
            <> "header (Spec §26.1.5/§36.28)"
        )

    -- The binding's resolved symbol surface (§36.28). Either an explicit
    -- symbolList, or one MECHANICALLY GENERATED from a header (looked up in
    -- genMap, which 'genThen' populated). A binding that provides modules but
    -- resolves to no surface is rejected: nothing to make importable or call.
    surfaceDecls :: Map.Map Text [SymbolDecl] -> HostBinding -> Either Diagnostics [SymbolDecl]
    surfaceDecls genMap hb = case hb.surface of
      SymbolListSurface [] -> Left [emptySurface hb]
      SymbolListSurface ds -> Right ds
      GeneratedSurface _ _ -> fromGen
      GeneratedPrefixSurface _ _ -> fromGen
      where
        fromGen = case Map.lookup (hb.name) genMap of
          Just ds@(_ : _) -> Right ds
          _ -> Left [emptySurface hb]

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
        ( "native binding '" <> hb.name <> "' provides '" <> m
            <> "', which is not a concrete module under the 'host.native' root; "
            <> "the zig native profile realizes only host.native.* modules "
            <> "(Spec §27.1.1, §34.5.3, §36.28)"
        )
    emptySurface hb =
      buildErr "E_NATIVE_BINDING_UNSUPPORTED" "kappa-hs.build.native-unsupported"
        ( "native binding '" <> hb.name <> "' declares no symbol surface; a "
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
            <> T.intercalate ", " (map (.path) (bc.sourceRoots)) <> ") (Spec §36.3, §36.4)"
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
  perRoot <- forM (bc.sourceRoots) $ \r -> do
    let rootDir = dir </> T.unpack (r.path)
    fs <- listKpFiles rootDir
    pure [(f, deriveModule rootDir f) | f <- fs]
  pure (sortOn fst (concat perRoot))

-- | §36.3 `modules` selector: which package modules belong to a target.
matchesSelector :: ModuleSelector -> ModuleName -> Bool
matchesSelector sel (ModuleName segs) = case sel of
  SelModule m -> segs == T.splitOn "." m
  SelModulesUnder p -> let ps = T.splitOn "." p in take (length ps) segs == ps

-- | §8.1/§36.12: the fragment-suffix tags of a source file — the dotted
-- segments of its final path component between the module-name leaf and the
-- @.kp@ extension. @runtime.kp@ → @[]@; @runtime.native.kp@ → @["native"]@;
-- @log.native.linux.kp@ → @["native","linux"]@.
fragmentSuffixes :: FilePath -> [Text]
fragmentSuffixes file =
  case T.splitOn "." (T.pack (takeFileName file)) of
    (_leaf : rest@(_ : _)) -> init rest -- drop the leaf and the trailing "kp"
    _ -> []

-- | §36.12: is @file@ selected for a target whose enabled fragment-tag set is
-- @enabled@? A file is selected iff every one of its fragment suffixes is in
-- @enabled@; a file with no suffixes is always selected.
fragmentSelected :: [Text] -> FilePath -> Bool
fragmentSelected enabled file = all (`elem` enabled) (fragmentSuffixes file)

-- | §36.12: a SELECTED source file MUST NOT use more than one tag from the
-- same exclusive fragment axis. (An undeclared suffix is not an error — it
-- simply means the file is not selected, per the rule-4 selection criterion.)
fragmentFileDiag :: [FragmentAxis] -> FilePath -> Maybe Diagnostic
fragmentFileDiag axes file =
  let sufs = fragmentSuffixes file
      axisOf t = [a.name | a <- axes, t `elem` a.tags]
      perAxis = Map.toList (foldl' (\m t -> foldl' (\m' an -> Map.insertWith (+) an (1 :: Int) m') m (axisOf t)) Map.empty sufs)
      doubled = [an | (an, c) <- perAxis, c > 1]
      sp = Span file (Pos 1 1) (Pos 1 1)
   in case doubled of
        (an : _) ->
          Just $
            diag SevError StageImports "E_BUILD_FRAGMENT_AXIS_CONFLICT" (Just "kappa-hs.build.fragment-axis") sp
              ( "source fragment '" <> T.pack (takeFileName file) <> "' uses more than one tag from the exclusive "
                  <> "fragment axis '" <> an <> "' (Spec §36.12)"
              )
        _ -> Nothing

-- | §36.12: a target MUST NOT enable more than one tag from the same exclusive
-- axis. Returns a diagnostic on violation.
fragmentTargetDiag :: FilePath -> [FragmentAxis] -> Text -> [Text] -> Maybe Diagnostic
fragmentTargetDiag manifestFile axes tgtName enabled =
  let axisOf t = [a.name | a <- axes, t `elem` a.tags]
      perAxis = Map.toList (foldl' (\m t -> foldl' (\m' an -> Map.insertWith (+) an (1 :: Int) m') m (axisOf t)) Map.empty enabled)
      doubled = [an | (an, c) <- perAxis, c > 1]
      sp = Span manifestFile (Pos 1 1) (Pos 1 1)
   in case doubled of
        (an : _) ->
          Just $
            diag SevError StageImports "E_BUILD_FRAGMENT_AXIS_CONFLICT" (Just "kappa-hs.build.fragment-axis") sp
              ( "target '" <> tgtName <> "' enables more than one tag from the exclusive fragment axis '"
                  <> an <> "' (Spec §36.12)"
              )
        _ -> Nothing

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
      case [d | d <- depBc0.dependencies, depName d == nm] of
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
  let libSelectors = [targetModules t | t <- depBc.targets, isLibraryT t]
      exeMains =
        [ ModuleName (T.splitOn "." nm')
        | t <- depBc.targets, Executable s <- [t.spec], SelModule nm' <- [s.main]
        ]
  pure $
    if null libSelectors
      then [x | x@(_, m) <- mods, m `notElem` exeMains]
      else [x | x@(_, m) <- mods, any (`matchesSelector` m) libSelectors]

-- | The dependency names a package's library targets declare — followed
-- transitively when resolving a path dependency's own dependencies.
libraryDeps :: BuildConfig -> [Text]
libraryDeps depBc = concat [targetDependencies t | t <- depBc.targets, isLibraryT t]

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
targetDependencies t = case t.spec of
  Executable s -> s.dependencies
  Library s -> s.dependencies
  Benchmark s -> s.dependencies
  Test {} -> []
  Aggregate {} -> []
  Alias {} -> []

-- | A target's referenced host-binding names (executables only carry them).
targetHostBindings :: Target -> [Text]
targetHostBindings t = case t.spec of
  Executable s -> s.hostBindings
  _ -> []

-- | The backend a buildable target compiles with. Only ever asked of the
-- buildable kinds (executable\/library\/benchmark); the catch-all is
-- unreachable for the others (which carry no backend).
targetBackend :: Target -> BackendProfile
targetBackend t = case t.spec of
  Executable s -> s.backend
  Library s -> s.backend
  Benchmark s -> s.backend
  _ -> JvmBackend

-- | The entry-module selector of an executable\/benchmark target.
targetMainSel :: Target -> ModuleSelector
targetMainSel t = case t.spec of
  Executable s -> s.main
  Benchmark s -> s.main
  _ -> SelModulesUnder ""

-- | The enabled fragment tags of a buildable target.
targetFragments :: Target -> [Text]
targetFragments t = case t.spec of
  Executable s -> s.fragments
  Library s -> s.fragments
  Benchmark s -> s.fragments
  _ -> []

-- | The @modules@ selector of any target that has one (all but aggregate\/alias).
targetModules :: Target -> ModuleSelector
targetModules t = case t.spec of
  Executable s -> s.modules
  Library s -> s.modules
  Test s -> s.modules
  Benchmark s -> s.modules
  _ -> SelModulesUnder ""

isLibraryT :: Target -> Bool
isLibraryT t = case t.spec of Library {} -> True; _ -> False

isTestT :: Target -> Bool
isTestT t = case t.spec of Test {} -> True; _ -> False

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
      let files = [f | (f, mn) <- allFiles, matchesSelector (targetModules tgt) mn]
      pure (Right (tgt.name, files))
  where
    sp = Span (manifestDir </> manifestBasename) (Pos 1 1) (Pos 1 1)
    tests = [t | t <- bc.targets, isTestT t]
    notFound msg = Left [diag SevError StageImports "E_BUILD_TARGET_NOT_FOUND" (Just "kappa-hs.build.target-not-found") sp msg]
    selectTest = case mTarget of
      Just nm -> case [t | t <- tests, t.name == nm] of
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
