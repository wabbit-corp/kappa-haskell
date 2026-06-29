{-# LANGUAGE OverloadedRecordDot #-}

-- | The conductor: it wires the individual phases together into a whole
-- compilation. If you want to see the order things happen in, this is the
-- file — and 'compileFilesWithCfgInj' is the function that runs the
-- sequence. (Background: docs/CONCEPTS.md.)
--
-- What it covers: prelude bootstrap, multi-file units with same-module
-- fragments (§8.1), §8.2 acyclic dependency ordering with cycle
-- diagnostics, §8.3 import processing (aliases, item selection, wildcards
-- with except-lists), §8.5 export visibility, then parse all files and, per
-- module, resolve fixities and elaborate.
module Kappa.Pipeline
  ( CompiledUnit (..)
  , TraceEvent
  , compileFiles
  , compileFilesIn
  , compileFilesWithConfig
  , moduleNameRelTo
  , compileSourceWithPrelude
  , importScopeFor
  , importScopeForWithConfig
  , loadSourceFile
  , compileManifest
  , manifestModuleName
  , compileProgramWithNative
  , reservedHostRootDiag
  , moduleNameOf
  , preludeState
  ) where

import Control.Monad.State.Strict (evalState)
import qualified Data.ByteString as BS
import Data.Char (isAlphaNum, isAscii, isLetter)
import Data.List (nub, partition, sortOn)
import qualified Data.Map.Lazy as MapLazy
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Encoding.Error as TEE
import Kappa.Backend.C (primRegistryDiagnostics)
import Kappa.Backend.NativeFfi
  ( ResolvedNativeSymbol (..)
  , nativeMemberType
  )
import Kappa.Builtins
import Kappa.Check
import Kappa.Config (ConfigProfile (..), checkConfigUnit)
import Kappa.Core (GName (..), Term (..), gnameText)
import Kappa.CoreLint (lintCoreBodies)
import Kappa.Diagnostic
import Kappa.Eval (EvalCtx (..), Globals (..), eval, quote)
import Kappa.Ownership (annotateOwnership, refineOwnership)
import Kappa.Parser (parseModule)
import Kappa.Prelude
  ( builtinState
  , preludeSource
  , stdAtomicSource
  , stdArrayMutableSource
  , stdBridgeSource
  , stdFfiCSource
  , stdFfiSource
  , stdGradualSource
  , stdDerivingShapeSource
  , stdHashSource
  , stdDebugSource
  , stdBytesSource
  , stdSupervisorSource
  , stdUnicodeSource
  , stdConfigSource
  , stdBuildSource
  )
import Kappa.Resolve (defaultFixities, fixitiesOf, multiFixityOps, resolveModule)
import Kappa.Source
import Kappa.Syntax
import Kappa.Unicode (confusableWithAscii, isBidiControl, isNfcQuick)
import Kappa.Usage
  ( CtorParamInfo
  , FieldShape (..)
  , PInfo
  , ProjUse
  , RecordShape (..)
  , RefOp (..)
  , coreFnParams
  , moduleUsageCtors
  , moduleUsageInoutResultsWith
  , moduleUsageProjections
  , moduleUsageResultTypesWith
  , moduleUsageValueResultTypes
  , moduleUsageRecordAliases
  , moduleUsageRecordDeps
  , moduleUsageRecordShapes
  , moduleUsageSignatures
  , usageDiagnostics
  )

-- | One §T.5.5 portable pipeline-trace step: @(event, subject)@.
-- The prelude bootstrap is implementation machinery and contributes no
-- portable trace steps.
type TraceEvent = (Text, Text)

data CompiledUnit = CompiledUnit
  { cuState :: !CheckState
  , cuDiags :: !Diagnostics
  , cuModule :: !ModuleName
  , cuTrace :: ![TraceEvent]
  }

-- | Compile the prelude into the base state, followed by the embedded
-- standard-library modules (currently @std.hash@).
preludeState :: (CheckState, Diagnostics)
preludeState =
  case parseModule "<std.prelude>" preludeSource of
    Left ds -> (builtinState, ds)
    Right (m, recovered) ->
      let (m', rdiags) = resolveModule defaultFixities m
          (st, diags) = checkModule builtinState m'
          stdSources =
            [ (modDerivingShape, "<std.deriving.shape>", stdDerivingShapeSource)
            , (modHash, "<std.hash>", stdHashSource)
            , (modDebug, "<std.debug>", stdDebugSource)
            , (modBytes, "<std.bytes>", stdBytesSource)
            , (modUnicode, "<std.unicode>", stdUnicodeSource)
            , (modFfi, "<std.ffi>", stdFfiSource)
            , (modFfiC, "<std.ffi.c>", stdFfiCSource)
            , (modAtomic, "<std.atomic>", stdAtomicSource)
            , (modArrayMutable, "<std.array.mutable>", stdArrayMutableSource)
            , (modGradual, "<std.gradual>", stdGradualSource)
            , (modBridge, "<std.bridge>", stdBridgeSource) -- after std.gradual
            , (modSupervisor, "<std.supervisor>", stdSupervisorSource)
            , -- §35.3/§29.8: config-mode schema modules. They are checked
              -- here so their config-safe vocabulary is registered in
              -- csGlobals/csCtors/csModuleExports; a build-manifest loader
              -- (Kappa.Config) installs their names into the manifest's
              -- schema scope without an ordinary import.
              (modConfig, "<std.config>", stdConfigSource)
            , (modBuild, "<std.build>", stdBuildSource)
            ]
          (stStd, sdiags) =
            foldl
              (\(stAcc, dsAcc) (mn, path, src) ->
                 let (stNext, ds) = stdModule mn path src stAcc
                  in (stNext, dsAcc ++ ds))
              (st, [])
              stdSources
          -- §4.5/§4.7 fail-safe: the embedded prelude/std-lib elaborated with
          -- the unsafe-intrinsic exemption ON (so they could admit the proof
          -- helpers and wrap the debug prims). Clear it in the base state handed
          -- to every downstream consumer (the user pipeline, config-mode, the
          -- assertType probe), so the SAFE default is "gated": a consumer that
          -- forgets to reset the flag inherits 'False', not the exemption. Only
          -- a user module with @AllowUnsafeIntrinsics re-enables it.
          st' = stStd {csAllowUnsafeIntrinsics = False, csEmbeddedLoad = False}
       in (st', recovered ++ rdiags ++ diags ++ sdiags ++ builtinContractDiags st')

-- | §28: the prelude must define every name the compiler wires in (see
-- "Kappa.Builtins"). Any name the compiler spells but the prelude does not
-- define is an internal inconsistency between the compiler and its bundled
-- prelude; report it here rather than let it miscompile downstream. The same
-- pass also checks the runtime-pinned constructor-tag table is internally
-- sound (ids contiguous and below 'kctUserBase') and that the primitive
-- registry only names prims the runtime implements.
builtinContractDiags :: CheckState -> Diagnostics
builtinContractDiags st =
  missingNameDiags ++ ctorTagDiags ++ primRegistryDiags
  where
    missingNameDiags = case unresolvedBuiltins st of
      [] -> []
      miss ->
        [ diag
            SevError
            StageElaborate
            "E_INTERNAL_BUILTIN_MISSING"
            (Just "kappa-hs.internal.builtin-missing")
            noSpan
            ( "the bundled prelude is missing names the compiler depends on (§28): "
                <> T.intercalate ", " (map (gnameText . wiName) miss)
            )
        ]
    ctorTagDiags = case runtimeCtorsDiagnostics of
      [] -> []
      problems ->
        [ diag
            SevError
            StageElaborate
            "E_INTERNAL_CTOR_TAG"
            (Just "kappa-hs.internal.ctor-tag")
            noSpan
            ( "the runtime-pinned constructor tag table is inconsistent (§28): "
                <> T.intercalate "; " problems
            )
        ]
    primRegistryDiags = case primRegistryDiagnostics of
      [] -> []
      problems ->
        [ diag
            SevError
            StageElaborate
            "E_INTERNAL_PRIM_REGISTRY"
            (Just "kappa-hs.internal.prim-registry")
            noSpan
            ( "the primitive registry is inconsistent with the runtime-implemented set (§28): "
                <> T.intercalate "; " problems
            )
        ]

-- | Compile one embedded standard-library module on top of the
-- prelude state and register its exports.
stdModule :: ModuleName -> FilePath -> Text -> CheckState -> (CheckState, Diagnostics)
stdModule mn path src st0 =
  case parseModule path src of
    Left ds -> (st0, ds)
    Right (m, recovered) ->
      let (m', rdiags) = resolveModule defaultFixities m
          ie = buildImportsInWithScope [] (preludeAllMemberScope st0) st0 m'
          stIn =
            st0
              { csModule = mn
              , csScope = ieScope ie
              , csScopeAmbig = ieAmbig ie
              , csModuleAliases = ieAliases ie
              , csDiags = []
              , -- entering a new module resets the §3.2.2 in-scope name
                -- cache, which is keyed on the import scope and module
                csScopeNameCache = Nothing
              }
          (st1, diags) = checkModule stIn m'
          st2 = st1 {csModuleExports = Map.insert mn (moduleExportNames m') (csModuleExports st1)}
       in (st2, recovered ++ rdiags ++ ieDiags ie ++ diags)


-- | Scope with prelude globals plus the fixed unqualified constructor
-- subset visible unqualified (§28.1). This is only for the implicit
-- prelude insertion; an explicit @import std.prelude.*@ uses ordinary
-- wildcard-import rules and does not import constructors through this
-- exception.
preludeScope :: CheckState -> Map.Map Text GName
preludeScope st =
  Map.fromList
    [ (gnameText g, g)
    | g@(GName m _) <- Map.keys (csGlobals st)
    , m == preludeModule
    , not ("__inst_" `T.isPrefixOf` gnameText g)
    , not (constructorOnlyGlobal st g)
    ]
    <> Map.fromList
      [ (gnameText g, g)
      | g@(GName m n) <- Map.keys (csCtors st)
      , m == preludeModule
      , n `elem` implicitPreludeCtorNames
      ]

preludeAllMemberScope :: CheckState -> Map.Map Text GName
preludeAllMemberScope st =
  Map.fromList
    [ (gnameText g, g)
    | g@(GName m _) <- Map.keys (csGlobals st) ++ Map.keys (csCtors st)
    , m == preludeModule
    , not ("__inst_" `T.isPrefixOf` gnameText g)
    ]

preludeWildcardMemberNames :: CheckState -> [Text]
preludeWildcardMemberNames st =
  [ gnameText g
  | g@(GName m _) <- Map.keys (csGlobals st)
  , m == preludeModule
  , not ("__inst_" `T.isPrefixOf` gnameText g)
  , not (constructorOnlyGlobal st g)
  ]

constructorOnlyGlobal :: CheckState -> GName -> Bool
constructorOnlyGlobal st g =
  Map.member g (csCtors st) && not (Map.member g (csDatas st))

-- | Per-file trace: parse always happens; KFrontIR construction happens
-- only when the file parses; the KCore lowering happens once per module.
fileTrace :: Bool -> [TraceEvent]
fileTrace parsedOk =
  ("parse", "file") : [("buildKFrontIR", "file") | parsedOk]

-- | Compile one source file (plus prelude) — used by check/run/test.
compileSourceWithPrelude :: FilePath -> Text -> CompiledUnit
compileSourceWithPrelude path src = compileFiles [(path, src)]

-- | The synthetic module name under which a build manifest's bindings
-- live. A config unit has no module header (§35.1), so its globals are
-- keyed under this fixed name; reification looks up @buildConfig@ here.
manifestModuleName :: ModuleName
manifestModuleName = ModuleName ["__manifest"]

-- | Load and config-check a build manifest (§35.13): parse it as
-- ordinary Kappa, then check it in the @config-expression@ profile under
-- the @std.config@/@std.build@ schema scope with the Chapter-35
-- restrictions (see "Kappa.Config"). Returns the checked state (whose
-- 'csCoreBodies' holds the elaborated @buildConfig@ for reification), the
-- manifest module name, and all diagnostics. This performs NO build-plan
-- resolution (§35.13): no source-root enumeration, dependency
-- resolution, or host inspection.
-- The parsed 'Module' is returned (when it parsed) so the caller can
-- compute value provenance (§35.7) over the surface AST.
compileManifest :: FilePath -> Text -> (CheckState, ModuleName, Maybe Module, Diagnostics)
compileManifest path src =
  let (pst, pdiags) = preludeState
   in case parseModule path src of
        Left ds -> (pst, manifestModuleName, Nothing, pdiags ++ ds)
        Right (m, recovered) ->
          let (st, diags) = checkConfigUnit ConfigExpression pst manifestModuleName m
           in (st, manifestModuleName, Just m, pdiags ++ recovered ++ diags)

-- | Multi-file compilation with basename-derived module names
-- (standalone files: §8.1 path-name derivation is not in force).
compileFiles :: [(FilePath, Text)] -> CompiledUnit
compileFiles = compileFilesWith False moduleNameOf

-- | Like 'compileFiles', but header-less module names derive from the
-- path relative to @root@ (the §T.2 suite root is the §8.1 source root
-- for module-path derivation): @root/demo/value.kp@ → @demo.value@.
compileFilesIn :: FilePath -> [(FilePath, Text)] -> CompiledUnit
compileFilesIn root = compileFilesWith True (moduleNameRelTo root)

-- | Like 'compileFilesIn', but with an explicit §4.2 build configuration
-- (which unsafe/debug facilities the build permits). 'compileFiles' and
-- 'compileFilesIn' use 'defaultUnsafeConfig' (everything disabled).
compileFilesWithConfig :: UnsafeConfig -> Bool -> FilePath -> [(FilePath, Text)] -> CompiledUnit
compileFilesWithConfig cfg packageMode root =
  compileFilesWithCfg Map.empty cfg packageMode (if packageMode then moduleNameRelTo root else moduleNameOf)

-- One parsed source fragment.
data Fragment = Fragment
  { frPath :: !FilePath
  , frModule :: !Module
  , frDiags :: !Diagnostics -- ^ parse-recovered diagnostics
  }

compileFilesWith :: Bool -> (FilePath -> ModuleName) -> [(FilePath, Text)] -> CompiledUnit
compileFilesWith = compileFilesWithCfg Map.empty defaultUnsafeConfig

-- | Compile a program with a set of manifest-selected @host.native.*@
-- host-binding modules made importable (§8.3.5/§34.5.3). Returns the
-- compiled unit and the gname→runtime-primitive map for codegen
-- ("Kappa.Backend.Driver" / 'Kappa.Backend.C.generateC'). The provided
-- modules come from the build manifest's native bindings (never a global
-- hardcoded list); an unknown module name is silently skipped here (the
-- build planner validates providers and reports diagnostics first).
compileProgramWithNative ::
  [ResolvedNativeSymbol] ->
  UnsafeConfig ->
  Bool ->
  (FilePath -> ModuleName) ->
  [(FilePath, Text)] ->
  (CompiledUnit, Map.Map GName ResolvedNativeSymbol)
compileProgramWithNative syms cfg packageMode nameOf files =
  ( compileFilesWithCfgInj (applyNativeModules syms) Map.empty cfg packageMode nameOf files
  , nativeHostSymbols syms
  )

-- | Register each resolved native symbol as an abstract global (no value —
-- runtime-only, §34.5.1) under its @host.native.*@ module, plus the module
-- export list, so a program can @import@ it and reference its members. The
-- member's Kappa type is DERIVED from its ABI signature (§26.1.4 via
-- 'nativeMemberType') and evaluated to the global's type — there is no
-- hardcoded catalog of types.
applyNativeModules :: [ResolvedNativeSymbol] -> CheckState -> CheckState
applyNativeModules syms st0 =
  let st1 = foldl' addMod st0 byModule
   in if null byModule
        then st1
        else
          -- Native host bindings extend global lookup before user checking.
          -- Drop proof/normalization caches inherited from the prelude state
          -- so their keys cannot straddle two global environments.
          invalidateSemanticCaches st1
  where
    byModule =
      Map.toList $
        foldl' (\m s -> Map.insertWith (++) (s.moduleName) [s] m) Map.empty syms
    addMod st (mn, ss) =
      let ec = EvalCtx (Globals (csGlobals st)) (csMetas st) False (csFacts st)
          gdOf s = GlobalDef (eval ec [] (nativeMemberType (s.params) (s.result))) Nothing False
          gs =
            foldl'
              (\g s -> Map.insert (GName mn (s.member)) (gdOf s) g)
              (csGlobals st)
              ss
       in st
            { csGlobals = gs
            , csModuleExports = Map.insert mn (map (.member) ss) (csModuleExports st)
            }

-- | The gname→resolved-symbol map for the provided host bindings, threaded
-- into codegen so each member reference lowers to a DIRECT typed call.
nativeHostSymbols :: [ResolvedNativeSymbol] -> Map.Map GName ResolvedNativeSymbol
nativeHostSymbols syms =
  Map.fromList [(GName (s.moduleName) (s.member), s) | s <- syms]

-- | Emit 'E_HOST_MODULE_SOURCE_DEFINED' if @mn@ is exactly a reserved host
-- root or lies under one (§8.3.5).
reservedHostRootDiag :: ModuleName -> Span -> Maybe Diagnostic
reservedHostRootDiag (ModuleName segs) sp
  | any (`isRootOf` segs) reservedHostRoots =
      Just $
        diag SevError StageImports "E_HOST_MODULE_SOURCE_DEFINED" (Just "kappa-hs.host.reserved") sp
          ( "module '" <> renderModuleName (ModuleName segs)
              <> "' is at or under a reserved host binding root (host.jvm/host.dotnet/"
              <> "host.native/host.python); such modules are supplied from host metadata "
              <> "or ABI descriptions, not user source (Spec §8.3.5)"
          )
  | otherwise = Nothing
  where
    isRootOf root xs = xs == root || (take (length root) xs == root && length xs > length root)

compileFilesWithCfg :: Map.Map Text Term -> UnsafeConfig -> Bool -> (FilePath -> ModuleName) -> [(FilePath, Text)] -> CompiledUnit
compileFilesWithCfg = compileFilesWithCfgInj id

-- | The general worker — the end-to-end compile of a set of source files.
-- Read top to bottom, the @let@ body is the pipeline:
--
--   1. bootstrap the prelude into the base state ('preludeState'), then
--      apply @inject@ and the build config;
--   2. parse every file ('parseModule' → @parsed@);
--   3. group fragments of the same module and derive\/validate module names
--      (§8.1: @frags0@, @effName@, @headerMismatchDiags@);
--   4. build the import dependency graph and put the modules in acyclic
--      order (§8.2: @order@), reporting cycles;
--   5. fold @step@ over that order — for each module: resolve fixities,
--      build its import scope (§8.3), elaborate\/type-check it, then run §12
--      usage analysis over it, accumulating diagnostics and state;
--   6. after the fold, re-zonk every captured core body against the final
--      metavariable state and assemble the 'CompiledUnit'.
--
-- @inject@ transforms the post-prelude base state before the user modules
-- are checked — used to register manifest-selected @host.native.*@
-- host-binding modules (§8.3.5/§34.5.3) so a program can @import@ them.
-- Plain compilation passes 'id'.
--
-- (The body is a single large @let@; extracting the phases into named
-- functions is tracked in docs/READABILITY_BACKLOG.md.)
compileFilesWithCfgInj :: (CheckState -> CheckState) -> Map.Map Text Term -> UnsafeConfig -> Bool -> (FilePath -> ModuleName) -> [(FilePath, Text)] -> CompiledUnit
compileFilesWithCfgInj inject intrinsics unsafeCfg packageMode nameOf files =
  let (pst0, pdiags) = preludeState
      -- §4.2: seed the build configuration into the state the user
      -- modules are checked against; the prelude itself is always checked
      -- with the default (disabled) configuration. @inject@ registers any
      -- manifest-provided host.native.* binding modules (§34.5.3).
      pst = inject (pst0 {csUnsafe = unsafeCfg, csBackendIntrinsics = intrinsics})
      parsed = [(path, parseModule path src) | (path, src) <- files]
      parseFails = [ds | (_, Left ds) <- parsed]
      frags0 =
        [ (effName path m, Fragment path m rec)
        | (path, Right (m, rec)) <- parsed
        ]
      effName path m = case modHeader m of
        Just mp -> ModuleName (modPathName mp)
        Nothing -> nameOf path
      -- §8.1: package-mode path-derived module names are ASCII
      -- identifiers; an underivable path cannot name a module
      badName (ModuleName segs) = packageMode && any (not . validSegment) segs
      validSegment s = case T.uncons s of
        Just (c, rest) ->
          (isAscii c && (isLetter c || c == '_'))
            && T.all (\ch -> isAscii ch && (isAlphaNum ch || ch == '_')) rest
        Nothing -> False
      -- §2.1/§8.1: in package mode an explicit module header must agree
      -- with the source-root-relative path-derived module name
      headerMismatchDiags =
        [ diag SevError StageImports "E_MODULE_PATH_MISMATCH" (Just "kappa-hs.module.path-mismatch")
            (Span path (Pos 1 1) (Pos 1 1))
            ( "module header '" <> renderModuleName (ModuleName (modPathName mp))
                <> "' does not match the path-derived module name '"
                <> renderModuleName (nameOf path) <> "' (Spec §2.1, §8.1)"
            )
        | packageMode
        , (path, Right (m, _)) <- parsed
        , Just mp <- [modHeader m]
        , ModuleName (modPathName mp) /= nameOf path
        , -- a file that failed UTF-8 decoding (replacement characters
          -- present) already has its §3.1.3 error; its header is moot
          maybe True (not . T.any (== '\xFFFD')) (lookup path files)
        ]
      pathDiags =
        [ diag SevError StageImports "E_MODULE_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
            (Span (frPath fr) (Pos 1 1) (Pos 1 1))
            ( "the path '" <> T.pack (frPath fr)
                <> "' does not derive a valid module name (segments of '"
                <> renderModuleName mn <> "' must be ASCII identifiers, Spec §8.1)"
            )
        | (mn, fr) <- frags0
        , badName mn
        ]
      badCount = length pathDiags
      -- §8.3.5: a source-defined module whose effective name is exactly a
      -- reserved host root, or begins with one followed by '.', is a
      -- compile-time error. Host binding modules are supplied from host
      -- metadata/ABI descriptions (the native catalog), never user source.
      reservedRootDiags =
        [ d
        | (mn, fr) <- frags0
        , Just d <- [reservedHostRootDiag mn (Span (frPath fr) (Pos 1 1) (Pos 1 1))]
        ]
      goodFrags = [(mn, fr) | (mn, fr) <- frags0, not (badName mn)]
      normPath = T.pack . map (\c -> if c == '\\' then '/' else c)
      firstFragmentPath mn = case [normPath (frPath fr) | (mn', fr) <- goodFrags, mn' == mn] of
        [] -> ""
        paths -> minimum paths
      moduleKey mn = (renderModuleName mn, firstFragmentPath mn)
      -- merge same-module fragments (§8.1) in deterministic canonical
      -- module order; the first fragment path is the Appendix T
      -- tie-breaker for directory-suite requests.
      moduleOrder = sortOn moduleKey (nub [mn | (mn, _) <- goodFrags])
      merged =
        [ (mn, mergedOf frs, frs)
        | mn <- moduleOrder
        , let frs = [fr | (mn', fr) <- goodFrags, mn' == mn]
        , not (null frs)
        ]
      mergedOf [] = Module [] Nothing []
      mergedOf frs@(fr0 : _) =
        Module
          (nub (concatMap (modAttrs . frModule) frs))
          (modHeader (frModule fr0))
          (concatMap (modDecls . frModule) frs)
      unitModules = [mn | (mn, _, _) <- merged]
      noPreludeConflictDiags =
        [ diag SevError StageImports "E_MODULE_ATTRIBUTE_CONFLICT" (Just "kappa-hs.module.attribute-conflict")
            (Span (frPath fr) (Pos 1 1) (Pos 1 1))
            ( "fragments of module '" <> renderModuleName mn
                <> "' disagree on @NoPrelude; explicit module headers in a multi-fragment module must agree (Spec §28.1)"
            )
        | (mn, _, frs) <- merged
        , let explicit =
                [ (fr, moduleHasAttr "NoPrelude" (frModule fr))
                | fr <- frs
                , isJust (modHeader (frModule fr))
                ]
        , any snd explicit
        , any (not . snd) explicit
        , (fr, _) <- take 1 explicit
        ]
      noPreludeConflictModules =
        [ mn
        | (mn, _, frs) <- merged
        , let explicit =
                [ moduleHasAttr "NoPrelude" (frModule fr)
                | fr <- frs
                , isJust (modHeader (frModule fr))
                ]
        , any id explicit
        , any not explicit
        ]
      -- §8.2: dependency order over import/export references, with
      -- cycle detection
      depMap =
        Map.fromList
          [ ( mn
            , sortOn
                (moduleKey . fst)
                [ (dep, sp)
                | (ref, sp) <- moduleRefsOf m
                , dep <- refModuleCandidates unitModules ref
                , dep /= mn
                ]
            )
          | (mn, m, _) <- merged
          ]
      (order, cycleDiags) = topoOrder (sortOn moduleKey unitModules) depMap
      byName = Map.fromList [(mn, (m, frs)) | (mn, m, frs) <- merged]
      -- Process one module @mn@ in dependency order, threading the running
      -- ('CheckState', diagnostic chunks, trace). It resolves the module's
      -- fixities, builds its import scope, elaborates/type-checks it against
      -- the state built up from its already-processed dependencies, and runs
      -- §12 usage analysis over it.
      step (st, chunks, trc) mn =
        case Map.lookup mn byName of
        Nothing -> (st, chunks, trc)
        Just (m, frs) ->
          let -- §5.5: exported fixity declarations are imported together
              -- with the corresponding operator name
              importedFix = importedFixities m
              effFixities = Map.unionWith (++) importedFix defaultFixities
              fullFixities = Map.unionWith (++) (fixitiesOf (modDecls m)) effFixities
              (m', rdiags) = resolveModule effFixities m
              attrDisablesPrelude =
                moduleHasAttr "NoPrelude" m'
                  && mn `notElem` noPreludeConflictModules
              preludeEnabled = implicitPrelude unsafeCfg && not attrDisablesPrelude
              ie = buildImportsInWith unitModules preludeEnabled st m'
              st0 =
                st
                  { csModule = mn
                  , csScope = ieScope ie
                  , csScopeAmbig = ieAmbig ie
                  , csModuleAliases = ieAliases ie
                  , csPreludeDisabled = not preludeEnabled
                  , -- §4.5 soundness escape: this module may name the
                    -- raw-admit proof intrinsics only if it carries the
                    -- @AllowUnsafeIntrinsics attribute (the prelude is always
                    -- permitted, independently of this flag).
                    csAllowUnsafeIntrinsics = moduleHasAttr "AllowUnsafeIntrinsics" m'
                  , -- §4.7: this is a user module, not the genuine embedded
                    -- load, so its accepted intrinsic uses ARE recorded in the
                    -- audit ledger (the embedded base set this 'True').
                    csEmbeddedLoad = False
                  , csDiags = []
                  , -- §5.5.1: bare `(op)` is ambiguous when more than one
                    -- callable fixity for `op` is in scope (e.g. `-`)
                    csMultiFixOps = multiFixityOps fullFixities
                  , -- §4.7: carry accepted unhide/clarify uses into the
                    -- module's audit ledger (the body pass appends more)
                    csAuditLedger = csAuditLedger st ++ ieAudit ie
                  , -- entering a new module resets the §3.2.2 in-scope name
                    -- cache, which is keyed on the import scope and module
                    csScopeNameCache = Nothing
                  }
              (st1, cdiagsRaw) = checkModule st0 m'
              cdiagCount = length cdiagsRaw
              cdiags0 = cdiagCount `seq` cdiagsRaw
              recovered = concatMap frDiags frs
              -- recovery hygiene (§3.1.14): when part of the module
              -- failed to parse, a signature's "missing" definition may
              -- simply be in the unparsed region — do not pile a
              -- §9.1 satisfaction error on top of the parse error
              parseErrored = any isError recovered
              -- §3.1.14A: a salvaged declaration region that already
              -- carries a syntax error gets no piled-on semantic
              -- errors — drop elaboration errors whose primary origin
              -- lies on a line a parse error covered
              parseErrLines =
                [ (spanFile (dPrimary d), ln)
                | d <- recovered
                , isError d
                , ln <- [posLine (spanStart (dPrimary d)) .. posLine (spanEnd (dPrimary d))]
                ]
              onParseErrLine d =
                ( spanFile (dPrimary d)
                , posLine (spanStart (dPrimary d))
                )
                  `elem` parseErrLines
              isSuppressedHere d =
                dCode d == "E_SIGNATURE_UNSATISFIED" || onParseErrLine d
              -- §3.1.10/§3.1.11: the surviving (kept) elaboration diags,
              -- and the cascade ones suppressed by the parse error
              (cdiags, suppressedByParse) =
                if parseErrored
                  then (filter (not . isSuppressedHere) cdiags0, filter isSuppressedHere cdiags0)
                  else (cdiags0, [])
              -- §3.1.11: attach each suppressed cascade summary to the
              -- parse-error diagnostic that explains it (the nearest one
              -- on the same line, else the first parse error), so tooling
              -- can still surface the dropped diagnostics on request.
              recovered' =
                if null suppressedByParse
                  then recovered
                  else attachSuppressed recovered suppressedByParse
              preDiags = recovered' ++ rdiags ++ ieDiags ie ++ cdiags
              -- §12.2–§12.4 usage analysis runs only over cleanly
              -- elaborated modules (its judgements presume well-typed
              -- bodies)
              udiags =
                if hasErrors preDiags
                  then []
                  else
                    let resolvedCtorAliases = usageLocalCtorAliases byName st1 m'
                     in
                    usageDiagnostics
                      (csExpansions st1)
                      (csMutableBindingFields st1)
                      (usageImportedParams byName st1 ie)
                      (usageImportedInoutResults byName st1 ie)
                      (usageImportedResultTypes byName st1 ie)
                      (usageImportedValueResultTypes byName st1 ie)
                      (usageImportedRecordAliases byName st1 ie)
                      (usageImportedRecordShapes byName st1 ie)
                      (usageImportedRecordDeps byName st1 ie)
                      (resolvedCtorAliases `Map.union` usageImportedCtors byName st1 ie)
                      (usageImportedRefOps st1 ie)
                      (usageRecognizedRefOps st1)
                      (usageImportedBorrowViewHeads st1 ie)
                      (usageVisibleMonadicResultHeads st1 ie m')
                      (usageImportedProjections byName st1 ie)
                      (usageImportedDuplicableStorageHeads st1 ie)
                      m'
              ftrace =
                concatMap (const (fileTrace True)) frs ++ [("lowerKCore", "module")]
              -- §8.4 re-exports: record where each aliased/selected
              -- export item originates, so importers resolve to the
              -- original declaration (identity preserved downstream)
              reExps =
                Map.fromList
                  [ (alias, GName (ModuleName (modPathName mp)) (nameText (iiName it)))
                  | DExport ss _ <- modDecls m'
                  , ImportItems (RefPath mp) items <- ss
                  , it <- items
                  , let alias = maybe (nameText (iiName it)) nameText (iiAlias it)
                  ]
           in cdiagCount `seq`
                ( st1
                        { csModuleExports = Map.insert mn (moduleExportNames m') (csModuleExports st1)
                        , csReExports =
                            if Map.null reExps
                              then csReExports st1
                              else Map.insert mn reExps (csReExports st1)
                        }
                    , (preDiags ++ udiags) : chunks
                    , ftrace : trc
                    )
      -- §5.5: the fixities a module's imports bring along — an
      -- operator's exported fixity is imported together with the
      -- operator name (computed from the unit's parsed sources, which
      -- are ordered by §8.2 dependency order)
      exportedFixOf mn = case Map.lookup mn byName of
        Just (em, _) ->
          let names = moduleExportNames em
           in Map.filterWithKey (\op _ -> op `elem` names) (fixitiesOf (modDecls em))
        Nothing -> Map.empty
      importedFixities m =
        Map.unionsWith
          (++)
          [pickFix spec | DImport ss _ <- modDecls m, spec <- ss]
      pickFix = \case
        ImportItems (RefPath mp) items ->
          let env = exportedFixOf (ModuleName (modPathName mp))
              wanted = [nameText (iiName it) | it <- items, Nothing <- [iiAlias it]]
           in Map.filterWithKey (\op _ -> op `elem` wanted) env
        ImportAll (RefPath mp) excepts ->
          let exc = [nameText n | ExceptItem _ n <- excepts]
           in Map.filterWithKey (\op _ -> op `notElem` exc) (exportedFixOf (ModuleName (modPathName mp)))
        ImportSingleton (RefPath mp) n ->
          Map.filterWithKey (\op _ -> op == nameText n) (exportedFixOf (ModuleName (modPathName mp)))
        _ -> Map.empty
      (finalSt, diagChunks, traceChunks) = foldl' step (pst, [pdiags], []) order
      -- §9.4: expect satisfaction is judged over the whole unit
      allDiags =
        concat parseFails
          ++ pathDiags
          ++ reservedRootDiags
          ++ headerMismatchDiags
          ++ noPreludeConflictDiags
          ++ cycleDiags
          ++ concat (reverse diagChunks)
          ++ expectUnsatisfiedDiags finalSt
      allTrace =
        concatMap (const (fileTrace False)) parseFails
          ++ concatMap (const (fileTrace True)) [() | _ <- [1 .. badCount]]
          ++ concat (reverse traceChunks)
      lastName = case reverse files of
        ((p, _) : _) ->
          case [mn | (mn, fr) <- goodFrags, frPath fr == p] of
            (mn : _) -> mn
            [] -> nameOf p
        [] -> ModuleName ["main"]
      -- §34.5/§16.3: a captured core body (csCoreBodies) was zonked when
      -- its definition was checked, but some evidence/type metavariables
      -- are only solved later in the unit (e.g. an instance dictionary for
      -- a polymorphic call resolved by a postponed goal). Re-zonk every
      -- captured body against the FINAL meta state so the native backend
      -- never sees an unsolved CMeta where a solved dictionary belongs.
      -- The map is intentionally lazy: native builds may only force the
      -- reachable subset of 'csCoreBodies', and eagerly re-zonking the whole
      -- package penalizes large game targets before backend reachability has a
      -- chance to prune unused definitions.
      finalSt'0 =
        finalSt
          { csCoreBodies =
              MapLazy.map
                (\tm -> evalState (zonkTermM 0 tm) finalSt)
                (csCoreBodies finalSt)
          }
      -- Perceus RC Stage S1.1/S1.4: populate the ownership side-table right
      -- after 'csCoreBodies' is finalized (mirroring the @gsSuspenders@
      -- precedent, which derives from the same core bodies). 'annotateOwnership'
      -- (S1.1) records per-binder ownership facts and per-occurrence last-use;
      -- 'refineOwnership' (S1.4 §3a) then TIGHTENS each binder's @boRefined@ to
      -- its whole-program usage interval wherever it is strictly narrower than
      -- the declared quantity. The compile is whole-program static (no dynamic
      -- linking / separate compilation), so the analysis sees ALL uses and EVERY
      -- provably-single-use binder is refined — exported, re-exported, and
      -- internal alike; the §3a gating boundary (the separately-compiled
      -- interface) is empty right now. It
      -- is observe-only — no consumer reads it, so codegen stays byte-identical;
      -- this only threads the metadata. The 'EvalCtx' is the same shape the lint
      -- and other post-finalization consumers build.
      ownCtx =
        EvalCtx
          (Globals (csGlobals finalSt'0))
          (csMetas finalSt'0)
          False
          (csFacts finalSt'0)
      ctorTypes = Map.map ciType (csCtors finalSt'0)
      finalSt' =
        finalSt'0
          { csOwnership =
              refineOwnership
                ownCtx
                ctorTypes
                (csCoreBodies finalSt'0)
                (annotateOwnership ownCtx ctorTypes (csCoreBodies finalSt'0))
          }
      -- KBackendIR Stage 0: an OBSERVE-ONLY lint over the elaborated,
      -- zonked Core. It only appends 'SevWarning' diagnostics — it never
      -- changes 'finalSt'' or codegen — so byte-identical backend output and
      -- conformance fixtures are unaffected. On a well-typed corpus it emits
      -- nothing; it exists to surface ill-typed application heads (the
      -- @kapp(unit, …)@ crash class) as a diagnostic rather than a crash.
      lintDiags =
        lintCoreBodies (csGlobals finalSt') (csMetas finalSt') (csCoreBodies finalSt')
   in CompiledUnit finalSt' (allDiags ++ lintDiags) lastName allTrace

renderModuleName :: ModuleName -> Text
renderModuleName (ModuleName segs) = T.intercalate "." segs

-- | §3.1.11: attach cascade-suppressed diagnostic summaries to the
-- parse-error diagnostic that explains them. Each suppressed diagnostic
-- is summarized onto the first error in @roots@ on the same source line
-- (preferred), otherwise onto the first error overall. Non-error roots
-- and the no-root case leave the suppressed list empty (nothing to
-- attach to), which is acceptable: the cascade is still dropped.
attachSuppressed :: Diagnostics -> Diagnostics -> Diagnostics
attachSuppressed roots supp
  | not (any isError roots) = roots -- no error root to own the summaries
  | otherwise = goAttach True roots
  where
    summarize s = Suppressed (dCode s) (dFamily s) (dPrimary s) (dMessage s)
    sameLine a b =
      spanFile (dPrimary a) == spanFile (dPrimary b)
        && posLine (spanStart (dPrimary a)) == posLine (spanStart (dPrimary b))
    -- the suppressed diagnostics that match no error root's line: they
    -- are owned by the first error root
    unlined = [s | s <- supp, not (any (\d -> isError d && sameLine d s) roots)]
    -- walk roots once; @firstErr@ flags whether this is the first error
    -- root (it additionally owns the unlined suppressed diagnostics)
    goAttach _ [] = []
    goAttach firstErr (d : rest)
      | not (isError d) = d : goAttach firstErr rest
      | otherwise =
          let lined = [summarize s | s <- supp, sameLine d s]
              mine = lined ++ (if firstErr then map summarize unlined else [])
              d' = if null mine then d else withSuppressed mine d
           in d' : goAttach False rest

-- ── Dependency graph (§8.2) ──────────────────────────────────────────

-- module references of import AND export declarations, with spans
moduleRefsOf :: Module -> [(ModuleRef, Span)]
moduleRefsOf m =
  [ (refOf spec, sp)
  | d <- modDecls m
  , (specs, sp) <- case d of
      DImport ss dsp -> [(ss, dsp)]
      DExport ss dsp -> [(ss, dsp)]
      _ -> []
  , spec <- specs
  ]
  where
    refOf = \case
      ImportModule r _ -> r
      ImportItems r _ -> r
      ImportAll r _ -> r
      ImportSingleton r _ -> r

-- which unit modules an import reference may depend on (§8.3: the
-- singleton form is disambiguated semantically, so both readings count)
refModuleCandidates :: [ModuleName] -> ModuleRef -> [ModuleName]
refModuleCandidates unitMods = \case
  RefUrl {} -> []
  RefPath mp ->
    let segs = modPathName mp
        names =
          ModuleName segs
            : [ModuleName (init segs) | length segs > 1]
     in nub [mn | mn <- names, mn `elem` unitMods]

-- DFS topological order; each back edge produces one E_IMPORT_CYCLE
topoOrder ::
  [ModuleName] ->
  Map.Map ModuleName [(ModuleName, Span)] ->
  ([ModuleName], Diagnostics)
topoOrder mods deps = (reverse outRev, reverse diagsRev)
  where
    (_, outRev, diagsRev) = foldl' (\acc mn -> go acc [] mn) ([], [], []) mods
    go st@(done, out, ds) path mn
      | mn `elem` done = st
      | mn `elem` path =
          let cyc = reverse (takeWhile (/= mn) path)
              sp = case path of
                (parent : _) ->
                  fromMaybe unitSpan (lookup mn (fromMaybe [] (Map.lookup parent deps)))
                [] -> unitSpan
              d =
                diag SevError StageImports "E_IMPORT_CYCLE" (Just "kappa-hs.import.cycle") sp
                  ( "module dependency cycle: "
                      <> T.intercalate " -> " (map renderModuleName (mn : cyc ++ [mn]))
                      <> " (module imports and re-exports must be acyclic, Spec §8.2)"
                  )
           in (done, out, d : ds)
      | otherwise =
          let children = fromMaybe [] (Map.lookup mn deps)
              (done', out', ds') =
                foldl' (\acc (c, _) -> go acc (mn : path) c) st children
           in (mn : done', mn : out', ds')
    unitSpan = Span "<unit>" (Pos 1 1) (Pos 1 1)

-- ── Exports (§8.5) ───────────────────────────────────────────────────

moduleHasAttr :: Text -> Module -> Bool
moduleHasAttr attr m = attr `elem` map nameText (modAttrs m)

moduleExportNames :: Module -> [Text]
moduleExportNames m =
  -- §5902/§8.5.1: a lexical scope maps each name to a binding group that
  -- may carry several declaration kinds (e.g. a signature `DSig` and its
  -- defining `DLet`). Visibility is a property of the named ITEM, not of
  -- an individual declaration: a `private` marker on ANY declaration of
  -- the group makes the item private and removes it from the export
  -- interface. We therefore aggregate per name — exported iff no
  -- declaration is `private` and at least one is exportable by default or
  -- explicitly `public` — rather than OR-ing exportability per
  -- declaration (which leaked a `private let` whose signature was
  -- unmarked, and vice versa).
  nub (groupedNames ++ otherNames)
  where
    pbd = moduleHasAttr "PrivateByDefault" m
    vis mods = case dmVisibility mods of
      VisPublic -> True
      VisPrivate -> False
      VisDefault -> not pbd
    -- visibilities of every signature/definition declaration that shares
    -- a module-scope term name (the §5902 binding group)
    groupVis :: Map.Map Text [Visibility]
    groupVis =
      Map.fromListWith (++) $
        concatMap
          ( \case
              DSig mods n _ _ -> [(nameText n, [dmVisibility mods])]
              DLet mods (LetDef (Just n) _ _ _ _ _ _ _) _ -> [(nameText n, [dmVisibility mods])]
              DTypeAlias mods n _ _ _ _ -> [(nameText n, [dmVisibility mods])]
              DProjection mods n _ _ _ _ -> [(nameText n, [dmVisibility mods])]
              _ -> []
          )
          (modDecls m)
    -- the binding group is exported iff no declaration is private and at
    -- least one is exportable
    groupExported viss =
      VisPrivate `notElem` viss
        && any (\v -> v == VisPublic || (v == VisDefault && not pbd)) viss
    groupedNames = [nm | (nm, viss) <- Map.toList groupVis, groupExported viss]
    -- everything that is NOT a §5902 grouped term name (data/trait/expect/
    -- re-export), still decided per declaration since each binds its name
    -- once
    otherNames = concatMap go (modDecls m)
    go = \case
      DData mods (DataDecl n _ _ ctors) _
        | vis mods -> nameText n : [nameText cn | CtorDecl cn _ _ _ <- ctors]
      -- §8.5: a trait declaration also binds each member name at module
      -- scope (the §14.2.1 overloaded-member projection), and those are
      -- ordinary top-level named items — exported by default with the
      -- trait
      DTrait mods td _
        | vis mods ->
            nameText (trName td)
              : nub
                  ( [nameText mn | TraitSig mn _ _ <- trMembers td]
                      ++ [nameText mn | TraitDefault (LetDef (Just mn) _ _ _ _ _ _ _) _ <- trMembers td]
                  )
      DExpect mods form _ -> [nameText (expectName form) | vis mods]
      -- §8.4 re-exports: `export M.(x [as y], ...)` exports the items
      -- under their (aliased) spellings
      DExport ss _ -> concatMap reExpNames ss
      _ -> []
    reExpNames = \case
      ImportItems (RefPath _) items ->
        [maybe (nameText (iiName it)) nameText (iiAlias it) | it <- items]
      ImportSingleton (RefPath _) n -> [nameText n]
      _ -> []
    expectName = \case
      ExpectTerm n _ -> n
      ExpectType n _ _ -> n
      ExpectData n _ _ -> n
      ExpectTrait n _ _ -> n

-- ── Import processing (§8.3) ─────────────────────────────────────────

data ImportEnv = ImportEnv
  { ieScope :: !(Map.Map Text GName)
  , ieAmbig :: !(Map.Map Text [GName])
  , ieAliases :: !(Map.Map Text ModuleName)
  , ieExplicit :: ![Text] -- ^ names selected by explicit items
  , ieWild :: ![Text] -- ^ names provided by wildcard imports
  , ieDiags :: !Diagnostics
  , ieAudit :: ![AuditRecord] -- ^ §4.7 accepted unhide/clarify uses
  }

-- | Unqualified scope induced by a module's imports over the
-- accumulated state: prelude base, import-selected names overlaid.
-- Names provided by two distinct wildcard origins become ambiguous
-- (§7.1); explicit items win; prelude names are shadowed silently.
-- Also validates items, URL pinning, and target module existence.
buildImports :: CheckState -> Module -> ImportEnv
buildImports = buildImportsIn []

buildImportsIn :: [ModuleName] -> CheckState -> Module -> ImportEnv
buildImportsIn unitMods st m =
  buildImportsInWith unitMods (not (moduleHasAttr "NoPrelude" m)) st m

buildImportsInWith :: [ModuleName] -> Bool -> CheckState -> Module -> ImportEnv
buildImportsInWith unitMods preludeEnabled st m =
  buildImportsInWithScope unitMods (if preludeEnabled then preludeScope st else Map.empty) st m

buildImportsInWithScope :: [ModuleName] -> Map.Map Text GName -> CheckState -> Module -> ImportEnv
buildImportsInWithScope unitMods baseScope st m = foldl' addSpec ie0 specs
  where
    ie0 = ImportEnv baseScope Map.empty Map.empty [] [] [] []
    -- URL pinning applies to re-exports as well (§8.3.2/§8.4)
    specs =
      [(spec, sp) | DImport ss sp <- modDecls m, spec <- ss]
        ++ [(spec, sp) | DExport ss sp <- modDecls m, spec <- ss, isUrl spec]
    isUrl = \case
      ImportModule (RefUrl {}) _ -> True
      ImportItems (RefUrl {}) _ -> True
      ImportAll (RefUrl {}) _ -> True
      ImportSingleton (RefUrl {}) _ -> True
      _ -> False
    exportsOf mn = Map.lookup mn (csModuleExports st)
    -- §8.4: an item exported by `export M.(x as y)` resolves to the
    -- originating declaration in M, preserving identity downstream
    reExpsOf mn = Map.findWithDefault Map.empty mn (csReExports st)
    exportTarget mn nm = Map.findWithDefault (GName mn nm) nm (reExpsOf mn)
    knownModule mn =
      mn == preludeModule
        || Map.member mn (csModuleExports st)
        || mn `elem` unitMods
    memberNames mn
      | mn == preludeModule = Map.keys (preludeAllMemberScope st)
      | otherwise = fromMaybe [] (exportsOf mn)
    hasGlobal g = Map.member g (csGlobals st) || Map.member g (csCtors st)
    ctorsOfType tyG =
      [c | (c, ci) <- Map.toList (csCtors st), ciData ci == tyG]
    err ie sp code fam msg =
      ie {ieDiags = ieDiags ie ++ [diag SevError StageImports code (Just fam) sp msg]}
    cfg = csUnsafe st
    -- §4.2/§4.3: gate the `unhide` / `clarify` import modifiers. Each is a
    -- compile-time error unless its build setting is enabled; an accepted
    -- modifier is recorded in the §4.7 audit ledger.
    gateImportModifiers mn sp it ie =
      let nm = nameText (iiName it)
          step (modPresent, allowed, facility, setting) acc
            | not modPresent = acc
            | allowed =
                acc {ieAudit = ieAudit acc ++ [AuditRecord facility mn sp nm setting Nothing]}
            | otherwise = gateErr acc sp facility setting nm
       in foldr
            step
            ie
            [ (iiUnhide it, allowUnhiding cfg, "unhide", "allow_unhiding")
            , (iiClarify it, allowClarify cfg, "clarify", "allow_clarify")
            ]
    gateErr ie sp facility setting nm =
      ie
        { ieDiags =
            ieDiags ie
              ++ [ withPayload (featureGatedPayload ("unsafe-import-modifier:" <> facility) setting)
                     $ withRelated
                     (related RoleFeatureGateSite sp ("build setting '" <> setting <> "' is disabled"))
                     ( diag SevError StageImports "E_FEATURE_INACTIVE" (Just "kappa.feature.gated") sp
                         ( "use of unsafe/debug import modifier '" <> facility <> "' (on '" <> nm
                             <> "') requires the build setting '" <> setting
                             <> "', which is disabled (Spec §4.2, §4.3)"
                         )
                     )
                 ]
        }
    -- §29.6: importing `std.debug` is a compile-time error unless the
    -- build enables `allow_debug_introspection`. (The module is always
    -- registered so its names exist; only the user import is gated.)
    refPathModule = \case
      ImportModule (RefPath mp) _ -> Just (pathModule mp)
      ImportAll (RefPath mp) _ -> Just (pathModule mp)
      ImportItems (RefPath mp) _ -> Just (pathModule mp)
      ImportSingleton (RefPath mp) _ -> Just (pathModule mp)
      _ -> Nothing
    debugGateErr ie sp =
      ie
        { ieDiags =
            ieDiags ie
              ++ [ withPayload (featureGatedPayload "debug-introspection" "allow_debug_introspection")
                     $ withRelated
                       (related RoleFeatureGateSite sp "build setting 'allow_debug_introspection' is disabled")
                     ( diag SevError StageImports "E_FEATURE_INACTIVE" (Just "kappa.feature.gated") sp
                         "importing 'std.debug' requires the build setting 'allow_debug_introspection', which is disabled (Spec §29.6)"
                     )
                 ]
        }
    addSpec ie (spec, sp)
      | Just mn <- refPathModule spec
      , mn == modDebug
      , not (allowDebugIntrospection cfg) =
          debugGateErr ie sp
    addSpec ie (spec, sp) = case spec of
      ImportModule (RefUrl u _) _ -> urlErr ie sp u
      ImportItems (RefUrl u _) _ -> urlErr ie sp u
      ImportAll (RefUrl u _) _ -> urlErr ie sp u
      ImportSingleton (RefUrl u _) _ -> urlErr ie sp u
      ImportModule (RefPath mp) malias ->
        let mn = pathModule mp
         in if not (knownModule mn)
              then unknownModule ie sp mn
              else case malias of
                Just a -> ie {ieAliases = Map.insert (nameText a) mn (ieAliases ie)}
                Nothing -> ie {ieAliases = Map.insert (moduleNameText mn) mn (ieAliases ie)}
      ImportAll (RefPath mp) excepts ->
        let mn = pathModule mp
            exceptNames = [nameText n | ExceptItem _ n <- excepts]
         in if not (knownModule mn)
              then unknownModule ie sp mn
              else
                foldl'
                  (\acc nm -> addWildName acc nm (exportTarget mn nm))
                  ie
                  [nm | nm <- wildMembers mn, nm `notElem` exceptNames]
      ImportItems (RefPath mp) items ->
        let mn = pathModule mp
            -- §8.3.1: the `(..)` constructor wildcard imports the type
            -- together with all its (own-spelling) constructors, while
            -- `as y` renames a single spelling. Combining them is
            -- ill-formed: there is no coherent target spelling for the
            -- constructors brought in by `(..)`. Reject `T(..) as y`
            -- independently of whether the module is known.
            (malformed, wellFormed) =
              partition (\it -> iiCtorAll it && isJust (iiAlias it)) items
            ieM = foldl' (\acc it -> malformedItem acc sp mn (nameText (iiName it))) ie malformed
         in if not (knownModule mn)
              then unknownModule ieM sp mn
              else foldl' (addItem mn sp) ieM wellFormed
      ImportSingleton (RefPath mp) n ->
        let mn = pathModule mp
            asModule = ModuleName (modPathName mp ++ [nameText n])
         in if knownModule mn && nameText n `elem` memberNames mn
              then addExplicit ie (nameText n) (exportTarget mn (nameText n))
              else
                if knownModule asModule
                  then ie
                  else
                    if knownModule mn
                      then itemNotFound ie sp mn (nameText n)
                      else unknownModule ie sp mn
    pathModule mp = ModuleName (modPathName mp)
    wildMembers mn
      | mn == preludeModule = preludeWildcardMemberNames st
      | otherwise = memberNames mn
    addItem mn sp ie0' it =
      let nm = nameText (iiName it)
          alias = maybe nm nameText (iiAlias it)
          g = exportTarget mn nm
          -- §4.2/§4.3: `unhide` and `clarify` are unsafe/debug import
          -- modifiers, gated by the build configuration. Gate before any
          -- name processing so the modifier is reported even when the
          -- target name is absent.
          ie = gateImportModifiers mn sp it ie0'
       in if nm `elem` memberNames mn
            then case kindMismatch g (iiKind it) of
              Just why ->
                err ie sp "E_IMPORT_ITEM_NOT_FOUND" "kappa.name.unresolved"
                  ("'" <> nm <> "' is exported by module '" <> renderModuleName mn
                     <> "', but not as a " <> why <> " (§8.3 kind selectors)")
              Nothing ->
                let ie1 = addExplicit ie alias g
                 in if iiCtorAll it
                      then foldl' (\acc c -> addExplicit acc (gnameText c) c) ie1 (ctorsOfType g)
                      else ie1
            else
              if hasGlobal g
                then
                  err ie sp "E_IMPORT_ITEM_NOT_FOUND" "kappa.name.unresolved"
                    ("'" <> nm <> "' exists in module '" <> renderModuleName mn <> "' but is not exported (Spec §8.5)")
                else itemNotFound ie sp mn nm
    -- §8.3 kind selectors: the selected member must have the stated
    -- kind (type/trait/ctor/term)
    kindMismatch g = \case
      Nothing -> Nothing
      Just SelTrait
        | isTrait g -> Nothing
        | otherwise -> Just "trait"
      Just SelType
        | isTrait g -> Just "type"
        | isData g || not (isCtor g) -> Nothing
        | otherwise -> Just "type"
      Just SelCtor
        -- §8.3.1: `ctor` selects a data constructor, including the
        -- same-spelling constructor facet of a data family (§7.2)
        | Map.member g (csCtors st) -> Nothing
        | otherwise -> Just "ctor"
      Just SelTerm
        | isData g || isTrait g -> Just "term"
        | otherwise -> Nothing
      Just _ -> Nothing
      where
        isTrait x = Map.member x (csTraits st)
        isData x = Map.member x (csDatas st)
        isCtor x = Map.member x (csCtors st) && not (isData x)
    itemNotFound ie sp mn nm =
      err ie sp "E_IMPORT_ITEM_NOT_FOUND" "kappa.name.unresolved"
        ("module '" <> renderModuleName mn <> "' does not export '" <> nm <> "' (Spec §8.3)")
    malformedItem ie sp mn nm =
      err ie sp "E_IMPORT_ITEM_MALFORMED" "kappa-hs.parse.error"
        ("import item '" <> nm <> "(..) as ...' from module '" <> renderModuleName mn
           <> "' combines the constructor wildcard '(..)' with an alias 'as'; "
           <> "these may not be combined because the alias has no coherent "
           <> "target for the wildcard constructors (Spec §8.3.1)")
    addExplicit ie alias g =
      ie
        { ieScope = Map.insert alias g (ieScope ie)
        , ieAmbig = Map.delete alias (ieAmbig ie)
        , ieExplicit = alias : ieExplicit ie
        }
    addWildName ie alias g
      | alias `elem` ieExplicit ie = ie
      | Just gs <- Map.lookup alias (ieAmbig ie) =
          if g `elem` gs then ie else ie {ieAmbig = Map.insert alias (g : gs) (ieAmbig ie)}
      | alias `elem` ieWild ie
      , Just g0 <- Map.lookup alias (ieScope ie)
      , g0 /= g =
          ie
            { ieAmbig = Map.insert alias [g, g0] (ieAmbig ie)
            , ieScope = Map.delete alias (ieScope ie)
            }
      | otherwise =
          ie
            { ieScope = Map.insert alias g (ieScope ie)
            , ieWild = alias : ieWild ie
            }
    -- §8.3.3 URL pins select the failure mode: no fetching machinery
    -- exists here, so a sha256-pinned import is unsupported outright; a
    -- ref-pinned import additionally needs the package-mode lockfile
    -- this implementation does not keep; an unpinned import violates
    -- package mode before fetching would even be attempted
    urlErr ie sp url = case T.breakOn "#" url of
      (_, pin)
        | "#ref:" `T.isPrefixOf` pin ->
            err ie sp "E_URL_IMPORT_REF_PIN_REQUIRES_LOCK" "kappa.package.reproducibility"
              "a 'ref:'-pinned URL import requires the resolved digest to be recorded in a lockfile in package mode (Spec §8.3.3); this implementation keeps no lockfile"
        | "#" `T.isPrefixOf` pin ->
            err ie sp "E_URL_IMPORT_UNSUPPORTED" "kappa-hs.import.url"
              "URL module fetching is not supported by this implementation (Spec §8.3.2)"
      _ ->
        err ie sp "E_URL_IMPORT_UNPINNED_IN_PACKAGE_MODE" "kappa.package.reproducibility"
          "URL module imports must be pinned in package mode (Spec §8.3.2)"
    unknownModule ie sp mn =
      err ie sp "E_MODULE_NAME_UNRESOLVED" "kappa.name.unresolved"
        ("imported module '" <> renderModuleName mn <> "' is not part of this compilation unit (Spec §8.2)")

-- | Unqualified scope for a module over an accumulated state — the
-- harness uses this for §T.5.2 probe elaboration.
importScopeFor :: CheckState -> Module -> Map.Map Text GName
importScopeFor st m = ieScope (buildImports st m)

importScopeForWithConfig :: UnsafeConfig -> CheckState -> Module -> Map.Map Text GName
importScopeForWithConfig cfg st m =
  ieScope (buildImportsInWith [] (implicitPrelude cfg && not (moduleHasAttr "NoPrelude" m)) st m)

usageImportedParams :: Map.Map ModuleName (Module, [Fragment]) -> CheckState -> ImportEnv -> Map.Map Text [PInfo]
usageImportedParams byName st ie =
  Map.mapMaybe paramsFor importedNames
  where
    ctx = EvalCtx (Globals (csGlobals st)) (csMetas st) False (csFacts st)
    sourceParams =
      Map.fromList
        [ ((mn, nm), ps)
        | (mn, (sm, _)) <- Map.toList byName
        , (nm, ps) <- Map.toList (moduleUsageSignatures sm)
        ]
    importedNames = usageImportedNames st ie
    paramsFor g@(GName mn nm) =
      case Map.lookup (mn, nm) sourceParams of
        Just ps -> Just ps
        Nothing -> coreFnParams . quote ctx 0 . gdType <$> Map.lookup g (csGlobals st)

usageImportedInoutResults ::
  Map.Map ModuleName (Module, [Fragment]) ->
  CheckState ->
  ImportEnv ->
  Map.Map Text [FieldShape]
usageImportedInoutResults byName st ie =
  Map.mapMaybeWithKey resultsFor importedNames
  where
    importedNames = usageImportedNames st ie
    sourceResults =
      Map.fromList
        [ ((mn, nm), shapes)
        | (mn, (sm, _)) <- Map.toList byName
        , (nm, shapes) <- Map.toList (moduleUsageInoutResultsWith (usageModuleMonadicResultHeads st mn) sm)
        ]
    resultsFor local (GName mn nm) =
      qualifyFieldShapeTypes (resultQualifier local mn) (sourceStorageTypeNamesIn byName mn)
        <$> Map.lookup (mn, nm) sourceResults

usageImportedResultTypes ::
  Map.Map ModuleName (Module, [Fragment]) ->
  CheckState ->
  ImportEnv ->
  Map.Map Text Expr
usageImportedResultTypes byName st ie =
  Map.mapMaybeWithKey resultFor importedNames
  where
    importedNames = usageImportedNames st ie
    sourceResults =
      Map.fromList
        [ ((mn, nm), ty)
        | (mn, (sm, _)) <- Map.toList byName
        , (nm, ty) <- Map.toList (moduleUsageResultTypesWith (usageModuleMonadicResultHeads st mn) sm)
        ]
    resultFor local (GName mn nm) =
      qualifyStorageExpr (resultQualifier local mn) (sourceStorageTypeNamesIn byName mn)
        <$> Map.lookup (mn, nm) sourceResults

usageImportedValueResultTypes ::
  Map.Map ModuleName (Module, [Fragment]) ->
  CheckState ->
  ImportEnv ->
  Map.Map Text Expr
usageImportedValueResultTypes byName st ie =
  Map.mapMaybeWithKey resultFor importedNames
  where
    importedNames = usageImportedNames st ie
    sourceResults =
      Map.fromList
        [ ((mn, nm), ty)
        | (mn, (sm, _)) <- Map.toList byName
        , (nm, ty) <- Map.toList (moduleUsageValueResultTypes sm)
        ]
    resultFor local (GName mn nm) =
      qualifyStorageExpr (resultQualifier local mn) (sourceStorageTypeNamesIn byName mn)
        <$> Map.lookup (mn, nm) sourceResults

usageImportedCtors ::
  Map.Map ModuleName (Module, [Fragment]) ->
  CheckState ->
  ImportEnv ->
  Map.Map Text [(Text, [CtorParamInfo])]
usageImportedCtors byName st ie =
  directCtors
    `Map.union` resolvedAliasCtors
    `Map.union` qualifiedTypeCtors
    `Map.union` moduleQualifiedTypeCtors
    `Map.union` aliasQualifiedTypeCtors
  where
    importedNames = usageImportedNames st ie
    sourceCtors = usageSourceCtors byName
    sourceDataCtors =
      Map.fromList
        [ ((mn, nameText (ddName dd)), [nameText (cdName c) | c <- ddCtors dd])
        | (mn, (sm, _)) <- Map.toList byName
        , DData _ dd _ <- modDecls sm
        ]
    sourceDataModules = nub [mn | ((mn, _), _) <- Map.toList sourceDataCtors]
    directCtors =
      Map.mapMaybeWithKey
        (\local g -> rekeyCtorFact local <$> ctorsFor g)
        importedNames
    resolvedAliasCtors =
      Map.mapMaybeWithKey
        ( \local g -> do
            target <- resolvedCtorAliasTarget st g
            rekeyCtorFact local <$> ctorFactsForTarget sourceCtors target
        )
        importedNames
    qualifiedTypeCtors =
      Map.fromList
        [ (localTy <> "." <> ctor, rekeyQualifiedCtorSiblings localTy siblings)
        | (localTy, GName mn sourceTy) <- Map.toList importedNames
        , ctor <- Map.findWithDefault [] (mn, sourceTy) sourceDataCtors
        , Just siblings <- [Map.lookup (mn, sourceTy <> "." <> ctor) sourceCtors]
        ]
    moduleQualifiedTypeCtors =
      Map.fromList
        [ (moduleNameText mn <> "." <> sourceTy <> "." <> ctor, rekeyQualifiedCtorSiblings (moduleNameText mn <> "." <> sourceTy) siblings)
        | ((mn, sourceTy), ctors) <- Map.toList sourceDataCtors
        , mn `elem` sourceDataModules
        , ctor <- ctors
        , Just siblings <- [Map.lookup (mn, sourceTy <> "." <> ctor) sourceCtors]
        ]
    aliasQualifiedTypeCtors =
      Map.fromList
        [ (alias <> "." <> sourceTy <> "." <> ctor, rekeyQualifiedCtorSiblings (alias <> "." <> sourceTy) siblings)
        | (alias, mn) <- Map.toList (ieAliases ie)
        , sourceTy <- sourceDataTypeNames mn
        , Just ctors <- [Map.lookup (mn, sourceTy) sourceDataCtors]
        , ctor <- ctors
        , Just siblings <- [Map.lookup (mn, sourceTy <> "." <> ctor) sourceCtors]
        ]
    ctorsFor (GName mn nm) = (\siblings -> (nm, siblings)) <$> Map.lookup (mn, nm) sourceCtors
    sourceDataTypeNames mn =
      [ ty
      | ((mn', ty), _) <- Map.toList sourceDataCtors
      , mn' == mn
      ]
    rekeyQualifiedCtorSiblings localTy siblings =
      [(localTy <> "." <> ctorLeaf cn, ps) | (cn, ps) <- siblings]

usageLocalCtorAliases ::
  Map.Map ModuleName (Module, [Fragment]) ->
  CheckState ->
  Module ->
  Map.Map Text [(Text, [CtorParamInfo])]
usageLocalCtorAliases byName st m =
  Map.fromList
    [ (alias, rekeyCtorFact alias facts)
    | DLet _ (LetDef (Just n) _ Nothing _ [] _ _ _) _ <- modDecls m
    , let alias = nameText n
          aliasG = GName (csModule st) alias
    , Just target <- [resolvedCtorAliasTarget st aliasG]
    , Just facts <- [ctorFactsForTarget sourceCtors target]
    ]
  where
    sourceCtors = usageSourceCtors byName

usageSourceCtors ::
  Map.Map ModuleName (Module, [Fragment]) ->
  Map.Map (ModuleName, Text) [(Text, [CtorParamInfo])]
usageSourceCtors byName =
  Map.fromList
    [ ((mn, nm), siblings)
    | (mn, (sm, _)) <- Map.toList byName
    , (nm, siblings) <- Map.toList (moduleUsageCtors sm)
    ]

resolvedCtorAliasTarget :: CheckState -> GName -> Maybe GName
resolvedCtorAliasTarget st g =
  case Map.lookup g (csCoreBodies st) of
    Just (CGlob target)
      | Map.member target (csCtors st) -> Just target
    _ -> Nothing

ctorFactsForTarget ::
  Map.Map (ModuleName, Text) [(Text, [CtorParamInfo])] ->
  GName ->
  Maybe (Text, [(Text, [CtorParamInfo])])
ctorFactsForTarget sourceCtors (GName mn nm) =
  case Map.lookup (mn, nm) sourceCtors of
    Just siblings -> Just (nm, siblings)
    Nothing -> Nothing

rekeyCtorFact :: Text -> (Text, [(Text, [CtorParamInfo])]) -> [(Text, [CtorParamInfo])]
rekeyCtorFact local (sourceHead, siblings) =
  case T.stripSuffix sourceHead local of
    Just prefix
      | not (T.null prefix)
      , "." `T.isSuffixOf` prefix ->
          [(prefix <> ctorLeaf cn, ps) | (cn, ps) <- siblings]
    _ | local == sourceHead -> siblings
    _ ->
      [ (local, params)
      | Just params <- [lookup sourceHead siblings]
      ]

ctorLeaf :: Text -> Text
ctorLeaf nm =
  let leaf = snd (T.breakOnEnd "." nm)
   in if T.null leaf then nm else leaf

usageImportedRecordAliases ::
  Map.Map ModuleName (Module, [Fragment]) ->
  CheckState ->
  ImportEnv ->
  Map.Map Text [(Text, Maybe Quantity)]
usageImportedRecordAliases byName st ie =
  Map.mapMaybe aliasesFor (usageImportedNames st ie)
  where
    sourceAliases =
      Map.fromList
        [ ((mn, nm), fields)
        | (mn, (sm, _)) <- Map.toList byName
        , (nm, fields) <- Map.toList (moduleUsageRecordAliases sm)
        ]
    aliasesFor (GName mn nm) = Map.lookup (mn, nm) sourceAliases

usageImportedRecordShapes ::
  Map.Map ModuleName (Module, [Fragment]) ->
  CheckState ->
  ImportEnv ->
  Map.Map Text RecordShape
usageImportedRecordShapes byName st ie =
  builtinShapes `Map.union` qualifiedAliasShapes `Map.union` directShapes
  where
    sourceShapes =
      Map.fromList
        [ ((mn, nm), shapes)
        | (mn, (sm, _)) <- Map.toList byName
        , (nm, shapes) <- Map.toList (moduleUsageRecordShapes sm)
        ]
    directShapes = directClosure `Map.union` Map.mapMaybeWithKey directShapeFor importedNames
    importedNames = usageImportedNames st ie
    builtinShapes =
      Map.fromList
        [ (local, shape)
        | (local, g) <- Map.toList importedNames
        , Just shape <- [usageBuiltinRecordShape g]
        ]
    importedGlobals = Map.elems importedNames
    directShapeModules =
      nub
        [ mn
        | g@(GName mn _) <- importedGlobals
        , isJust (shapesFor g)
        ]
    directClosure =
      Map.fromList
        [ (sourceKey mn nm, qualifyRecordShapeTypes (moduleNameText mn) (sourceStorageTypeNamesIn byName mn) shapes)
        | ((mn, nm), shapes) <- Map.toList sourceShapes
        , mn `elem` directShapeModules
        ]
    qualifiedAliasShapes =
      Map.fromList
        [ (alias <> "." <> nm, qualifyRecordShapeTypes alias sourceShapeNames shapes)
        | (alias, mn) <- Map.toList (ieAliases ie)
        , nm <- exportedMemberNames st mn
        , let sourceShapeNames = sourceStorageTypeNamesIn byName mn
        , Just shapes <- [Map.lookup (mn, nm) sourceShapes]
        ]
    shapesFor (GName mn nm) = Map.lookup (mn, nm) sourceShapes
    directShapeFor _local (GName mn nm) =
      qualifyRecordShapeTypes (moduleNameText mn) (sourceStorageTypeNamesIn byName mn) <$> Map.lookup (mn, nm) sourceShapes
    sourceKey mn nm = moduleNameText mn <> "." <> nm

usageBuiltinRecordShape :: GName -> Maybe RecordShape
usageBuiltinRecordShape g
  | g == prelZipper =
      Just $
        RecordShape
          ["whole", "focus", "replace"]
          [ FieldShape "focus" Nothing Nothing
          , FieldShape "fill" (Just QOne) Nothing
          ]
  | otherwise = Nothing

usageImportedRecordDeps ::
  Map.Map ModuleName (Module, [Fragment]) ->
  CheckState ->
  ImportEnv ->
  Map.Map Text [(Text, [Text])]
usageImportedRecordDeps byName st ie =
  qualifiedAliasDeps `Map.union` directDeps
  where
    sourceDeps =
      Map.fromList
        [ ((mn, nm), deps)
        | (mn, (sm, _)) <- Map.toList byName
        , (nm, deps) <- Map.toList (moduleUsageRecordDeps sm)
        ]
    importedNames = usageImportedNames st ie
    importedGlobals = Map.elems importedNames
    directDeps = directClosure `Map.union` Map.mapMaybe depsFor importedNames
    directDepModules =
      nub
        [ mn
        | g@(GName mn _) <- importedGlobals
        , isJust (depsFor g)
        ]
    directClosure =
      Map.fromList
        [ (moduleNameText mn <> "." <> nm, deps)
        | ((mn, nm), deps) <- Map.toList sourceDeps
        , mn `elem` directDepModules
        ]
    qualifiedAliasDeps =
      Map.fromList
        [ (alias <> "." <> nm, deps)
        | (alias, mn) <- Map.toList (ieAliases ie)
        , nm <- exportedMemberNames st mn
        , Just deps <- [Map.lookup (mn, nm) sourceDeps]
        ]
    depsFor (GName mn nm) = Map.lookup (mn, nm) sourceDeps

resultQualifier :: Text -> ModuleName -> Text
resultQualifier local mn =
  case T.breakOnEnd "." local of
    (prefix, _) | not (T.null prefix) -> T.dropEnd 1 prefix
    _ -> moduleNameText mn

sourceStorageTypeNamesIn :: Map.Map ModuleName (Module, [Fragment]) -> ModuleName -> [Text]
sourceStorageTypeNamesIn byName mn =
  sourceRecordShapeNames ++ sourceDataTypeNames
  where
    sourceRecordShapeNames =
      [ nm
      | (mn', (sm, _)) <- Map.toList byName
      , mn' == mn
      , nm <- Map.keys (moduleUsageRecordShapes sm)
      ]
    sourceDataTypeNames =
      [ nameText (ddName dd)
      | (mn', (sm, _)) <- Map.toList byName
      , mn' == mn
      , DData _ dd _ <- modDecls sm
      ]

qualifyRecordShapeTypes :: Text -> [Text] -> RecordShape -> RecordShape
qualifyRecordShapeTypes alias sourceShapeNames shape =
  shape {rsFields = qualifyFieldShapeTypes alias sourceShapeNames (rsFields shape)}

qualifyFieldShapeTypes :: Text -> [Text] -> [FieldShape] -> [FieldShape]
qualifyFieldShapeTypes alias sourceShapeNames =
  map $ \s -> s {fsType = qualifyStorageExpr alias sourceShapeNames <$> fsType s}

qualifyStorageExpr :: Text -> [Text] -> Expr -> Expr
qualifyStorageExpr alias sourceShapeNames = qualifyExpr
  where
    isSourceShape n = nameText n `elem` sourceShapeNames
    qualifyExpr = \case
      EVar n
        | isSourceShape n ->
            EDot (EVar (Name alias (nameSpan n))) (DotName n)
      ETuple es sp -> ETuple (map qualifyExpr es) sp
      ERecordType fs mtail sp ->
        ERecordType [f {rtfType = qualifyExpr (rtfType f)} | f <- fs] (qualifyExpr <$> mtail) sp
      EApp f args -> EApp (qualifyExpr f) (map qualifyArg args)
      EDot e m -> EDot (qualifyExpr e) m
      EQDot e m -> EQDot (qualifyExpr e) m
      EArrow b body -> EArrow (qualifyBinder b) (qualifyExpr body)
      EForall bs body sp -> EForall (map qualifyBinder bs) (qualifyExpr body) sp
      EExists bs body sp -> EExists (map qualifyBinder bs) (qualifyExpr body) sp
      ETraitArrow c body -> ETraitArrow (qualifyExpr c) (qualifyExpr body)
      EEffRow fields mtail sp -> EEffRow [(n, qualifyExpr e) | (n, e) <- fields] (qualifyExpr <$> mtail) sp
      EVariant arms mtail sp -> EVariant (map qualifyVariant arms) (qualifyExpr <$> mtail) sp
      EAscription e ty sp -> EAscription (qualifyExpr e) (qualifyExpr ty) sp
      ECaptures e caps sp -> ECaptures (qualifyExpr e) caps sp
      EOptionSugar e sp -> EOptionSugar (qualifyExpr e) sp
      other -> other
    qualifyBinder b = b {bType = qualifyExpr <$> bType b, bDefault = qualifyExpr <$> bDefault b}
    qualifyVariant (VariantArm e ty) = VariantArm (qualifyExpr e) (qualifyExpr <$> ty)
    qualifyArg = \case
      ArgExplicit e -> ArgExplicit (qualifyExpr e)
      ArgImplicit e -> ArgImplicit (qualifyExpr e)
      ArgInout e sp -> ArgInout (qualifyExpr e) sp
      ArgNamedBlock items sp ->
        ArgNamedBlock [(n, qualifyExpr <$> me) | (n, me) <- items] sp

usageImportedRefOps :: CheckState -> ImportEnv -> Map.Map Text RefOp
usageImportedRefOps st ie =
  Map.mapMaybe refOpFor (usageImportedNames st ie)
  where
    refOpFor g
      | g == prelReadRef = Just RefRead
      | g == prelWriteRef = Just RefWrite
      | otherwise = Nothing

usageRecognizedRefOps :: CheckState -> Map.Map Span RefOp
usageRecognizedRefOps st =
  Map.mapMaybe refOpFor (csRecognizedRefOps st)
  where
    refOpFor op
      | op == T.pack "readRef" = Just RefRead
      | op == T.pack "writeRef" = Just RefWrite
      | otherwise = Nothing

usageImportedBorrowViewHeads :: CheckState -> ImportEnv -> Set.Set Text
usageImportedBorrowViewHeads st ie =
  Map.keysSet $
    Map.filter (== prelBorrowView) (usageImportedNames st ie)

usageVisibleMonadicResultHeads :: CheckState -> ImportEnv -> Module -> Set.Set Text
usageVisibleMonadicResultHeads st ie m =
  usageModuleMonadicResultHeads st (csModule st)
    `Set.union` (usageImportedMonadicResultHeads st ie Set.\\ localTypeHeads m)

usageImportedMonadicResultHeads :: CheckState -> ImportEnv -> Set.Set Text
usageImportedMonadicResultHeads st ie =
  Set.fromList
    [ alias
    | (alias, g) <- Map.toList (usageImportedNames st ie)
    , g `Set.member` usageMonadicCarrierGlobals st
    ]

usageModuleMonadicResultHeads :: CheckState -> ModuleName -> Set.Set Text
usageModuleMonadicResultHeads st mn =
  Set.fromList
    [ nm
    | GName im nm <- Set.toList (usageMonadicCarrierGlobals st)
    , im == mn
    ]

usageMonadicCarrierGlobals :: CheckState -> Set.Set GName
usageMonadicCarrierGlobals st =
  Set.fromList
    [ g
    | inst <- csInstances st
    , ieTrait inst == prelMonad || ieTrait inst == prelMonadRef
    , Just g <- [monadicCarrierHead (ieHead inst)]
    ]

monadicCarrierHead :: [Term] -> Maybe GName
monadicCarrierHead (ty : _) = coreTypeHeadGName ty
monadicCarrierHead [] = Nothing

coreTypeHeadGName :: Term -> Maybe GName
coreTypeHeadGName = \case
  CGlob g -> Just g
  CApp _ f _ -> coreTypeHeadGName f
  CForceE t -> coreTypeHeadGName t
  _ -> Nothing

localTypeHeads :: Module -> Set.Set Text
localTypeHeads m =
  Set.fromList $
    [nameText (ddName dd) | DData _ dd _ <- modDecls m]
      ++ [nameText n | DTypeAlias _ n _ _ _ _ <- modDecls m]

usageImportedProjections ::
  Map.Map ModuleName (Module, [Fragment]) ->
  CheckState ->
  ImportEnv ->
  Map.Map Text ProjUse
usageImportedProjections byName st ie =
  Map.mapMaybe projFor (usageImportedNames st ie)
  where
    sourceProjs =
      Map.fromList
        [ ((mn, nm), pu)
        | (mn, (sm, _)) <- Map.toList byName
        , (nm, pu) <- Map.toList (moduleUsageProjections sm)
        ]
    projFor (GName mn nm) = Map.lookup (mn, nm) sourceProjs

usageImportedDuplicableStorageHeads :: CheckState -> ImportEnv -> Set.Set Text
usageImportedDuplicableStorageHeads st ie =
  Set.fromList
    [ alias
    | (alias, g) <- Map.toList (usageImportedNames st ie)
    , g `Set.member` duplicableStorageTypes
    ]
  where
    duplicableStorageTypes =
      Set.fromList
        [ prelUnit
        , prelBool
        , prelString
        , prelNat
        , prelInt
        , prelInteger
        , prelDouble
        , prelByte
        , prelGrapheme
        , prelUnicodeScalar
        , gPrel "Ordering"
        , prelRegion
        , prelRef
        , gPrel "TVar"
        , gPrel "Fiber"
        , gPrel "Promise"
        , gPrel "Scope"
        , gPrel "Duration"
        , gPrel "Instant"
        ]

usageImportedNames :: CheckState -> ImportEnv -> Map.Map Text GName
usageImportedNames st ie =
  Map.fromListWith
    const
    ( Map.toList (ieScope ie)
        ++ [ (alias <> "." <> nm, usageExportTarget st mn nm)
           | (alias, mn) <- Map.toList (ieAliases ie)
           , nm <- exportedMemberNames st mn
        ]
    )

usageExportTarget :: CheckState -> ModuleName -> Text -> GName
usageExportTarget st mn nm =
  Map.findWithDefault (GName mn nm) nm (Map.findWithDefault Map.empty mn (csReExports st))

exportedMemberNames :: CheckState -> ModuleName -> [Text]
exportedMemberNames st mn
  | mn == preludeModule = preludeWildcardMemberNames st
  | otherwise = fromMaybe [] (Map.lookup mn (csModuleExports st))

-- | Path-derived module name (§8.1, simplified: basename only).
moduleNameOf :: FilePath -> ModuleName
moduleNameOf path =
  let base = T.pack (takeWhileEnd (/= '/') path)
      noExt = T.takeWhile (/= '.') base
   in ModuleName [if T.null noExt then "main" else noExt]
  where
    takeWhileEnd f = reverse . takeWhile f . reverse

-- | §8.1 source-root-relative module name: each directory below the
-- root is one segment, the basename (extension dropped) is the last.
moduleNameRelTo :: FilePath -> FilePath -> ModuleName
moduleNameRelTo root path =
  let rel = case stripPrefixStr (root ++ "/") path of
        Just r -> r
        Nothing -> path
      segs =
        [ T.takeWhile (/= '.') s
        | s <- T.splitOn "/" (T.pack rel)
        , not (T.null s)
        ]
   in case [s | s <- segs, not (T.null s)] of
        [] -> ModuleName ["main"]
        ss -> ModuleName ss
  where
    stripPrefixStr pre s =
      if take (length pre) s == pre then Just (drop (length pre) s) else Nothing

-- ── Source loading and hygiene (§3.1.3) ──────────────────────────────

-- | Read one source file. The raw bytes are validated as UTF-8
-- (invalid bytes are an 'E_UNICODE_INVALID_UTF8' error at the top of
-- the file, and the text is recovered by U+FFFD replacement); valid
-- files receive the optional §3.1.3 source-hygiene warnings.
loadSourceFile :: FilePath -> IO (Text, Diagnostics)
loadSourceFile path = do
  bytes <- BS.readFile path
  case TE.decodeUtf8' bytes of
    Left _ ->
      pure
        ( TE.decodeUtf8With TEE.lenientDecode bytes
        , [ diag SevError StageLex "E_UNICODE_INVALID_UTF8"
              (Just "kappa-hs.unicode.invalid-utf8") (lineSpan 1)
              "source file is not valid UTF-8 (Spec §3.1.3)"
          ]
        )
    Right txt -> pure (txt, sourceHygieneWarnings path txt)
  where
    lineSpan n = Span path (Pos n 1) (Pos n 2)

-- | Optional §3.1.3 source-text warnings (at most one per class per
-- file, at the first offending line):
--
--   * 'W_UNICODE_BIDI_CONTROL' — raw bidirectional control characters
--     outside string literals (comments and identifiers included);
--   * 'W_UNICODE_CONFUSABLE_IDENTIFIER' — identifier-position
--     characters visually identical to an ASCII letter under the
--     documented skeleton table (strings and comments excluded);
--   * 'W_UNICODE_NON_NORMALIZED_SOURCE_TEXT' — source text that is not
--     in Unicode Normalization Form C.
sourceHygieneWarnings :: FilePath -> Text -> Diagnostics
sourceHygieneWarnings path txt =
  take 1 bidi ++ take 1 confusable ++ take 1 nonNfc
  where
    lns = zip [1 :: Int ..] (T.lines txt)
    warn n code fam msg =
      diag SevWarning StageLex code (Just fam) (Span path (Pos n 1) (Pos n 2)) msg
    bidi =
      [ warn n "W_UNICODE_BIDI_CONTROL" "kappa-hs.unicode.bidi-control"
          "source text contains a bidirectional control character outside a string literal (§3.1.3)"
      | (n, l) <- lns
      , T.any isBidiControl (stripStrings l)
      ]
    confusable =
      [ warn n "W_UNICODE_CONFUSABLE_IDENTIFIER" "kappa.unicode.name"
          "an identifier contains characters visually confusable with ASCII letters (§3.1.3)"
      | (n, l) <- lns
      , T.any (isJust . confusableWithAscii) (stripComment (stripStrings l))
      ]
    nonNfc =
      [ warn n "W_UNICODE_NON_NORMALIZED_SOURCE_TEXT" "kappa-hs.unicode.non-normalized-text"
          "source text is not in Unicode Normalization Form C (§3.1.3)"
      | (n, l) <- lns
      , not (isNfcQuick l)
      ]
    -- blank out double-quoted string contents (escape-aware, one line)
    stripStrings l = T.pack (outside (T.unpack l))
      where
        outside [] = []
        outside ('"' : cs) = '"' : inside cs
        outside (c : cs) = c : outside cs
        inside [] = []
        inside ('\\' : _ : cs) = ' ' : ' ' : inside cs
        inside ('"' : cs) = '"' : outside cs
        inside (_ : cs) = ' ' : inside cs
    stripComment l = fst (T.breakOn "--" l)
