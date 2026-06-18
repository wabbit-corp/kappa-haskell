-- | Compilation pipeline: prelude bootstrap, multi-file units with
-- same-module fragments (§8.1), §8.2 acyclic dependency ordering with
-- cycle diagnostics, §8.3 import processing (aliases, item selection,
-- wildcards with except-lists), §8.5 export visibility, then
-- parse → fixity resolution → elaboration.
module Kappa.Pipeline
  ( CompiledUnit (..)
  , TraceEvent
  , compileFiles
  , compileFilesIn
  , compileFilesWithConfig
  , moduleNameRelTo
  , compileSourceWithPrelude
  , importScopeFor
  , loadSourceFile
  , compileManifest
  , manifestModuleName
  , compileProgramWithNative
  , reservedHostRootDiag
  , moduleNameOf
  ) where

import Control.Monad.State.Strict (evalState)
import qualified Data.ByteString as BS
import Data.Char (isAlphaNum, isAscii, isLetter)
import Data.List (foldl', nub, partition)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Encoding.Error as TEE
import Kappa.Backend.NativeFfi
  ( ResolvedNativeSymbol (..)
  , nativeMemberType
  )
import Kappa.Check
import Kappa.Config (ConfigProfile (..), checkConfigUnit)
import Kappa.Core (GName (..), Term, gnameText)
import Kappa.Diagnostic
import Kappa.Eval (EvalCtx (..), Globals (..), eval)
import Kappa.Parser (parseModule)
import Kappa.Prelude
  ( builtinState
  , preludeSource
  , stdAtomicSource
  , stdBridgeSource
  , stdFfiCSource
  , stdFfiSource
  , stdGradualSource
  , stdDerivingShapeSource
  , stdHashSource
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
import Kappa.Usage (usageDiagnostics)

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
            [ (ModuleName ["std", "deriving", "shape"], "<std.deriving.shape>", stdDerivingShapeSource)
            , (ModuleName ["std", "hash"], "<std.hash>", stdHashSource)
            , (ModuleName ["std", "bytes"], "<std.bytes>", stdBytesSource)
            , (ModuleName ["std", "unicode"], "<std.unicode>", stdUnicodeSource)
            , (ModuleName ["std", "ffi"], "<std.ffi>", stdFfiSource)
            , (ModuleName ["std", "ffi", "c"], "<std.ffi.c>", stdFfiCSource)
            , (ModuleName ["std", "atomic"], "<std.atomic>", stdAtomicSource)
            , (ModuleName ["std", "gradual"], "<std.gradual>", stdGradualSource)
            , (ModuleName ["std", "bridge"], "<std.bridge>", stdBridgeSource) -- after std.gradual
            , (ModuleName ["std", "supervisor"], "<std.supervisor>", stdSupervisorSource)
            , -- §35.3/§29.8: config-mode schema modules. They are checked
              -- here so their config-safe vocabulary is registered in
              -- csGlobals/csCtors/csModuleExports; a build-manifest loader
              -- (Kappa.Config) installs their names into the manifest's
              -- schema scope without an ordinary import.
              (ModuleName ["std", "config"], "<std.config>", stdConfigSource)
            , (ModuleName ["std", "build"], "<std.build>", stdBuildSource)
            ]
          (st', sdiags) =
            foldl
              (\(stAcc, dsAcc) (mn, path, src) ->
                 let (stNext, ds) = stdModule mn path src stAcc
                  in (stNext, dsAcc ++ ds))
              (st, [])
              stdSources
       in (st', recovered ++ rdiags ++ diags ++ sdiags)

-- | Compile one embedded standard-library module on top of the
-- prelude state and register its exports.
stdModule :: ModuleName -> FilePath -> Text -> CheckState -> (CheckState, Diagnostics)
stdModule mn path src st0 =
  case parseModule path src of
    Left ds -> (st0, ds)
    Right (m, recovered) ->
      let (m', rdiags) = resolveModule defaultFixities m
          ie = buildImports st0 m'
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

-- | Scope with every prelude global visible unqualified (§28.1).
preludeScope :: CheckState -> Map.Map Text GName
preludeScope st =
  Map.fromList
    [ (gnameText g, g)
    | g@(GName m _) <- Map.keys (csGlobals st) ++ Map.keys (csCtors st)
    , m == preludeModule
    , not ("__inst_" `T.isPrefixOf` gnameText g)
    ]

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
applyNativeModules syms st0 = foldl' addMod st0 byModule
  where
    byModule =
      Map.toList $
        foldl' (\m s -> Map.insertWith (++) (rnsModule s) [s] m) Map.empty syms
    addMod st (mn, ss) =
      let ec = EvalCtx (Globals (csGlobals st)) (csMetas st) False (csFacts st)
          gdOf s = GlobalDef (eval ec [] (nativeMemberType (rnsParams s) (rnsResult s))) Nothing False
          gs =
            foldl'
              (\g s -> Map.insert (GName mn (rnsMember s)) (gdOf s) g)
              (csGlobals st)
              ss
       in st
            { csGlobals = gs
            , csModuleExports = Map.insert mn (map rnsMember ss) (csModuleExports st)
            }

-- | The gname→resolved-symbol map for the provided host bindings, threaded
-- into codegen so each member reference lowers to a DIRECT typed call.
nativeHostSymbols :: [ResolvedNativeSymbol] -> Map.Map GName ResolvedNativeSymbol
nativeHostSymbols syms =
  Map.fromList [(GName (rnsModule s) (rnsMember s), s) | s <- syms]

-- | §8.3.5 reserved host roots. A source-defined module at or under one of
-- these is a compile-time error (host binding modules are host-supplied).
reservedHostRoots :: [[Text]]
reservedHostRoots =
  [ ["host", "jvm", "jni"]
  , ["host", "jvm"]
  , ["host", "dotnet"]
  , ["host", "native"]
  , ["host", "python"]
  ]

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

-- | The general worker. @inject@ transforms the post-prelude base state
-- before the user modules are checked — used to register manifest-selected
-- @host.native.*@ host-binding modules (§8.3.5/§34.5.3) so a program can
-- @import@ them. Plain compilation passes 'id'.
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
      -- merge same-module fragments (§8.1) in first-appearance order
      moduleOrder = nub [mn | (mn, _) <- goodFrags]
      merged =
        [ (mn, mergedOf frs, frs)
        | mn <- moduleOrder
        , let frs = [fr | (mn', fr) <- goodFrags, mn' == mn]
        , not (null frs)
        ]
      mergedOf frs =
        Module
          (nub (concatMap (modAttrs . frModule) frs))
          (modHeader (frModule (head frs)))
          (concatMap (modDecls . frModule) frs)
      unitModules = [mn | (mn, _, _) <- merged]
      -- §8.2: dependency order over import/export references, with
      -- cycle detection
      depMap =
        Map.fromList
          [ ( mn
            , [ (dep, sp)
              | (ref, sp) <- moduleRefsOf m
              , dep <- refModuleCandidates unitModules ref
              , dep /= mn
              ]
            )
          | (mn, m, _) <- merged
          ]
      (order, cycleDiags) = topoOrder unitModules depMap
      byName = Map.fromList [(mn, (m, frs)) | (mn, m, frs) <- merged]
      step (st, chunks, trc) mn = case Map.lookup mn byName of
        Nothing -> (st, chunks, trc)
        Just (m, frs) ->
          let -- §5.5: exported fixity declarations are imported together
              -- with the corresponding operator name
              importedFix = importedFixities m
              effFixities = Map.unionWith (++) importedFix defaultFixities
              fullFixities = Map.unionWith (++) (fixitiesOf (modDecls m)) effFixities
              (m', rdiags) = resolveModule effFixities m
              ie = buildImportsIn unitModules st m'
              st0 =
                st
                  { csModule = mn
                  , csScope = ieScope ie
                  , csScopeAmbig = ieAmbig ie
                  , csModuleAliases = ieAliases ie
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
              (st1, cdiags0) = checkModule st0 m'
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
                  else usageDiagnostics (csExpansions st1) m'
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
           in ( st1
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
      finalSt' =
        finalSt
          { csCoreBodies =
              Map.map
                (\tm -> evalState (zonkTermM 0 tm) finalSt)
                (csCoreBodies finalSt)
          }
   in CompiledUnit finalSt' allDiags lastName allTrace

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
    pbd = "PrivateByDefault" `elem` map nameText (modAttrs m)
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
buildImportsIn unitMods st m = foldl' addSpec ie0 specs
  where
    ie0 = ImportEnv (preludeScope st) Map.empty Map.empty [] [] [] []
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
      | mn == preludeModule = Map.keys (preludeScope st)
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
                Nothing -> ie
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
    wildMembers = memberNames
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
