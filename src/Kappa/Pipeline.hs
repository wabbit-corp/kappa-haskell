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
  , moduleNameRelTo
  , compileSourceWithPrelude
  , importScopeFor
  , loadSourceFile
  ) where

import qualified Data.ByteString as BS
import Data.Char (isAlphaNum, isAscii, isLetter)
import Data.List (foldl', nub)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Encoding.Error as TEE
import Kappa.Check
import Kappa.Core (GName (..), gnameText)
import Kappa.Diagnostic
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
  , stdSupervisorSource
  , stdUnicodeSource
  )
import Kappa.Resolve (defaultFixities, fixitiesOf, resolveModule)
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
            , (ModuleName ["std", "unicode"], "<std.unicode>", stdUnicodeSource)
            , (ModuleName ["std", "ffi"], "<std.ffi>", stdFfiSource)
            , (ModuleName ["std", "ffi", "c"], "<std.ffi.c>", stdFfiCSource)
            , (ModuleName ["std", "atomic"], "<std.atomic>", stdAtomicSource)
            , (ModuleName ["std", "gradual"], "<std.gradual>", stdGradualSource)
            , (ModuleName ["std", "bridge"], "<std.bridge>", stdBridgeSource) -- after std.gradual
            , (ModuleName ["std", "supervisor"], "<std.supervisor>", stdSupervisorSource)
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

-- | Multi-file compilation with basename-derived module names
-- (standalone files: §8.1 path-name derivation is not in force).
compileFiles :: [(FilePath, Text)] -> CompiledUnit
compileFiles = compileFilesWith False moduleNameOf

-- | Like 'compileFiles', but header-less module names derive from the
-- path relative to @root@ (the §T.2 suite root is the §8.1 source root
-- for module-path derivation): @root/demo/value.kp@ → @demo.value@.
compileFilesIn :: FilePath -> [(FilePath, Text)] -> CompiledUnit
compileFilesIn root = compileFilesWith True (moduleNameRelTo root)

-- One parsed source fragment.
data Fragment = Fragment
  { frPath :: !FilePath
  , frModule :: !Module
  , frDiags :: !Diagnostics -- ^ parse-recovered diagnostics
  }

compileFilesWith :: Bool -> (FilePath -> ModuleName) -> [(FilePath, Text)] -> CompiledUnit
compileFilesWith packageMode nameOf files =
  let (pst, pdiags) = preludeState
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
        [ diag SevError StageImports "E_MODULE_PATH_MISMATCH" (Just "kappa.module.path-mismatch")
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
              (m', rdiags) = resolveModule (Map.unionWith (++) importedFix defaultFixities) m
              ie = buildImportsIn unitModules st m'
              st0 =
                st
                  { csModule = mn
                  , csScope = ieScope ie
                  , csScopeAmbig = ieAmbig ie
                  , csModuleAliases = ieAliases ie
                  , csDiags = []
                  }
              (st1, cdiags0) = checkModule st0 m'
              recovered = concatMap frDiags frs
              -- recovery hygiene (§3.1.14): when part of the module
              -- failed to parse, a signature's "missing" definition may
              -- simply be in the unparsed region — do not pile a
              -- §9.1 satisfaction error on top of the parse error
              parseErrored = any isError recovered
              cdiags =
                if parseErrored
                  then [d | d <- cdiags0, dCode d /= "E_SIGNATURE_UNSATISFIED"]
                  else cdiags0
              preDiags = recovered ++ rdiags ++ ieDiags ie ++ cdiags
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
   in CompiledUnit finalSt allDiags lastName allTrace

renderModuleName :: ModuleName -> Text
renderModuleName (ModuleName segs) = T.intercalate "." segs

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
                diag SevError StageImports "E_IMPORT_CYCLE" (Just "kappa.import.cycle") sp
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
moduleExportNames m = nub (concatMap go (modDecls m))
  where
    pbd = "PrivateByDefault" `elem` map nameText (modAttrs m)
    vis mods = case dmVisibility mods of
      VisPublic -> True
      VisPrivate -> False
      VisDefault -> not pbd
    go = \case
      DSig mods n _ _ -> [nameText n | vis mods]
      DLet mods (LetDef (Just n) _ _ _ _ _ _ _) _ -> [nameText n | vis mods]
      DData mods (DataDecl n _ _ ctors) _
        | vis mods -> nameText n : [nameText cn | CtorDecl cn _ _ _ <- ctors]
      DTypeAlias mods n _ _ _ _ -> [nameText n | vis mods]
      DTrait mods td _ -> [nameText (trName td) | vis mods]
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
    ie0 = ImportEnv (preludeScope st) Map.empty Map.empty [] [] []
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
         in if not (knownModule mn)
              then unknownModule ie sp mn
              else foldl' (addItem mn sp) ie items
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
    addItem mn sp ie it =
      let nm = nameText (iiName it)
          alias = maybe nm nameText (iiAlias it)
          g = exportTarget mn nm
       in if nm `elem` memberNames mn
            then case kindMismatch g (iiKind it) of
              Just why ->
                err ie sp "E_IMPORT_ITEM_NOT_FOUND" "kappa.import.item"
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
                  err ie sp "E_IMPORT_ITEM_NOT_FOUND" "kappa.import.item"
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
      err ie sp "E_IMPORT_ITEM_NOT_FOUND" "kappa.import.item"
        ("module '" <> renderModuleName mn <> "' does not export '" <> nm <> "' (Spec §8.3)")
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
            err ie sp "E_URL_IMPORT_REF_PIN_REQUIRES_LOCK" "kappa.import.url"
              "a 'ref:'-pinned URL import requires the resolved digest to be recorded in a lockfile in package mode (Spec §8.3.3); this implementation keeps no lockfile"
        | "#" `T.isPrefixOf` pin ->
            err ie sp "E_URL_IMPORT_UNSUPPORTED" "kappa.import.url"
              "URL module fetching is not supported by this implementation (Spec §8.3.2)"
      _ ->
        err ie sp "E_URL_IMPORT_UNPINNED_IN_PACKAGE_MODE" "kappa.import.url"
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
              (Just "kappa.unicode.invalid-utf8") (lineSpan 1)
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
      [ warn n "W_UNICODE_BIDI_CONTROL" "kappa.unicode.bidi-control"
          "source text contains a bidirectional control character outside a string literal (§3.1.3)"
      | (n, l) <- lns
      , T.any isBidiControl (stripStrings l)
      ]
    confusable =
      [ warn n "W_UNICODE_CONFUSABLE_IDENTIFIER" "kappa.unicode.confusable"
          "an identifier contains characters visually confusable with ASCII letters (§3.1.3)"
      | (n, l) <- lns
      , T.any (isJust . confusableWithAscii) (stripComment (stripStrings l))
      ]
    nonNfc =
      [ warn n "W_UNICODE_NON_NORMALIZED_SOURCE_TEXT" "kappa.unicode.non-normalized-text"
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
