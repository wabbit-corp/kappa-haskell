-- | Compilation pipeline: prelude bootstrap, module loading in import
-- order (§8.2 acyclic), parse → fixity resolution → elaboration.
module Kappa.Pipeline
  ( CompiledUnit (..)
  , TraceEvent
  , compileFiles
  , compileFilesIn
  , compileSourceWithPrelude
  , importScopeFor
  ) where

import Data.List (foldl')
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Check
import Kappa.Core (GName (..), gnameText)
import Kappa.Diagnostic
import Kappa.Parser (parseModule)
import Kappa.Prelude (builtinState, preludeSource)
import Kappa.Resolve (defaultFixities, resolveModule)
import Kappa.Source
import Kappa.Syntax

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

-- | Compile the prelude into the base state.
preludeState :: (CheckState, Diagnostics)
preludeState =
  case parseModule "<std.prelude>" preludeSource of
    Left ds -> (builtinState, ds)
    Right (m, recovered) ->
      let (m', rdiags) = resolveModule defaultFixities m
          (st, diags) = checkModule builtinState m'
       in (st, recovered ++ rdiags ++ diags)

-- | Scope with every prelude global visible unqualified (§28.1).
preludeScope :: CheckState -> Map.Map Text GName
preludeScope st =
  Map.fromList
    [ (gnameText g, g)
    | g@(GName m _) <- Map.keys (csGlobals st) ++ Map.keys (csCtors st)
    , m == preludeModule
    , not ("__inst_" `T.isPrefixOf` gnameText g)
    ]

-- | Per-file trace: parse always happens; KFrontIR construction and the
-- KCore lowering of the module happen only when the file parses.
fileTrace :: Bool -> [TraceEvent]
fileTrace parsedOk =
  ("parse", "file")
    : if parsedOk
      then [("buildKFrontIR", "file"), ("lowerKCore", "module")]
      else []

-- | Compile one source file (plus prelude) — used by check/run/test.
compileSourceWithPrelude :: FilePath -> Text -> CompiledUnit
compileSourceWithPrelude path src =
  let (pst, pdiags) = preludeState
      modName = moduleNameOf path
   in case parseModule path src of
        Left ds -> CompiledUnit pst (pdiags ++ ds) modName (fileTrace False)
        Right (m, recovered) ->
          let effName = case modHeader m of
                Just mp -> ModuleName (modPathName mp)
                Nothing -> modName
              (m', rdiags) = resolveModule defaultFixities m
              st0 =
                pst
                  { csModule = effName
                  , csScope = preludeScope pst
                  , csDiags = []
                  }
              (st1, cdiags) = checkModule st0 m'
              ediags = expectUnsatisfiedDiags st1
           in CompiledUnit st1 (pdiags ++ recovered ++ rdiags ++ cdiags ++ ediags) effName (fileTrace True)

-- | Unqualified scope induced by a module's import declarations over an
-- accumulated state (§7.1 visibility, import-selected): the prelude
-- scope extended with each imported module's globals.
importScopeFor :: CheckState -> Module -> Map.Map Text GName
importScopeFor st m = foldl' addImport (preludeScope st) (importsOf m)
  where
    addImport sc spec = case spec of
      ImportAll (RefPath mp) _ ->
        let im = ModuleName (modPathName mp)
         in sc
              `Map.union` Map.fromList
                [ (gnameText g, g)
                | g@(GName gm _) <- Map.keys (csGlobals st)
                , gm == im
                ]
      ImportItems (RefPath mp) items ->
        let im = ModuleName (modPathName mp)
            wanted = [(nameText (iiName i), maybe (nameText (iiName i)) nameText (iiAlias i)) | i <- items]
         in sc
              `Map.union` Map.fromList
                [ (alias, GName im orig)
                | (orig, alias) <- wanted
                , Map.member (GName im orig) (csGlobals st)
                ]
      _ -> sc

-- | Multi-file compilation: files are compiled in argument order into
-- one accumulated state (import statements select visibility; module
-- dependency order is the caller's responsibility in v1). Header-less
-- module names derive from the file basename.
compileFiles :: [(FilePath, Text)] -> CompiledUnit
compileFiles = compileFilesWith moduleNameOf

-- | Like 'compileFiles', but header-less module names derive from the
-- path relative to @root@ (the §T.2 suite root is the §8.1 source root
-- for module-path derivation): @root/demo/value.kp@ → @demo.value@.
compileFilesIn :: FilePath -> [(FilePath, Text)] -> CompiledUnit
compileFilesIn root = compileFilesWith (moduleNameRelTo root)

compileFilesWith :: (FilePath -> ModuleName) -> [(FilePath, Text)] -> CompiledUnit
compileFilesWith nameOf files =
  let (pst, pdiags) = preludeState
      -- diagnostics accumulate as reversed chunks and are concatenated
      -- once at the end (appending per file would be quadratic)
      step (st, chunks, trc) (path, src) =
        case parseModule path src of
          Left ds -> (st, ds : chunks, fileTrace False : trc)
          Right (m, recovered) ->
            let effName = case modHeader m of
                  Just mp -> ModuleName (modPathName mp)
                  Nothing -> nameOf path
                (m', rdiags) = resolveModule defaultFixities m
                scope = importScopeFor st m'
                st0 = st {csModule = effName, csScope = scope, csDiags = []}
                (st1, cdiags) = checkModule st0 m'
             in (st1, (recovered ++ rdiags ++ cdiags) : chunks, fileTrace True : trc)
      (finalSt, diagChunks, traceChunks) = foldl' step (pst, [pdiags], []) files
      -- §9.4: expect satisfaction is judged over the whole unit
      allDiags = concat (reverse diagChunks) ++ expectUnsatisfiedDiags finalSt
      lastName = case reverse files of
        ((p, _) : _) -> nameOf p
        [] -> ModuleName ["main"]
   in CompiledUnit finalSt allDiags lastName (concat (reverse traceChunks))

importsOf :: Module -> [ImportSpec]
importsOf m = concat [specs | DImport specs _ <- modDecls m]

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
