-- | Compilation pipeline: prelude bootstrap, module loading in import
-- order (§8.2 acyclic), parse → fixity resolution → elaboration.
module Kappa.Pipeline
  ( CompiledUnit (..)
  , compileFiles
  , compileSourceWithPrelude
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

data CompiledUnit = CompiledUnit
  { cuState :: !CheckState
  , cuDiags :: !Diagnostics
  , cuModule :: !ModuleName
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

-- | Compile one source file (plus prelude) — used by check/run/test.
compileSourceWithPrelude :: FilePath -> Text -> CompiledUnit
compileSourceWithPrelude path src =
  let (pst, pdiags) = preludeState
      modName = moduleNameOf path
   in case parseModule path src of
        Left ds -> CompiledUnit pst (pdiags ++ ds) modName
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
           in CompiledUnit st1 (pdiags ++ recovered ++ rdiags ++ cdiags) effName

-- | Multi-file compilation: files are compiled in argument order into
-- one accumulated state (import statements select visibility; module
-- dependency order is the caller's responsibility in v1).
compileFiles :: [(FilePath, Text)] -> CompiledUnit
compileFiles files =
  let (pst, pdiags) = preludeState
      -- diagnostics accumulate as reversed chunks and are concatenated
      -- once at the end (appending per file would be quadratic)
      step (st, chunks) (path, src) =
        case parseModule path src of
          Left ds -> (st, ds : chunks)
          Right (m, recovered) ->
            let effName = case modHeader m of
                  Just mp -> ModuleName (modPathName mp)
                  Nothing -> moduleNameOf path
                (m', rdiags) = resolveModule defaultFixities m
                scope = foldl' addImport (preludeScope st) (importsOf m')
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
                st0 = st {csModule = effName, csScope = scope, csDiags = []}
                (st1, cdiags) = checkModule st0 m'
             in (st1, (recovered ++ rdiags ++ cdiags) : chunks)
      (finalSt, diagChunks) = foldl' step (pst, [pdiags]) files
      allDiags = concat (reverse diagChunks)
      lastName = case reverse files of
        ((p, _) : _) -> moduleNameOf p
        [] -> ModuleName ["main"]
   in CompiledUnit finalSt allDiags lastName
  where
    importsOf m = concat [specs | DImport specs _ <- modDecls m]

-- | Path-derived module name (§8.1, simplified: basename only).
moduleNameOf :: FilePath -> ModuleName
moduleNameOf path =
  let base = T.pack (takeWhileEnd (/= '/') path)
      noExt = T.takeWhile (/= '.') base
   in ModuleName [if T.null noExt then "main" else noExt]
  where
    takeWhileEnd f = reverse . takeWhile f . reverse
