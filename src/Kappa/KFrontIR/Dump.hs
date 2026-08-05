{-# LANGUAGE DataKinds #-}

module Kappa.KFrontIR.Dump
  ( renderKFrontIRJson
  ) where

import Data.IntMap.Strict qualified as IntMap
import Data.List (sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Kappa.Diagnostic (jArray, jObject, jStr)
import Kappa.KFrontIR.Identity.Internal
import Kappa.KFrontIR.Origin
import Kappa.KFrontIR.Types.Internal
import Kappa.KFrontIR.Verify (verifyKFrontIR)
import Kappa.Source (Pos (..), Span (..))

data DumpNode = DumpNode
  { dnKind :: !Text
  , dnReference :: !SomeFrontNodeId
  , dnOrigin :: !OriginId
  , dnPhase :: !KFrontIRPhase
  , dnSyntax :: !Text
  , dnFacts :: !Text
  }

-- | Canonical machine-readable frontend dump. Arena IDs never appear in the
-- output: occurrence IDs are reassigned by structural path and kind, so
-- allocation strategy and incremental-session reuse cannot change the dump.
-- Verification findings are included rather than preventing emission because
-- §34.2 requires invalid/recovery syntax to remain inspectable.
renderKFrontIRJson :: KFrontIR -> Text
renderKFrontIRJson front =
  jObject
    [ ("schema", jStr "kappa.kfrontir.v1")
    , ("phase", jStr (phaseText (kfHighestPhase front)))
    , ("module", maybe "null" (number . canonicalNodeId nodeIds . SomeModuleNode) (kfModule front))
    , ("nodes", jArray (map (renderNode nodeIds originIds expansionIds front) orderedNodes))
    , ("origins", jArray (map (renderOrigin nodeIds originIds expansionIds front) orderedOrigins))
    , ("expansions", jArray (map (renderExpansion nodeIds originIds expansionIds) orderedExpansions))
    , ("violations", jArray (map jStr (verifyKFrontIR front)))
    ]
  where
    nodesByReference = Map.fromList [(dnReference node, node) | node <- dumpNodes front]
    orderedReferences = canonicalReferences front nodesByReference
    orderedNodes = map (nodesByReference Map.!) orderedReferences
    nodeIds = Map.fromList (zip (map dnReference orderedNodes) [0 :: Int ..])
    orderedExpansions =
      sortOn
        (map (canonicalNodeId nodeIds) . erGeneratedRoots)
        (IntMap.elems (kfExpansions front))
    expansionIds = Map.fromList (zip (map erId orderedExpansions) [0 :: Int ..])
    orderedOrigins = canonicalOrigins front (map dnOrigin orderedNodes)
    originIds = Map.fromList (zip orderedOrigins [0 :: Int ..])

renderNode
  :: Map SomeFrontNodeId Int
  -> Map OriginId Int
  -> Map ExpansionId Int
  -> KFrontIR
  -> DumpNode
  -> Text
renderNode nodeIds originIds _ front node =
  jObject
    [ ("id", number (canonicalNodeId nodeIds (dnReference node)))
    , ("kind", jStr (dnKind node))
    , ("phase", jStr (phaseText (dnPhase node)))
    , ("origin", number (canonicalOriginId originIds (dnOrigin node)))
    , ("children", jArray (map (number . canonicalNodeId nodeIds) (Map.findWithDefault [] (dnReference node) (kfChildren front))))
    , ("syntax", jStr (dnSyntax node))
    , ("facts", jStr (dnFacts node))
    ]

renderExpansion
  :: Map SomeFrontNodeId Int
  -> Map OriginId Int
  -> Map ExpansionId Int
  -> ExpansionRecord
  -> Text
renderExpansion nodeIds originIds expansionIds record =
  jObject
    [ ("id", number (canonicalExpansionId expansionIds (erId record)))
    , ("invocation", number (canonicalNodeId nodeIds (erInvocation record)))
    , ("parentOrigin", number (canonicalOriginId originIds (erParentOrigin record)))
    , ("roots", jArray (map (number . canonicalNodeId nodeIds) (erGeneratedRoots record)))
    ]

renderOrigin
  :: Map SomeFrontNodeId Int
  -> Map OriginId Int
  -> Map ExpansionId Int
  -> KFrontIR
  -> OriginId
  -> Text
renderOrigin nodeIds originIds expansionIds front identity =
  case originLookup identity of
    Nothing -> jObject [("id", originNumber), ("kind", jStr "missing")]
    Just (SourceOrigin span') ->
      jObject [("id", originNumber), ("kind", jStr "source"), ("span", renderSpan span')]
    Just (SyntheticOrigin expansion parent producer role) ->
      jObject
        [ ("id", originNumber)
        , ("kind", jStr "synthetic")
        , ("expansion", number (canonicalExpansionId expansionIds expansion))
        , ("producer", number (canonicalNodeId nodeIds producer))
        , ("role", jStr (T.pack (show role)))
        , ("parent", number (canonicalOriginId originIds parent))
        ]
  where
    originNumber = number (canonicalOriginId originIds identity)
    originLookup (OriginId arena key)
      | arena == kfArena front = IntMap.lookup key (kfOrigins front)
      | otherwise = Nothing

renderSpan :: Span -> Text
renderSpan (Span file (Pos startLine startColumn) (Pos endLine endColumn)) =
  jObject
    [ ("file", jStr (T.pack file))
    , ("start", jArray [number startLine, number startColumn])
    , ("end", jArray [number endLine, number endColumn])
    ]

canonicalNodeId :: Map SomeFrontNodeId Int -> SomeFrontNodeId -> Int
canonicalNodeId identities reference = Map.findWithDefault (-1) reference identities

canonicalExpansionId :: Map ExpansionId Int -> ExpansionId -> Int
canonicalExpansionId identities identity = Map.findWithDefault (-1) identity identities

canonicalOriginId :: Map OriginId Int -> OriginId -> Int
canonicalOriginId identities identity = Map.findWithDefault (-1) identity identities

number :: Show value => value -> Text
number = T.pack . show

phaseText :: KFrontIRPhase -> Text
phaseText = T.toUpper . T.pack . show

dumpNodes :: KFrontIR -> [DumpNode]
dumpNodes front =
  map (\node -> make "module" (SomeModuleNode (fnId node)) node (fnSyntax node) (fnFacts node)) (IntMap.elems (kfModules front))
    ++ map (\node -> make "declaration" (SomeDeclNode (fnId node)) node (fnSyntax node) (fnFacts node)) (IntMap.elems (kfDecls front))
    ++ map (\node -> make "expression" (SomeExprNode (fnId node)) node (fnSyntax node) (fnFacts node)) (IntMap.elems (kfExprs front))
    ++ map (\node -> make "argument" (SomeArgNode (fnId node)) node (fnSyntax node) (fnFacts node)) (IntMap.elems (kfArgs front))
    ++ map (\node -> make "binder" (SomeBinderNode (fnId node)) node (fnSyntax node) (fnFacts node)) (IntMap.elems (kfBinders front))
    ++ map (\node -> make "pattern" (SomePatternNode (fnId node)) node (fnSyntax node) (fnFacts node)) (IntMap.elems (kfPatterns front))
    ++ map (\node -> make "field" (SomeFieldNode (fnId node)) node (fnSyntax node) (fnFacts node)) (IntMap.elems (kfFields front))
    ++ map (\node -> make "import" (SomeImportNode (fnId node)) node (fnSyntax node) (fnFacts node)) (IntMap.elems (kfImports front))
    ++ map (\node -> make "export" (SomeExportNode (fnId node)) node (fnSyntax node) (fnFacts node)) (IntMap.elems (kfExports front))
  where
    make kind reference node syntax facts =
      DumpNode kind reference (fnOrigin node) (fnHighestPhase node) (T.pack (show syntax)) (T.pack (show facts))

canonicalReferences :: KFrontIR -> Map SomeFrontNodeId DumpNode -> [SomeFrontNodeId]
canonicalReferences front nodes = ordered ++ leftovers
  where
    sourceRoots = maybe [] (pure . SomeModuleNode) (kfModule front)
    expansionRecords =
      sortOn
        (\record -> (Map.lookup (erInvocation record) sourceOrdinals, show (map rootSyntax (erGeneratedRoots record))))
        (IntMap.elems (kfExpansions front))
    roots = sourceRoots ++ concatMap erGeneratedRoots expansionRecords
    ordered = walkMany Set.empty roots
    seen = Set.fromList ordered
    leftovers =
      map fst
        ( sortOn
            (\(_, node) -> (dnKind node, dnSyntax node, dnFacts node))
            [entry | entry@(reference, _) <- Map.toList nodes, reference `Set.notMember` seen]
        )
    sourceOrdinals = Map.fromList (zip (walkMany Set.empty sourceRoots) [0 :: Int ..])

    rootSyntax reference = maybe "<missing>" dnSyntax (Map.lookup reference nodes)

    walkMany initial roots' = reverse (go initial roots' [])
      where
        go _ [] ordered' = ordered'
        go visited (reference : rest) ordered'
          | reference `Set.member` visited = go visited rest ordered'
          | otherwise =
              let children = Map.findWithDefault [] reference (kfChildren front)
               in go
                    (Set.insert reference visited)
                    (children ++ rest)
                    (reference : ordered')

canonicalOrigins :: KFrontIR -> [OriginId] -> [OriginId]
canonicalOrigins front roots = reverse (go Set.empty roots []) ++ leftovers
  where
    go _ [] ordered = ordered
    go visited (origin : rest) ordered
      | origin `Set.member` visited = go visited rest ordered
      | otherwise =
          let parents = case origin of
                OriginId arena key
                  | arena == kfArena front -> case IntMap.lookup key (kfOrigins front) of
                      Just (SyntheticOrigin _ parent _ _) -> [parent]
                      _ -> []
                _ -> []
           in go (Set.insert origin visited) (parents ++ rest) (origin : ordered)
    seen = Set.fromList (reverse (go Set.empty roots []))
    leftovers =
      [ OriginId (kfArena front) key
      | key <- IntMap.keys (kfOrigins front)
      , OriginId (kfArena front) key `Set.notMember` seen
      ]
