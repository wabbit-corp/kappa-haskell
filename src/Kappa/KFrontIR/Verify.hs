{-# LANGUAGE DataKinds #-}

module Kappa.KFrontIR.Verify
  ( verifyKFrontIR
  , verifyRawKFrontIR
  ) where

import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.KFrontIR.Identity.Internal
import Kappa.KFrontIR.Origin
import Kappa.KFrontIR.Types.Internal

verifyRawKFrontIR :: KFrontIR -> [Text]
verifyRawKFrontIR front =
  ["RAW KFrontIR advertises a later global phase" | kfHighestPhase front /= Raw]
    ++ verifyKFrontIR front
    ++ rawFactErrors front

verifyKFrontIR :: KFrontIR -> [Text]
verifyKFrontIR front =
  transactionErrors
    ++ moduleErrors
    ++ arenaErrors
    ++ identityErrors
    ++ edgeErrors
    ++ originErrors
    ++ expansionErrors
    ++ phaseErrors
  where
    transactionErrors =
      [ "KFrontIR has an unpublished open phase transaction: " <> T.pack (show phase)
      | phase <- maybe [] pure (kfOpenPhase front)
      ]
    references = allNodeReferences front
    referenceSet = Set.fromList references
    arenaErrors =
      [ "KFrontIR node belongs to another arena: " <> T.pack (show reference)
      | reference <- references
      , frontNodeArena reference /= kfArena front
      ]
        ++ [ "KFrontIR origin belongs to another arena: " <> T.pack (show origin)
           | origin <- allNodeOrigins front
           , originArena origin /= kfArena front
           ]
        ++ [ "KFrontIR expansion belongs to another arena: " <> T.pack (show (erId record))
           | record <- IntMap.elems (kfExpansions front)
           , expansionArena (erId record) /= kfArena front
           ]
    moduleErrors = case kfModule front of
      Nothing -> ["RAW KFrontIR has no module root"]
      Just moduleId ->
        ["RAW KFrontIR module root is dangling" | not (nodeExists front (SomeModuleNode moduleId))]

    identityErrors =
      [ "KFrontIR node identity appears in more than one typed arena: "
          <> T.pack (show duplicate)
      | duplicate <- duplicates (map frontNodeIdValue references)
      ]
        ++ [ "KFrontIR next node identity does not exceed every allocated identity"
           | any (>= kfNextNodeId front) (map frontNodeIdValue references)
           ]

    expansionRoots = Set.fromList (concatMap erGeneratedRoots (IntMap.elems (kfExpansions front)))
    childSets = Map.map Set.fromList (kfChildren front)
    structuralRoots =
      expansionRoots
        <> maybe Set.empty (Set.singleton . SomeModuleNode) (kfModule front)
    edgeErrors =
      [ "KFrontIR child edge has a missing parent: " <> T.pack (show parent)
      | parent <- Map.keys (kfChildren front)
      , parent `Set.notMember` referenceSet
      ]
        ++ [ "KFrontIR child edge has a missing child: " <> T.pack (show child)
           | child <- concat (Map.elems (kfChildren front))
           , child `Set.notMember` referenceSet
           ]
        ++ [ "KFrontIR child and parent indexes disagree for: " <> T.pack (show child)
           | (parent, children) <- Map.toList (kfChildren front)
           , child <- children
           , Map.lookup child (kfParent front) /= Just parent
           ]
        ++ [ "KFrontIR parent index is not represented by a child edge: " <> T.pack (show child)
           | (child, parent) <- Map.toList (kfParent front)
           , child `Set.notMember` Map.findWithDefault Set.empty parent childSets
           ]
        ++ [ "KFrontIR non-root occurrence has no structural parent: " <> T.pack (show reference)
           | reference <- references
           , reference `Set.notMember` structuralRoots
           , Map.notMember reference (kfParent front)
           ]
        ++ [ "KFrontIR structural root unexpectedly has a parent: " <> T.pack (show root)
           | root <- Set.toList structuralRoots
           , Map.member root (kfParent front)
           ]
        ++ ["KFrontIR structural child graph contains a cycle" | childGraphCyclic front]

    originErrors =
      [ "KFrontIR node has a dangling origin: " <> T.pack (show origin)
      | origin <- allNodeOrigins front
      , not (originExists front origin)
      ]
        ++ concatMap validateOrigin (IntMap.toList (kfOrigins front))
        ++ ["KFrontIR synthetic-origin graph contains a cycle" | originGraphCyclic front]

    validateOrigin (_, SourceOrigin _) = []
    validateOrigin (_, SyntheticOrigin expansion parent producer _) =
      ["synthetic origin references a missing expansion" | not (expansionExists front expansion)]
        ++ ["synthetic origin references a missing parent origin" | not (originExists front parent)]
        ++ ["synthetic origin references a missing producer node" | not (nodeExists front producer)]
        ++ case IntMap.lookup (expansionValue expansion) (kfExpansions front) of
          Just record ->
            ["synthetic origin producer disagrees with its expansion record" | producer /= erInvocation record]
              ++ ["synthetic origin parent disagrees with its expansion record" | parent /= erParentOrigin record]
          Nothing -> []

    expansionErrors = concatMap validateExpansion (IntMap.toList (kfExpansions front))
    validateExpansion (key, record) =
      ["expansion arena key disagrees with its typed identity" | key /= expansionValue (erId record)]
        ++ ["expansion invocation is dangling" | not (nodeExists front (erInvocation record))]
        ++ ["expansion parent origin is dangling" | not (originExists front (erParentOrigin record))]
        ++ [ "expansion parent origin is not the invocation origin"
           | nodeOrigin front (erInvocation record) /= Just (erParentOrigin record)
           ]
        ++ ["expansion generated root is dangling" | root <- erGeneratedRoots record, not (nodeExists front root)]
        ++ [ "expansion generated root origin disagrees with its expansion record"
           | root <- erGeneratedRoots record
           , not (rootOriginMatches record root)
           ]

    rootOriginMatches record root =
      case nodeOrigin front root >>= originLookup front of
        Just (SyntheticOrigin expansion parent producer _) ->
          expansion == erId record
            && parent == erParentOrigin record
            && producer == erInvocation record
        _ -> False

    phaseErrors =
      [ "KFrontIR node phase exceeds the published global phase: " <> T.pack (show reference)
      | (reference, phase) <- allNodePhases front
      , phase > kfHighestPhase front
      ]

rawFactErrors :: KFrontIR -> [Text]
rawFactErrors front =
  ["RAW expression contains non-pending semantic facts" | node <- IntMap.elems (kfExprs front), not (rawExprFacts (fnFacts node))]
    ++ ["RAW argument contains non-pending semantic facts" | node <- IntMap.elems (kfArgs front), not (rawArgFacts (fnFacts node))]
    ++ ["RAW declaration contains a semantic symbol" | node <- IntMap.elems (kfDecls front), fnFacts node /= Pending]

rawExprFacts :: ExprFacts -> Bool
rawExprFacts facts =
  efResolvedType facts == Pending
    && efExpectedType facts == Pending
    && efExpectedQuantity facts == Pending
    && efExpressionErasure facts == Pending
    && efExpansion facts == Nothing

rawArgFacts :: ArgFacts -> Bool
rawArgFacts facts =
  afSelectedBinder facts == Pending
    && afExpectedType facts == Pending
    && afExpectedClassifier facts == Pending
    && afDemand facts == Pending
    && afBorrowDemand facts == Pending
    && afErasure facts == Pending

allNodeReferences :: KFrontIR -> [SomeFrontNodeId]
allNodeReferences front =
  map (SomeModuleNode . fnId) (IntMap.elems (kfModules front))
    ++ map (SomeDeclNode . fnId) (IntMap.elems (kfDecls front))
    ++ map (SomeExprNode . fnId) (IntMap.elems (kfExprs front))
    ++ map (SomeArgNode . fnId) (IntMap.elems (kfArgs front))
    ++ map (SomeBinderNode . fnId) (IntMap.elems (kfBinders front))
    ++ map (SomePatternNode . fnId) (IntMap.elems (kfPatterns front))
    ++ map (SomeFieldNode . fnId) (IntMap.elems (kfFields front))
    ++ map (SomeImportNode . fnId) (IntMap.elems (kfImports front))
    ++ map (SomeExportNode . fnId) (IntMap.elems (kfExports front))

allNodeOrigins :: KFrontIR -> [OriginId]
allNodeOrigins front =
  map fnOrigin (IntMap.elems (kfModules front))
    ++ map fnOrigin (IntMap.elems (kfDecls front))
    ++ map fnOrigin (IntMap.elems (kfExprs front))
    ++ map fnOrigin (IntMap.elems (kfArgs front))
    ++ map fnOrigin (IntMap.elems (kfBinders front))
    ++ map fnOrigin (IntMap.elems (kfPatterns front))
    ++ map fnOrigin (IntMap.elems (kfFields front))
    ++ map fnOrigin (IntMap.elems (kfImports front))
    ++ map fnOrigin (IntMap.elems (kfExports front))

allNodePhases :: KFrontIR -> [(SomeFrontNodeId, KFrontIRPhase)]
allNodePhases front =
  map (\node -> (SomeModuleNode (fnId node), fnHighestPhase node)) (IntMap.elems (kfModules front))
    ++ map (\node -> (SomeDeclNode (fnId node), fnHighestPhase node)) (IntMap.elems (kfDecls front))
    ++ map (\node -> (SomeExprNode (fnId node), fnHighestPhase node)) (IntMap.elems (kfExprs front))
    ++ map (\node -> (SomeArgNode (fnId node), fnHighestPhase node)) (IntMap.elems (kfArgs front))
    ++ map (\node -> (SomeBinderNode (fnId node), fnHighestPhase node)) (IntMap.elems (kfBinders front))
    ++ map (\node -> (SomePatternNode (fnId node), fnHighestPhase node)) (IntMap.elems (kfPatterns front))
    ++ map (\node -> (SomeFieldNode (fnId node), fnHighestPhase node)) (IntMap.elems (kfFields front))
    ++ map (\node -> (SomeImportNode (fnId node), fnHighestPhase node)) (IntMap.elems (kfImports front))
    ++ map (\node -> (SomeExportNode (fnId node), fnHighestPhase node)) (IntMap.elems (kfExports front))

nodeExists :: KFrontIR -> SomeFrontNodeId -> Bool
nodeExists front = \case
  SomeModuleNode (FrontNodeId arena key) -> inArena arena && IntMap.member key (kfModules front)
  SomeDeclNode (FrontNodeId arena key) -> inArena arena && IntMap.member key (kfDecls front)
  SomeExprNode (FrontNodeId arena key) -> inArena arena && IntMap.member key (kfExprs front)
  SomeArgNode (FrontNodeId arena key) -> inArena arena && IntMap.member key (kfArgs front)
  SomeBinderNode (FrontNodeId arena key) -> inArena arena && IntMap.member key (kfBinders front)
  SomePatternNode (FrontNodeId arena key) -> inArena arena && IntMap.member key (kfPatterns front)
  SomeFieldNode (FrontNodeId arena key) -> inArena arena && IntMap.member key (kfFields front)
  SomeImportNode (FrontNodeId arena key) -> inArena arena && IntMap.member key (kfImports front)
  SomeExportNode (FrontNodeId arena key) -> inArena arena && IntMap.member key (kfExports front)
  where
    inArena arena = arena == kfArena front

originExists :: KFrontIR -> OriginId -> Bool
originExists front (OriginId arena key) =
  arena == kfArena front && IntMap.member key (kfOrigins front)

originLookup :: KFrontIR -> OriginId -> Maybe Origin
originLookup front (OriginId arena key)
  | arena == kfArena front = IntMap.lookup key (kfOrigins front)
  | otherwise = Nothing

nodeOrigin :: KFrontIR -> SomeFrontNodeId -> Maybe OriginId
nodeOrigin front = \case
  SomeModuleNode (FrontNodeId arena key) -> fnOrigin <$> lookupArena arena (kfModules front) key
  SomeDeclNode (FrontNodeId arena key) -> fnOrigin <$> lookupArena arena (kfDecls front) key
  SomeExprNode (FrontNodeId arena key) -> fnOrigin <$> lookupArena arena (kfExprs front) key
  SomeArgNode (FrontNodeId arena key) -> fnOrigin <$> lookupArena arena (kfArgs front) key
  SomeBinderNode (FrontNodeId arena key) -> fnOrigin <$> lookupArena arena (kfBinders front) key
  SomePatternNode (FrontNodeId arena key) -> fnOrigin <$> lookupArena arena (kfPatterns front) key
  SomeFieldNode (FrontNodeId arena key) -> fnOrigin <$> lookupArena arena (kfFields front) key
  SomeImportNode (FrontNodeId arena key) -> fnOrigin <$> lookupArena arena (kfImports front) key
  SomeExportNode (FrontNodeId arena key) -> fnOrigin <$> lookupArena arena (kfExports front) key
  where
    lookupArena arena nodes key
      | arena == kfArena front = IntMap.lookup key nodes
      | otherwise = Nothing

expansionExists :: KFrontIR -> ExpansionId -> Bool
expansionExists front expansion = IntMap.member (expansionValue expansion) (kfExpansions front)

expansionValue :: ExpansionId -> Int
expansionValue = expansionIdValue

duplicates :: Ord a => [a] -> [a]
duplicates values =
  Set.toList
    (snd
      (foldr
        (\value (seen, repeated) ->
           if value `Set.member` seen
             then (seen, Set.insert value repeated)
             else (Set.insert value seen, repeated))
        (Set.empty, Set.empty)
        values))

originGraphCyclic :: KFrontIR -> Bool
originGraphCyclic front = functionalGraphCyclic parentOf (IntMap.keys (kfOrigins front))
  where
    parentOf key = case IntMap.lookup key (kfOrigins front) of
      Just (SyntheticOrigin _ (OriginId arena parent) _ _)
        | arena == kfArena front -> Just parent
      _ -> Nothing

childGraphCyclic :: KFrontIR -> Bool
childGraphCyclic front =
  functionalGraphCyclic
    (\node -> Map.lookup node (kfParent front))
    (Map.keys (kfParent front))

functionalGraphCyclic :: Ord node => (node -> Maybe node) -> [node] -> Bool
functionalGraphCyclic parentOf = fst . foldl visitRoot (False, Set.empty)
  where
    visitRoot result@(True, _) _ = result
    visitRoot (False, completed) root = visit completed Set.empty root

    visit completed active node
      | node `Set.member` completed = (False, completed)
      | node `Set.member` active = (True, completed)
      | otherwise = case parentOf node of
          Nothing -> (False, Set.insert node completed)
          Just parent ->
            let (cyclic, completed') = visit completed (Set.insert node active) parent
             in (cyclic, Set.insert node completed')
