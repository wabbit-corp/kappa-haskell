{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Kappa.KFrontIR.Build
  ( FrontBuildError (..)
  , buildRawKFrontIR
  , instantiateExpressionExpansion
  ) where

import Control.Monad.State.Strict
import Data.Data (Data, cast, gmapM, gmapQ)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust, listToMaybe, mapMaybe)
import Kappa.KFrontIR.Identity.Internal
import Kappa.KFrontIR.Origin
import Kappa.KFrontIR.Types.Internal
import Kappa.Source (Pos (..), Span (..))
import Kappa.Syntax

data ImportRole = ImportRole | ExportRole

data OriginPlan
  = SourcePlan
  | SyntheticPlan !ExpansionId !OriginId !SomeFrontNodeId !SyntheticRole

data WalkContext = WalkContext
  { wcImportRole :: !(Maybe ImportRole)
  , wcOriginPlan :: !OriginPlan
  , wcParentNode :: !(Maybe SomeFrontNodeId)
  }

type BuildM = State KFrontIR

data FrontBuildError
  = FrontBuildMissingProducer !SomeFrontNodeId
  | FrontBuildMissingProducerOrigin !OriginId
  | FrontBuildExpansionRootMissing
  deriving stock (Eq, Show)

buildRawKFrontIR :: Module -> KFrontIR
buildRawKFrontIR syntax =
  execState
    (do
       fallback <- allocateOrigin (SourceOrigin unknownSpan)
       root <- walk (WalkContext Nothing SourcePlan Nothing) fallback syntax
       case root of
         Just (SomeModuleNode moduleId) ->
           modify' (\front -> front {kfModule = Just moduleId})
         _ -> pure ())
    (emptyKFrontIR syntax)

instantiateExpressionExpansion
  :: SomeFrontNodeId
  -> SyntheticRole
  -> Expr
  -> KFrontIR
  -> Either FrontBuildError (ExpansionId, FrontNodeId 'ExprNode, KFrontIR)
instantiateExpressionExpansion producer role expression front0 = do
  parentOrigin <- maybe (Left (FrontBuildMissingProducer producer)) Right (nodeOrigin producer front0)
  if not (originExists parentOrigin front0)
    then Left (FrontBuildMissingProducerOrigin parentOrigin)
    else pure ()
  let expansion = ExpansionId (kfArena front0) (kfNextExpansionId front0)
      start = front0 {kfNextExpansionId = kfNextExpansionId front0 + 1}
      (root, front1) =
        runState
          (walk (WalkContext Nothing (SyntheticPlan expansion parentOrigin producer role) Nothing) parentOrigin expression)
          start
  rootId <- case root of
    Just (SomeExprNode expressionId) -> Right expressionId
    _ -> Left FrontBuildExpansionRootMissing
  let record = ExpansionRecord expansion producer parentOrigin [SomeExprNode rootId]
      front2 =
        front1
          { kfExpansions =
              IntMap.insert (unExpansionId expansion) record (kfExpansions front1)
          }
  pure (expansion, rootId, front2)

unExpansionId :: ExpansionId -> Int
unExpansionId = expansionIdValue

walk
  :: forall a
   . Data a
  => WalkContext
  -> OriginId
  -> a
  -> BuildM (Maybe SomeFrontNodeId)
walk context inheritedOrigin value = do
  origin <- originFor context inheritedOrigin value
  reference <- recordRecognized context origin value
  recordParent (wcParentNode context) reference
  let childContext =
        (contextForChildren context value)
          { wcParentNode = case reference of
              Just current -> Just current
              Nothing -> wcParentNode context
          }
  _ <- gmapM (walkChild childContext origin) value
  pure reference
  where
    walkChild
      :: Data child
      => WalkContext
      -> OriginId
      -> child
      -> BuildM child
    walkChild childContext parentOrigin child = do
      _ <- walk childContext parentOrigin child
      pure child

contextForChildren :: Data a => WalkContext -> a -> WalkContext
contextForChildren context value =
  case cast value :: Maybe Decl of
    Just DImport {} -> context {wcImportRole = Just ImportRole}
    Just DExport {} -> context {wcImportRole = Just ExportRole}
    Just _ -> context {wcImportRole = Nothing}
    Nothing -> context

recordParent :: Maybe SomeFrontNodeId -> Maybe SomeFrontNodeId -> BuildM ()
recordParent (Just parent) (Just child) =
  modify'
    (\front ->
       front
         { kfChildren = Map.insertWith (flip (++)) parent [child] (kfChildren front)
         , kfParent = Map.insert child parent (kfParent front)
         })
recordParent _ _ = pure ()

originFor :: Data a => WalkContext -> OriginId -> a -> BuildM OriginId
originFor WalkContext {wcOriginPlan = SourcePlan} inherited value =
  maybe (pure inherited) (allocateOrigin . SourceOrigin) (frontSpan value)
originFor WalkContext {wcOriginPlan = SyntheticPlan expansion parent producer role} _ _ =
  allocateOrigin (SyntheticOrigin expansion parent producer role)

allocateOrigin :: Origin -> BuildM OriginId
allocateOrigin origin = do
  front <- get
  let value = kfNextOriginId front
      identity = OriginId (kfArena front) value
  put
    front
      { kfNextOriginId = value + 1
      , kfOrigins = IntMap.insert value origin (kfOrigins front)
      }
  pure identity

allocateNode :: BuildM Int
allocateNode = do
  front <- get
  let identity = kfNextNodeId front
  put front {kfNextNodeId = identity + 1}
  pure identity

recordRecognized
  :: forall a
   . Data a
  => WalkContext
  -> OriginId
  -> a
  -> BuildM (Maybe SomeFrontNodeId)
recordRecognized context origin value
  | Just syntax <- cast value :: Maybe Module = do
      raw <- allocateNode
      arena <- gets kfArena
      let identity = FrontNodeId arena raw
          node = FrontNode identity origin Raw syntax ()
      modify' (\front -> front {kfModules = IntMap.insert raw node (kfModules front)})
      pure (Just (SomeModuleNode identity))
  | Just syntax <- cast value :: Maybe Decl = do
      raw <- allocateNode
      arena <- gets kfArena
      let identity = FrontNodeId arena raw
          node = FrontNode identity origin Raw syntax Pending
      modify' (\front -> front {kfDecls = IntMap.insert raw node (kfDecls front)})
      pure (Just (SomeDeclNode identity))
  | Just syntax <- cast value :: Maybe Expr = do
      raw <- allocateNode
      arena <- gets kfArena
      let identity = FrontNodeId arena raw
          node = FrontNode identity origin Raw syntax emptyExprFacts
      modify' (\front -> front {kfExprs = IntMap.insert raw node (kfExprs front)})
      pure (Just (SomeExprNode identity))
  | Just syntax <- cast value :: Maybe Arg = do
      raw <- allocateNode
      arena <- gets kfArena
      let identity = FrontNodeId arena raw
          node = FrontNode identity origin Raw syntax emptyArgFacts
      modify' (\front -> front {kfArgs = IntMap.insert raw node (kfArgs front)})
      pure (Just (SomeArgNode identity))
  | Just syntax <- cast value :: Maybe Binder = do
      raw <- allocateNode
      arena <- gets kfArena
      let identity = FrontNodeId arena raw
          node = FrontNode identity origin Raw syntax ()
      modify' (\front -> front {kfBinders = IntMap.insert raw node (kfBinders front)})
      pure (Just (SomeBinderNode identity))
  | Just syntax <- cast value :: Maybe Pattern = do
      raw <- allocateNode
      arena <- gets kfArena
      let identity = FrontNodeId arena raw
          node = FrontNode identity origin Raw syntax ()
      modify' (\front -> front {kfPatterns = IntMap.insert raw node (kfPatterns front)})
      pure (Just (SomePatternNode identity))
  | Just syntax <- FrontRecordValueField <$> (cast value :: Maybe RecItem) =
      recordField origin syntax
  | Just syntax <- FrontRecordTypeField <$> (cast value :: Maybe RecTypeField) =
      recordField origin syntax
  | Just syntax <- FrontPatchField <$> (cast value :: Maybe PatchItem) =
      recordField origin syntax
  | Just syntax <- FrontImportSpec <$> (cast value :: Maybe ImportSpec) =
      recordImport context origin syntax
  | Just syntax <- FrontImportItem <$> (cast value :: Maybe ImportItem) =
      recordImport context origin syntax
  | Just syntax <- FrontExceptItem <$> (cast value :: Maybe ExceptItem) =
      recordImport context origin syntax
  | otherwise = pure Nothing

recordField :: OriginId -> FrontFieldSyntax -> BuildM (Maybe SomeFrontNodeId)
recordField origin syntax = do
  raw <- allocateNode
  arena <- gets kfArena
  let identity = FrontNodeId arena raw
      node = FrontNode identity origin Raw syntax ()
  modify' (\front -> front {kfFields = IntMap.insert raw node (kfFields front)})
  pure (Just (SomeFieldNode identity))

recordImport
  :: WalkContext
  -> OriginId
  -> FrontImportSyntax
  -> BuildM (Maybe SomeFrontNodeId)
recordImport context origin syntax = do
  raw <- allocateNode
  arena <- gets kfArena
  case wcImportRole context of
    Just ExportRole -> do
      let identity = FrontNodeId arena raw
          node = FrontNode identity origin Raw syntax ()
      modify' (\front -> front {kfExports = IntMap.insert raw node (kfExports front)})
      pure (Just (SomeExportNode identity))
    _ -> do
      let identity = FrontNodeId arena raw
          node = FrontNode identity origin Raw syntax ()
      modify' (\front -> front {kfImports = IntMap.insert raw node (kfImports front)})
      pure (Just (SomeImportNode identity))

frontSpan :: Data a => a -> Maybe Span
frontSpan value
  | Just expression <- cast value = Just (exprSpan expression)
  | Just argument <- cast value = Just (argumentSpan argument)
  | Just binder <- cast value = Just (bSpan binder)
  | Just pattern' <- cast value = Just (patternSpan pattern')
  | Just declaration <- cast value = Just (declarationSpan declaration)
  | Just field <- cast value :: Maybe RecItem = Just (nameSpan (riName field))
  | Just field <- cast value :: Maybe RecTypeField = Just (nameSpan (rtfName field))
  | Just item <- cast value :: Maybe ImportItem = Just (nameSpan (iiName item))
  | Just (ExceptItem _ name) <- cast value = Just (nameSpan name)
  | recognizedFrontValue value = shallowSpan value
  | otherwise = Nothing

-- Keep source origins one-for-one with indexed occurrences. Generic children
-- often contain inherited 'Span' fields but are not KFrontIR nodes; allocating
-- origins for them creates unreachable, allocation-order-sensitive entries.
recognizedFrontValue :: Data a => a -> Bool
recognizedFrontValue value =
  or
    [ isJust (cast value :: Maybe Module)
    , isJust (cast value :: Maybe Decl)
    , isJust (cast value :: Maybe Expr)
    , isJust (cast value :: Maybe Arg)
    , isJust (cast value :: Maybe Binder)
    , isJust (cast value :: Maybe Pattern)
    , isJust (cast value :: Maybe RecItem)
    , isJust (cast value :: Maybe RecTypeField)
    , isJust (cast value :: Maybe PatchItem)
    , isJust (cast value :: Maybe ImportSpec)
    , isJust (cast value :: Maybe ImportItem)
    , isJust (cast value :: Maybe ExceptItem)
    ]

argumentSpan :: Arg -> Span
argumentSpan = \case
  ArgExplicit expression -> exprSpan expression
  ArgImplicit expression -> exprSpan expression
  ArgNamedBlock _ span' -> span'
  ArgInout _ span' -> span'

declarationSpan :: Decl -> Span
declarationSpan = \case
  DSig _ _ _ span' -> span'
  DLet _ _ span' -> span'
  DData _ _ span' -> span'
  DTypeAlias _ _ _ _ _ span' -> span'
  DTrait _ _ span' -> span'
  DInstance _ span' -> span'
  DDerive _ span' -> span'
  DEffect _ _ span' -> span'
  DFixity _ span' -> span'
  DImport _ span' -> span'
  DExport _ span' -> span'
  DExpect _ _ span' -> span'
  DPattern _ _ span' -> span'
  DProjection _ _ _ _ _ span' -> span'
  DTopSplice _ span' -> span'
  DUnsafeAssert _ _ span' -> span'

shallowSpan :: Data a => a -> Maybe Span
shallowSpan value =
  listToMaybe (mapMaybe id (gmapQ (\child -> cast child :: Maybe Span) value))

unknownSpan :: Span
unknownSpan = Span "<kfrontir>" (Pos 1 1) (Pos 1 1)

nodeExists :: SomeFrontNodeId -> KFrontIR -> Bool
nodeExists reference front = case reference of
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

nodeOrigin :: SomeFrontNodeId -> KFrontIR -> Maybe OriginId
nodeOrigin reference front = case reference of
  SomeModuleNode (FrontNodeId arena key) -> fnOrigin <$> inArena arena (IntMap.lookup key (kfModules front))
  SomeDeclNode (FrontNodeId arena key) -> fnOrigin <$> inArena arena (IntMap.lookup key (kfDecls front))
  SomeExprNode (FrontNodeId arena key) -> fnOrigin <$> inArena arena (IntMap.lookup key (kfExprs front))
  SomeArgNode (FrontNodeId arena key) -> fnOrigin <$> inArena arena (IntMap.lookup key (kfArgs front))
  SomeBinderNode (FrontNodeId arena key) -> fnOrigin <$> inArena arena (IntMap.lookup key (kfBinders front))
  SomePatternNode (FrontNodeId arena key) -> fnOrigin <$> inArena arena (IntMap.lookup key (kfPatterns front))
  SomeFieldNode (FrontNodeId arena key) -> fnOrigin <$> inArena arena (IntMap.lookup key (kfFields front))
  SomeImportNode (FrontNodeId arena key) -> fnOrigin <$> inArena arena (IntMap.lookup key (kfImports front))
  SomeExportNode (FrontNodeId arena key) -> fnOrigin <$> inArena arena (IntMap.lookup key (kfExports front))
  where
    inArena arena value
      | arena == kfArena front = value
      | otherwise = Nothing

originExists :: OriginId -> KFrontIR -> Bool
originExists (OriginId arena key) front =
  arena == kfArena front && IntMap.member key (kfOrigins front)
