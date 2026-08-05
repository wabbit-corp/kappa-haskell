{-# OPTIONS_GHC -fomit-interface-pragmas #-}

-- | Pure declaration-universe projection and Core rewriting.
--
-- During header elaboration a declaration reference carries a provisional
-- universe spine. Principalization can remove positions from that spine, so
-- every stored reference needs the same structural projection. Keeping this
-- pass independent of the checker makes the projection contract reusable and
-- prevents changes to its implementation from rebuilding the elaborator.
module Kappa.UniverseProjection
  ( UniverseReferenceProjection (..)
  , UniverseReferenceProjections (..)
  , deriveUniverseReferenceProjection
  , deriveUniverseReferenceProjectionToLevels
  , uniqueUniverseReferenceProjections
  , rewriteProvisionalUniverseReferences
  ) where

import Control.Applicative ((<|>))
import Control.Monad (guard)
import Data.List (findIndex, nub)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Kappa.Core
import Kappa.CoreOps (mapPatternConstructorUniverses, mapTermWithDepth)
import Kappa.Level
  ( LevelMeta
  , normalizeLevel
  , substituteLevelMetas
  )

-- | A morphism from a provisional source spine to the retained declaration
-- telescope. Retained positions are indices into the source spine.
data UniverseReferenceProjection = UniverseReferenceProjection
  { urpSourceArity :: !Int
  , urpRetainedPositions :: ![Int]
  }
  deriving (Eq, Show)

-- | Global and constructor facets share the 'GName' namespace but can own
-- different schemas. Exact occurrence keys disambiguate distinct provisional
-- spines that happen to have the same arity.
data UniverseReferenceProjections = UniverseReferenceProjections
  { urpGlobals :: !(Map (GName, Int) UniverseReferenceProjection)
  , urpConstructors :: !(Map (GName, Int) UniverseReferenceProjection)
  , urpExactGlobals :: !(Map (GName, [Level]) UniverseReferenceProjection)
  , urpExactConstructors :: !(Map (GName, [Level]) UniverseReferenceProjection)
  }
  deriving (Eq, Show)

deriveUniverseReferenceProjection
  :: Map LevelMeta Level
  -> [LevelMeta]
  -> [LevelMeta]
  -> Maybe UniverseReferenceProjection
deriveUniverseReferenceProjection assignments sourceMetas retainedMetas =
  deriveUniverseReferenceProjectionToLevels
    assignments sourceMetas (map LMeta retainedMetas)

deriveUniverseReferenceProjectionToLevels
  :: Map LevelMeta Level
  -> [LevelMeta]
  -> [Level]
  -> Maybe UniverseReferenceProjection
deriveUniverseReferenceProjectionToLevels assignments sourceMetas retainedLevels = do
  positions <- traverse positionOf retainedLevels
  guard (length positions == length (nub positions))
  pure (UniverseReferenceProjection (length sourceMetas) positions)
  where
    sourceImages =
      [ normalizeLevel (substituteLevelMetas assignments (LMeta sourceMeta))
      | sourceMeta <- sourceMetas
      ]
    positionOf retained =
      findIndex (== normalizeLevel retained) sourceImages

-- | Keep a projection only when every observation for its key derives the
-- same total morphism. Absence is the conservative identity fallback.
uniqueUniverseReferenceProjections
  :: Ord key
  => [(key, Maybe UniverseReferenceProjection)]
  -> Map key UniverseReferenceProjection
uniqueUniverseReferenceProjections alternatives =
  Map.mapMaybe selectProjection
    (Map.fromListWith (++) [(key, [projection]) | (key, projection) <- alternatives])
  where
    selectProjection possibilities =
      case sequence possibilities of
        Just projections -> case nub projections of
          [projection] -> Just projection
          _ -> Nothing
        Nothing -> Nothing

rewriteProvisionalUniverseReferences
  :: UniverseReferenceProjections
  -> Term
  -> Term
rewriteProvisionalUniverseReferences projections term =
  mapPatternConstructorUniverses projectConstructorSpine (walk 0 term)
  where
    walk depth = mapTermWithDepth rewrite depth

    projectConstructorSpine target universes =
      case
          Map.lookup (target, universes) (urpExactConstructors projections)
            <|> Map.lookup (target, length universes) (urpConstructors projections) of
        Just projection
          | length universes == urpSourceArity projection ->
              [universes !! position | position <- urpRetainedPositions projection]
        _ -> universes

    rewrite depth = \case
      CGlobal target universes
        | Just projection <-
            Map.lookup (target, universes) (urpExactGlobals projections)
              <|> Map.lookup (target, length universes) (urpGlobals projections)
        , length universes == urpSourceArity projection ->
            Just
              ( CGlobal target
                  [ universes !! position
                  | position <- urpRetainedPositions projection
                  ]
              )
      CCtorI target universes annotation arguments
        | Just projection <-
            Map.lookup (target, universes) (urpExactConstructors projections)
              <|> Map.lookup (target, length universes) (urpConstructors projections)
        , length universes == urpSourceArity projection ->
            -- 'mapTermWithDepth' is pre-order. Recurse explicitly when this
            -- node is rewritten so nested references are projected too.
            Just
              ( CCtorI target
                  [ universes !! position
                  | position <- urpRetainedPositions projection
                  ]
                  (fmap (walk depth) annotation)
                  [argument {caTerm = walk depth (caTerm argument)} | argument <- arguments]
              )
      _ -> Nothing
