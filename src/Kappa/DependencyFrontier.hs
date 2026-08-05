{-# OPTIONS_GHC -fomit-interface-pragmas #-}

module Kappa.DependencyFrontier
  ( DependencyFrontier
  , emptyDependencyFrontier
  , recordDependencyCompletions
  ) where

import Data.Graph (SCC (..), stronglyConnComp)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

-- | Incremental dependency frontier for completed owners. Each owner is
-- expanded once. Dependencies remain pending until their owner completes;
-- reverse edges make completion proportional to the newly released region.
data DependencyFrontier owner = DependencyFrontier
  { dfOpenDependencies :: !(Map owner (Set owner))
  , dfDependents :: !(Map owner (Set owner))
  }

emptyDependencyFrontier :: DependencyFrontier owner
emptyDependencyFrontier = DependencyFrontier Map.empty Map.empty

-- | Record a batch of completed owners and return every owner released by the
-- event. A batch can contain a mutually recursive component: internal SCC
-- edges are discharged together, while every member waits on the component's
-- aggregate external dependencies. A missing dependency summary is not
-- registered and therefore cannot release its dependents.
recordDependencyCompletions
  :: Ord owner
  => Set owner
  -> (owner -> Maybe (Set owner))
  -> DependencyFrontier owner
  -> (Set owner, DependencyFrontier owner)
recordDependencyCompletions completed dependencies frontier0 =
  let available =
        Map.fromList
          [ (owner, open)
          | owner <- Set.toList completed
          , Just open <- [dependencies owner]
          ]
      availableOwners = Map.keysSet available
      components =
        stronglyConnComp
          [ ( owner
            , owner
            , Set.toList (Set.intersection availableOwners open)
            )
          | (owner, open) <- Map.toList available
          ]
      componentDependencies =
        Map.fromList
          [ (owner, external)
          | component <- components
          , let members = componentMembers component
                external =
                  Set.difference
                    ( Set.unions
                        [ Map.findWithDefault Set.empty member available
                        | member <- Set.toList members
                        ]
                    )
                    members
          , owner <- Set.toList members
          ]
      (ready, frontier1) =
        Map.foldlWithKey' registerOwner (Set.empty, frontier0) componentDependencies
   in drainReady ready Set.empty frontier1
  where
    componentMembers = \case
      AcyclicSCC owner -> Set.singleton owner
      CyclicSCC owners -> Set.fromList owners

    registerOwner (ready, frontier) owner open
      | Set.null open = (Set.insert owner ready, frontier)
      | otherwise =
          let pending' = Map.insert owner open (dfOpenDependencies frontier)
              dependents' =
                Set.foldl'
                  (\dependents dependency ->
                     Map.insertWith Set.union dependency (Set.singleton owner) dependents)
                  (dfDependents frontier)
                  open
           in (ready, DependencyFrontier pending' dependents')

    drainReady ready closed frontier =
      case Set.minView ready of
        Nothing -> (closed, frontier)
        Just (dependency, remainingReady) ->
          let DependencyFrontier pending dependents = frontier
              waiting = Map.findWithDefault Set.empty dependency dependents
              releaseOwner (newlyReady, pendingOwners) owner =
                case Map.lookup owner pendingOwners of
                  Nothing -> (newlyReady, pendingOwners)
                  Just open ->
                    let open' = Set.delete dependency open
                     in if Set.null open'
                          then
                            ( Set.insert owner newlyReady
                            , Map.delete owner pendingOwners
                            )
                          else
                            (newlyReady, Map.insert owner open' pendingOwners)
              (newlyReady, pending') =
                Set.foldl' releaseOwner (Set.empty, pending) waiting
              frontier' =
                DependencyFrontier
                  pending'
                  (Map.delete dependency dependents)
           in drainReady
                (Set.union remainingReady newlyReady)
                (Set.insert dependency closed)
                frontier'
