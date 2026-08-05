-- | Deterministic directed-graph indexing shared by compiler solvers.
-- Callers often receive an edge stream, but repeated adjacency scans turn a
-- nominally linear graph algorithm into O(V*E). Build the index once and keep
-- traversal proportional to the represented graph.
module Kappa.DirectedGraph
  ( DirectedGraph
  , fromEdges
  , reachable
  , reachableFrom
  , stronglyConnectedComponents
  ) where

import Data.Graph (SCC (..), stronglyConnComp)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

newtype DirectedGraph vertex = DirectedGraph (Map vertex (Set vertex))

fromEdges :: Ord vertex => [(vertex, vertex)] -> DirectedGraph vertex
fromEdges edges =
  DirectedGraph
    ( Map.unionWith
        Set.union
        (Map.fromListWith Set.union [(source, Set.singleton target) | (source, target) <- edges])
        (Map.fromSet (const Set.empty) targets)
    )
  where
    targets = Set.fromList [target | (_, target) <- edges]

reachable :: Ord vertex => DirectedGraph vertex -> vertex -> vertex -> Bool
reachable (DirectedGraph adjacency) source target = go Set.empty [source]
  where
    go _ [] = False
    go seen (current : rest)
      | current == target = True
      | current `Set.member` seen = go seen rest
      | otherwise =
          go
            (Set.insert current seen)
            (Set.toAscList (Map.findWithDefault Set.empty current adjacency) ++ rest)

-- | The reflexive reachability closure of a set of roots. Each represented
-- edge is followed at most once after its source enters the visited set. Roots
-- absent from the graph remain in the result, which is useful for dependency
-- closures whose initial authorities need not have outgoing edges.
reachableFrom :: Ord vertex => DirectedGraph vertex -> Set vertex -> Set vertex
reachableFrom (DirectedGraph adjacency) roots = go Set.empty roots
  where
    go visited pending
      | Set.null pending = visited
      | otherwise =
          let (current, pendingWithoutCurrent) = Set.deleteFindMin pending
           in if current `Set.member` visited
                then go visited pendingWithoutCurrent
                else
                  go
                    (Set.insert current visited)
                    ( Set.union
                        pendingWithoutCurrent
                        (Map.findWithDefault Set.empty current adjacency)
                    )

stronglyConnectedComponents :: Ord vertex => DirectedGraph vertex -> [[vertex]]
stronglyConnectedComponents (DirectedGraph adjacency) =
  map members
    ( stronglyConnComp
        [ (vertex, vertex, Set.toAscList successors)
        | (vertex, successors) <- Map.toAscList adjacency
        ]
    )
  where
    members = \case
      AcyclicSCC vertex -> [vertex]
      CyclicSCC vertices -> Set.toAscList (Set.fromList vertices)
