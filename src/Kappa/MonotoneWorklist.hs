{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -fomit-interface-pragmas #-}

-- | A small, domain-independent dependency worklist.
--
-- Callers provide a monotone transfer function and a reverse dependency map:
-- when a key changes, only the keys listed as its dependents are reconsidered.
-- The explicit step budget turns a broken monotonicity/termination invariant
-- into a fail-closed result instead of an unbounded compiler pass.
module Kappa.MonotoneWorklist
  ( WorklistResult (..)
  , stabilizeWorklist
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

data WorklistResult key state
  = WorklistConverged !state
  | WorklistExhausted !(Set key) !state
  deriving stock (Eq, Show)

-- | Stabilize @initialKeys@ under @step@. The dependency map is in the
-- invalidation direction: @dependents Map.! changed@ contains the keys whose
-- transfer result may depend on @changed@. Duplicate invalidations coalesce in
-- the pending set.
stabilizeWorklist
  :: Ord key
  => Int
  -> Map key (Set key)
  -> (key -> state -> (Bool, state))
  -> Set key
  -> state
  -> WorklistResult key state
stabilizeWorklist stepBudget dependents step = go (max 0 stepBudget)
  where
    go !remaining !pending !current
      | Set.null pending = WorklistConverged current
      | remaining == 0 = WorklistExhausted pending current
      | otherwise =
          let (key, pendingWithoutKey) = Set.deleteFindMin pending
              !(changed, next) = step key current
              invalidated =
                if changed
                  then Map.findWithDefault Set.empty key dependents
                  else Set.empty
           in next `seq`
                go
                  (remaining - 1)
                  (Set.union pendingWithoutKey invalidated)
                  next
