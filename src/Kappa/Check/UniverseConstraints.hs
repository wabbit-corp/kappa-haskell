-- | Owner-indexed operations for incremental universe-constraint closeout.
--
-- This module is intentionally independent of checker state. The checker owns
-- the authority maps; these operations preserve authoritative list order while
-- limiting an incremental rewrite to explicitly selected identities.
module Kappa.Check.UniverseConstraints
  ( constraintIdsForOwners
  , constraintIdsForOwnersAndOccurrences
  , rewriteSelectedConstraints
  ) where

import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Kappa.Core (GName)
import Kappa.Level (LevelConstraint (lcIdentity))

constraintIdsForOwners
  :: Map.Map GName [LevelConstraint]
  -> Set GName
  -> Set Int
constraintIdsForOwners constraintsByOwner owners =
  Set.fromList
    [ lcIdentity constraint
    | owner <- Set.toAscList owners
    , constraint <- Map.findWithDefault [] owner constraintsByOwner
    ]

-- | Closeout owns both declaration-bucket constraints and constraints copied
-- for exact provisional occurrences. The latter remain selectable even when
-- their consumer has no active declaration owner.
constraintIdsForOwnersAndOccurrences
  :: Map.Map GName [LevelConstraint]
  -> Set GName
  -> [Set Int]
  -> Set Int
constraintIdsForOwnersAndOccurrences constraintsByOwner owners occurrenceIds =
  Set.unions (constraintIdsForOwners constraintsByOwner owners : occurrenceIds)

-- | Rewrite selected constraints without rebuilding or reordering unrelated
-- entries. Returning 'Nothing' retires a selected constraint; unselected
-- constraints are retained exactly as supplied.
rewriteSelectedConstraints
  :: Set Int
  -> (LevelConstraint -> Maybe LevelConstraint)
  -> [LevelConstraint]
  -> [LevelConstraint]
rewriteSelectedConstraints selected rewrite = foldr step []
  where
    step constraint rest
      | lcIdentity constraint `Set.member` selected =
          maybe rest (: rest) (rewrite constraint)
      | otherwise = constraint : rest
