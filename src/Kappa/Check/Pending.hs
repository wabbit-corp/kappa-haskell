{-# OPTIONS_GHC -fomit-interface-pragmas #-}

-- | Domain-independent retry snapshots for postponed checker work.
--
-- A failed monotone attempt need not be repeated until one of the semantic
-- dependencies observed by that attempt changes.  The caller owns dependency
-- discovery and versioning; this module only supplies the exact, reusable
-- scheduling primitive.
module Kappa.Check.Pending
  ( DependencySnapshot
  , captureDependencySnapshot
  , dependencySnapshotIsCurrent
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)

newtype DependencySnapshot dependency version =
  DependencySnapshot (Map dependency version)
  deriving stock (Eq, Show)

captureDependencySnapshot
  :: (dependency -> version)
  -> Set dependency
  -> DependencySnapshot dependency version
captureDependencySnapshot versionOf dependencies =
  DependencySnapshot
    (Map.fromSet versionOf dependencies)

dependencySnapshotIsCurrent
  :: Eq version
  => (dependency -> version)
  -> DependencySnapshot dependency version
  -> Bool
dependencySnapshotIsCurrent versionOf (DependencySnapshot versions) =
  Map.foldlWithKey'
    (\current dependency version ->
       current && versionOf dependency == version)
    True
    versions
