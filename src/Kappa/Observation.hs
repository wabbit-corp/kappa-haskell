-- | Static observation mode carried independently from quantity, access, and
-- explicitness (Spec SS11.1.2.3B, SS12.1.1, SS30.2.0).
module Kappa.Observation
  ( ObservationMode (..)
  , FormationMode (..)
  , observationModeSubsumes
  ) where

import Data.Data (Data)

data ObservationMode
  = Ordinary
  | Parametric
  deriving stock (Eq, Ord, Show, Data)

-- | Outer-Pi observation-mode subsumption (Spec SS12.1.1, SS30.2.0).
-- A parametrically observing function accepts every ordinary argument that
-- an ordinary-observing contract permits. The converse would allow a caller
-- to pass a parametrically dependent value to an ordinary-only function.
-- This relation is a checking rule, not definitional equality.
observationModeSubsumes :: ObservationMode -> ObservationMode -> Bool
observationModeSubsumes actual expected =
  actual == expected || (actual == Parametric && expected == Ordinary)

-- | Universe-formation policy selected while elaborating a dependent former.
-- This is deliberately not represented by 'ObservationMode': a parametrically
-- observed non-kind domain still forms predicatively.
data FormationMode
  = FormationOrdinary
  | FormationParametric
  deriving stock (Eq, Ord, Show, Data)
