-- | Static observation mode carried independently from quantity, access, and
-- explicitness (Spec SS11.1.2.3B, SS12.1.1, SS30.2.0).
module Kappa.Observation
  ( ObservationMode (..)
  , FormationMode (..)
  ) where

import Data.Data (Data)

data ObservationMode
  = Ordinary
  | Parametric
  deriving stock (Eq, Ord, Show, Data)

-- | Universe-formation policy selected while elaborating a dependent former.
-- This is deliberately not represented by 'ObservationMode': a parametrically
-- observed non-kind domain still forms predicatively.
data FormationMode
  = FormationOrdinary
  | FormationParametric
  deriving stock (Eq, Ord, Show, Data)
