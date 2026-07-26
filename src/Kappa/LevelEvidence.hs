-- | Explicit universe-proof metadata shared by typed Core checkpoints.
--
-- The checker records authenticated level assumptions on the binder or field
-- that introduces them. Later phases scope and transport that metadata; they
-- never recover proof authority by inspecting a Core term's source shape.
module Kappa.LevelEvidence
  ( coreTypeIsTypeLevel
  , scopeRecordLevelAssumption
  , scopeRecordLevelFields
  ) where

import Data.Bifunctor (bimap)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)

import Kappa.Builtins
  ( prelThis
  , prelTypeLevel
  )
import Kappa.Core
import Kappa.CoreOps (mapTermWithDepth, shiftTerm, zonkTermWith)

-- | Exact typed-Core recognition of the canonical TypeLevel carrier.  Record
-- scope construction uses this before granting a field projection authority
-- to appear in a universe expression.
coreTypeIsTypeLevel :: Term -> Bool
coreTypeIsTypeLevel = \case
  CGlobal global [] -> global == prelTypeLevel
  CUniverseLift _ _ _ inner -> coreTypeIsTypeLevel inner
  CSchemaLift _ _ _ _ _ _ _ _ inner -> coreTypeIsTypeLevel inner
  _ -> False

-- | Replace record-telescope-local field identities by the rigid level locals
-- introduced by the already typed preceding fields. Field names are unique in
-- a checked record telescope, so the field metadata is a semantic binder
-- identity here, not a source-name lookup. Unknown fields remain unchanged and
-- are rejected by the finalized-Core scope validator.
scopeRecordLevelFields :: Int -> Int -> Map Text Int -> Term -> Term
scopeRecordLevelFields outerDepth fieldCount fields =
  zonkTermWith (\_ _ -> Nothing) scopeLevel scopedDepth
    . mapTermWithDepth scopeProjection scopedDepth
    . shiftTerm fieldCount 0
  where
    scopedDepth = outerDepth + fieldCount
    scopeProjection _ = \case
      CProjM _ (CGlobal receiver []) field
        | receiver == prelThis
        , Just level <- Map.lookup field fields -> Just (CLevel (LVar level))
      CProjAtM _ (CGlobal receiver []) field _
        | receiver == prelThis
        , Just level <- Map.lookup field fields -> Just (CLevel (LVar level))
      _ -> Nothing
    scopeLevel = \case
      LField _ field
        | Just level <- Map.lookup field fields -> LVar level
      LSucc level -> levelSucc (scopeLevel level)
      LAdd lhs rhs -> levelAdd (scopeLevel lhs) (scopeLevel rhs)
      LMax lhs rhs -> levelMax (scopeLevel lhs) (scopeLevel rhs)
      LNeutral atom -> LNeutral (mapNeutralLevelAtomLevels scopeLevel atom)
      other -> other

-- | Scope the authenticated assumption metadata of a dependent record field
-- by the same field-identity map used for its type. The metadata and term must
-- move together; otherwise KCoreText could cite a proof whose endpoints still
-- contain an escaped @this.field@ atom.
scopeRecordLevelAssumption :: Map Text Int -> Maybe (Level, Level) -> Maybe (Level, Level)
scopeRecordLevelAssumption fields = fmap (bimap scopeLevel scopeLevel)
  where
    scopeLevel = \case
      LField _ field
        | Just level <- Map.lookup field fields -> LVar level
      LSucc level -> levelSucc (scopeLevel level)
      LAdd lhs rhs -> levelAdd (scopeLevel lhs) (scopeLevel rhs)
      LMax lhs rhs -> levelMax (scopeLevel lhs) (scopeLevel rhs)
      LNeutral atom -> LNeutral (mapNeutralLevelAtomLevels scopeLevel atom)
      other -> other
