-- | Canonical semantic tags for variant member types.
module Kappa.TypeTag
  ( semanticTypeTag
  ) where

import Data.Text (Text)
import Kappa.Core
import Kappa.Eval (EvalCtx, force, quote)
import Kappa.Pretty (renderTerm)

-- | Alias-normalize a type throughout before rendering its semantic variant
-- identity. Both source elaboration and KCoreText serialization use this one
-- definition so a tag cannot drift at the checkpoint boundary.
semanticTypeTag :: EvalCtx -> Int -> Value -> Text
semanticTypeTag context depth value =
  renderTerm (quote context depth (deepForceValue context value))

deepForceValue :: EvalCtx -> Value -> Value
deepForceValue context = go (32 :: Int)
  where
    go 0 value = value
    go fuel value = case force context value of
      VGlobI global universes spine ->
        VGlobI global universes [(explicitness, go (fuel - 1) argument) | (explicitness, argument) <- spine]
      VCtorI constructor universes arguments ->
        VCtorI constructor universes
          [ argument {cvaValue = go (fuel - 1) (cvaValue argument)}
          | argument <- arguments
          ]
      VRecordTQ fields -> VRecordTQ (map (fmap (go (fuel - 1))) fields)
      VVariantT members -> VVariantT (map (go (fuel - 1)) members)
      forced -> forced
