{-# LANGUAGE DataKinds #-}

module Kappa.KFrontIR.Identity
  ( FrontNodeKind (..)
  , FrontNodeId
  , SomeFrontNodeId (..)
  , frontNodeIdValue
  , OriginId
  , ExpansionId
  , DeclarationSymbolId
  , SelectedBinderId
  , selectedSourceBinder
  , SemanticObjectId
  , ObligationId
  , FrontErrorId
  , CoreNodeId
  ) where

import Kappa.KFrontIR.Identity.Internal

selectedSourceBinder :: FrontNodeId 'BinderNode -> SelectedBinderId
selectedSourceBinder = SelectedSourceBinder
