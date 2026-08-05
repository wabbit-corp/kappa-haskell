{-# LANGUAGE DataKinds #-}

module Kappa.KFrontIR.Origin
  ( SyntheticRole (..)
  , Origin (..)
  , ExpansionRecord (..)
  ) where

import Kappa.KFrontIR.Identity
import Kappa.Source (Span)

data SyntheticRole
  = MacroExpansion
  | Desugaring
  | InsertedCoercion
  | ImplicitPreludeImport
  | ElaboratedSyntax
  | GeneratedObligation
  deriving stock (Eq, Ord, Show)

data Origin
  = SourceOrigin !Span
  | SyntheticOrigin !ExpansionId !OriginId !SomeFrontNodeId !SyntheticRole
  deriving stock (Eq, Ord, Show)

data ExpansionRecord = ExpansionRecord
  { erId :: !ExpansionId
  , erInvocation :: !SomeFrontNodeId
  , erParentOrigin :: !OriginId
  , erGeneratedRoots :: ![SomeFrontNodeId]
  }
  deriving stock (Eq, Ord, Show)
