module Kappa.KFrontIR.Types
  ( KFrontIRPhase (..)
  , Resolution (..)
  , FrontNode
  , fnId
  , fnOrigin
  , fnHighestPhase
  , fnSyntax
  , fnFacts
  , FrontFieldSyntax
  , FrontImportSyntax
  , ExprFacts
  , efResolvedType
  , efExpectedType
  , efExpectedQuantity
  , efExpressionErasure
  , efExpansion
  , ArgFacts
  , afSelectedBinder
  , afExpectedType
  , afExpectedClassifier
  , afDemand
  , afBorrowDemand
  , afErasure
  , KFrontIR
  ) where

import Kappa.KFrontIR.Types.Internal
