{-# LANGUAGE DataKinds #-}

module Kappa.KFrontIR.Phase
  ( FrontPhaseError (..)
  , beginFrontIRPhase
  , publishFrontIRPhase
  , advanceFrontIR
  , requireFrontIRPhase
  , requireFrontIRWritePhase
  ) where

import Data.IntMap.Strict qualified as IntMap
import Kappa.KFrontIR.Types.Internal

data FrontPhaseError
  = FrontPhaseRegression !KFrontIRPhase !KFrontIRPhase
  | FrontPhaseUnavailable !KFrontIRPhase !KFrontIRPhase
  | FrontPhaseAlreadyOpen !KFrontIRPhase
  | FrontPhaseNotOpen !KFrontIRPhase
  | FrontPhaseOpenMismatch !KFrontIRPhase !KFrontIRPhase
  | FrontPhaseIncomplete !KFrontIRPhase ![String]
  deriving stock (Eq, Show)

-- | Open an immutable phase transaction. Fact writers may only write facts
-- owned by the open phase; the globally visible checkpoint is unchanged.
beginFrontIRPhase :: KFrontIRPhase -> KFrontIR -> Either FrontPhaseError KFrontIR
beginFrontIRPhase requested front
  | Just open <- kfOpenPhase front = Left (FrontPhaseAlreadyOpen open)
  | requested <= current = Left (FrontPhaseRegression current requested)
  | otherwise = Right front {kfOpenPhase = Just requested}
  where
    current = kfHighestPhase front

-- | Publish an open phase only after every fact required at that checkpoint
-- is terminal. Fused implementations may skip internal phases, but may not
-- advertise a partially populated artifact.
publishFrontIRPhase :: KFrontIRPhase -> KFrontIR -> Either FrontPhaseError KFrontIR
publishFrontIRPhase requested front =
  case kfOpenPhase front of
    Nothing -> Left (FrontPhaseNotOpen requested)
    Just open
      | open /= requested -> Left (FrontPhaseOpenMismatch open requested)
      | not (null missing) -> Left (FrontPhaseIncomplete requested missing)
      | otherwise ->
          Right
            (advanceAllNodes requested front)
              { kfHighestPhase = requested
              , kfOpenPhase = Nothing
              }
  where
    missing = incompleteFacts requested front

-- | Convenience for a phase with no facts to populate. A fact-owning phase
-- fails closed here because beginning and immediately publishing it leaves
-- mandatory facts pending.
advanceFrontIR :: KFrontIRPhase -> KFrontIR -> Either FrontPhaseError KFrontIR
advanceFrontIR requested front =
  beginFrontIRPhase requested front >>= publishFrontIRPhase requested

requireFrontIRPhase :: KFrontIRPhase -> KFrontIR -> Either FrontPhaseError ()
requireFrontIRPhase required front
  | kfHighestPhase front < required =
      Left (FrontPhaseUnavailable (kfHighestPhase front) required)
  | otherwise = Right ()

requireFrontIRWritePhase :: KFrontIRPhase -> KFrontIR -> Either FrontPhaseError ()
requireFrontIRWritePhase required front =
  case kfOpenPhase front of
    Nothing -> Left (FrontPhaseNotOpen required)
    Just open
      | open < required -> Left (FrontPhaseUnavailable open required)
      | otherwise -> Right ()

incompleteFacts :: KFrontIRPhase -> KFrontIR -> [String]
incompleteFacts phase front =
  declarationFacts ++ expressionFacts ++ argumentFacts
  where
    declarationFacts
      | phase < DeclarationShapes = []
      | otherwise =
          [ "declaration " <> show (fnId node) <> " has no terminal symbol resolution"
          | node <- IntMap.elems (kfDecls front)
          , not (terminal (fnFacts node))
          ]
    expressionFacts
      | phase < BodyResolve = []
      | otherwise = concatMap missingExpr (IntMap.elems (kfExprs front))
    argumentFacts
      | phase < BodyResolve = []
      | otherwise = concatMap missingArg (IntMap.elems (kfArgs front))

    missingExpr node =
      [ "expression " <> show (fnId node) <> " has pending " <> label
      | (label, complete) <-
          [ ("resolved type", terminal (efResolvedType facts))
          , ("expected type", terminal (efExpectedType facts))
          , ("expected quantity", terminal (efExpectedQuantity facts))
          , ("runtime erasure", terminal (efExpressionErasure facts))
          ]
      , not complete
      ]
      where
        facts = fnFacts node

    missingArg node =
      [ "argument " <> show (fnId node) <> " has pending " <> label
      | (label, complete) <-
          [ ("selected binder", terminal (afSelectedBinder facts))
          , ("expected type", terminal (afExpectedType facts))
          , ("expected classifier", terminal (afExpectedClassifier facts))
          , ("demand", terminal (afDemand facts))
          , ("borrow demand", terminal (afBorrowDemand facts))
          , ("runtime erasure", terminal (afErasure facts))
          ]
      , not complete
      ]
      where
        facts = fnFacts node

terminal :: Resolution a -> Bool
terminal Pending = False
terminal _ = True

advanceAllNodes :: KFrontIRPhase -> KFrontIR -> KFrontIR
advanceAllNodes phase front =
  front
    { kfModules = fmap advance (kfModules front)
    , kfDecls = fmap advance (kfDecls front)
    , kfExprs = fmap advance (kfExprs front)
    , kfArgs = fmap advance (kfArgs front)
    , kfBinders = fmap advance (kfBinders front)
    , kfPatterns = fmap advance (kfPatterns front)
    , kfFields = fmap advance (kfFields front)
    , kfImports = fmap advance (kfImports front)
    , kfExports = fmap advance (kfExports front)
    }
  where
    advance node = node {fnHighestPhase = phase}
