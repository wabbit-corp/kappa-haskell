-- | Derivation-shape reflection (Spec §22).
--
-- Reading the shape of a declaration so a @derive@ obligation can be
-- discharged against it.
--
-- Carved out of "Kappa.Check" as part of splitting that module; see
-- "Kappa.Check.Types" for the shared data dictionary and docs\/CONCEPTS.md
-- for the vocabulary these assume.
module Kappa.Check.Derive
  ( gShape
  , listValue
  , shapeCtorInfo
  , shapeFamily
  , shapeInspectAdtOp
  , shapeInspectRecordOp
  , valueList
  ) where

import Control.Applicative ((<|>))
import Control.Monad (filterM, foldM, forM, forM_, guard, replicateM, unless, void, when, zipWithM)
import Control.Monad.State.Strict
import Data.Char (isLower)
import Data.Data (Data, cast, gmapQ)
import Data.Graph (SCC (..), stronglyConnComp)
import Data.List (elemIndex, find, intersect, nub, nubBy, sort, sortOn, zip4, (\\))
import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, isJust, isNothing, listToMaybe, mapMaybe, maybeToList)
import Data.Monoid (Any (..))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Stack (HasCallStack, callStack, prettyCallStack)
import Numeric.Natural (Natural)
import Kappa.Builtins
import Kappa.Cardinality
  ( CardConstraint (..)
  , CardExpr (..)
  , cardAdd
  , cardGuardedSub
  , cardIf
  , cardIndex
  , cardLiteral
  , cardMul
  , normalizeCardExpr
  )
import Kappa.Arithmetic
  ( AFormula (..)
  , ArithmeticSemantics (..)
  , PrimitiveComparisonDomain (..)
  , decodePrimitiveComparisonOperandM
  , deriveArithmeticFormulaReplayWithAssumptions
  , derivePrincipalAffineSubstitution
  , formulaAssumptionFacts
  )
import Kappa.Check.Patch
import Kappa.Check.Pending
  ( captureDependencySnapshot
  , dependencySnapshotIsCurrent
  )
import Kappa.Check.Arith
import Kappa.Check.Totality
import Kappa.Check.Types
import Kappa.Check.UniverseConstraints
  ( constraintIdsForOwnersAndOccurrences
  , rewriteSelectedConstraints
  )
import Kappa.Check.Support
import Kappa.Core
import Kappa.CoreOps
  ( declarationUniverseConstraintBinder
  , declarationUniverseConstraints
  , dedupeUniverseConstraints
  , equivalentUniverseConstraint
  , foldTerm
  , foldTermWithDepth
  , coreToNeutralLevelTerm
  , mentionsGlobal
  , globalsOfTerm
  , mapSchemaRoleEvidence
  , mapPatternConstructorUniverses
  , mapTermWithDepth
  , plainPatternBinder
  , eraseObserveOnlyAnnotations
  , levelMetasOfTerm
  , levelParamsOfTerm
  , roleLevelParamsOfTerm
  , maxFreeIndexTerm
  , metaIdsOf
  , metaOccursInTermShallow
  , metaOccursInTermShallowFuel
  , patBindersC
  , CorePatternDecision (..)
  , instantiateEtaConstructor
  , instantiateCorePatternBody
  , matchCorePattern
  , projectionDepsOf
  , shiftTerm
  , weakenTermUnderBinderAt
  , specializeTraitMemberProjectionType
  , spineOfTerm
  , substGlobal
  , substTopTermAt
  , termClosed
  , termScopedAt
  , zonkTermWith
  )
import qualified Kappa.Backend.Repr as Repr
import Kappa.DependencyFrontier
  ( emptyDependencyFrontier
  , recordDependencyCompletions
  )
import qualified Kappa.DirectedGraph as DirectedGraph
import Kappa.Diagnostic
import Kappa.Eval
import Kappa.Inhabitance
  ( InhabEnv (..)
  , InhabitanceSummary (Empty, Contractible, Finite, Unknown)
  , InhabitancePurpose (..)
  , HeadClass (..)
  , CtorFiber (..)
  , inhabitanceSummary
  , isEmpty
  , multiplySummaries
  , symbolicCardinality
  )
import Kappa.Level
  ( Assumptions
  , ConstraintOrigin (..)
  , LevelMeta
  , LevelConstraint (..)
  , LevelAssignmentGraphError (..)
  , LevelSolveError (..)
  , LevelSolution (..)
  , PrincipalInferenceOutcome (..)
  , PrincipalNonLeastWitness (..)
  , SolveResult (..)
  , assumptionsConsistent
  , assumptionsList
  , classifyAssumptions
  , abstractLocalLevelParams
  , compareClosedLevel
  , emptyLevelAssignmentGraphBudget
  , emptyAssumptions
  , insertAssumption
  , instantiateLocalLevelParams
  , levelVars
  , levelFields
  , levelParams
  , normalizeLevel
  , proveLevelEq
  , proveLevelLeq
  , renderLevel
  , inferPrincipalLevelsFor
  , extendLevelAssignmentGraphWithBudget
  , solveLevelConstraints
  , solveLevelConstraintsFor
  , uniquelyDeterminedLevelAssignmentsFor
  , substituteLevelConstraintMetas
  , substituteLevelMetas
  , substituteLevelParams
  , levelMetas
  , neutralLevelTermLevels
  )
import Kappa.LevelEvidence (validateUniverseEvidenceRelationUnder)
import Kappa.Observation (observationModeSubsumes)
import Kappa.MonotoneWorklist
  ( WorklistResult (..)
  , stabilizeWorklist
  )
import Kappa.UniverseProjection
  ( UniverseReferenceProjection (..)
  , UniverseReferenceProjections (..)
  , deriveUniverseReferenceProjection
  , deriveUniverseReferenceProjectionToLevels
  , rewriteProvisionalUniverseReferences
  , uniqueUniverseReferenceProjections
  )
import Kappa.NominalVariance
import Kappa.ObservationDeps
  ( DependencySet
  , ObservationBinding (..)
  , ObservationOracle (..)
  , ParametricOrigin (..)
  , classifierRelativeDependencies
  , constructorPatternObservationSites
  , dependencyIsAnalysisFailure
  , dependenciesMode
  , evidenceRelativeCallableDependencies
  , isParametricKindValue
  , observationDependencies
  )
import Kappa.Pretty (renderTerm)
import Kappa.Parser (parseExprText)
import Kappa.Representation
import Kappa.Source
import Kappa.Syntax hiding (CompClause (..), Quantity (..))
import qualified Kappa.Syntax as S
import Kappa.Termination hiding (expandedGlobalsOfTerm)
import qualified Kappa.Termination as Termination
import Kappa.TypeTag (semanticTypeTag)
import Kappa.SyntaxOps
  ( boundNamesIn
  , collectSplices
  , freeVarOccurrences
  , freeVarOccurrencesScoped
  , renameFreeVarOccurrences
  , renameVarOccurrences
  , renderExprSrc
  , replaceSplices
  , substQuoteHoles
  )
import Kappa.SurfaceValidation (quantityBorrowMarkerSpans)
import Kappa.Token (QuotedLit (..), StrFragment (..), StringLit (..))
import Kappa.Unicode (isSingleGrapheme)
import Kappa.Usage (tailResumptiveClause)

gShape :: Text -> GName
gShape = GName shapeModule

shapeFamily :: Maybe DiagnosticFamily
shapeFamily = Just "kappa.deriving.shape"

listValue :: [Value] -> Value
listValue = foldr (\x t -> VCtor prelCons [x, t]) (VCtor prelNil [])

valueList :: Value -> CheckM [Value]
valueList v = do
  vF <- forceRT v
  case vF of
    VCtor (GName _ "::") [h, t] -> (h :) <$> valueList t
    _ -> pure []

shapeFieldValue :: Maybe Text -> Int -> Value
shapeFieldValue mname i =
  VCtor
    (gShape "ShapeField")
    [ maybe (VCtor prelNone []) (\n -> VCtor prelSome [VLit (LitStr n)]) mname
    , VLit (LitStr renderName)
    ]
  where
    renderName = fromMaybe ("_" <> T.pack (show (i + 1))) mname

-- | The §22.1 constructor summaries of a data type.
shapeCtorValues :: GName -> CheckM [Value]
shapeCtorValues g = do
  st <- get
  let ctorGs = maybe [] diCtors (Map.lookup g (csDatas st))
  pure
    [ VCtor
        (gShape "ShapeConstructor")
        [ VLit (LitStr (gnameText cg))
        , VLit (LitStr (gnameText cg))
        , VLit (LitInt (fromIntegral tag))
        , listValue
            [ shapeFieldValue mname i
            | (i, (mname, _)) <- zip [0 ..] (maybe [] ciFields (Map.lookup cg (csCtors st)))
            ]
        ]
    | (tag, cg) <- zip [0 :: Int ..] ctorGs
    ]

-- | §22.1 'inspectAdt': the inspected head must be a data type whose
-- representation is visible at this elaboration site.
shapeInspectAdtOp :: Ctx -> Span -> Value -> CheckM (Either () Value)
shapeInspectAdtOp _ctx sp tyV = do
  t <- forceRT tyV
  st <- get
  case t of
    VGlobN g _
      | Just di <- Map.lookup g (csDatas st) -> do
          let GName declMod _ = g
              opaque = Map.member g (csOpaqueDatas st)
          if opaque && declMod /= csModule st
            then do
              errAt sp "KAPPA_DERIVING_SHAPE_OPAQUE_REPRESENTATION" shapeFamily
                ("the representation of '" <> gnameText g
                   <> "' is opaque outside its defining module; shape inspection requires a representation ordinary code at this site could match on (§22.1)")
              pure (Left ())
            else do
              ctorVs <- shapeCtorValues g
              st' <- get
              let ctorGs = diCtors di
                  fieldCounts =
                    [maybe 0 (length . ciFields) (Map.lookup cg (csCtors st')) | cg <- ctorGs]
                  kindName
                    | length ctorGs == 1 = "ProductAdt"
                    | all (== 0) fieldCounts = "EnumAdt"
                    | otherwise = "SumAdt"
              pure $
                Right $
                  VCtor
                    (gShape "AdtShape")
                    [ VLit (LitStr (gnameText g))
                    , VLit (LitStr (gnameText g))
                    , VCtor (gShape "ShapeRepresentationVisible") []
                    , VCtor (gShape kindName) []
                    , listValue ctorVs
                    ]
    _ -> do
      tT <- quoteIn emptyCtx t
      errAt sp "KAPPA_DERIVING_SHAPE_NOT_DATA" shapeFamily
        ("shape inspection requires a data type; '" <> renderTerm tT <> "' is not one (§22.1)")
      pure (Left ())

-- | §22.1 'inspectRecord': closed records only; field order follows
-- the written order of the inspected alias when known (§22.2).
shapeInspectRecordOp :: Ctx -> Span -> Value -> Value -> CheckM (Either () Value)
shapeInspectRecordOp _ctx sp tyV target = do
  t <- forceRT tyV
  case t of
    VRecordT fs -> do
      written <- targetFieldOrder target
      let names = map fst fs
          ordered = case written of
            Just ws | sort ws == sort names -> ws
            _ -> names
      pure $
        Right $
          VCtor
            (gShape "RecordShape")
            [listValue [shapeFieldValue (Just nm) i | (i, nm) <- zip [0 ..] ordered]]
    VGlobI openRecord [_] _
      | openRecord == prelOpenRec -> do
          errAt sp "KAPPA_DERIVING_SHAPE_NOT_CLOSED_RECORD" shapeFamily
            "Phase 0 record shape inspection requires a closed record type; open record types are reserved for a later phase (§22.1)"
          pure (Left ())
    _ -> do
      tT <- quoteIn emptyCtx t
      errAt sp "KAPPA_DERIVING_SHAPE_NOT_CLOSED_RECORD" shapeFamily
        ("record shape inspection requires a closed record type; '" <> renderTerm tT <> "' is not one (§22.1)")
      pure (Left ())
  where
    targetFieldOrder tv = do
      tvF <- forceRT tv
      case tvF of
        VQuote qs _
          | EVar n <- qsExpr qs -> do
              mg <- lookupGlobalName (nameText n)
              case mg of
                Just g -> gets (Map.lookup g . csRecordOrders)
                Nothing -> pure Nothing
        _ -> pure Nothing

-- | Field arity of a shape-constructor summary value.
shapeCtorInfo :: Value -> CheckM (Text, Int, [Value])
shapeCtorInfo cv = do
  cvF <- forceRT cv
  case cvF of
    VCtor (GName _ "ShapeConstructor") [nmV, _, _, fieldsV] -> do
      nmF <- forceRT nmV
      let nm = case nmF of
            VLit (LitStr s) -> s
            _ -> "?"
      fields <- valueList fieldsV
      pure (nm, length fields, fields)
    _ -> pure ("?", 0, [])
