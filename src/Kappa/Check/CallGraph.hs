-- | Call-graph and recursive-group construction.
--
-- Building the caller/callee relation used to form declaration SCCs and to
-- seed termination checking in "Kappa.Check.Totality".
--
-- Carved out of "Kappa.Check" as part of splitting that module; see
-- "Kappa.Check.Types" for the shared data dictionary and docs\/CONCEPTS.md
-- for the vocabulary these assume.
module Kappa.Check.CallGraph
  ( bindDerivedEqEvidence
  , closeDerivedEqEvidence
  , compilerOwnedTypeLevelTraits
  , constraintHead
  , constraintIdOccs
  , constructorFieldBinders
  , derivedEmptyInstance
  , derivedComparatorBridgeBody
  , derivedEqualityBody
  , derivedEqualityBodyWithEvidence
  , derivedEqualityCompleteBody
  , derivedEqualitySoundBody
  , derivedFunctionalEqualityMemberBody
  , derivedGeneratedSpan
  , derivedRefinementViewDecl
  , derivedTraitHead
  , derivedWholeInstance
  , freeLower
  , instBindPremises
  , instDictTy
  , instSplitHead
  , instanceDictionaryTraitUniverses
  , instanceFreeVars
  , intrinsicUniverseTraits
  , refinementIsPropFiber
  , withTemporaryReducibleGlobals
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

derivedGeneratedSpan :: Span -> Int -> Span
derivedGeneratedSpan (Span file start (Pos endLine endColumn)) discriminator =
  Span file start (Pos endLine (endColumn + discriminator))

derivedTraitHead :: Span -> Text -> Expr -> Expr
derivedTraitHead span' trait target =
  EApp (EVar (Name trait span')) [ArgExplicit target]

derivedEmptyInstance :: Span -> Int -> Text -> Expr -> Decl
derivedEmptyInstance sourceSpan discriminator trait target =
  let span' = derivedGeneratedSpan sourceSpan discriminator
   in DInstance
        ( InstanceDecl
            Nothing
            []
            (derivedTraitHead span' trait target)
            (InstanceMembers [])
        )
        span'

-- | Declaration-level @derive (Tr T)@ uses the same facet-completion mode as
-- @instance Tr T = derive@ (§14.3.4A). Trait-specific structural generators
-- may still produce a more explicit checked instance before reaching this
-- fallback; this constructor is the uniform protocol for every other trait.
derivedWholeInstance :: Span -> GName -> Expr -> Decl
derivedWholeInstance sourceSpan trait target =
  let span' = derivedGeneratedSpan sourceSpan 1
   in DInstance
        ( InstanceDecl
            Nothing
            []
            (derivedTraitHead span' (gnameText trait) target)
            InstanceDerive
        )
        span'

-- | Recover the semantic fiber from checked @IsProp fiber@ evidence. Hidden
-- declaration-universe proof arguments are removed through the trait's
-- registered semantic telescope, so this cannot be confused by source
-- spelling or a same-named non-prelude declaration.
refinementIsPropFiber :: Value -> CheckM (Maybe Value)
refinementIsPropFiber fieldType = do
  normalized <- forceM fieldType
  state <- get
  pure $ case normalized of
    VGlobN trait arguments
      | trait == gPrel "IsProp"
      , Just [(Expl, fiber)] <- traitSemanticSpineIn state trait arguments ->
          Just fiber
    _ -> Nothing

derivedRefinementViewDecl
  :: Span
  -> Expr
  -> DerivedRefinementViewShape
  -> Decl
derivedRefinementViewDecl sourceSpan target shape =
  DInstance
    ( InstanceDecl
        Nothing
        []
        (derivedTraitHead span' "RefinementView" target)
        (InstanceMembers members)
    )
    span'
  where
    span' = derivedGeneratedSpan sourceSpan 1
    baseName = Name "__derive_refinement_base" span'
    valueName = Name "__derive_refinement_value" span'
    isPropName = Name "__derive_refinement_is_prop" span'
    proofName = Name "__derive_refinement_proof" span'
    refinedName = Name "__derive_refinement_value_object" span'
    predicateIsPropName = Name "__derive_refinement_predicate_is_prop" span'
    predicateProofName = Name "__derive_refinement_predicate_proof" span'
    implicit name = (simpleBinder name) {bImplicit = True}
    member name binders body =
      DLet
        noMods
        ( LetDef
            (Just (Name name span'))
            False
            Nothing
            Nothing
            emptyPrefix
            binders
            Nothing
            Nothing
            body
        )
        span'
    members =
      [ member "Base" [] (drvsBaseType shape)
      , member "Predicate" [simpleBinder baseName] (drvsPredicateBody shape)
      , member
          "refinementValue"
          [simpleBinder refinedName]
          (projectRefinementField refinedName (drvsBaseFieldName shape) valueName)
      , member
          "refinementPredicateIsProp"
          [simpleBinder refinedName]
          ( projectRefinementField
              refinedName
              (Just (drvsIsPropFieldName shape))
              isPropName
          )
      , member
          "refinementProof"
          [simpleBinder refinedName]
          ( projectRefinementField
              refinedName
              (Just (drvsProofFieldName shape))
              proofName
          )
      , member
          "refine"
          [ simpleBinder baseName
          , implicit predicateIsPropName
          , implicit predicateProofName
          ]
          constructDerivedRefinement
      , member
          "valueAfterRefine"
          [ implicit baseName
          , implicit predicateIsPropName
          , implicit predicateProofName
          ]
          refl
      , member
          "refineAfterValue"
          [implicit refinedName]
          (matchRefinementBase refinedName refl)
      ]
    targetQualifier = case targetHead target of
      EVar name -> Just name
      _ -> Nothing
    targetHead = \case
      EApp function _ -> targetHead function
      other -> other
    constructorName = Name (gnameText (drvsConstructor shape)) span'
    constructorPattern =
      PCtor
        (CtorRef targetQualifier constructorName)
        [PVar valueName]
        span'
    matchRefinementBase scrutinee body =
      EMatch
        (EVar scrutinee)
        [ MatchCase
            constructorPattern
            Nothing
            body
            span'
        ]
        span'
    projectRefinementField scrutinee fieldName fallbackName =
      case fieldName of
        Just name ->
          EDot (EVar scrutinee) (DotName (Name name span'))
        Nothing ->
          matchRefinementBase scrutinee (EVar fallbackName)
    constructorExpression =
      case targetQualifier of
        Just qualifier -> EDot (EVar qualifier) (DotName constructorName)
        Nothing -> EVar constructorName
    constructDerivedRefinement =
      EApp
        constructorExpression
        [ argumentFor index icit
        | (index, icit) <- zip [0 :: Int ..] (drvsFieldIcit shape)
        ]
    argumentFor index icit =
      let expression
            | index == drvsBaseIndex shape = EVar baseName
            | index == drvsIsPropIndex shape = EVar predicateIsPropName
            | index == drvsProofIndex shape = EVar predicateProofName
            | otherwise = EHole Nothing span'
       in case icit of
            Expl -> ArgExplicit expression
            Impl -> ArgImplicit expression
    refl = EVar (Name "refl" span')

derivedEqualityBody
  :: Span
  -> Expr
  -> DerivedNominalShape
  -> Name
  -> Name
  -> Expr
derivedEqualityBody span' target shape xName yName =
  derivedEqualityBodyWithMethods
    span'
    target
    shape
    (Map.map (map DerivedEqFieldEvidence) defaultEvidence)
    xName
    yName
  where
    defaultEvidence =
      Map.fromList
        [ (constructor, replicate (length fields) Nothing)
        | (constructor, fields) <- shape
        ]

derivedEqualityBodyWithEvidence
  :: Span
  -> Expr
  -> DerivedNominalShape
  -> DerivedEqEvidenceNames
  -> Name
  -> Name
  -> Expr
derivedEqualityBodyWithEvidence span' target shape evidenceNames xName yName =
  derivedEqualityBodyWithMethods
    span'
    target
    shape
    (Map.map (map DerivedEqFieldEvidence) evidenceNames)
    xName
    yName

derivedEqualityBodyWithMethods
  :: Span
  -> Expr
  -> DerivedNominalShape
  -> DerivedEqFieldMethods
  -> Name
  -> Name
  -> Expr
derivedEqualityBodyWithMethods span' target shape methods xName yName =
  EMatch (ETuple [EVar xName, EVar yName] span')
    ( [ MatchCase
          (derivedEqualityPairPattern span' target constructor xFields constructor yFields)
          Nothing
          ( compareFields
              fields
              (Map.findWithDefault defaultMethods constructor methods)
              xFields
              yFields
          )
          span'
      | (constructor, fields) <- shape
      , let xFields = derivedEqualityFieldNames span' "__derive_x" constructor fields
            yFields = derivedEqualityFieldNames span' "__derive_y" constructor fields
      ]
        ++ [MatchCase (PWild span') Nothing falseExpr span']
    )
    span'
  where
    compareFields [] _ [] [] = trueExpr
    compareFields (field : fields) (method : methods') (left : lefts) (right : rights)
      | dnfQuantity field == Q0 =
          compareFields fields methods' lefts rights
      | not (hasRuntimeDerivedField fields) =
          fieldCondition field method left right
      | otherwise =
          EIf
            [ ( fieldCondition field method left right
              , compareFields fields methods' lefts rights
              )
            ]
            (Just falseExpr)
            span'
    compareFields _ _ _ _ = falseExpr
    defaultMethods = repeat (DerivedEqFieldEvidence Nothing)
    fieldCondition field method left right =
      case method of
        DerivedEqFieldEvidence evidence ->
          fieldEqualityWithEvidence
            span'
            (dnfTypeExpression field)
            evidence
            left
            right
        DerivedEqFieldRecursive -> falseExpr
    trueExpr = EVar (Name "True" span')
    falseExpr = EVar (Name "False" span')

-- | Expose both comparator applications to the ordinary checker under every
-- constructor pair, then ask the unified derivation engine for the remaining
-- equality. This is the proof-producing fallback for selected comparators
-- that are extensionally structural only after checked normalization.
derivedComparatorBridgeBody
  :: Span
  -> Expr
  -> DerivedNominalShape
  -> Name
  -> Name
  -> Expr
derivedComparatorBridgeBody span' target shape xName yName =
  EMatch (EVar xName)
    [ MatchCase
        (derivedEqualityCtorPattern span' target left leftFields)
        Nothing
        ( EMatch (EVar yName)
            [ MatchCase
                (derivedEqualityCtorPattern span' target right rightFields)
                Nothing
                -- Complete checked constructor facts bound the remaining
                -- equality goal. The unified derivation engine may use
                -- ordinary conversion, arithmetic normalization, and
                -- selected evidence, but must still produce a checked proof.
                (EDerive Nothing span')
                span'
            | (right, rightShape) <- shape
            , let rightFields =
                    derivedEqualityFieldNames
                      span'
                      "__derive_bridge_right"
                      right
                      rightShape
            ]
            span'
        )
        span'
    | (left, leftShape) <- shape
    , let leftFields =
            derivedEqualityFieldNames
              span'
              "__derive_bridge_left"
              left
              leftShape
    ]
    span'

bindDerivedEqEvidence
  :: Ctx
  -> [DerivedEqEvidenceBinding]
  -> CheckM Ctx
bindDerivedEqEvidence source = foldM bindOne source
  where
    bindOne active DerivedEqEvidenceBinding {..} = do
      dictionaryValue <- evalIn source deebDictionary
      pure
        ( bindCtxLet
            (nameText deebName)
            False
            deebDictionaryType
            dictionaryValue
            active
        )

closeDerivedEqEvidence
  :: [DerivedEqEvidenceBinding]
  -> Term
  -> Term
closeDerivedEqEvidence bindings body0 =
  foldl'
    (\body (index, binding) ->
       substTopTermAt
         0
         (shiftTerm index 0 (deebDictionary binding))
         body)
    body0
    (reverse (zip [0 :: Int ..] bindings))

-- | Temporarily expose already-certified equations while preserving every
-- other state change made by the enclosed checker action.  Restoring just the
-- reducibility bits is important for speculative derive candidates: metas and
-- selected evidence from a successful ordinary check must survive, while the
-- module-level termination pass remains the sole publisher of permanent
-- conversion transparency.
withTemporaryReducibleGlobals :: [GName] -> CheckM a -> CheckM a
withTemporaryReducibleGlobals identities action = do
  globals <- gets csGlobals
  let saved =
        Map.map gdReducible
          (Map.restrictKeys globals (Set.fromList identities))
  modify' $ \state ->
    invalidateSemanticCaches
      state
        { csGlobals =
            foldr
              (Map.adjust (\definition -> definition {gdReducible = True}))
              (csGlobals state)
              identities
        }
  result <- action
  modify' $ \state ->
    invalidateSemanticCaches
      state
        { csGlobals =
            Map.foldlWithKey'
              (\globals identity reducible ->
                 Map.adjust
                   (\definition -> definition {gdReducible = reducible})
                   identity
                   globals)
              (csGlobals state)
              saved
        }
  pure result

derivedEqualitySoundBody
  :: Span
  -> Expr
  -> DerivedNominalShape
  -> DerivedEqEvidenceNames
  -> Name
  -> Name
  -> Name
  -> Expr
derivedEqualitySoundBody span' target shape evidenceNames xName yName proofName =
  derivedEqualitySoundBodyWithMethods
    span'
    target
    shape
    (Map.map (map DerivedEqFieldEvidence) evidenceNames)
    Nothing
    xName
    yName
    proofName

derivedEqualitySoundBodyWithMethods
  :: Span
  -> Expr
  -> DerivedNominalShape
  -> DerivedEqFieldMethods
  -> Maybe (Name, Name)
  -> Name
  -> Name
  -> Name
  -> Expr
derivedEqualitySoundBodyWithMethods span' target shape methods recursion xName yName proofName =
  EMatch (EVar xName)
    [ MatchCase
        (derivedEqualityCtorPattern span' target constructor xFields)
        Nothing
        ( EMatch (EVar yName)
            [ MatchCase
                (derivedEqualityCtorPattern span' target other yFields)
                Nothing
                ( if constructor == other
                    then
                      proveFields
                        fields
                        (Map.findWithDefault defaultMethods constructor methods)
                        xFields
                        yFields
                        (EVar proofName)
                    else eliminateFalseProof (EVar proofName)
                )
                span'
            | (other, otherFields) <- shape
            , let yFields =
                    derivedEqualityFieldNames
                      span'
                      "__derive_sound_y"
                      other
                      otherFields
            ]
            span'
        )
        span'
    | (constructor, fields) <- shape
    , let xFields =
            derivedEqualityFieldNames span' "__derive_sound_x" constructor fields
    ]
    span'
  where
    proveFields [] _ [] [] _ = reflExpr span'
    proveFields
      (field : fields)
      (method : methods')
      (left : lefts)
      (right : rights)
      proof
        | dnfQuantity field == Q0 =
            matchRefl
              span'
              (subsingletonEquality span' fieldType left right)
              (proveFields fields methods' lefts rights proof)
        | not (hasRuntimeDerivedField fields) =
            let fieldProof =
                  fieldSoundProof fieldType method left right proof
             in matchRefl
                  span'
                  fieldProof
                  (proveFields fields methods' lefts rights (reflExpr span'))
        | otherwise =
            let condition =
                  fieldCondition fieldType method left right
                remainder =
                  fieldEqualityBodyWithMethods
                    span'
                    fields
                    methods'
                    recursion
                    lefts
                    rights
                headProof =
                  callNamed
                    span'
                    "boolGuardCondition"
                    [condition, remainder, proof]
                tailProof =
                  callNamed
                    span'
                    "boolGuardBody"
                    [condition, remainder, proof]
                fieldProof =
                  fieldSoundProof fieldType method left right headProof
             in matchRefl
                  span'
                  fieldProof
                  (proveFields fields methods' lefts rights tailProof)
      where
        fieldType = dnfTypeExpression field
    proveFields _ _ _ _ proof = eliminateFalseProof proof
    eliminateFalseProof proof =
      matchRefl span' proof (EImpossible span')
    defaultMethods = repeat (DerivedEqFieldEvidence Nothing)
    fieldCondition fieldType method left right =
      case method of
        DerivedEqFieldEvidence evidence ->
          fieldEqualityWithEvidence span' fieldType evidence left right
        DerivedEqFieldRecursive ->
          case recursion of
            Just (comparator, _) ->
              callNamed span' (nameText comparator) [EVar left, EVar right]
            Nothing ->
              fieldEqualityWithEvidence span' fieldType Nothing left right
    fieldSoundProof fieldType method left right proof =
      case (method, recursion) of
        (DerivedEqFieldRecursive, Just (_, helper)) ->
          callNamed span' (nameText helper) [EVar left, EVar right, proof]
        (DerivedEqFieldEvidence evidence, _) ->
          fieldEvidenceMemberCall
            span'
            fieldType
            evidence
            "eqSound"
            [EVar left, EVar right, proof]
        (DerivedEqFieldRecursive, Nothing) -> EImpossible span'

derivedEqualityCompleteBody
  :: Span
  -> Expr
  -> DerivedNominalShape
  -> DerivedEqEvidenceNames
  -> Name
  -> Name
  -> Name
  -> Expr
derivedEqualityCompleteBody span' target shape evidenceNames xName yName proofName =
  derivedEqualityCompleteBodyWithMethods
    span'
    target
    shape
    (Map.map (map DerivedEqFieldEvidence) evidenceNames)
    Nothing
    xName
    yName
    proofName

derivedEqualityCompleteBodyWithMethods
  :: Span
  -> Expr
  -> DerivedNominalShape
  -> DerivedEqFieldMethods
  -> Maybe (Name, Name)
  -> Name
  -> Name
  -> Name
  -> Expr
derivedEqualityCompleteBodyWithMethods span' target shape methods recursion xName _yName proofName =
  -- Split the ordinary endpoint before eliminating its equality proof.  The
  -- refl constructor binds its endpoint parametrically; eliminating it first
  -- lets branch conversion quote a runtime comparator through that erased
  -- witness.  Constructor-first path induction keeps the comparator motive
  -- rooted at the checked ordinary endpoint while retaining the same equality
  -- certificate inside each finite branch.
  EMatch (EVar xName)
    [ MatchCase
        (derivedEqualityCtorPattern span' target constructor fields)
        Nothing
        ( matchRefl
            span'
            (EVar proofName)
            ( proveReflexive
                constructorFields
                (Map.findWithDefault defaultMethods constructor methods)
                fields
            )
        )
        span'
    | (constructor, constructorFields) <- shape
    , let fields =
            derivedEqualityFieldNames
              span'
              "__derive_complete_x"
              constructor
              constructorFields
    ]
    span'
  where
    proveReflexive [] _ [] = reflExpr span'
    proveReflexive (fieldInfo : fields) (method : methods') (field : rest)
      | dnfQuantity fieldInfo == Q0 =
          proveReflexive fields methods' rest
      | not (hasRuntimeDerivedField fields) =
          fieldCompleteProof fieldType method field
      | otherwise =
          let condition =
                fieldCondition fieldType method field field
              remainder =
                fieldEqualityBodyWithMethods
                  span'
                  fields
                  methods'
                  recursion
                  rest
                  rest
              headProof =
                fieldCompleteProof fieldType method field
              tailProof = proveReflexive fields methods' rest
           in callNamed
                span'
                "boolGuardComplete"
                [condition, remainder, headProof, tailProof]
      where
        fieldType = dnfTypeExpression fieldInfo
    proveReflexive _ _ _ = EImpossible span'
    defaultMethods = repeat (DerivedEqFieldEvidence Nothing)
    fieldCondition fieldType method left right =
      case method of
        DerivedEqFieldEvidence evidence ->
          fieldEqualityWithEvidence span' fieldType evidence left right
        DerivedEqFieldRecursive ->
          case recursion of
            Just (comparator, _) ->
              callNamed span' (nameText comparator) [EVar left, EVar right]
            Nothing ->
              fieldEqualityWithEvidence span' fieldType Nothing left right
    fieldCompleteProof fieldType method field =
      case (method, recursion) of
        (DerivedEqFieldRecursive, Just (_, helper)) ->
          callNamed
            span'
            (nameText helper)
            [EVar field, EVar field, reflExpr span']
        (DerivedEqFieldEvidence evidence, _) ->
          fieldEvidenceMemberCall
            span'
            fieldType
            evidence
            "eqComplete"
            [EVar field, EVar field, reflExpr span']
        (DerivedEqFieldRecursive, Nothing) -> EImpossible span'

derivedFunctionalEqualityMemberBody
  :: Bool
  -> Span
  -> Expr
  -> DerivedNominalShape
  -> DerivedEqFieldMethods
  -> DerivedFunctionalEquality
  -> Name
  -> Name
  -> Name
  -> Expr
derivedFunctionalEqualityMemberBody sound span' target shape rootMethods functional xName yName proofName =
  ELet
    [ LetBind
        False
        emptyPrefix
        (PVar helperProofName)
        (Just helperProofType)
        (ELambda Nothing (map simpleBinder [helperX, helperY, helperProof]) helperBody span')
        span'
    ]
    rootBody
    span'
  where
    comparatorName = dfeBindingName functional
    helperProofName =
      Name
        (if sound then "__derive_functional_sound" else "__derive_functional_complete")
        span'
    helperX = Name "__derive_functional_x" span'
    helperY = Name "__derive_functional_y" span'
    helperProof = Name "__derive_functional_proof" span'
    recursion = Just (comparatorName, helperProofName)
    helperProofType =
      derivedFunctionalEqualityProofType
        sound
        span'
        (dfeDomainExpr functional)
        comparatorName
        helperX
        helperY
        helperProof
    helperBody
      | sound =
          derivedEqualitySoundBodyWithMethods
            span'
            (dfeDomainExpr functional)
            (dfeShape functional)
            (dfeMethods functional)
            recursion
            helperX
            helperY
            helperProof
      | otherwise =
          derivedEqualityCompleteBodyWithMethods
            span'
            (dfeDomainExpr functional)
            (dfeShape functional)
            (dfeMethods functional)
            recursion
            helperX
            helperY
            helperProof
    rootBody
      | sound =
          derivedEqualitySoundBodyWithMethods
            span'
            target
            shape
            rootMethods
            recursion
            xName
            yName
            proofName
      | otherwise =
          derivedEqualityCompleteBodyWithMethods
            span'
            target
            shape
            rootMethods
            recursion
            xName
            yName
            proofName

derivedFunctionalEqualityProofType
  :: Bool
  -> Span
  -> Expr
  -> Name
  -> Name
  -> Name
  -> Name
  -> Expr
derivedFunctionalEqualityProofType sound span' domain comparator xName yName proofName =
  EArrow (typed xName domain) $
    EArrow (typed yName domain) $
      EArrow (typed proofName premise) conclusion
  where
    comparatorResult =
      callNamed span' (nameText comparator) [EVar xName, EVar yName]
    decisionTrue = equality comparatorResult (EVar (Name "True" span'))
    endpointsEqual = equality (EVar xName) (EVar yName)
    (premise, conclusion)
      | sound = (decisionTrue, endpointsEqual)
      | otherwise = (endpointsEqual, decisionTrue)
    typed name ty = (simpleBinder name) {bType = Just ty}
    equality left right =
      EApp
        (EOpRef Nothing (Name "=" span') span')
        [ArgExplicit left, ArgExplicit right]

derivedEqualityCtorPattern :: Span -> Expr -> GName -> [Name] -> Pattern
derivedEqualityCtorPattern span' target constructor fields =
  PCtor
    (CtorRef (targetHeadName target) (Name (gnameText constructor) span'))
    (map PVar fields)
    span'

derivedEqualityPairPattern
  :: Span
  -> Expr
  -> GName
  -> [Name]
  -> GName
  -> [Name]
  -> Pattern
derivedEqualityPairPattern span' target left leftFields right rightFields =
  PTuple
    [ derivedEqualityCtorPattern span' target left leftFields
    , derivedEqualityCtorPattern span' target right rightFields
    ]
    span'

derivedEqualityFieldNames
  :: Span
  -> Text
  -> GName
  -> [DerivedNominalField]
  -> [Name]
derivedEqualityFieldNames span' prefix constructor fields =
  [ Name
      (prefix <> "_" <> gnameText constructor <> "_" <> T.pack (show index))
      span'
  | (index, _) <- zip [0 :: Int ..] fields
  ]

fieldEqualityBody
  :: Span
  -> [DerivedNominalField]
  -> [Maybe Name]
  -> [Name]
  -> [Name]
  -> Expr
fieldEqualityBody span' fields evidences =
  fieldEqualityBodyWithMethods
    span'
    fields
    (map DerivedEqFieldEvidence evidences)
    Nothing

fieldEqualityBodyWithMethods
  :: Span
  -> [DerivedNominalField]
  -> [DerivedEqFieldMethod]
  -> Maybe (Name, Name)
  -> [Name]
  -> [Name]
  -> Expr
fieldEqualityBodyWithMethods span' fields methods recursion = go fields methods
  where
    go [] _ [] [] = EVar (Name "True" span')
    go (field : restFields) (method : restMethods) (left : lefts) (right : rights)
      | dnfQuantity field == Q0 = go restFields restMethods lefts rights
      | not (hasRuntimeDerivedField restFields) =
          condition field method left right
      | otherwise =
          EIf
            [ ( condition field method left right
              , go restFields restMethods lefts rights
              )
            ]
            (Just (EVar (Name "False" span')))
            span'
    go _ _ _ _ = EVar (Name "False" span')

    condition field method left right =
      case method of
        DerivedEqFieldEvidence evidence ->
          fieldEqualityWithEvidence
            span'
            (dnfTypeExpression field)
            evidence
            left
            right
        DerivedEqFieldRecursive ->
          case recursion of
            Just (comparator, _) ->
              callNamed span' (nameText comparator) [EVar left, EVar right]
            Nothing ->
              fieldEqualityWithEvidence
                span'
                (dnfTypeExpression field)
                Nothing
                left
                right

hasRuntimeDerivedField :: [DerivedNominalField] -> Bool
hasRuntimeDerivedField = any ((/= Q0) . dnfQuantity)

fieldEquality :: Span -> Expr -> Name -> Name -> Expr
fieldEquality span' fieldType left right =
  fieldEqualityWithEvidence span' fieldType Nothing left right

fieldEqualityWithEvidence
  :: Span
  -> Expr
  -> Maybe Name
  -> Name
  -> Name
  -> Expr
fieldEqualityWithEvidence span' fieldType evidence left right =
  fieldEvidenceMemberCall
    span'
    fieldType
    evidence
    "=="
    [EVar left, EVar right]

-- | Invoke one checked member of the exact selected @Eq@ dictionary. Keeping
-- the dictionary projection in the generated term preserves the comparator's
-- evidence identity and universe instantiation; routing through a freshly
-- specialized @eqBoolean*@ convenience wrapper would create a second
-- conversion obligation unrelated to the user's checked comparator.
fieldEvidenceMemberCall
  :: Span
  -> Expr
  -> Maybe Name
  -> Text
  -> [Expr]
  -> Expr
fieldEvidenceMemberCall span' fieldType evidence member arguments =
  EApp
    ( EDot
        (fieldEvidenceExpression span' fieldType evidence)
        (DotName (Name member span'))
    )
    (map ArgExplicit arguments)

fieldEvidenceExpression :: Span -> Expr -> Maybe Name -> Expr
fieldEvidenceExpression span' fieldType =
  maybe
    (traitEvidenceExpression span' "Eq" fieldType)
    EVar

subsingletonEquality :: Span -> Expr -> Name -> Name -> Expr
subsingletonEquality span' fieldType left right =
  EApp
    ( EDot
        (traitEvidenceExpression span' "IsSubsingleton" fieldType)
        (DotName (Name "allEqual" span'))
    )
    [ArgExplicit (EVar left), ArgExplicit (EVar right)]

traitEvidenceExpression :: Span -> Text -> Expr -> Expr
traitEvidenceExpression span' trait fieldType =
  callNamed
    span'
    "summon"
    [EApp (EVar (Name trait span')) [ArgExplicit fieldType]]

callNamed :: Span -> Text -> [Expr] -> Expr
callNamed span' name arguments =
  EApp
    (EVar (Name name span'))
    (map ArgExplicit arguments)

matchRefl :: Span -> Expr -> Expr -> Expr
matchRefl span' scrutinee body =
  EMatch
    scrutinee
    [ MatchCase
        (PCtor (CtorRef Nothing (Name "refl" span')) [] span')
        Nothing
        body
        span'
    ]
    span'

reflExpr :: Span -> Expr
reflExpr span' = EVar (Name "refl" span')

targetHeadName :: Expr -> Maybe Name
targetHeadName = \case
  EVar name -> Just name
  EApp function _ -> targetHeadName function
  _ -> Nothing

constructorFieldBinders :: CtorInfo -> [(Q, Term)]
constructorFieldBinders info =
  drop (length binders - fieldCount) binders
  where
    -- 'ciFields' contains only explicit source fields because it also stores
    -- explicit-field defaults. Semantic constructor shape must include erased
    -- implicit proof fields as well; 'ciSourceFields' is the exact source
    -- telescope with family/generated binders intentionally absent.
    fieldCount = length (ciSourceFields info)
    binders = piBinders (ciType info)
    piBinders = \case
      CPiBoundM _ _ quantity _ _ _ domain body ->
        (quantity, domain) : piBinders body
      _ -> []

compilerOwnedTypeLevelTraits :: [GName]
compilerOwnedTypeLevelTraits =
  [ gPrel "Eq"
  , prelOrd
  , gPrel "Zero"
  , gPrel "One"
  , gPrel "FromInteger"
  , prelSuccessor
  , gPrel "Add"
  , prelMax
  ]

intrinsicUniverseTraits :: Set GName
intrinsicUniverseTraits = Set.fromList [prelIsNType, prelRuntimeErased]

instSplitHead :: Expr -> CheckM (Maybe GName, Maybe [Expr], [Expr])
instSplitHead e = case e of
  EApp f args -> do
    (g, universes, es) <- instSplitHead f
    pure (g, universes, es ++ [a | ArgExplicit a <- args])
  EUniverseInstantiation base levels _ -> do
    (g, inherited, es) <- instSplitHead base
    case inherited of
      Nothing -> pure (g, Just levels, es)
      Just _ -> do
        errAt (exprSpan e) "E_UNIVERSE_SCHEMA_SCOPE" (Just "kappa.universe.schema-scope")
          "an instance trait head may carry only one explicit universe instantiation"
        pure (g, inherited, es)
  EVar n -> do
    mg <- lookupGlobalName (nameText n)
    pure (mg, Nothing, [])
  _ -> pure (Nothing, Nothing, [])

-- | Bind the instance's premise dictionaries as implicit-local candidates.
-- Each premise term was elaborated under the fv binders only, so the k-th
-- premise sits under k earlier premise binders and must be shifted by k. Each
-- dictionary also gets a DISTINCT name: 'localCandidate' dedups candidates by
-- name, so premises sharing a name (e.g. two @Eq@ premises @Eq e@, @Eq a@)
-- would shadow each other and the second goal would never resolve locally.
instBindPremises :: Ctx -> [Term] -> CheckM Ctx
instBindPremises ctx0 = go (0 :: Int) ctx0
  where
    go _ c [] = pure c
    go i c (p : rest) = do
      pv <- evalIn c (shiftTerm i 0 p)
      go (i + 1) (bindCtx ("__prem" <> T.pack (show i)) True pv c) rest

instDictTy :: Telescope -> [Term] -> Term -> CheckM (Term, Value)
instDictTy fvTele premTms dictHead = do
  -- premises were elaborated under the fv binders only; the k-th
  -- premise domain sits under k earlier premise binders, so shift by
  -- k. The head ('argTms') was elaborated under fvs + all premises
  -- and is already correctly indexed. The fully applied dictionary head also
  -- retains every generated hidden argument inserted between source slots.
  let withPrems = go (0 :: Int) premTms
      go _ [] = dictHead
      go k (p : ps) = CPiFormedM Ordinary FormationOrdinary Impl QW False "__p" (shiftTerm k 0 p) (go (k + 1) ps)
  let coreType = foldr telePi withPrems fvTele
  coreValue <- evalIn emptyCtx coreType
  pure (coreType, coreValue)

-- | Recover the owning trait's exact universe occurrence from the registered
-- instance head.  The instance registry is transformed together with the
-- dictionary declaration at every universe-finalization boundary, whereas
-- reparsing the dictionary's semantic type can observe an earlier
-- provisional reference shape while its body is still deferred.
instanceDictionaryTraitUniverses
  :: Span
  -> GName
  -> GName
  -> CheckM [Level]
instanceDictionaryTraitUniverses site dictionary expectedTrait = do
  state <- get
  case
      [ entry
      | entry <- csInstances state
      , ieDict entry == dictionary
      , ieTrait entry == expectedTrait
      ]
    of
      [entry] ->
        pure
          ( map
              (resolveFinalizedOwnerLevel state dictionary)
              (ieTraitUniverses entry)
          )
      _ -> malformed
  where
    malformed = do
      errAt site "E_INTERNAL_PRELUDE_INTERFACE" (Just "kappa.internal.compiler")
        ( "the registered head of instance dictionary '"
            <> gnameText dictionary
            <> "' does not identify exactly one entry for trait '"
            <> gnameText expectedTrait
            <> "'"
        )
      pure []

-- free lowercase identifiers (implicit universalization, §11.3.3
-- approximation: ASCII lowercase heads not resolving to globals).
freeLower :: Expr -> [Text]
freeLower = go
  where
    go = \case
      EVar (Name n _)
        | isLowerHead n -> [n]
        | otherwise -> []
      -- the label argument of a row constraint is not a type variable
      -- (§11.3.1: 'LacksRec r age')
      EApp f@(EVar hd) [rowA, ArgExplicit (EVar _)]
        | nameText hd == "LacksRec" -> go f ++ goArg rowA
      EApp f args -> go f ++ concatMap goArg args
      EArrow b e -> maybe [] go (bType b) ++ withoutBinders [b] (go e)
      -- §11.3.3: a `forall` binder is in scope for every LATER binder's
      -- type and the body, so a name bound earlier in the telescope is not
      -- free where a subsequent binder's type mentions it (e.g. the `a` in
      -- `(x : Core G a)` after `(a : Type)`). Threading the binders left to
      -- right avoids spuriously universalizing such a name as an extra
      -- leading implicit, which otherwise duplicates the binder and
      -- cross-links shared dependent indices.
      EForall bs e _ -> goTele bs
        where
          goTele [] = go e
          goTele (b : rest) = maybe [] go (bType b) ++ withoutBinders [b] (goTele rest)
      EExists bs e _ -> goTele bs
        where
          goTele [] = go e
          goTele (b : rest) = maybe [] go (bType b) ++ withoutBinders [b] (goTele rest)
      ETraitArrow a b -> go a ++ go b
      EOptionSugar e _ -> go e
      ETuple es _ -> concatMap go es
      ERecordType fields mtail _ ->
        let fieldNames = map (nameText . rtfName) fields
            mentioned = concatMap (go . rtfType) fields ++ maybe [] go mtail
         in filter (`notElem` fieldNames) mentioned
      EEffRow entries mtail _ ->
        concatMap (go . snd) entries ++ maybe [] go mtail
      EVariant arms mtail _ ->
        concatMap (\arm -> go (vaExpr arm) ++ maybe [] go (vaType arm)) arms
          ++ maybe [] go mtail
      EAscription e ty _ -> go e ++ go ty
      -- a dotted head (module path / projection, e.g. `main.Big`) is
      -- never an implicitly-universalized type variable
      EDot {} -> []
      _ -> []
    withoutBinders bs fvs =
      let bound = [nameText n | b <- bs, Just n <- [bName b]]
       in filter (`notElem` bound) fvs
    goArg = \case
      ArgExplicit e -> go e
      ArgImplicit e -> go e
      _ -> []
    isLowerHead n = case T.uncons n of
      Just (c, _) -> c >= 'a' && c <= 'z'
      Nothing -> False

instanceFreeVars :: [Expr] -> CheckM [Text]
instanceFreeVars exprs =
  filterM
    (\name -> do
       global <- lookupGlobalName name
       schemaLevel <- gets (Map.lookup name . csActiveUniverseSchema)
       -- Primitive universe spellings are syntax, never implicitly
       -- universalized instance-head variables. Treating @Type@ as an
       -- ordinary free head installs a local binder that shadows the
       -- primitive family and turns @Type u@ into an invalid runtime use of
       -- the rigid schema parameter @u@.
       pure
         ( isNothing global
             && isNothing schemaLevel
             && isNothing (sortName name)
             && name /= "ω"
         ))
    . nub
    $ concatMap constraintIdOccs exprs

-- | §14.3.5 instance-search termination: the identifier-leaf occurrences
-- of a constraint (type constructors AND variables, counting repetitions),
-- used to measure each instance premise against the head. Mirrors the
-- 'freeLower' traversal but keeps every name (not just free lowercase ones)
-- and does not deduplicate.
-- | The head identifier (trait name) of a constraint's application spine,
-- if any. Tells a self-recursive premise (same trait as the head) from a
-- cross-trait bridge premise like @Eq a => Equiv a@ (§14.3.5).
constraintHead :: Expr -> Maybe Text
constraintHead = \case
  EApp f _ -> constraintHead f
  EUniverseInstantiation base _ _ -> constraintHead base
  EVar (Name n _) -> Just n
  _ -> Nothing

constraintIdOccs :: Expr -> [Text]
constraintIdOccs = go
  where
    go = \case
      EVar (Name n _) -> [n]
      EApp f args -> go f ++ concatMap goArg args
      EUniverseInstantiation base _ _ -> go base
      EArrow b e -> maybe [] go (bType b) ++ go e
      EForall bs e _ -> concatMap (maybe [] go . bType) bs ++ go e
      ETraitArrow a b -> go a ++ go b
      EOptionSugar e _ -> go e
      ETuple es _ -> concatMap go es
      EDot {} -> []
      _ -> []
    goArg = \case
      ArgExplicit e -> go e
      ArgImplicit e -> go e
      _ -> []
