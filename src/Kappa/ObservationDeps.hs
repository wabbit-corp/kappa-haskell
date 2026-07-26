{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}

-- | The finite-origin observation dependency calculus of Spec SS30.2.0.
--
-- This module is deliberately checker-independent.  Elaboration and the
-- finalized KCore checkpoint supply the same typed lookup oracle and consume
-- the same equations, so neither phase can silently recover observation from
-- quantity or from source syntax.
module Kappa.ObservationDeps
  ( ParametricOrigin (..)
  , DependencySet
  , ObservationBinding (..)
  , ObservationOracle (..)
  , observationDependencies
  , dependenciesMode
  , classifierRelativeDependencies
  , evidenceRelativeCallableDependencies
  , dependencyBlocksFinalizedAnalysis
  , dependencyIsAnalysisFailure
  , constructorPatternObservationSites
  , intrinsicEffectConstructorType
  , isParametricKindValue
  , parametricCodomainPropagates
  , observationCallableType
  ) where

import Control.Applicative ((<|>))
import Control.Monad (guard)
import Data.List (find)
import qualified Data.Map.Strict as Map
import Data.Monoid (Any (..))
import Data.Maybe (fromMaybe, isNothing)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text

import Kappa.Builtins
  ( prelEff
  , prelEffLabel
  , prelEffOp
  , prelEffPure
  , prelEffRowCons
  , prelEffRowNil
  , prelCaptures
  , prelFalse
  , prelHandleEff
  , prelIO
  , prelOpenRec
  , prelProjector
  , prelSTM
  , prelString
  , prelThis
  , prelTrue
  )
import Kappa.Core
import Kappa.CoreOps (foldTermWithDepth, globalsOfTerm, itemPatternLevels, shiftTerm, spineOfTerm, substTopTermAt, termNodeLevels, termScopedAt)
import Kappa.Eval (EvalCtx (..), convertible, eval, evalApp, force, quote)
import Kappa.Source (ModuleName (..))

-- | Stable within one canonical Core tree.  Local paths are structural child
-- paths, not source names; global identities are resolved 'GName's; projected
-- origins identify the exact elimination node that re-introduced a sealed
-- parametric field.
data ParametricOrigin
  = ParametricExternal !Int !Text
  | ParametricBinder ![Int] !Text
  | ParametricGlobal !GName
  | ParametricProjection ![Int] !Text
  | ParametricTraitProjection ![Int] !GName !Text
  | ParametricThisProjection ![Int] !Text
  | ParametricPattern ![Int] !Int
  | ParametricMeta !MetaId
  | ParametricReflection ![Int]
  | ParametricAnalysisFailure ![Int] !Text
  deriving stock (Eq, Ord, Show)

type DependencySet = Set ParametricOrigin

data ObservationBinding = ObservationBinding
  { obMode :: !ObservationMode
  , obOrigin :: !(Maybe ParametricOrigin)
  , obType :: !(Maybe Value)
  , obUniverses :: !(Maybe DeclarationUniverseTelescope)
  , obDefinition :: !(Maybe (Int, Term))
  -- ^ Nonrecursive local body together with the environment depth at its
  -- definition site. This is typed structural authority for beta/zeta
  -- dependency analysis; recursive definitions deliberately omit it.
  }

-- | Typed facts owned by the caller.  The dependency equations remain shared;
-- only ordinary Core typing lookups that depend on checker-owned trait and
-- constructor tables are supplied through this interface.
data ObservationOracle = ObservationOracle
  { ooEvalCtx :: !EvalCtx
  , ooThisType :: !(Maybe Value)
  , ooGlobalMode :: GName -> Maybe ObservationMode
  , ooGlobalBody :: GName -> Maybe Term
  , ooGlobalPrimitive :: GName -> Bool
  , ooMetaMode :: MetaId -> Maybe ObservationMode
  , ooInferType :: Int -> [ObservationBinding] -> Term -> Maybe Value
  , ooProjectionMode :: Value -> Text -> Maybe ObservationMode
  , ooProjectionType :: Int -> Value -> Text -> Maybe Value
  , ooProjectionTrait :: Value -> Text -> Maybe GName
  , ooConstructorType :: GName -> Maybe [Level] -> Maybe Value
  , ooProvisionalUniverseMetadata :: !Bool
  , ooExpandingGlobals :: !(Set GName)
  -- ^ Transparent definitions currently being expanded by the beta/zeta
  -- dependency equation.  Re-entering one of these identities denotes the
  -- bottom edge of the recursive SCC's finite least fixed point; independent
  -- dependencies in every acyclic path through the SCC are still visited.
  }

dependenciesMode :: DependencySet -> ObservationMode
dependenciesMode dependencies
  | Set.null dependencies = Ordinary
  | otherwise = Parametric

-- | Remove dependencies that are already carried by the checked classifier
-- of an ordinary runtime value.  A value of @List A@ does not thereby observe
-- the parametric code @A@; using the same term as a value of @Type u@ still
-- retains the dependency because that classifier contains no @A@ origin.
-- Analysis and reflection barriers are never discharged this way.
classifierRelativeDependencies
  :: ObservationOracle
  -> [ObservationBinding]
  -> Int
  -> Value
  -> DependencySet
  -> DependencySet
classifierRelativeDependencies oracle bindings depth classifier dependencies =
  dependencies `Set.difference` removable
  where
    classifierTerm = quote (ooEvalCtx oracle) depth classifier
    classifierDependencies = observationDependencies oracle bindings Nothing classifierTerm
    removable = Set.filter isClassifierOrigin classifierDependencies
    isClassifierOrigin = \case
      ParametricAnalysisFailure {} -> False
      ParametricReflection {} -> False
      _ -> True

-- | §14.3.1A permits runtime behavior to depend on ordinary trait evidence
-- without promoting an associated static witness to ordinary observation.
-- A callable can therefore close over associated-type projections from that
-- evidence when its terminal result is an ordinary runtime classifier.  This
-- does not discharge ordinary record/package projections, arbitrary
-- parametric binders, analysis failures, or a callable that returns static
-- code.  The trait identity is supplied by the typed oracle, never a field
-- spelling heuristic.
evidenceRelativeCallableDependencies
  :: EvalCtx -> Int -> Value -> DependencySet -> DependencySet
evidenceRelativeCallableDependencies ctx depth classifier dependencies
  | Set.null dependencies = dependencies
  | all traitProjection (Set.toList dependencies)
  , Just (terminalDepth, terminal) <- callableTerminal depth classifier
  , not (isParametricKindValue ctx terminalDepth terminal) = Set.empty
  | otherwise = dependencies
  where
    traitProjection = \case
      ParametricTraitProjection {} -> True
      _ -> False

    callableTerminal level value = case observationCallableType ctx level value of
      VPiM _ _ _ _ _ _ (Closure environment codomain) ->
        let result = eval ctx (VRigid level [] : environment) codomain
         in case callableTerminal (level + 1) result of
              Just terminal -> Just terminal
              Nothing -> Just (level + 1, result)
      _ -> Nothing

dependencyIsAnalysisFailure :: ParametricOrigin -> Bool
dependencyIsAnalysisFailure = \case
  ParametricAnalysisFailure {} -> True
  _ -> False

-- | Metavariables are legitimate finite origins while elaboration is still
-- solving a declaration, but finalized typed Core has no later phase that can
-- discharge them. Keep this checkpoint predicate separate from
-- 'dependencyIsAnalysisFailure' so declaration generalization can still
-- distinguish a flexible origin from an actual analyzer failure.
dependencyBlocksFinalizedAnalysis :: ParametricOrigin -> Bool
dependencyBlocksFinalizedAnalysis = \case
  ParametricMeta {} -> True
  origin -> dependencyIsAnalysisFailure origin

rigidEnvironment :: Int -> [Value]
rigidEnvironment depth = [VRigid level [] | level <- reverse [0 .. depth - 1]]

-- | Recover the exact callable interface of checked Core types whose runtime
-- elimination shape differs from their nominal classifier. Capture
-- annotations wrap a function type without adding a binder, and first-class
-- projector application is a typed elimination even though the descriptor
-- retains nominal type @Projector Roots Focus@. This operation is used only
-- while typing lambda/application structure; it is not a global coercion.
observationCallableType :: EvalCtx -> Int -> Value -> Value
observationCallableType ctx depth value =
  let unwrapped = peelCaptures value
      raw = quote ctx depth unwrapped
      expanded = expandProjectionResult raw
   in if expanded == raw
        then unwrapped
        else eval ctx (rigidEnvironment depth) expanded
  where
    peelCaptures current = case force ctx current of
      VGlobI global _ ((_, inner) : _)
        | global == prelCaptures -> peelCaptures inner
      forced -> forced

    expandProjectionResult = \case
      CPiEvidenceM mode formation icit quantity borrowed name assumption origin domain codomain ->
        CPiEvidenceM mode formation icit quantity borrowed name assumption origin domain
          (expandProjectionResult codomain)
      result ->
        case spineOfTerm result of
          (CGlobal projector _, [(Expl, CRecordTQ fields), (Expl, focus)])
            | projector == prelProjector -> projectionRootPis 0 fields focus
          _ -> result

    projectionRootPis added [] focus = shiftTerm added 0 focus
    projectionRootPis added (field : fields) focus =
      CPiEvidenceM (rfMode field) (rfFormation field) Expl (rfQ field) False (rfName field)
        (rfLevelAssumption field)
        BinderSourceWritten
        (shiftTerm added 0 (rfType field))
        (projectionRootPis (added + 1) fields focus)

-- | Validate the complete occurrence-local telescope of the two
-- implementation-owned effect-tree constructors. They deliberately have no
-- source constructor-table entry, so their annotation may become typing
-- authority only after this identity-and-shape replay succeeds.
intrinsicEffectConstructorType
  :: EvalCtx
  -> Int
  -> GName
  -> Maybe Term
  -> [ConstructorArg]
  -> Maybe Value
intrinsicEffectConstructorType ctx depth constructor annotation arguments = do
  telescopeTerm <- annotation
  guard (termScopedAt depth telescopeTerm)
  let telescope = eval ctx (rigidEnvironment depth) telescopeTerm
  if constructor == prelEffPure
    then validatePure telescope
    else if constructor == prelEffOp
      then validateOperation telescope
      else Nothing
  pure telescope
  where
    validatePure telescope = case arguments of
      [payload] -> do
        (mode, icit, quantity, borrowed, domain, result) <- applyBinder telescope payload
        guard (mode == Ordinary && icit == Expl && quantity == Q1 && not borrowed)
        (_, payloadType) <- effectResult result
        guard (convertible ctx depth domain payloadType)
      _ -> Nothing

    validateOperation telescope = case arguments of
      [label, operation, payload, resume] -> do
        (labelMode, labelIcit, _, labelBorrowed, labelDomain, afterLabel) <- applyBinder telescope label
        guard (labelMode == Ordinary && labelIcit == Expl && not labelBorrowed)
        guard (plainGlobal labelDomain prelEffLabel)
        (operationMode, operationIcit, _, operationBorrowed, operationDomain, afterOperation) <-
          applyBinder afterLabel operation
        guard (operationMode == Ordinary && operationIcit == Expl && not operationBorrowed)
        guard (plainGlobal operationDomain prelString)
        (_, payloadIcit, _, payloadBorrowed, _, afterPayload) <- applyBinder afterOperation payload
        guard (payloadIcit == Expl && not payloadBorrowed)
        (resumeMode, resumeIcit, resumeQuantity, resumeBorrowed, resumeDomain, result) <-
          applyBinder afterPayload resume
        guard (resumeMode == Ordinary && resumeIcit == Expl && resumeQuantity == Q1 && not resumeBorrowed)
        (row, operationResult) <- effectResult result
        (resumeArgumentMode, resumeArgumentIcit, resumeArgumentQuantity, resumeArgumentBorrowed,
          resumeArgumentDomain, resumeResult) <- inspectBinder resumeDomain
        guard
          ( resumeArgumentMode == Ordinary
              && resumeArgumentIcit == Expl
              && resumeArgumentQuantity == Q1
              && not resumeArgumentBorrowed
          )
        guard (convertible ctx depth resumeArgumentDomain operationResult)
        guard (convertible ctx (depth + 1) resumeResult (shiftValue result))
        rowLabel <- singletonEffectRowLabel row
        let labelValue = eval ctx (rigidEnvironment depth) (caTerm label)
        guard (convertible ctx depth rowLabel labelValue)
      _ -> Nothing

    applyBinder functionType argument = do
      (mode, icit, quantity, borrowed, domain, Closure closureEnv codomain) <- splitBinder functionType
      guard (caIcit argument == icit)
      guard (termScopedAt depth (caTerm argument))
      let argumentValue = eval ctx (rigidEnvironment depth) (caTerm argument)
      pure
        ( mode
        , icit
        , quantity
        , borrowed
        , domain
        , eval ctx (argumentValue : closureEnv) codomain
        )

    inspectBinder functionType = do
      (mode, icit, quantity, borrowed, domain, Closure closureEnv codomain) <- splitBinder functionType
      let result = eval ctx (VRigid depth [] : closureEnv) codomain
      pure (mode, icit, quantity, borrowed, domain, result)

    splitBinder functionType = case force ctx functionType of
      VPiM mode icit quantity borrowed _ domain closure ->
        Just (mode, icit, quantity, borrowed, domain, closure)
      _ -> Nothing

    effectResult value = case force ctx value of
      VGlobN global [(_, row), (_, payload)]
        | global == prelEff -> Just (row, payload)
      _ -> Nothing

    singletonEffectRowLabel value = case force ctx value of
      VGlobN global [(_, label), (_, _interface), (_, tailRow)]
        | global == prelEffRowCons
        , plainGlobal tailRow prelEffRowNil -> Just label
      _ -> Nothing

    plainGlobal value global = case force ctx value of
      VGlobN actual [] -> actual == global
      _ -> False

    -- The result of the resumption Pi is quoted one binder deeper than the
    -- enclosing Eff result. Preserve that scope when comparing them.
    shiftValue = eval ctx (rigidEnvironment (depth + 1)) . shiftTerm 1 0 . quote ctx depth

-- | The single propagation predicate from §30.2.0. Keeping this exported
-- from the dependency-calculus module prevents finalized-definition checks
-- from approximating the application rule differently.
parametricCodomainPropagates :: EvalCtx -> Int -> ObservationMode -> Closure -> Bool
parametricCodomainPropagates ctx level mode (Closure closureEnv codomain) =
  mode == Parametric
    && ( mentionsTopBinder codomain
           || isParametricKindValue ctx (level + 1)
                (eval ctx (VRigid level [] : closureEnv) codomain)
       )

-- | Recover the checked explicit field telescope of a constructor pattern at
-- its actual scrutinee type. Constructor declarations are stored as generic Pi
-- telescopes, so merely taking their trailing explicit domains leaves family
-- parameters as fresh rigids. Aligning the constructor result with the
-- scrutinee first is what turns (for example) @Some : a -> Option a@ into a
-- field of the concrete @Outer@ type when matching @Option Outer@.
--
-- Failure is deliberate: callers are checkpoint validators and must not guess
-- field classifiers when the nominal result cannot be aligned.
constructorPatternObservationSites
  :: EvalCtx
  -> Bool
  -> Int
  -> Int
  -> Value
  -> Value
  -> Maybe [(ObservationMode, Value)]
constructorPatternObservationSites ctx allowProvisionalLevels depth fieldCount constructorType scrutineeType = do
  -- Constructor-local binders begin after the already-live scrutinee context.
  -- This is not cosmetic: GADT alignment may equate a constructor parameter
  -- with an outer rigid, so the two namespaces must never alias numerically.
  let (explicitSites, resultType) = collect depth constructorType
  substitution <- align Map.empty resultType scrutineeType
  pure
    [ (mode, substituteValue substitution domain)
    | (mode, domain) <- drop (max 0 (length explicitSites - fieldCount)) explicitSites
    ]
  where
    collect level value = case force ctx value of
      VPiM mode icit _ _ _ domain (Closure closureEnv codomain) ->
        let (rest, result) =
              collect (level + 1) (eval ctx (VRigid level [] : closureEnv) codomain)
         in ((if icit == Expl then [(mode, domain)] else []) ++ rest, result)
      result -> ([], result)

    align substitution patternValue actualValue =
      case
          ( force ctx (substituteValue substitution patternValue)
          , force ctx (substituteValue substitution actualValue)
          )
        of
        (VRigid level [], actual) -> bind level actual substitution
        (patternForced, VRigid level []) -> bind level patternForced substitution
        (VRigid level patternSpine, VRigid actualLevel actualSpine)
          | level == actualLevel -> alignSpines substitution patternSpine actualSpine
        (VFlex meta patternSpine, VFlex actualMeta actualSpine)
          | meta == actualMeta -> alignSpines substitution patternSpine actualSpine
        (VGlobal global levels patternSpine, VGlobal actualGlobal actualLevels actualSpine)
          | global == actualGlobal
          , allowProvisionalLevels || levels == actualLevels ->
              alignSpines substitution patternSpine actualSpine
        (VCtorI constructor levels patternArguments, VCtorI actualConstructor actualLevels actualArguments)
          | constructor == actualConstructor
          , allowProvisionalLevels || levels == actualLevels ->
              alignValues substitution
                (map cvaValue patternArguments)
                (map cvaValue actualArguments)
        (VRecordTQ patternFields, VRecordTQ actualFields)
          | map rfName patternFields == map rfName actualFields ->
              alignValues substitution
                (map rfType patternFields)
                (map rfType actualFields)
        (VVariantT patternMembers, VVariantT actualMembers) ->
          alignValues substitution patternMembers actualMembers
        (VInject patternTag patternPayload, VInject actualTag actualPayload)
          | patternTag == actualTag -> align substitution patternPayload actualPayload
        (VPrim patternPrimitive patternArguments, VPrim actualPrimitive actualArguments)
          | patternPrimitive == actualPrimitive ->
              alignValues substitution patternArguments actualArguments
        (VSort patternLevel, VSort actualLevel)
          | patternLevel == actualLevel -> Just substitution
        (VLevel patternLevel, VLevel actualLevel)
          | patternLevel == actualLevel -> Just substitution
        (VLit patternLiteral, VLit actualLiteral)
          | patternLiteral == actualLiteral -> Just substitution
        (patternForced, actualForced)
          | Just (patternGlobal, patternLevels, patternSpine) <-
              globalApplicationView patternForced
          , Just (actualGlobal, actualLevels, actualSpine) <-
              globalApplicationView actualForced
          , patternGlobal == actualGlobal
          , allowProvisionalLevels || patternLevels == actualLevels ->
              alignSpines substitution patternSpine actualSpine
        (patternForced, actualForced)
          | convertible ctx depth patternForced actualForced -> Just substitution
        _ -> Nothing

    alignSpines substitution patternSpine actualSpine
      | length patternSpine /= length actualSpine = Nothing
      | otherwise =
          foldl
            (\result ((patternIcit, patternArg), (actualIcit, actualArg)) -> do
                current <- result
                guard (patternIcit == actualIcit)
                align current patternArg actualArg)
            (Just substitution)
            (zip patternSpine actualSpine)

    alignValues substitution patternValues actualValues
      | length patternValues /= length actualValues = Nothing
      | otherwise =
          foldl
            (\result (patternValue, actualValue) ->
                result >>= \current -> align current patternValue actualValue)
            (Just substitution)
            (zip patternValues actualValues)

    -- Evaluation may represent the same neutral global application either as
    -- a 'VGlobal' carrying its spine or as nested 'VAppN' nodes around that
    -- global.  Constructor alignment is representation-independent: flatten
    -- both forms before comparing the authenticated global identity, universe
    -- arguments, icities, and semantic arguments.
    globalApplicationView = go []
      where
        go suffix = \case
          VAppN icit function argument ->
            go ((icit, argument) : suffix) function
          VGlobal global levels spine ->
            Just (global, levels, spine ++ suffix)
          _ -> Nothing

    bind level actual substitution =
      let actual' = substituteValue substitution actual
       in case actual' of
            VRigid actualLevel [] | actualLevel == level -> Just substitution
            _
              | rigidOccurs substitution level actual' -> Nothing
              | otherwise -> case Map.lookup level substitution of
                  Nothing -> Just (Map.insert level actual' substitution)
                  Just previous -> align substitution previous actual'

    -- The branch equations form a first-order rigid unifier. Reject recursive
    -- equations rather than manufacturing an infinite classifier (for example
    -- @i ~ F i@). Closures are inspected through their captured environments;
    -- object-language binders in the closure body cannot refer directly to an
    -- outer semantic level except through that environment.
    rigidOccurs substitution needle = go Set.empty
      where
        go seen value = case value of
          VRigid level spine ->
            level == needle
              || any (go seen . snd) spine
              || case Map.lookup level substitution of
                   Just replacement
                     | Set.notMember level seen -> go (Set.insert level seen) replacement
                   _ -> False
          VFlex _ spine -> any (go seen . snd) spine
          VGlobal _ _ spine -> any (go seen . snd) spine
          VLamM _ _ _ _ (Closure environment _) -> any (go seen) environment
          VPiEvidenceM _ _ _ _ _ _ _ _ domain (Closure environment _) ->
            go seen domain || any (go seen) environment
          VCtorI _ _ arguments -> any (go seen . cvaValue) arguments
          VRecordTQ fields -> any (go seen . rfType) fields
          VRecordV fields -> any (go seen . snd) fields
          VVariantT members -> any (go seen) members
          VInject _ payload -> go seen payload
          VMatchN scrutinee annotation _ environment ->
            go seen scrutinee || maybe False (go seen) annotation || any (go seen) environment
          VProjN _ receiver _ -> go seen receiver
          VAppN _ function argument -> go seen function || go seen argument
          VSealV _ inner -> go seen inner
          VSigT _ inner -> go seen inner
          VDoV _ _ environment -> any (go seen) environment
          VThunkV (Closure environment _) -> any (go seen) environment
          VLazyV (Closure environment _) -> any (go seen) environment
          VIfN condition (Closure yesEnvironment _) (Closure noEnvironment _) ->
            go seen condition || any (go seen) yesEnvironment || any (go seen) noEnvironment
          VPrim _ arguments -> any (go seen) arguments
          VIOAction _ arguments -> any (go seen) arguments
          VQuote _ slots -> any (go seen) slots
          VSort {} -> False
          VLevel {} -> False
          VLit {} -> False
          VRef {} -> False
          VArr {} -> False
          VMVar {} -> False
          VFiber {} -> False
          VScope {} -> False
          VFiberRef {} -> False
          VTVar {} -> False

    substituteValue substitution = go Set.empty
      where
        go resolving value = case value of
          VRigid level spine ->
            let spine' = [(icit, go resolving argument) | (icit, argument) <- spine]
             in case Map.lookup level substitution of
                  Just base
                    | Set.notMember level resolving ->
                        evalApp ctx (go (Set.insert level resolving) base) spine'
                  Nothing -> VRigid level spine'
                  _ -> VRigid level spine'
          VFlex meta spine -> VFlex meta [(icit, go resolving argument) | (icit, argument) <- spine]
          VGlobal global levels spine ->
            VGlobal global levels [(icit, go resolving argument) | (icit, argument) <- spine]
          VLamM mode icit quantity name closure ->
            VLamM mode icit quantity name (substituteClosure resolving closure)
          VPiEvidenceM mode formation icit quantity borrowed name assumption origin domain closure ->
            VPiEvidenceM mode formation icit quantity borrowed name assumption origin
              (go resolving domain) (substituteClosure resolving closure)
          VCtorI constructor levels arguments ->
            VCtorI constructor levels
              [argument {cvaValue = go resolving (cvaValue argument)} | argument <- arguments]
          VRecordTQ fields -> VRecordTQ (map (fmap (go resolving)) fields)
          VRecordV fields -> VRecordV [(name, go resolving field) | (name, field) <- fields]
          VVariantT members -> VVariantT (map (go resolving) members)
          VInject tag payload -> VInject tag (go resolving payload)
          VMatchN scrutinee annotation alternatives environment ->
            VMatchN (go resolving scrutinee) (go resolving <$> annotation)
              alternatives (map (go resolving) environment)
          VProjN mode receiver field -> VProjN mode (go resolving receiver) field
          VAppN icit function argument -> VAppN icit (go resolving function) (go resolving argument)
          VSealV labels inner -> VSealV labels (go resolving inner)
          VSigT labels inner -> VSigT labels (go resolving inner)
          VDoV label items environment -> VDoV label items (map (go resolving) environment)
          VThunkV closure -> VThunkV (substituteClosure resolving closure)
          VLazyV closure -> VLazyV (substituteClosure resolving closure)
          VIfN condition yes no ->
            VIfN (go resolving condition) (substituteClosure resolving yes) (substituteClosure resolving no)
          VPrim primitive arguments -> VPrim primitive (map (go resolving) arguments)
          VIOAction primitive arguments -> VIOAction primitive (map (go resolving) arguments)
          VQuote syntax slots -> VQuote syntax (map (go resolving) slots)
          VSort {} -> value
          VLevel {} -> value
          VLit {} -> value
          VRef {} -> value
          VArr {} -> value
          VMVar {} -> value
          VFiber {} -> value
          VScope {} -> value
          VFiberRef {} -> value
          VTVar {} -> value

        substituteClosure resolving (Closure environment body) =
          Closure (map (go resolving) environment) body

observationDependencies :: ObservationOracle -> [ObservationBinding] -> Maybe Value -> Term -> DependencySet
observationDependencies oracle bindings expected = go [] bindings expected
  where
    ctx = ooEvalCtx oracle

    child :: [Int] -> Int -> [Int]
    child path index = index : path

    originPath :: [Int] -> [Int]
    originPath = reverse

    bindingDependencies path index env =
      case drop index env of
        -- Lambda/pattern binders only carry an origin when they are
        -- parametric. Let-bound definitions additionally carry a structural
        -- substitution identity even when their declared mode is ordinary;
        -- this makes the §30.2.0 zeta equation hold for known helpers.
        ObservationBinding {obOrigin = Just origin} : _ -> Set.singleton origin
        ObservationBinding {} : _ -> Set.empty
        _ ->
          analysisFailure path
            ( "local binding identity " <> Text.pack (show index)
                <> " is outside the supplied typed environment of size "
                <> Text.pack (show (length env))
            )

    analysisFailure path reason =
      Set.singleton (ParametricAnalysisFailure (originPath path) reason)

    directLevelDependencies path env term =
      Set.unions
        [ levelDependencies (child path index) env level
        | (index, level) <- zip [0 ..] (termNodeLevels term)
        ]

    levelDependencies path env = \case
      LZero -> Set.empty
      LFinite _ -> Set.empty
      LOmega -> Set.empty
      LSucc level -> levelDependencies (child path 0) env level
      LAdd left right ->
        levelDependencies (child path 0) env left
          `Set.union` levelDependencies (child path 1) env right
      LMax left right ->
        levelDependencies (child path 0) env left
          `Set.union` levelDependencies (child path 1) env right
      LVar level -> localLevelDependencies path env level []
      LProjection level fields -> localLevelDependencies path env level fields
      LParam _ -> Set.empty
      LField _ field -> Set.singleton (ParametricThisProjection (originPath path) field)
      LNeutral atom -> neutralAtomDependencies path env atom
      LMeta meta -> Set.singleton (ParametricMeta meta)

    localLevelDependencies path env level fields =
      let index = length env - level - 1
          rootDependencies =
            if index < 0 || index >= length env
              then analysisFailure path
                ("level-local identity " <> Text.pack (show level)
                  <> " is outside the supplied typed environment of size "
                  <> Text.pack (show (length env)))
              else bindingDependencies path index env
       in if Set.null rootDependencies && not (null fields)
            then projectedLevelDependencies path env index fields
            else rootDependencies

    projectedLevelDependencies path env index fields =
      case drop index env of
        ObservationBinding {obType = Just rootType} : _ -> walk rootType fields
        _ -> analysisFailure path "a projected level root has no authenticated classifier"
      where
        walk _ [] = Set.empty
        walk receiverType (field : rest) =
          let mode = ooProjectionMode oracle receiverType field
              here = case mode of
                Just Parametric ->
                  Set.singleton
                    (ParametricProjection (originPath path) (Text.intercalate "." fields))
                Just Ordinary -> Set.empty
                Nothing -> analysisFailure path
                  ("observation mode is unavailable for TypeLevel projection '" <> field <> "'")
           in if not (Set.null here) || null rest
                then here
                else case projectionType (length env) receiverType field of
                  Just nextType -> walk nextType rest
                  Nothing -> analysisFailure path
                    ("classifier is unavailable for nested TypeLevel projection '" <> field <> "'")

    neutralAtomDependencies path env = \case
      NeutralLevelTermAtom _ term -> neutralTermDependencies path env term
      NeutralLevelSymbol identity arguments ->
        analysisFailure path
          ("solver-only neutral level symbol escaped typed Core: " <> identity)
          `Set.union` Set.unions
            [levelDependencies (child path index) env argument | (index, argument) <- zip [0 ..] arguments]

    neutralTermDependencies path env = \case
      NLTLocal level -> localLevelDependencies path env level []
      NLTLocalDeclaration level universes ->
        localLevelDependencies path env level []
          `Set.union` Set.unions
            [levelDependencies (child path index) env universe | (index, universe) <- zip [0 ..] universes]
      NLTGlobal owner name universes ->
        let global = GName (ModuleName owner) name
            headDependencies = case ooGlobalMode oracle global of
              Just Parametric -> Set.singleton (ParametricGlobal global)
              Just Ordinary -> Set.empty
              Nothing -> analysisFailure path
                ("global observation metadata is unavailable for level term " <> gnameText global)
         in headDependencies `Set.union` Set.unions
              [levelDependencies (child path index) env universe | (index, universe) <- zip [0 ..] universes]
      NLTConstruct _ _ universes arguments ->
        Set.unions
          ( [levelDependencies (child path index) env universe | (index, universe) <- zip [0 ..] universes]
              ++ [neutralTermDependencies (child path (length universes + index)) env argument
                 | (index, (_, argument)) <- zip [0 ..] arguments]
          )
      NLTApply _ function argument ->
        neutralTermDependencies (child path 0) env function
          `Set.union` neutralTermDependencies (child path 1) env argument
      NLTProject _ receiver -> neutralTermDependencies (child path 0) env receiver
      NLTLevel level -> levelDependencies (child path 0) env level
      NLTLiteral _ -> Set.empty
      NLTRecord fields -> Set.unions
        [neutralTermDependencies (child path index) env value | (index, (_, value)) <- zip [0 ..] fields]
      NLTIf condition thenBranch elseBranch ->
        Set.unions
          [ neutralTermDependencies (child path 0) env condition
          , neutralTermDependencies (child path 1) env thenBranch
          , neutralTermDependencies (child path 2) env elseBranch
          ]
      NLTUnsupported reason -> analysisFailure path
        ("unsupported neutral level term escaped typed Core: " <> reason)

    preserveBarriers = Set.filter $ \case
      ParametricReflection {} -> True
      ParametricAnalysisFailure {} -> True
      _ -> False

    bindingDefinition index env =
      case drop index env of
        ObservationBinding {obDefinition = Just (definitionDepth, body)} : _ ->
          Just (shiftTerm (length env - definitionDepth) 0 body)
        _ -> Nothing

    disableBindingDefinition index = goDisable index
      where
        goDisable _ [] = []
        goDisable 0 (binding : rest) = binding {obDefinition = Nothing} : rest
        goDisable remaining (binding : rest) =
          binding : goDisable (remaining - 1) rest

    inferAt env term =
      case ooInferType oracle (length env) env term of
        Just inferred -> Just inferred
        Nothing -> inferStructural env term

    -- A surviving KBind is a kernel bind. Its pattern sees the payload of the
    -- action, not the action carrier itself. User monads have already been
    -- elaborated through their selected bind dictionary before Core.
    kernelActionResult value = case force ctx value of
      VGlobI global _ [(_, _errorType), (_, resultType)]
        | global == prelIO -> Just resultType
      VGlobI global _ [(_, resultType)]
        | global == prelSTM -> Just resultType
      _ -> Nothing

    -- Builtin reference witnesses authenticate checker-generated MonadRef
    -- actions. The explicit element-type argument is therefore typed Core
    -- authority for the payload of readRef even when generic trait projection
    -- typing cannot reconstruct an intermediate local reference classifier.
    witnessedReadResult env witness action = case (witness, spineOfTerm action) of
      (Just BuiltinIORefRead {}, (CProjM Ordinary _ _, (Impl, elementType) : _))
        | termScopedAt (length env) elementType ->
            Just (eval ctx (rigidEnv (length env)) elementType)
      _ -> Nothing

    inferStructural env application@CApp {} =
      let (headTerm, arguments) = spineOfTerm application
       in case betaApply (length env) headTerm arguments of
            Just reduced -> inferAt env reduced
            Nothing -> Nothing
    inferStructural _ (CGlobal global _)
      | global == prelThis = ooThisType oracle
    inferStructural env (CProjM _ receiver field) = do
      receiverType <- inferAt env receiver
      projectionType (length env) receiverType field
    inferStructural env (CProjAtM _ receiver field _) = do
      receiverType <- inferAt env receiver
      projectionType (length env) receiverType field
    inferStructural env (CCtorI _ _ (Just annotation) arguments)
      | termScopedAt (length env) annotation =
          applyConstructorType env
            (eval ctx (rigidEnv (length env)) annotation)
            arguments
    inferStructural env (CMeta meta) = do
      solution <- Map.lookup meta (ecMetas ctx) >>= id
      let solutionTerm = quote ctx (length env) solution
      guard (solutionTerm /= CMeta meta)
      inferAt env solutionTerm
    inferStructural _ _ = Nothing

    projectionType depth receiverType field =
      case force ctx receiverType of
        VRecordTQ fields -> rfType <$> find ((== field) . rfName) fields
        VSigT _ inner -> projectionType depth inner field
        _ -> ooProjectionType oracle depth receiverType field

    betaApply _ term [] = Just term
    betaApply depth (CLamM _ expectedIcit _ _ body) ((actualIcit, argument) : rest)
      | actualIcit == expectedIcit =
          betaApply depth (substTopTermAt depth argument body) rest
    betaApply _ _ _ = Nothing

    applyConstructorType _ functionType [] = Just functionType
    applyConstructorType env functionType (argument : rest) =
      case force ctx functionType of
        VPiM _ expectedIcit _ _ _ _ (Closure closureEnv codomain)
          | caIcit argument == expectedIcit ->
              let argumentValue = eval ctx (rigidEnv (length env)) (caTerm argument)
               in applyConstructorType env (eval ctx (argumentValue : closureEnv) codomain) rest
        _ -> Nothing

    -- Observation dependencies are invariant under ordinary computation.
    -- Reduce only closed, well-scoped Boolean conditions here; an open or
    -- malformed condition keeps the conservative branch join below.
    closedBoolean env term
      | termScopedAt (length env) term =
          case force ctx (eval ctx (rigidEnv (length env)) term) of
            VCtor constructor []
              | constructor == prelTrue -> Just True
              | constructor == prelFalse -> Just False
            _ -> Nothing
      | otherwise = Nothing

    binderAt path name mode ty =
      ObservationBinding mode
        (if mode == Parametric then Just (ParametricBinder (originPath path) name) else Nothing)
        ty
        Nothing
        Nothing

    go path env wanted term =
      directLevelDependencies path env term `Set.union` case term of
      CVar index -> bindingDependencies path index env
      CLocal index _ -> bindingDependencies path index env
      CGlobal global _
        | global == prelThis -> Set.empty
        | Just Parametric <- ooGlobalMode oracle global -> Set.singleton (ParametricGlobal global)
        | Just Ordinary <- ooGlobalMode oracle global -> Set.empty
        | otherwise -> analysisFailure path "global observation metadata is unavailable"
      CLamM mode icit _ name body ->
        let origin = ParametricBinder (originPath (child path 0)) name
            (domain, bodyExpected) = lambdaExpected env mode icit wanted
            binding = ObservationBinding mode (if mode == Parametric then Just origin else Nothing) domain Nothing Nothing
         in Set.delete origin (go (child path 1) (binding : env) bodyExpected body)
      CPiEvidenceM mode _ _ _ _ name _ _ domain codomain ->
        let domainDeps = go (child path 0) env Nothing domain
            domainType = Just (eval ctx (rigidEnv (length env)) domain)
            origin = ParametricBinder (originPath (child path 1)) name
            binding = ObservationBinding mode (if mode == Parametric then Just origin else Nothing) domainType Nothing Nothing
            codomainDeps = Set.delete origin (go (child path 2) (binding : env) Nothing codomain)
         in domainDeps `Set.union` codomainDeps
      application@CApp {} -> applicationDependencies path env wanted application
      CSort _ -> Set.empty
      CLevel _ -> Set.empty
      CUniverseLift _ _ _ inner -> go (child path 0) env wanted inner
      CSchemaLift _ _ _ _ _ _ _ _ inner -> go (child path 0) env wanted inner
      CLit _ -> Set.empty
      CCtorI constructor universes annotation arguments ->
        constructorDependencies path env constructor (Just universes) annotation arguments
      CMatch scrutinee annotation alternatives ->
        matchDependencies path env wanted scrutinee annotation alternatives
      -- Constructing Sigma/static record code is not a package-construction
      -- sealing boundary. Field modes govern values supplied to CRecordV;
      -- dependencies of every field TYPE remain observable components of the
      -- resulting code (§30.2.0, "Pi, Sigma, and other static code").
      CRecordTQ fields ->
        let localParametricFields =
              Set.fromList
                [rfName field | field <- fields, rfMode field == Parametric]
            thisType = eval ctx (rigidEnv (length env)) (CRecordTQ fields)
            dependencies = Set.unions
              [ prefixDependencies (originPath (child path index)) $
                  observationDependencies
                    oracle {ooThisType = Just thisType}
                    env
                    Nothing
                    (rfType field)
              | (index, field) <- zip [0 ..] fields
              ]
         in Set.filter
              (\case
                 ParametricThisProjection _ field ->
                   field `Set.notMember` localParametricFields
                 _ -> True)
              dependencies
      CRecordV fields -> recordDependencies path env wanted fields
      CProjM mode receiver field -> projectionDependencies path env mode receiver field Nothing
      CProjAtM mode receiver field index -> projectionDependencies path env mode receiver field (Just index)
      CVariantT members -> Set.unions
        [go (child path index) env Nothing member | (index, member) <- zip [0 ..] members]
      CInject _ value -> go (child path 0) env Nothing value
      CLetM mode _ name ty rhs body ->
        let rhsDeps = go (child path 0) env (Just (eval ctx (rigidEnv (length env)) ty)) rhs
            origin = ParametricBinder (originPath (child path 1)) name
            binding = ObservationBinding mode (Just origin)
                        (Just (eval ctx (rigidEnv (length env)) ty))
                        Nothing
                        (Just (length env, rhs))
            bodyDeps = go (child path 2) (binding : env) wanted body
         in substituteOrigin origin rhsDeps bodyDeps
      CLetRecM mode _ name ty rhs body ->
        let origin = ParametricBinder (originPath (child path 0)) name
            tyValue = eval ctx (rigidEnv (length env)) ty
            binding = ObservationBinding mode (Just origin) (Just tyValue)
                        Nothing
                        (Just (length env + 1, rhs))
            rhsDeps0 = go (child path 1) (binding : env) (Just tyValue) rhs
            rhsDeps = Set.delete origin rhsDeps0
            bodyDeps = go (child path 2) (binding : env) wanted body
         in substituteOrigin origin rhsDeps bodyDeps
      CLetPolyM mode _ name telescope ty rhs body ->
        let rhsDeps = go (child path 0) env (Just (eval ctx (rigidEnv (length env)) ty)) rhs
            origin = ParametricBinder (originPath (child path 1)) name
            binding = ObservationBinding mode (Just origin)
                        (Just (eval ctx (rigidEnv (length env)) ty))
                        (Just telescope)
                        (Just (length env, rhs))
            bodyDeps = go (child path 2) (binding : env) wanted body
         in substituteOrigin origin rhsDeps bodyDeps
      CLetRecPolyM mode _ name telescope ty rhs body ->
        let origin = ParametricBinder (originPath (child path 0)) name
            tyValue = eval ctx (rigidEnv (length env)) ty
            binding = ObservationBinding mode (Just origin) (Just tyValue)
                        (Just telescope)
                        (Just (length env + 1, rhs))
            rhsDeps0 = go (child path 1) (binding : env) (Just tyValue) rhs
            rhsDeps = Set.delete origin rhsDeps0
            bodyDeps = go (child path 2) (binding : env) wanted body
         in substituteOrigin origin rhsDeps bodyDeps
      CLetRecGroupM telescope definitions body ->
        let base = length env
            indexed = zip [0 ..] definitions
            members =
              [ let origin = ParametricBinder (originPath (child path index)) (clrdName definition)
                    tyValue = eval ctx (rigidEnv base) (clrdType definition)
                 in (definition, origin, ObservationBinding (clrdMode definition)
                       (Just origin)
                       (Just tyValue)
                       (Just telescope)
                       (Just (base + length definitions, clrdRhs definition)))
              | (index, definition) <- indexed
              ]
            recursiveEnv = reverse [binding | (_, _, binding) <- members] ++ env
            origins = Set.fromList [origin | (_, origin, _) <- members]
            direct =
              Map.fromList
                [ ( origin
                  , go (child path (length definitions + index)) recursiveEnv
                      (Just (eval ctx (rigidEnv base) (clrdType definition)))
                      (clrdRhs definition)
                  )
                | (index, (definition, origin, _)) <- zip [0 ..] members
                ]
            close currentSummaries =
              let expand dependencies =
                    Set.unions
                      ( Set.difference dependencies origins
                          : [Map.findWithDefault Set.empty origin currentSummaries | origin <- Set.toList (Set.intersection dependencies origins)]
                      )
                  next = Map.map expand direct
               in if next == currentSummaries then currentSummaries else close next
            summaries = close (Map.map (`Set.difference` origins) direct)
            bodyDeps = go (child path (2 * length definitions)) recursiveEnv wanted body
         in foldl
              (\dependencies (origin, replacement) -> substituteOrigin origin replacement dependencies)
              bodyDeps
              (Map.toList summaries)
      -- An inference meta inherits observation from its authenticated
      -- creation-site classifier. Ordinary erased indices are not parametric
      -- witnesses merely because they remain flexible in finalized Core.
      -- Missing classifier provenance remains fail-closed.
      CMeta meta -> case ooMetaMode oracle meta of
        Just Ordinary -> Set.empty
        _ -> Set.singleton (ParametricMeta meta)
      CDo _ items -> doDependencies path env items
      CSealE _ value -> go (child path 0) env wanted value
      CSigT _ value -> go (child path 0) env Nothing value
      CThunkE value -> go (child path 0) env Nothing value
      CLazyE value -> go (child path 0) env Nothing value
      CForceE value -> go (child path 0) env wanted value
      CIf condition yes no ->
        let conditionDeps = go (child path 0) env Nothing condition
         in conditionDeps `Set.union` case closedBoolean env condition of
              Just True -> go (child path 1) env wanted yes
              Just False -> go (child path 2) env wanted no
              Nothing ->
                go (child path 1) env wanted yes
                  `Set.union` go (child path 2) env wanted no
      CQuote _ slots ->
        let dependencies = Set.unions
              [go (child path index) env Nothing slot | (index, slot) <- zip [0 ..] slots]
         in if Set.null dependencies
              then Set.empty
              else Set.insert (ParametricReflection (originPath path)) dependencies

    applicationDependencies path env wanted application =
      let (headTerm, arguments) = spineOfTerm application
          headType = observationCallableType ctx (length env) <$> inferAt env headTerm
          rawDependencies = case betaApply (length env) headTerm arguments of
            -- Eta-expanded constructor values are a definitional presentation
            -- detail.  Analyze the saturated constructor application itself so
            -- its checked telescope supplies every argument domain.  This is
            -- also the beta-preservation equation required by §30.2.0; keeping
            -- the lambda-shaped presentation here loses the domain of record
            -- arguments because Core lambdas do not duplicate Pi annotations.
            Just reduced@CCtorI {} -> go path env wanted reduced
            _ -> case headTerm of
              CLamM {} -> lambdaApplicationDependencies path env env headType headTerm arguments 0
              CGlobal global _
                | global `Set.member` ooExpandingGlobals oracle ->
                    -- Recursive observation equations are unions of finite
                    -- origins.  A back-edge contributes the current bottom
                    -- approximation; dependencies reached before that edge
                    -- remain in the surrounding analysis.  The resolved
                    -- global mode is retained so a genuinely parametric
                    -- global cannot be made ordinary by transparency.
                    go (child path 0) env Nothing headTerm
              CGlobal global _
                | global == prelHandleEff ->
                    fromMaybe
                      (applicationDependenciesRaw path env application)
                      (intrinsicHandlerDependencies path env arguments)
              CGlobal global _
                | Just body <- ooGlobalBody oracle global
                , globalBodyIsRecursive global body ->
                    case betaApply (length env) body arguments of
                      Just reduced ->
                        observationDependencies
                          oracle
                            { ooExpandingGlobals =
                                Set.insert global (ooExpandingGlobals oracle)
                            }
                          env
                          wanted
                          reduced
                      Nothing -> applicationDependenciesRaw path env application
              CGlobal global _
                | Just body <- ooGlobalBody oracle global
                , not (globalBodyIsRecursive global body) ->
                    -- A finalized nonrecursive body is stronger authority than
                    -- syntactic dependency in its telescope. Opaque/external
                    -- and recursive globals retain the fail-closed type path.
                    -- Recursion is an SCC property: checking only whether the
                    -- body mentions itself lets mutually recursive globals
                    -- inline each other without bound.
                    case body of
                      CLamM {} -> lambdaApplicationDependencies path env env headType body arguments 0
                      _ -> applicationDependenciesRaw path env application
              CGlobal global _
                | ooGlobalPrimitive oracle global ->
                    fromMaybe
                      (applicationDependenciesRaw path env application)
                      (primitiveRuntimeApplicationDependencies
                        path env headTerm headType arguments)
              CLocal index _
                | Just body <- bindingDefinition index env ->
                    case body of
                      CLamM {} ->
                        lambdaApplicationDependencies
                          path
                          (disableBindingDefinition index env)
                          (disableBindingDefinition index env)
                          headType body arguments 0
                      _ -> applicationDependenciesRaw path env application
              CVar index
                | Just body <- bindingDefinition index env ->
                    case body of
                      CLamM {} ->
                        lambdaApplicationDependencies
                          path
                          (disableBindingDefinition index env)
                          (disableBindingDefinition index env)
                          headType body arguments 0
                      _ -> applicationDependenciesRaw path env application
              _ -> applicationDependenciesRaw path env application
       in maybe rawDependencies
            (\callable ->
              evidenceRelativeCallableDependencies
                ctx (length env) callable rawDependencies)
            headType

    -- __handleEff is a checked KCore form represented as an internal primitive
    -- application. Its public primitive signature is intentionally only an
    -- unnameable placeholder, so generic Pi-spine recovery is not authority
    -- for these five elaborator-produced runtime arguments. A saturated form
    -- does not observe the static types used to check the handler interface;
    -- reflection and analysis barriers remain visible.
    intrinsicHandlerDependencies path env arguments = do
      guard (length arguments == 5)
      guard (all ((== Expl) . fst) arguments)
      let labelTerm = snd (arguments !! 1)
      labelType <- ooInferType oracle (length env) env labelTerm
      case force ctx labelType of
        VGlobI global _ [] -> guard (global == prelEffLabel)
        _ -> Nothing
      pure $ Set.unions
        [ Set.filter isReflection
            (go (child path (index + 1)) env Nothing argument)
        | (index, (_, argument)) <- zip [0 ..] arguments
        ]
      where
        isReflection ParametricReflection {} = True
        isReflection _ = False

    -- Does expanding @start@ lead back to @start@ through the oracle's
    -- finalized transparent bodies? The walk is identity-based and finite;
    -- opaque/external edges simply stop. An acyclic helper may therefore still
    -- normalize through renames/eta wrappers, while every member of a direct
    -- or mutual recursive SCC keeps the typed application rule.
    globalBodyIsRecursive start initialBody = reaches Set.empty (globalsOfTerm initialBody)
      where
        reaches visited frontier
          | start `Set.member` frontier = True
          | otherwise =
              any follows
                (Set.toList (Set.difference frontier visited))
          where
            follows global =
              case ooGlobalBody oracle global of
                Nothing -> False
                Just body ->
                  reaches (Set.insert global visited) (globalsOfTerm body)

    -- A lambda does not carry its domain in Core, so the declaration/checking
    -- classifier is the only typed authority available to the dependency
    -- calculus.  Preserve that Pi telescope while descending; otherwise a
    -- projected method head inside the body becomes untypable and the
    -- fail-closed application rule spuriously retains every argument.
    lambdaExpected env mode icit wanted =
      case force ctx . observationCallableType ctx (length env) <$> wanted of
        Just (VPiM expectedMode expectedIcit _ _ _ domain (Closure closureEnv codomain))
          | mode == expectedMode
          , icit == expectedIcit ->
              let binder = VRigid (length env) []
               in (Just domain, Just (eval ctx (binder : closureEnv) codomain))
        _ -> (Nothing, Nothing)

    -- Evaluate beta dependency by the normative substitution equation instead
    -- of substituting (and potentially duplicating) the argument term. This is
    -- stable for eta-expanded constructors and cannot execute local recursion.
    lambdaApplicationDependencies path bodyEnv _argumentEnv functionType term [] _ =
      go path bodyEnv functionType term
    lambdaApplicationDependencies path bodyEnv argumentEnv functionType term arguments@((actualIcit, argument) : rest) offset =
      case term of
        CLamM mode expectedIcit _ name body
          | actualIcit == expectedIcit ->
              let lambdaPath = child path (2 * offset)
                  argumentPath = child path (2 * offset + 1)
                  origin = ParametricBinder (originPath (child lambdaPath 0)) name
                  (domain, bodyType) =
                    lambdaApplicationExpected argumentEnv mode expectedIcit functionType argument
                  binding =
                    ObservationBinding mode
                      (if mode == Parametric then Just origin else Nothing)
                      domain
                      Nothing
                      Nothing
                  argumentDeps = go argumentPath argumentEnv domain argument
                  bodyDeps =
                    lambdaApplicationDependencies
                      (child lambdaPath 1)
                      (binding : bodyEnv)
                      argumentEnv
                      bodyType
                      body
                      rest
                      (offset + 1)
               in substituteOrigin origin argumentDeps bodyDeps
        _ ->
          applicationDependenciesMixed
            path bodyEnv argumentEnv functionType term arguments

    -- A transparent lambda body and the arguments supplied at its occurrence
    -- live in different de Bruijn environments.  The body scope grows as its
    -- binders are exposed; every call-site argument remains scoped in the
    -- original occurrence environment.  Specialize the maintained Pi type
    -- with the argument evaluated in that occurrence environment rather than
    -- interpreting it under the growing body telescope.
    lambdaApplicationExpected argumentEnv mode icit functionType argument =
      case force ctx . observationCallableType ctx (length argumentEnv) <$> functionType of
        Just (VPiM expectedMode expectedIcit _ _ _ domain (Closure closureEnv codomain))
          | mode == expectedMode
          , icit == expectedIcit
          , termScopedAt (length argumentEnv) argument ->
              let argumentValue = eval ctx (rigidEnv (length argumentEnv)) argument
               in (Just domain, Just (eval ctx (argumentValue : closureEnv) codomain))
        _ -> (Nothing, Nothing)

    -- Once beta analysis reaches a non-lambda body, its supplied type is the
    -- authoritative classifier of that body expression.  Analyze the body in
    -- body scope, then walk only the remaining external arguments in their
    -- call-site scope; constructing one synthetic application would combine
    -- incompatible de Bruijn environments.
    applicationDependenciesMixed path bodyEnv argumentEnv functionType term arguments =
      let headDeps = go (child path 0) bodyEnv functionType term
       in walkArguments path argumentEnv (applicationHeadFailure term) headDeps functionType arguments 0

    applicationDependenciesRaw path env application =
      let (headTerm, arguments) = spineOfTerm application
          headDeps = go (child path 0) env Nothing headTerm
          headType = observationCallableType ctx (length env) <$> inferAt env headTerm
          typedHeadDeps = case (headTerm, headType) of
            (CVar index, Nothing) ->
              analysisFailure path
                ("application head local type is unavailable at index "
                  <> Text.pack (show index)
                  <> " in an observation environment of size "
                  <> Text.pack (show (length env))
                  <> maybe " (binding is out of scope)"
                    (\binding -> if isNothing (obType binding)
                      then " (binding has no recorded type)"
                      else " (recorded type could not be applied)")
                    (listAt index env))
            (CLocal index universes, Nothing) ->
              analysisFailure path
                ("universe-specialized application head type is unavailable at index "
                  <> Text.pack (show index)
                  <> " with "
                  <> Text.pack (show (length universes))
                  <> " universe arguments in an observation environment of size "
                  <> Text.pack (show (length env))
                  <> maybe " (binding is out of scope)"
                    (\binding -> case (obType binding, obUniverses binding) of
                      (Nothing, _) -> " (binding has no recorded type)"
                      (_, Nothing) -> " (binding has no recorded universe telescope)"
                      (Just _, Just telescope) ->
                        " (recorded telescope expects "
                          <> Text.pack (show (dutParameterCount telescope))
                          <> " universe arguments)")
                    (listAt index env))
            _ -> Set.empty
       in walkArguments path env (applicationHeadFailure headTerm)
            (headDeps `Set.union` typedHeadDeps) headType arguments 0

    -- Implementation primitives receive erased parametric arguments only as
    -- compile-time specialization inputs.  Once fully saturated to a runtime
    -- classifier, those inputs cannot be observed by the generated runtime
    -- operation; only explicit reflection/analysis barriers remain.  A partial
    -- application, static result, malformed spine, or out-of-scope argument
    -- falls back to the general §30.2.0 application equation.
    primitiveRuntimeApplicationDependencies path env headTerm headType arguments = do
      functionType <- headType
      barriers <- walkPrimitive functionType arguments 0 Set.empty
      pure (go (child path 0) env Nothing headTerm `Set.union` barriers)
      where
        walkPrimitive functionType [] _ barriers = case force ctx functionType of
          VPiM {} -> Nothing
          result
            | isParametricKindValue ctx (length env) result -> Nothing
            | otherwise -> Just barriers
        walkPrimitive functionType ((actualIcit, argument) : rest) offset barriers =
          case force ctx functionType of
            VPiM _ expectedIcit _ _ _ _ (Closure closureEnv codomain)
              | actualIcit == expectedIcit
              , termScopedAt (length env) argument ->
                  let argumentDeps =
                        go (child path (offset + 1)) env Nothing argument
                      argumentValue = eval ctx (rigidEnv (length env)) argument
                      resultType = eval ctx (argumentValue : closureEnv) codomain
                   in walkPrimitive resultType rest (offset + 1)
                        (barriers `Set.union` preserveBarriers argumentDeps)
            _ -> Nothing

    listAt index values = case drop index values of
      value : _ -> Just value
      [] -> Nothing

    applicationHeadFailure = \case
      CLocal index universes ->
        "universe-specialized local at index " <> Text.pack (show index)
          <> " with " <> Text.pack (show (length universes)) <> " universe arguments"
      CVar index -> "local at index " <> Text.pack (show index)
      CGlobal global universes ->
        "global " <> gnameText global
          <> " with " <> Text.pack (show (length universes)) <> " universe arguments"
      CLamM {} -> "lambda"
      CProjM _ _ field -> "projection ." <> field
      CProjAtM _ _ field _ -> "indexed projection ." <> field
      CMeta meta -> "metavariable ?" <> Text.pack (show meta)
      _ -> "unsupported Core head form"

    walkArguments _ _ _ accumulated _ [] _ = accumulated
    walkArguments path env unavailableHead accumulated Nothing arguments offset =
      let argumentDependencies =
            [ go (child path (offset + index + 1)) env Nothing argument
            | (index, (_, argument)) <- zip [0 ..] arguments
            ]
          known = accumulated `Set.union` Set.unions argumentDependencies
          established = Set.filter (\case ParametricMeta {} -> False; _ -> True) known
       in if Set.null established
            then known
            else if any dependencyIsAnalysisFailure (Set.toList known)
              then known
            else known `Set.union` analysisFailure path
              ("application head type is unavailable for " <> unavailableHead)
    walkArguments path env unavailableHead accumulated (Just functionType) ((actualIcit, argument) : rest) offset =
      case force ctx functionType of
        VPiM mode expectedIcit _ _ _name domain (Closure closureEnv codomain)
          | actualIcit == expectedIcit ->
              let argumentPath = child path (offset + 1)
                  argumentDeps = go argumentPath env (Just domain) argument
                  propagated
                    | mode == Ordinary = Set.empty
                    | parametricCodomainPropagates ctx (length env) mode (Closure closureEnv codomain) = argumentDeps
                    | otherwise = preserveBarriers argumentDeps
                  accumulated' = accumulated `Set.union` propagated
               in if termScopedAt (length env) argument
                    then
                      let argumentValue = eval ctx (rigidEnv (length env)) argument
                          resultType = eval ctx (argumentValue : closureEnv) codomain
                       in walkArguments path env unavailableHead accumulated' (Just resultType) rest (offset + 1)
                    else
                      -- A recovery term outside the supplied local telescope
                      -- cannot safely specialize a dependent codomain. Retain
                      -- the dependencies already proved and analyze every
                      -- remaining argument conservatively.
                      walkArguments path env unavailableHead accumulated' Nothing rest (offset + 1)
        _ ->
          walkArguments path env unavailableHead accumulated Nothing
            ((actualIcit, argument) : rest) offset

    constructorDependencies path env constructor universes annotation arguments =
      let constructorType =
            ooConstructorType oracle constructor universes
              <|> intrinsicEffectConstructorType ctx (length env) constructor annotation arguments
       in case constructorType of
            Just typed -> walkDeclaredConstructor path env typed arguments 0
            Nothing -> Set.unions
              [ analysisFailure path "constructor observation telescope is missing, malformed, or has the wrong arity"
              , Set.unions
                  [go (child path index) env Nothing (caTerm argument) | (index, argument) <- zip [0 ..] arguments]
              ]

    walkDeclaredConstructor _ _ functionType [] _ =
      case force ctx functionType of
        VPiM {} -> analysisFailure [] "constructor application has too few arguments"
        _ -> Set.empty
    walkDeclaredConstructor path env functionType (constructorArgument : rest) index =
      case force ctx functionType of
        VPiM mode expectedIcit _ _ _ domain (Closure closureEnv codomain)
          | caIcit constructorArgument == expectedIcit ->
              let argument = caTerm constructorArgument
                  argumentPath = child path index
                  dependencies = go argumentPath env (Just domain) argument
                  retained = if mode == Parametric then preserveBarriers dependencies else dependencies
               in if termScopedAt (length env) argument
                    then
                      let argumentValue = eval ctx (rigidEnv (length env)) argument
                          resultType = eval ctx (argumentValue : closureEnv) codomain
                       in retained
                            `Set.union` walkDeclaredConstructor path env resultType rest (index + 1)
                    else retained
                      `Set.union` analysisFailure argumentPath
                        "constructor argument is outside the supplied local telescope"
                      `Set.union` Set.unions
                        [go (child path later) env Nothing (caTerm remaining)
                        | (later, remaining) <- zip [index + 1 ..] rest
                        ]
        _ -> Set.unions
          [ analysisFailure (child path index)
              "constructor observation telescope has the wrong arity or icity"
          , Set.unions
              [go (child path later) env Nothing (caTerm remaining)
              | (later, remaining) <- zip [index ..] (constructorArgument : rest)
              ]
          ]

    recordDependencies path env wanted fields =
      case wanted >>= forceRecordType of
        Just declared -> Set.unions
          [ case find ((== name) . rfName) declared of
              Just field
                | rfMode field == Parametric ->
                    preserveBarriers (go (child path index) env (Just (rfType field)) value)
                | otherwise -> go (child path index) env (Just (rfType field)) value
              Nothing ->
                analysisFailure (child path index) "record field is absent from its typed interface"
                  `Set.union` go (child path index) env Nothing value
          | (index, (name, value)) <- zip [0 ..] fields
          ]
        Nothing
          | null fields -> Set.empty
          | Just classifier <- wanted
          , Just typedFields <- traverse (typedNominalField classifier) fields ->
              Set.unions
                [ let dependencies = go (child path index) env fieldType value
                   in if mode == Parametric then preserveBarriers dependencies else dependencies
                | (index, ((_, value), (mode, fieldType))) <- zip [0 ..] (zip fields typedFields)
                ]
        Nothing ->
          let known = Set.unions
                [go (child path index) env Nothing value | (index, (_, value)) <- zip [0 ..] fields]
           in if Set.null known
                then Set.empty
                else known `Set.union` analysisFailure path "record interface is unavailable"
      where
        typedNominalField classifier (name, _) = do
          mode <- ooProjectionMode oracle classifier name
          pure (mode, ooProjectionType oracle (length env) classifier name)

    projectionDependencies path env mode receiver field storedIndex =
      let receiverDeps = go (child path 0) env Nothing receiver
          receiverType = inferAt env receiver
          typedMode = case receiver of
            CGlobal global _ | global == prelThis -> Just mode
            CRecordV fields
              | Just index <- storedIndex
              , index >= 0
              , Just (storedField, _) <- listAt index fields
              , storedField == field -> Just mode
            _ -> receiverType >>= projectionMode field
          onlyDeferredMetas =
            all (\case ParametricMeta {} -> True; _ -> False) (Set.toList receiverDeps)
          metadataFailure =
            [ analysisFailure path
                (if isNothing receiverType
                  then "projection receiver type is unavailable"
                  else "projection field metadata is unavailable for "
                    <> maybe "<missing>" receiverTypeShape receiverType)
            | isNothing typedMode
            , not (isNothing receiverType && onlyDeferredMetas)
            ]
          mismatchFailure =
            [analysisFailure path "projection observation mode disagrees with its typed field interface"
            | Just expectedMode <- [typedMode], expectedMode /= mode]
          result = if mode == Parametric
            then
              let origin = case receiver of
                    CGlobal global _ | global == prelThis ->
                      ParametricThisProjection (originPath path) field
                    _ -> case receiverType >>= \classifier -> ooProjectionTrait oracle classifier field of
                      Just trait -> ParametricTraitProjection (originPath path) trait field
                      Nothing -> ParametricProjection (originPath path) field
               in Set.insert origin receiverDeps
            else receiverDeps
       in Set.unions (result : metadataFailure ++ mismatchFailure)

    receiverTypeShape value = case force ctx value of
      VRecordTQ _ -> "record"
      VSigT _ _ -> "signature"
      VGlobal global _ _ -> "global " <> gnameText global
      VRigid level _ -> "local rigid " <> Text.pack (show level)
      _ -> "non-record classifier"

    projectionMode field receiverType = case force ctx receiverType of
      VRecordTQ fields -> rfMode <$> find ((== field) . rfName) fields
      VSigT _ inner -> projectionMode field inner
      VGlobI global _ [(_, _row), (_, prefix)]
        | global == prelOpenRec -> projectionMode field prefix
      other -> ooProjectionMode oracle other field

    matchDependencies path env wanted scrutinee annotation alternatives =
      let scrutineeType =
            (\term -> eval ctx (rigidEnv (length env)) term)
              <$> (annotation >>= \term -> term <$ guard (termScopedAt (length env) term))
              <|> inferAt env scrutinee
          -- A checked match annotation is the typed interface of its
          -- scrutinee.  Dropping it here makes an otherwise well-typed record
          -- literal look unclassified precisely when one of its fields has a
          -- parametric dependency (for example the record view generated by
          -- existential `open`).
          scrutineeDeps = go (child path 0) env scrutineeType scrutinee
          typedFailure =
            [analysisFailure path "match scrutinee type is unavailable"
            | isNothing scrutineeType]
          branchDeps = Set.unions
            [ let branchPath = child path (index + 1)
                  (bindings', substitutions) =
                    patternBindings (length env) branchPath scrutineeDeps scrutineeType pattern'
                  guardDeps = maybe Set.empty (go (child branchPath 0) (bindings' ++ env) Nothing) guard
                  bodyDeps = go (child branchPath 1) (bindings' ++ env) wanted body
               in foldr (uncurry substituteOrigin) (guardDeps `Set.union` bodyDeps) substitutions
            | (index, CaseAlt pattern' guard body) <- zip [0 ..] alternatives
            ]
       in Set.unions (scrutineeDeps : branchDeps : typedFailure)

    patternBindings depth path sourceDeps sourceType pattern' =
      let sites = patternSites depth sourceType pattern'
          structural =
            [ let origin = ParametricPattern (originPath path) index
                  replacement =
                    if mode == Parametric
                      then Set.insert origin sourceDeps
                      else sourceDeps
               in ( ObservationBinding mode (if mode == Parametric then Just origin else Nothing) ty
                       Nothing
                       Nothing
                  , (origin, replacement)
                  )
            | (index, (mode, ty)) <- zip [0 ..] sites
            ]
       in (reverse (map fst structural), map snd structural)

    patternSites depth expectedType = \case
      CPWild -> []
      CPVarM mode _ -> [(mode, expectedType)]
      CPLit _ -> []
      CPCtorM existentialModes constructor universes patterns ->
        let explicitSites = do
              constructorType <- ooConstructorType oracle constructor (Just universes)
              scrutineeType <- expectedType
              constructorPatternObservationSites
                ctx (ooProvisionalUniverseMetadata oracle) depth
                (length patterns) constructorType scrutineeType
         in [(mode, Nothing) | mode <- existentialModes]
              ++ case explicitSites of
                   Just sites -> concat
                     [ patternSites depth (Just fieldType) pattern'
                     | (pattern', (_, fieldType)) <- zip patterns sites
                     ]
                   Nothing -> concatMap (patternSites depth Nothing) patterns
      CPTuple patterns ->
        case expectedType >>= forceRecordType of
          Just fields ->
            concat
              [ patternSites depth (Just (rfType field)) pattern'
              | (pattern', field) <- zip patterns fields
              ]
          Nothing -> concatMap (patternSites depth Nothing) patterns
      CPRecordM fields rest ->
        let declared = expectedType >>= forceRecordType
            fieldSites = concat
              [ patternSites depth (rfType <$> (declared >>= find ((== name) . rfName))) pattern'
              | (name, pattern') <- fields
              ]
            restSites = case rest of
              Just (mode, name) | name /= "" -> [(mode, expectedType)]
              _ -> []
         in fieldSites ++ restSites
      CPInject _ pattern' -> patternSites depth Nothing pattern'
      CPInjectRestM mode _ -> [(mode, expectedType)]
      CPOr (pattern' : _) _ -> patternSites depth expectedType pattern'
      CPOr [] _ -> []
      CPAsM mode _ pattern' -> (mode, expectedType) : patternSites depth expectedType pattern'

    doDependencies path env = goItems path env 0
      where
        goItems _ _ _ [] = Set.empty
        goItems base current index (item : rest) =
          let itemPath = child base index
              continue = goItems base current (index + 1) rest
              patternLevelDeps = Set.unions
                [levelDependencies itemPath current level | level <- itemPatternLevels item]
              bindResult unwrapAction retainDefinition witness pattern' producer =
                let producerDeps = go (child itemPath 0) current Nothing producer
                    producerType =
                      witnessedReadResult current witness producer
                        <|> (inferAt current producer >>= \ty ->
                              if unwrapAction then kernelActionResult ty else Just ty)
                    (rawBindings, substitutions) =
                      patternBindings (length current) (child itemPath 1) producerDeps producerType pattern'
                    bindings' = case (retainDefinition, pattern', rawBindings) of
                      (True, CPVarM {}, binding : remaining) ->
                        binding {obDefinition = Just (length current, producer)} : remaining
                      _ -> rawBindings
                    restDeps = goItems base (bindings' ++ current) (index + 1) rest
                 in producerDeps `Set.union` foldr (uncurry substituteOrigin) restDeps substitutions
           in patternLevelDeps `Set.union` case item of
                KBind _ pattern' action witness ->
                  bindResult True False witness pattern' action
                KLet _ pattern' value -> bindResult False True Nothing pattern' value
                KLetQ pattern' value mElse ->
                  let mainDeps = bindResult False False Nothing pattern' value
                      elseDeps = maybe Set.empty (\(elsePattern, elseBody) ->
                        let (bindings', substitutions) =
                              patternBindings (length current) (child itemPath 2) Set.empty Nothing elsePattern
                         in foldr (uncurry substituteOrigin)
                              (go (child itemPath 3) (bindings' ++ current) Nothing elseBody)
                              substitutions) mElse
                   in mainDeps `Set.union` elseDeps
                KExpr value -> go (child itemPath 0) current Nothing value `Set.union` continue
                KVarItem name initial action _ ->
                  let referenceType = inferAt current action >>= kernelActionResult
                   in Set.unions
                        [ go (child itemPath 0) current Nothing initial
                        , go (child itemPath 1) current Nothing action
                        , goItems base
                            (binderAt (child itemPath 2) name Ordinary referenceType : current)
                            (index + 1) rest
                        ]
                KAssign reference _ rhs action _ -> Set.unions
                  [ go (child itemPath 0) current Nothing reference
                  , go (child itemPath 1) current Nothing rhs
                  , go (child itemPath 2) current Nothing action
                  , continue
                  ]
                KReturn value -> go (child itemPath 0) current Nothing value `Set.union` continue
                KBreak _ -> continue
                KContinue _ -> continue
                KWhile _ condition body mElse -> Set.unions
                  [ conditionDeps itemPath current condition
                  , goItems (child itemPath 1) current 0 body
                  , maybe Set.empty (goItems (child itemPath 2) current 0) mElse
                  , continue
                  ]
                KFor _ pattern' source body mElse ->
                  let sourceDeps = go (child itemPath 0) current Nothing source
                      (bindings', substitutions) =
                        patternBindings (length current) (child itemPath 1) sourceDeps Nothing pattern'
                      bodyDeps = foldr (uncurry substituteOrigin)
                        (goItems (child itemPath 2) (bindings' ++ current) 0 body) substitutions
                   in Set.unions [sourceDeps, bodyDeps, maybe Set.empty (goItems (child itemPath 3) current 0) mElse, continue]
                KIf arms mElse -> Set.unions
                  ( continue
                  : maybe Set.empty (goItems (child itemPath 99) current 0) mElse
                  : [ go (child itemPath (2 * armIndex)) current Nothing condition
                        `Set.union` goItems (child itemPath (2 * armIndex + 1)) current 0 body
                    | (armIndex, (condition, body)) <- zip [0 ..] arms
                    ]
                  )
                KDefer _ action -> go (child itemPath 0) current Nothing action `Set.union` continue
                KUsing pattern' acquire release ->
                  let acquireDeps = go (child itemPath 0) current Nothing acquire
                      releaseDeps = go (child itemPath 1) current Nothing release
                      (bindings', substitutions) =
                        patternBindings (length current) (child itemPath 2) acquireDeps Nothing pattern'
                      restDeps = goItems base (bindings' ++ current) (index + 1) rest
                   in acquireDeps `Set.union` releaseDeps
                        `Set.union` foldr (uncurry substituteOrigin) restDeps substitutions
                KSubDo _ body -> goItems (child itemPath 0) current 0 body `Set.union` continue

        conditionDeps base current = \case
          KCondPure value -> go (child base 0) current Nothing value
          KCondAction value -> go (child base 0) current Nothing value

    forceRecordType value = case force ctx value of
      VRecordTQ fields -> Just fields
      VSigT _ inner -> forceRecordType inner
      _ -> Nothing

    substituteOrigin origin replacement dependencies
      | origin `Set.member` dependencies = Set.delete origin dependencies `Set.union` replacement
      | otherwise = dependencies

    prefixDependencies prefix = Set.map $ \case
      ParametricBinder path name -> ParametricBinder (prefix ++ path) name
      ParametricProjection path field -> ParametricProjection (prefix ++ path) field
      ParametricTraitProjection path trait field ->
        ParametricTraitProjection (prefix ++ path) trait field
      ParametricThisProjection path field -> ParametricThisProjection (prefix ++ path) field
      ParametricPattern path index -> ParametricPattern (prefix ++ path) index
      ParametricReflection path -> ParametricReflection (prefix ++ path)
      ParametricAnalysisFailure path reason ->
        ParametricAnalysisFailure (prefix ++ path) reason
      origin -> origin

    rigidEnv depth = [VRigid level [] | level <- reverse [0 .. depth - 1]]

-- | Semantic recognition of the §11.1.2.3B parametric-kind grammar.
-- Callers supply the next rigid level for traversing dependent codomains.
isParametricKindValue :: EvalCtx -> Int -> Value -> Bool
isParametricKindValue ctx level value = case force ctx value of
  VSort _ -> True
  VPiM Parametric _ Q0 False _ domain (Closure closureEnv codomain) ->
    isParametricKindValue ctx level domain
      && isParametricKindValue ctx (level + 1)
        (eval ctx (VRigid level [] : closureEnv) codomain)
  _ -> False

mentionsTopBinder :: Term -> Bool
mentionsTopBinder = getAny . foldTermWithDepth occurrence 0
  where
    occurrence depth = \case
      CVar index | index == depth -> Any True
      _ -> mempty
