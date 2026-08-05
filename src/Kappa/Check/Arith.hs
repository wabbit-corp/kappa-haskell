-- | Arithmetic and boolean evidence: turning checked Core terms into the
-- linear-arithmetic facts the totality checker reasons with.
--
-- Termination checking (see "Kappa.Check.Totality") has to decide questions
-- like /is this argument strictly smaller on every recursive call?/ It cannot
-- answer those from Core syntax alone, so this module sits underneath it and
-- does the translation: it recognizes the standard arithmetic and comparison
-- operations behind their trait-dictionary encodings, normalizes a term far
-- enough to expose one, and reads branch conditions and pattern matches as
-- assumptions ('AFact') that hold inside a branch.
--
-- The recognizers are deliberately identity-based rather than
-- spelling-based: 'canonicalStandardBinaryOperation' and friends check the
-- resolved semantic identity of the operation and its dictionary, so a
-- user-defined @+@ is never mistaken for the primitive one.
--
-- Nothing here depends on the elaboration kernel in "Kappa.Check"; the
-- dependency runs the other way, which is why this can be its own module.
module Kappa.Check.Arith
  ( arithmeticBooleanFormula
  , arithmeticDomainForCarrier
  , assumeBoolM
  , boolEqualityTruePayload
  , boundedInsert
  , canonicalStandardBinaryOperation
  , canonicalizeStandardArithmeticOperations
  , comparePatternFactsM
  , decodeSelectedNatRange
  , ecOf
  , ec_
  , gnameInModule
  , isNatType
  , kCondTerm
  , memberGlobal
  , normalizeTermAt
  , proveBoolTrue
  , proveEq
  , proveFact
  , proveLt
  , proveNonNeg
  , proveTypeRelationTrue
  , relationIsPrimitiveLtInt
  , renderStructuralTermKey
  , selectedArithmeticExpression
  , selectedArithmeticPredicateFact
  , selectedArithmeticPredicateFactForDomain
  , selectedNatArithmeticExpression
  , selectedNatRangeMembershipFacts
  , selectedNatRangeMembershipOperands
  , selectedStandardOrderFact
  , standardPreludeDictionary
  , stripIdentityWrappers
  , substituteLevelAssumptions
  , termCacheUniverseScoped
  , termHeadGlob
  , transparentProofReduce
  , unsolvedMetasOf
  ) where

import Control.Applicative ((<|>))
import Control.Monad (guard, when)
import Control.Monad.State.Strict
import Data.List (nub, sort)
import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust, maybeToList)
import Data.Monoid (Any (..))
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Builtins
import Kappa.Arithmetic
  ( AFormula (..)
  , ArithmeticSemantics (..)
  , PrimitiveComparisonDomain (..)
  , decodePrimitiveComparisonOperandM
  )
import Kappa.Check.Types
import Kappa.Core
import Kappa.CoreOps
  ( foldTerm
  , mapTermWithDepth
  , levelParamsOfTerm
  , patBindersC
  , CorePatternDecision (..)
  , instantiateCorePatternBody
  , matchCorePattern
  , shiftTerm
  , substTopTermAt
  , zonkTermWith
  )
import Kappa.Eval
import Kappa.Level
  ( Assumptions
  , LevelMeta
  , assumptionsList
  , emptyAssumptions
  , insertAssumption
  , normalizeLevel
  , substituteLevelMetas
  , substituteLevelParams
  )
import Kappa.Source
import Kappa.Termination hiding (expandedGlobalsOfTerm)

kCondTerm :: KCond -> Term
kCondTerm = \case
  KCondPure t -> t
  KCondAction t -> t

ec_ :: CheckM EvalCtx
ec_ = gets ecOf

-- | The (compile-time, non-runtime) 'EvalCtx' implied by a 'CheckState'. Pure
-- so callers holding a saved state can force values without re-entering the
-- monad.
ecOf :: CheckState -> EvalCtx
ecOf st = EvalCtx (Globals (csGlobals st)) (csMetas st) False (csFacts st)

maxNormCacheEntries :: Int
maxNormCacheEntries = 8192

-- | Deterministic bounded insertion.  This is deliberately not an LRU cache:
-- carrying access-order state through the checker would complicate auditing
-- without changing the trusted result.  Dropping the smallest structural key
-- keeps the bound strict and leaves cache contents semantically irrelevant.
boundedInsert :: Ord k => Int -> k -> a -> Map k a -> Map k a
boundedInsert cap k v m =
  let m' = Map.insert k v m
   in if Map.size m' <= cap
        then m'
        else snd (Map.deleteFindMin m')

-- | Structural key for cache lookups.  This intentionally uses Core's derived
-- representation, not user-facing pretty printing: it is exact enough for a
-- best-effort cache and never participates in user-visible output or
-- reproducibility.
renderStructuralTermKey :: Term -> Text
renderStructuralTermKey = T.pack . show

-- | A declaration-universe parameter is lexical to its owning hidden
-- telescope. Cache entries may retain such parameters only while keyed by
-- that same declaration, and every index must be in range. This preserves
-- useful within-body caching without allowing syntactically identical
-- @LParam 0@ values from unrelated declarations to alias.
termCacheUniverseScoped :: CheckState -> Term -> Bool
termCacheUniverseScoped st term =
  case csActiveUniverseDefinition st >>= (`Map.lookup` csGlobals st) of
    Nothing -> null parameters
    Just definition ->
      let arity = dutParameterCount (gdUniverses definition)
       in all (\parameter -> parameter >= 0 && parameter < arity) parameters
  where
    parameters = levelParamsOfTerm term

substituteLevelAssumptions :: Map LevelMeta Level -> Assumptions -> Assumptions
substituteLevelAssumptions assignments =
  foldr
    (\(lower, upper) assumptions ->
      insertAssumption
        (normalizeLevel (substituteLevelMetas assignments lower))
        (normalizeLevel (substituteLevelMetas assignments upper))
        assumptions)
    emptyAssumptions
    . assumptionsList

-- | Unsolved ordinary term metavariables. Universe metavariables share the
-- numeric identifier representation but have a separate solution table and
-- are classified by 'levelMetasOfTerm'; conflating the two commits deferred
-- universe obligations as though they contained flexible term evidence.
unsolvedMetasOf :: CheckState -> Term -> [MetaId]
unsolvedMetasOf st t =
  [ m
  | m <- nub (foldTerm ordinaryMeta (const []) t)
  , case Map.lookup m (csMetas st) of
      Just (Just _) -> False
      _ -> True
  ]
  where
    ordinaryMeta = \case
      CMeta meta -> [meta]
      _ -> []

arithmeticBooleanFormula
  :: Int
  -> ArithmeticDomain
  -> Term
  -> CheckM (Maybe AFormula)
arithmeticBooleanFormula depth domain term =
  case simplifyDecisionTerm term of
    CThunkE body _ ->
      arithmeticBooleanFormula depth domain body
    CForceE (CThunkE body _) _ ->
      arithmeticBooleanFormula depth domain body
    CCtor constructor _ []
      | constructor == prelTrue -> pure (Just (ATruth True))
      | constructor == prelFalse -> pure (Just (ATruth False))
    CCtorI constructor _ _ []
      | constructor == prelTrue -> pure (Just (ATruth True))
      | constructor == prelFalse -> pure (Just (ATruth False))
    CIf condition thenTerm elseTerm
      | isTrueTerm thenTerm
      , isFalseTerm elseTerm ->
          arithmeticBooleanFormula depth domain condition
      | isFalseTerm thenTerm
      , isTrueTerm elseTerm ->
          fmap ANot <$> arithmeticBooleanFormula depth domain condition
      | isFalseTerm elseTerm ->
          liftA2 (liftA2 AAnd)
            (arithmeticBooleanFormula depth domain condition)
            (arithmeticBooleanFormula depth domain thenTerm)
      | isTrueTerm thenTerm ->
          liftA2 (liftA2 AOr)
            (arithmeticBooleanFormula depth domain condition)
            (arithmeticBooleanFormula depth domain elseTerm)
    simplified -> do
      let (headTerm, arguments) =
            spineOfTerm (stripIdentityWrappers simplified)
          explicit = [argument | (Expl, argument) <- arguments]
          binary constructor =
            case last2 explicit of
              Just (lhs, rhs) ->
                liftA2 (liftA2 constructor)
                  (arithmeticBooleanFormula depth domain lhs)
                  (arithmeticBooleanFormula depth domain rhs)
              Nothing -> pure Nothing
      case termHeadGlob (stripIdentityWrappers headTerm) of
        Just operation
          | operation == prelAnd -> binary AAnd
          | operation == prelOr -> binary AOr
          | operation == prelNot ->
              case reverse explicit of
                argument : _ ->
                  fmap ANot <$> arithmeticBooleanFormula depth domain argument
                _ -> pure Nothing
        _ ->
          if domain == ArithmeticNatural
            then
              selectedNatRangeMembershipFacts depth simplified >>= \case
                Just facts -> pure (formulaFromFacts facts)
                Nothing -> atom simplified
            else atom simplified
  where
    atom candidate =
      fmap AAtom
        <$> selectedArithmeticPredicateFactForDomain domain depth candidate

    formulaFromFacts = \case
      [] -> Just (ATruth True)
      fact : rest ->
        Just (foldl' AAnd (AAtom fact) (map AAtom rest))

    isTrueTerm = \case
      CCtor constructor _ [] -> constructor == prelTrue
      CCtorI constructor _ _ [] -> constructor == prelTrue
      _ -> False

    isFalseTerm = \case
      CCtor constructor _ [] -> constructor == prelFalse
      CCtorI constructor _ _ [] -> constructor == prelFalse
      _ -> False

selectedArithmeticExpression
  :: ArithmeticDomain
  -> Int
  -> Term
  -> CheckM (Maybe AExpr)
selectedArithmeticExpression domain depth = go (24 :: Int)
  where
    go fuel term
      | fuel <= 0 = pure Nothing
      | otherwise =
          direct term >>= \case
            Just expression -> pure (Just expression)
            Nothing ->
              case stripIdentityWrappers term of
                CIf condition thenTerm elseTerm -> do
                  conditionFormula <-
                    arithmeticBooleanFormula depth domain condition
                  thenExpression <- go (fuel - 1) thenTerm
                  elseExpression <- go (fuel - 1) elseTerm
                  pure
                    ( AIf
                        <$> conditionFormula
                        <*> thenExpression
                        <*> elseExpression
                    )
                _ -> do
                  reduced <- transparentProofReduce depth 48 term
                  if simplifyDecisionTerm reduced == simplifyDecisionTerm term
                    then pure Nothing
                    else go (fuel - 1) reduced

    direct term = do
      instances <- gets csInstances
      let canonical =
            canonicalizeStandardArithmeticOperations instances term
      case domain of
        ArithmeticNatural ->
          selectedNatArithmeticExpressionDirect depth canonical
        ArithmeticInteger -> pure (arithOf depth canonical)
        ArithmeticTypeLevel -> pure Nothing
        ArithmeticProviderLaw -> pure Nothing

-- | Wrappers that are transparent to resolved semantic identity. Universe
-- lifts constrain classification but do not change the selected global head.
stripIdentityWrappers :: Term -> Term
stripIdentityWrappers = \case
  CUniverseLift _ _ _ inner -> stripIdentityWrappers inner
  CSchemaLift _ _ _ _ _ _ _ _ inner -> stripIdentityWrappers inner
  term -> term

-- | Decode a boolean arithmetic predicate only after authenticating the
-- selected provider and member identity. Primitive comparisons are already
-- self-authenticating through their wired-in global identities. Trait methods
-- additionally require the exact coherent dictionary selected by elaboration;
-- a user dictionary or an unrelated field with the same source label is never
-- admitted to the arithmetic solver.
selectedArithmeticPredicateFact :: Int -> Term -> CheckM (Maybe AFact)
selectedArithmeticPredicateFact depth term =
  boolRelBranchM depth term >>= \case
    Just primitive -> pure (Just primitive)
    Nothing ->
      selectedStandardCheckedPredicateFact
        ArithmeticNatural
        depth
        term

-- | Domain-indexed certificate entry point for selected arithmetic
-- predicates. A still-selected standard order application carries its
-- carrier explicitly, so reject a certificate-domain mismatch before trying
-- representation-level primitive recognition. This prevents a Nat proof from
-- being replayed as Integer arithmetic (or conversely) merely because both
-- lower to the same integer comparison primitives.
selectedArithmeticPredicateFactForDomain
  :: ArithmeticDomain
  -> Int
  -> Term
  -> CheckM (Maybe AFact)
selectedArithmeticPredicateFactForDomain domain depth term =
  selectedStandardOrderFact depth term >>= \case
    Just (selectedDomain, fact) ->
      pure (if selectedDomain == domain then Just fact else Nothing)
    Nothing -> do
      selectedPrimitiveArithmeticPredicateFact domain depth term >>= \case
        Just fact -> pure (Just fact)
        Nothing ->
          selectedStandardCheckedPredicateFact domain depth term >>= \case
            Just fact -> pure (Just fact)
            Nothing -> case domain of
              ArithmeticNatural -> selectedArithmeticPredicateFact depth term
              ArithmeticInteger -> boolRelBranchM depth term
              ArithmeticTypeLevel -> pure Nothing
              ArithmeticProviderLaw -> pure Nothing

-- | Decode the canonical primitive comparison emitted after an authenticated
-- standard order call has been lowered.  Primitive identity authenticates the
-- relation, while the Nat domain additionally requires both operands to pass
-- through the checked @natToInt@ bridge.  This keeps Nat and Integer
-- certificates disjoint even though their exact runtime comparison primitive
-- is shared.
selectedPrimitiveArithmeticPredicateFact
  :: ArithmeticDomain
  -> Int
  -> Term
  -> CheckM (Maybe AFact)
selectedPrimitiveArithmeticPredicateFact domain depth term =
  case spineOfTerm (stripIdentityWrappers term) of
    (headTerm, arguments)
      | Just operation <- termHeadGlob (stripIdentityWrappers headTerm)
      , Just comparison <-
          lookup
            operation
            [ (gPrel "ltInt", ACmpLt)
            , (gPrel "leInt", ACmpLe)
            , (gPrel "eqInt", ACmpEq)
            ]
      , Just (left, right) <-
          last2 [argument | (Expl, argument) <- arguments] -> do
          logicalDomain <- case domain of
            ArithmeticNatural ->
              pure (Just PrimitiveComparisonNatural)
            ArithmeticInteger ->
              pure (Just PrimitiveComparisonInteger)
            ArithmeticTypeLevel -> pure Nothing
            ArithmeticProviderLaw -> pure Nothing
          leftExpression <- case logicalDomain of
            Nothing -> pure Nothing
            Just selected ->
              decodePrimitiveComparisonOperandM
                natBridgePayload
                decodeExpression
                selected
                left
          rightExpression <- case logicalDomain of
            Nothing -> pure Nothing
            Just selected ->
              decodePrimitiveComparisonOperandM
                natBridgePayload
                decodeExpression
                selected
                right
          pure
            ( AFact comparison
                <$> leftExpression
                <*> rightExpression
            )
    _ -> pure Nothing
  where
    decodeExpression selected =
      selectedArithmeticExpression
        ( case selected of
            PrimitiveComparisonNatural -> ArithmeticNatural
            PrimitiveComparisonInteger -> ArithmeticInteger
        )
        depth

    natBridgePayload operand =
      case spineOfTerm (stripIdentityWrappers operand) of
        (headTerm, arguments)
          | termHeadGlob (stripIdentityWrappers headTerm)
              == Just prelNatToInt
          , [payload] <- [argument | (Expl, argument) <- arguments] ->
              Just payload
        _ -> Nothing

-- | Reify the normative §28.2.3 domains of the standard checked operations.
-- The operation member, selected dictionary identity, checked carrier head,
-- and supported arithmetic domain are all authenticated before a fact reaches
-- the generic arithmetic kernel. A same-spelled user field or custom
-- dictionary therefore fails closed.
selectedStandardCheckedPredicateFact
  :: ArithmeticDomain
  -> Int
  -> Term
  -> CheckM (Maybe AFact)
selectedStandardCheckedPredicateFact domain depth term =
  firstDescriptor standardCheckedPredicates
  where
    stateMemberOwners state = csBareTraitMembers state
    (headTerm, arguments) = spineOfTerm (stripIdentityWrappers term)
    explicitArguments = [argument | (Expl, argument) <- arguments]
    implicitArguments = [argument | (Impl, argument) <- arguments]

    firstDescriptor [] = pure Nothing
    firstDescriptor (descriptor : rest)
      | domain `notElem` scpDomains descriptor = firstDescriptor rest
      | otherwise = do
          state <- get
          let trait = scpTrait descriptor
              member = scpMember descriptor
              qualifiedMember = memberGlobal trait member
              selectedGlobal candidate =
                case termHeadGlob (stripIdentityWrappers candidate) of
                  Just global ->
                    global == qualifiedMember
                      || Map.lookup global (stateMemberOwners state)
                           == Just (trait, member)
                  Nothing -> False
              globalCall = do
                guard (selectedGlobal headTerm)
                carrier : dictionary : _ <- pure implicitArguments
                guard (arithmeticDomainForCarrier carrier == Just domain)
                (left, right) <- last2 explicitArguments
                pure (dictionary, left, right)
              projectedCall =
                case stripIdentityWrappers headTerm of
                  CProjM _ dictionary projectedMember
                    | projectedMember == member -> do
                        (left, right) <- last2 explicitArguments
                        pure (dictionary, left, right)
                  CProjAtM _ dictionary projectedMember _
                    | projectedMember == member -> do
                        (left, right) <- last2 explicitArguments
                        pure (dictionary, left, right)
                  _ -> Nothing
          case globalCall <|> projectedCall of
            Nothing -> firstDescriptor rest
            Just (dictionary, left, right) -> do
              standard <-
                standardPreludeDictionary
                  trait
                  (\case
                    [carrier] ->
                      arithmeticDomainForCarrier carrier == Just domain
                    _ -> False)
                  dictionary
              if not standard
                then firstDescriptor rest
                else do
                  leftExpression <-
                    selectedArithmeticExpression domain depth left
                  rightExpression <-
                    selectedArithmeticExpression domain depth right
                  pure $ do
                    left' <- leftExpression
                    right' <- rightExpression
                    pure $ case scpSemantics descriptor of
                      CheckedSubtractionDomain ->
                        AFact ACmpLe right' left'
                      CheckedNonzeroDomain ->
                        AFact ACmpNe right' (AConst 0)

standardCheckedPredicates :: [StandardCheckedPredicate]
standardCheckedPredicates =
  [ StandardCheckedPredicate
      (gPrel "CheckedSub")
      "subDefined"
      [ArithmeticNatural]
      CheckedSubtractionDomain
  , StandardCheckedPredicate
      (gPrel "CheckedDiv")
      "divDefined"
      [ArithmeticNatural, ArithmeticInteger]
      CheckedNonzeroDomain
  , StandardCheckedPredicate
      (gPrel "CheckedMod")
      "modDefined"
      [ArithmeticNatural, ArithmeticInteger]
      CheckedNonzeroDomain
  ]

-- | Reify the normative §20.2.1 equations for canonical Nat ranges. Every
-- semantic step is authenticated: the selected @Contains@ dictionary must be
-- the prelude instance for @(NumericRange Nat, Nat)@, and the range value must
-- be built by the selected prelude @Rangeable Nat@ instance (or already be its
-- checked constructor result). A same-spelled user member or range constructor
-- cannot enter this proof source.
selectedNatRangeMembershipFacts :: Int -> Term -> CheckM (Maybe [AFact])
selectedNatRangeMembershipFacts depth term = do
  selectedNatRangeMembershipOperands term >>= \case
    Nothing -> pure Nothing
    Just (rangeValue, value) -> do
      decodedRange <- decodeSelectedNatRange depth rangeValue
      case decodedRange of
        Nothing -> pure Nothing
        Just (lower, upper, exclusive) -> do
          lowerExpression <- selectedNatArithmeticExpression depth lower
          valueExpression <- selectedNatArithmeticExpression depth value
          upperExpression <- selectedNatArithmeticExpression depth upper
          pure $ do
            lower' <- lowerExpression
            value' <- valueExpression
            upper' <- upperExpression
            pure
              [ AFact ACmpLe lower' value'
              , AFact
                  (if exclusive then ACmpLt else ACmpLe)
                  value'
                  upper'
              ]

-- | Authenticate one selected @Contains (NumericRange Nat) Nat@ application
-- and recover its range/value operands. Dictionary discovery is by checked
-- instance identity, not by a source-spine position: generated erased proof
-- arguments may be interleaved with ordinary implicits.
selectedNatRangeMembershipOperands :: Term -> CheckM (Maybe (Term, Term))
selectedNatRangeMembershipOperands term = do
  state <- get
  let containsTrait = gPrel "Contains"
      containsMember = memberGlobal containsTrait "contains"
      arguments = snd (spineOfTerm (stripIdentityWrappers term))
      explicitArguments = [argument | (Expl, argument) <- arguments]
      implicitArguments = [argument | (Impl, argument) <- arguments]
      selectedContainsGlobal candidate =
        case termHeadGlob (stripIdentityWrappers candidate) of
          Just global ->
            global == containsMember
              || Map.lookup global (csBareTraitMembers state)
                   == Just (containsTrait, "contains")
          Nothing -> False
      globalCall candidate = do
        guard (selectedContainsGlobal candidate)
        (rangeValue, value) <- last2 explicitArguments
        pure (implicitArguments, rangeValue, value)
      projectedCall candidate = case stripIdentityWrappers candidate of
        CProjM _ dictionary "contains" -> do
          (rangeValue, value) <- last2 explicitArguments
          pure ([dictionary], rangeValue, value)
        CProjAtM _ dictionary "contains" _ -> do
          (rangeValue, value) <- last2 explicitArguments
          pure ([dictionary], rangeValue, value)
        _ -> Nothing
      headTerm = fst (spineOfTerm (stripIdentityWrappers term))
  case globalCall headTerm <|> projectedCall headTerm of
    Nothing -> pure Nothing
    Just (dictionaryCandidates, rangeValue, value) -> do
      selectedDictionary <-
        uniqueStandardPreludeDictionaryArgument
          containsTrait
          (\case
            [container, item] ->
              isNumericRangeNatType container && isNatType item
            _ -> False)
          dictionaryCandidates
      case selectedDictionary of
        Nothing -> pure Nothing
        Just _ -> pure (Just (rangeValue, value))

decodeSelectedNatRange :: Int -> Term -> CheckM (Maybe (Term, Term, Bool))
decodeSelectedNatRange depth rangeValue = do
  normalized <- transparentProofReduce depth 48 rangeValue
  case decodedConstructor normalized of
    Just decoded -> pure (Just decoded)
    Nothing -> decodeRangeCall rangeValue
  where
    decodedConstructor = \case
      CCtorI constructor _ _ arguments
        | constructor == prelNumericRange
        , [lower, upper, exclusive] <-
            [caTerm argument | argument <- arguments, caPayload argument]
        , Just exclusiveValue <- boolLiteralTerm exclusive ->
            Just (lower, upper, exclusiveValue)
      _ -> Nothing

    decodeRangeCall term =
      case spineOfTerm (stripIdentityWrappers term) of
        (headTerm, arguments)
          | Just operator <- termHeadGlob (stripIdentityWrappers headTerm)
          , operator == gPrel ".." || operator == gPrel "..<"
          , [lower, upper] <- [argument | (Expl, argument) <- arguments] -> do
              dictionary <-
                uniqueStandardPreludeDictionaryArgument
                  (gPrel "Rangeable")
                  (\case
                    [headType] -> isNatType headType
                    _ -> False)
                  [argument | (Impl, argument) <- arguments]
              pure $
                case dictionary of
                  Just _ -> Just (lower, upper, operator == gPrel "..<")
                  Nothing -> Nothing
        _ -> pure Nothing

    boolLiteralTerm = \case
      CCtor constructor _ []
        | constructor == prelTrue -> Just True
        | constructor == prelFalse -> Just False
      _ -> Nothing

isNatType :: Term -> Bool
isNatType term =
  termHeadGlob (stripIdentityWrappers term) == Just prelNat

isNumericRangeNatType :: Term -> Bool
isNumericRangeNatType term =
  case spineOfTerm (stripIdentityWrappers term) of
    (headTerm, arguments)
      | termHeadGlob (stripIdentityWrappers headTerm) == Just prelNumericRange ->
          case reverse [argument | (_, argument) <- arguments] of
            item : _ -> isNatType item
            _ -> False
    _ -> False

-- | Authenticate a selected premise-free standard dictionary against its
-- checked trait head. This shared helper is intentionally structural: callers
-- supply semantic head predicates over resolved Core, never rendered names.
standardPreludeDictionary
  :: GName
  -> ([Term] -> Bool)
  -> Term
  -> CheckM Bool
standardPreludeDictionary trait validHead dictionary = do
  instances <- gets csInstances
  pure (standardPreludeDictionaryIn instances trait validHead dictionary)

-- | Select one authenticated dictionary from an application implicit spine.
-- Generated universe-relation proofs and other erased implicits may precede
-- or follow source dictionaries, so semantic consumers must not recover
-- evidence by a fixed argument offset. Exactly one checked prelude instance
-- must match; absence and ambiguity both fail closed.
uniqueStandardPreludeDictionaryArgument
  :: GName
  -> ([Term] -> Bool)
  -> [Term]
  -> CheckM (Maybe Term)
uniqueStandardPreludeDictionaryArgument trait validHead candidates = do
  instances <- gets csInstances
  pure $ case
    [ candidate
    | candidate <- candidates
    , standardPreludeDictionaryIn instances trait validHead candidate
    ] of
      [dictionary] -> Just dictionary
      _ -> Nothing

standardPreludeDictionaryIn
  :: [InstanceEntry]
  -> GName
  -> ([Term] -> Bool)
  -> Term
  -> Bool
standardPreludeDictionaryIn instances trait validHead dictionary =
  case termHeadGlob (stripIdentityWrappers dictionary) of
    Just dictionaryGlobal ->
      dictionaryGlobal `gnameInModule` preludeModule
        && any
          ( \entry ->
              ieDict entry == dictionaryGlobal
                && ieTrait entry == trait
                && null (iePremises entry)
                && validHead (ieHead entry)
          )
          instances
    Nothing -> False

-- | Bounded, non-strict proof-side reduction.
--
-- Runtime evaluation of Kappa is strict, but proposition solving must not
-- force arbitrary user arguments just to learn that a transparent proof
-- predicate ignores them.  This reducer unfolds only definitions that the
-- ordinary totality machinery has already marked conversion-reducible, then
-- performs beta/projection/known-branch reduction on Core syntax without
-- evaluating function arguments first.  If the fuel runs out, it returns the
-- best neutral term it has instead of claiming a proof.
transparentProofReduce :: Int -> Int -> Term -> CheckM Term
transparentProofReduce d fuel0 t0 = go fuel0 (simplifyDecisionTermAt d t0)
  where
    go fuel t
      | fuel <= 0 = pure (simplifyDecisionTermAt d t)
      | otherwise = do
          -- Preserve authenticated arithmetic providers before unfolding
          -- their library implementation. Provider decoders need the selected
          -- dictionary identity; reducing past it would retain operational
          -- behavior while discarding the authority used by proof synthesis.
          primitiveCompare <- primitiveOrderedCompareArgsRaw d t
          case primitiveCompare of
            Just _ -> reduceProtectedApplication fuel t
            Nothing -> selectedStandardOrderFact d t >>= \case
              Just _ -> reduceProtectedApplication fuel t
              Nothing -> do
                let simplified = simplifyDecisionTermAt d t
                if simplified /= t
                  then
                    -- Beta/iota reduction can expose a selected provider
                    -- application. Give the semantic recognizers first right
                    -- of refusal before generic delta reduction unfolds away
                    -- its checked dictionary identity.
                    go (fuel - 1) simplified
                  else case t of
                    CGlobal g universes ->
                      maybe (pure (CGlobal g universes)) (go (fuel - 1))
                        =<< unfoldReducibleGlobal d g universes
                    application@CApp {}
                      | trustedNaturalBridgeApplication application ->
                          reduceTrustedNaturalBridge (fuel - 1) application
                      | trustedIntegerPrimitiveApplication application ->
                          reduceProtectedApplication fuel application
                      | otherwise -> reduceApp fuel application
                    CProjM mode e f -> do
                      e' <- go (fuel - 1) e
                      case e' of
                        CRecordV fs | Just x <- lookup f fs -> go (fuel - 1) x
                        CCtorI constructor _ _ arguments ->
                          typedConstructorProjection constructor arguments f >>= \case
                            Just x -> go (fuel - 1) x
                            Nothing -> pure (CProjM mode e' f)
                        CSealE ls inner | f `notElem` ls -> go (fuel - 1) (CProjM mode inner f)
                        _ -> pure (CProjM mode e' f)
                    CProjAtM mode e f i -> do
                      e' <- go (fuel - 1) e
                      case e' of
                        CRecordV fs | Just x <- lookup f fs -> go (fuel - 1) x
                        CCtorI constructor _ _ arguments ->
                          typedConstructorProjection constructor arguments f >>= \case
                            Just x -> go (fuel - 1) x
                            Nothing -> pure (CProjAtM mode e' f i)
                        CSealE ls inner | f `notElem` ls -> go (fuel - 1) (CProjAtM mode inner f i)
                        _ -> pure (CProjAtM mode e' f i)
                    CIf c th el -> do
                      c' <- go (fuel - 1) c
                      case c' of
                        CCtor g _ [] | g == prelTrue -> go (fuel - 1) th
                        CCtor g _ [] | g == prelFalse -> go (fuel - 1) el
                        _ -> pure (CIf c' th el)
                    CMatch s ann resultAnn alts -> do
                      s' <- go (fuel - 1) s
                      case s' of
                        CIf condition thenBranch elseBranch ->
                          go
                            (fuel - 1)
                            ( CIf
                                condition
                                (CMatch thenBranch ann resultAnn alts)
                                (CMatch elseBranch ann resultAnn alts)
                            )
                        _ ->
                          transparentSelectorProjection s' alts >>= \case
                            Just projection -> go (fuel - 1) projection
                            Nothing -> reduceKnownMatch (fuel - 1) s' ann resultAnn alts
                    CLet _ _ _ rhs body ->
                      go (fuel - 1) (substTopTermAt d rhs body)
                    CLetRecRuntimeM mode q n runtimeErasure a rhs body ->
                      pure (CLetRecRuntimeM mode q n runtimeErasure a rhs body)
                    CForceE delayed resultType -> do
                      delayed' <- go (fuel - 1) delayed
                      case delayed' of
                        CThunkE body _ -> go (fuel - 1) body
                        _ -> pure (CForceE delayed' resultType)
                    other -> pure other

    -- Keep the authenticated operation and every implicit evidence argument
    -- intact, but do not freeze ordinary value operands underneath it.
    -- Dependent projections and known-constructor matches may otherwise remain
    -- hidden below a selected comparison forever, preventing the surrounding
    -- branch fact from reaching a fixed point.
    reduceProtectedApplication fuel application = do
      let (headTerm, arguments) = spineOfTerm application
      arguments' <-
        traverse
          (\case
            (Expl, argument) -> (Expl,) <$> go (fuel - 1) argument
            implicit -> pure implicit)
          arguments
      let reduced =
            List.foldl'
              (\function (icit, argument) -> CApp icit function argument)
              headTerm
              arguments'
      pure (fromMaybe reduced (foldTrustedIntegerPrimitive reduced))

    trustedIntegerPrimitiveApplication application =
      case spineOfTerm (stripIdentityWrappers application) of
        (headTerm, _) ->
          maybe
            False
            ( \global ->
                isJust (intArithPrim global)
                  || isJust (intCmpPrim global)
            )
            (termHeadGlob (stripIdentityWrappers headTerm))

    -- The standard Nat-to-Integer bridge is an exact compiler-wired pure
    -- operation. Reducing its sole operand is therefore safe even though the
    -- generic non-strict reducer leaves arbitrary function arguments opaque.
    -- This exposes known constructor projections selected by branch facts;
    -- only a resulting Nat literal is folded by the shared authenticated
    -- bridge rule.
    trustedNaturalBridgeApplication application =
      case spineOfTerm (stripIdentityWrappers application) of
        (headTerm, [(Expl, _)]) ->
          termHeadGlob (stripIdentityWrappers headTerm)
            `elem`
              [ Just prelNatToInt
              , Just (GName primModule (gKey prelNatToInt))
              ]
        _ -> False

    reduceTrustedNaturalBridge fuel application =
      case spineOfTerm (stripIdentityWrappers application) of
        (headTerm, [(Expl, operand)]) -> do
          operand' <- go fuel operand
          let reduced = CApp Expl headTerm operand'
          pure
            (fromMaybe reduced (canonicalTrustedNaturalLiteralBridge reduced))
        _ -> pure application

    -- Keep neutral integer primitives visible to the arithmetic reifier, but
    -- do not strand a branch decision once every operand is a closed literal.
    -- The exact primitive identity authorizes evaluation through the same pure
    -- runtime table used by conversion; partial operations such as division by
    -- zero return 'Nothing' and therefore remain neutral.
    foldTrustedIntegerPrimitive application = do
      let (headTerm, arguments) =
            spineOfTerm (stripIdentityWrappers application)
      global@(GName _ operation) <-
        termHeadGlob (stripIdentityWrappers headTerm)
      guard
        ( isJust (intArithPrim global)
            || isJust (intCmpPrim global)
        )
      operands <-
        traverse literalValue
          [argument | (Expl, argument) <- arguments]
      result <- evalPurePrim operation operands
      literalTerm result

    literalValue = \case
      CLit literal -> Just (VLit literal)
      _ -> Nothing

    literalTerm = \case
      VLit literal -> Just (CLit literal)
      VCtorI constructor universes [] ->
        Just (CCtorI constructor universes Nothing [])
      _ -> Nothing

    reduceApp fuel t = do
      let (hd0, args0) = spineOfTerm t
      hd <- go (fuel - 1) hd0
      applySpine (fuel - 1) hd args0

    applySpine fuel hd args
      | fuel <= 0 = pure (List.foldl' (\f (ic, a) -> CApp ic f a) hd args)
      | otherwise = case (hd, args) of
          (CLam lamIc _ _ body, (argIc, arg) : rest)
            | lamIc == argIc -> go (fuel - 1) (List.foldl' (\f (ic, a) -> CApp ic f a) (substTopTermAt d arg body) rest)
          (CProjM mode e f, _) -> do
            hd' <- go (fuel - 1) (CProjM mode e f)
            if hd' == hd
              then pure (List.foldl' (\f (ic, a) -> CApp ic f a) hd args)
              else applySpine (fuel - 1) hd' args
          (CProjAtM mode e f i, _) -> do
            hd' <- go (fuel - 1) (CProjAtM mode e f i)
            if hd' == hd
              then pure (List.foldl' (\f (ic, a) -> CApp ic f a) hd args)
              else applySpine (fuel - 1) hd' args
          (CGlobal g universes, _) -> do
            mBody <- unfoldReducibleGlobal d g universes
            case mBody of
              Just body -> applySpine (fuel - 1) body args
              Nothing -> pure (List.foldl' (\f (ic, a) -> CApp ic f a) hd args)
          _ -> pure (List.foldl' (\f (ic, a) -> CApp ic f a) hd args)

    reduceKnownMatch fuel scrutinee annotation resultAnnotation = select
      where
        preserve alternatives =
          pure (simplifyDecisionTerm (CMatch scrutinee annotation resultAnnotation alternatives))

        select [] = preserve []
        select alternatives@(CaseAlt pattern' guardTerm body : rest) =
          case matchCorePattern pattern' scrutinee of
            CorePatternMismatch -> select rest
            CorePatternUndecided -> preserve alternatives
            CorePatternMatched bindings -> do
              let instantiate =
                    instantiateCorePatternBody d bindings
                  body' = instantiate body
              case guardTerm of
                Nothing -> go fuel body'
                Just guardBody -> do
                  guard' <- go fuel (instantiate guardBody)
                  case guard' of
                    CCtor constructor _ []
                      | constructor == prelTrue -> go fuel body'
                      | constructor == prelFalse -> select rest
                    _ -> preserve alternatives

    -- A transparent named projection over a single-constructor family is
    -- commonly elaborated as a one-arm match. Preserve that ordinary
    -- eliminator semantics when its scrutinee is neutral: the exact checked
    -- constructor identity and source-field table authenticate the rewrite.
    -- Any richer match remains neutral and is handled by 'reduceKnownMatch'.
    transparentSelectorProjection scrutinee = \case
      [ CaseAlt
          (CPCtorM [] [] hidden constructor _ patterns)
          Nothing
          (CVar selectedIndex)
        ] -> do
          state <- get
          pure $ do
            constructorInfo <- Map.lookup constructor (csCtors state)
            dataInfo <- Map.lookup (ciData constructorInfo) (csDatas state)
            guard (diCtors dataInfo == [constructor])
            let explicitFields =
                  [fieldName | (Expl, fieldName) <- ciSourceFields constructorInfo]
            guard (length patterns == length explicitFields)
            source <-
              interleaveConstructorSourceBinders
                hidden
                (zip explicitFields patterns)
            let slots =
                  concatMap
                    ( \case
                        Left _ -> [Nothing]
                        Right (Just fieldName, CPVarM mode _) ->
                          [Just (fieldName, mode)]
                        Right (_, pattern') ->
                          replicate (patBindersC pattern') Nothing
                    )
                    source
                binderCount = length slots
                sourceIndex =
                  binderCount - selectedIndex - 1
            guard (sourceIndex >= 0)
            (fieldName, mode) <- slots `atMay` sourceIndex >>= id
            pure (CProjM mode scrutinee fieldName)
      _ -> pure Nothing

    -- A saturated typed constructor occurrence carries the complete checked Pi
    -- spine, including stable source-field identities. Reduce a named
    -- projection only when the exact constructor interface confirms one unique
    -- source field and the occurrence carries one matching named argument.
    -- Untyped legacy constructors and malformed/ambiguous spines stay neutral.
    typedConstructorProjection constructor arguments field = do
      state <- get
      pure $ do
        constructorInfo <- Map.lookup constructor (csCtors state)
        guard
          ( length
              [ ()
              | (_, Just sourceField) <- ciSourceFields constructorInfo
              , sourceField == field
              ]
              == 1
          )
        case
          [ caTerm argument
          | argument <- arguments
          , caName argument == Just field
          ] of
          [value] -> Just value
          _ -> Nothing

    atMay values index =
      case drop index values of
        value : _ -> Just value
        [] -> Nothing

unfoldReducibleGlobal :: Int -> GName -> [Level] -> CheckM (Maybe Term)
unfoldReducibleGlobal d g universes = do
  st <- get
  case Map.lookup g (csGlobals st) of
    Just gd | gdReducible gd, Just body <- gdValue gd ->
      -- Prefer the raw (un-normalized) recorded core body. The bounded
      -- syntactic reducer 'transparentProofReduce' steps through it itself,
      -- and it deliberately does NOT descend into stuck `if`/`match`
      -- branches — so a recursive definition applied to a neutral argument
      -- unfolds at most once per step and is bounded by that reducer's fuel.
      -- Quoting 'gdValue' instead would *fully* normalize the body (running
      -- every stuck branch via 'quote'/'closRun', which is unbounded) and
      -- diverges for such a recursive function (e.g. a §3.2.3 branch-fact
      -- normalization that unfolds a recursive predicate). The core body is
      -- closed and definitionally equal to the value's normal form, so
      -- non-recursive helpers still reduce identically.
      case specializeGlobalDefinitionBody universes gd of
        Just coreTm -> pure (Just coreTm)
        Nothing -> do
          ec <- ec_
          pure
            ( Just
                ( zonkTermWith
                    (\_ _ -> Nothing)
                    (substituteLevelParams universes)
                    0
                    (quote ec d body)
                )
            )
    _ -> pure Nothing

-- | Revisit selected operations after evidence solving. An application can
-- be elaborated while its dictionary is still a metavariable and only later
-- become a coherent standard arithmetic provider. Module finalization runs
-- this monotone pass over every surviving artifact so early elaboration order
-- cannot decide whether one semantic operation is canonicalized. Every
-- rewrite authenticates the exact trait, carrier, and selected dictionary.
canonicalizeStandardArithmeticOperations :: [InstanceEntry] -> Term -> Term
canonicalizeStandardArithmeticOperations instances = fixedPoint
  where
    rewrite =
      mapTermWithDepth
        (\_ term -> case term of
           -- A certificate deliberately separates its canonical conclusion
           -- from the exact provider proposition that justified it. Module
           -- finalization normalizes the conclusion and replay material
           -- together so the proof term keeps the same type as its
           -- canonicalized surroundings. The checked provider proposition
           -- and proof source remain exact; the independent verifier checks
           -- their authenticated relation to the replay goal.
           CArithmeticProof certificate ->
             Just
               ( CArithmeticProof
                   certificate
                     { acGoal =
                         fixedPoint (acGoal certificate)
                     , acReplayGoal =
                         fixedPoint (acReplayGoal certificate)
                     , acAssumptions =
                         map canonicalizeAssumption
                           (acAssumptions certificate)
                     }
               )
           _ -> canonicalStandardArithmeticOperation instances term)
        0
    fixedPoint term =
      let term' = rewrite term
       in if term' == term then term else fixedPoint term'

    canonicalizeAssumption assumption =
      assumption
        { aaReplayProposition =
            fixedPoint (aaReplayProposition assumption)
        }

canonicalStandardArithmeticOperation :: [InstanceEntry] -> Term -> Maybe Term
canonicalStandardArithmeticOperation instances term =
  canonicalTrustedNaturalLiteralBridge term
    <|> canonicalTrustedIntegerPrimitive term
    <|> canonicalStandardBooleanOperation term
    <|> canonicalStandardFromIntegerOperation instances term
    <|> canonicalStandardBinaryOperation instances term
    <|> canonicalStandardComparisonOperation instances term

-- | Compute the exact closed Nat-to-Integer bridge used by the standard Nat
-- arithmetic dictionaries. Nat literals and Integer literals share the exact
-- arbitrary-precision Core literal payload, so this removes only a checked,
-- resolved bridge application; open operands and user functions stay opaque.
canonicalTrustedNaturalLiteralBridge :: Term -> Maybe Term
canonicalTrustedNaturalLiteralBridge application =
  case spineOfTerm (stripIdentityWrappers application) of
    (headTerm, [(Expl, literal@(CLit (LitInt value)))])
      | value >= 0
      , termHeadGlob (stripIdentityWrappers headTerm)
          `elem`
            [ Just prelNatToInt
            , Just (GName primModule (gKey prelNatToInt))
            ] ->
          Just literal
    _ -> Nothing

-- | Expose the exact short-circuit Core semantics of the resolved prelude
-- Boolean combinators. The right operand of conjunction/disjunction remains
-- forced only in the selected branch, so this is a semantic identity
-- normalization rather than an eager Boolean rewrite.
canonicalStandardBooleanOperation :: Term -> Maybe Term
canonicalStandardBooleanOperation application =
  case spineOfTerm (stripIdentityWrappers application) of
    (headTerm, arguments)
      | termHeadGlob (stripIdentityWrappers headTerm) == Just prelOr
      , Just (left, right) <-
          last2 [argument | (Expl, argument) <- arguments] ->
          Just (CIf left trueTerm (CForceE right (Just (CGlob prelBool))))
      | termHeadGlob (stripIdentityWrappers headTerm) == Just prelAnd
      , Just (left, right) <-
          last2 [argument | (Expl, argument) <- arguments] ->
          Just (CIf left (CForceE right (Just (CGlob prelBool))) falseTerm)
      | termHeadGlob (stripIdentityWrappers headTerm) == Just prelNot
      , [argument] <- [candidate | (Expl, candidate) <- arguments] ->
          Just (CIf argument falseTerm trueTerm)
    _ -> Nothing
  where
    trueTerm = CCtorI prelTrue [] Nothing []
    falseTerm = CCtorI prelFalse [] Nothing []

-- | Evaluation quotes a wired-in primitive value through the internal
-- @__prim@ module. Final Core and certificates use the corresponding checked
-- @std.prelude@ identity instead. The shared primitive classifiers authorize
-- exactly this finite integer-operation family; no user spelling or arbitrary
-- internal global is rewritten.
canonicalTrustedIntegerPrimitive :: Term -> Maybe Term
canonicalTrustedIntegerPrimitive = \case
  CGlobal global universes
    | Just canonical <- canonicalTrustedIntPrimitive global
    , global /= canonical ->
        Just (CGlobal canonical universes)
  _ -> Nothing

-- | Lower one fully selected standard @FromInteger Nat@ application to the
-- canonical Nat literal consumed by the arithmetic reifier. The selected
-- dictionary, checked instance head, and nonnegative literal jointly provide
-- the authority; user dictionaries and negative literals remain untouched.
-- This rewrite runs before enclosing order operations in the fixed-point pass,
-- so a literal does not become hidden below @natToInt@ first.
canonicalStandardFromIntegerOperation
  :: [InstanceEntry]
  -> Term
  -> Maybe Term
canonicalStandardFromIntegerOperation instances application = do
  let trait = gPrel traitFromInteger
      (headTerm, arguments) =
        spineOfTerm (stripIdentityWrappers application)
      explicitArguments =
        [argument | (Expl, argument) <- arguments]
      implicitArguments =
        [argument | (Impl, argument) <- arguments]
      exactAccessor global =
        global == gPrel "fromInteger"
          || global == memberGlobal trait "fromInteger"
      selectedDictionary =
        case stripIdentityWrappers headTerm of
          CProjM _ dictionary "fromInteger" -> Just dictionary
          CProjAtM _ dictionary "fromInteger" _ -> Just dictionary
          candidate
            | Just global <- termHeadGlob candidate
            , exactAccessor global
            , carrier : dictionary : _ <- implicitArguments
            , isNatType carrier ->
                Just dictionary
          _ -> Nothing
  [CLit (LitInt literal)] <- pure explicitArguments
  guard (literal >= 0)
  dictionary <- selectedDictionary
  guard
    ( standardPreludeDictionaryIn
        instances
        trait
        (\case
          [headType] -> isNatType headType
          _ -> False)
        dictionary
    )
  pure (CLit (LitInt literal))

canonicalStandardBinaryOperation :: [InstanceEntry] -> Term -> Maybe Term
canonicalStandardBinaryOperation instances application =
  case spineOfTerm (stripIdentityWrappers application) of
    (headTerm, arguments)
      | Just (operation, trait, dictionary, selectedDomain, proofArguments) <-
          selectedOperation headTerm arguments
      , Just (left, right) <-
          last2 [argument | (Expl, argument) <- arguments]
      , Just domain <-
          selectedDomain <|> uniqueDictionaryDomain trait dictionary
      , operationIsTotal operation
          || any checkedProofArgument proofArguments
      , standardPreludeDictionaryIn
          instances
          trait
          (\case
             [headType] -> arithmeticDomainForCarrier headType == Just domain
             _ -> False)
          dictionary ->
          lower domain operation left right
    _ -> Nothing
  where
    selectedOperation headTerm arguments =
      globalOperation headTerm arguments
        <|> projectedOperation headTerm arguments

    globalOperation headTerm arguments = do
      operation <- termHeadGlob (stripIdentityWrappers headTerm)
      (operationKind, trait) <- operationDescriptor operation
      carrier : dictionary : proofArguments <-
        pure [argument | (Impl, argument) <- arguments]
      domain <- arithmeticDomainForCarrier carrier
      pure
        ( operationKind
        , trait
        , dictionary
        , Just domain
        , proofArguments
        )

    projectedOperation headTerm arguments = case headTerm of
      CProjM _ dictionary member -> do
        (operationKind, trait) <- projectedDescriptor member
        pure
          ( operationKind
          , trait
          , dictionary
          , Nothing
          , [argument | (Impl, argument) <- arguments]
          )
      CProjAtM _ dictionary member _ -> do
        (operationKind, trait) <- projectedDescriptor member
        pure
          ( operationKind
          , trait
          , dictionary
          , Nothing
          , [argument | (Impl, argument) <- arguments]
          )
      _ -> Nothing

    operationIsTotal = \case
      ArithmeticAdd -> True
      ArithmeticMultiply -> True
      ArithmeticSubtract -> False
      ArithmeticDivide -> False
      ArithmeticModulo -> False

    -- A checked operation may be lowered to its primitive implementation only
    -- after its erased domain argument has been discharged.  Before zonking,
    -- an unresolved proof is represented by a Core metavariable; preserving
    -- that application keeps the exact proof dependency available to delayed
    -- conversion.  The application checker has already checked every
    -- non-meta argument against the selected method telescope, so no source
    -- spelling or untyped proof assertion is trusted here.
    checkedProofArgument proof =
      not
        ( getAny
            ( foldTerm
                (\case
                   CMeta _ -> Any True
                   _ -> Any False)
                (const mempty)
                proof
            )
        )

    operationDescriptor operation
      | operation `elem` [prelAddOp, prelAddMethod, memberGlobal prelAdd "add"] =
          Just (ArithmeticAdd, prelAdd)
      | operation `elem` [gPrel "*", gPrel "multiply", memberGlobal (gPrel "Mul") "multiply"] =
          Just (ArithmeticMultiply, gPrel "Mul")
      | operation `elem` [gPrel "-", gPrel "subtract", memberGlobal (gPrel "CheckedSub") "subtract"] =
          Just (ArithmeticSubtract, gPrel "CheckedSub")
      | operation `elem` [gPrel "/", gPrel "divide", memberGlobal (gPrel "CheckedDiv") "divide"] =
          Just (ArithmeticDivide, gPrel "CheckedDiv")
      | operation `elem` [gPrel "%", gPrel "modulo", memberGlobal (gPrel "CheckedMod") "modulo"] =
          Just (ArithmeticModulo, gPrel "CheckedMod")
      | otherwise = Nothing

    projectedDescriptor member
      | member == "add" = Just (ArithmeticAdd, prelAdd)
      | member == "multiply" = Just (ArithmeticMultiply, gPrel "Mul")
      | member == "subtract" = Just (ArithmeticSubtract, gPrel "CheckedSub")
      | member == "divide" = Just (ArithmeticDivide, gPrel "CheckedDiv")
      | member == "modulo" = Just (ArithmeticModulo, gPrel "CheckedMod")
      | otherwise = Nothing

    uniqueDictionaryDomain trait dictionary =
      case
          [ domain
          | domain <- [ArithmeticNatural, ArithmeticInteger]
          , standardPreludeDictionaryIn
              instances
              trait
              (\case
                [headType] ->
                  arithmeticDomainForCarrier headType == Just domain
                _ -> False)
              dictionary
          ] of
        [domain] -> Just domain
        _ -> Nothing

    lower domain operation left right = case (domain, operation) of
      (ArithmeticNatural, ArithmeticAdd) ->
        Just (binary (CGlob prelNatAdd) left right)
      (ArithmeticNatural, ArithmeticMultiply) ->
        Just (binary (CGlob prelNatMultiply) left right)
      (ArithmeticNatural, ArithmeticSubtract) ->
        Just (naturalPrimitive "subInt" left right)
      (ArithmeticNatural, ArithmeticDivide) ->
        Just (naturalPrimitive "divInt" left right)
      (ArithmeticNatural, ArithmeticModulo) ->
        Just (naturalPrimitive "modInt" left right)
      (ArithmeticInteger, ArithmeticAdd) ->
        Just (integerPrimitive "addInt" left right)
      (ArithmeticInteger, ArithmeticMultiply) ->
        Just (integerPrimitive "mulInt" left right)
      (ArithmeticInteger, ArithmeticSubtract) ->
        Just (integerPrimitive "subInt" left right)
      (ArithmeticInteger, ArithmeticDivide) ->
        Just (integerPrimitive "divInt" left right)
      (ArithmeticInteger, ArithmeticModulo) ->
        Just (integerPrimitive "modInt" left right)
      (ArithmeticTypeLevel, _) -> Nothing
      (ArithmeticProviderLaw, _) -> Nothing

    binary function left right = CApp Expl (CApp Expl function left) right
    unary function argument = CApp Expl function argument
    integerPrimitive primitive =
      binary (CGlob (gPrel primitive))
    naturalPrimitive primitive left right =
      unary
        (CGlob (gPrel "natOfInt"))
        ( binary
            (CGlob (gPrel primitive))
            (unary (CGlob prelNatToInt) left)
            (unary (CGlob prelNatToInt) right)
        )

-- | Canonicalize the public standard equality and order combinators while
-- their selected dictionary is still explicit. KCore arithmetic certificates
-- deliberately recognize only primitive comparison identities; this
-- evidence-checked lowering is the bridge from overloaded source semantics
-- to that portable representation.
canonicalStandardComparisonOperation :: [InstanceEntry] -> Term -> Maybe Term
canonicalStandardComparisonOperation instances application = do
  (headTerm, arguments) <-
    pure (spineOfTerm (stripIdentityWrappers application))
  (comparison, trait, dictionary, carrier) <-
    selectedComparison headTerm arguments
  (left, right) <- last2 [argument | (Expl, argument) <- arguments]
  domain <- arithmeticDomainForCarrier carrier
  guard
    ( standardPreludeDictionaryIn
        instances
        trait
        (\case
           [headType] -> arithmeticDomainForCarrier headType == Just domain
           _ -> False)
        dictionary
    )
  let primitive = CGlob (gPrel comparison)
      convert = case domain of
        ArithmeticNatural ->
          \operand -> CApp Expl (CGlob prelNatToInt) operand
        ArithmeticInteger -> id
        ArithmeticTypeLevel -> id
        ArithmeticProviderLaw -> id
  pure
    ( CApp Expl
        (CApp Expl primitive (convert left))
        (convert right)
    )
  where
    selectedComparison headTerm arguments =
      selectedGlobal headTerm arguments
        <|> selectedProjection headTerm arguments

    selectedGlobal headTerm arguments = do
      operation <- termHeadGlob (stripIdentityWrappers headTerm)
      (comparison, trait) <- comparisonDescriptor operation
      carrier : dictionary : _ <-
        pure [argument | (Impl, argument) <- arguments]
      pure (comparison, trait, dictionary, carrier)

    selectedProjection headTerm arguments = do
      (dictionary, member) <- case stripIdentityWrappers headTerm of
        CProjM _ dictionary' member' -> Just (dictionary', member')
        CProjAtM _ dictionary' member' _ -> Just (dictionary', member')
        _ -> Nothing
      (comparison, trait) <- projectedComparisonDescriptor member
      domain <-
        uniqueDictionaryDomain trait dictionary
      pure (comparison, trait, dictionary, arithmeticCarrierTerm domain)

    comparisonDescriptor operation
      | operation
          `elem`
            [ gPrel "=="
            , memberGlobal (gPrel "Eq") "=="
            ] =
          Just ("eqInt", gPrel "Eq")
      | operation == gPrel "<" =
          Just ("ltInt", prelOrd)
      | operation == gPrel "<=" =
          Just ("leInt", prelOrd)
      | otherwise = Nothing

    projectedComparisonDescriptor member
      | member == "==" = Just ("eqInt", gPrel "Eq")
      | member == "<" = Just ("ltInt", prelOrd)
      | member == "<=" = Just ("leInt", prelOrd)
      | otherwise = Nothing

    uniqueDictionaryDomain trait dictionary =
      case
          [ domain
          | domain <- [ArithmeticNatural, ArithmeticInteger]
          , standardPreludeDictionaryIn
              instances
              trait
              (\case
                [headType] ->
                  arithmeticDomainForCarrier headType == Just domain
                _ -> False)
              dictionary
          ] of
        [domain] -> Just domain
        _ -> Nothing

    arithmeticCarrierTerm = \case
      ArithmeticNatural -> CGlob prelNat
      ArithmeticInteger -> CGlob prelInteger
      ArithmeticTypeLevel -> CGlob prelTypeLevel
      ArithmeticProviderLaw -> CGlob prelUnit

arithmeticDomainForCarrier :: Term -> Maybe ArithmeticDomain
arithmeticDomainForCarrier carrier =
  case termHeadGlob (stripIdentityWrappers carrier) of
    Just global
      | global == prelNat -> Just ArithmeticNatural
      | global == prelInteger || global == prelInt -> Just ArithmeticInteger
    _ -> Nothing

-- | Authenticate the compiler-owned prelude instance for one Nat trait.
-- Instance identity, trait identity, premise closure, and checked head carrier
-- must all agree; rendered dictionary/member spellings are not authority.
standardNaturalDictionary :: GName -> Term -> CheckM Bool
standardNaturalDictionary trait =
  standardPreludeDictionary
    trait
    (\case
      [headType] -> isNatType headType
      _ -> False)

-- | Reify a Nat arithmetic expression without erasing the authority that
-- selected its overloaded operations. The shared termination reifier handles
-- already-canonical Core. Numeric literals may additionally occur as a
-- checked @FromInteger Nat@ method application; admit that form only after
-- authenticating the exact coherent standard dictionary. This keeps
-- arithmetic proof normalization provider-driven instead of unfolding an
-- arbitrary same-shaped function.
selectedNatArithmeticExpression :: Int -> Term -> CheckM (Maybe AExpr)
selectedNatArithmeticExpression =
  selectedArithmeticExpression ArithmeticNatural

selectedNatArithmeticExpressionDirect :: Int -> Term -> CheckM (Maybe AExpr)
selectedNatArithmeticExpressionDirect depth term =
  case arithOf depth term of
    Just expression -> pure (Just expression)
    Nothing ->
      case spineOfTerm (stripIdentityWrappers term) of
        (headTerm, arguments)
          | [CLit (LitInt literal)] <-
              [argument | (Expl, argument) <- arguments]
          , literal >= 0
          , Just dictionary <- selectedFromIntegerDictionary headTerm arguments -> do
              standard <- standardNaturalDictionary (gPrel traitFromInteger) dictionary
              pure (if standard then Just (AConst literal) else Nothing)
        _ -> pure Nothing
  where
    selectedFromIntegerDictionary headTerm arguments =
      case stripIdentityWrappers headTerm of
        CProjM _ dictionary member
          | member == "fromInteger" -> Just dictionary
        CProjAtM _ dictionary member _
          | member == "fromInteger" -> Just dictionary
        candidate
          | termHeadGlob candidate
              `elem`
                [ Just (gPrel "fromInteger")
                , Just (memberGlobal (gPrel traitFromInteger) "fromInteger")
                ] ->
              case [argument | (Impl, argument) <- arguments] of
                carrier : dictionary : _
                  | isNatType carrier -> Just dictionary
                _ -> Nothing
        _ -> Nothing

memberGlobal :: GName -> Text -> GName
memberGlobal (GName m t) member = GName m (t <> "." <> member)

termHeadGlob :: Term -> Maybe GName
termHeadGlob = \case
  CApp _ f _ -> termHeadGlob f
  CUniverseLift _ _ _ term -> termHeadGlob term
  CGlob g -> Just g
  CGlobal g _ -> Just g
  CCtor g _ [] -> Just g
  CCtorI g _ _ [] -> Just g
  _ -> Nothing

relationIsPrimitiveLtInt :: Int -> Term -> CheckM Bool
relationIsPrimitiveLtInt d relTm = do
  relNorm <- normalizeTermAt d relTm
  if directLt relNorm
    then pure True
    else do
      let x = CVar 1
          y = CVar 0
          relUnderBinders = shiftTerm 2 0 relNorm
          applied = CApp Expl (CApp Expl relUnderBinders x) y
      appliedNorm <- normalizeTermAt (d + 2) applied
      pure $ case spineOfTerm appliedNorm of
        (CGlob g, args)
          | intCmpPrim g == Just PrimLtInt ->
              case last2 [a | (Expl, a) <- args] of
                Just (a, b) -> a == x && b == y
                Nothing -> False
        _ -> False
  where
    directLt = \case
      CGlob g -> intCmpPrim g == Just PrimLtInt
      _ -> False

normalizeTermAt :: Int -> Term -> CheckM Term
normalizeTermAt d t = do
  st <- get
  -- 'csFacts' alters conversion-time reduction of rigids.  Rather than trying
  -- to serialize arbitrary 'Value' facts into a cache key, bypass the cache
  -- while such facts are active.  Boolean branch facts are handled at the
  -- proposition-cache layer, not here.
  let cacheable =
        Map.null (csFacts st)
          && null (unsolvedMetasOf st t)
          && termCacheUniverseScoped st t
      key =
        NormCacheKey
          (csNormEpoch st)
          (csActiveUniverseDefinition st)
          d
          (renderStructuralTermKey t)
  case if cacheable then Map.lookup key (csNormCache st) else Nothing of
    Just cached -> pure cached
    Nothing -> do
      ec <- ec_
      let normalized =
            if maxFreeIndexTerm t >= d
              then simplifyDecisionTerm t
              else
                let env = [VRigid lvl [] | lvl <- [d - 1, d - 2 .. 0]]
                    v = force ec (eval ec env t)
                 in simplifyDecisionTerm (quote ec d v)
      let storeable =
            cacheable
              && null (unsolvedMetasOf st normalized)
              && termCacheUniverseScoped st normalized
      when storeable $
        modify' $ \s ->
          s {csNormCache = boundedInsert maxNormCacheEntries key normalized (csNormCache s)}
      pure normalized

assumeBoolM :: Int -> Bool -> Term -> CheckM [AFact]
assumeBoolM d truth t = do
  mFact <- boolRelBranchM d t
  pure $ case mFact >>= if truth then Just else negateFact of
    Just assumed -> [assumed]
    Nothing -> []

-- | Classify a boolean known from control flow into arithmetic evidence
-- without normalizing arbitrary function calls.  Branch conditions may be
-- recursive, effectful after erasure, or simply large; they are proof sources
-- only when their surface Core shape is already an arithmetic comparison.
-- Losing a branch fact is conservative, while unfolding a recursive condition
-- during checked arithmetic can make elaboration non-terminating.
boolRelBranchM :: Int -> Term -> CheckM (Maybe AFact)
boolRelBranchM d t0 = case simplifyDecisionTerm t0 of
  CIf c th el
    | isTrueTm th, isFalseTm el -> boolRelBranchM d c
    | isFalseTm th, isTrueTm el -> (>>= negateFact) <$> boolRelBranchM d c
    | isTrueTm th -> do
        cFact <- boolRelBranchM d c
        elFact <- boolRelBranchM d el
        pure (cFact >>= \cf -> elFact >>= combineOr cf)
  t -> case boolRel d t of
    Just fact -> pure (Just fact)
    Nothing -> do
      selectedStandardOrderFact d t >>= \case
        Just (_, fact) -> pure (Just fact)
        Nothing ->
          primitiveEqBranchM d t >>= \case
            Just fact -> pure (Just fact)
            Nothing -> compareMatchRelBranchM d t
  where
    isTrueTm = \case CCtor g _ [] -> g == prelTrue; _ -> False
    isFalseTm = \case CCtor g _ [] -> g == prelFalse; _ -> False
    combineOr (AFact ACmpLt a b) (AFact ACmpEq a' b') | a == a' && b == b' = Just (AFact ACmpLe a b)
    combineOr (AFact ACmpEq a b) (AFact ACmpLt a' b') | a == a' && b == b' = Just (AFact ACmpLe a b)
    combineOr _ _ = Nothing

-- | Decode the standard Nat/Integer order combinators while their exact
-- selected dictionary is still present. The public operators are ordinary
-- prelude definitions rather than trait members, so unrestricted transparent
-- reduction would turn them into a compare/match tree and lose provider
-- identity. Return the authenticated carrier domain with the fact so
-- certificate construction cannot silently cross domains.
selectedStandardOrderFact
  :: Int
  -> Term
  -> CheckM (Maybe (ArithmeticDomain, AFact))
selectedStandardOrderFact depth term =
  case spineOfTerm (stripIdentityWrappers term) of
    (headTerm, arguments)
      | Just operation <- termHeadGlob (stripIdentityWrappers headTerm)
      , operation `elem` map gPrel ["<", "<=", ">", ">="] -> do
          let implicitArguments = [argument | (Impl, argument) <- arguments]
              explicitArguments = [argument | (Expl, argument) <- arguments]
          case (implicitArguments, last2 explicitArguments) of
            (carrier : dictionary : _, Just (left, right)) ->
              case arithmeticDomainForCarrier carrier of
                Nothing -> pure Nothing
                Just domain -> do
                  standard <-
                    standardPreludeDictionary
                      prelOrd
                      (\case
                        [headType] ->
                          arithmeticDomainForCarrier headType == Just domain
                        _ -> False)
                      dictionary
                  if not standard
                    then pure Nothing
                    else do
                      leftExpression <-
                        selectedArithmeticExpression domain depth left
                      rightExpression <-
                        selectedArithmeticExpression domain depth right
                      pure $ do
                        left' <- leftExpression
                        right' <- rightExpression
                        pure
                          ( domain
                          , if operation == gPrel "<"
                              then AFact ACmpLt left' right'
                              else if operation == gPrel "<="
                                then AFact ACmpLe left' right'
                                else if operation == gPrel ">"
                                  then AFact ACmpLt right' left'
                                  else AFact ACmpLe right' left'
                          )
            _ -> pure Nothing
    _ -> pure Nothing

-- | Recognize an unresolved standard equality operation before transparent
-- projection reduction has exposed its primitive implementation.  Deferred
-- checked-arithmetic goals can be revisited while the branch condition still
-- has this shape.  The operation head, carrier, and selected dictionary are
-- all authenticated by semantic identity; user-defined equality operations
-- and dictionaries remain outside the arithmetic proof source.
primitiveEqBranchM :: Int -> Term -> CheckM (Maybe AFact)
primitiveEqBranchM d term = case spineOfTerm term of
  (CGlob operation, arguments)
    | operation == gPrel "==" -> do
        let implicits = [argument | (Impl, argument) <- arguments]
            explicits = [argument | (Expl, argument) <- arguments]
        case (implicits, last2 explicits) of
          (carrier : dictionary : _, Just (lhs, rhs)) -> do
            authenticated <- standardPrimitiveEqDict carrier dictionary
            if not authenticated
              then pure Nothing
              else do
                lhsExpression <- selectedNatArithmeticExpression d lhs
                rhsExpression <- selectedNatArithmeticExpression d rhs
                pure (AFact ACmpEq <$> lhsExpression <*> rhsExpression)
          _ -> pure Nothing
  _ -> pure Nothing

standardPrimitiveEqDict :: Term -> Term -> CheckM Bool
standardPrimitiveEqDict carrier dictionary =
  if primitiveOrderedType (stripIdentityWrappers carrier)
    then
      standardPreludeDictionary
        (gPrel "Eq")
        (\headArguments ->
           map stripIdentityWrappers headArguments
             == [stripIdentityWrappers carrier])
        dictionary
    else pure False

comparePatternFactsM :: Int -> Term -> CorePat -> CheckM [AFact]
comparePatternFactsM d scrut pat = do
  mArgs <- primitiveOrderedCompareArgs d scrut
  pure $ case mArgs of
    Just (aa, bb) -> maybeToList $ do
      mkFact <- compareCtorFact pat
      pure (mkFact aa bb)
    Nothing -> []
  where
    compareCtorFact = \case
      CPCtor g _ [] | g == prelLT -> Just (\a b -> AFact ACmpLt a b)
      CPCtor g _ [] | g == prelEQ -> Just (\a b -> AFact ACmpEq a b)
      CPCtor g _ [] | g == prelGT -> Just (\a b -> AFact ACmpLt b a)
      _ -> Nothing

compareMatchRelBranchM :: Int -> Term -> CheckM (Maybe AFact)
compareMatchRelBranchM d = \case
  CMatch scrut _ _ alts -> do
    mArgs <- primitiveOrderedCompareArgsRaw d scrut
    pure $ do
      (aa, bb) <- mArgs
      cmp <- compareBoolMatch alts
      pure $ case cmp of
        CompareLt -> AFact ACmpLt aa bb
        CompareLe -> AFact ACmpLe aa bb
        CompareGt -> AFact ACmpLt bb aa
        CompareGe -> AFact ACmpLe bb aa
  _ -> pure Nothing

compareBoolMatch :: [CaseAlt] -> Maybe CompareBoolMatch
compareBoolMatch alts = do
  branches <- traverse compareBoolBranch alts
  let tags = sort [tag | (tag, _) <- branches]
      expectedTags = ["EQ", "GT", "LT"] :: [Text]
  unlessMaybe (tags == expectedTags)
  lt <- lookup "LT" branches
  eq <- lookup "EQ" branches
  gt <- lookup "GT" branches
  case (lt, eq, gt) of
    (True, False, False) -> Just CompareLt
    (True, True, False) -> Just CompareLe
    (False, False, True) -> Just CompareGt
    (False, True, True) -> Just CompareGe
    _ -> Nothing
  where
    unlessMaybe True = Just ()
    unlessMaybe False = Nothing

    compareBoolBranch :: CaseAlt -> Maybe (Text, Bool)
    compareBoolBranch (CaseAlt (CPCtor g _ []) Nothing body)
      | g == prelLT = (\b -> ("LT", b)) <$> boolBody body
      | g == prelEQ = (\b -> ("EQ", b)) <$> boolBody body
      | g == prelGT = (\b -> ("GT", b)) <$> boolBody body
    compareBoolBranch _ = Nothing

    boolBody = \case
      CCtor g _ [] | g == prelTrue -> Just True
      CCtor g _ [] | g == prelFalse -> Just False
      _ -> Nothing

primitiveOrderedCompareArgs :: Int -> Term -> CheckM (Maybe (AExpr, AExpr))
primitiveOrderedCompareArgs d t = do
  raw <- primitiveOrderedCompareArgsRaw d t
  case raw of
    Just args -> pure (Just args)
    Nothing -> do
      t' <- transparentProofReduce d (96 :: Int) t
      primitiveOrderedCompareArgsRaw d t' >>= \case
        Just args -> pure (Just args)
        Nothing -> pure (primitiveCompareShape d t')

primitiveOrderedCompareArgsRaw :: Int -> Term -> CheckM (Maybe (AExpr, AExpr))
primitiveOrderedCompareArgsRaw d t =
  case rawCompareArgs t of
    Just (tyArg, dictArg, aa, bb) -> do
      ok <- standardPrimitiveOrdDict tyArg dictArg
      pure (if ok then Just (aa, bb) else Nothing)
    Nothing -> pure Nothing
  where
    rawCompareArgs :: Term -> Maybe (Term, Term, AExpr, AExpr)
    rawCompareArgs x = case spineOfTerm x of
      (CGlob g, args)
        | g == prelCompare -> do
            let impls = [a | (Impl, a) <- args]
                ex = [a | (Expl, a) <- args]
            case (impls, last2 ex) of
              (tyArg : dictArg : _, Just (a, b))
                | primitiveOrderedType tyArg -> do
                    aa <- arithOf d a
                    bb <- arithOf d b
                    Just (tyArg, dictArg, aa, bb)
              _ -> Nothing
      _ -> Nothing

primitiveCompareShape :: Int -> Term -> Maybe (AExpr, AExpr)
primitiveCompareShape d t0 = case simplifyDecisionTerm t0 of
  CIf lt (CCtor ltG _ []) (CIf eq (CCtor eqG _ []) (CCtor gtG _ []))
    | ltG == prelLT
    , eqG == prelEQ
    , gtG == prelGT -> do
        AFact ACmpLt a b <- boolRel d lt
        AFact ACmpEq a' b' <- boolRel d eq
        if a == a' && b == b'
          then Just (a, b)
          else Nothing
  _ -> Nothing

primitiveOrderedType :: Term -> Bool
primitiveOrderedType ty =
  let carrier = stripIdentityWrappers ty
   in carrier == CGlob prelInteger
        || carrier == CGlob prelNat

standardPrimitiveOrdDict :: Term -> Term -> CheckM Bool
standardPrimitiveOrdDict ty dictionary =
  standardPreludeDictionary
    prelOrd
    (\headArguments ->
       map stripIdentityWrappers headArguments
         == [stripIdentityWrappers ty])
    dictionary

gnameInModule :: GName -> ModuleName -> Bool
gnameInModule (GName m _) target = m == target

proveLt :: Set Int -> [AFact] -> Int -> Term -> Term -> CheckM Bool
proveLt natLvls facts d lhs rhs = do
  lhs' <- normalizeTermAt d lhs
  rhs' <- normalizeTermAt d rhs
  case (arithOf d lhs', arithOf d rhs') of
    (Just l, Just r) -> proveFact natLvls facts (AFact ACmpLt l r)
    _ -> pure False

proveEq :: Set Int -> [AFact] -> Int -> Term -> Term -> CheckM Bool
proveEq natLvls facts d lhs rhs = do
  lhs' <- normalizeTermAt d lhs
  rhs' <- normalizeTermAt d rhs
  if lhs' == rhs'
    then pure True
    else case (arithOf d lhs', arithOf d rhs') of
      (Just l, Just r) -> proveFact natLvls facts (AFact ACmpEq l r)
      _ -> pure False

proveNonNeg :: Set Int -> [AFact] -> Int -> Term -> CheckM Bool
proveNonNeg natLvls facts d t = do
  t' <- normalizeTermAt d t
  case arithOf d t' of
    Just a -> proveFact natLvls facts (AFact ACmpLe (AConst 0) a)
    Nothing -> pure False

proveBoolTrue :: Set Int -> [AFact] -> Int -> Term -> CheckM Bool
proveBoolTrue natLvls facts d t = do
  t' <- normalizeTermAt d t
  case t' of
    CCtor g _ [] | g == prelTrue -> pure True
    _ -> case boolRel d t' of
      Just fact -> proveFact natLvls facts fact
      Nothing -> pure False

-- | A Type-valued relation often encodes a decidable order as
-- `(p = True)`.  When normalization exposes that shape, the same arithmetic
-- evidence used for Bool-valued primitive orders can discharge the Type
-- proposition.  This is still conservative: arbitrary inhabited propositions
-- are not guessed.
proveTypeRelationTrue :: Set Int -> [AFact] -> Int -> Term -> CheckM Bool
proveTypeRelationTrue natLvls facts d t = do
  t' <- normalizeTermAt d t
  case boolEqualityTruePayload t' of
    Just b -> proveBoolTrue natLvls facts d b
    Nothing -> pure False

boolEqualityTruePayload :: Term -> Maybe Term
boolEqualityTruePayload t = case spineOfTerm (stripIdentityWrappers t) of
  (headTerm, args)
    | Just eqG <- termHeadGlob (stripIdentityWrappers headTerm)
    , eqG == prelEqType -> do
        let ex = [a | (Expl, a) <- args]
        (lhs, rhs) <- last2 ex
        case (stripIdentityWrappers lhs, stripIdentityWrappers rhs) of
          (relation, truth) | isTrueCtor truth -> Just relation
          (truth, relation) | isTrueCtor truth -> Just relation
          _ -> Nothing
  _ -> Nothing
  where
    isTrueCtor = \case
      CCtor g _ [] -> g == prelTrue
      CCtorI g _ _ [] -> g == prelTrue
      _ -> False

proveFact :: Set Int -> [AFact] -> AFact -> CheckM Bool
proveFact natLvls facts goal =
  if proveFactByBounds ArithmeticNaturalSemantics natLvls facts goal
    then pure True
    else pure False
