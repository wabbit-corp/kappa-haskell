-- | Pure, portable value-level arithmetic reasoning.
--
-- This module deliberately knows nothing about Core, source names, implicit
-- resolution, or the checker state.  Clients first reify authenticated
-- operations and evidence into 'AExpr'/'AFact'; this kernel then produces a
-- deterministic replay descriptor.  The same operation is used by
-- elaboration, termination, and the KCoreText trust boundary.
module Kappa.Arithmetic
  ( AExpr (..)
  , ACmp (..)
  , AFact (..)
  , AFormula (..)
  , ABounds (..)
  , ArithmeticNormalForm (..)
  , ArithmeticProofRule (..)
  , ArithmeticReplay (..)
  , ArithmeticFormulaReplay (..)
  , ArithmeticSemantics (..)
  , negateFact
  , formulaAssumptionFacts
  , proveFactByBounds
  , deriveArithmeticReplay
  , deriveArithmeticFormulaReplay
  , derivePrincipalAffineAssignment
  , verifyArithmeticReplay
  , reindexArithmeticFact
  , reindexArithmeticFormula
  , simplifyA
  , lowerBoundExpr
  ) where

import Control.Applicative ((<|>))
import Control.Monad (foldM)
import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import Data.Set (Set)
import qualified Data.Set as Set

-- | A symbolic arithmetic expression. Variables are identities chosen by the
-- reifying client: Core uses de Bruijn levels and KCoreText uses stable local
-- identities.
data AExpr
  = AConst !Integer
  | AVar !Int
  | AScale !Integer !AExpr
  | AAdd !AExpr !AExpr
  | ASub !AExpr !AExpr
  | AMul !AExpr !AExpr
  | ADiv !AExpr !AExpr
  | AMod !AExpr !AExpr
  | ANeg !AExpr
  | AMax !AExpr !AExpr
  | AMin !AExpr !AExpr
  | AIf !AFormula !AExpr !AExpr
  deriving stock (Eq, Ord, Show)

data ACmp = ACmpLt | ACmpLe | ACmpEq | ACmpNe
  deriving stock (Eq, Ord, Show)

data AFact = AFact !ACmp !AExpr !AExpr
  deriving stock (Eq, Ord, Show)

-- | A checked Boolean combination of authenticated arithmetic atoms.
-- Connective identity is established by the Core/KCore clients before a
-- formula reaches this portable kernel.
data AFormula
  = ATruth !Bool
  | AAtom !AFact
  | AAnd !AFormula !AFormula
  | AOr !AFormula !AFormula
  | ANot !AFormula
  deriving stock (Eq, Ord, Show)

data ABounds = ABounds !(Maybe Integer) !(Maybe Integer)
  deriving stock (Eq, Show)

data ALin = ALin !Integer !(Map Int Integer)
  deriving stock (Eq, Show)

newtype Monomial = Monomial (Map Int Int)
  deriving stock (Eq, Ord, Show)

newtype Poly = Poly (Map Monomial Integer)
  deriving stock (Eq, Show)

-- | Canonical material retained in an arithmetic certificate.  A verifier
-- recomputes this value instead of trusting a Boolean decision or a claimed
-- result.
data ArithmeticNormalForm
  = NormalPolynomial ![([(Int, Int)], Integer)]
    -- ^ Canonical monomials: each variable/exponent vector is kept together
    -- with its coefficient. Constants use the empty variable vector.
  | NormalLinear !Integer ![(Int, Integer)]
  | NormalLowerBound !Integer
  | NormalDisequality
  | NormalCaseSplit !AFormula !ArithmeticReplay !ArithmeticReplay
  deriving stock (Eq, Ord, Show)

data ArithmeticProofRule
  = ProvePolynomialEquality
  | ProveLinearEquality
  | ProveStrictLowerBound
  | ProveNonStrictLowerBound
  | ProveDisequality
  | ProveCaseSplit
  deriving stock (Eq, Ord, Show)

data ArithmeticReplay = ArithmeticReplay
  { arGoal :: !AFact
  , arRule :: !ArithmeticProofRule
  , arNormalForm :: !ArithmeticNormalForm
  }
  deriving stock (Eq, Ord, Show)

-- | Deterministic proof tree for one arithmetic Boolean formula. Atomic
-- leaves retain the existing independently replayable arithmetic witness.
-- For a false conjunction or true disjunction, the first derivable branch is
-- selected in source order; the rule constructor records that choice.
data ArithmeticFormulaReplay
  = ReplayTruth !Bool
  | ReplayAtom !Bool !ArithmeticReplay
  | ReplayAndTrue !ArithmeticFormulaReplay !ArithmeticFormulaReplay
  | ReplayAndFalseLeft !ArithmeticFormulaReplay
  | ReplayAndFalseRight !ArithmeticFormulaReplay
  | ReplayOrTrueLeft !ArithmeticFormulaReplay
  | ReplayOrTrueRight !ArithmeticFormulaReplay
  | ReplayOrFalse !ArithmeticFormulaReplay !ArithmeticFormulaReplay
  | ReplayNot !ArithmeticFormulaReplay
  deriving stock (Eq, Ord, Show)

-- | The exact partial-operation contract used while replaying one arithmetic
-- certificate.  The expression language is shared, but natural subtraction
-- carries a domain obligation whereas integer subtraction is total. Division
-- and modulo require a nonzero divisor. For Nat, the ambient nonnegativity
-- invariant makes a nonzero divisor positive; Integer also admits negatives.
data ArithmeticSemantics
  = ArithmeticNaturalSemantics
  | ArithmeticIntegerSemantics
  deriving stock (Eq, Ord, Show)

-- | Reindex every atom in one arithmetic fact into a certificate-local
-- context. A missing atom is a scope error, not a fresh variable.
reindexArithmeticFact :: Map Int Int -> AFact -> Maybe AFact
reindexArithmeticFact variables (AFact comparison lhs rhs) =
  AFact comparison
    <$> reindexExpression lhs
    <*> reindexExpression rhs
  where
    reindexExpression = \case
      AConst value -> Just (AConst value)
      AVar variable -> AVar <$> Map.lookup variable variables
      AScale scale expression ->
        AScale scale <$> reindexExpression expression
      AAdd lhs' rhs' -> binary AAdd lhs' rhs'
      ASub lhs' rhs' -> binary ASub lhs' rhs'
      AMul lhs' rhs' -> binary AMul lhs' rhs'
      ADiv lhs' rhs' -> binary ADiv lhs' rhs'
      AMod lhs' rhs' -> binary AMod lhs' rhs'
      ANeg expression -> ANeg <$> reindexExpression expression
      AMax lhs' rhs' -> binary AMax lhs' rhs'
      AMin lhs' rhs' -> binary AMin lhs' rhs'
      AIf condition thenExpression elseExpression ->
        AIf
          <$> reindexArithmeticFormula variables condition
          <*> reindexExpression thenExpression
          <*> reindexExpression elseExpression
    binary constructor lhs' rhs' =
      constructor
        <$> reindexExpression lhs'
        <*> reindexExpression rhs'

reindexArithmeticFormula :: Map Int Int -> AFormula -> Maybe AFormula
reindexArithmeticFormula variables = \case
  ATruth truth -> pure (ATruth truth)
  AAtom fact -> AAtom <$> reindexArithmeticFact variables fact
  AAnd lhs rhs ->
    AAnd
      <$> reindexArithmeticFormula variables lhs
      <*> reindexArithmeticFormula variables rhs
  AOr lhs rhs ->
    AOr
      <$> reindexArithmeticFormula variables lhs
      <*> reindexArithmeticFormula variables rhs
  ANot formula ->
    ANot <$> reindexArithmeticFormula variables formula

negateFact :: AFact -> Maybe AFact
negateFact = \case
  AFact ACmpLt a b -> Just (AFact ACmpLe b a)
  AFact ACmpLe a b -> Just (AFact ACmpLt b a)
  AFact ACmpEq a b -> Just (AFact ACmpNe a b)
  AFact ACmpNe a b -> Just (AFact ACmpEq a b)

-- | Extract exactly the polarity-safe atomic consequences of an assumption.
-- A true conjunction and a false disjunction expose both children; the
-- opposite polarities do not choose a branch. This is the certificate-side
-- equivalent of control-flow Boolean-fact decomposition.
formulaAssumptionFacts :: Bool -> AFormula -> Maybe [AFact]
formulaAssumptionFacts wanted = \case
  ATruth actual
    | actual == wanted -> Just []
    | otherwise -> Nothing
  AAtom fact
    | wanted -> Just [fact]
    | otherwise -> (: []) <$> negateFact fact
  AAnd lhs rhs
    | wanted ->
        (++)
          <$> formulaAssumptionFacts True lhs
          <*> formulaAssumptionFacts True rhs
    | otherwise -> Nothing
  AOr lhs rhs
    | not wanted ->
        (++)
          <$> formulaAssumptionFacts False lhs
          <*> formulaAssumptionFacts False rhs
    | otherwise -> Nothing
  ANot formula ->
    formulaAssumptionFacts (not wanted) formula

-- | Produce the unique replay descriptor for a fact in the supported
-- fragment. Before normalization, independently establish every partial
-- operation's domain from already-admitted assumptions. A reflexive equality
-- containing an unchecked partial operation is therefore not proof evidence.
deriveArithmeticReplay
  :: ArithmeticSemantics
  -> Set Int
  -> [AFact]
  -> AFact
  -> Maybe ArithmeticReplay
deriveArithmeticReplay semantics naturalVariables assumptions goal = do
  admitted <- admitArithmeticAssumptions semantics naturalVariables assumptions
  guardArithmeticDomain semantics naturalVariables admitted goal
  deriveWithCaseSplits admitted goal
  where
    deriveWithCaseSplits admitted goal' =
      case splitFirstConditionalFact goal' of
        Nothing ->
          deriveArithmeticReplayUnchecked naturalVariables admitted goal'
        Just (condition, thenGoal, elseGoal) -> do
          thenFacts <- formulaAssumptionFacts True condition
          elseFacts <- formulaAssumptionFacts False condition
          let thenAssumptions =
                map (specializeConditionalFact condition True) admitted
                  ++ thenFacts
              elseAssumptions =
                map (specializeConditionalFact condition False) admitted
                  ++ elseFacts
          thenReplay <-
            deriveArithmeticReplay
              semantics
              naturalVariables
              thenAssumptions
              thenGoal
          elseReplay <-
            deriveArithmeticReplay
              semantics
              naturalVariables
              elseAssumptions
              elseGoal
          pure
            ArithmeticReplay
              { arGoal = goal'
              , arRule = ProveCaseSplit
              , arNormalForm =
                  NormalCaseSplit condition thenReplay elseReplay
              }

-- | Solve exactly one assignable variable from an affine equality.
--
-- This is the assignment-producing counterpart of arithmetic replay, not a
-- heuristic equation rearranger. It first checks every partial-operation
-- domain using the same admitted assumptions as 'deriveArithmeticReplay',
-- then requires the normalized difference to contain exactly one variable
-- with a nonzero coefficient. The quotient must be exact and, for natural
-- arithmetic, nonnegative. Equations with no variable, multiple variables,
-- nonlinear residue, or a non-integral solution remain unsolved.
derivePrincipalAffineAssignment
  :: ArithmeticSemantics
  -> Set Int
  -> Set Int
  -> [AFact]
  -> AFact
  -> Maybe (Int, Integer)
derivePrincipalAffineAssignment semantics naturalVariables assignableVariables assumptions goal = do
  admitted <- admitArithmeticAssumptions semantics naturalVariables assumptions
  guardArithmeticDomain semantics naturalVariables admitted goal
  (lhs, rhs) <- case goal of
    AFact ACmpEq lhs' rhs' -> Just (lhs', rhs')
    _ -> Nothing
  ALin constant coefficients <-
    linOf (simplifyA naturalVariables admitted (ASub lhs rhs))
  (variable, coefficient) <- case Map.toAscList coefficients of
    [entry] -> Just entry
    _ -> Nothing
  if variable `Set.member` assignableVariables && coefficient /= 0
    then pure ()
    else Nothing
  let numerator = negate constant
  if numerator `rem` coefficient == 0
    then pure ()
    else Nothing
  let solution = numerator `quot` coefficient
  case semantics of
    ArithmeticNaturalSemantics
      | solution < 0 -> Nothing
    _ -> pure ()
  pure (variable, solution)

-- | Prove a Boolean formula from atomic assumptions. The recursive shape is
-- pure and deterministic; all arithmetic authority remains in
-- 'deriveArithmeticReplay'.
deriveArithmeticFormulaReplay
  :: ArithmeticSemantics
  -> Set Int
  -> [AFact]
  -> Bool
  -> AFormula
  -> Maybe ArithmeticFormulaReplay
deriveArithmeticFormulaReplay semantics naturalVariables assumptions =
  prove
  where
    prove wanted = \case
      ATruth actual
        | actual == wanted -> Just (ReplayTruth actual)
        | otherwise -> Nothing
      AAtom fact -> do
        selected <- if wanted then Just fact else negateFact fact
        replay <-
          deriveArithmeticReplay
            semantics
            naturalVariables
            assumptions
            selected
        pure (ReplayAtom wanted replay)
      AAnd lhs rhs
        | wanted ->
            ReplayAndTrue
              <$> prove True lhs
              <*> prove True rhs
        | otherwise ->
            case prove False lhs of
              Just replay -> Just (ReplayAndFalseLeft replay)
              Nothing -> ReplayAndFalseRight <$> prove False rhs
      AOr lhs rhs
        | wanted ->
            case prove True lhs of
              Just replay -> Just (ReplayOrTrueLeft replay)
              Nothing -> ReplayOrTrueRight <$> prove True rhs
        | otherwise ->
            ReplayOrFalse
              <$> prove False lhs
              <*> prove False rhs
      ANot formula ->
        ReplayNot <$> prove (not wanted) formula

deriveArithmeticReplayUnchecked :: Set Int -> [AFact] -> AFact -> Maybe ArithmeticReplay
deriveArithmeticReplayUnchecked naturalVariables assumptions goal =
  case goal of
    AFact ACmpEq lhs rhs ->
      let difference = simplifyA naturalVariables assumptions (ASub lhs rhs)
       in case polyOf difference of
            Just polynomial
              | polyIsZero polynomial
              , Just lhsPolynomial <-
                  polyOf (simplifyA naturalVariables assumptions lhs) ->
                  Just
                    ( ArithmeticReplay
                        goal
                        ProvePolynomialEquality
                        (NormalPolynomial (canonicalPolynomial lhsPolynomial))
                    )
            _ -> case linOf difference of
              Just (ALin constant coefficients)
                | constant == 0
                , all (== 0) (Map.elems coefficients) ->
                    Just
                      ( ArithmeticReplay
                          goal
                          ProveLinearEquality
                          (NormalLinear constant (Map.toAscList coefficients))
                      )
              Just linear@(ALin constant coefficients)
                | lowerBoundLin naturalVariables assumptions linear >= Just 0
                , lowerBoundLin naturalVariables assumptions (scaleLin (-1) linear) >= Just 0 ->
                    Just
                      ( ArithmeticReplay
                          goal
                          ProveLinearEquality
                          (NormalLinear constant (Map.toAscList coefficients))
                      )
              _ -> Nothing
    AFact ACmpLt lhs rhs -> do
      lower <- lowerBoundExpr naturalVariables assumptions (ASub rhs lhs)
      if lower >= 1
        then
          Just
            ( ArithmeticReplay
                goal
                ProveStrictLowerBound
                (NormalLowerBound lower)
            )
        else Nothing
    AFact ACmpLe lhs rhs -> do
      lower <- lowerBoundExpr naturalVariables assumptions (ASub rhs lhs)
      if lower >= 0
        then
          Just
            ( ArithmeticReplay
                goal
                ProveNonStrictLowerBound
                (NormalLowerBound lower)
            )
        else Nothing
    AFact ACmpNe lhs rhs
      | disequalityAssumed lhs rhs assumptions ->
          Just
            ( ArithmeticReplay
                goal
                ProveDisequality
                NormalDisequality
            )
      | otherwise ->
          let lhsBelow = lowerBoundExpr naturalVariables assumptions (ASub rhs lhs)
              rhsBelow = lowerBoundExpr naturalVariables assumptions (ASub lhs rhs)
           in if lhsBelow >= Just 1 || rhsBelow >= Just 1
                then
                  Just
                    ( ArithmeticReplay
                        goal
                        ProveDisequality
                        NormalDisequality
                    )
                else Nothing
  where
    disequalityAssumed lhs rhs =
      any $ \case
        AFact ACmpNe lhs' rhs' ->
          (lhs == lhs' && rhs == rhs') || (lhs == rhs' && rhs == lhs')
        _ -> False

verifyArithmeticReplay
  :: ArithmeticSemantics
  -> Set Int
  -> [AFact]
  -> ArithmeticReplay
  -> Bool
verifyArithmeticReplay semantics naturalVariables assumptions replay =
  deriveArithmeticReplay semantics naturalVariables assumptions (arGoal replay)
    == Just replay

proveFactByBounds :: ArithmeticSemantics -> Set Int -> [AFact] -> AFact -> Bool
proveFactByBounds semantics naturalVariables assumptions =
  maybe False (const True)
    . deriveArithmeticReplay semantics naturalVariables assumptions

-- | Admit assumptions monotonically. An assumption containing a checked
-- operation may use only domain facts admitted earlier in canonical order;
-- mutually circular partial-operation justifications never bootstrap.
admitArithmeticAssumptions
  :: ArithmeticSemantics
  -> Set Int
  -> [AFact]
  -> Maybe [AFact]
admitArithmeticAssumptions semantics naturalVariables assumptions =
  close [] assumptions
  where
    close admitted [] = Just admitted
    close admitted pending =
      let (newlyAdmitted, blocked) =
            List.partition
              (arithmeticDomainHolds semantics naturalVariables admitted)
              pending
       in if null newlyAdmitted
            then Nothing
            else close (admitted ++ newlyAdmitted) blocked

guardArithmeticDomain
  :: ArithmeticSemantics
  -> Set Int
  -> [AFact]
  -> AFact
  -> Maybe ()
guardArithmeticDomain semantics naturalVariables assumptions fact
  | arithmeticDomainHolds semantics naturalVariables assumptions fact = Just ()
  | otherwise = Nothing

arithmeticDomainHolds
  :: ArithmeticSemantics
  -> Set Int
  -> [AFact]
  -> AFact
  -> Bool
arithmeticDomainHolds semantics naturalVariables assumptions (AFact _ lhs rhs) =
  case (expressionDomainObligations semantics lhs, expressionDomainObligations semantics rhs) of
    (Just lhsObligations, Just rhsObligations) ->
      all
        (isJustReplay . deriveArithmeticReplayUnchecked naturalVariables assumptions)
        (lhsObligations ++ rhsObligations)
    _ -> False
  where
    isJustReplay = maybe False (const True)

expressionDomainObligations
  :: ArithmeticSemantics
  -> AExpr
  -> Maybe [AFact]
expressionDomainObligations semantics = \case
  AConst value
    | semantics == ArithmeticNaturalSemantics && value < 0 -> Nothing
    | otherwise -> Just []
  AVar _ -> Just []
  AScale coefficient expression
    | semantics == ArithmeticNaturalSemantics && coefficient < 0 -> Nothing
    | otherwise -> expressionDomainObligations semantics expression
  AAdd lhs rhs -> binary lhs rhs
  ASub lhs rhs -> do
    nested <- binary lhs rhs
    pure $
      case semantics of
        ArithmeticNaturalSemantics -> AFact ACmpLe rhs lhs : nested
        ArithmeticIntegerSemantics -> nested
  AMul lhs rhs -> binary lhs rhs
  ADiv lhs rhs -> checkedDivisor lhs rhs
  AMod lhs rhs -> checkedDivisor lhs rhs
  ANeg expression
    | semantics == ArithmeticNaturalSemantics -> Nothing
    | otherwise -> expressionDomainObligations semantics expression
  AMax lhs rhs -> binary lhs rhs
  AMin lhs rhs -> binary lhs rhs
  AIf condition thenExpression elseExpression -> do
    conditionObligations <- formulaDomainObligations semantics condition
    branchObligations <- binary thenExpression elseExpression
    pure (conditionObligations ++ branchObligations)
  where
    binary lhs rhs =
      (++)
        <$> expressionDomainObligations semantics lhs
        <*> expressionDomainObligations semantics rhs
    checkedDivisor lhs rhs = do
      nested <- binary lhs rhs
      pure (AFact ACmpNe rhs (AConst 0) : nested)

formulaDomainObligations
  :: ArithmeticSemantics
  -> AFormula
  -> Maybe [AFact]
formulaDomainObligations semantics = \case
  ATruth _ -> Just []
  AAtom (AFact _ lhs rhs) ->
    (++)
      <$> expressionDomainObligations semantics lhs
      <*> expressionDomainObligations semantics rhs
  AAnd lhs rhs -> binary lhs rhs
  AOr lhs rhs -> binary lhs rhs
  ANot formula -> formulaDomainObligations semantics formula
  where
    binary lhs rhs =
      (++)
        <$> formulaDomainObligations semantics lhs
        <*> formulaDomainObligations semantics rhs

canonicalPolynomial :: Poly -> [([(Int, Int)], Integer)]
canonicalPolynomial (Poly terms) =
  [ (Map.toAscList variables, coefficient)
  | (Monomial variables, coefficient) <- Map.toAscList terms
  ]

simplifyA :: Set Int -> [AFact] -> AExpr -> AExpr
simplifyA naturalVariables assumptions = go
  where
    go = \case
      AScale k a -> case go a of
        AConst n -> AConst (k * n)
        a'
          | k == 0 -> AConst 0
          | k == 1 -> a'
          | k == -1 -> ANeg a'
          | otherwise -> AScale k a'
      AAdd a b -> foldConst AAdd (+) (go a) (go b)
      ASub a b -> foldConst ASub (-) (go a) (go b)
      AMul a b -> simplifyMul (go a) (go b)
      ADiv a b -> simplifyDiv (go a) (go b)
      AMod a b -> simplifyMod (go a) (go b)
      ANeg a -> case go a of
        AConst k -> AConst (negate k)
        a' -> ANeg a'
      AMax a b -> simplifyMax (go a) (go b)
      AMin a b -> simplifyMin (go a) (go b)
      AIf condition thenExpression elseExpression ->
        let thenExpression' = go thenExpression
            elseExpression' = go elseExpression
         in if thenExpression' == elseExpression'
              then thenExpression'
              else AIf condition thenExpression' elseExpression'
      other -> other

    simplifyMul a b = case (a, b) of
      (AConst x, AConst y) -> AConst (x * y)
      (AConst 0, _) -> AConst 0
      (_, AConst 0) -> AConst 0
      (AConst 1, x) -> x
      (x, AConst 1) -> x
      (AConst (-1), x) -> ANeg x
      (x, AConst (-1)) -> ANeg x
      (AConst k, x) -> AScale k x
      (x, AConst k) -> AScale k x
      _ -> AMul a b

    simplifyDiv a b = case (a, b) of
      (AConst x, AConst y) | y /= 0 -> AConst (x `quot` y)
      (x, AConst 1) -> x
      (x, AConst divisor)
        | divisor /= 0
        , Just linear <- linOf x
        , Just quotient <- divideLinearExact divisor linear ->
            linearExpression quotient
      _ -> ADiv a b

    simplifyMod a b = case (a, b) of
      (AConst x, AConst y) | y > 0 -> AConst (x `mod` y)
      (_, AConst 1) -> AConst 0
      (x, AConst modulus)
        | modulus > 1
        , Just linear <- linOf x ->
            case knownLinearResidue modulus linear assumptions of
              Just residue -> AConst residue
              Nothing ->
                let reduced = reduceLinearModulo modulus linear
                 in if Map.null (linearCoefficients reduced)
                      then AConst (linearConstant reduced)
                      else AMod (linearExpression reduced) (AConst modulus)
      _ -> AMod a b

    simplifyMax a b = case (a, b) of
      (x, y) | x == y -> x
      (AConst x, AConst y) -> AConst (max x y)
      (AConst 0, x)
        | Just lower <- lowerBoundRaw naturalVariables assumptions x
        , lower >= 0 -> x
        | Just upper <- upperBoundRaw naturalVariables assumptions x
        , upper <= 0 -> AConst 0
      (x, AConst 0)
        | Just lower <- lowerBoundRaw naturalVariables assumptions x
        , lower >= 0 -> x
        | Just upper <- upperBoundRaw naturalVariables assumptions x
        , upper <= 0 -> AConst 0
      _ -> AMax a b

    simplifyMin a b = case (a, b) of
      (x, y) | x == y -> x
      (AConst x, AConst y) -> AConst (min x y)
      _ -> AMin a b

    foldConst constructor operation a b = case (a, b) of
      (AConst x, AConst y) -> AConst (operation x y)
      _ -> constructor a b

linearConstant :: ALin -> Integer
linearConstant (ALin constant _) = constant

linearCoefficients :: ALin -> Map Int Integer
linearCoefficients (ALin _ coefficients) = coefficients

linearExpression :: ALin -> AExpr
linearExpression (ALin constant coefficients) =
  List.foldl'
    AAdd
    (AConst constant)
    [ if coefficient == 1
        then AVar variable
        else AScale coefficient (AVar variable)
    | (variable, coefficient) <- Map.toAscList coefficients
    , coefficient /= 0
    ]

divideLinearExact :: Integer -> ALin -> Maybe ALin
divideLinearExact divisor (ALin constant coefficients)
  | divisor == 0 = Nothing
  | constant `rem` divisor /= 0 = Nothing
  | any ((/= 0) . (`rem` divisor)) (Map.elems coefficients) = Nothing
  | otherwise =
      Just
        ( ALin
            (constant `quot` divisor)
            (Map.map (`quot` divisor) coefficients)
        )

reduceLinearModulo :: Integer -> ALin -> ALin
reduceLinearModulo modulus (ALin constant coefficients) =
  ALin
    (constant `mod` modulus)
    (Map.filter (/= 0) (Map.map (`mod` modulus) coefficients))

-- | Resolve one affine residue from an explicitly recorded congruence.  Both
-- sides are reduced modulo the same positive literal; no division, inverse, or
-- source spelling is guessed.  This is enough to transport congruence through
-- affine shifts while remaining a deterministic, replayable kernel rule.
knownLinearResidue :: Integer -> ALin -> [AFact] -> Maybe Integer
knownLinearResidue modulus target assumptions =
  List.find (const True) (catMaybes (map residue assumptions))
  where
    targetReduced = reduceLinearModulo modulus target
    residue = \case
      AFact ACmpEq lhs rhs ->
        fromSides lhs rhs <|> fromSides rhs lhs
      _ -> Nothing
    fromSides modular constantSide = do
      (base, recordedModulus) <- moduloExpression modular
      guardSameModulus recordedModulus
      recordedResidue <- constantExpression constantSide
      baseLinear <- linOf base
      let baseReduced = reduceLinearModulo modulus baseLinear
      if linearCoefficients baseReduced == linearCoefficients targetReduced
        then
          Just
            ( ( recordedResidue
                  + linearConstant targetReduced
                  - linearConstant baseReduced
              )
                `mod` modulus
            )
        else Nothing
    moduloExpression = \case
      AMod base (AConst value) -> Just (base, value)
      _ -> Nothing
    constantExpression = \case
      AConst value -> Just (value `mod` modulus)
      _ -> Nothing
    guardSameModulus value
      | value == modulus = Just ()
      | otherwise = Nothing

lowerBoundExpr :: Set Int -> [AFact] -> AExpr -> Maybe Integer
lowerBoundExpr naturalVariables assumptions expression0 =
  case lowerBoundSpecial naturalVariables assumptions expression of
    Just lower -> Just lower
    Nothing -> case linOf expression >>= lowerBoundLin naturalVariables assumptions of
      Just lower -> Just lower
      Nothing -> case polyOf expression >>= lowerBoundPoly naturalVariables assumptions of
        Just lower -> Just lower
        Nothing -> lowerBound naturalVariables assumptions expression
  where
    expression = simplifyA naturalVariables assumptions expression0

lowerBoundSpecial :: Set Int -> [AFact] -> AExpr -> Maybe Integer
lowerBoundSpecial naturalVariables assumptions = \case
  -- Order-lattice case analysis, replayed from the same authenticated
  -- comparison facts as source-level @if@.  These identities are inequalities,
  -- not conversion rules: proving an upper bound for @max@ (or a lower bound
  -- for @min@) requires both branches, while the dual direction may use
  -- either branch.
  ASub upper (AMax lhs rhs) -> do
    lhsBound <-
      lowerBoundExpr naturalVariables assumptions (ASub upper lhs)
    rhsBound <-
      lowerBoundExpr naturalVariables assumptions (ASub upper rhs)
    pure (min lhsBound rhsBound)
  ASub upper (AMin lhs rhs) ->
    maximumMaybe
      [ lowerBoundExpr naturalVariables assumptions (ASub upper lhs)
      , lowerBoundExpr naturalVariables assumptions (ASub upper rhs)
      ]
  ASub (AMax lhs rhs) lower ->
    maximumMaybe
      [ lowerBoundExpr naturalVariables assumptions (ASub lhs lower)
      , lowerBoundExpr naturalVariables assumptions (ASub rhs lower)
      ]
  ASub (AMin lhs rhs) lower -> do
    lhsBound <-
      lowerBoundExpr naturalVariables assumptions (ASub lhs lower)
    rhsBound <-
      lowerBoundExpr naturalVariables assumptions (ASub rhs lower)
    pure (min lhsBound rhsBound)
  ASub x (ADiv y (AConst k))
    | k > 1
    , x == y
    , Just lower <- lowerBoundRaw naturalVariables assumptions x
    , lower >= 1 -> Just 1
  ASub x (ADiv y (AConst k))
    | k > 1
    , Just yLower <- lowerBoundRaw naturalVariables assumptions y
    , yLower >= 0
    , lowerBoundExpr naturalVariables assumptions (ASub (AMul (AConst k) x) y) >= Just 1 -> Just 1
  _ -> Nothing
  where
    maximumMaybe candidates =
      case catMaybes candidates of
        [] -> Nothing
        values -> Just (maximum values)

lowerBoundLin :: Set Int -> [AFact] -> ALin -> Maybe Integer
lowerBoundLin naturalVariables assumptions linear@(ALin constant coefficients) =
  bestMaybe $
    foldM addCoefficient constant (Map.toList coefficients)
      : map (factLowerBound linear) assumptions
  where
    addCoefficient accumulator (variable, coefficient)
      | coefficient == 0 = Just accumulator
      | coefficient > 0 =
          (+ accumulator) . (* coefficient)
            <$> lowerOf (varBounds naturalVariables assumptions variable)
      | otherwise =
          (+ accumulator) . (* coefficient)
            <$> upperOf (varBounds naturalVariables assumptions variable)

    bestMaybe candidates = case catMaybes candidates of
      [] -> Nothing
      values -> Just (maximum values)

    factLowerBound query fact =
      case fact of
        AFact ACmpLt a b -> affineDiffLower 1 query a b
        AFact ACmpLe a b -> affineDiffLower 0 query a b
        AFact ACmpEq a b ->
          affineDiffLower 0 query a b <|> affineDiffLower 0 query b a
        AFact ACmpNe _ _ -> Nothing

    affineDiffLower base query smaller larger = do
      difference <- linOf (ASub larger smaller)
      queryAsDiffPlusConstant base query difference

    queryAsDiffPlusConstant base (ALin queryConstant queryMap) (ALin differenceConstant differenceMap)
      | queryMap == differenceMap =
          Just (base + queryConstant - differenceConstant)
      | otherwise = Nothing

lowerBound :: Set Int -> [AFact] -> AExpr -> Maybe Integer
lowerBound naturalVariables assumptions =
  lowerOf . boundsA naturalVariables assumptions

lowerBoundRaw :: Set Int -> [AFact] -> AExpr -> Maybe Integer
lowerBoundRaw naturalVariables assumptions =
  lowerOf . boundsRaw naturalVariables assumptions

upperBoundRaw :: Set Int -> [AFact] -> AExpr -> Maybe Integer
upperBoundRaw naturalVariables assumptions =
  upperOf . boundsRaw naturalVariables assumptions

boundsA :: Set Int -> [AFact] -> AExpr -> ABounds
boundsA naturalVariables assumptions =
  boundsRaw naturalVariables assumptions
    . simplifyA naturalVariables assumptions

boundsRaw :: Set Int -> [AFact] -> AExpr -> ABounds
boundsRaw naturalVariables assumptions expression = case expression of
  AConst k -> ABounds (Just k) (Just k)
  AVar variable -> varBounds naturalVariables assumptions variable
  AScale k a -> scaleBounds k (boundsRaw naturalVariables assumptions a)
  AAdd a b ->
    addBounds
      (boundsRaw naturalVariables assumptions a)
      (boundsRaw naturalVariables assumptions b)
  ASub a b ->
    subBounds
      (boundsRaw naturalVariables assumptions a)
      (boundsRaw naturalVariables assumptions b)
  AMul a b ->
    mulBounds
      (boundsRaw naturalVariables assumptions a)
      (boundsRaw naturalVariables assumptions b)
  ADiv a (AConst k)
    | k > 0 -> divByPositiveConstBounds k (boundsRaw naturalVariables assumptions a)
    | k < 0 -> divByNegativeConstBounds k (boundsRaw naturalVariables assumptions a)
  ADiv {} -> ABounds Nothing Nothing
  AMod {} -> ABounds Nothing Nothing
  ANeg a -> negBounds (boundsRaw naturalVariables assumptions a)
  AMax a b ->
    maxBounds
      (boundsRaw naturalVariables assumptions a)
      (boundsRaw naturalVariables assumptions b)
  AMin a b ->
    minBounds
      (boundsRaw naturalVariables assumptions a)
      (boundsRaw naturalVariables assumptions b)
  AIf _ thenExpression elseExpression ->
    branchBounds
      (boundsRaw naturalVariables assumptions thenExpression)
      (boundsRaw naturalVariables assumptions elseExpression)

varBounds :: Set Int -> [AFact] -> Int -> ABounds
varBounds naturalVariables assumptions variable =
  List.foldl' addFact initial assumptions
  where
    initial =
      ABounds
        (if Set.member variable naturalVariables then Just 0 else Nothing)
        Nothing
    addFact bounds = \case
      AFact ACmpLe (AVar x) (AConst c)
        | x == variable -> tightenUpper c bounds
      AFact ACmpLe (AConst c) (AVar x)
        | x == variable -> tightenLower c bounds
      AFact ACmpLt (AVar x) (AConst c)
        | x == variable -> tightenUpper (c - 1) bounds
      AFact ACmpLt (AConst c) (AVar x)
        | x == variable -> tightenLower (c + 1) bounds
      AFact ACmpEq (AVar x) (AConst c)
        | x == variable -> tightenUpper c (tightenLower c bounds)
      AFact ACmpEq (AConst c) (AVar x)
        | x == variable -> tightenUpper c (tightenLower c bounds)
      AFact ACmpNe (AVar x) (AConst 0)
        | x == variable
        , x `Set.member` naturalVariables -> tightenLower 1 bounds
      AFact ACmpNe (AConst 0) (AVar x)
        | x == variable
        , x `Set.member` naturalVariables -> tightenLower 1 bounds
      _ -> bounds

addBounds, subBounds :: ABounds -> ABounds -> ABounds
addBounds (ABounds lower1 upper1) (ABounds lower2 upper2) =
  ABounds ((+) <$> lower1 <*> lower2) ((+) <$> upper1 <*> upper2)
subBounds (ABounds lower1 upper1) (ABounds lower2 upper2) =
  ABounds ((-) <$> lower1 <*> upper2) ((-) <$> upper1 <*> lower2)

divByPositiveConstBounds :: Integer -> ABounds -> ABounds
divByPositiveConstBounds k (ABounds lower upper) =
  ABounds ((`quot` k) <$> lower) ((`quot` k) <$> upper)

divByNegativeConstBounds :: Integer -> ABounds -> ABounds
divByNegativeConstBounds k (ABounds lower upper) =
  ABounds ((`quot` k) <$> upper) ((`quot` k) <$> lower)

negBounds :: ABounds -> ABounds
negBounds (ABounds lower upper) = ABounds (negate <$> upper) (negate <$> lower)

scaleBounds :: Integer -> ABounds -> ABounds
scaleBounds k bounds@(ABounds lower upper)
  | k == 0 = ABounds (Just 0) (Just 0)
  | k > 0 = ABounds ((* k) <$> lower) ((* k) <$> upper)
  | otherwise = scaleBounds (negate k) (negBounds bounds)

mulBounds :: ABounds -> ABounds -> ABounds
mulBounds bounds1@(ABounds lower1 upper1) bounds2@(ABounds lower2 upper2)
  | Just values <- sequence [lower1, upper1, lower2, upper2] =
      let products = [x * y | x <- take 2 values, y <- drop 2 values]
       in ABounds (Just (minimum products)) (Just (maximum products))
  | Just lo1 <- lower1
  , Just lo2 <- lower2
  , lo1 >= 0
  , lo2 >= 0 = ABounds (Just (lo1 * lo2)) ((*) <$> upper1 <*> upper2)
  | otherwise = conservativeMul bounds1 bounds2
  where
    conservativeMul (ABounds (Just 0) (Just 0)) _ =
      ABounds (Just 0) (Just 0)
    conservativeMul _ (ABounds (Just 0) (Just 0)) =
      ABounds (Just 0) (Just 0)
    conservativeMul _ _ = ABounds Nothing Nothing

maxBounds, minBounds :: ABounds -> ABounds -> ABounds
maxBounds (ABounds lower1 upper1) (ABounds lower2 upper2) =
  ABounds (maxKnown lower1 lower2) (maxBoth upper1 upper2)
minBounds (ABounds lower1 upper1) (ABounds lower2 upper2) =
  ABounds (minBoth lower1 lower2) (minKnown upper1 upper2)

branchBounds :: ABounds -> ABounds -> ABounds
branchBounds (ABounds lower1 upper1) (ABounds lower2 upper2) =
  ABounds (minBoth lower1 lower2) (maxBoth upper1 upper2)

lowerOf, upperOf :: ABounds -> Maybe Integer
lowerOf (ABounds lower _) = lower
upperOf (ABounds _ upper) = upper

tightenLower :: Integer -> ABounds -> ABounds
tightenLower value (ABounds lower upper) =
  ABounds (maxKnown lower (Just value)) upper

tightenUpper :: Integer -> ABounds -> ABounds
tightenUpper value (ABounds lower upper) =
  ABounds lower (minKnown upper (Just value))

maxKnown, minKnown, maxBoth, minBoth :: Maybe Integer -> Maybe Integer -> Maybe Integer
maxKnown (Just a) (Just b) = Just (max a b)
maxKnown a Nothing = a
maxKnown Nothing b = b

minKnown (Just a) (Just b) = Just (min a b)
minKnown a Nothing = a
minKnown Nothing b = b

maxBoth (Just a) (Just b) = Just (max a b)
maxBoth _ _ = Nothing

minBoth (Just a) (Just b) = Just (min a b)
minBoth _ _ = Nothing

linOf :: AExpr -> Maybe ALin
linOf = \case
  AConst k -> Just (ALin k Map.empty)
  AVar variable -> Just (ALin 0 (Map.singleton variable 1))
  AScale k a -> scaleLin k <$> linOf a
  AAdd a b -> addLin <$> linOf a <*> linOf b
  ASub a b -> subLin <$> linOf a <*> linOf b
  AMul (AConst k) a -> scaleLin k <$> linOf a
  AMul a (AConst k) -> scaleLin k <$> linOf a
  ANeg a -> scaleLin (-1) <$> linOf a
  AIf {} -> Nothing
  _ -> Nothing

addLin, subLin :: ALin -> ALin -> ALin
addLin (ALin constant1 map1) (ALin constant2 map2) =
  ALin
    (constant1 + constant2)
    (Map.filter (/= 0) (Map.unionWith (+) map1 map2))
subLin x y = addLin x (scaleLin (-1) y)

scaleLin :: Integer -> ALin -> ALin
scaleLin k (ALin constant coefficients) =
  ALin
    (k * constant)
    (Map.filter (/= 0) (Map.map (k *) coefficients))

polyOf :: AExpr -> Maybe Poly
polyOf = \case
  AConst k -> Just (polyConst k)
  AVar variable -> Just (polyVar variable)
  AScale k a -> polyScale k <$> polyOf a
  AAdd a b -> polyAdd <$> polyOf a <*> polyOf b
  ASub a b -> polySub <$> polyOf a <*> polyOf b
  AMul a b -> polyMul <$> polyOf a <*> polyOf b
  ANeg a -> polyScale (-1) <$> polyOf a
  AMax {} -> Nothing
  AMin {} -> Nothing
  AIf {} -> Nothing
  ADiv {} -> Nothing
  AMod {} -> Nothing

splitFirstConditionalFact :: AFact -> Maybe (AFormula, AFact, AFact)
splitFirstConditionalFact (AFact comparison lhs rhs) =
  case splitFirstConditionalExpression lhs of
    Just (condition, thenExpression, elseExpression) ->
      Just
        ( condition
        , AFact comparison thenExpression rhs
        , AFact comparison elseExpression rhs
        )
    Nothing -> do
      (condition, thenExpression, elseExpression) <-
        splitFirstConditionalExpression rhs
      pure
        ( condition
        , AFact comparison lhs thenExpression
        , AFact comparison lhs elseExpression
        )

splitFirstConditionalExpression
  :: AExpr
  -> Maybe (AFormula, AExpr, AExpr)
splitFirstConditionalExpression = \case
  AIf condition thenExpression elseExpression ->
    Just (condition, thenExpression, elseExpression)
  AScale coefficient expression ->
    descend (AScale coefficient) expression
  AAdd lhs rhs -> binary AAdd lhs rhs
  ASub lhs rhs -> binary ASub lhs rhs
  AMul lhs rhs -> binary AMul lhs rhs
  ADiv lhs rhs -> binary ADiv lhs rhs
  AMod lhs rhs -> binary AMod lhs rhs
  ANeg expression -> descend ANeg expression
  AMax lhs rhs -> binary AMax lhs rhs
  AMin lhs rhs -> binary AMin lhs rhs
  AConst {} -> Nothing
  AVar {} -> Nothing
  where
    descend constructor expression = do
      (condition, thenExpression, elseExpression) <-
        splitFirstConditionalExpression expression
      pure
        ( condition
        , constructor thenExpression
        , constructor elseExpression
        )

    binary constructor lhs rhs =
      case splitFirstConditionalExpression lhs of
        Just (condition, thenExpression, elseExpression) ->
          Just
            ( condition
            , constructor thenExpression rhs
            , constructor elseExpression rhs
            )
        Nothing -> do
          (condition, thenExpression, elseExpression) <-
            splitFirstConditionalExpression rhs
          pure
            ( condition
            , constructor lhs thenExpression
            , constructor lhs elseExpression
            )

-- | Restrict an arithmetic context to one branch of a case split. Goals and
-- assumptions must be specialized together: retaining an assumption such as
-- @lo <= if p then x else y@ after entering the @p@ branch discards the
-- usable fact @lo <= x@ and makes nested min/max/clamp proofs incomplete.
--
-- Every occurrence of an identical condition selects the same branch because
-- arithmetic conditions are pure. Other conditions remain available for
-- deterministic splitting later.
specializeConditionalFact :: AFormula -> Bool -> AFact -> AFact
specializeConditionalFact condition branch (AFact comparison lhs rhs) =
  AFact
    comparison
    (specializeConditionalExpression condition branch lhs)
    (specializeConditionalExpression condition branch rhs)

specializeConditionalExpression :: AFormula -> Bool -> AExpr -> AExpr
specializeConditionalExpression condition branch = expression
  where
    expression = \case
      AIf candidate thenExpression elseExpression
        | candidate == condition ->
            expression
              (if branch then thenExpression else elseExpression)
        | otherwise ->
            AIf
              (formula candidate)
              (expression thenExpression)
              (expression elseExpression)
      AScale coefficient value -> AScale coefficient (expression value)
      AAdd lhs rhs -> AAdd (expression lhs) (expression rhs)
      ASub lhs rhs -> ASub (expression lhs) (expression rhs)
      AMul lhs rhs -> AMul (expression lhs) (expression rhs)
      ADiv lhs rhs -> ADiv (expression lhs) (expression rhs)
      AMod lhs rhs -> AMod (expression lhs) (expression rhs)
      ANeg value -> ANeg (expression value)
      AMax lhs rhs -> AMax (expression lhs) (expression rhs)
      AMin lhs rhs -> AMin (expression lhs) (expression rhs)
      value -> value

    formula = \case
      ATruth truth -> ATruth truth
      AAtom fact -> AAtom (specializeConditionalFact condition branch fact)
      AAnd lhs rhs -> AAnd (formula lhs) (formula rhs)
      AOr lhs rhs -> AOr (formula lhs) (formula rhs)
      ANot value -> ANot (formula value)

polyConst :: Integer -> Poly
polyConst 0 = Poly Map.empty
polyConst k = Poly (Map.singleton (Monomial Map.empty) k)

polyVar :: Int -> Poly
polyVar variable =
  Poly (Map.singleton (Monomial (Map.singleton variable 1)) 1)

polyAdd, polySub, polyMul :: Poly -> Poly -> Poly
polyAdd (Poly a) (Poly b) =
  normalizePoly (Poly (Map.unionWith (+) a b))
polySub polynomial other = polyAdd polynomial (polyScale (-1) other)
polyMul (Poly a) (Poly b) =
  normalizePoly $
    Poly $
      Map.fromListWith (+)
        [ (mulMonomial monomialA monomialB, coefficientA * coefficientB)
        | (monomialA, coefficientA) <- Map.toList a
        , (monomialB, coefficientB) <- Map.toList b
        ]

polyScale :: Integer -> Poly -> Poly
polyScale k (Poly polynomial)
  | k == 0 = Poly Map.empty
  | otherwise = normalizePoly (Poly (Map.map (k *) polynomial))

normalizePoly :: Poly -> Poly
normalizePoly (Poly polynomial) =
  Poly (Map.filter (/= 0) polynomial)

polyIsZero :: Poly -> Bool
polyIsZero (Poly polynomial) = Map.null polynomial

mulMonomial :: Monomial -> Monomial -> Monomial
mulMonomial (Monomial a) (Monomial b) =
  Monomial (Map.filter (> 0) (Map.unionWith (+) a b))

lowerBoundPoly :: Set Int -> [AFact] -> Poly -> Maybe Integer
lowerBoundPoly naturalVariables assumptions (Poly polynomial) =
  foldM addTerm 0 (Map.toList polynomial)
  where
    addTerm accumulator (monomial, coefficient)
      | coefficient == 0 = Just accumulator
      | coefficient > 0 = do
          lower <- lowerOf (boundsMonomial naturalVariables assumptions monomial)
          pure (accumulator + coefficient * lower)
      | otherwise = do
          upper <- upperOf (boundsMonomial naturalVariables assumptions monomial)
          pure (accumulator + coefficient * upper)

boundsMonomial :: Set Int -> [AFact] -> Monomial -> ABounds
boundsMonomial naturalVariables assumptions (Monomial powers) =
  List.foldl' mulBounds (ABounds (Just 1) (Just 1))
    [ powBounds power (varBounds naturalVariables assumptions variable)
    | (variable, power) <- Map.toList powers
    ]

powBounds :: Int -> ABounds -> ABounds
powBounds power bounds
  | power <= 0 = ABounds (Just 1) (Just 1)
  | power == 1 = bounds
powBounds power (ABounds (Just lower) (Just upper))
  | lower >= 0 =
      ABounds (Just (lower ^ power)) (Just (upper ^ power))
  | upper <= 0 =
      let lo =
            if even power
              then min (lower ^ power) (upper ^ power)
              else lower ^ power
          hi =
            if even power
              then max (lower ^ power) (upper ^ power)
              else upper ^ power
       in ABounds (Just lo) (Just hi)
  | even power =
      ABounds
        (Just 0)
        (Just (max (abs lower) (abs upper) ^ power))
  | otherwise =
      ABounds (Just (lower ^ power)) (Just (upper ^ power))
powBounds power (ABounds (Just lower) Nothing)
  | lower >= 0 = ABounds (Just (lower ^ power)) Nothing
powBounds power (ABounds Nothing (Just upper))
  | upper <= 0 && odd power =
      ABounds Nothing (Just (upper ^ power))
  | upper <= 0 && even power =
      ABounds (Just 0) Nothing
powBounds _ _ = ABounds Nothing Nothing
