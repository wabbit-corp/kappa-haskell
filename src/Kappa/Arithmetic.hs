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
  , ABounds (..)
  , ArithmeticNormalForm (..)
  , ArithmeticProofRule (..)
  , ArithmeticReplay (..)
  , negateFact
  , proveFactByBounds
  , deriveArithmeticReplay
  , verifyArithmeticReplay
  , reindexArithmeticFact
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
  deriving stock (Eq, Ord, Show)

data ACmp = ACmpLt | ACmpLe | ACmpEq
  deriving stock (Eq, Ord, Show)

data AFact = AFact !ACmp !AExpr !AExpr
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
  deriving stock (Eq, Ord, Show)

data ArithmeticProofRule
  = ProvePolynomialEquality
  | ProveLinearEquality
  | ProveStrictLowerBound
  | ProveNonStrictLowerBound
  deriving stock (Eq, Ord, Show)

data ArithmeticReplay = ArithmeticReplay
  { arGoal :: !AFact
  , arRule :: !ArithmeticProofRule
  , arNormalForm :: !ArithmeticNormalForm
  }
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
    binary constructor lhs' rhs' =
      constructor
        <$> reindexExpression lhs'
        <*> reindexExpression rhs'

negateFact :: AFact -> Maybe AFact
negateFact = \case
  AFact ACmpLt a b -> Just (AFact ACmpLe b a)
  AFact ACmpLe a b -> Just (AFact ACmpLt b a)
  AFact ACmpEq _ _ -> Nothing

-- | Produce the unique replay descriptor for a fact in the supported
-- fragment. 'Nothing' means that the kernel cannot prove the fact.
deriveArithmeticReplay :: Set Int -> [AFact] -> AFact -> Maybe ArithmeticReplay
deriveArithmeticReplay naturalVariables assumptions goal =
  case goal of
    AFact ACmpEq lhs rhs ->
      let difference = simplifyA naturalVariables assumptions (ASub lhs rhs)
       in case polyOf difference of
            Just polynomial
              | polyIsZero polynomial ->
                  Just
                    ( ArithmeticReplay
                        goal
                        ProvePolynomialEquality
                        (NormalPolynomial (canonicalPolynomial polynomial))
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

verifyArithmeticReplay :: Set Int -> [AFact] -> ArithmeticReplay -> Bool
verifyArithmeticReplay naturalVariables assumptions replay =
  deriveArithmeticReplay naturalVariables assumptions (arGoal replay)
    == Just replay

proveFactByBounds :: Set Int -> [AFact] -> AFact -> Bool
proveFactByBounds naturalVariables assumptions =
  maybe False (const True)
    . deriveArithmeticReplay naturalVariables assumptions

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
      _ -> ADiv a b

    simplifyMod a b = case (a, b) of
      (AConst x, AConst y) | y /= 0 -> AConst (x `rem` y)
      (_, AConst 1) -> AConst 0
      _ -> AMod a b

    simplifyMax a b = case (a, b) of
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
      (AConst x, AConst y) -> AConst (min x y)
      _ -> AMin a b

    foldConst constructor operation a b = case (a, b) of
      (AConst x, AConst y) -> AConst (operation x y)
      _ -> constructor a b

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
  ADiv {} -> Nothing
  AMod {} -> Nothing

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
