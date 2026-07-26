-- | Termination/totality support shared by the checker.
--
-- Kappa wants recursive definitions to be /total/ (to always halt) so that
-- types-as-propositions stay sound. A definition passes when every recursive
-- call makes some /measure/ strictly decrease on a well-founded ordering.
-- This module is the pure machinery that decides that:
--
--   * dependency scanning, to find the mutually-recursive groups
--     ('expandedGlobalsOfTerm');
--   * measure handling: instantiation at a call site ('instantiateByLevelMaybe')
--     and decomposition of tuple\/lexicographic measures ('rankComponents'); and
--   * a small abstract-arithmetic prover (the 'AExpr' \/ 'AFact' \/ 'ABounds'
--     family) that decides goals like "this argument is smaller than that
--     one" from the integer facts in scope.
--
-- The monadic checker integration stays in "Kappa.Check" because it needs
-- diagnostics, global reducibility state, normalization caches, and
-- elaboration context.
module Kappa.Termination
  ( TerminationDecl (..)
  , TerminationResult (..)
  , AExpr (..)
  , ACmp (..)
  , AFact (..)
  , ABounds (..)
  , IntArithPrim (..)
  , IntCmpPrim (..)
  , globalsOfTerm
  , expandedGlobalsOfTerm
  , rankComponents
  , instantiateByLevelMaybe
  , maxFreeIndexTerm
  , simplifyDecisionTerm
  , negateFact
  , intArithPrim
  , intCmpPrim
  , trustedIntPrimModule
  , boolRel
  , boolNotArg
  , lastExplicitArg
  , arithOf
  , arithmeticMetaVariable
  , proveFactByBounds
  , lowerBoundExpr
  , lastMaybe
  , last2
  , nthMaybe
  , spineOfTerm
  ) where

import Control.Applicative ((<|>))
import Control.Monad (foldM)
import Data.List (sortOn)
import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, isNothing)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as T
import Text.Read (readMaybe)

import Kappa.Builtins
  ( prelFalse
  , prelNatAdd
  , prelNatMultiply
  , prelNatSucc
  , prelNatZero
  , prelNot
  , prelTrue
  , preludeModule
  )
import Kappa.Core
import Kappa.CoreOps
  ( globalsOfTerm
  , maxFreeIndexTerm
  , patBindersC
  , shiftTerm
  , spineOfTerm
  )
import Kappa.Source (ModuleName, Span)
import Kappa.Syntax (Binder, Decreases)

-- | The source metadata needed for the whole-module termination pass.
-- Recursive SCCs cannot be checked soundly one declaration at a time:
-- a later definition may close a cycle through an earlier one.  Bodies are
-- therefore installed conservatively and this record lets the final SCC pass
-- decide which definitions may be conversion-reducible (§15.1/§15.11).
data TerminationDecl = TerminationDecl
  { tdName :: !GName
  , tdSigType :: !Value
  , tdBinders :: ![Binder]
  , tdDecreases :: !(Maybe Decreases)
  , tdCoreBody :: !Term
  , tdSpan :: !Span
  }

data TerminationResult
  = TerminationUnverified
  | TerminationTotalOnly
  | TerminationConversionSafe
  deriving stock (Eq, Show)

-- | Expand direct global references through known-reducible bodies.  The caller
-- supplies only reducibility and body data so this remains independent of the
-- checker state record.
expandedGlobalsOfTerm :: Map GName (Bool, Maybe Term) -> Term -> Set GName
expandedGlobalsOfTerm globals = go Set.empty
  where
    go seen tm =
      Set.unions [expand seen g | g <- Set.toList (globalsOfTerm tm)]

    expand seen g
      | Set.member g seen = Set.singleton g
      | otherwise =
          Set.insert g $
            case Map.lookup g globals of
              Just (True, Just body) -> go (Set.insert g seen) body
              _ -> Set.empty

rankComponents :: Term -> [Term]
rankComponents = \case
  CRecordV fs
    | Just components <- tupleComponents fs -> map snd components
  t -> [t]
  where
    tupleComponents fs = do
      indexed <- traverse tupleField fs
      let sorted = sortOn fst indexed
      if map fst sorted == [1 .. length sorted]
        then Just sorted
        else Nothing

    tupleField (nm, tm) = do
      raw <- T.stripPrefix "_" nm
      ix <- readMaybe (T.unpack raw)
      if ix >= (1 :: Int)
        then Just (ix, tm)
        else Nothing

instantiateByLevelMaybe :: Int -> Int -> Map Int Term -> Term -> Maybe Term
instantiateByLevelMaybe oldDepth _callDepth subst = go oldDepth
  where
    go curDepth = \case
      CVar i ->
        let lvl = curDepth - 1 - i
         in if lvl >= oldDepth
              then Just (CVar i)
              else case Map.lookup lvl subst of
                Just arg -> Just (shiftTerm (curDepth - oldDepth) 0 arg)
                Nothing -> Nothing
      CLocal i universes ->
        let lvl = curDepth - 1 - i
         in if lvl >= oldDepth
              then Just (CLocal i universes)
              else case Map.lookup lvl subst of
                Just arg -> Just (shiftTerm (curDepth - oldDepth) 0 arg)
                Nothing -> Nothing
      CGlobal x universes -> Just (CGlobal x universes)
      CLamM mode ic q n b -> CLamM mode ic q n <$> go (curDepth + 1) b
      CPiEvidenceM mode formation ic q brw n assumption origin a b ->
        CPiEvidenceM mode formation ic q brw n assumption origin <$> go curDepth a <*> go (curDepth + 1) b
      CApp ic f a -> CApp ic <$> go curDepth f <*> go curDepth a
      CSort u -> Just (CSort u)
      CLevel u -> Just (CLevel u)
      CUniverseLift from to evidence t ->
        CUniverseLift from to evidence <$> go curDepth t
      CSchemaLift family source target roles evidence certificate sourceArguments targetArguments t ->
        CSchemaLift family source target roles evidence certificate
          <$> traverse (go curDepth) sourceArguments
          <*> traverse (go curDepth) targetArguments
          <*> go curDepth t
      CLit l -> Just (CLit l)
      CCtorI cg universes ann arguments ->
        CCtorI cg universes <$> traverse (go curDepth) ann
          <*> traverse (\argument -> (\term -> argument {caTerm = term}) <$> go curDepth (caTerm argument)) arguments
      CMatch s ann alts -> CMatch <$> go curDepth s <*> traverse (go curDepth) ann <*> traverse goAlt alts
        where
          goAlt (CaseAlt pat gd b) =
            CaseAlt pat
              <$> traverse (go (curDepth + patBindersC pat)) gd
              <*> go (curDepth + patBindersC pat) b
      CRecordTQ fs -> CRecordTQ <$> traverse (traverse (go curDepth)) fs
      CRecordV fs -> CRecordV <$> traverseField curDepth fs
      CProjM mode e f -> CProjM mode <$> go curDepth e <*> pure f
      CProjAtM mode e f i -> CProjAtM mode <$> go curDepth e <*> pure f <*> pure i
      CVariantT ms -> CVariantT <$> traverse (go curDepth) ms
      CInject tag e -> CInject tag <$> go curDepth e
      CLetM mode q n a b c -> CLetM mode q n <$> go curDepth a <*> go curDepth b <*> go (curDepth + 1) c
      CLetRecM mode q n a b c -> CLetRecM mode q n <$> go curDepth a <*> go (curDepth + 1) b <*> go (curDepth + 1) c
      CLetPolyM mode q n telescope a b c ->
        CLetPolyM mode q n telescope <$> go curDepth a <*> go curDepth b <*> go (curDepth + 1) c
      CLetRecPolyM mode q n telescope a b c ->
        CLetRecPolyM mode q n telescope <$> go curDepth a <*> go (curDepth + 1) b <*> go (curDepth + 1) c
      CLetRecGroupM telescope definitions body -> do
        let groupDepth = curDepth + length definitions
        definitions' <- traverse
          (\definition ->
             (\ty rhs -> definition {clrdType = ty, clrdRhs = rhs})
               <$> go curDepth (clrdType definition)
               <*> go groupDepth (clrdRhs definition))
          definitions
        CLetRecGroupM telescope definitions' <$> go groupDepth body
      CMeta m -> Just (CMeta m)
      CDo {} -> Nothing
      CSealE ls e -> CSealE ls <$> go curDepth e
      CSigT ls e -> CSigT ls <$> go curDepth e
      CThunkE e -> CThunkE <$> go curDepth e
      CLazyE e -> CLazyE <$> go curDepth e
      CForceE e -> CForceE <$> go curDepth e
      CIf a b c -> CIf <$> go curDepth a <*> go curDepth b <*> go curDepth c
      CQuote qs slots -> CQuote qs <$> traverse (go curDepth) slots

    traverseField curDepth fs = traverse (\(n, x) -> (,) n <$> go curDepth x) fs

simplifyDecisionTerm :: Term -> Term
simplifyDecisionTerm = go
  where
    go = \case
      CIf c t e ->
        let c' = go c
            t' = go t
            e' = go e
         in case (c', t', e') of
              (CCtor g _ [], _, _) | g == prelTrue -> t'
              (CCtor g _ [], _, _) | g == prelFalse -> e'
              (_, CCtor gt _ [], CCtor gf _ []) | gt == prelTrue, gf == prelFalse -> c'
              _ -> CIf c' t' e'
      CMatch (CIf c t e) ann alts | all ((== 0) . patBindersC . caPat) alts ->
        go (CIf c (CMatch t ann alts) (CMatch e ann alts))
      CMatch s ann alts ->
        let s' = go s
            alts' = [CaseAlt p (fmap go gd) (go b) | CaseAlt p gd b <- alts]
         in fromMaybe (CMatch s' ann alts') (reduceSimpleMatch s' alts')
      CApp ic f a -> CApp ic (go f) (go a)
      CUniverseLift from to evidence t -> CUniverseLift from to evidence (go t)
      CSchemaLift family source target roles evidence certificate sourceArguments targetArguments t ->
        CSchemaLift family source target roles evidence certificate
          (map go sourceArguments) (map go targetArguments) (go t)
      CLamM mode ic q n b -> CLamM mode ic q n (go b)
      CPiEvidenceM mode formation ic q brw n assumption origin a b ->
        CPiEvidenceM mode formation ic q brw n assumption origin (go a) (go b)
      CCtorI g universes ann arguments ->
        CCtorI g universes (fmap go ann)
          [argument {caTerm = go (caTerm argument)} | argument <- arguments]
      CRecordTQ fs -> CRecordTQ (map (fmap go) fs)
      CRecordV fs -> CRecordV [(n, go x) | (n, x) <- fs]
      CProjM mode e f -> CProjM mode (go e) f
      CProjAtM mode e f i -> CProjAtM mode (go e) f i
      CVariantT ms -> CVariantT (map go ms)
      CInject tag e -> CInject tag (go e)
      CLetM mode q n a b c -> CLetM mode q n (go a) (go b) (go c)
      CLetRecM mode q n a b c -> CLetRecM mode q n (go a) (go b) (go c)
      CLetPolyM mode q n telescope a b c -> CLetPolyM mode q n telescope (go a) (go b) (go c)
      CLetRecPolyM mode q n telescope a b c -> CLetRecPolyM mode q n telescope (go a) (go b) (go c)
      CLetRecGroupM telescope definitions body ->
        CLetRecGroupM telescope
          [definition {clrdType = go (clrdType definition), clrdRhs = go (clrdRhs definition)} | definition <- definitions]
          (go body)
      CThunkE e -> CThunkE (go e)
      CLazyE e -> CLazyE (go e)
      CForceE e -> CForceE (go e)
      CSealE ls e -> CSealE ls (go e)
      CSigT ls e -> CSigT ls (go e)
      CQuote qs slots -> CQuote qs (map go slots)
      other -> other

    reduceSimpleMatch s = goAlts
      where
        goAlts [] = Nothing
        goAlts (CaseAlt p gd b : rest) =
          case simplePatDecision p s of
            Just False -> goAlts rest
            Just True
              | isNothing gd
              , patBindersC p == 0 -> Just b
              | otherwise -> Nothing
            Nothing -> Nothing

    simplePatDecision p s = case (p, s) of
      (CPWild, _) -> Just True
      (CPVar _, _) -> Just True
      (CPLit l, CLit l') -> Just (l == l')
      (CPCtor g _ ps, CCtor g' _ as)
        | g /= g' -> Just False
        | length ps == length as -> allDecisions (zipWith simplePatDecision ps as)
        | otherwise -> Just False
      (CPInject tag p', CInject tag' x)
        | tag /= tag' -> Just False
        | otherwise -> simplePatDecision p' x
      (CPOr ps _, _) -> orDecisions (map (`simplePatDecision` s) ps)
      (CPAs _ p', _) -> simplePatDecision p' s
      _ -> Nothing

    allDecisions xs
      | any (== Just False) xs = Just False
      | all (== Just True) xs = Just True
      | otherwise = Nothing

    orDecisions xs
      | any (== Just True) xs = Just True
      | all (== Just False) xs = Just False
      | otherwise = Nothing

-- ── Abstract arithmetic (the measure prover) ──────────────────────────
--
-- To show a measure decreases, the checker reasons about integers
-- symbolically rather than running them. It extracts an 'AExpr' (an abstract
-- arithmetic expression) from a core term, gathers the 'AFact's known true
-- at the call site (mostly from enclosing @if@ guards, e.g. @n > 0@), and
-- proves the goal by bounding each side to an integer interval ('ABounds').
-- 'ALin' and 'Poly' are the linear- and polynomial-normal forms used to
-- compute those bounds.

-- | A symbolic integer expression lifted out of a core term by 'arithOf'.
data AExpr
  = AConst !Integer
  | AVar !Int -- ^ a rigid level, or a negative 'arithmeticMetaVariable'
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

-- | A comparison relation: strictly-less, less-or-equal, equal.
data ACmp = ACmpLt | ACmpLe | ACmpEq
  deriving stock (Eq, Ord, Show)

-- | A known or to-be-proved comparison fact @lhs `cmp` rhs@.
data AFact = AFact !ACmp !AExpr !AExpr
  deriving stock (Eq, Ord, Show)

-- | An inclusive integer interval @[lo, hi]@; 'Nothing' on a side means
-- unbounded there.
data ABounds = ABounds !(Maybe Integer) !(Maybe Integer)
  deriving stock (Eq, Show)

-- | A linear form: a constant plus a map from variable level to coefficient
-- (@c + Σ kᵢ·xᵢ@).
data ALin = ALin !Integer !(Map Int Integer)
  deriving stock (Eq, Show)

-- | A product of variables with exponents (level ↦ power); the building
-- block of 'Poly', used when reasoning isn't purely linear.
newtype Monomial = Monomial (Map Int Int)
  deriving stock (Eq, Ord, Show)

-- | A polynomial: a sum of monomials with integer coefficients.
newtype Poly = Poly (Map Monomial Integer)
  deriving stock (Eq, Show)

-- | Negate a fact (for the @else@ branch of a guard): @a < b@ becomes
-- @b <= a@, etc. Equality has no single-fact negation, so 'Nothing'.
negateFact :: AFact -> Maybe AFact
negateFact = \case
  AFact ACmpLt a b -> Just (AFact ACmpLe b a)
  AFact ACmpLe a b -> Just (AFact ACmpLt b a)
  AFact ACmpEq _ _ -> Nothing

data IntArithPrim
  = PrimAddInt
  | PrimSubInt
  | PrimMulInt
  | PrimDivInt
  | PrimModInt
  | PrimNegInt
  | PrimNatToInt
  | PrimNatOfInt
  | PrimIntToNat
  deriving stock (Eq, Show)

data IntCmpPrim = PrimLtInt | PrimLeInt | PrimEqInt
  deriving stock (Eq, Show)

intArithPrim :: GName -> Maybe IntArithPrim
intArithPrim (GName m p)
  | not (trustedIntPrimModule m) = Nothing
  | otherwise = case p of
      "addInt" -> Just PrimAddInt
      "subInt" -> Just PrimSubInt
      "mulInt" -> Just PrimMulInt
      "divInt" -> Just PrimDivInt
      "modInt" -> Just PrimModInt
      "negInt" -> Just PrimNegInt
      "natToInt" -> Just PrimNatToInt
      "natOfInt" -> Just PrimNatOfInt
      "intToNat" -> Just PrimIntToNat
      _ -> Nothing

intCmpPrim :: GName -> Maybe IntCmpPrim
intCmpPrim (GName m p)
  | not (trustedIntPrimModule m) = Nothing
  | otherwise = case p of
      "ltInt" -> Just PrimLtInt
      "leInt" -> Just PrimLeInt
      "eqInt" -> Just PrimEqInt
      _ -> Nothing

trustedIntPrimModule :: ModuleName -> Bool
trustedIntPrimModule m = m == primModule || m == preludeModule

-- | Read a comparison 'AFact' out of a /boolean/-valued core term @t0@ at
-- depth @d@ (e.g. recognize @ltInt x y@ as @x < y@), seeing through @not@
-- and boolean-encoded @if@. 'Nothing' if it isn't a recognized comparison.
boolRel :: Int -> Term -> Maybe AFact
boolRel d t0 = case simplifyDecisionTerm t0 of
  CIf c th el
    | isTrueTm th, isFalseTm el -> boolRel d c
    | isFalseTm th, isTrueTm el -> boolRel d c >>= negateFact
    | isTrueTm th -> do
        cFact <- boolRel d c
        elFact <- boolRel d el
        combineOr cFact elFact
  t -> case spineOfTerm t of
    (CGlob g, args)
      | g == prelNot
      , Just p <- lastExplicitArg args -> boolRel d p >>= negateFact
    (CGlob rg, args) -> do
      let ex = [a | (Expl, a) <- args]
      (a, b) <- last2 ex
      aa <- arithOf d a
      bb <- arithOf d b
      case intCmpPrim rg of
        Just PrimLtInt -> pure (AFact ACmpLt aa bb)
        Just PrimLeInt -> pure (AFact ACmpLe aa bb)
        Just PrimEqInt -> pure (AFact ACmpEq aa bb)
        Nothing -> Nothing
    _ -> Nothing
  where
    isTrueTm = \case CCtor g _ [] -> g == prelTrue; _ -> False
    isFalseTm = \case CCtor g _ [] -> g == prelFalse; _ -> False
    combineOr (AFact ACmpLt a b) (AFact ACmpEq a' b') | a == a' && b == b' = Just (AFact ACmpLe a b)
    combineOr (AFact ACmpEq a b) (AFact ACmpLt a' b') | a == a' && b == b' = Just (AFact ACmpLe a b)
    combineOr _ _ = Nothing

boolNotArg :: Term -> Maybe Term
boolNotArg t = case spineOfTerm t of
  (CGlob g, args)
    | g == prelNot -> lastExplicitArg args
  _ -> Nothing

lastExplicitArg :: [(Icit, Term)] -> Maybe Term
lastExplicitArg args = lastMaybe [a | (Expl, a) <- args]

-- | Lift an integer-valued core term @t0@ (at depth @d@) into a symbolic
-- 'AExpr', recognizing literals, variables, the trusted int primitives
-- (@addInt@, @subInt@, …), and @if@-as-@max@\/@min@. 'Nothing' if some part
-- isn't understood arithmetically. The @d - 1 - i@ turns the variable's de
-- Bruijn index into the level 'AVar' stores.
arithOf :: Int -> Term -> Maybe AExpr
arithOf d t0 = case simplifyDecisionTerm t0 of
  CLit (LitInt n) -> Just (AConst n)
  CCtorI g _ _ []
    | g == prelNatZero -> Just (AConst 0)
  CCtorI g _ _ [argument]
    | g == prelNatSucc ->
        AAdd (AConst 1) <$> arithOf d (caTerm argument)
  CVar i -> Just (AVar (d - 1 - i))
  CMeta meta -> Just (AVar (arithmeticMetaVariable meta))
  CIf c th el -> arithIf c th el
  t@CApp {} -> arithApp t
  _ -> Nothing
  where
    arithIf c th el = do
      fact <- boolRel d c
      aThen <- arithOf d th
      aElse <- arithOf d el
      case fact of
        AFact cmp x y | cmp == ACmpLe || cmp == ACmpLt ->
          if aThen == y && aElse == x
            then Just (AMax x y)
            else if aThen == x && aElse == y
              then Just (AMin x y)
              else Nothing
        _ -> Nothing

    arithApp t = case spineOfTerm t of
      (CGlob fg, args) -> do
        let ex = [a | (Expl, a) <- args]
            bin f = do
              (a, b) <- last2 ex
              f <$> arithOf d a <*> arithOf d b
            un f = do
              a <- lastMaybe ex
              f <$> arithOf d a
        if fg == prelNatAdd
          then bin AAdd
          else if fg == prelNatMultiply
            then bin AMul
            else case intArithPrim fg of
              Just PrimAddInt -> bin AAdd
              Just PrimSubInt -> bin ASub
              Just PrimMulInt -> bin AMul
              Just PrimDivInt -> bin ADiv
              Just PrimModInt -> bin AMod
              Just PrimNegInt -> un ANeg
              Just PrimNatToInt -> un id
              Just PrimNatOfInt -> un id
              Just PrimIntToNat -> un id
              Nothing -> Nothing
      _ -> Nothing

-- | Give an inference meta a stable arithmetic-variable identity disjoint
-- from every de Bruijn level.  Callers still decide whether the meta is known
-- to be Nat-typed before adding this identity to the non-negative variable
-- set; merely reifying a meta here grants it no arithmetic facts.
arithmeticMetaVariable :: MetaId -> Int
arithmeticMetaVariable meta = negate meta - 1

-- | Try to prove a goal 'AFact' from the facts in scope. @natLvls@ is the
-- set of variable /levels/ known to be naturals (so they're @>= 0@ for
-- free). The trick is to reduce every goal to a lower-bound question:
-- @a < b@ holds iff @b - a >= 1@, @a <= b@ iff @b - a >= 0@, and @a == b@
-- iff @a - b@ simplifies to zero. Conservative: 'False' means "couldn't
-- prove it," not "false."
proveFactByBounds :: Set Int -> [AFact] -> AFact -> Bool
proveFactByBounds natLvls facts = \case
  AFact ACmpLt a b -> lowerBoundExpr natLvls facts (ASub b a) >= Just 1
  AFact ACmpLe a b -> lowerBoundExpr natLvls facts (ASub b a) >= Just 0
  AFact ACmpEq a b -> isZeroArithmetic (simplifyA natLvls facts (ASub a b))

isZeroArithmetic :: AExpr -> Bool
isZeroArithmetic expr =
  case polyOf expr of
    Just p -> polyIsZero p
    Nothing -> case linOf expr of
      Just (ALin c coeffs) -> c == 0 && all (== 0) (Map.elems coeffs)
      Nothing -> False

simplifyA :: Set Int -> [AFact] -> AExpr -> AExpr
simplifyA natLvls facts = go
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
        | Just lb <- lowerBoundRaw natLvls facts x, lb >= 0 -> x
        | Just ub <- upperBoundRaw natLvls facts x, ub <= 0 -> AConst 0
      (x, AConst 0)
        | Just lb <- lowerBoundRaw natLvls facts x, lb >= 0 -> x
        | Just ub <- upperBoundRaw natLvls facts x, ub <= 0 -> AConst 0
      _ -> AMax a b

    simplifyMin a b = case (a, b) of
      (AConst x, AConst y) -> AConst (min x y)
      _ -> AMin a b

    foldConst ctor op a b = case (a, b) of
      (AConst x, AConst y) -> AConst (op x y)
      _ -> ctor a b

-- | Compute a lower bound (largest provable @>= n@) for @expr0@ given the
-- nat-typed levels and facts in scope. Tries special-case reasoning, then a
-- linear-form bound, then a polynomial bound. 'Nothing' = no bound found.
lowerBoundExpr :: Set Int -> [AFact] -> AExpr -> Maybe Integer
lowerBoundExpr natLvls facts expr0 =
  case lowerBoundSpecial natLvls facts expr of
    Just lb -> Just lb
    Nothing -> case linOf expr >>= lowerBoundLin natLvls facts of
      Just lb -> Just lb
      Nothing -> case polyOf expr >>= lowerBoundPoly natLvls facts of
        Just lb -> Just lb
        Nothing -> lowerBound natLvls facts expr
  where
    expr = simplifyA natLvls facts expr0

lowerBoundSpecial :: Set Int -> [AFact] -> AExpr -> Maybe Integer
lowerBoundSpecial natLvls facts = \case
  ASub x (ADiv y (AConst k))
    | k > 1
    , x == y
    , Just lb <- lowerBoundRaw natLvls facts x
    , lb >= 1 -> Just 1
  ASub x (ADiv y (AConst k))
    | k > 1
    , Just yLb <- lowerBoundRaw natLvls facts y
    , yLb >= 0
    , lowerBoundExpr natLvls facts (ASub (AMul (AConst k) x) y) >= Just 1 -> Just 1
  _ -> Nothing

lowerBoundLin :: Set Int -> [AFact] -> ALin -> Maybe Integer
lowerBoundLin natLvls facts lin@(ALin c coeffs) =
  bestMaybe $
    foldM addCoeff c (Map.toList coeffs)
      : map (factLowerBound lin) facts
  where
    addCoeff acc (v, k)
      | k == 0 = Just acc
      | k > 0 = (+ acc) . (* k) <$> lowerOf (varBounds natLvls facts v)
      | otherwise = (+ acc) . (* k) <$> upperOf (varBounds natLvls facts v)

    bestMaybe xs = case catMaybes xs of
      [] -> Nothing
      ys -> Just (maximum ys)

    factLowerBound query fact =
      case fact of
        AFact ACmpLt a b -> affineDiffLower 1 query a b
        AFact ACmpLe a b -> affineDiffLower 0 query a b
        AFact ACmpEq a b -> affineDiffLower 0 query a b <|> affineDiffLower 0 query b a

    affineDiffLower base query smaller larger = do
      diff <- linOf (ASub larger smaller)
      queryAsDiffPlusConst base query diff

    queryAsDiffPlusConst base (ALin qc qm) (ALin dc dm)
      | qm == dm = Just (base + qc - dc)
      | otherwise = Nothing

lowerBound :: Set Int -> [AFact] -> AExpr -> Maybe Integer
lowerBound natLvls facts = lowerOf . boundsA natLvls facts

lowerBoundRaw :: Set Int -> [AFact] -> AExpr -> Maybe Integer
lowerBoundRaw natLvls facts = lowerOf . boundsRaw natLvls facts

upperBoundRaw :: Set Int -> [AFact] -> AExpr -> Maybe Integer
upperBoundRaw natLvls facts = upperOf . boundsRaw natLvls facts

boundsA :: Set Int -> [AFact] -> AExpr -> ABounds
boundsA natLvls facts = boundsRaw natLvls facts . simplifyA natLvls facts

boundsRaw :: Set Int -> [AFact] -> AExpr -> ABounds
boundsRaw natLvls facts expr = case expr of
  AConst k -> ABounds (Just k) (Just k)
  AVar v -> varBounds natLvls facts v
  AScale k a -> scaleBounds k (boundsRaw natLvls facts a)
  AAdd a b -> addBounds (boundsRaw natLvls facts a) (boundsRaw natLvls facts b)
  ASub a b -> subBounds (boundsRaw natLvls facts a) (boundsRaw natLvls facts b)
  AMul a b -> mulBounds (boundsRaw natLvls facts a) (boundsRaw natLvls facts b)
  ADiv a (AConst k)
    | k > 0 -> divByPositiveConstBounds k (boundsRaw natLvls facts a)
    | k < 0 -> divByNegativeConstBounds k (boundsRaw natLvls facts a)
  ADiv {} -> ABounds Nothing Nothing
  AMod {} -> ABounds Nothing Nothing
  ANeg a -> negBounds (boundsRaw natLvls facts a)
  AMax a b -> maxBounds (boundsRaw natLvls facts a) (boundsRaw natLvls facts b)
  AMin a b -> minBounds (boundsRaw natLvls facts a) (boundsRaw natLvls facts b)

varBounds :: Set Int -> [AFact] -> Int -> ABounds
varBounds natLvls facts v =
  let start = ABounds (if Set.member v natLvls then Just 0 else Nothing) Nothing
   in List.foldl' addFact start facts
  where
    addFact b = \case
      AFact ACmpLe (AVar x) (AConst c) | x == v -> tightenUpper c b
      AFact ACmpLe (AConst c) (AVar x) | x == v -> tightenLower c b
      AFact ACmpLt (AVar x) (AConst c) | x == v -> tightenUpper (c - 1) b
      AFact ACmpLt (AConst c) (AVar x) | x == v -> tightenLower (c + 1) b
      AFact ACmpEq (AVar x) (AConst c) | x == v -> tightenUpper c (tightenLower c b)
      AFact ACmpEq (AConst c) (AVar x) | x == v -> tightenUpper c (tightenLower c b)
      _ -> b

addBounds, subBounds :: ABounds -> ABounds -> ABounds
addBounds (ABounds l1 u1) (ABounds l2 u2) = ABounds ((+) <$> l1 <*> l2) ((+) <$> u1 <*> u2)
subBounds (ABounds l1 u1) (ABounds l2 u2) = ABounds ((-) <$> l1 <*> u2) ((-) <$> u1 <*> l2)

divByPositiveConstBounds :: Integer -> ABounds -> ABounds
divByPositiveConstBounds k (ABounds l u) = ABounds ((`quot` k) <$> l) ((`quot` k) <$> u)

divByNegativeConstBounds :: Integer -> ABounds -> ABounds
divByNegativeConstBounds k (ABounds l u) = ABounds ((`quot` k) <$> u) ((`quot` k) <$> l)

negBounds :: ABounds -> ABounds
negBounds (ABounds l u) = ABounds (negate <$> u) (negate <$> l)

scaleBounds :: Integer -> ABounds -> ABounds
scaleBounds k b@(ABounds l u)
  | k == 0 = ABounds (Just 0) (Just 0)
  | k > 0 = ABounds ((* k) <$> l) ((* k) <$> u)
  | otherwise = scaleBounds (negate k) (negBounds b)

mulBounds :: ABounds -> ABounds -> ABounds
mulBounds b1@(ABounds l1 u1) b2@(ABounds l2 u2)
  | Just xs <- sequence [l1, u1, l2, u2] =
      let products = [x * y | x <- take 2 xs, y <- drop 2 xs]
       in ABounds (Just (minimum products)) (Just (maximum products))
  | Just lo1 <- l1
  , Just lo2 <- l2
  , lo1 >= 0
  , lo2 >= 0 = ABounds (Just (lo1 * lo2)) ((*) <$> u1 <*> u2)
  | otherwise = conservativeMul b1 b2
  where
    conservativeMul (ABounds (Just 0) (Just 0)) _ = ABounds (Just 0) (Just 0)
    conservativeMul _ (ABounds (Just 0) (Just 0)) = ABounds (Just 0) (Just 0)
    conservativeMul _ _ = ABounds Nothing Nothing

maxBounds, minBounds :: ABounds -> ABounds -> ABounds
maxBounds (ABounds l1 u1) (ABounds l2 u2) = ABounds (maxKnown l1 l2) (maxBoth u1 u2)
minBounds (ABounds l1 u1) (ABounds l2 u2) = ABounds (minBoth l1 l2) (minKnown u1 u2)

lowerOf, upperOf :: ABounds -> Maybe Integer
lowerOf (ABounds l _) = l
upperOf (ABounds _ u) = u

tightenLower :: Integer -> ABounds -> ABounds
tightenLower x (ABounds l u) = ABounds (maxKnown l (Just x)) u

tightenUpper :: Integer -> ABounds -> ABounds
tightenUpper x (ABounds l u) = ABounds l (minKnown u (Just x))

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
  AVar v -> Just (ALin 0 (Map.singleton v 1))
  AScale k a -> scaleLin k <$> linOf a
  AAdd a b -> addLin <$> linOf a <*> linOf b
  ASub a b -> subLin <$> linOf a <*> linOf b
  AMul (AConst k) a -> scaleLin k <$> linOf a
  AMul a (AConst k) -> scaleLin k <$> linOf a
  ANeg a -> scaleLin (-1) <$> linOf a
  _ -> Nothing

addLin, subLin :: ALin -> ALin -> ALin
addLin (ALin c1 m1) (ALin c2 m2) = ALin (c1 + c2) (Map.filter (/= 0) (Map.unionWith (+) m1 m2))
subLin x y = addLin x (scaleLin (-1) y)

scaleLin :: Integer -> ALin -> ALin
scaleLin k (ALin c m) = ALin (k * c) (Map.filter (/= 0) (Map.map (k *) m))

polyOf :: AExpr -> Maybe Poly
polyOf = \case
  AConst k -> Just (polyConst k)
  AVar v -> Just (polyVar v)
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
polyVar v = Poly (Map.singleton (Monomial (Map.singleton v 1)) 1)

polyAdd, polySub, polyMul :: Poly -> Poly -> Poly
polyAdd (Poly a) (Poly b) = normalizePoly (Poly (Map.unionWith (+) a b))
polySub p q = polyAdd p (polyScale (-1) q)
polyMul (Poly a) (Poly b) =
  normalizePoly $
    Poly $
      Map.fromListWith (+)
        [ (mulMonomial ma mb, ca * cb)
        | (ma, ca) <- Map.toList a
        , (mb, cb) <- Map.toList b
        ]

polyScale :: Integer -> Poly -> Poly
polyScale k (Poly p)
  | k == 0 = Poly Map.empty
  | otherwise = normalizePoly (Poly (Map.map (k *) p))

normalizePoly :: Poly -> Poly
normalizePoly (Poly p) = Poly (Map.filter (/= 0) p)

polyIsZero :: Poly -> Bool
polyIsZero (Poly p) = Map.null p

mulMonomial :: Monomial -> Monomial -> Monomial
mulMonomial (Monomial a) (Monomial b) = Monomial (Map.filter (> 0) (Map.unionWith (+) a b))

-- | A lower bound for a whole polynomial: to minimize the sum, take the
-- /lower/ bound of each positive-coefficient term and the /upper/ bound of
-- each negative-coefficient term. 'Nothing' if any needed bound is unknown.
lowerBoundPoly :: Set Int -> [AFact] -> Poly -> Maybe Integer
lowerBoundPoly natLvls facts (Poly p) = foldM addTerm 0 (Map.toList p)
  where
    addTerm acc (mono, coeff)
      | coeff == 0 = Just acc
      | coeff > 0 = do
          lb <- lowerOf (boundsMonomial natLvls facts mono)
          pure (acc + coeff * lb)
      | otherwise = do
          ub <- upperOf (boundsMonomial natLvls facts mono)
          pure (acc + coeff * ub)

boundsMonomial :: Set Int -> [AFact] -> Monomial -> ABounds
boundsMonomial natLvls facts (Monomial powers) =
  List.foldl' mulBounds (ABounds (Just 1) (Just 1))
    [ powBounds power (varBounds natLvls facts v)
    | (v, pow) <- Map.toList powers
    , let power = pow
    ]

powBounds :: Int -> ABounds -> ABounds
powBounds e b
  | e <= 0 = ABounds (Just 1) (Just 1)
  | e == 1 = b
powBounds e (ABounds (Just l) (Just u))
  | l >= 0 = ABounds (Just (l ^ e)) (Just (u ^ e))
  | u <= 0 =
      let lo = if even e then min (l ^ e) (u ^ e) else l ^ e
          hi = if even e then max (l ^ e) (u ^ e) else u ^ e
       in ABounds (Just lo) (Just hi)
  | even e = ABounds (Just 0) (Just (max (abs l) (abs u) ^ e))
  | otherwise = ABounds (Just (l ^ e)) (Just (u ^ e))
powBounds e (ABounds (Just l) Nothing)
  | l >= 0 = ABounds (Just (l ^ e)) Nothing
powBounds e (ABounds Nothing (Just u))
  | u <= 0 && odd e = ABounds Nothing (Just (u ^ e))
  | u <= 0 && even e = ABounds (Just 0) Nothing
powBounds _ _ = ABounds Nothing Nothing

lastMaybe :: [a] -> Maybe a
lastMaybe [] = Nothing
lastMaybe xs = Just (last xs)

last2 :: [a] -> Maybe (a, a)
last2 xs = case reverse xs of
  b : a : _ -> Just (a, b)
  _ -> Nothing

nthMaybe :: Int -> [a] -> Maybe a
nthMaybe i xs
  | i < 0 = Nothing
  | otherwise = case drop i xs of
      x : _ -> Just x
      [] -> Nothing
