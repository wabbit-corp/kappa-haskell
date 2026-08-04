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
  , Change (..)
  , SCGraph (..)
  , sizeChangeTerminates
  , strongerChange
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
  , simplifyDecisionTermAt
  , negateFact
  , intArithPrim
  , intCmpPrim
  , canonicalTrustedIntPrimitive
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

import Data.List (nub, sortOn)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, isJust, isNothing)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as T
import Text.Read (readMaybe)

import Kappa.Arithmetic
import Kappa.Builtins
  ( gPrel
  , prelFalse
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
  , substTopTermAt
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

-- | One relation in a size-change graph. A weak edge preserves structural
-- size; a strict edge proves a proper subterm. The graph algebra is syntax
-- independent so source Core and serialized KCore replay the same decision
-- procedure instead of maintaining parallel termination checkers.
data Change = ChWeak | ChStrict
  deriving stock (Eq, Ord, Show)

data SCGraph name = SCGraph
  { scFrom :: !name
  , scTo :: !name
  , scRows :: !Int
  , scCols :: !Int
  , scMat :: !(Map (Int, Int) Change)
  }
  deriving stock (Eq, Ord, Show)

-- | Lee-Jones-Ben-Amram size-change termination over a finite graph closure.
-- The deterministic cap is deliberately fail-closed: exceeding it cannot turn
-- an unverified recursive component into a total one.
sizeChangeTerminates :: Ord name => [SCGraph name] -> Bool
sizeChangeTerminates initial = go (Set.fromList initial) initial (0 :: Int)
  where
    graphCap = 4096 :: Int
    go allGraphs work fuel
      | Set.size allGraphs > graphCap = False
      | fuel > graphCap = False
      | null work = all idempotentCycleHasStrictDiagonal (Set.toList allGraphs)
      | otherwise =
          let newComps =
                nub
                  [ comp
                  | g1 <- work
                  , g2 <- Set.toList allGraphs
                  , comp <- catMaybes [composeSC g1 g2, composeSC g2 g1]
                  , not (Set.member comp allGraphs)
                  ]
              all' = foldr Set.insert allGraphs newComps
           in go all' newComps (fuel + 1)

    idempotentCycleHasStrictDiagonal graph
      | scFrom graph /= scTo graph = True
      | Just squared <- composeSC graph graph
      , squared == graph = hasStrictDiagonal graph
      | otherwise = True

    hasStrictDiagonal graph =
      let dimension = min (scRows graph) (scCols graph)
       in any
            (\index -> Map.lookup (index, index) (scMat graph) == Just ChStrict)
            [0 .. dimension - 1]

composeSC :: Ord name => SCGraph name -> SCGraph name -> Maybe (SCGraph name)
composeSC left right
  | scTo left /= scFrom right = Nothing
  | otherwise =
      Just
        SCGraph
          { scFrom = scFrom left
          , scTo = scTo right
          , scRows = scRows left
          , scCols = scCols right
          , scMat = Map.fromListWith strongerChange entries
          }
  where
    entries =
      [ ((source, target), composeChange first second)
      | ((source, middle), first) <- Map.toList (scMat left)
      , ((middle', target), second) <- Map.toList (scMat right)
      , middle == middle'
      ]

composeChange :: Change -> Change -> Change
composeChange ChStrict _ = ChStrict
composeChange _ ChStrict = ChStrict
composeChange ChWeak ChWeak = ChWeak

strongerChange :: Change -> Change -> Change
strongerChange ChStrict _ = ChStrict
strongerChange _ ChStrict = ChStrict
strongerChange ChWeak ChWeak = ChWeak

-- | Expand direct global references through known-reducible bodies. The caller
-- supplies a point lookup rather than a materialized environment so this stays
-- independent of checker state without forcing incremental callers to rebuild
-- their complete global map for every dependency query.
expandedGlobalsOfTerm
  :: (GName -> Maybe (Bool, Maybe Term))
  -> Term
  -> Set GName
expandedGlobalsOfTerm lookupGlobal = go Set.empty
  where
    go seen tm =
      Set.unions [expand seen g | g <- Set.toList (globalsOfTerm tm)]

    expand seen g
      | Set.member g seen = Set.singleton g
      | otherwise =
          Set.insert g $
            case lookupGlobal g of
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
      CArithmeticProof certificate ->
        CArithmeticProof <$> traverseArithmeticCertificate (go curDepth) certificate
      CLit l -> Just (CLit l)
      CCtorI cg universes ann arguments ->
        CCtorI cg universes <$> traverse (go curDepth) ann
          <*> traverse (\argument -> (\term -> argument {caTerm = term}) <$> go curDepth (caTerm argument)) arguments
      CMatch s scrutineeAnn resultAnn alts ->
        CMatch
          <$> go curDepth s
          <*> traverse (go curDepth) scrutineeAnn
          <*> traverse (go curDepth) resultAnn
          <*> traverse goAlt alts
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
      CThunkE e suspensionType ->
        CThunkE <$> go curDepth e <*> traverse (go curDepth) suspensionType
      CLazyE e suspensionType ->
        CLazyE <$> go curDepth e <*> traverse (go curDepth) suspensionType
      CForceE e resultType ->
        CForceE <$> go curDepth e <*> traverse (go curDepth) resultType
      CIf a b c -> CIf <$> go curDepth a <*> go curDepth b <*> go curDepth c
      CQuote qs slots -> CQuote qs <$> traverse (go curDepth) slots

    traverseField curDepth fs = traverse (\(n, x) -> (,) n <$> go curDepth x) fs

simplifyDecisionTerm :: Term -> Term
simplifyDecisionTerm = simplifyDecisionTermAt 0

-- | Reduce local decision structure without unfolding global definitions.
-- Keeping selected operation heads intact is important for proof-producing
-- arithmetic: their checked identities are part of the solver authority.
-- The ambient depth makes beta reduction correct for Core level variables.
simplifyDecisionTermAt :: Int -> Term -> Term
simplifyDecisionTermAt = go
  where
    go depth = \case
      CIf c t e ->
        let c' = go depth c
            t' = go depth t
            e' = go depth e
         in case (c', t', e') of
              (CCtor g _ [], _, _) | g == prelTrue -> t'
              (CCtor g _ [], _, _) | g == prelFalse -> e'
              (_, CCtor gt _ [], CCtor gf _ []) | gt == prelTrue, gf == prelFalse -> c'
              _ -> CIf c' t' e'
      CMatch (CIf c t e) scrutineeAnn resultAnn alts
        | all ((== 0) . patBindersC . caPat) alts ->
            go depth
              ( CIf c
                  (CMatch t scrutineeAnn resultAnn alts)
                  (CMatch e scrutineeAnn resultAnn alts)
              )
      CMatch s scrutineeAnn resultAnn alts ->
        let s' = go depth s
            alts' =
              [ let branchDepth = depth + patBindersC p
                 in CaseAlt p (fmap (go branchDepth) gd) (go branchDepth b)
              | CaseAlt p gd b <- alts
              ]
         in fromMaybe
              (CMatch s' scrutineeAnn resultAnn alts')
              (reduceSimpleMatch s' alts')
      CApp ic f a ->
        let function = go depth f
            argument = go depth a
         in case function of
              CLamM _ binderIcit _ _ body
                | binderIcit == ic ->
                    go depth (substTopTermAt depth argument body)
              _ -> CApp ic function argument
      CUniverseLift from to evidence t ->
        CUniverseLift from to evidence (go depth t)
      CSchemaLift family source target roles evidence certificate sourceArguments targetArguments t ->
        CSchemaLift family source target roles evidence certificate
          (map (go depth) sourceArguments)
          (map (go depth) targetArguments)
          (go depth t)
      CLamM mode ic q n b -> CLamM mode ic q n (go (depth + 1) b)
      CPiEvidenceM mode formation ic q brw n assumption origin a b ->
        CPiEvidenceM mode formation ic q brw n assumption origin
          (go depth a)
          (go (depth + 1) b)
      CCtorI g universes ann arguments ->
        CCtorI g universes (fmap (go depth) ann)
          [argument {caTerm = go depth (caTerm argument)} | argument <- arguments]
      CRecordTQ fs ->
        CRecordTQ
          [ fmap (go (depth + index)) field
          | (index, field) <- zip [0 :: Int ..] fs
          ]
      CRecordV fs -> CRecordV [(n, go depth x) | (n, x) <- fs]
      CProjM mode e f -> CProjM mode (go depth e) f
      CProjAtM mode e f i -> CProjAtM mode (go depth e) f i
      CVariantT ms -> CVariantT (map (go depth) ms)
      CInject tag e -> CInject tag (go depth e)
      CLetM mode q n a b c ->
        CLetM mode q n (go depth a) (go depth b) (go (depth + 1) c)
      CLetRecM mode q n a b c ->
        CLetRecM mode q n (go depth a) (go (depth + 1) b) (go (depth + 1) c)
      CLetPolyM mode q n telescope a b c ->
        CLetPolyM mode q n telescope (go depth a) (go depth b) (go (depth + 1) c)
      CLetRecPolyM mode q n telescope a b c ->
        CLetRecPolyM mode q n telescope (go depth a) (go (depth + 1) b) (go (depth + 1) c)
      CLetRecGroupM telescope definitions body ->
        let groupDepth = depth + length definitions
         in CLetRecGroupM telescope
              [ definition
                  { clrdType = go depth (clrdType definition)
                  , clrdRhs = go groupDepth (clrdRhs definition)
                  }
              | definition <- definitions
              ]
              (go groupDepth body)
      CThunkE e suspensionType -> CThunkE (go depth e) (go depth <$> suspensionType)
      CLazyE e suspensionType -> CLazyE (go depth e) (go depth <$> suspensionType)
      CForceE e resultType ->
        case go depth e of
          CThunkE body _ -> go depth body
          delayed -> CForceE delayed (go depth <$> resultType)
      CSealE ls e -> CSealE ls (go depth e)
      CSigT ls e -> CSigT ls (go depth e)
      CQuote qs slots -> CQuote qs (map (go depth) slots)
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

-- | Map either trusted spelling of an integer primitive to the checked public
-- prelude identity used in finalized Core and interchange artifacts. The
-- finite primitive classifiers above are the authority; an arbitrary name in
-- either trusted module is not rewritten.
canonicalTrustedIntPrimitive :: GName -> Maybe GName
canonicalTrustedIntPrimitive global@(GName _ operation)
  | isJust (intArithPrim global) || isJust (intCmpPrim global) =
      Just (gPrel operation)
  | otherwise = Nothing

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
  CUniverseLift _ _ _ term -> arithOf d term
  CSchemaLift _ _ _ _ _ _ _ _ term -> arithOf d term
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
