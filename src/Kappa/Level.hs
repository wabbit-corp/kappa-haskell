-- | Canonical universe levels and the pure ordering judgment of Spec
-- §11.1.1-§11.1.2.2. Source expressions never enter this module: the
-- elaborator first resolves operations and selected evidence, then translates
-- only compiler-owned intrinsic heads to this representation.
module Kappa.Level
  ( Level (..)
  , NeutralLevelAtom (..)
  , NeutralLevelTerm (..)
  , NeutralLevelLiteral (..)
  , neutralLevelTermAtom
  , neutralLevelTermDigest
  , mapNeutralLevelTermLevels
  , mapNeutralLevelAtomLevels
  , neutralLevelTermLevels
  , neutralLevelTermLocals
  , LevelMeta
  , UniverseConstraint (..)
  , DeclarationUniverseTelescope (..)
  , emptyDeclarationUniverseTelescope
  , ConstraintOrigin (..)
  , LevelConstraint (..)
  , LevelSolveError (..)
  , LevelAssignmentGraphError (..)
  , LevelAssignmentGraphBudget
  , LevelSolution (..)
  , PrincipalInferenceOutcome (..)
  , PrincipalNonLeastWitness (..)
  , Assumptions
  , SolveResult (..)
  , emptyAssumptions
  , assumptionsList
  , classifyAssumptions
  , insertAssumption
  , assumptionsConsistent
  , finiteLevel
  , levelSucc
  , levelAdd
  , levelMax
  , normalizeLevel
  , levelMetas
  , levelVars
  , levelFields
  , levelParams
  , substituteLevelMeta
  , substituteLevelMetas
  , substituteLevelConstraintMetas
  , substituteLevelParams
  , abstractLocalLevelParams
  , instantiateLocalLevelParams
  , weakenLevelLocalsAt
  , solveLevelConstraints
  , solveLevelConstraintsFor
  , inferPrincipalLevelsFor
  , mergeLevelAssignments
  , emptyLevelAssignmentGraphBudget
  , rebuildLevelAssignmentGraphBudget
  , extendLevelAssignmentGraph
  , extendLevelAssignmentGraphWithBudget
  , proveLevelLeq
  , proveLevelEq
  , compareClosedLevel
  , renderLevel
  ) where

import Control.Applicative ((<|>))
import Control.Monad (guard)
import Data.Integer.SAT qualified as SAT
import Data.Graph (SCC (..), stronglyConnComp)
import Data.List (nub, sort, sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Data.Word (Word8)
import Kappa.SemanticHash (sha256Hex)

type LevelMeta = Int

-- | A serializable, alpha-stable fragment of typed Core used as the identity
-- of an opaque but admissible TypeLevel term. Locals are de Bruijn /levels/
-- so source binder spelling is absent from semantic identity. Globals retain
-- their resolved module and declaration identities. This syntax is kept
-- independent of 'Kappa.Core' to avoid making the level solver depend on the
-- term calculus; the checker is the sole producer and KCoreText is the sole
-- serializer.
data NeutralLevelTerm
  = NLTLocal !Int
  | NLTLocalDeclaration !Int ![Level]
  | NLTGlobal ![Text] !Text ![Level]
  | NLTConstruct ![Text] !Text ![Level] ![(Bool, NeutralLevelTerm)]
  | NLTApply !Bool !NeutralLevelTerm !NeutralLevelTerm
  | NLTProject !Text !NeutralLevelTerm
  | NLTLevel !Level
  | NLTLiteral !NeutralLevelLiteral
  | NLTRecord ![(Text, NeutralLevelTerm)]
  | NLTIf !NeutralLevelTerm !NeutralLevelTerm !NeutralLevelTerm
  | NLTUnsupported !Text
  deriving stock (Eq, Ord, Show)

data NeutralLevelLiteral
  = NLLInt !Integer
  | NLLDouble !Double
  | NLLString !Text
  | NLLScalar !Char
  | NLLByte !Word8
  | NLLBytes ![Word8]
  | NLLGrapheme !Text
  deriving stock (Eq, Ord, Show)

-- | Source neutral terms carry their canonical structural artifact and its
-- deterministic digest. The symbolic form is reserved for direct solver
-- tests, where no typed source/KCore term exists; serializers reject it.
data NeutralLevelAtom
  = NeutralLevelTermAtom !Text !NeutralLevelTerm
  | NeutralLevelSymbol !Text ![Level]
  deriving stock (Eq, Ord, Show)

neutralLevelTermAtom :: NeutralLevelTerm -> NeutralLevelAtom
neutralLevelTermAtom term = NeutralLevelTermAtom (neutralLevelTermDigest term) term

neutralLevelTermDigest :: NeutralLevelTerm -> Text
neutralLevelTermDigest =
  sha256Hex . ("KAPPA:v1:NeutralLevelTerm:" <>) . T.pack . show

mapNeutralLevelTermLevels :: (Level -> Level) -> NeutralLevelTerm -> NeutralLevelTerm
mapNeutralLevelTermLevels mapLevel = go
  where
    go = \case
      NLTLocal local -> NLTLocal local
      NLTLocalDeclaration local levels -> NLTLocalDeclaration local (map mapLevel levels)
      NLTGlobal owner name levels -> NLTGlobal owner name (map mapLevel levels)
      NLTConstruct owner name levels arguments ->
        NLTConstruct owner name (map mapLevel levels) [(explicit, go argument) | (explicit, argument) <- arguments]
      NLTApply explicit function argument -> NLTApply explicit (go function) (go argument)
      NLTProject field receiver -> NLTProject field (go receiver)
      NLTLevel level -> NLTLevel (mapLevel level)
      NLTLiteral literal -> NLTLiteral literal
      NLTRecord fields -> NLTRecord [(field, go value) | (field, value) <- fields]
      NLTIf condition thenBranch elseBranch -> NLTIf (go condition) (go thenBranch) (go elseBranch)
      NLTUnsupported reason -> NLTUnsupported reason

neutralLevelTermLevels :: NeutralLevelTerm -> [Level]
neutralLevelTermLevels = \case
  NLTLocal _ -> []
  NLTLocalDeclaration _ levels -> levels
  NLTGlobal _ _ levels -> levels
  NLTConstruct _ _ levels arguments -> levels ++ concatMap (neutralLevelTermLevels . snd) arguments
  NLTApply _ function argument -> neutralLevelTermLevels function ++ neutralLevelTermLevels argument
  NLTProject _ receiver -> neutralLevelTermLevels receiver
  NLTLevel level -> [level]
  NLTLiteral _ -> []
  NLTRecord fields -> concatMap (neutralLevelTermLevels . snd) fields
  NLTIf condition thenBranch elseBranch ->
    concatMap neutralLevelTermLevels [condition, thenBranch, elseBranch]
  NLTUnsupported _ -> []

neutralLevelTermLocals :: NeutralLevelTerm -> [Int]
neutralLevelTermLocals = \case
  NLTLocal local -> [local]
  NLTLocalDeclaration local _ -> [local]
  NLTGlobal _ _ _ -> []
  NLTConstruct _ _ _ arguments -> concatMap (neutralLevelTermLocals . snd) arguments
  NLTApply _ function argument -> neutralLevelTermLocals function ++ neutralLevelTermLocals argument
  NLTProject _ receiver -> neutralLevelTermLocals receiver
  NLTLevel _ -> []
  NLTLiteral _ -> []
  NLTRecord fields -> concatMap (neutralLevelTermLocals . snd) fields
  NLTIf condition thenBranch elseBranch ->
    concatMap neutralLevelTermLocals [condition, thenBranch, elseBranch]
  NLTUnsupported _ -> []

mapNeutralLevelAtomLevels :: (Level -> Level) -> NeutralLevelAtom -> NeutralLevelAtom
mapNeutralLevelAtomLevels mapLevel = \case
  NeutralLevelTermAtom _ term -> neutralLevelTermAtom (mapNeutralLevelTermLevels mapLevel term)
  NeutralLevelSymbol identity arguments -> NeutralLevelSymbol identity (map mapLevel arguments)

neutralAtomLevels :: NeutralLevelAtom -> [Level]
neutralAtomLevels = \case
  NeutralLevelTermAtom _ term -> neutralLevelTermLevels term
  NeutralLevelSymbol _ arguments -> arguments

neutralAtomLocals :: NeutralLevelAtom -> [Int]
neutralAtomLocals = \case
  NeutralLevelTermAtom _ term -> neutralLevelTermLocals term
  NeutralLevelSymbol _ _ -> []

-- | Alpha-stable canonical level syntax. 'LVar' is a de Bruijn /level/
-- identity allocated by the elaboration context, not a rendered source name.
data Level
  = LZero
  | LFinite !Integer
  -- ^ Compact normal form for repeated finite successor. This is an internal
  -- normalization node, not an additional source-level TypeLevel operation.
  | LOmega
  | LSucc !Level
  | LAdd !Level !Level
  | LMax !Level !Level
  | LVar !Int
  | LParam !Int
  -- ^ Hidden declaration-universe parameter. This is distinct from 'LVar':
  -- it is instantiated at a global reference and is never a term binder.
  | LField !Int !Text
  | LProjection !Int ![Text]
  -- ^ A TypeLevel-valued projection rooted at a local term binder. The
  -- integer is the binder's de Bruijn level (outermost-first), and the path
  -- is the resolved record/package field path. Unlike 'LField', which names
  -- a sibling of the distinguished dependent-record @this@ value, this node
  -- is substituted when the owning term binder is instantiated.
  | LNeutral !NeutralLevelAtom
  -- ^ A stable total neutral level term. Its artifact carries the
  -- alpha-normalized structural digest, resolved global identities, and
  -- free-variable identities required by §11.1.1. A meta below this node is
  -- not assignable without selected monotonicity/order-embedding evidence.
  | LMeta !LevelMeta
  deriving stock (Eq, Show)

-- | §11.1.2.4A's portable ordering of constructor normal forms.  This
-- instance is used while building the sorted additive and maximum lists, so
-- it must encode the specified semantic ranks rather than Haskell's source
-- constructor order.  The final raw tie-break is observable only for
-- noncanonical terms with the same constructor-NF key; it preserves the
-- 'Ord' law that @compare x y == EQ@ exactly when @x == y@.
instance Ord Level where
  compare left right
    | left == right = EQ
    | otherwise =
        case compareConstructorNF left right of
          EQ -> compareRawLevel left right
          ordering -> ordering

compareConstructorNF :: Level -> Level -> Ordering
compareConstructorNF left right =
  case compare (constructorNFRank left) (constructorNFRank right) of
    EQ -> compareWithinRank left right
    ordering -> ordering
  where
    compareWithinRank lhs rhs
      | Just lhsClosed <- closedLevel lhs
      , Just rhsClosed <- closedLevel rhs = compare lhsClosed rhsClosed
    compareWithinRank lhs rhs = case (lhs, rhs) of
      (LVar lhsLocal, LVar rhsLocal) -> compare lhsLocal rhsLocal
      (LParam lhsParameter, LParam rhsParameter) -> compare lhsParameter rhsParameter
      (LField lhsOwner lhsField, LField rhsOwner rhsField) ->
        compare (lhsOwner, lhsField) (rhsOwner, rhsField)
      (LProjection lhsRoot lhsPath, LProjection rhsRoot rhsPath) ->
        compare (lhsRoot, lhsPath) (rhsRoot, rhsPath)
      (LNeutral lhsAtom, LNeutral rhsAtom) -> compareNeutralLevelAtom lhsAtom rhsAtom
      (LAdd _ _, LAdd _ _) -> compare (flattenAddNF lhs) (flattenAddNF rhs)
      (LSucc _, LSucc _) -> compare (flattenAddNF lhs) (flattenAddNF rhs)
      (LSucc _, LAdd _ _) -> compare (flattenAddNF lhs) (flattenAddNF rhs)
      (LAdd _ _, LSucc _) -> compare (flattenAddNF lhs) (flattenAddNF rhs)
      (LMax _ _, LMax _ _) -> compare (flattenMaxNF lhs) (flattenMaxNF rhs)
      (LMeta lhsMeta, LMeta rhsMeta) -> compare lhsMeta rhsMeta
      -- Different atom kinds are ordered local, declaration parameter,
      -- field, projection, neutral term.  Other same-rank combinations are
      -- noncanonical and use their stable structural tags.
      _ -> compare (atomKindRank lhs, rawLevelTag lhs) (atomKindRank rhs, rawLevelTag rhs)

constructorNFRank :: Level -> Int
constructorNFRank level
  | Just _ <- closedLevel level = 0
constructorNFRank level = case level of
  LVar _ -> 1
  LParam _ -> 1
  LField _ _ -> 1
  LProjection _ _ -> 1
  LNeutral _ -> 1
  LSucc _ -> 2
  LAdd _ _ -> 2
  LMax _ _ -> 3
  LMeta _ -> 4
  -- All closed constructors were handled above.
  LZero -> 0
  LFinite _ -> 0
  LOmega -> 0

atomKindRank :: Level -> Int
atomKindRank = \case
  LVar _ -> 0
  LParam _ -> 1
  LField _ _ -> 2
  LProjection _ _ -> 3
  LNeutral _ -> 4
  level -> 5 + rawLevelTag level

flattenAddNF :: Level -> [Level]
flattenAddNF = \case
  LAdd lhs rhs -> flattenAddNF lhs ++ flattenAddNF rhs
  LSucc level -> flattenAddNF level ++ [LFinite 1]
  LZero -> []
  level -> [level]

flattenMaxNF :: Level -> [Level]
flattenMaxNF = \case
  LMax lhs rhs -> flattenMaxNF lhs ++ flattenMaxNF rhs
  LZero -> []
  level -> [level]

compareNeutralLevelAtom :: NeutralLevelAtom -> NeutralLevelAtom -> Ordering
compareNeutralLevelAtom left right = case (left, right) of
  (NeutralLevelTermAtom lhsDigest lhsTerm, NeutralLevelTermAtom rhsDigest rhsTerm) ->
    compare (lhsDigest, lhsTerm) (rhsDigest, rhsTerm)
  (NeutralLevelTermAtom {}, NeutralLevelSymbol {}) -> LT
  (NeutralLevelSymbol {}, NeutralLevelTermAtom {}) -> GT
  (NeutralLevelSymbol lhsIdentity lhsArguments, NeutralLevelSymbol rhsIdentity rhsArguments) ->
    compare (lhsIdentity, lhsArguments) (rhsIdentity, rhsArguments)

compareRawLevel :: Level -> Level -> Ordering
compareRawLevel left right =
  case compare (rawLevelTag left) (rawLevelTag right) of
    EQ -> case (left, right) of
      (LZero, LZero) -> EQ
      (LFinite lhs, LFinite rhs) -> compare lhs rhs
      (LOmega, LOmega) -> EQ
      (LSucc lhs, LSucc rhs) -> compare lhs rhs
      (LAdd lhsA lhsB, LAdd rhsA rhsB) -> compare (lhsA, lhsB) (rhsA, rhsB)
      (LMax lhsA lhsB, LMax rhsA rhsB) -> compare (lhsA, lhsB) (rhsA, rhsB)
      (LVar lhs, LVar rhs) -> compare lhs rhs
      (LParam lhs, LParam rhs) -> compare lhs rhs
      (LField lhsOwner lhsField, LField rhsOwner rhsField) -> compare (lhsOwner, lhsField) (rhsOwner, rhsField)
      (LProjection lhsRoot lhsPath, LProjection rhsRoot rhsPath) -> compare (lhsRoot, lhsPath) (rhsRoot, rhsPath)
      (LNeutral lhs, LNeutral rhs) -> compareNeutralLevelAtom lhs rhs
      (LMeta lhs, LMeta rhs) -> compare lhs rhs
      _ -> EQ
    ordering -> ordering

rawLevelTag :: Level -> Int
rawLevelTag = \case
  LZero -> 0
  LFinite _ -> 1
  LOmega -> 2
  LSucc _ -> 3
  LAdd _ _ -> 4
  LMax _ _ -> 5
  LVar _ -> 6
  LParam _ -> 7
  LField _ _ -> 8
  LProjection _ _ -> 9
  LNeutral _ -> 10
  LMeta _ -> 11

data UniverseConstraint = UniverseConstraint
  { ucLower :: !Level
  , ucUpper :: !Level
  }
  deriving stock (Eq, Ord, Show)

data DeclarationUniverseTelescope = DeclarationUniverseTelescope
  { dutParameterCount :: !Int
  , dutExplicit :: !Bool
  -- ^ True when the source wrote the complete schema. Such a telescope may
  -- never be extended by implicit declaration-level generalization.
  }
  deriving stock (Eq, Ord, Show)

emptyDeclarationUniverseTelescope :: DeclarationUniverseTelescope
emptyDeclarationUniverseTelescope = DeclarationUniverseTelescope 0 False

newtype Assumptions = Assumptions [(Level, Level)]
  deriving stock (Eq, Show)

data SolveResult
  = Proved
  | Disproved
  | Blocked ![LevelMeta]
  | ContradictoryAssumptions
  | IndeterminateResourceLimit
  deriving stock (Eq, Show)

data ConstraintOrigin = ConstraintOrigin
  { coDescription :: !Text
  , coConstruct :: !Text
  }
  deriving stock (Eq, Ord, Show)

data LevelConstraint = LevelConstraint
  { lcIdentity :: !Int
  , lcLhs :: !Level
  , lcRhs :: !Level
  , lcOrigin :: !ConstraintOrigin
  , lcAssumptions :: !Assumptions
  }
  deriving stock (Eq, Show)

data LevelSolveError
  = LevelConstraintDisproved !LevelConstraint
  | LevelContradictoryAssumptions !LevelConstraint
  | LevelMetaOccurs !LevelMeta !Level !LevelConstraint
  | LevelResourceLimit !LevelConstraint !Int
  deriving stock (Eq, Show)

data LevelAssignmentGraphError
  = LevelAssignmentGraphConflict !LevelMeta !Level !Level
  | LevelAssignmentGraphResourceLimit !Int
  deriving stock (Eq, Show)

-- | Incremental certificate that the installed assignment graph remains
-- inside the portable materialization budget. The constructor is private so
-- callers cannot pair an arbitrary summary with a different graph.
data LevelAssignmentGraphBudget = LevelAssignmentGraphBudget
  { lagbRootCosts :: !(Map LevelMeta Int)
  , lagbTotalCost :: !Int
  }
  deriving stock (Eq, Show)

emptyLevelAssignmentGraphBudget :: LevelAssignmentGraphBudget
emptyLevelAssignmentGraphBudget = LevelAssignmentGraphBudget Map.empty 0

-- The portable solver is exact inside this explicit resource boundary.
-- Crossing it is never interpreted as proof or satisfiability failure:
-- callers receive the §11.1.2.4A indeterminate classification and fail
-- closed. The budget also bounds materialization of the indexed assignment
-- graph, preventing a compact repeated-meta DAG from expanding exponentially.
solverNodeBudget :: Int
solverNodeBudget = 100000

levelForestWithinBudget :: [Level] -> Bool
levelForestWithinBudget levels =
  snd (foldl countOne (0, True) levels)
  where
    countOne state@(_, False) _ = state
    countOne (used, True) level =
      let used' = levelNodeCostCapped (solverNodeBudget - used) level
       in (used + used', used + used' <= solverNodeBudget)

levelNodeCostCapped :: Int -> Level -> Int
levelNodeCostCapped remaining level
  | remaining < 1 = 1
  | otherwise =
      case level of
        LSucc child -> add 1 [child]
        LAdd left right -> add 1 [left, right]
        LMax left right -> add 1 [left, right]
        LNeutral atom -> add 1 (neutralAtomLevels atom)
        _ -> 1
  where
    add base children =
      foldl
        (\used child ->
           min (remaining + 1)
             (used + levelNodeCostCapped (remaining - used) child))
        base
        children

rebuildLevelAssignmentGraphBudget
  :: Map LevelMeta Level
  -> Either LevelAssignmentGraphError LevelAssignmentGraphBudget
rebuildLevelAssignmentGraphBudget assignments = do
  (costs, total) <-
    assignmentRootCosts
      assignments
      (Map.keysSet assignments)
      Map.empty
      solverNodeBudget
      (Map.keys assignments)
  pure (LevelAssignmentGraphBudget costs total)

assignmentGraphWithinBudget :: Map LevelMeta Level -> Bool
assignmentGraphWithinBudget assignments =
  case rebuildLevelAssignmentGraphBudget assignments of
    Right _ -> True
    Left _ -> False

assignmentRootCosts
  :: Map LevelMeta Level
  -> Set.Set LevelMeta
  -> Map LevelMeta Int
  -> Int
  -> [LevelMeta]
  -> Either LevelAssignmentGraphError (Map LevelMeta Int, Int)
assignmentRootCosts assignments recomputed fallbackCosts totalBudget roots =
  case foldl' visitRoot (Right (Map.empty, 0)) roots of
    Right result -> Right result
    Left () -> Left (LevelAssignmentGraphResourceLimit solverNodeBudget)
  where
    visitRoot (Left ()) _ = Left ()
    visitRoot (Right (memo, total)) meta =
      case costMeta Set.empty memo meta of
        Left () -> Left ()
        Right (cost, memo') ->
          let total' = total + cost
           in if total' > totalBudget
                then Left ()
                else Right (memo', total')

    costMeta visiting memo meta
      | Just cost <- Map.lookup meta memo = Right (cost, memo)
      | meta `Set.notMember` recomputed
      , Just cost <- Map.lookup meta fallbackCosts =
          Right (cost, memo)
      | meta `Set.member` visiting = Right (1, memo)
      | Just replacement <- Map.lookup meta assignments = do
          (cost, memo') <- costLevel (Set.insert meta visiting) memo replacement
          pure (cost, Map.insert meta cost memo')
      | otherwise = Right (1, memo)

    costLevel visiting memo = \case
      LMeta meta -> costMeta visiting memo meta
      LSucc child -> costChildren visiting memo 1 [child]
      LAdd left right -> costChildren visiting memo 1 [left, right]
      LMax left right -> costChildren visiting memo 1 [left, right]
      LNeutral atom -> costChildren visiting memo 1 (neutralAtomLevels atom)
      _ -> Right (1, memo)

    costChildren _ memo used [] = Right (used, memo)
    costChildren visiting memo used (child : rest) = do
      (cost, memo') <- costLevel visiting memo child
      let used' = used + cost
      if used' > solverNodeBudget
        then Left ()
        else costChildren visiting memo' used' rest

data LevelSolution = LevelSolution
  { lsAssignments :: !(Map LevelMeta Level)
  , lsResidual :: ![LevelConstraint]
  }
  deriving stock (Eq, Show)

-- | Normative §11.1.3 outcome classes for selected-meta inference. The old
-- 'LevelSolution' remains the detailed assignment/residual carrier used by
-- the elaborator; this classification prevents callers from conflating a
-- residual constraint with either inconsistency or a proved lack of a least
-- solution.
data PrincipalInferenceOutcome
  = SolvedPrincipal !(Map LevelMeta Level)
  | Unsatisfiable
  | NoPointwiseLeastSolution !PrincipalNonLeastWitness
  | OutsidePortableInferenceFragment
  | BlockedByUnselectedMetas
  deriving stock (Eq, Show)

-- | Checked incomparable minimal assignments witnessing that a selected
-- system has solutions but no pointwise least one.
data PrincipalNonLeastWitness = PrincipalNonLeastWitness
  { pnlwLeft :: !(Map LevelMeta Level)
  , pnlwRight :: !(Map LevelMeta Level)
  }
  deriving stock (Eq, Show)

-- | Compose principal substitutions without revising an assignment that has
-- already been installed. A later substitution may solve a dependency named
-- by an older right-hand side, but two assignments for the same metavariable
-- must denote the same level after the complete substitution is applied.
-- Returning the normalized conflicting pair lets the elaborator report the
-- owning declaration rather than silently joining the values.
mergeLevelAssignments
  :: Map LevelMeta Level
  -> Map LevelMeta Level
  -> Either (LevelMeta, Level, Level) (Map LevelMeta Level)
mergeLevelAssignments old new =
  case conflicts of
    conflict : _ -> Left conflict
    [] -> Right normalized
  where
    raw = Map.union new old
    zonk = normalizeLevel . substituteLevelMetas raw
    normalized = Map.map zonk raw
    conflicts =
      [ (meta, oldLevel', newLevel')
      | meta <- Set.toAscList (Set.intersection (Map.keysSet old) (Map.keysSet new))
      , let oldLevel' = zonk (old Map.! meta)
            newLevel' = zonk (new Map.! meta)
      , not (semanticallyEqual oldLevel' newLevel')
      ]
    semanticallyEqual left right =
      proveLevelLeq emptyAssumptions left right == Proved
        && proveLevelLeq emptyAssumptions right left == Proved

-- | Extend an installed substitution graph without eagerly rewriting every
-- older right-hand side. The dependency index is oriented from a referenced
-- metavariable to the assignments whose effective values depend on it.
-- Consumers observe the graph through 'substituteLevelMetas'; the returned
-- affected closure is precisely the set whose effective values may have
-- changed and therefore need reflecting into the term metavariable store.
--
-- Existing assignments remain semantically immutable. An overlapping update
-- may use a different but equivalent presentation, but a genuine revision is
-- rejected before either map is changed.
extendLevelAssignmentGraph
  :: Map LevelMeta Level
  -> Map LevelMeta (Set.Set LevelMeta)
  -> Map LevelMeta Level
  -> Either
       LevelAssignmentGraphError
       (Map LevelMeta Level, Map LevelMeta (Set.Set LevelMeta), Set.Set LevelMeta)
extendLevelAssignmentGraph old oldDependents new = do
  budget <- rebuildLevelAssignmentGraphBudget old
  (combined, dependents, _, affected) <-
    extendLevelAssignmentGraphWithBudget old oldDependents budget new
  pure (combined, dependents, affected)

-- | Incremental form of 'extendLevelAssignmentGraph'. The supplied budget is
-- the opaque certificate returned by a previous call (or
-- 'emptyLevelAssignmentGraphBudget' for an empty graph). Only assignments in
-- the reverse dependency closure of this update are re-costed; exact replay
-- of an already-installed substitution is a constant-state no-op.
extendLevelAssignmentGraphWithBudget
  :: Map LevelMeta Level
  -> Map LevelMeta (Set.Set LevelMeta)
  -> LevelAssignmentGraphBudget
  -> Map LevelMeta Level
  -> Either
       LevelAssignmentGraphError
       ( Map LevelMeta Level
       , Map LevelMeta (Set.Set LevelMeta)
       , LevelAssignmentGraphBudget
       , Set.Set LevelMeta
       )
extendLevelAssignmentGraphWithBudget old oldDependents oldBudget new
  | exactReplay =
      Right (old, oldDependents, oldBudget, Set.empty)
  | otherwise = do
      budget <- recomputeAffectedBudget
      case conflicts of
        (meta, installed, requested) : _ ->
          Left (LevelAssignmentGraphConflict meta installed requested)
        [] -> Right (combined, dependents, budget, affected)
  where
    exactReplay =
      all
        (\(meta, requested) -> Map.lookup meta old == Just requested)
        (Map.toAscList new)
    combined = Map.union new old
    zonk = normalizeLevel . substituteLevelMetas combined
    conflicts =
      [ (meta, installed', requested')
      | (meta, requested) <- Map.toAscList new
      , Just installed <- [Map.lookup meta old]
      , let installed' = zonk installed
            requested' = zonk requested
      , not (semanticallyEqual installed' requested')
      ]
    semanticallyEqual left right =
      proveLevelLeq emptyAssumptions left right == Proved
        && proveLevelLeq emptyAssumptions right left == Proved

    removeDependent owner dependencies dependency =
      Map.update
        (\owners ->
           let owners' = Set.delete owner owners
            in if Set.null owners' then Nothing else Just owners')
        dependency
        dependencies
    removeOldDependencies dependencies (owner, _) =
      case Map.lookup owner old of
        Nothing -> dependencies
        Just previous ->
          foldl'
            (removeDependent owner)
            dependencies
            (Set.toList (Set.fromList (levelMetas previous)))
    addNewDependencies dependencies (owner, replacement) =
      foldl'
        (\current dependency ->
           Map.insertWith Set.union dependency (Set.singleton owner) current)
        dependencies
        (Set.toList (Set.fromList (levelMetas replacement)))
    dependents =
      foldl' addNewDependencies
        (foldl' removeOldDependencies oldDependents (Map.toAscList new))
        (Map.toAscList new)

    roots = Map.keysSet new
    affected = close roots roots
    close seen frontier
      | Set.null frontier = seen
      | otherwise =
          let next =
                Set.difference
                  (Set.unions
                    [ Map.findWithDefault Set.empty meta dependents
                    | meta <- Set.toList frontier
                    ])
                  seen
           in close (Set.union seen next) next

    oldAffectedTotal =
      Set.foldl'
        (\total meta ->
          total + Map.findWithDefault 0 meta (lagbRootCosts oldBudget))
        0
        affected
    unaffectedTotal =
      lagbTotalCost oldBudget - oldAffectedTotal
    affectedRoots = Set.toAscList affected
    recomputeAffectedBudget = do
      (affectedCosts, affectedTotal) <-
        assignmentRootCosts
          combined
          affected
          (lagbRootCosts oldBudget)
          (solverNodeBudget - unaffectedTotal)
          affectedRoots
      let costs = Map.union affectedCosts (lagbRootCosts oldBudget)
          total = unaffectedTotal + affectedTotal
      if total > solverNodeBudget
        then Left (LevelAssignmentGraphResourceLimit solverNodeBudget)
        else Right (LevelAssignmentGraphBudget costs total)

emptyAssumptions :: Assumptions
emptyAssumptions = Assumptions []

assumptionsList :: Assumptions -> [(Level, Level)]
assumptionsList (Assumptions xs) = xs

insertAssumption :: Level -> Level -> Assumptions -> Assumptions
insertAssumption lhs rhs (Assumptions xs) =
  Assumptions (nub ((normalizeLevel lhs, normalizeLevel rhs) : xs))

-- | Classify the scoped assumption context without collapsing contradiction,
-- blocked inference, and resource exhaustion into one Boolean. This is the
-- assumption-only form of the five-way judgment in §11.1.2.4A.
classifyAssumptions :: Assumptions -> SolveResult
classifyAssumptions assumptions@(Assumptions edges)
  | not (levelForestWithinBudget forest) = IndeterminateResourceLimit
  | not (null metas) = Blocked (sort (nub metas))
  | all (\(lhs, rhs) -> isJustRigid lhs && isJustRigid rhs) expandedEdges = Proved
  | otherwise =
      case presburgerSatisfiability assumptions Nothing of
        Satisfiable -> Proved
        UnsatisfiableFormula -> ContradictoryAssumptions
        SatisfiabilityResourceLimit -> IndeterminateResourceLimit
  where
    forest = concatMap (\(lower, upper) -> [lower, upper]) edges
    metas = concatMap levelMetas forest
    expandedEdges = concatMap expandLeftMaxAssumption edges
    isJustRigid = maybe False (const True) . atomicRigidLevel

-- | Compatibility predicate for validation sites that only need a yes/no
-- answer. Elaboration sites that produce diagnostics use
-- 'classifyAssumptions' so resource exhaustion is never called a
-- contradiction.
assumptionsConsistent :: Assumptions -> Bool
assumptionsConsistent assumptions = classifyAssumptions assumptions == Proved

finiteLevel :: Integral n => n -> Level
finiteLevel n
  | n <= 0 = LZero
  | otherwise = LFinite (toInteger n)

levelSucc :: Level -> Level
levelSucc = normalizeLevel . LSucc

levelAdd :: Level -> Level -> Level
levelAdd a = normalizeLevel . LAdd a

levelMax :: Level -> Level -> Level
levelMax a = normalizeLevel . LMax a

-- | A closed level below omega^2, represented as @omega*c + n@. Addition in
-- the source 'TypeLevel' algebra is the natural/Hessenberg sum on this
-- fragment, hence componentwise and commutative.
closedLevel :: Level -> Maybe (Integer, Integer)
closedLevel = \case
  LZero -> Just (0, 0)
  LFinite n -> Just (0, n)
  LOmega -> Just (1, 0)
  LSucc a -> do
    (c, n) <- closedLevel a
    pure (c, n + 1)
  LAdd a b -> do
    (ac, an) <- closedLevel a
    (bc, bn) <- closedLevel b
    pure (ac + bc, an + bn)
  LMax a b -> max <$> closedLevel a <*> closedLevel b
  LVar _ -> Nothing
  LParam _ -> Nothing
  LField _ _ -> Nothing
  LProjection _ _ -> Nothing
  LNeutral _ -> Nothing
  LMeta _ -> Nothing

compareClosedLevel :: Level -> Level -> Maybe Ordering
compareClosedLevel a b = compare <$> closedLevel (normalizeLevel a) <*> closedLevel (normalizeLevel b)

fromClosedOrdinal :: (Integer, Integer) -> Level
fromClosedOrdinal (c, n)
  | c <= 0 = finiteLevel n
  | n <= 0 = omegaPart
  | otherwise = LAdd omegaPart (finiteLevel n)
  where
    omegaPart = foldr1 LAdd (replicate (fromInteger c) LOmega)

normalizeLevel :: Level -> Level
normalizeLevel level =
  case go level of
    x | Just o <- closedLevel x -> fromClosedOrdinal o
    x -> x
  where
    go = \case
      LZero -> LZero
      LFinite n -> finiteLevel n
      LOmega -> LOmega
      LVar v -> LVar v
      LParam p -> LParam p
      LField i f -> LField i f
      LProjection root path -> LProjection root path
      LNeutral atom -> LNeutral (mapNeutralLevelAtomLevels go atom)
      LMeta m -> LMeta m
      LSucc a -> canonicalAdd [go a, LFinite 1]
      LAdd a b -> canonicalAdd (flattenAdd (go a) <> flattenAdd (go b))
      LMax a b -> canonicalMax (flattenMax (go a) <> flattenMax (go b))

    flattenAdd = \case
      LAdd a b -> flattenAdd a <> flattenAdd b
      LZero -> []
      x -> [x]

    canonicalAdd xs =
      let (closed, open) = foldr collect ((0, 0), []) xs
          closedTerm = fromClosedOrdinal closed
          terms = sort (open <> [closedTerm | closedTerm /= LZero])
       in case terms of
            [] -> LZero
            [x] -> x
            x : rest -> foldl LAdd x rest

    collect x ((coefficient, remainder), open) =
      case closedLevel x of
        Just (c, n) -> ((coefficient + c, remainder + n), open)
        Nothing -> ((coefficient, remainder), x : open)

    flattenMax = \case
      LMax a b -> flattenMax a <> flattenMax b
      LZero -> Set.empty
      x -> Set.singleton x

    canonicalMax xs =
      case Set.toAscList xs of
        [] -> LZero
        [x] -> x
        x : rest -> foldl LMax x rest

levelMetas :: Level -> [LevelMeta]
levelMetas = sort . Set.toList . go
  where
    go = \case
      LMeta m -> Set.singleton m
      LNeutral atom -> Set.unions (map go (neutralAtomLevels atom))
      LSucc a -> go a
      LAdd a b -> go a <> go b
      LMax a b -> go a <> go b
      _ -> Set.empty

levelVars :: Level -> [Int]
levelVars = sort . Set.toList . go
  where
    go = \case
      LVar v -> Set.singleton v
      LProjection root _ -> Set.singleton root
      LNeutral atom ->
        Set.fromList (neutralAtomLocals atom)
          <> Set.unions (map go (neutralAtomLevels atom))
      LSucc a -> go a
      LAdd a b -> go a <> go b
      LMax a b -> go a <> go b
      _ -> Set.empty

levelParams :: Level -> [Int]
levelParams = sort . Set.toList . go
  where
    go = \case
      LParam p -> Set.singleton p
      LNeutral atom -> Set.unions (map go (neutralAtomLevels atom))
      LSucc a -> go a
      LAdd a b -> go a <> go b
      LMax a b -> go a <> go b
      _ -> Set.empty

-- | Stable identities for level-valued fields in a dependent record or
-- package telescope. Record labels are semantic identities, so unlike source
-- binder names they do not require alpha-renaming.
levelFields :: Level -> [(Int, Text)]
levelFields = sort . Set.toList . go
  where
    go = \case
      LField i f -> Set.singleton (i, f)
      LNeutral atom -> Set.unions (map go (neutralAtomLevels atom))
      LSucc a -> go a
      LAdd a b -> go a <> go b
      LMax a b -> go a <> go b
      _ -> Set.empty

substituteLevelMeta :: LevelMeta -> Level -> Level -> Level
substituteLevelMeta meta replacement = normalizeLevel . go
  where
    go = \case
      LMeta m | m == meta -> replacement
      LNeutral atom -> LNeutral (mapNeutralLevelAtomLevels go atom)
      LSucc a -> LSucc (go a)
      LAdd a b -> LAdd (go a) (go b)
      LMax a b -> LMax (go a) (go b)
      x -> x

substituteLevelMetas :: Map LevelMeta Level -> Level -> Level
substituteLevelMetas assignments = normalizeLevel . go Set.empty
  where
    go seen = \case
      LMeta m
        | m `Set.member` seen -> LMeta m
        | Just replacement <- Map.lookup m assignments -> go (Set.insert m seen) replacement
      LNeutral atom -> LNeutral (mapNeutralLevelAtomLevels (go seen) atom)
      LSucc a -> LSucc (go seen a)
      LAdd a b -> LAdd (go seen a) (go seen b)
      LMax a b -> LMax (go seen a) (go seen b)
      level -> level

-- | Apply one metavariable substitution to the complete judgment. The
-- assumptions are part of a 'LevelConstraint''s proof context, not diagnostic
-- metadata: leaving them in the pre-substitution identity space can turn an
-- authenticated residual relation into an unrelated rigid inequality after
-- declaration generalization.
substituteLevelConstraintMetas :: Map LevelMeta Level -> LevelConstraint -> LevelConstraint
substituteLevelConstraintMetas assignments constraint =
  constraint
    { lcLhs = substituteLevelMetas assignments (lcLhs constraint)
    , lcRhs = substituteLevelMetas assignments (lcRhs constraint)
    , lcAssumptions =
        foldr
          (\(lower, upper) ->
             insertAssumption
               (substituteLevelMetas assignments lower)
               (substituteLevelMetas assignments upper))
          emptyAssumptions
          (assumptionsList (lcAssumptions constraint))
    }

substituteLevelParams :: [Level] -> Level -> Level
substituteLevelParams arguments = normalizeLevel . go
  where
    go = \case
      LParam p -> case drop p arguments of
        replacement : _ -> replacement
        [] -> LParam p
      LNeutral atom -> LNeutral (mapNeutralLevelAtomLevels go atom)
      LSucc a -> LSucc (go a)
      LAdd a b -> LAdd (go a) (go b)
      LMax a b -> LMax (go a) (go b)
      level -> level

-- | Enter a local declaration-universe telescope with @count@ parameters.
-- Existing declaration parameters become outer references above the new
-- prefix, exactly as term de Bruijn indices shift under a binder.
abstractLocalLevelParams :: Int -> Level -> Level
abstractLocalLevelParams count = normalizeLevel . go
  where
    go = \case
      LParam parameter -> LParam (parameter + count)
      LNeutral atom -> LNeutral (mapNeutralLevelAtomLevels go atom)
      LSucc level -> LSucc (go level)
      LAdd left right -> LAdd (go left) (go right)
      LMax left right -> LMax (go left) (go right)
      level -> level

-- | Leave a local declaration-universe telescope. The leading parameters are
-- specialized from the occurrence spine and outer parameters are shifted
-- back into the enclosing declaration scope.
instantiateLocalLevelParams :: Int -> [Level] -> Level -> Level
instantiateLocalLevelParams count arguments = normalizeLevel . go
  where
    go = \case
      LParam parameter
        | parameter < count ->
            case drop parameter arguments of
              replacement : _ -> replacement
              [] -> LParam parameter
        | otherwise -> LParam (parameter - count)
      LNeutral atom -> LNeutral (mapNeutralLevelAtomLevels go atom)
      LSucc level -> LSucc (go level)
      LAdd left right -> LAdd (go left) (go right)
      LMax left right -> LMax (go left) (go right)
      level -> level

-- | Insert one ordinary term binder at the supplied de Bruijn /level/.
-- Local level identities are absolute within their enclosing term scope, so
-- every identity introduced at or inside the insertion point moves by one.
-- This includes the roots embedded in opaque neutral terms; changing only
-- 'LVar'/'LProjection' would make two representations of the same admissible
-- level term disagree after weakening.
weakenLevelLocalsAt :: Int -> Level -> Level
weakenLevelLocalsAt cutoff = normalizeLevel . go
  where
    weakenLocal local
      | local >= cutoff = local + 1
      | otherwise = local

    go = \case
      LVar local -> LVar (weakenLocal local)
      LProjection local fields -> LProjection (weakenLocal local) fields
      LNeutral atom -> LNeutral (goAtom atom)
      LSucc level -> LSucc (go level)
      LAdd left right -> LAdd (go left) (go right)
      LMax left right -> LMax (go left) (go right)
      level -> level

    goAtom = \case
      NeutralLevelTermAtom _ term -> neutralLevelTermAtom (goTerm term)
      NeutralLevelSymbol identity arguments ->
        NeutralLevelSymbol identity (map go arguments)

    goTerm = \case
      NLTLocal local -> NLTLocal (weakenLocal local)
      NLTLocalDeclaration local levels ->
        NLTLocalDeclaration (weakenLocal local) (map go levels)
      NLTGlobal owner name levels -> NLTGlobal owner name (map go levels)
      NLTConstruct owner name levels arguments ->
        NLTConstruct owner name (map go levels)
          [(explicit, goTerm argument) | (explicit, argument) <- arguments]
      NLTApply explicit function argument ->
        NLTApply explicit (goTerm function) (goTerm argument)
      NLTProject field receiver -> NLTProject field (goTerm receiver)
      NLTLevel level -> NLTLevel (go level)
      NLTLiteral literal -> NLTLiteral literal
      NLTRecord fields -> NLTRecord [(field, goTerm value) | (field, value) <- fields]
      NLTIf condition thenBranch elseBranch ->
        NLTIf (goTerm condition) (goTerm thenBranch) (goTerm elseBranch)
      NLTUnsupported reason -> NLTUnsupported reason

-- | Solve the assignable fragment of a set of level inequalities. Rigid
-- ordering remains the exact Presburger judgment below. Metas receive the
-- deterministic least lower bound forced by constraints of the form
-- @lower <= ?u@; upper-only and structurally embedded metas remain residual
-- for boundary generalization/defaulting. Sorting and joining lower bounds
-- makes the result independent of constraint insertion order.
solveLevelConstraints :: [LevelConstraint] -> Either LevelSolveError LevelSolution
solveLevelConstraints constraints =
  solveLevelConstraintsFor
    (Set.fromList
      [ meta
      | constraint <- constraints
      , meta <- levelMetas (lcLhs constraint) ++ levelMetas (lcRhs constraint)
      ])
    constraints

-- | Solve only the selected metavariables. This is the declaration-boundary
-- operation required by §11.1.3: result-classifier metas have principal least
-- solutions, while parameter-position metas remain rigid until they are
-- generalized. A selected meta may be solved in terms of an unselected meta;
-- the latter is deliberately retained in the residual interface constraints.
solveLevelConstraintsFor :: Set.Set LevelMeta -> [LevelConstraint] -> Either LevelSolveError LevelSolution
solveLevelConstraintsFor targets constraints0 = do
  let lowerOnlyContradictions =
        [ constraint
        | constraint <- constraints
        , let lhsMetas = Set.fromList (levelMetas (lcLhs constraint))
              rhsMetas = levelMetas (lcRhs constraint)
              assumptionMetas =
                [ meta
                | (lower, upper) <- assumptionsList (lcAssumptions constraint)
                , meta <- levelMetas lower ++ levelMetas upper
                ]
        , not (Set.null (Set.intersection targets lhsMetas))
        , selectedMetasMonotoneIn targets (lcLhs constraint)
        , null rhsMetas
        , null assumptionMetas
        , let leastLhs =
                normalizeLevel
                  (foldr (\meta -> substituteLevelMeta meta LZero) (lcLhs constraint)
                    (Set.toList targets))
        , proveLevelLeq (lcAssumptions constraint) leastLhs (lcRhs constraint) == Disproved
        ]
      lowerEntries =
        [ (meta, lower, constraint)
        | constraint <- constraints
        , meta <- levelMetas (lcRhs constraint)
        , meta `Set.member` targets
        , proveLevelLeq (lcAssumptions constraint) (lcLhs constraint) (lcRhs constraint) /= Proved
        , Just lower <- [principalLowerBound meta constraint]
        ]
      directOccurs =
        [ (meta, lower, constraint)
        | constraint <- constraints
        , LMeta meta <- [lcRhs constraint]
        , meta `Set.member` targets
        , let lower = lcLhs constraint
        , meta `elem` levelMetas lower
        , Nothing <- [principalSelfLowerBound meta lower]
        ]
  case lowerOnlyContradictions of
    contradiction : _ -> Left (LevelConstraintDisproved contradiction)
    [] -> case directOccurs of
      (bad : _) -> Left (uncurry3 LevelMetaOccurs bad)
      [] -> do
        rawAssignments <- assignmentSccs lowerEntries
        case constraints of
          resourceSite : _
            | not (assignmentGraphWithinBudget rawAssignments) ->
                Left (LevelResourceLimit resourceSite solverNodeBudget)
          _ -> do
            let assignments = Map.map (substituteLevelMetas rawAssignments) rawAssignments
            finish assignments (map (zonkConstraint assignments) constraints)
  where
    constraints = sortOnKey constraints0

    -- Lower-bound equations form a finite max-semilattice dataflow graph.
    -- Solve each dependency SCC once instead of constructing recursive maps
    -- such as @u0 -> u1, u1 -> u0@ and relying on substitution's cycle guard.
    -- Internal dependencies are removable only in max positions; a successor
    -- or natural-addition edge around a cycle is genuine self-containment.
    assignmentSccs entries = do
      let targets = Set.fromList [meta | (meta, _, _) <- entries]
          byTarget =
            Map.fromListWith (++)
              [ (meta, [(lower, constraint)])
              | (meta, lower, constraint) <- entries
              ]
          graph =
            [ (meta, meta, filter (`Set.member` targets) (levelMetas lower))
            | (meta, lowers) <- Map.toAscList byTarget
            , let lower = foldr levelMax LZero (map fst lowers)
            ]
      fmap Map.unions (traverse (solveComponent byTarget) (stronglyConnComp graph))

    solveComponent byTarget component = do
      let members = case component of
            AcyclicSCC meta -> [meta]
            CyclicSCC metas -> sort metas
          memberSet = Set.fromList members
          entries =
            [ (meta, lower, constraint)
            | meta <- members
            , (lower, constraint) <- Map.findWithDefault [] meta byTarget
            ]
          reduced =
            [ (meta, lower, constraint, removeInternal memberSet lower)
            | (meta, lower, constraint) <- entries
            ]
      case [(meta, lower, constraint) | (meta, lower, constraint, Nothing) <- reduced] of
        ((meta, lower, constraint) : _) -> Left (LevelMetaOccurs meta lower constraint)
        [] ->
          let representative = minimum members
              base =
                foldr levelMax LZero
                  [ lower
                  | (_, _, _, Just lower) <- reduced
                  ]
           in Right $
                Map.fromList
                  ( (representative, base)
                      : [ (meta, LMeta representative)
                        | meta <- members
                        , meta /= representative
                        ]
                  )

    removeInternal members = fmap normalizeLevel . go
      where
        go level
          | all (`Set.notMember` members) (levelMetas level) = Just level
        go (LMeta meta) | meta `Set.member` members = Just LZero
        go (LMax a b) = levelMax <$> go a <*> go b
        go _ = Nothing

    finish assignments constraints' =
      foldl step (Right []) constraints' >>= \residualReversed ->
        pure (LevelSolution assignments (reverse residualReversed))
      where
        step acc c = do
          rest <- acc
          case proveLevelLeq (lcAssumptions c) (lcLhs c) (lcRhs c) of
            _ | normalizeLevel (lcLhs c) == normalizeLevel (lcRhs c) -> pure rest
            Proved -> pure rest
            Disproved -> Left (LevelConstraintDisproved c)
            Blocked _ -> pure (c : rest)
            ContradictoryAssumptions -> Left (LevelContradictoryAssumptions c)
            IndeterminateResourceLimit -> Left (LevelResourceLimit c solverNodeBudget)

    zonkConstraint = substituteLevelConstraintMetas

    sortOnKey =
      sortOn (\c -> (lcOrigin c, normalizeLevel (lcLhs c), normalizeLevel (lcRhs c)))
        . Map.elems
        . Map.fromListWith preferEarlier
        . map (\constraint -> (constraintJudgmentKey constraint, constraint))

    constraintJudgmentKey constraint =
      ( sort
          [ (normalizeLevel lhs, normalizeLevel rhs)
          | (lhs, rhs) <- assumptionsList (lcAssumptions constraint)
          ]
      , normalizeLevel (lcLhs constraint)
      , normalizeLevel (lcRhs constraint)
      )

    preferEarlier lhs rhs
      | lcIdentity lhs <= lcIdentity rhs = lhs
      | otherwise = rhs
    uncurry3 f (a, b, c) = f a b c

    -- The standard level constructors are monotone in their arguments. An
    -- opaque neutral term is not: even selected Monotone evidence does not
    -- make the function an order embedding, so @f ?u <= f p@ cannot be
    -- refuted by testing @?u = 0@. Keep such constraints in the portable
    -- outside-fragment path unless a future rule consumes stronger evidence.
    selectedMetasMonotoneIn selected = \case
      LSucc level -> selectedMetasMonotoneIn selected level
      LAdd left right ->
        selectedMetasMonotoneIn selected left
          && selectedMetasMonotoneIn selected right
      LMax left right ->
        selectedMetasMonotoneIn selected left
          && selectedMetasMonotoneIn selected right
      neutral@(LNeutral _) ->
        Set.null (Set.intersection selected (Set.fromList (levelMetas neutral)))
      _ -> True

    -- @max ?u lower <= ?u@ is not an occurs-check cycle: it is exactly the
    -- lower-bound constraint @lower <= ?u@ and has the same principal least
    -- solution. Only occurrences beneath max are eliminable this way; an
    -- occurrence beneath successor or natural addition is genuine recursive
    -- self-containment and remains an error.
    principalSelfLowerBound meta = fmap normalizeLevel . go
      where
        go level
          | meta `notElem` levelMetas level = Just level
        go (LMeta m) | m == meta = Just LZero
        go (LMax a b) = levelMax <$> go a <*> go b
        go _ = Nothing

    -- Derive the exact least value of one selected metavariable from a
    -- monotone right-hand context. Direct @lower <= ?u@ constraints retain
    -- symbolic rigid lower bounds. For an embedded occurrence, derive a value
    -- only when both the lower bound and every other part of the context are
    -- closed. This covers arbitrary nesting/repetition under natural addition,
    -- successor, and max without inventing a conditional expression that the
    -- level algebra cannot represent. Contexts containing another unresolved
    -- meta therefore remain residual, which is the required no-principal path
    -- for judgments such as @omega <= max ?u ?v@.
    principalLowerBound meta constraint =
      case cancelCommonAddition (lcLhs constraint) (lcRhs constraint) of
        (lower, LMeta rhsMeta)
          | rhsMeta == meta -> principalSelfLowerBound meta lower
        (lower, rhs) ->
          closedEmbeddedLeast meta lower rhs
            <|> rigidMaxLeast (lcAssumptions constraint) meta lower rhs

    -- The portable symbolic max rule does not require a closed ordinal.
    -- If the selected meta occurs only as max arms, erase those arms to ask
    -- whether the rigid remainder already covers the lower bound.  Otherwise
    -- the lower bound itself is the least expressible uniform assignment:
    -- @max lower remainder@ covers @lower@ for every rigid valuation.  Other
    -- metas keep the judgment residual so selected and unselected inference
    -- are never conflated.
    rigidMaxLeast assumptions meta lower rhs = do
      remainder <- eraseMaxArms rhs
      guard (meta `elem` levelMetas rhs)
      guard (null (levelMetas remainder))
      pure $
        case proveLevelLeq assumptions lower remainder of
          Proved -> LZero
          _ -> normalizeLevel lower
      where
        eraseMaxArms level
          | meta `notElem` levelMetas level = Just level
        eraseMaxArms (LMeta found)
          | found == meta = Just LZero
        eraseMaxArms (LMax left right) =
          levelMax <$> eraseMaxArms left <*> eraseMaxArms right
        eraseMaxArms _ = Nothing

    -- Constructor NF preserves additive multiplicity, so cancellation is an
    -- entailment/inference rule rather than a normalizer rewrite. Removing
    -- the multiset intersection is valid for natural (Hessenberg) addition
    -- and exposes the principal direct bound in judgments such as
    -- @p + 1 <= ?u + 1@ and @succ p <= succ ?u@.
    cancelCommonAddition lower upper =
      let lowerTerms = additiveTerms (normalizeLevel lower)
          upperTerms = additiveTerms (normalizeLevel upper)
          (lowerOnly, upperOnly) = cancelSorted lowerTerms upperTerms
       in (fromAdditiveTerms lowerOnly, fromAdditiveTerms upperOnly)

    additiveTerms = \case
      LAdd lhs rhs -> additiveTerms lhs ++ additiveTerms rhs
      LZero -> []
      level -> [level]

    cancelSorted left right = go (sort left) (sort right)
      where
        go [] ys = ([], ys)
        go xs [] = (xs, [])
        go xs@(x : xt) ys@(y : yt) = case compare x y of
          LT -> first (x :) (go xt ys)
          EQ -> go xt yt
          GT -> second (y :) (go xs yt)

    fromAdditiveTerms = \case
      [] -> LZero
      firstTerm : rest -> foldl levelAdd firstTerm rest

    first f (a, b) = (f a, b)
    second f (a, b) = (a, f b)

    closedEmbeddedLeast meta lower rhs = do
      lowerPair@(lowerCoefficient, lowerTail) <- closedLevel (normalizeLevel lower)
      let evaluate pair =
            closedLevel
              (substituteLevelMeta meta (fromClosedOrdinal pair) rhs)
          satisfies pair = maybe False (>= lowerPair) (evaluate pair)
          coefficientWorks coefficient = satisfies (coefficient, lowerTail)
      coefficient <- leastTrue 0 lowerCoefficient coefficientWorks
      tailValue <- leastTrue 0 lowerTail (\tail' -> satisfies (coefficient, tail'))
      pure (fromClosedOrdinal (coefficient, tailValue))

    -- Binary search the least satisfying natural. The caller establishes a
    -- monotone predicate and a satisfying upper bound; failure means the
    -- embedded context was not an exact solvable lower-bound shape.
    leastTrue lower upper predicate
      | lower > upper = Nothing
      | not (predicate upper) = Nothing
      | lower == upper = Just lower
      | otherwise =
          let middle = lower + (upper - lower) `div` 2
           in if predicate middle
                then leastTrue lower middle predicate
                else leastTrue (middle + 1) upper predicate

-- | Classify selected-meta inference using the five outcomes required by
-- §11.1.3. This API deliberately sits on top of the detailed solver so every
-- successful assignment has already been substituted through and every
-- original constraint has been rechecked. Non-principality is reported only
-- for the max-split shape with a concrete positive witness: assigning the
-- complete lower bound to either selected arm yields two incomparable minimal
-- solutions, so no pointwise least solution can exist.
inferPrincipalLevelsFor :: Set.Set LevelMeta -> [LevelConstraint] -> PrincipalInferenceOutcome
inferPrincipalLevelsFor targets constraints =
  case solveLevelConstraintsFor remainingTargets preparedConstraints of
    Left LevelResourceLimit {} -> OutsidePortableInferenceFragment
    Left _ -> Unsatisfiable
    Right solution
      | acceptsConditionalPrincipal leastCandidate -> SolvedPrincipal leastCandidate
      | Just witness <- checkedMaxSplitWitness leastCandidate -> NoPointwiseLeastSolution witness
      | any residualBlockedByUnselected (lsResidual solution) -> BlockedByUnselectedMetas
      | otherwise -> OutsidePortableInferenceFragment
      where
        solvedAssignments =
          Map.map (substituteLevelMetas combinedAssignments) combinedAssignments
        combinedAssignments = Map.union (lsAssignments solution) forcedAssignments
        -- Zero is the pointwise least universe. Selected metas which received
        -- no forced lower bound therefore have a principal value exactly when
        -- substituting zero makes the complete original system hold. This
        -- includes genuinely unconstrained metas and upper-only occurrences;
        -- it is a checked candidate, not declaration-boundary defaulting.
        leastCandidate =
          normalizeAssignments
            ( Map.union
                solvedAssignments
                (Map.fromSet (const LZero) (Set.difference targets (Map.keysSet solvedAssignments)))
            )
        residualBlockedByUnselected constraint =
          let metas = constraintMetas constraint
           in not (Set.null (Set.intersection targets metas))
                && not (Set.null (Set.difference metas targets))
        checkedMaxSplitWitness base = firstJust (map (maxSplitWitness base) (lsResidual solution))
  where
    firstJust [] = Nothing
    firstJust (Just value : _) = Just value
    firstJust (Nothing : rest) = firstJust rest

    constraintMetas constraint =
      Set.fromList
        ( levelMetas (lcLhs constraint)
            ++ levelMetas (lcRhs constraint)
            ++ concatMap
              (\(lower, upper) -> levelMetas lower ++ levelMetas upper)
              (assumptionsList (lcAssumptions constraint))
        )

    selectedConstraints =
      [ constraint
      | constraint <- constraints
      , let metas = constraintMetas constraint
      , not (Set.null (Set.intersection targets metas))
      ]
    forcedZeroAssignments =
      Map.fromSet (const LZero) . Set.fromList $
        [ meta
        | constraint <- constraints
        , (lower, upper) <-
            (lcLhs constraint, lcRhs constraint) : assumptionsList (lcAssumptions constraint)
        , normalizeLevel upper == LZero
        , LMeta meta <- [normalizeLevel lower]
        , meta `Set.member` targets
        ]
    forcedAliasAssignments =
      Map.fromList
        [ (meta, LMeta representative)
        | component <- stronglyConnComp equalityGraph
        , let members = case component of
                AcyclicSCC member -> [member]
                CyclicSCC cyclicMembers -> sort cyclicMembers
        , let unselected = filter (`Set.notMember` targets) members
        , representative <- take 1 unselected
        , meta <- members
        , meta `Set.member` targets
        ]
    forcedAssignments = Map.union forcedZeroAssignments forcedAliasAssignments
    remainingTargets = Set.difference targets (Map.keysSet forcedAssignments)
    preparedConstraints = map (zonkConstraint forcedAssignments) constraints

    -- An unconditional atomic equality between a selected occurrence meta and
    -- an unselected declaration meta fixes the occurrence to that rigid
    -- identity. Other lower bounds then become selected-free declaration
    -- obligations after substitution; they are retained for generated proof
    -- binders instead of being joined into a different occurrence value.
    equalityEdges =
      [ (lower, upper)
      | constraint <- constraints
      , null (assumptionsList (lcAssumptions constraint))
      , LMeta lower <- [normalizeLevel (lcLhs constraint)]
      , LMeta upper <- [normalizeLevel (lcRhs constraint)]
      ]
    equalityVertices =
      Set.toAscList (Set.fromList (concat [[lower, upper] | (lower, upper) <- equalityEdges]))
    equalityGraph =
      [ (meta, meta, [upper | (lower, upper) <- equalityEdges, lower == meta])
      | meta <- equalityVertices
      ]

    zonkConstraint = substituteLevelConstraintMetas

    substituteAssumptions assignments =
      foldr
        (\(lower, upper) ->
           insertAssumption
             (substituteLevelMetas assignments lower)
             (substituteLevelMetas assignments upper))
        emptyAssumptions
        . assumptionsList

    normalizeAssignments assignments =
      Map.map (normalizeLevel . substituteLevelMetas assignments) assignments

    satisfiesAll assignments =
      all
        (\candidate ->
           proveLevelLeq
             (substituteAssumptions assignments (lcAssumptions candidate))
             (substituteLevelMetas assignments (lcLhs candidate))
             (substituteLevelMetas assignments (lcRhs candidate))
             == Proved)
        selectedConstraints

    acceptsConditionalPrincipal assignments =
      all accepts selectedConstraints
      where
        accepts candidate =
          let assumptions = substituteAssumptions assignments (lcAssumptions candidate)
              lower = substituteLevelMetas assignments (lcLhs candidate)
              upper = substituteLevelMetas assignments (lcRhs candidate)
           in case proveLevelLeq assumptions lower upper of
                Proved -> True
                Disproved -> False
                Blocked residualMetas ->
                  Set.null
                    (Set.intersection targets (Set.fromList residualMetas))
                ContradictoryAssumptions -> False
                IndeterminateResourceLimit -> False

    maxSplitWitness base constraint =
      case (closedLevel (normalizeLevel (lcLhs constraint)), normalizeLevel (lcRhs constraint)) of
        (Just lower, LMax (LMeta left) (LMeta right))
          | left /= right
          , left `Set.member` targets
          , right `Set.member` targets
          , lower > (0, 0) ->
              let bound = fromClosedOrdinal lower
                  leftSolution = Map.union (Map.fromList [(left, bound), (right, LZero)]) base
                  rightSolution = Map.union (Map.fromList [(left, LZero), (right, bound)]) base
               in if satisfiesAll leftSolution
                    && satisfiesAll rightSolution
                    && not (pointwiseLeq leftSolution rightSolution)
                    && not (pointwiseLeq rightSolution leftSolution)
                    then Just (PrincipalNonLeastWitness leftSolution rightSolution)
                    else Nothing
        _ -> Nothing

    pointwiseLeq left right =
      all
        (\meta ->
          proveLevelLeq
            emptyAssumptions
            (Map.findWithDefault LZero meta left)
            (Map.findWithDefault LZero meta right)
            == Proved)
        (Set.toList targets)

-- | Decide a rigid inequality under lexically scoped assumptions. Metas are
-- never guessed here: the caller receives 'Blocked' and owns solving or
-- boundary generalization. Closed levels take a constant-time fast path. Open
-- levels are translated exactly to guarded quantifier-free Presburger
-- arithmetic over the @(omega coefficient, finite tail)@ representation; the
-- inequality is proved precisely when assumptions plus its negation are
-- unsatisfiable.
proveLevelLeq :: Assumptions -> Level -> Level -> SolveResult
proveLevelLeq assumps lhs0 rhs0
  | ContradictoryAssumptions <- assumptionResult = ContradictoryAssumptions
  | IndeterminateResourceLimit <- assumptionResult = IndeterminateResourceLimit
  | structurallyLeq lhs rhs = Proved
  | LMax left right <- lhs =
      conjunction
        (proveLevelLeq assumps left rhs)
        (proveLevelLeq assumps right rhs)
  | not (null allMetas) = Blocked allMetas
  | Just ordering <- compareClosedLevel lhs rhs =
      if ordering /= GT then Proved else Disproved
  | assumptionReachable relevantAssumptions lhs rhs = Proved
  | Just result <- atomicRigidOrdering relevantAssumptions lhs rhs = result
  | not
      ( levelForestWithinBudget
          (lhs : rhs : concatMap (\(lower, upper) -> [lower, upper])
            (assumptionsList relevantAssumptions))
      ) = IndeterminateResourceLimit
  | otherwise =
      case presburgerSatisfiability relevantAssumptions (Just (lhs, rhs)) of
        Satisfiable -> Disproved
        UnsatisfiableFormula -> Proved
        SatisfiabilityResourceLimit -> IndeterminateResourceLimit
  where
    lhs = normalizeLevel lhs0
    rhs = normalizeLevel rhs0
    relevantAssumptions = restrictAssumptionsTo lhs rhs assumps
    queryMetas =
      sort . nub $
        levelMetas lhs
          ++ levelMetas rhs
    assumptionMetas = case assumptionResult of
      Blocked metas -> metas
      _ -> []
    allMetas = sort . nub $ assumptionMetas ++ queryMetas
    assumptionResult = classifyAssumptions assumps

    conjunction ContradictoryAssumptions _ = ContradictoryAssumptions
    conjunction _ ContradictoryAssumptions = ContradictoryAssumptions
    conjunction Proved Proved = Proved
    conjunction Disproved _ = Disproved
    conjunction _ Disproved = Disproved
    conjunction IndeterminateResourceLimit _ = IndeterminateResourceLimit
    conjunction _ IndeterminateResourceLimit = IndeterminateResourceLimit
    conjunction (Blocked lhsMetas) (Blocked rhsMetas) = Blocked (sort . nub $ lhsMetas ++ rhsMetas)
    conjunction (Blocked blocked) Proved = Blocked blocked
    conjunction Proved (Blocked blocked) = Blocked blocked

-- | Decide rigid semantic equality as the normative pair of inequalities.
-- Constructor normalization is only a deterministic syntax normal form; it
-- intentionally does not encode distributivity, dominance, or every other
-- equality of the level algebra.
proveLevelEq :: Assumptions -> Level -> Level -> SolveResult
proveLevelEq assumptions left right =
  combine (proveLevelLeq assumptions left right) (proveLevelLeq assumptions right left)
  where
    combine ContradictoryAssumptions _ = ContradictoryAssumptions
    combine _ ContradictoryAssumptions = ContradictoryAssumptions
    combine Proved Proved = Proved
    combine Disproved _ = Disproved
    combine _ Disproved = Disproved
    combine IndeterminateResourceLimit _ = IndeterminateResourceLimit
    combine _ IndeterminateResourceLimit = IndeterminateResourceLimit
    combine (Blocked leftMetas) (Blocked rightMetas) =
      Blocked (sort . nub $ leftMetas ++ rightMetas)
    combine (Blocked metas) Proved = Blocked metas
    combine Proved (Blocked metas) = Blocked metas

-- | Assumption components disconnected from the queried rigid identities
-- cannot affect that inequality. Assumption sets are checked for consistency
-- when they enter scope, so retaining the complete undirected component of
-- every queried identity is an exact logical slice, not a heuristic. Closed
-- assumptions are retained defensively; they carry no graph identity and are
-- discharged by the ordinary closed-level judgment.
restrictAssumptionsTo :: Level -> Level -> Assumptions -> Assumptions
restrictAssumptionsTo lhs rhs original@(Assumptions assumptions)
  | Set.null seeds = original
  | otherwise = Assumptions (filter relevant assumptions)
  where
    seeds = Set.fromList (rigidLevelIds lhs ++ rigidLevelIds rhs)
    edgeIds (lower, upper) =
      Set.fromList (rigidLevelIds lower ++ rigidLevelIds upper)
    components = map (\edge -> (edge, edgeIds edge)) assumptions
    reachable = close seeds
    close current =
      let next =
            Set.unions
              ( current
                  : [ identities
                    | (_, identities) <- components
                    , not (Set.null (Set.intersection current identities))
                    ]
              )
       in if next == current then current else close next
    relevant edge =
      let identities = edgeIds edge
       in Set.null identities || not (Set.null (Set.intersection reachable identities))

-- | Scoped assumptions are themselves proof evidence, including when their
-- endpoints are compound natural-sum expressions. Reachability over exact
-- normalized endpoints is a sound (but deliberately incomplete) implication
-- fragment and avoids translating common ceiling chains to Presburger.
assumptionReachable :: Assumptions -> Level -> Level -> Bool
assumptionReachable (Assumptions assumptions) source target =
  go Set.empty [source]
  where
    edges =
      nub
        [ (normalizeLevel lower, normalizeLevel upper)
        | assumption <- assumptions
        , (lower, upper) <- expandLeftMaxAssumption assumption
        ]

    go _ [] = False
    go seen (current : rest)
      | current == target = True
      | current `Set.member` seen = go seen rest
      | otherwise =
          let next = [upper | (lower, upper) <- edges, lower == current]
           in go (Set.insert current seen) (next ++ rest)

-- | Atomic rigid inequalities form a directed preorder. Reachability is the
-- complete implication judgment for that fragment; when no path exists, a
-- topological valuation gives a countermodel. This avoids invoking the
-- Presburger engine for the overwhelmingly common hidden-telescope identity
-- comparisons while leaving every compound level expression to it.
atomicRigidOrdering :: Assumptions -> Level -> Level -> Maybe SolveResult
atomicRigidOrdering (Assumptions assumptions) lhs rhs = do
  lhsId <- atomicRigidLevel lhs
  rhsIds <- atomicRigidUpper rhs
  edges <- traverse rigidEdge relevantAssumptions
  pure $ if any (reachable edges lhsId) rhsIds then Proved else Disproved
  where
    relevantAssumptions =
      [ edge
      | edge@(lower, upper) <- concatMap expandLeftMaxAssumption assumptions
      , not (structurallyLeq lower upper)
      ]

    rigidEdge (lower, upper) = (,) <$> atomicRigidLevel lower <*> atomicRigidLevel upper

    atomicRigidUpper (LMax left right) =
      (++) <$> atomicRigidUpper left <*> atomicRigidUpper right
    atomicRigidUpper level = pure <$> atomicRigidLevel level

    reachable edges source target = go Set.empty [source]
      where
        go _ [] = False
        go seen (current : rest)
          | current == target = True
          | current `Set.member` seen = go seen rest
          | otherwise =
              let next = [upper | (lower, upper) <- edges, lower == current]
               in go (Set.insert current seen) (next ++ rest)

-- | @max(a,b) <= c@ is definitionally equivalent to the conjunction of its
-- two arm bounds. Expanding this shape in scoped assumptions exposes the
-- atomic preorder without making the incomplete dual transformation on a
-- right-side maximum.
expandLeftMaxAssumption :: (Level, Level) -> [(Level, Level)]
expandLeftMaxAssumption (LMax left right, upper) =
  expandLeftMaxAssumption (left, upper) ++ expandLeftMaxAssumption (right, upper)
expandLeftMaxAssumption edge = [edge]

-- These lattice laws are valid independently of the values eventually
-- assigned to universe metavariables.  Apply them before the general meta
-- blocker so constraints produced by formation, such as @?u <= max ?u ?v@,
-- do not survive to declaration defaulting as spurious ambiguity.  This is a
-- proof-only simplifier: failure means "not established structurally" and
-- falls through to the complete rigid solver or the ordinary meta solver.
structurallyLeq :: Level -> Level -> Bool
structurallyLeq lhs rhs
  | lhs == rhs = True
structurallyLeq LZero _ = True
structurallyLeq (LMax a b) rhs = structurallyLeq a rhs && structurallyLeq b rhs
structurallyLeq lhs (LMax a b) = structurallyLeq lhs a || structurallyLeq lhs b
structurallyLeq _ _ = False

data RigidLevelId
  = RigidZero
  | RigidLocal !Int
  | RigidParam !Int
  | RigidField !Int !Text
  | RigidProjection !Int ![Text]
  | RigidNeutral !NeutralLevelAtom
  deriving stock (Eq, Ord, Show)

data SymbolicLevel = SymbolicLevel
  { soCoefficient :: !SAT.Expr
  , soTail :: !SAT.Expr
  }

-- | Is there a non-negative level valuation satisfying all assumptions and,
-- when supplied, refuting the queried inequality? 'Data.Integer.SAT' is the
-- maintained pure Omega-style QF integer procedure vendored under its BSD
-- license; there is no external solver or bounded model search here.
data SatisfiabilityResult
  = Satisfiable
  | UnsatisfiableFormula
  | SatisfiabilityResourceLimit

presburgerSatisfiability :: Assumptions -> Maybe (Level, Level) -> SatisfiabilityResult
presburgerSatisfiability (Assumptions edges0) refuted
  | not (levelForestWithinBudget inputLevels) = SatisfiabilityResourceLimit
  | zeroValuationSatisfies edges0 refuted = Satisfiable
  | otherwise =
      case SAT.checkSat (SAT.assert formula SAT.noProps) of
        Nothing -> UnsatisfiableFormula
        Just _ -> Satisfiable
  where
    inputLevels =
      concatMap (\(lower, upper) -> [lower, upper]) edges0
        ++ maybe [] (\(lower, upper) -> [lower, upper]) refuted
    normalizedEdges =
      nub
        [ (normalizeLevel a, normalizeLevel b)
        | edge <- edges0
        , (a, b) <- expandLeftMaxAssumption edge
        ]
    representatives = rigidEqualityRepresentatives normalizedEdges
    canonicalize = canonicalizeRigidLevels representatives
    edges =
      nub
        [ (a', b')
        | (a, b) <- normalizedEdges
        , let a' = canonicalize a
              b' = canonicalize b
        , a' /= b'
        ]
    refuted' = fmap (\(a, b) -> (canonicalize a, canonicalize b)) refuted
    allLevels =
      concatMap (\(a, b) -> [a, b]) edges
        ++ maybe [] (\(a, b) -> [a, b]) refuted'
    rigidIds = sort . nub $ concatMap rigidLevelIds allLevels
    symbols = Map.fromList (zip rigidIds [0 :: Int ..])
    nonNegative =
      foldr satAnd SAT.PTrue
        [ SAT.K 0 SAT.:<= SAT.Var (SAT.toName index)
        | slot <- [0 .. length rigidIds - 1]
        , index <- [2 * slot, 2 * slot + 1]
        ]
    assumed =
      foldr satAnd SAT.PTrue
        [levelLe (symbolic symbols a) (symbolic symbols b) | (a, b) <- edges]
    contradicted = case refuted' of
      Nothing -> SAT.PTrue
      Just (a, b) -> SAT.Not (levelLe (symbolic symbols a) (symbolic symbols b))
    formula = nonNegative `satAnd` assumed `satAnd` contradicted

-- | The all-zero rigid valuation is a cheap exact witness, not a heuristic.
-- Natural universe variables range over non-negative levels, so replacing
-- every rigid identity by zero yields one valid valuation. If it satisfies
-- the assumptions (and, for a refutation query, falsifies the inequality),
-- satisfiability is established without entering the complete SAT fallback.
zeroValuationSatisfies :: [(Level, Level)] -> Maybe (Level, Level) -> Bool
zeroValuationSatisfies assumptions refuted =
  all holds (concatMap expandLeftMaxAssumption assumptions)
    && maybe True (not . holds) refuted
  where
    holds (lower, upper) =
      compareClosedLevel (zeroRigidLevel lower) (zeroRigidLevel upper)
        `elem` [Just LT, Just EQ]

zeroRigidLevel :: Level -> Level
zeroRigidLevel = normalizeLevel . go
  where
    go = \case
      LVar _ -> LZero
      LParam _ -> LZero
      LField _ _ -> LZero
      LProjection _ _ -> LZero
      LNeutral _ -> LZero
      LMeta meta -> LMeta meta
      LSucc level -> LSucc (go level)
      LAdd lhs rhs -> LAdd (go lhs) (go rhs)
      LMax lhs rhs -> LMax (go lhs) (go rhs)
      level -> level

-- | Mutual ordering of two atomic rigid universe identities is equality by
-- antisymmetry. Collapse those identities before producing the Presburger
-- formula: keeping each equality as two ordinal disjunctions causes
-- exponential branching for declarations with many independently-floated
-- annotations. Non-atomic equalities remain ordinary solver constraints.
rigidEqualityRepresentatives :: [(Level, Level)] -> Map RigidLevelId RigidLevelId
rigidEqualityRepresentatives edges =
  Map.fromList
    [ (member, minimum members)
    | component <- stronglyConnComp graph
    , let members = case component of
            AcyclicSCC ident -> [ident]
            CyclicSCC idents -> idents
    , member <- members
    ]
  where
    edgeSet = Set.fromList edges
    equalities =
      [ (lhsId, rhsId)
      | (lhs, rhs) <- edges
      , (rhs, lhs) `Set.member` edgeSet
      , Just lhsId <- [atomicRigidLevel lhs]
      , Just rhsId <- [atomicRigidLevel rhs]
      ]
    identities = sort . nub $ concat [[lhs, rhs] | (lhs, rhs) <- equalities]
    graph =
      [ (ident, ident, [rhs | (lhs, rhs) <- equalities, lhs == ident])
      | ident <- identities
      ]

canonicalizeRigidLevels :: Map RigidLevelId RigidLevelId -> Level -> Level
canonicalizeRigidLevels representatives = normalizeLevel . go
  where
    go = \case
      LVar ident -> fromRigid (RigidLocal ident)
      LParam ident -> fromRigid (RigidParam ident)
      LField index field -> fromRigid (RigidField index field)
      LProjection root path -> fromRigid (RigidProjection root path)
      LNeutral atom ->
        fromRigid (RigidNeutral (mapNeutralLevelAtomLevels go atom))
      LSucc level -> LSucc (go level)
      LAdd lhs rhs -> LAdd (go lhs) (go rhs)
      LMax lhs rhs -> LMax (go lhs) (go rhs)
      level -> level

    fromRigid ident =
      case Map.findWithDefault ident ident representatives of
        RigidZero -> LZero
        RigidLocal index -> LVar index
        RigidParam index -> LParam index
        RigidField index field -> LField index field
        RigidProjection root path -> LProjection root path
        RigidNeutral atom -> LNeutral atom

atomicRigidLevel :: Level -> Maybe RigidLevelId
atomicRigidLevel = \case
  LZero -> Just RigidZero
  LVar ident -> Just (RigidLocal ident)
  LParam ident -> Just (RigidParam ident)
  LField index field -> Just (RigidField index field)
  LProjection root path -> Just (RigidProjection root path)
  neutral@(LNeutral atom)
    | null (levelMetas neutral) -> Just (RigidNeutral (mapNeutralLevelAtomLevels normalizeLevel atom))
  _ -> Nothing

satAnd :: SAT.Prop -> SAT.Prop -> SAT.Prop
satAnd = (SAT.:&&)

satOr :: SAT.Prop -> SAT.Prop -> SAT.Prop
satOr = (SAT.:||)

levelLe :: SymbolicLevel -> SymbolicLevel -> SAT.Prop
levelLe a b =
  (soCoefficient a SAT.:< soCoefficient b)
    `satOr` ((soCoefficient a SAT.:== soCoefficient b) `satAnd` (soTail a SAT.:<= soTail b))

symbolic :: Map RigidLevelId Int -> Level -> SymbolicLevel
symbolic symbols = go . normalizeLevel
  where
    go = \case
      LZero -> SymbolicLevel (SAT.K 0) (SAT.K 0)
      LFinite n -> SymbolicLevel (SAT.K 0) (SAT.K n)
      LOmega -> SymbolicLevel (SAT.K 1) (SAT.K 0)
      LVar v -> variable (RigidLocal v)
      LParam p -> variable (RigidParam p)
      LField i f -> variable (RigidField i f)
      LProjection root path -> variable (RigidProjection root path)
      neutral@(LNeutral atom)
        | null (levelMetas neutral) -> variable (RigidNeutral (mapNeutralLevelAtomLevels normalizeLevel atom))
        | otherwise -> error "symbolic: unresolved universe metavariable below neutral term"
      LMeta _ -> error "symbolic: unresolved universe metavariable"
      LSucc a ->
        let SymbolicLevel c n = go a
         in SymbolicLevel c (n SAT.:+ SAT.K 1)
      LAdd a b ->
        let SymbolicLevel ac an = go a
            SymbolicLevel bc bn = go b
         in SymbolicLevel (ac SAT.:+ bc) (an SAT.:+ bn)
      LMax a b ->
        let sa = go a
            sb = go b
            aLeB = levelLe sa sb
         in SymbolicLevel
              (SAT.If aLeB (soCoefficient sb) (soCoefficient sa))
              (SAT.If aLeB (soTail sb) (soTail sa))

    variable ident =
      case Map.lookup ident symbols of
        Nothing -> error "symbolic: missing rigid universe identity"
        Just slot ->
          SymbolicLevel
            (SAT.Var (SAT.toName (2 * slot)))
            (SAT.Var (SAT.toName (2 * slot + 1)))

rigidLevelIds :: Level -> [RigidLevelId]
rigidLevelIds = \case
  LVar v -> [RigidLocal v]
  LParam p -> [RigidParam p]
  LField i f -> [RigidField i f]
  LProjection root path -> [RigidProjection root path]
  neutral@(LNeutral atom)
    | null (levelMetas neutral) -> [RigidNeutral (mapNeutralLevelAtomLevels normalizeLevel atom)]
  LSucc a -> rigidLevelIds a
  LAdd a b -> rigidLevelIds a ++ rigidLevelIds b
  LMax a b -> rigidLevelIds a ++ rigidLevelIds b
  _ -> []

renderLevel :: Level -> Text
renderLevel = go . normalizeLevel
  where
    go = \case
      LZero -> "0"
      LFinite n -> T.pack (show n)
      LOmega -> "ω"
      LSucc a -> "succ " <> atom a
      LAdd a b -> atom a <> " + " <> atom b
      LMax a b -> "max " <> atom a <> " " <> atom b
      LVar v -> "u" <> T.pack (show v)
      LField _ f -> "this." <> f
      LProjection root path ->
        "u" <> T.pack (show root) <> "." <> T.intercalate "." path
      LNeutral atom -> renderNeutralAtom atom
      LMeta m -> "?u" <> T.pack (show m)
      LParam p -> "^u#" <> T.pack (show p)
    atom x@LAdd {} = "(" <> go x <> ")"
    atom x@LMax {} = "(" <> go x <> ")"
    atom x = go x

    renderNeutralAtom = \case
      NeutralLevelTermAtom digest _ -> "neutral#" <> digest
      NeutralLevelSymbol identity arguments ->
        identity <> if null arguments then "" else "[" <> T.intercalate ", " (map go arguments) <> "]"
