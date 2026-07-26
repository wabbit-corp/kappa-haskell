# Implemented universe-level normal forms, solving, and certificates

Status: implementation audit for specification backport  
Snapshot date: 2026-07-20  
Scope: universe levels below omega², natural/Hessenberg addition, lexicographic ordering, maximum, successor, metavariable inference, Core evidence, and KCoreText certificates

## Executive conclusion

The implementation has made a clear semantic choice, but it has not made one single normal form serve every purpose.

There are three different mechanisms:

1. A deterministic constructor normal form is used for storage, comparison fast paths, rendering, and some equality checks. It flattens and sorts addition, folds closed constants, flattens and deduplicates maximum, and rewrites successor as addition by one. It is an AC normal form for addition and an ACI normal form for maximum. It is not a complete semantic normal form for open expressions.
2. Rigid open inequalities are decided exactly by translating every level to a pair of quantifier-free Presburger expressions representing omega coefficient and finite tail. Maximum becomes a guarded conditional over lexicographic comparison. Entailment is tested by asking whether the assumptions together with the negation of the conclusion are satisfiable.
3. Assignable metavariables are handled by a separate lower-bound solver. It computes deterministic least assignments for a useful, explicitly described fragment, including direct lower bounds, maximum-only cycles, and closed embedded contexts. It is not a complete principal-solution algorithm for all constraints for which an expressible least solution exists.

The certificate story is likewise split:

- Internal Core evidence records normalized endpoints and the subset of assumptions needed to replay an inequality. Validation reruns the semantic solver. This is independently replayable if that solver is normative, but it is not a proof-producing arithmetic certificate.
- KCoreText exposes a small structural proof language. Its verifier is precise for the rules it has, but the language is not complete for the same fragment as the semantic solver.
- The KCoreText certificate generator tries to reconstruct a small structural proof from internal solver evidence. It can therefore fail to serialize some inequalities already established by the complete rigid solver.
- The special closed proof invokes the solver, but only for an entire certificate with no universe parameters and no assumptions. It cannot be nested as an arithmetic lemma.

Consequently, the implementation has already decided the denotational semantics and the rigid decision procedure. It has not yet joined that decision procedure to the portable certificate language, and its principal-inference claim must be narrowed or the inference algorithm strengthened.

The best specification backport is a hybrid contract:

- normatively define the current deterministic constructor normal form;
- normatively define pair semantics and Presburger entailment as the semantic equality and ordering procedure;
- add a generic arithmetic proof node whose verifier performs that normative entailment check, while retaining the small structural rules as compact conveniences;
- specify principal least solutions only for the actual assignable fragment, unless a complete symbolic optimization procedure is added;
- require the KCoreText canonicalizer to normalize level expressions enough that AC-equivalent input has one canonical serialization.

## 1. What is already decided

| Question | Implemented answer | Specification consequence |
|---|---|---|
| Meaning of a closed level | A pair of naturals: omega coefficient and finite tail | This can be made normative directly |
| Meaning of addition | Componentwise addition of the pair | This is natural/Hessenberg addition below omega² |
| Meaning of ordering | Lexicographic ordering of the pair | This can be made normative directly |
| Meaning of maximum | Lexicographic maximum of the pair | This can be made normative directly |
| Meaning of successor | Add one to the finite tail | The equation succ x = x + 1 is implemented |
| Stored open normal form | Flattened and sorted addition; flattened, sorted, deduplicated maximum; folded closed constants | This is deterministic syntax, not full semantic canonicalization |
| Exact rigid inequality | QF Presburger satisfiability over pair-valued rigid atoms | This is the real completeness mechanism |
| Exact rigid equality | In the main checker, mutual inequality; in several other paths, normalized syntax equality | The spec should choose semantic equality and retain syntax equality only as a fast path |
| Scoped strict constraints | Stored internally as succ lhs <= rhs | The small proof tree has no corresponding conversion rules |
| Least metavariable solution | Lower-bound join plus several special embedded cases | Principal only for an assignable fragment |
| Internal Core evidence | Endpoints plus minimized assumption dependencies, verified by solver replay | Checkable by recomputation, not a proof trace |
| Portable KCoreText certificate | Small structural derivation language | Incomplete relative to the semantic solver |
| Canonical KCoreText levels | Alpha-renaming only; no AC normalization pass | Equivalent written levels can retain distinct canonical text and hashes |

One practical caveat matters for backporting: the audited implementation is present in a working tree that contains uncommitted universe-related additions and modifications. It should be treated as the current implementation candidate, not as proof that the same behavior is already present in a released or clean baseline.

## 2. Semantic domain

### 2.1 Level syntax

The implementation distinguishes closed constructors, rigid symbolic identities, and assignable metavariables:

~~~haskell
type LevelMeta = Int

data Level
  = LZero
  | LFinite !Integer
  | LOmega
  | LSucc !Level
  | LAdd !Level !Level
  | LMax !Level !Level
  | LVar !Int
  | LParam !Int
  | LField !Int !Text
  | LProjection !Int ![Text]
  | LMeta !LevelMeta
  deriving stock (Eq, Ord, Show)
~~~

The symbolic atoms are intentionally not interchangeable:

- LVar identifies a local level-valued binder.
- LParam identifies a hidden declaration-universe parameter.
- LField identifies a dependent-record field in a particular scope.
- LProjection identifies a projection path rooted at a local term binder.
- LMeta is an inference variable and is never treated as universally quantified by the rigid decision procedure.

This distinction is semantically important. Two fields with the same label but different owning scopes are different rigid identities. A projection identity includes both its root and its resolved path.

LFinite is an internal compact representation for repeated finite successor. It is not a new source-language operation.

### 2.2 Closed pair interpretation

A closed level is interpreted as omega times a natural coefficient plus a natural finite tail:

~~~haskell
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
  LMeta _ -> Nothing
~~~

Because ordinary pair comparison is lexicographic, the closed semantics are:

- zero = (0, 0);
- finite n = (0, n);
- omega = (1, 0);
- succ(c, n) = (c, n + 1);
- (c₁, n₁) + (c₂, n₂) = (c₁ + c₂, n₁ + n₂);
- max is lexicographic maximum;
- (c₁, n₁) ≤ (c₂, n₂) exactly when c₁ < c₂, or c₁ = c₂ and n₁ ≤ n₂.

This makes addition commutative and associative. It is the natural/Hessenberg sum restricted below omega², not ordinal addition. In particular:

- 1 + omega = omega + 1;
- omega + 1 is strictly above omega;
- omega + omega = omega times 2.

The representation function back from a pair is:

~~~haskell
fromClosedOrdinal :: (Integer, Integer) -> Level
fromClosedOrdinal (c, n)
  | c <= 0 = finiteLevel n
  | n <= 0 = omegaPart
  | otherwise = LAdd omegaPart (finiteLevel n)
  where
    omegaPart = foldr1 LAdd (replicate (fromInteger c) LOmega)
~~~

The implementation assumes nonnegative coefficients and tails throughout the public algebra. Negative finite input is collapsed to zero by the smart constructor:

~~~haskell
finiteLevel :: Integral n => n -> Level
finiteLevel n
  | n <= 0 = LZero
  | otherwise = LFinite (toInteger n)
~~~

A normative specification should say directly that coefficients and tails range over naturals. It should not expose this defensive behavior for negative internal input as a semantic equation unless negative level literals are actually part of the language.

## 3. The implemented constructor normal form

### 3.1 Exact algorithm

The complete normalization routine is short enough to state directly:

~~~haskell
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
      LMeta m -> LMeta m
      LSucc a -> canonicalAdd [go a, LFinite 1]
      LAdd a b ->
        canonicalAdd (flattenAdd (go a) <> flattenAdd (go b))
      LMax a b ->
        canonicalMax (flattenMax (go a) <> flattenMax (go b))

    flattenAdd = \case
      LAdd a b -> flattenAdd a <> flattenAdd b
      LZero -> []
      x -> [x]

    canonicalAdd xs =
      let (closed, open) = foldr collect ((0, 0), []) xs
          closedTerm = fromClosedOrdinal closed
          terms =
            sort
              (open <> [closedTerm | closedTerm /= LZero])
       in case terms of
            [] -> LZero
            [x] -> x
            x : rest -> foldl LAdd x rest

    collect x ((coefficient, remainder), open) =
      case closedLevel x of
        Just (c, n) ->
          ((coefficient + c, remainder + n), open)
        Nothing ->
          ((coefficient, remainder), x : open)

    flattenMax = \case
      LMax a b -> flattenMax a <> flattenMax b
      LZero -> Set.empty
      x -> Set.singleton x

    canonicalMax xs =
      case Set.toAscList xs of
        [] -> LZero
        [x] -> x
        x : rest -> foldl LMax x rest
~~~

### 3.2 Addition rules actually normalized

For addition, normalization:

- recursively normalizes every operand;
- rewrites successor to addition by one;
- flattens nested additions;
- removes zero;
- combines all closed summands by pair addition;
- reifies the combined closed summand;
- sorts every remaining term by the implementation's structural total order;
- retains duplicate open summands;
- rebuilds a fixed left-associated tree.

It therefore validates:

- x + 0 = x;
- 0 + x = x;
- x + y = y + x;
- (x + y) + z = x + (y + z);
- succ x = x + 1.

It does not validate idempotence of addition. The expression x + x retains two copies of x.

The sort order is inherited from the constructor declaration's structural ordering. That is deterministic inside this implementation, but it is not a suitable portable specification by itself. A portable spec must enumerate an explicit constructor rank and recursively define comparison of payloads. Otherwise independent implementations can satisfy AC normalization and still serialize different trees.

### 3.3 Maximum rules actually normalized

For maximum, normalization:

- recursively normalizes every operand;
- flattens nested maxima;
- removes zero;
- inserts all remaining arms into an ordered set;
- therefore sorts and deduplicates them;
- rebuilds a fixed left-associated tree.

It validates:

- max 0 x = x;
- max x 0 = x;
- max x y = max y x;
- max (max x y) z = max x (max y z);
- max x x = x.

The treatment of zero as an identity relies on every level being nonnegative.

### 3.4 Rules deliberately not normalized

The constructor normalizer does not distribute addition over maximum in either direction. It also does not implement general semantic dominance or absorption.

Examples that are semantically equal but need not have the same normalized tree include:

~~~text
max u (succ u)
succ u

u + max v w
max (u + v) (u + w)

max (u + 1) (u + omega)
u + omega
~~~

The rigid semantic solver can establish both inequalities for these examples, but the syntax normalizer does not collapse them.

This is why the implemented normal form is not accurately described as maximum of affine natural-sum expressions. Such a form would require distribution of addition across maximum and then removal of semantically dominated arms. The current implementation stores arbitrary nesting between addition and maximum after only local AC or ACI flattening.

### 3.5 Correct name for the implemented normal form

A precise name is:

> Recursive AC/ACI constructor normal form with closed-constant folding.

It is canonical for these syntactic equations:

- associativity, commutativity, and zero identity of addition;
- associativity, commutativity, idempotence, and zero identity of maximum;
- successor expansion;
- evaluation of wholly closed subexpressions.

It is not canonical for all semantic equalities in the pair algebra.

### 3.6 Required portable ordering

If this storage normal form is specified, a portable order must replace the language-derived constructor order. One possible order matching the current constructor sequence is:

~~~text
zero
< finite
< omega
< successor
< addition
< maximum
< local variable
< declaration parameter
< field
< projection
< metavariable
~~~

Payloads would then be compared lexicographically, using integer order for numeric identities and a specified code-point or byte order for canonical text and field paths. The exact order is not semantically significant, but it is serialization-significant and must be normative if hashes depend on it.

A cleaner spec may assign ranks only to constructors that survive normalization. Because successor does not survive and zero is omitted from nontrivial addition and maximum, the normalized grammar can be narrower than the raw grammar.

## 4. Exact rigid decision procedure

### 4.1 No semantic expression normal form is constructed

Open equality and ordering are not decided by reducing every expression to a unique maximum of affine forms. Instead, each rigid atom receives a symbolic pair and the whole expression becomes guarded QF Presburger arithmetic.

~~~haskell
data SymbolicLevel = SymbolicLevel
  { soCoefficient :: !SAT.Expr
  , soTail :: !SAT.Expr
  }
~~~

Every rigid identity receives two integer variables:

~~~haskell
variable ident =
  case Map.lookup ident symbols of
    Nothing -> error "missing rigid universe identity"
    Just slot ->
      SymbolicLevel
        (SAT.Var (SAT.toName (2 * slot)))
        (SAT.Var (SAT.toName (2 * slot + 1)))
~~~

Both variables are constrained to be nonnegative.

### 4.2 Lexicographic ordering

Pair ordering is translated exactly as:

~~~haskell
levelLe :: SymbolicLevel -> SymbolicLevel -> SAT.Prop
levelLe a b =
  (soCoefficient a SAT.:< soCoefficient b)
    `satOr`
      ( (soCoefficient a SAT.:== soCoefficient b)
          `satAnd`
        (soTail a SAT.:<= soTail b)
      )
~~~

### 4.3 Expression translation

~~~haskell
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
      LProjection root path ->
        variable (RigidProjection root path)
      LMeta _ ->
        error "unresolved universe metavariable"

      LSucc a ->
        let SymbolicLevel c n = go a
         in SymbolicLevel c (n SAT.:+ SAT.K 1)

      LAdd a b ->
        let SymbolicLevel ac an = go a
            SymbolicLevel bc bn = go b
         in SymbolicLevel
              (ac SAT.:+ bc)
              (an SAT.:+ bn)

      LMax a b ->
        let sa = go a
            sb = go b
            aLeB = levelLe sa sb
         in SymbolicLevel
              (SAT.If aLeB
                (soCoefficient sb)
                (soCoefficient sa))
              (SAT.If aLeB
                (soTail sb)
                (soTail sa))
~~~

Maximum is not algebraically distributed. It becomes a pair of conditionals selecting the lexicographically larger operand. The integer engine lowers conditionals to fresh variables guarded by the corresponding propositions.

### 4.4 Entailment query

For assumptions A and proposed inequality x ≤ y, the implementation asks whether this formula has a model:

~~~text
nonnegative-rigid-components
and translation(A)
and not(translation(x <= y))
~~~

If satisfiable, the inequality is disproved by a countermodel. If unsatisfiable, the inequality is proved.

The relevant formula construction is:

~~~haskell
nonNegative =
  foldr satAnd SAT.PTrue
    [ SAT.K 0 SAT.:<= SAT.Var (SAT.toName index)
    | slot <- [0 .. length rigidIds - 1]
    , index <- [2 * slot, 2 * slot + 1]
    ]

assumed =
  foldr satAnd SAT.PTrue
    [ levelLe (symbolic symbols a)
              (symbolic symbols b)
    | (a, b) <- edges
    ]

contradicted = case refuted of
  Nothing ->
    SAT.PTrue
  Just (a, b) ->
    SAT.Not
      (levelLe (symbolic symbols a)
               (symbolic symbols b))

formula =
  nonNegative `satAnd` assumed `satAnd` contradicted
~~~

No bounded enumeration is used by the production fallback. A finite bounded reference model exists in tests, but the actual judgment uses an exact integer procedure.

### 4.5 Fast paths

Several sound fast paths precede Presburger:

~~~haskell
proveLevelLeq assumps lhs0 rhs0
  | structurallyLeq lhs rhs =
      Proved

  | LMax left right <- lhs =
      conjunction
        (proveLevelLeq assumps left rhs)
        (proveLevelLeq assumps right rhs)

  | not (null metas) =
      Blocked metas

  | Just ordering <- compareClosedLevel lhs rhs =
      if ordering /= GT then Proved else Disproved

  | assumptionReachable
      relevantAssumptions lhs rhs =
      Proved

  | Just result <-
      atomicRigidOrdering relevantAssumptions lhs rhs =
      result

  | presburgerSatisfiable
      relevantAssumptions (Just (lhs, rhs)) =
      Disproved

  | otherwise =
      Proved
~~~

Their roles are:

1. elementary lattice relations, even in the presence of metas;
2. left-maximum elimination;
3. blocking rather than guessing unresolved metas;
4. constant-time closed comparison;
5. exact-endpoint assumption reachability;
6. graph reachability for the atomic rigid preorder;
7. exact arithmetic fallback.

The structural lattice fragment is:

~~~haskell
structurallyLeq :: Level -> Level -> Bool
structurallyLeq lhs rhs
  | lhs == rhs = True
structurallyLeq LZero _ = True
structurallyLeq (LMax a b) rhs =
  structurallyLeq a rhs && structurallyLeq b rhs
structurallyLeq lhs (LMax a b) =
  structurallyLeq lhs a || structurallyLeq lhs b
structurallyLeq _ _ = False
~~~

This contains the missing max-least principle at the solver level:

~~~text
a <= c    b <= c
----------------
max a b <= c
~~~

The gap is in the portable proof grammar and generator, not in inequality solving.

### 4.6 Assumptions and strictness

Assumptions are normalized endpoint pairs:

~~~haskell
newtype Assumptions =
  Assumptions [(Level, Level)]

insertAssumption lhs rhs (Assumptions xs) =
  Assumptions
    (nub
      ((normalizeLevel lhs, normalizeLevel rhs) : xs))
~~~

A strict external constraint is converted immediately to a non-strict successor bound:

~~~haskell
add assumptions (KConstraint strict lhs rhs) =
  case (toLevel lhs, toLevel rhs) of
    (Just lhs', Just rhs') ->
      insertAssumption
        (if strict then levelSucc lhs' else lhs')
        rhs'
        assumptions
    _ ->
      assumptions
~~~

Thus the semantic solver operates on ≤ only:

~~~text
x < y    iff    succ x <= y
~~~

A maximum on the left of an assumption is expanded conjunctively:

~~~haskell
expandLeftMaxAssumption
  :: (Level, Level)
  -> [(Level, Level)]
expandLeftMaxAssumption (LMax left right, upper) =
  expandLeftMaxAssumption (left, upper)
    ++ expandLeftMaxAssumption (right, upper)
expandLeftMaxAssumption edge =
  [edge]
~~~

The right-hand dual is deliberately not applied. From a ≤ max b c one cannot choose one arm uniformly.

Disconnected assumptions may be sliced away before solving. The slice retains the complete undirected identity component touching the query, plus closed assumptions. Assumption contexts are checked for consistency when they enter scope, so this slicing does not allow an unrelated contradiction to prove an arbitrary query.

### 4.7 Consistency and atomic equality

Consistency means existence of a nonnegative pair valuation satisfying every assumption. Contexts containing unresolved metas are rejected as inconsistent rather than guessed.

Atomic non-strict rigid edges have an immediate all-zero model. Compound or strict-derived constraints use arithmetic satisfiability. A strict self-cycle, represented by succ u ≤ u, is unsatisfiable.

Mutually ordered atomic identities are collapsed before constructing the arithmetic formula. If assumptions contain u ≤ v and v ≤ u, antisymmetry makes their pair values equal. This is a formula optimization, not an exposed certificate rule.

## 5. Equality of open expressions

There are currently two equality notions.

### 5.1 Constructor-normal equality

Some paths compare:

~~~haskell
normalizeLevel lhs == normalizeLevel rhs
~~~

The KCoreText helper does this when both inputs translate to solver levels:

~~~haskell
sameKLevel lhs rhs =
  case (toLevel lhs, toLevel rhs) of
    (Just lhs', Just rhs') ->
      normalizeLevel lhs' == normalizeLevel rhs'
    _ ->
      lhs == rhs
~~~

This recognizes the normalizer's AC or ACI equations but not every semantic identity.

### 5.2 Semantic equality

The main checker treats rigid semantic equality as mutual entailment:

~~~text
A proves x = y
exactly when
A proves x <= y
and A proves y <= x
~~~

This recognizes distribution, dominance, and other consequences of pair semantics even when normalized trees differ.

### 5.3 Required specification decision

The normative equality for solver-level open expressions should be:

~~~text
A entails x = y
iff
A entails x <= y and A entails y <= x
~~~

Constructor-normal equality should be described only as:

- a sufficient fast path;
- the equality used to identify one canonical stored syntax;
- not the complete semantic judgment.

Using constructor equality as normative open equality would contradict the exact decision behavior.

## 6. Least-solution computation

### 6.1 Explicit fragment boundary

The solver describes itself as handling an assignable fragment:

~~~haskell
-- Solve the assignable fragment of a set of level inequalities.
-- Rigid ordering remains the exact Presburger judgment.
-- Metas receive the deterministic least lower bound forced by
-- constraints of the form lower <= ?u.
-- Upper-only and structurally embedded metas remain residual
-- for boundary generalization/defaulting.
~~~

This qualification is essential. Rigid entailment is complete; metavariable inference is not complete over the same full expression language.

### 6.2 Direct lower bounds

For a selected meta m, a direct constraint lower ≤ m contributes lower. Multiple contributions are joined with maximum. Therefore:

~~~text
1 <= ?u
3 <= ?u
~~~

has the least solution:

~~~text
?u := 3
~~~

A rigid lower expression is retained symbolically:

~~~text
p <= ?u
~~~

gives:

~~~text
?u := p
~~~

Assignments are substituted through one another, constraints are sorted and deduplicated, and the result is independent of insertion order.

### 6.3 Selected and unselected metas

The solver can receive an explicit set of metas to solve. This supports declaration boundaries where result-classifier metas are solved while parameter-position metas remain rigid or are generalized.

A selected meta may be assigned an expression containing an unselected meta. The unselected meta remains visible in residual interface constraints.

This distinction must be normative. Without it, principal relative to what set of unknowns is undefined.

### 6.4 Maximum-only cycles

Lower-bound dependencies form a graph. Strongly connected components are solved together. Internal occurrences can be removed only beneath maximum:

~~~haskell
removeInternal members =
  fmap normalizeLevel . go
  where
    go level
      | all (`Set.notMember` members)
          (levelMetas level) =
          Just level

    go (LMeta meta)
      | meta `Set.member` members =
          Just LZero

    go (LMax a b) =
      levelMax <$> go a <*> go b

    go _ =
      Nothing
~~~

This accepts:

~~~text
max ?u 4 <= ?u
~~~

with least solution 4.

Mutually recursive maximum lower bounds are collapsed to a shared representative and the maximum of all external bases.

An occurrence beneath successor or addition is genuine self-containment and fails the occurs check:

~~~text
succ ?u <= ?u
?u + 1 <= ?u
~~~

### 6.5 Closed embedded contexts

The implementation performs an additional exact search for a selected meta embedded in a monotone right-hand expression, but only when:

- the lower bound is closed; and
- every other component of the right-hand context is closed after substituting a closed candidate for the selected meta.

It evaluates pair candidates and binary-searches the least coefficient, then least tail:

~~~haskell
closedEmbeddedLeast meta lower rhs = do
  lowerPair@(lowerCoefficient, lowerTail) <-
    closedLevel (normalizeLevel lower)

  let evaluate pair =
        closedLevel
          (substituteLevelMeta
            meta
            (fromClosedOrdinal pair)
            rhs)

      satisfies pair =
        maybe False (>= lowerPair) (evaluate pair)

      coefficientWorks coefficient =
        satisfies (coefficient, lowerTail)

  coefficient <-
    leastTrue
      0
      lowerCoefficient
      coefficientWorks

  tailValue <-
    leastTrue
      0
      lowerTail
      (\tail' -> satisfies (coefficient, tail'))

  pure (fromClosedOrdinal (coefficient, tailValue))
~~~

This produces:

| Constraint | Implemented least assignment |
|---|---|
| omega ≤ max ?u 1 | ?u := omega |
| omega ≤ ?u + 1 | ?u := omega |
| 5 ≤ ?u + 2 | ?u := 3 |

Repeated or nested occurrences can be handled if the resulting evaluation is closed and monotone.

### 6.6 Correct no-principal result

For:

~~~text
omega <= max ?u ?v
~~~

there is no pointwise least assignment to both metas. Either may carry omega while the other is zero, and those solutions are incomparable. The implementation correctly leaves this residual.

### 6.7 Concrete incompleteness

Consider:

~~~text
p + 1 <= ?u + 1
~~~

where p is rigid and ?u is selected. Componentwise natural addition is cancellative, so the unique expressible least solution is:

~~~text
?u := p
~~~

The current solver does not derive it:

- the right side is not the direct meta;
- the lower bound is not closed, so closed embedded search does not apply;
- the obligation remains residual.

A similar limitation occurs when an embedded context contains another meta even if other constraints later determine that meta. Solving does not generally combine all constraints into a symbolic optimization problem before choosing assignments.

Therefore the implementation does not justify an unrestricted statement that it computes principal least solutions for every constraint in the portable rigid-expression algebra.

### 6.8 Normative meaning of principal

For selected metas M, define pointwise assignment ordering:

~~~text
sigma <= tau
iff
for every m in M, sigma(m) <= tau(m)
~~~

A principal least solution sigma for constraints C relative to rigid parameters and assumptions A must satisfy:

1. sigma makes every solved obligation valid, leaving only explicitly permitted residual obligations;
2. for every other satisfying assignment tau, A entails sigma(m) ≤ tau(m) for every selected m;
3. sigma is expressible in the allowed level-expression language;
4. sigma is stable under renaming and independent of constraint insertion order.

The current algorithm meets this contract only on its assignable fragment.

### 6.9 Two honest specification choices

Choice A, matching the implementation:

- normatively define direct lower bounds and maximum SCCs;
- include closed embedded search;
- state that other selected-meta constraints may remain residual;
- reserve principal least solution for obligations recognized by this fragment.

Choice B, preserving a broad completeness promise:

- define complete symbolic solving and optimization over pair-valued metas and rigid parameters;
- specify when the least solution is expressible in the source level language;
- return no-principal only when the solution set truly lacks a least expressible assignment.

Choice B is a substantial implementation project. It likely needs quantifier elimination, parametric Presburger optimization, or a proved max-affine representation with case partitions. The existing algorithm is not already that procedure.

## 7. Internal Core evidence

### 7.1 Representation

~~~haskell
data UniverseEvidenceStep = UniverseEvidenceStep
  { uesLower :: !Level
  , uesUpper :: !Level
  , uesAssumptions :: ![(Level, Level)]
  }
  deriving stock (Eq, Ord, Show)

newtype UniverseEvidence = UniverseEvidence
  { ueSteps :: [UniverseEvidenceStep]
  }
  deriving stock (Eq, Ord, Show)
~~~

Multiple steps represent a composed lift. The upper endpoint of each step must equal the next lower endpoint after normalization.

### 7.2 Construction and dependency minimization

Evidence construction normalizes the theorem and assumptions, then greedily removes unnecessary dependencies:

~~~haskell
canonicalUniverseEvidenceStep lower upper assumptions =
  UniverseEvidenceStep
    normalizedLower
    normalizedUpper
    proofDependencies
  where
    normalizedLower =
      normalizeLevel lower

    normalizedUpper =
      normalizeLevel upper

    normalizedAssumptions =
      sort
        (nub
          [ (normalizeLevel a, normalizeLevel b)
          | (a, b) <- assumptions
          ])

    proofDependencies
      | assumptionsConsistent normalizedContext
      , proveLevelLeq
          normalizedContext
          normalizedLower
          normalizedUpper
            == Proved =
          minimizeDependencies normalizedAssumptions

      | otherwise =
          normalizedAssumptions
~~~

The minimizer finds one deterministic irredundant subset for sorted input, not necessarily a globally minimum-cardinality set.

### 7.3 Validation

Validation checks:

- evidence is nonempty;
- overall endpoints match the lift;
- adjacent steps compose;
- local identities are in scope;
- declaration-universe parameters are in scope;
- record-field identities have not escaped;
- no metavariables remain;
- every recorded dependency exists in the trusted surrounding scope;
- the trusted assumption context is consistent;
- replaying the semantic solver proves every step.

Recorded assumptions are dependencies, not self-authenticating premises. Validation uses the trusted outer context, so forged evidence cannot invent an assumption and then use it to prove itself.

### 7.4 Meaning of independently checkable

Internal evidence is independently replayable in this sense:

- it carries endpoints and dependency identities;
- a validator implementing the normative level solver can recompute the judgment;
- stale evidence is rejected after substitution if endpoints or dependencies no longer match.

It is not a small proof artifact. No Presburger unsatisfiability trace is stored.

The specification must decide which meaning of independently checkable it intends.

## 8. KCoreText certificate language

### 8.1 Current grammar

~~~haskell
data KLevelProof
  = KLPAssumption !Int
  | KLPClosed
  | KLPZero !KLevel
  | KLPRefl !KLevel
  | KLPTrans !KLevelProof !KLevelProof
  | KLPSuccMono !KLevelProof
  | KLPMaxLeft !KLevel !KLevel
  | KLPMaxRight !KLevel !KLevel
  | KLPAddMonoLeft !KLevel !KLevelProof
  | KLPAddMonoRight !KLevel !KLevelProof
  deriving stock (Eq, Ord, Show)
~~~

The concrete parser recognizes exactly:

~~~text
assumption(n);
closed;
zero-left level;
refl level;
trans { proof proof }
succ-mono { proof }
max-left level level;
max-right level level;
add-mono-left level { proof }
add-mono-right level { proof }
~~~

The theorem and each assumption carry a separate strictness bit:

~~~haskell
data KConstraint =
  KConstraint !Bool !KLevel !KLevel
~~~

True means strict and false means non-strict.

### 8.2 Rule meanings

Assumption:

~~~text
Gamma[n] = relation
-------------------
Gamma proves relation
~~~

Closed:

~~~text
The complete certificate has no universe parameters,
has no assumptions, has closed endpoints,
and the semantic solver proves the theorem.
----------------------------------------------------
Gamma proves theorem
~~~

Closed is legal only as the whole proof, not as a nested node.

Zero-left:

~~~text
------------
0 <= x
~~~

Reflexivity:

~~~text
------------
x <= x
~~~

Transitivity:

~~~text
x R1 y    y R2 z
----------------
x R z

R is strict iff R1 or R2 is strict.
~~~

Successor monotonicity:

~~~text
x R y
----------------
succ x R succ y
~~~

Maximum introductions:

~~~text
----------------
x <= max x y

----------------
y <= max x y
~~~

Addition monotonicity:

~~~text
x R y
-------------------------
fixed + x R fixed + y

x R y
-------------------------
x + fixed R y + fixed
~~~

Strictness is preserved by successor and addition. Transitivity is strict if either child is strict.

### 8.3 Endpoint matching

After deriving a proof-tree relation, the verifier requires:

- identical strictness bits; and
- endpoints equal under constructor normalization when they translate to solver levels.

Addition AC and maximum ACI may therefore be used implicitly at final endpoints and transitivity joints. More general semantic equalities cannot.

### 8.4 Closed proof limitation

Closed invokes the solver only if:

~~~haskell
null universes
&& null constraints
&& closedConstraint theorem
&& constraintProved emptyAssumptions theorem
~~~

It cannot prove an open arithmetic fact. It cannot be nested under addition monotonicity to establish a closed sub-inequality such as 1 ≤ omega. It cannot use assumptions.

### 8.5 Missing rules

This semantically valid construction has no proof rule:

~~~text
u <= w    v <= w
----------------
max u v <= w
~~~

The solver implements it by splitting the left maximum, but KCoreText has only maximum introduction on the right.

The grammar also lacks explicit rules for:

- replacing an endpoint with a semantically equal normalized expression;
- converting x < y to succ x ≤ y;
- converting succ x ≤ y to x < y;
- deriving equality from mutual inequalities;
- rewriting by equality;
- invoking the open arithmetic solver;
- using a closed arithmetic fact as a nested lemma;
- distributivity or dominance.

### 8.6 Assessment of the proposed additions

The proposed additions are useful:

- max-least closes the obvious lattice gap.
- normalized-equality-rewrite makes normalization dependence explicit.
- lt-to-succ-le and succ-le-to-lt expose the strictness encoding.
- antisymmetry can derive equality if a distinct equality judgment is introduced.

They are not sufficient for completeness relative to guarded Presburger arithmetic.

For example:

~~~text
omega <= u + omega
~~~

requires arithmetic knowledge about the coefficient of u + omega. It is not generally derivable from the listed structural rules without auxiliary arithmetic lemmas.

Similarly:

~~~text
u + max v w
=
max (u + v) (u + w)
~~~

requires distributivity or generic semantic arithmetic.

Antisymmetry does not help unless equality becomes a first-class judgment with congruence or rewrite rules that consume it.

## 9. Certificate generation

### 9.1 Reconstruction from solver evidence

The generator filters internal evidence dependencies to declaration-owned constraints. It then tries:

- reflexivity;
- zero-left;
- an exact direct assumption;
- a chain of exact assumption endpoints;
- successor monotonicity;
- right-side maximum introduction when the lower endpoint is exactly one arm;
- addition monotonicity when both endpoint trees have an exactly shared child.

The structural cases are:

~~~haskell
structuralProof =
  case (lower, upper) of
    (LSucc lhs, LSucc rhs) ->
      KLPSuccMono
        <$> deriveProof available visited lhs rhs

    (_, LMax lhs rhs)
      | lower == lhs ->
          KLPMaxLeft
            <$> levelToText lhs
            <*> levelToText rhs

      | lower == rhs ->
          KLPMaxRight
            <$> levelToText lhs
            <*> levelToText rhs

    (LAdd fixed lhs, LAdd fixed' rhs)
      | fixed == fixed' ->
          KLPAddMonoLeft
            <$> levelToText fixed
            <*> deriveProof available visited lhs rhs

    (LAdd lhs fixed, LAdd rhs fixed')
      | fixed == fixed' ->
          KLPAddMonoRight
            <$> levelToText fixed
            <*> deriveProof available visited lhs rhs

    _ ->
      Nothing
~~~

### 9.2 Consequence

Internal evidence records only that the semantic solver proved a relation under particular dependencies. It does not record the arithmetic derivation. Reconstruction therefore searches a weaker language after the fact.

Serialization can fail for an already checked Core lift with a diagnostic equivalent to:

~~~text
cannot serialize the checked level derivation lower <= upper
~~~

Representative failures include:

- max u v ≤ w from assumptions u ≤ w and v ≤ w;
- max u (succ u) ≤ succ u;
- open distributive or dominance facts;
- arithmetic facts needing an invented intermediate expression;
- addition monotonicity when canonical AC order does not place a shared summand in the generator's expected binary position;
- a proof needing a closed arithmetic lemma nested in a larger open proof.

This is exactly where complete solver and independently checkable portable certificates are not joined.

### 9.3 Closed and open generation

A single-step relation is emitted as closed only when:

- its endpoints contain no declaration parameters; and
- the relation is provable without assumptions.

Otherwise structural reconstruction is mandatory.

Closed generated certificates have no parameters and assumptions. Open certificates carry the owner's universe telescope and constraint block.

### 9.4 Certificate use is well guarded

When a certificate authorizes a lift, the checker:

1. specializes its universe parameters;
2. checks its constraint block under ambient assumptions;
3. re-verifies the certificate declaration;
4. checks that the specialized theorem materially establishes the requested lift.

The selected theorem may prove the lift by itself, or be an essential anchored premise together with ambient assumptions. An unrelated valid certificate cannot be repurposed merely because ambient context already proves the lift.

This authority model should be preserved in any redesign.

## 10. Strict inequality mismatch

### 10.1 Semantic representation

Strict constraints become successor inequalities before entering the semantic assumption set:

~~~text
x < y  becomes  succ x <= y
~~~

This is valid for the discrete lexicographic order on natural pairs.

### 10.2 Portable representation

KCoreText retains a strictness bit on each derived relation. Assumptions can introduce strict judgments directly, and transitivity, successor, and addition propagate strictness.

No rule connects the strict bit to successor encoding. Endpoint comparison requires an exact bit match:

~~~haskell
sameConstraint
  (KConstraint strictA lhsA rhsA)
  (KConstraint strictB lhsB rhsB) =
    strictA == strictB
      && sameKLevel lhsA lhsB
      && sameKLevel rhsA rhsB
~~~

Thus these solver-equivalent judgments are not interchangeable in a proof tree:

~~~text
x < y
succ x <= y
~~~

The spec should either:

- eliminate strict proof judgments and normalize all strict relations to successor plus ≤ before proof checking; or
- retain strict judgments and add both conversion rules.

The first option is smaller and matches the semantic solver.

## 11. Canonical KCoreText serialization

### 11.1 Current canonicalization

KCoreText alpha-renames universe identities and recursively traverses levels:

~~~haskell
canonicalLevel universes = \case
  KLUniverse ref ->
    KLUniverse
      (Map.findWithDefault ref (urId ref) universes)

  KLSucc level ->
    KLSucc (canonicalLevel universes level)

  KLMax lhs rhs ->
    KLMax
      (canonicalLevel universes lhs)
      (canonicalLevel universes rhs)

  KLAdd lhs rhs ->
    KLAdd
      (canonicalLevel universes lhs)
      (canonicalLevel universes rhs)

  KLTerm term ->
    KLTerm (canonicalTerm universes term)

  level ->
    level
~~~

It does not translate KLevel to the solver representation, normalize it, and translate it back.

Constraint blocks are sorted by recursively canonicalized raw structure. Proofs are alpha-renamed, assumption indices are remapped, and neutral transitivity around reflexivity is removed.

### 11.2 Observable gap

Inputs containing:

~~~text
add(u, v)
add(v, u)
~~~

can verify as equal through the solver-level helper while still printing as different canonical text and producing different hashes.

The same applies to reassociation and maximum arm order.

If canonical KCoreText is intended to be unique modulo the level algebra, its canonicalizer must normalize solver-representable levels before sorting declarations, constraints, or proofs.

Opaque level terms that cannot translate to the solver algebra may retain structural canonicalization. The boundary must be explicit.

## 12. Existing tests

### 12.1 Strong coverage

Tests currently exercise:

- finite successor folding;
- commutativity and associativity of open natural addition;
- zero identity of maximum;
- maximum introduction and elimination in the semantic solver;
- left-maximum assumption expansion;
- strict-cycle inconsistency;
- equality cycles and rigid representative collapse;
- successor closure under assumptions;
- atomic reachability and right-maximum countermodels;
- open addition facts involving omega;
- metavariable blocking;
- order-independent lower-bound joins;
- occurs checks;
- maximum-only recursive bounds;
- closed embedded maximum and addition solutions;
- the incomparable maximum no-principal example;
- rigid parameters as symbolic least lower bounds;
- residual preservation;
- maximum SCC solving;
- a bounded finite-model cross-check for many small rigid expressions and assumption sets;
- internal evidence dependency minimization;
- evidence composition, substitution, scope rejection, and forged-assumption rejection;
- generated scoped certificate round trips;
- direct assumption and transitivity certificates;
- invalid assumption indices;
- canonical removal of transitivity with reflexivity.

### 12.2 Missing coverage

Before claiming a final contract, add tests for:

- every rigid solver-proved relation used as Core evidence can be serialized and re-verified;
- max-least proof generation;
- strict/successor certificate conversions;
- semantic endpoint rewrites inside certificates;
- nested closed arithmetic;
- open arithmetic replay;
- canonical text equivalence for addition AC and maximum ACI;
- explicit counterexamples for non-principal inference;
- symbolic cancellation if broad principal completeness is retained;
- semantic equality versus mutual entailment;
- malformed arithmetic proof rejection if proof traces are selected.

The strongest cross-layer property is:

~~~text
For every accepted Core lift evidence E:
  emit(E) succeeds,
  parsing the emitted certificate succeeds,
  independent verification succeeds,
  and the theorem has E's normalized endpoints.
~~~

That property is not currently guaranteed by construction.

## 13. Recommended normative architecture

### 13.1 Separate syntax normalization from semantic decision

Layer 1: canonical stored syntax

~~~text
nf(0) = 0
nf(n) = finite(n)
nf(omega) = omega
nf(atom) = atom
nf(succ x) = addNF([nf(x), 1])
nf(x + y) =
  addNF(flatAdd(nf(x)) ++ flatAdd(nf(y)))
nf(max x y) =
  maxNF(flatMax(nf(x)) union flatMax(nf(y)))
~~~

Addition normal form must:

- erase zero;
- collect closed terms by pair addition;
- retain multiplicity of open terms;
- sort by a specified portable order;
- use one specified association convention.

Maximum normal form must:

- erase zero;
- deduplicate;
- sort by the same order;
- use one specified association convention.

State explicitly:

~~~text
No distributivity, cancellation, absorption, or
semantic dominance is part of constructor normalization.
~~~

Layer 2: semantic interpretation and entailment

Every rigid atom denotes an arbitrary nonnegative pair. Expression interpretation uses componentwise addition, tail successor, and lexicographic maximum. Entailment is unsatisfiability of assumptions plus negated conclusion in QF Presburger arithmetic.

This is the architecture already implemented.

### 13.2 Normative equality

Use:

~~~text
A entails x = y
iff
A entails x <= y and A entails y <= x
~~~

Constructor-normal equality remains a sound fast path.

### 13.3 Preferred certificate extension: arithmetic replay

The smallest complete bridge is a generic proof node:

~~~text
arithmetic;
~~~

Its verifier should:

1. convert strict assumptions x < y to succ x ≤ y;
2. convert a strict theorem similarly;
3. reject unresolved metas and out-of-scope identities;
4. normalize syntax;
5. assign two nonnegative integer variables to each rigid atom;
6. translate successor, addition, maximum, and lexicographic order exactly;
7. accept exactly when assumptions and negated theorem are unsatisfiable.

This is independently checkable by any separate implementation of the normative arithmetic verifier. It is not a proof trace, but neither is current internal evidence. The check is deterministic and complete.

Existing structural rules remain useful as compact, transparent certificates. Generation can prefer them and fall back to arithmetic.

A dependency-explicit variant is better:

~~~text
arithmetic [assumption(0), assumption(3), assumption(4)];
~~~

Only listed assumptions participate. This preserves dependency minimization and the current authority model.

### 13.4 Alternative: proof-producing Presburger certificates

If independently checkable means a verifier must not rerun a general decision procedure, the certificate must carry an unsatisfiability proof.

That design needs much more than five extra structural rules. It must specify:

- guarded branches for maximum;
- linear integer normalization;
- Boolean case splits;
- nonnegativity premises;
- cutting-plane, Omega-test, or equivalent elimination steps;
- contradiction witnesses;
- introduced-variable validation;
- proof-size and resource limits;
- deterministic emission, if canonical certificates are required.

This yields a smaller trusted checker but a much larger proof language and generator. Nothing equivalent is currently implemented.

### 13.5 Why structural enrichment alone is insufficient

Adding max-least, equality rewrite, strict conversions, and antisymmetry repairs known examples but does not establish completeness for all guarded Presburger consequences. Each new arithmetic pattern can expose another missing lemma.

If the spec promises portable completeness, generic arithmetic replay or a complete arithmetic proof system is the robust boundary.

## 14. Proposed proof grammar

A practical compatible grammar is:

~~~text
levelProof ::=
    assumption(integer) ;
  | closed ;
  | arithmetic [integer, ...] ;
  | zero-left level ;
  | refl level ;
  | trans { levelProof levelProof }
  | succ-mono { levelProof }
  | max-left level level ;
  | max-right level level ;
  | max-least { levelProof levelProof }
  | add-mono-left level { levelProof }
  | add-mono-right level { levelProof }
  | normalize-left level { levelProof }
  | normalize-right level { levelProof }
  | lt-to-succ-le { levelProof }
  | succ-le-to-lt { levelProof }
~~~

Recommended simplifications:

- If strict theorems normalize to successor ≤ before proof checking, omit both strict conversion rules internally.
- If endpoint matching uses normative semantic equality, explicit normalize-left and normalize-right are unnecessary. If matching stays syntax-directed, keep them.
- Add antisymmetry only if equality becomes a first-class judgment. It cannot return a ≤ or < judgment by itself.

The max-least verifier is:

~~~text
derive p = a <= c
derive q = b <= c
sameLevel c c'
--------------------------------
derive max-least { p q } = max a b <= c
~~~

For strict arms, max a b < c requires both a < c and b < c. If either premise is merely non-strict, the result is non-strict.

## 15. Normative arithmetic-verifier pseudocode

~~~text
verifyArithmetic(assumptions, theorem):

  normalizedAssumptions =
    normalizeStrictnessAndLevels(assumptions)

  normalizedTheorem =
    normalizeStrictnessAndLevels(theorem)

  require no metavariables
  require every identity is in scope
  require assumptions are satisfiable

  atoms =
    sorted distinct rigid atoms appearing in
    normalizedAssumptions and normalizedTheorem

  for each atom a:
    introduce natural variables a.c and a.n

  interpret(0)       = (0, 0)
  interpret(k)       = (0, k)
  interpret(omega)   = (1, 0)
  interpret(atom a)  = (a.c, a.n)
  interpret(succ x)  =
    let (c,n)=interpret(x) in (c,n+1)
  interpret(x + y)   =
    componentwiseSum(interpret(x), interpret(y))
  interpret(max x y) =
    if lexLe(interpret(x), interpret(y))
    then interpret(y)
    else interpret(x)

  lexLe((ac,an),(bc,bn)) =
    ac < bc or (ac = bc and an <= bn)

  formula =
    all atom components are nonnegative
    and every normalized assumption
    and not normalizedTheorem

  accept iff formula is unsatisfiable
~~~

An independent verifier may use any complete QF Presburger procedure if it implements these semantics exactly. If resource limits matter, the spec must define them and the failure mode. Resource exhaustion must reject or report indeterminate; it must never accept.

## 16. Principal-solver contract for immediate backport

If current inference remains normative, specify this fragment.

### 16.1 Inputs

- A finite set T of selected metas.
- A finite set of normalized inequalities, each with a consistent rigid assumption context.
- Unselected metas are residual unknowns, not selected variables.

### 16.2 Recognized contributions

For m in T, recognize:

1. lower ≤ m, after eliminating self-occurrences that appear only beneath maximum;
2. lower ≤ C[m], when lower and C with a closed candidate substituted for m are closed and C is evaluated by level semantics.

Do not claim arbitrary symbolic contexts C.

### 16.3 Joining and cycles

- Join contributions to m with maximum.
- Form selected-meta dependencies.
- Solve SCCs together.
- Remove internal SCC occurrences only beneath maximum.
- Reject internal occurrences under successor or addition.
- Choose the least meta identity as SCC representative.
- Substitute transitively and normalize.

### 16.4 Final classification

For each zonked constraint:

- discard if normalized endpoints are identical;
- discard if rigid solving proves it;
- reject if rigid solving disproves it;
- retain if metas still block it.

A residual does not prove absence of a principal solution. It may mean:

- no pointwise least solution exists;
- a least solution exists outside the recognized fragment;
- solving is deferred to generalization or defaulting.

Those outcomes need distinct diagnostics if users or tools must rely on them.

## 17. Specification decision matrix

| Area | Copy current behavior | Strengthen before specifying | Do not claim yet |
|---|---|---|---|
| Pair semantics | Yes | — | — |
| Natural addition | Yes | Say componentwise explicitly | — |
| Lexicographic order | Yes | Define strict conversion | — |
| Constructor AC/ACI normalization | Yes | Specify total order and association | — |
| Full semantic open normal form | — | Choose and implement if desired | Not present |
| Rigid inequality completeness | Yes | Make arithmetic translation normative | — |
| Open equality | Use mutual entailment | Remove syntax-only use where semantics are required | Unique semantic tree |
| Assumption consistency | Yes | State rejection of meta-bearing contexts | — |
| Principal direct lower bounds | Yes | Define selected metas and pointwise order | — |
| Principal arbitrary symbolic contexts | — | Requires a new algorithm | Not present |
| Internal replay evidence | Yes | Define normative replay | Arithmetic proof trace |
| Structural certificate rules | Yes | Add max-least at minimum | Completeness |
| Generic arithmetic certificate | — | Recommended | Not present |
| Proof-producing arithmetic trace | — | Large new design | Not present |
| Canonical text/hash modulo AC/ACI | — | Normalize levels before printing | Not currently ensured |

## 18. Concrete specification clauses

### 18.1 Denotation

> A solver level denotes an element of N × N. The pair (c,n) denotes omega times c plus n. Zero denotes (0,0), finite k denotes (0,k), omega denotes (1,0), successor maps (c,n) to (c,n+1), natural addition is componentwise pair addition, and maximum is maximum under lexicographic pair order. Rigid level identities range independently over N × N unless constrained by the local assumption context.

### 18.2 Ordering

> The relation (c,n) ≤ (d,m) holds exactly when c < d, or c = d and n ≤ m. Strict inequality x < y is definitionally represented in solver obligations by succ x ≤ y.

### 18.3 Constructor normalization

> Constructor normalization recursively expands successor as addition by one. Addition is flattened modulo associativity, zero operands are erased, closed operands are combined, remaining operands are sorted by the specified level-syntax order, multiplicity is retained, and the result is left-associated. Maximum is flattened modulo associativity, zero arms are erased, duplicate arms are removed, remaining arms are sorted by the specified level-syntax order, and the result is left-associated. No distributivity, cancellation, absorption, or dominance rule is part of constructor normalization.

### 18.4 Semantic equality

> Two rigid open level expressions are equal under assumptions A exactly when A entails each expression to be no greater than the other. Equality of constructor normal forms is a sound but incomplete fast path.

### 18.5 Rigid completeness

> To decide A entails x ≤ y, translate rigid atoms to pairs of nonnegative integer variables, translate level operations by pair semantics, and decide unsatisfiability of A together with not(x ≤ y) in quantifier-free Presburger arithmetic. The procedure returns proved exactly for unsatisfiable refutation formulas and disproved exactly for satisfiable refutation formulas. Obligations containing unresolved inference metavariables are blocked and are not rigid judgments.

### 18.6 Certificate replay

> An arithmetic level proof is valid exactly when the normative rigid entailment procedure proves its theorem from the indexed assumptions named by the proof. Recorded assumptions are dependencies and acquire authority only from the enclosing verified constraint telescope.

### 18.7 Principal fragment

> For each selected inference metavariable, direct lower bounds are joined by maximum. Maximum-only dependency cycles are solved as one semilattice component after replacing internal maximum occurrences by zero. An occurrence beneath successor or natural addition is rejected as recursive self-containment. A selected metavariable embedded in a right-hand context may additionally be solved by least closed-pair search only when the lower bound and all other context components are closed. Constraints outside this fragment remain residual and do not imply that no principal semantic solution exists.

## 19. Required conformance examples

### 19.1 Normalization

~~~text
succ 2                    => 3
1 + omega                 => omega + 1 in chosen sorted order
u + 0                     => u
u + v                     => v + u modulo canonical order
(u + v) + 1               => canonical flattened addition
max 0 u                   => u
max u u                   => u
max u v                   => canonical sorted maximum
max (max u v) w           => canonical flattened maximum
~~~

These must not be required to share constructor normal forms:

~~~text
max u (succ u)            and succ u
u + max v w               and max (u + v) (u + w)
~~~

They must be semantically equal.

### 19.2 Entailment

~~~text
100 <= omega                         proved
omega + 1 <= omega                   disproved
omega <= u + omega                   proved
u + omega <= omega                   disproved
u <= max u v                         proved
max u v <= w under u<=w and v<=w    proved
succ u <= succ v under u<=v          proved
u <= v under u<=v and v<=u           proved
~~~

### 19.3 Consistency

~~~text
u <= v, v <= u                       consistent
u < u                                inconsistent
max u v <= w                         equivalent to u<=w and v<=w
~~~

### 19.4 Metavariable inference

~~~text
1<=?u, 3<=?u                         ?u := 3
p<=?u                                ?u := p
max ?u 4<=?u                         ?u := 4
omega<=max ?u 1                      ?u := omega
5<=?u+2                              ?u := 3
omega<=max ?u ?v                     residual/no pointwise least
p+1<=?u+1                            residual in current fragment
succ ?u<=?u                          occurs-check error
~~~

### 19.5 Certificates

~~~text
u<=w from assumptions u<=v, v<=w                     accepted
max u v<=w from assumptions u<=w, v<=w               accepted
x<y and succ x<=y conversion                          accepted
u+max v w = max(u+v)(u+w) by arithmetic replay       accepted
a certificate naming an unavailable assumption       rejected
a certificate carrying a self-invented assumption    rejected
an out-of-scope universe identity                     rejected
an unresolved metavariable                           rejected
~~~

## 20. Final answer to the motivating concern

The implementation has decided more than the current prose spec in two important ways:

1. The semantic model and exact rigid decision method are concrete: pair-valued levels plus guarded QF Presburger arithmetic.
2. The stored syntax normal form is concrete: recursive AC addition, ACI maximum, successor expansion, and closed folding.

It has not selected a complete semantic normal form for open expressions. It does not normalize to maximums of affine expressions or an explicit ordered case partition. Case partitioning exists only inside the Presburger translation through guarded conditionals.

It also does not have a portable certificate language complete for that decision procedure. Internal Core evidence is solver-replay evidence; KCoreText proofs form a smaller structural system; generation bridges only the cases it can reconstruct.

Finally, the least-solution solver is principled and deterministic for a useful fragment, but it is not complete for all expressible principal solutions. The example p + 1 ≤ ?u + 1 prevents an unrestricted completeness claim.

The specification decision should therefore be:

- specify current syntax normalization as syntax, not semantic equality;
- specify guarded paired Presburger translation as the complete rigid judgment;
- define equality by mutual entailment;
- use a generic checked arithmetic certificate, or design a full proof-producing Presburger certificate;
- add max-least and strictness conversions if the structural language remains;
- narrow principal-solution wording to the assignable fragment unless inference is upgraded;
- normalize solver-representable KCoreText levels before canonical printing and hashing;
- require an emission-and-reverification property test connecting solver evidence to portable certificates.

Those changes would join complete solving and independent certificate checking at one normative boundary without pretending the constructor normalizer or structural proof grammar already provides semantic completeness.
