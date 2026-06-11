# Kappa Spec Digest: §15 Totality, §30 KCore, §31 Equality/Erasure, §32.1 Runtime

## §15 Totality
Two bits per definition: total-certified; conversion-reducible (δ-unfoldable). Conversion-reducible ⊆ total-certified. Conversion-reducible iff: non-recursive transparent; structurally recursive (§15.3) reducing by β/ι/δ; semantic structural descent; certificate marked conversion-safe; assertReducible (unsafe builds only). WF-recursion-only defs: total-certified, NOT conversion-reducible. assertTerminates suppresses checking for acceptance only.

§15.2 minimum: MUST accept structural descent (§15.3), Nat / lex Nat-tuple measures (§15.4), hidden phase mutual recursion (§15.10), explicit decreases (§15.11). Checking conservative otherwise; soundness mandatory.

§15.3 structural descent `<ₛ`: least transitive relation from (1) pattern matching on v binding ctor arg u ⟹ u <ₛ v; (2) congruence on same-ctor with defeq other args. Structural parameter must be explicit parameter of inductive type. Accept iff every recursive call strictly decreases the chosen parameter tuple under lex lifting.

§15.8 arithmetic solver MUST decide: `n - 1 < n` under `0 < n`; `a - (b+1) < a - b` under `b < a`; lex Nat-tuple comparison; non-negative affine combinations.

§15.10 hidden phase: order SCC members by (normalized source path, source start offset); member i of n gets phase n-1-i appended as final lex component.

§15.11 decreases grammar:
```text
decreasesSpec ::= termMeasure | 'structural' (x | (x, y, ...)) | termMeasure 'by' R
                | termMeasure 'by' R 'using' proof | termMeasure 'using' proof | 'sized' x
```
`decreases sized x` reserved, ill-formed in v1. SCC uniformity: all members same kind/arity. Rejection family: kappa.termination.failure.

RECURSION RULE: no `let rec`. Top-level/local binding recursive ONLY with preceding (same-file/same-block) signature declaration; mutual groups need signatures for every member. SCCs elaborate from semantic fixpoint: publish all headers before checking bodies.

## §30 KCore
Pipeline: source → KFrontIR → KCore (after CORE_LOWERING). Elaboration MUST terminate. KCore = source of truth for typechecking/normalization/defeq/hashing. No unresolved names/overloads/inference in KCore. Retains: intrinsic compile-time types, binder quantities/regions/implicits, proofs, branch refinements as erased bindings, handler forms, application spines, suspensions, places.

Core forms:
```text
AppSpine fn [a1, ..., ak]      -- one node per application site
Thunk/Need : Type -> Type;  Delay : A -> Thunk A;  Memo : A -> Need A;  Force : both -> A
Place ::= PVar ident | PField Place label | PCtorField Place label
ReadPlace/MovePlace : Place -> Term; FillPlace : Place -> Term -> Term (pure rebuild); OpenPlace : Place -> Term
WithBorrowPlace p as (ρ, x) in e
RetCtx = [(L1:R1)...]; Completion(RetCtx,A) = Normal A | Break L | Continue L | Return[Li] Ri
ExitAction(m) = Deferred (m Unit) | Release[A] ((1 r:A) -> m Unit) (1 r:A)
DoScope : DoScopeLabel -> m Completion -> m Completion        -- exit actions LIFO exactly once
ScheduleExit : DoScopeLabel -> ExitAction(m) -> m Completion -> m Completion
OpCall : EffLabel -> OpSymbol -> ArgSpine -> Eff r_all B
HandleShallow : EffLabel -> HandlerSpec -> Eff r_all A -> m B
Resumption : Type -> Type -> Type; Resume : ...
CtorTag; HasCtor/LacksCtor : forall (@0 a). a -> CtorTag -> Type; ⟨C⟩ canonical tags
```
Active refinement context threads through every branch/guard/normalization/conversion query: BoolIsTrue/False, HasCtorFact, LacksCtorFact, CtorIndexEq, StableAliasEq, VarCurrentVersion. Facts part of memo keys; erased before backend.

Erasure justifications per erased occurrence: QuantityZero | AmbientDemandZero | RuntimeErasedEvidence | CompileTimeClassifier | MetaPhaseBinding | CaptureAnnotationStructure | ErasedIndex | ExplicitRuntimeSafeEliminator | BackendIntrinsicErasure.

Inhabitance summaries (§30.2.7): Empty | Subsingleton | Contractible | Finite n | Unknown; only exact Empty under SourceReachability justifies impossible.

Local declarations (§30.1.1): closure-convert over captured free vars; family identity per declaration site (never per dynamic evaluation).

## §31 Definitional equality
Conversion = smallest congruence with: β; δ (transparent conversion-reducible only, keyed by resolved declaration identity + opacity env); ι (match/if/tag-test reduction from scrutinee normal form OR refinement context); η (functions: f ≡ \x -> f x; records ≡ reconstruction from projections; zero-field record ≡ Unit); suspension (force (thunk e) ↦ e, force (lazy e) ↦ e); capture-annotation equality; QUANTITIES PART OF FUNCTION-TYPE IDENTITY (binders equal iff q1 = q2 ∧ A1 ≡ A2 ∧ B1 ≡ B2; subsumption is coercion not defeq). Also: T? ↦ Option T; variant rows canonical order modulo dup removal; record canonical field order; literal normalization (fromInteger of total transparent fn δ-reduces).

Environment stability: conversion must not depend on import/load/iteration/cache order. Fuel-bounded normalization OK if sound. Position independence: same transparent def reduces uniformly in all positions.

Refinement-aware ι (§31.1.2): HasCtor s ⟨D⟩ ⟹ LacksCtor s ⟨C⟩ for distinct C; LacksCtor for all visible ctors but one ⟹ HasCtor for remainder; b = True/False reduces if/match; case decisions select HasCtor branch / skip LacksCtor branches. Guard failure introduces NO negative facts.

§31.2 erasure deletes: quantity-0 binders/fields/args; RuntimeErased-typed; capture annotations; compile-time classifiers regardless of quantity (Syntax, Elab, rows, labels, quantities, regions, universes, Type u). subst/pathInd with erased proof = coercion, never runtime branch.

§31.4 record canonicalization: dependency topological order, ties by Unicode scalar lexicographic field name. Defeq iff canonical forms field-wise defeq INCLUDING quantities. Runtime field evaluation stays source order.

## §32.1 Dynamic semantics
STRICT call-by-value, LEFT-TO-RIGHT, except suspensions. Application: fn then arg then apply. Records/tuples: fields left-to-right. Record patch: scrutinee once, RHSs in source order once, canonical assembly. if: cond then one branch. match: scrutinee once, cases top-to-bottom, guards after pattern match. do = desugared monads. thunk/lazy don't evaluate at construction; force per kind (Delay every time; Memo once).

## Implementation takeaways
1. Definitions: separate totalCertified/conversionReducible flags; δ-unfold only latter. Minimum checker: structural descent + Nat measures + decreases. Recursion via preceding signatures only.
2. Conversion: β+δ+ι+η + suspension + canonicalizations; refinement context in memo keys.
3. Erasure: quantity-0 + classifier-based before interpretation.
4. Interpreter: strict CBV left-to-right.
