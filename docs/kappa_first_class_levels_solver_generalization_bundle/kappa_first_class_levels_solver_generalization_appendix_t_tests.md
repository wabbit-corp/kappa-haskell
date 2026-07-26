# Appendix T companion tests: first-class levels, solver certificates, generalization, and recursive schemas

**Base specification:** `Spec(100).md`  
**Independent directory suites:** 67

These tests are separate from the normative specification. The accompanying patch adds any new portable harness
assertions used below.

## Coverage summary

* `kcore`: 8 suites
* `negative`: 17 suites
* `positive`: 29 suites
* `solver`: 13 suites

## Suite inventory

### 1. `kcore/arithmetic_certificate_bad_assumption`

Arithmetic replay rejects an unavailable assumption index.

**Expected result:** `reject`

**Files:** `bad.kcore`, `main.kp`, `suite.ktest`

### 2. `kcore/arithmetic_certificate_valid`

Arithmetic replay proves max-least from the selected assumptions.

**Expected result:** `accept`

**Files:** `main.kp`, `proof.kcore`, `suite.ktest`

### 3. `kcore/canonical_ac_level_hash`

AC-equivalent level expressions have canonical KCore semantic identity.

**Expected result:** `accept`

**Files:** `a.kcore`, `b.kcore`, `main.kp`, `suite.ktest`

### 4. `kcore/direct_and_composed_lift_same_hash`

Canonical lift composition makes direct and transitively composed lifts semantically identical.

**Expected result:** `accept`

**Files:** `composed.kcore`, `direct.kcore`, `main.kp`, `suite.ktest`

### 5. `kcore/lift_proof_identity_hash`

Different proofs of the same lift theorem produce the same semantic hash.

**Expected result:** `accept`

**Files:** `arithmetic.kcore`, `closed.kcore`, `main.kp`, `suite.ktest`

### 6. `kcore/reject_declared_sealing_eliminator`

KCore has no generic sealing eliminator authority.

**Expected result:** `reject`

**Files:** `bad.kcore`, `main.kp`, `suite.ktest`

### 7. `kcore/structural_and_arithmetic_same_hash`

Structural and arithmetic proofs canonicalize to the same level-evidence semantic identity.

**Expected result:** `accept`

**Files:** `arithmetic.kcore`, `main.kp`, `structural.kcore`, `suite.ktest`

### 8. `kcore/typelevel_algebra_version_mismatch`

KCoreText artifacts with an incompatible TypeLevel algebra version are rejected.

**Expected result:** `reject`

**Files:** `bad.kcore`, `main.kp`, `suite.ktest`

### 9. `negative/distinct_neutral_atoms_need_evidence`

Distinct opaque level terms are not ordered without evidence.

**Expected result:** `reject`

**Files:** `main.kp`

### 10. `negative/forall_does_not_commute_implicitly`

Universal quantification is not silently moved through a type constructor.

**Expected result:** `reject`

**Files:** `main.kp`

### 11. `negative/generalization_meta_free_in_environment`

A candidate variable free in the surrounding environment is not generalized by a nested declaration.

**Expected result:** `reject`

**Files:** `main.kp`

### 12. `negative/generalization_parametric_escape`

Rigid parametric rechecking rejects a declaration that returns its generalized type witness ordinarily.

**Expected result:** `reject`

**Files:** `main.kp`

### 13. `negative/inverse_schema_lift_not_implicit`

A covariant upward schema lift has no implicit inverse.

**Expected result:** `reject`

**Files:** `main.kp`

### 14. `negative/monadic_bound_value_not_generalized`

A monadic bind variable does not introduce fresh outer quantification.

**Expected result:** `reject`

**Files:** `main.kp`

### 15. `negative/monotone_theorem_not_scanned`

A nearby theorem is not discovered unless packaged as ordinary evidence.

**Expected result:** `reject`

**Files:** `main.kp`

### 16. `negative/mutable_current_level_index`

A mutable current-value facet is not a stable universe index in v1.

**Expected result:** `reject`

**Files:** `main.kp`

### 17. `negative/pattern_match_does_not_drop_dependency`

Pattern matching a parametric field preserves the parametric origin.

**Expected result:** `reject`

**Files:** `main.kp`

### 18. `negative/principal_self_containment`

Positive self-occurrence beneath successor is rejected.

**Expected result:** `reject`

**Files:** `main.kp`

### 19. `negative/recursive_schema_increase`

An upward recursive declaration-schema instantiation is rejected in v1.

**Expected result:** `reject`

**Files:** `main.kp`

### 20. `negative/recursive_schema_leq_not_termination`

A non-increasing schema edge alone is not a strict termination argument.

**Expected result:** `reject`

**Files:** `main.kp`

### 21. `negative/recursive_schema_nonidentity_implicit`

A non-identity recursive schema instantiation may not be inferred.

**Expected result:** `reject`

**Files:** `main.kp`

### 22. `negative/schema_constraint_unsatisfied`

Explicit schema instantiation must discharge its erased comparison proof.

**Expected result:** `reject`

**Files:** `main.kp`

### 23. `negative/schema_reification_does_not_fill_explicit_level`

Schema reification never supplies an omitted explicit term-level TypeLevel argument.

**Expected result:** `reject`

**Files:** `main.kp`

### 24. `negative/unbounded_parametric_package_no_code_escape`

A projected parametric witness cannot be returned as an ordinary type code.

**Expected result:** `reject`

**Files:** `main.kp`

### 25. `negative/wrong_type_level_index`

A non-TypeLevel term cannot index Type.

**Expected result:** `reject`

**Files:** `main.kp`

### 26. `positive/action_value_generalizes_outer_parameter`

A monadic action value may be generalized; each use instantiates before execution.

**Expected result:** `accept`

**Files:** `main.kp`

### 27. `positive/branch_expected_widening`

Expected-type-directed branch joining may forget an exact level through cumulativity.

**Expected result:** `accept`

**Files:** `main.kp`

### 28. `positive/exact_level_result_not_widened`

Application to an opaque index retains Type (f x) rather than widening to a ceiling.

**Expected result:** `accept`

**Files:** `main.kp`

### 29. `positive/explicit_schema_constraint_proof_binder`

A user-written erased proof binder expresses a declaration-universe constraint.

**Expected result:** `accept`

**Files:** `main.kp`

### 30. `positive/first_class_level_recursion_can_increase`

A first-class TypeLevel argument may increase when another ordinary measure decreases.

**Expected result:** `accept`

**Files:** `main.kp`

### 31. `positive/forall_commutes_with_selected_evidence`

Expected-type-directed quantifier interchange succeeds through PreservesParametricForall evidence.

**Expected result:** `accept`

**Files:** `main.kp`

### 32. `positive/inferred_schema_constraint_becomes_binder`

An inferred declaration constraint is serialized as an anonymous erased proof binder.

**Expected result:** `accept`

**Files:** `main.kp`

### 33. `positive/level_snapshot_from_var`

An immutable snapshot of a mutable current value may be used in a local type.

**Expected result:** `accept`

**Files:** `main.kp`

### 34. `positive/local_declaration_universe_generalization`

A local semantic declaration may generalize a fresh universe and be instantiated independently.

**Expected result:** `accept`

**Files:** `main.kp`

### 35. `positive/monotone_global_instance`

An ordinary global Monotone instance permits covariance through an opaque TypeLevel function.

**Expected result:** `accept`

**Files:** `main.kp`

### 36. `positive/monotone_local_evidence`

A local erased Monotone binder is selected before variance inference.

**Expected result:** `accept`

**Files:** `main.kp`

### 37. `positive/neutral_level_bound_evidence`

Ordinary erased proof evidence may bound an opaque neutral level term.

**Expected result:** `accept`

**Files:** `main.kp`

### 38. `positive/neutral_term_schema_instantiation`

An explicit declaration-schema instantiation may use a stable opaque TypeLevel term.

**Expected result:** `accept`

**Files:** `main.kp`

### 39. `positive/opaque_level_application_exact_result`

An opaque total TypeLevel application is a valid universe index and the exact dependent result is retained.

**Expected result:** `accept`

**Files:** `main.kp`

### 40. `positive/preserve_existing_forall`

Aliasing an already polymorphic value preserves its first-class polymorphic type.

**Expected result:** `accept`

**Files:** `main.kp`

### 41. `positive/record_projection_level_index`

A stable immutable record projection of TypeLevel may index Type.

**Expected result:** `accept`

**Files:** `main.kp`

### 42. `positive/recursive_schema_identity`

An identity recursive schema call may omit its universe instantiation.

**Expected result:** `accept`

**Files:** `main.kp`

### 43. `positive/recursive_schema_lower`

A non-identity recursive schema call is explicit and pointwise lower-or-equal.

**Expected result:** `accept`

**Files:** `main.kp`

### 44. `positive/recursive_schema_strict_level_termination`

A strict same-or-lower schema edge may contribute a well-founded termination decrease.

**Expected result:** `accept`

**Files:** `main.kp`

### 45. `positive/same_neutral_term_atom_identity`

Definitionally identical neutral level terms receive the same rigid atom identity.

**Expected result:** `accept`

**Files:** `main.kp`

### 46. `positive/schema_lift_expected_type_direct`

schemaLift is inserted only against a known expected fully saturated same-family target.

**Expected result:** `accept`

**Files:** `main.kp`

### 47. `positive/schema_lift_not_used_for_meta_solving`

Exact same-family unification solves a bare target instance without inserting schemaLift.

**Expected result:** `accept`

**Files:** `main.kp`

### 48. `positive/schema_reify_bounded_expected_type`

A declaration schema eta-expands into a bounded first-class level function from an expected type.

**Expected result:** `accept`

**Files:** `main.kp`

### 49. `positive/schema_store_bounded_first_class`

A field with an expected bounded first-class type preserves declaration-level polymorphism by eta-expansion.

**Expected result:** `accept`

**Files:** `main.kp`

### 50. `positive/schema_store_monomorphic_context`

Without an expected level-polymorphic type, a declaration schema is instantiated once.

**Expected result:** `accept`

**Files:** `main.kp`

### 51. `positive/standard_add_partial_monotone`

The standard prelude provides Monotone evidence for addition by a fixed level.

**Expected result:** `accept`

**Files:** `main.kp`

### 52. `positive/unbounded_parametric_package_projection`

An unbounded package may project its type field parametrically and use it in a dependent result.

**Expected result:** `accept`

**Files:** `main.kp`

### 53. `positive/unbounded_parametric_package_repack`

Ordinary construction and projection are sufficient to repack an unbounded parametric witness.

**Expected result:** `accept`

**Files:** `main.kp`

### 54. `positive/user_constraint_reuses_generated_obligation`

An equivalent user proof binder prevents a duplicate generated constraint.

**Expected result:** `accept`

**Files:** `main.kp`

### 55. `solver/constructor_nf_add_ac`

Addition constructor normalization is AC, zero-eliminating, sorted, and multiplicity-preserving.

**Expected result:** `accept`

**Files:** `main.kp`

### 56. `solver/constructor_nf_max_aci`

Maximum constructor normalization is ACI, zero-eliminating, sorted, and duplicate-free.

**Expected result:** `accept`

**Files:** `main.kp`

### 57. `solver/monotone_not_order_embedding`

Monotone evidence alone does not authorize inverse-order cancellation.

**Expected result:** `accept`

**Files:** `main.kp`

### 58. `solver/neutral_atom_not_entailed`

An opaque neutral atom has no unproved relation to another atom.

**Expected result:** `accept`

**Files:** `main.kp`

### 59. `solver/no_pointwise_least`

Two metas under max have no pointwise least assignment.

**Expected result:** `accept`

**Files:** `main.kp`

### 60. `solver/outside_portable_fragment`

A minimizable symbolic context outside the portable assignment fragment requires annotation.

**Expected result:** `accept`

**Files:** `main.kp`

### 61. `solver/principal_additive_cancellation`

Common additive context cancellation solves p+1 <= ?u+1.

**Expected result:** `accept`

**Files:** `main.kp`

### 62. `solver/principal_closed_residuation`

Closed additive residuation computes the least pair solution.

**Expected result:** `accept`

**Files:** `main.kp`

### 63. `solver/principal_direct_lower_bounds`

The portable solver joins direct lower bounds by maximum.

**Expected result:** `accept`

**Files:** `main.kp`

### 64. `solver/principal_single_meta_max_context`

A single-meta maximum context is solved when the other arm is rigidly insufficient.

**Expected result:** `accept`

**Files:** `main.kp`

### 65. `solver/principal_successor_cancellation`

Common successor cancellation solves succ p <= succ ?u.

**Expected result:** `accept`

**Files:** `main.kp`

### 66. `solver/semantic_distribution_beyond_nf`

Rigid Presburger semantics proves distributive equality not used by stored syntax normalization.

**Expected result:** `accept`

**Files:** `main.kp`

### 67. `solver/semantic_equality_beyond_nf`

Rigid semantic equality recognizes dominance not performed by constructor normalization.

**Expected result:** `accept`

**Files:** `main.kp`

## Required harness properties exercised

The package assumes the patch's new assertions for level normalization, entailment, direct principal-solver
queries, recursive schema edges, selected evidence, and KCore semantic-hash equality. All other directives are
existing Appendix T forms.

KCoreText fixtures require the five TypeLevel algebra/solver version metadata fields, arithmetic replay, and
canonical proof-irrelevant level-evidence hashing.

## Execution status

The suite manifests, paths, JSON, Markdown, and ZIP structure are validated. The repository integration imports the
exact tree under `tests/conformance/spec-coverage/first-class-levels-solver-generalization/`; all 67 suites pass the
Appendix T harness.
