# Appendix T test manifest

This package contains **109 independent Appendix T suite roots**. Each ordinary test lives in its own directory and has its own `main.kp`; multi-file and incremental tests retain the standard directory-suite layouts required by Appendix T.

The suite roots must be executed independently. Compiling the entire `tests/` tree as one directory suite would intentionally combine unrelated modules and diagnostics, which is the sort of administrative catastrophe test harnesses exist to prevent.

## T12.1 Expression forms, context, quantities, and proof relevance

| Test | Suite root | Purpose |
|---|---|---|
| T12.1.1 | `tests/T12_1_1_bare_expected_type` | Bare derive uses a rigid expected type. |
| T12.1.2 | `tests/T12_1_2_explicit_goal` | derive(T) uses an explicit type goal. |
| T12.1.3 | `tests/T12_1_3_missing_expected_type` | Bare derive without an expected type is rejected. |
| T12.1.4 | `tests/T12_1_4_proof_relevant_bool_choice` | A proof-relevant finite choice is not selected arbitrarily. |
| T12.1.5 | `tests/T12_1_5_exact_local_hypothesis` | Derivation may use an exact explicit hypothesis. |
| T12.1.6 | `tests/T12_1_6_linear_candidate_not_duplicated` | Derivation obeys linear-use constraints. |
| T12.1.7 | `tests/T12_1_7_branch_refinement` | Branch-local equality and constructor facts participate in derive. |
| T12.1.8 | `tests/T12_1_8_higher_paths_ambiguous` | Parallel paths remain ambiguous without IsSet. |
| T12.1.9 | `tests/T12_1_9_isset_merges_paths` | IsSet permits deterministic merging of path candidates. |

## T12.2 `forall`, ordinary functions, function extensionality, and h-level closure

| Test | Suite root | Purpose |
|---|---|---|
| T12.2.1 | `tests/T12_2_1_hedberg_ordinary_decider` | Hedberg receives an ordinary borrowed decision procedure. |
| T12.2.2 | `tests/T12_2_2_forall_decider_is_distinct` | An implicit quantity-0 forall decider is not an ordinary Hedberg argument. |
| T12.2.3 | `tests/T12_2_3_ordinary_pi_isprop` | Pointwise IsProp closes an ordinary dependent function type. |
| T12.2.4 | `tests/T12_2_4_ordinary_pi_isset` | Pointwise IsSet closes an ordinary dependent function type. |
| T12.2.5 | `tests/T12_2_5_sigma_isset` | Set closure applies to transparent dependent records rather than sealed exists syntax. |
| T12.2.6 | `tests/T12_2_6_funext_not_defeq` | Function extensionality constructs a path but does not extend conversion. |
| T12.2.7 | `tests/T12_2_7_happly_definition` | happly is an ordinary definition derived from congruence. |
| T12.2.8 | `tests/T12_2_8_implicit_pi_isprop` | Pointwise proposition evidence closes an implicit quantity-0 Pi with forallExt. |
| T12.2.9 | `tests/T12_2_9_forall_extensionality` | forallExt proves equality of implicit quantity-0 functions without changing conversion. |
| T12.2.10 | `tests/T12_2_10_borrow_function_extensionality` | Borrowed operation fields use the borrowed-Pi extensionality projection required by Eq uniqueness. |
| T12.2.11 | `tests/T12_2_11_first_class_pi_isprop` | piIsProp is an ordinary first-class evidence transformation rather than a special instance declaration. |

## T12.3 `Reflects` and equality reflection

| Test | Suite root | Purpose |
|---|---|---|
| T12.3.1 | `tests/T12_3_1_reflects_dec_true` | reflectsDec preserves positive evidence. |
| T12.3.2 | `tests/T12_3_2_reflects_dec_false` | reflectsDec preserves a refutation. |
| T12.3.3 | `tests/T12_3_3_reflects_sound` | reflectsSound is ordinary elimination. |
| T12.3.4 | `tests/T12_3_4_reflects_complete` | reflectsComplete is ordinary elimination. |
| T12.3.5 | `tests/T12_3_5_eq_reflect` | eqReflect packages both Eq directions without becoming a trait member. |

## T12.4 Independent evidence uniqueness and first-class evidence

| Test | Suite root | Purpose |
|---|---|---|
| T12.4.1 | `tests/T12_4_1_isset_independent` | IsSet is independently unique evidence. |
| T12.4.2 | `tests/T12_4_2_eq_independent` | Eq carries an independent uniqueness certificate. |
| T12.4.3 | `tests/T12_4_3_equiv_sealed` | Equiv remains a sealed selected structure. |
| T12.4.4 | `tests/T12_4_4_custom_property_unique` | A proof-only custom trait can declare independent uniqueness. |
| T12.4.5 | `tests/T12_4_5_invalid_unique_runtime_field` | A Bool operation prevents a bogus structural uniqueness proof. |
| T12.4.6 | `tests/T12_4_6_circular_unique_certificate` | A uniqueness proof may not use IsTrait subsingletonhood for itself. |
| T12.4.7 | `tests/T12_4_7_first_class_hedberg` | An ordinary function returns fresh independently unique IsSet evidence. |
| T12.4.8 | `tests/T12_4_8_local_independent_instance` | A local orphan instance is permitted for independently unique evidence. |
| T12.4.9 | `tests/T12_4_9_sealed_local_orphan_rejected` | The local-orphan relaxation does not apply to sealed evidence. |
| T12.4.10 | `tests/T12_4_10_semantic_vs_artifact_identity` | Independent evidence may be semantically equal with distinct proof artifacts. |
| T12.4.11 | `tests/T12_4_11_unique_certificate_mutation` | Independent uniqueness certificates reject decisive mutations. |
| T12.4.12 | `tests/T12_4_12_fresh_first_class_eq` | Expression-level derive may construct fresh first-class Eq evidence because Eq is independently unique. |
| T12.4.13 | `tests/T12_4_13_fresh_eq_not_registered` | Fresh expression-level Eq evidence is an ordinary value and does not register a global instance candidate. |

## T12.5 Trait-member and supertrait completion

| Test | Suite root | Purpose |
|---|---|---|
| T12.5.1 | `tests/T12_5_1_derived_member` | Prefix derive members are solved per concrete instance. |
| T12.5.2 | `tests/T12_5_2_explicit_member_override` | An explicit law overrides a synthesized member. |
| T12.5.3 | `tests/T12_5_3_automatic_omitted_prop` | An omitted independently propositional member is attempted automatically. |
| T12.5.4 | `tests/T12_5_4_missing_runtime_member` | A missing runtime member is not silently synthesized. |
| T12.5.5 | `tests/T12_5_5_member_order_independent` | Members inside one instance complete by dependency rather than source order. |
| T12.5.6 | `tests/T12_5_6_incomplete_self_rejected` | A synthesized member cannot summon its incomplete dictionary. |
| T12.5.7 | `tests/T12_5_7_member_cycle` | Mutually dependent synthesized members without a base are rejected. |
| T12.5.8 | `tests/T12_5_8_derived_supertrait` | A synthesized supertrait remains a real public projection. |
| T12.5.9 | `tests/T12_5_9_plain_supertrait_input` | A plain supertrait is still an input rather than a derived default. |
| T12.5.10 | `tests/T12_5_10_direct_supertrait_wins` | Direct coherent evidence is used before a synthesized supertrait default. |
| T12.5.11 | `tests/T12_5_11_prefix_member_parse` | Prefix derived-member syntax parses an arrow ending in equality without a trailing = derive ambiguity. |

## T12.6 `Eq`, `Equiv`, fallback instances, and instance termination

| Test | Suite root | Purpose |
|---|---|---|
| T12.6.1 | `tests/T12_6_1_structural_eq` | Structural Eq derivation produces laws and IsSet. |
| T12.6.2 | `tests/T12_6_2_always_false_eq` | An always-false comparator fails completeness. |
| T12.6.3 | `tests/T12_6_3_always_true_eq` | An always-true comparator fails soundness. |
| T12.6.4 | `tests/T12_6_4_isset_does_not_rescue_eq` | Existing IsSet evidence does not validate a bad comparator. |
| T12.6.5 | `tests/T12_6_5_shared_isset_goal` | Explicit IsSet and Eq completion share one goal independent of source order. |
| T12.6.6 | `tests/T12_6_6_eq_semantic_uniqueness` | Distinct lawful Eq constructions are semantically identical. |
| T12.6.7 | `tests/T12_6_7_equiv_fallback_selected` | Eq supplies Equiv only through fallback when no direct Equiv exists. |
| T12.6.8 | `tests/T12_6_8_direct_equiv_overrides_fallback` | A direct non-equality Equiv overrides the Eq fallback. |
| T12.6.9 | `tests/T12_6_9_equiv_nonreflecting` | A non-equality Equiv proof never reflects to propositional equality. |
| T12.6.10 | `tests/T12_6_10_fallback_ambiguity` | Two incompatible fallback instances are rejected deterministically. |
| T12.6.11 | `tests/T12_6_11_fallback_instance_cycle` | A cross-trait fallback cycle without a decreasing argument is rejected by size-change instance termination. |
| T12.6.12 | `tests/T12_6_12_unsolved_ordinary_premise_falls_back` | A well-formed ordinary candidate with unsolved premises is discarded before the Eq-to-Equiv fallback stage. |

## T12.7 Relation-law evidence, `Preorder`, `PartialOrder`, and `Ord`

| Test | Suite root | Purpose |
|---|---|---|
| T12.7.1 | `tests/T12_7_1_multiple_relation_values` | Several explicit relations and law evidences can coexist. |
| T12.7.2 | `tests/T12_7_2_law_evidence_unique` | Proof-only law evidence for the same relation is independently unique. |
| T12.7.3 | `tests/T12_7_3_preorder_basic` | A selected Preorder carries reflexivity and transitivity laws. |
| T12.7.4 | `tests/T12_7_4_partial_order_derives_eq` | PartialOrder derives Eq from mutual leq. |
| T12.7.5 | `tests/T12_7_5_antisymmetry_failure` | A non-antisymmetric preorder cannot become PartialOrder. |
| T12.7.6 | `tests/T12_7_6_ord_totality` | Ord proves actual totality and derives compare agreement. |
| T12.7.7 | `tests/T12_7_7_partial_not_total` | A lawful partial order with incomparable values cannot derive Ord. |
| T12.7.8 | `tests/T12_7_8_compare_agreement` | A custom compare implementation must agree with Eq and leq. |
| T12.7.9 | `tests/T12_7_9_leq_only_needs_preorder` | <= is available with Preorder without Ord. |
| T12.7.10 | `tests/T12_7_10_explicit_total_order_laws` | IsTotalOrder classifies an explicit relation without selecting ambient Ord. |
| T12.7.11 | `tests/T12_7_11_first_class_preorder_laws` | preorderLaws returns independently unique law evidence as an ordinary first-class value. |

## T12.8 `Alternative` laws

| Test | Suite root | Purpose |
|---|---|---|
| T12.8.1 | `tests/T12_8_1_alternative_laws` | Alternative refines Applicative and carries identity/associativity laws. |
| T12.8.2 | `tests/T12_8_2_alternative_requires_applicative` | Alternative cannot be constructed without Applicative evidence. |
| T12.8.3 | `tests/T12_8_3_bad_alternative_identity` | An invalid Alternative operation is rejected by its laws. |
| T12.8.4 | `tests/T12_8_4_alternative_not_commutative` | Left-biased Alternative is accepted; commutativity is not required. |

## T12.9 No-confusion, decision procedures, induction, and helper lemmas

| Test | Suite root | Purpose |
|---|---|---|
| T12.9.1 | `tests/T12_9_1_constructor_disjointness` | No-confusion proves constructor disjointness. |
| T12.9.2 | `tests/T12_9_2_constructor_injectivity` | No-confusion proves same-constructor injectivity. |
| T12.9.3 | `tests/T12_9_3_presburger` | Presburger arithmetic participates in derive. |
| T12.9.4 | `tests/T12_9_4_append_right_identity` | Structural induction is selected automatically. |
| T12.9.5 | `tests/T12_9_5_append_associativity` | Induction and rewriting prove append associativity. |
| T12.9.6 | `tests/T12_9_6_map_identity` | Automatic induction proves map identity. |
| T12.9.7 | `tests/T12_9_7_indexed_vector` | Indexed induction preserves constructor-forced indices. |
| T12.9.8 | `tests/T12_9_8_mutual_induction` | Mutual induction follows a verified inductive group. |
| T12.9.9 | `tests/T12_9_9_functional_induction` | Functional induction follows checked recursive equations. |
| T12.9.10 | `tests/T12_9_10_helper_lemma` | Accumulator generalization may synthesize a private helper lemma. |
| T12.9.11 | `tests/T12_9_11_false_conjecture_counterexample` | A false finite theorem produces a checked counterexample. |

## T12.10 Opacity, theorem scope, local scope, pipeline records, and incrementality

| Test | Suite root | Purpose |
|---|---|---|
| T12.10.1 | `tests/T12_10_1_opaque_representation` | Client derivation cannot inspect an opaque representation. |
| T12.10.2 | `tests/T12_10_2_visible_theorem_scope` | An explicitly imported theorem may discharge derive. |
| T12.10.3 | `tests/T12_10_3_unimported_theorem_not_searched` | A transitive but unimported theorem is not premise-search scope. |
| T12.10.4 | `tests/T12_10_4_local_scope_sequential` | Local declaration scope remains sequential. |
| T12.10.5 | `tests/T12_10_5_derive_respects_borrow` | Derivation cannot turn a borrowed value into an escaping owned value. |
| T12.10.6 | `tests/T12_10_6_derive_record_body_resolve` | BODY_RESOLVE exposes a structured DeriveRecord. |
| T12.10.7 | `tests/T12_10_7_kcore_has_no_derive_node` | No source derive node survives KCore. |
| T12.10.8 | `tests/T12_10_8_derive_proof_mutations` | Generated proof records reject decisive KCore and certificate mutations. |
| T12.10.9 | `tests/T12_10_9_incremental_evidence_identity` | Changing only the proof artifact preserves semantic evidence identity but changes the exact fingerprint. |
| T12.10.10 | `tests/T12_10_10_declaration_permutation` | Top-level declaration permutation preserves derivation and interface semantics. |
| T12.10.11 | `tests/T12_10_11_fallback_import_order` | A direct Equiv instance wins over the Eq fallback independently of import processing order. |
| T12.10.12 | `tests/T12_10_12_fallback_absence_invalidation` | Adding an ordinary Equiv invalidates the negative absence dependency of an earlier Eq fallback selection. |

## T12.11 Whole-evidence derivation, registration, and lexical evidence roots

| Test | Suite root | Purpose |
|---|---|---|
| T12.11.1 | `tests/T12_11_1_instance_whole_derive` | instance G = derive publishes sealed-coherent evidence through an instance artifact. |
| T12.11.2 | `tests/T12_11_2_declaration_derive_registers` | Declaration-level derive registers evidence for later implicit resolution. |
| T12.11.3 | `tests/T12_11_3_expression_evidence_not_global` | An exported explicit evidence value does not register a global instance when it is not imported or bound locally. |
| T12.11.4 | `tests/T12_11_4_implicit_does_not_escalate` | Ordinary omitted implicit arguments do not invoke full structural derive. |
| T12.11.5 | `tests/T12_11_5_declaration_derive_pointed` | Declaration-level whole evidence derivation may synthesize a unique Unit operation and register it. |
| T12.11.6 | `tests/T12_11_6_sealed_existing_reused` | Expression-level derive may reuse existing sealed-coherent evidence. |
| T12.11.7 | `tests/T12_11_7_whole_instance_ambiguous_member` | Whole-instance derive reports an ambiguous proof-relevant operation. |
| T12.11.8 | `tests/T12_11_8_explicit_evidence_local_root` | A local explicit evidence binding becomes a local implicit candidate without global registration. |

## T12.12 Finite and algebraic solver portfolio

| Test | Suite root | Purpose |
|---|---|---|
| T12.12.1 | `tests/T12_12_1_finite_decision` | Finite enumeration constructs a total decision procedure over Bool. |
| T12.12.2 | `tests/T12_12_2_ring_normalization` | Algebraic normalization proves a polynomial identity from selected Integer evidence. |

## Machine-readable manifest

`tests/manifest.json` records the same suite roots, file lists, IDs, and descriptions for test-runner integration.
