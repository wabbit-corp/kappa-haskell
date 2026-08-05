# Appendix T amendments for unified `derive` and canonical evidence

## Ready-to-insert changes for `Spec(108).md`

These amendments extend the standard harness only where ordinary diagnostics, type assertions, stage dumps, and existing
semantic-hash assertions are insufficient to observe the new feature. The individual `.kp` suites in this package are
normative examples of the added directives.

---

## 1. Amend §T.4 capability names

Add:

```text
deriveAutomation
deriveTrace
deriveCounterexamples
evidenceUniqueness
fallbackInstances
```

Meaning:

* `deriveAutomation` covers the required portable provider portfolio and derivation expressions.
* `deriveTrace` covers structured `DeriveRecord` queries and provider-provenance assertions.
* `deriveCounterexamples` covers checked counterexample records.
* `evidenceUniqueness` covers independent evidence-uniqueness certificates and construction-mode queries.
* `fallbackInstances` covers the ordinary-before-fallback resolution stage.

An implementation claiming the language feature standardized by the companion patch MUST advertise
`deriveAutomation`, `evidenceUniqueness`, and `fallbackInstances`. `deriveTrace` is mandatory for the standard harness even
when the implementation does not expose the trace through its ordinary command-line interface.

---

## 2. Amend §T.5.2 supported directives

Add:

```text
assertDeriveOutcome <qualified-declaration> <outcome>
assertDeriveProviderUsed <qualified-declaration> <provider-kind>
assertDeriveProviderNotUsed <qualified-declaration> <provider-kind>
assertDeriveInductionSubject <qualified-declaration> <zero-based-binder-index>
assertDeriveHelperCount <qualified-declaration> <relop> <n>
assertDeriveProofChecks <qualified-declaration>
assertDeriveProofMutationsReject <qualified-declaration>
assertDeriveCounterexample <qualified-declaration>
assertDeriveCycleContains <qualified-declaration> <goal-fragment>

assertDerivedInstance <trait-goal>
assertDerivedInstanceProviderUsed <provider-kind> for <trait-goal>
assertDerivedMember <member-name> for <trait-goal>
assertMemberCompletionMode <member-name> for <trait-goal> <explicit|ordinary-default|derived|auto-proposition>
assertDerivedSupertrait <supertrait-goal> from <child-trait-goal>
assertSupertraitCompletionMode <supertrait-goal> from <child-trait-goal> <direct|derived>
assertSharedDerivedEvidence for <trait-goal>

assertEvidenceUniquenessMode <trait-constructor-or-goal> <independent|sealed>
assertEvidenceUniquenessCertificateValid <trait-constructor>
assertEvidenceUniquenessCertificateMutationsReject <trait-constructor>
assertEvidenceConstructionMode <qualified-declaration> <existing|fresh-independent|instance-artifact|intrinsic>
assertEvidenceSemanticIdentityEquals <qualified-value-a> <qualified-value-b>
assertEvidenceSemanticIdentityDiffers <qualified-value-a> <qualified-value-b>
assertEvidenceArtifactFingerprintEquals <qualified-value-a> <qualified-value-b>
assertEvidenceArtifactFingerprintDiffers <qualified-value-a> <qualified-value-b>

assertFallbackSelected <trait-goal> <qualified-instance>
assertFallbackNotSelected <trait-goal>
assertOrdinaryInstanceSelected <trait-goal> <qualified-instance>
```

`outcome` is one of:

```text
Solved
Refuted
Counterexample
Ambiguous
Blocked
BudgetExhausted
Cycle
Unsupported
```

Portable `provider-kind` spellings are:

```text
exact
contractible
focused-introduction
normalization
logical-evaluation
reflection
no-confusion
hlevel
hedberg
arithmetic
universe
quantity
row
capture
set-congruence
path-congruence
function-extensionality
theorem-search
structural-induction
indexed-induction
mutual-induction
functional-induction
helper-lemma
dependent-inhabitation
superposition
hammer
parametricity
proof-transfer
finite-enumeration
external-certificate
fallback-instance
```

Rules:

* `<qualified-declaration>` resolves one source or generated declaration containing a derivation request. A declaration
  containing several requests is accepted only when the assertion is unambiguous; otherwise the implementation requires a
  stable request selector in the qualified spelling.
* `assertDeriveOutcome` checks the final `DeriveRecord`, not a transient provider result.
* Provider assertions inspect the selected proof's transitive provenance. Attempted but unused providers do not satisfy
  `assertDeriveProviderUsed`.
* `assertDeriveInductionSubject` uses the declaration's explicit source binder telescope. Generated helper binders are not
  counted.
* `assertDeriveHelperCount` uses the `relop` grammar of `assertTraceCount`.
* `assertDeriveProofChecks` independently rechecks the generated KCore and every reachable compact certificate.
* `assertDeriveProofMutationsReject` applies the standard mutation set to the generated goal, proof term or certificate,
  provider identity, dependency list, scope telescope, and provenance reference; every decisive mutation must fail KCore or
  certificate verification.
* `assertDeriveCounterexample` succeeds only when the final failure record contains a concrete checked witness whose
  instantiated proposition reduces to or is proved false. A random-test sample without a checked refutation does not count.
* `assertDeriveCycleContains` checks one normalized goal fragment in the reported cycle path; it does not parse rendered
  prose.

Instance assertions:

* `assertDerivedInstance G` succeeds only when the accepted instance artifact for normalized goal `G` was introduced by
  `instance G = derive` or declaration-level `derive G`.
* `assertDerivedInstanceProviderUsed provider for G` inspects whole-instance derivation provenance.
* `assertDerivedMember member for G` checks that the completed member slot was generated by a synthesized-member request or
  automatic omitted-proposition attempt.
* `assertMemberCompletionMode` checks the final source of one completed member slot.
* `assertDerivedSupertrait parent from child` succeeds iff completed child evidence contains the normalized parent
  projection and that slot was synthesized rather than supplied directly.
* `assertSupertraitCompletionMode` checks whether a completed supertrait slot was supplied/resolved directly or synthesized.
* `assertSharedDerivedEvidence for G` succeeds iff all direct requests and completion slots normalized to `G` consume one
  canonical goal node and one accepted semantic evidence object.

Evidence assertions:

* `assertEvidenceUniquenessMode` inspects the imported or local trait metadata after certificate verification.
* `assertEvidenceUniquenessCertificateValid` independently replays the certificate and its independence check.
* `assertEvidenceUniquenessCertificateMutationsReject` mutates, at minimum, the theorem goal, one field projection, one
  dependency identity, the foundation identity, the same-goal forbidden-dependency set, the provider identity, and the
  checker version. Every mutation must be rejected with `E_EVIDENCE_UNIQUENESS_INVALID` or
  `E_EVIDENCE_UNIQUENESS_CYCLE`, as appropriate.
* `assertEvidenceConstructionMode d existing` means `d` reused an accepted evidence value.
* `fresh-independent` means `d` constructed complete evidence under a verified independent uniqueness certificate.
* `instance-artifact` means the evidence was created by an ordinary, fallback, local, or generated instance artifact.
* `intrinsic` means an intrinsic solver produced it.
* Semantic identity assertions compare `EvidenceSemanticIdentity` after checking trust-profile compatibility.
* Artifact fingerprint assertions compare exact `EvidenceArtifactFingerprint` values.

Fallback assertions:

* `assertFallbackSelected G I` succeeds iff ordinary resolution found no surviving ordinary candidate and selected fallback
  artifact `I`.
* `assertFallbackNotSelected G` succeeds iff a fallback head matched but resolution selected local, intrinsic, or ordinary
  evidence before the fallback stage.
* `assertOrdinaryInstanceSelected G I` succeeds iff ordinary instance artifact `I` was selected before fallback
  consideration.

All trait goals and relation-indexed law goals in these directives are parsed with the ordinary type grammar and normalized
under the suite's ordinary visibility and opacity environment.

---

## 3. Amend §T.5.3 stage-dump assertions

Add:

```text
assertDeriveRecordPresent <checkpoint> <qualified-declaration>
assertEvidenceUniquenessRecordPresent <checkpoint> <trait-constructor>
assertFallbackSelectionRecordPresent <checkpoint> <trait-goal>
```

These assertions are valid for `KFrontIR.BODY_RESOLVE` and later checkpoints. At KCore they check retained provenance and
certificate metadata, not survival of a source-level `derive` syntax node.

---

## 4. Amend §T.7 incremental assertions

Add:

```text
assertStepArtifactFingerprintEquals <step-a> <step-b> <qualified-declaration-or-module>
assertStepArtifactFingerprintDiffers <step-a> <step-b> <qualified-declaration-or-module>
assertStepEvidenceSemanticIdentityEquals <step-a> <step-b> <qualified-value>
assertStepEvidenceSemanticIdentityDiffers <step-a> <step-b> <qualified-value>
```

Rules:

* artifact-fingerprint assertions compare exact reproducible artifact fingerprints, including generated proof bodies and
  provider identities;
* evidence-semantic-identity assertions compare the canonical semantic identity selected by §33.2.1;
* a proof-only change may preserve semantic identity while changing the artifact fingerprint; and
* cross-step comparison uses the same normalized declaration or evidence identity in each complete source snapshot.

---

## 5. Add a conformance-test inventory paragraph after §T.10

A portable conformance suite for unified `derive` SHOULD include separate suites for:

* expected-type and explicit-goal expression forms;
* the `forall` versus ordinary-arrow distinction;
* quantities, borrows, captures, and local refinement contexts;
* proof-relevant equality and `IsSet`-licensed merging;
* `Reflects`, Hedberg, and function extensionality;
* synthesized members and supertraits;
* instance-facet order independence and incomplete-self cycles;
* independent evidence uniqueness and forbidden circular certificates;
* first-class construction of h-level and law evidence;
* rejection of fresh sealed-coherent evidence in expression position;
* `Eq` derivation, invalid comparators, and shared `IsSet` evidence;
* the direct `Equiv` override and fallback `Eq -> Equiv` bridge;
* explicit relation law traits and multiple simultaneous relation values;
* `Preorder`, `PartialOrder`, corrected total `Ord`, and `Alternative` laws;
* no-confusion, arithmetic, finite domains, induction, and generated helper lemmas;
* opacity, theorem scope, local declaration scope, and incremental invalidation;
* semantic evidence identity versus exact artifact fingerprint;
* deterministic provider scheduling and fallback selection; and
* KFrontIR, KCore, certificate mutation, diagnostics, and proof materialization.

## 6. Standard fallback provider selector

For harness assertions only, the canonical standard-library fallback bridge from `Eq a` to `Equiv a` is selected by:

```text
std.prelude.eqToEquivFallback
```

This is a semantic provider selector, not a source-resolvable term or instance name.
