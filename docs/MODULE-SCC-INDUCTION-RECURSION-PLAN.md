# Module-Wide Declaration SCCs / Induction-Recursion - Implementation Plan

Status: **Specification applied; implementation planned (2026-08-01).**
`docs/Spec.md` contains the Spec(106)->Spec(107) patch from
`docs/higher-and-quotient-types/module-wide-declaration-SCCs-induction-recursion.diff`
and passes the repository specification validator. The patch applied cleanly at
working-tree Spec state `eabc67a7` (compiler commit `f1e4161b`); the bundle
manifest's recorded baseline hash names an upstream `Spec(106).md` snapshot
that differs from our file only in content the hunks did not touch. Twenty-
three section-id comments displaced or omitted by the patch were repaired
during application (`scripts/validate.py` is green).

The contract is materialized as a **190-suite** tree under
`tests/pending-import/module-scc-ir/`, imported verbatim from
`docs/higher-and-quotient-types/kappa-spec106-appendix-t-module-scc-ir-tests/`
with per-suite `-- STATUS(f1e4161b)` lines recording the audited baseline.
`scripts/validate_module_scc_ir_contract.py` fixes the manifest/tree contract
(suite count, categories, per-suite files, exact suite.ktest directive lists,
incremental step roots) and passes at 190 suites. Conformance fixtures whose
pinned outcomes the revision invalidates are rewritten to the Spec-107
contract and staged under `tests/pending-import/module-scc-ir/retargeted/`
(see §1.4). None of these suites is eligible for active conformance yet.

The revision makes top-level declaration order non-semantic, discovers
recursive groups from typed declaration *facets* instead of source adjacency,
admits ordinary inductive-inductive and inductive-recursive groups, replaces
source-order hidden phases with call-graph-derived phases, and extends KCore,
interfaces, hashes, incremental invalidation, and Appendix T accordingly.

This plan is the implementation authority for that contract. `ROADMAP.md`
contains only the short stage ledger.

## 0. Objective and boundaries

Implement the current `docs/Spec.md` contract so that:

1. top-level declaration shapes are module-wide scoped (§7.1A): an earlier
   declaration may reference a later one, duplicate detection runs over the
   whole effective module, and no declaration wins by source position;
2. a separate top-level signature pairs with its definition in either textual
   order and across selected fragments of one effective module, and a complete
   inline signature enables recursion exactly as a separate one does (§9.2,
   §36.12);
3. recursive grouping is inferred from semantic dependency edges over typed
   declaration facets (shape/header/formation/body/default-body/certificate/
   interface), with header strata, checking SCCs, and projected declaration
   groups classified acyclic / term-recursive / inductive /
   inductive-recursive (§9.5);
4. strict value and pattern-initializer cycles, header cycles, and unsupported
   mixed cycles fail closed with their dedicated diagnostics and one
   group-level root diagnostic instead of unresolved-name cascades;
5. singleton and joint inductive groups satisfy the group universe, greatest-
   fixed-point parameter-positivity, and nominal-closure rules; positivity
   failures use `kappa.data.strict-positivity` / `E_DATA_STRICT_POSITIVITY`
   (§10.4.1-§10.4.3);
6. ordinary inductive-inductive and inductive-recursive groups (the `Ctx`/`Ty`
   and `Code`/`decode` shapes) are admitted under the §10.4.4 rules -
   stratified headers, transparent total structural recursive operations,
   IR-admissible applications over available subjects, pointwise children,
   result externality - with joint eliminators and definitional
   equation reduction;
7. hidden phases are derived from the phase-constraint graph of recursive-call
   obligations, never from source order (§15.10), and structural descent uses
   the group relation `<_s,G` (§15.3);
8. KCore, KCoreText, interfaces, and semantic hashes represent declaration
   groups and inductive-group certificates explicitly, verify them
   independently, reject mutations, and are invariant under top-level
   declaration permutation (§30.2.0B, §33, §34); and
9. incremental compilation keys on declaration-group fingerprints, recomputes
   SCCs when generated syntax retargets dependencies, and never answers a
   query from a source-order prefix environment (§34.2).

The following are deliberate non-goals:

* Do not implement higher inductive types, quotient types, or coinduction.
  §10.5 reserves the stronger nominal-signature contract for them; this
  revision is their prerequisite, not their delivery.
* Do not introduce a `mutual` block, `let rec`, or any new grouping syntax.
  Groups are discovered, never declared.
* Do not introduce or infer a parameter/index partition anywhere - family
  telescopes stay whole, in KFrontIR, interfaces, KCore, and stage dumps.
* Do not let `assertTerminates`, legacy `assertTotal`, `assertReducible`, or
  `unsafeAssertProof` satisfy any formation, positivity, externality,
  structural-recursion, eliminator, or computation-rule obligation of an
  inductive-recursive group.
* Do not relax the source-location-sensitive forms: imports, fixities, local
  block scoping (§9.3.1), constructor order within one `data`, binder/field/
  default/pattern/branch and runtime evaluation order all stay ordered.
* Do not make general recursive value initializers lazy. Cyclic strict values
  stay rejected; only standardized guarded/productive features may ever admit
  them.

## 1. Current implementation audit

### 1.1 Existing substrate to keep

* `src/Kappa/Check.hs` already forms declaration SCCs with `Data.Graph`
  (`stronglyConnComp`), publishes completed group headers at SCC boundaries
  for universe-schema generalization, and implements the parameter-positivity
  greatest fixed point for singleton and mutually recursive data groups.
* `src/Kappa/Termination.hs` implements structural descent, visible measures,
  and the existing mutual-SCC acceptance the new §15.10 scheme must subsume.
* `src/Kappa/Pipeline.hs` implements the staged phase model (§34.2) the
  revision extends, including per-declaration query scheduling.
* `src/Kappa/CoreText.hs` has versioned, canonically ordered declaration
  serialization with certificate declarations preceding their consumers - the
  pattern `declaration-group` / `inductive-group-certificate` records follow.
* `src/Kappa/SemanticHash.hs` and `src/Kappa/Build/Types.hs` carry the
  interface-identity and fingerprint machinery the new group fingerprints
  extend.
* `src/Kappa/TestHarness.hs` hosts Appendix T; the directive registry pattern
  from the Nat/Fin campaign (typed directives over public compiler queries)
  is the template for the new group assertions.

### 1.2 Contract gaps

* Top-level scope is source-ordered: forward references to later declarations
  are unresolved-name errors, and recursion is enabled by a *preceding*
  separate signature only - inline signatures and signature-after-definition
  do not enable it.
* Signature/definition pairing is same-file only; §36.12 currently rejects
  cross-fragment pairing that Spec 107 requires.
* There is no facet model: declarations are single dependency vertices, so
  the formation/body/default-body distinctions of §9.5.2 (and their
  false-cycle avoidance) do not exist, and no declaration-group
  classification, features, or group root diagnostics are produced.
* `E_DECLARATION_HEADER_CYCLE`, `E_RECURSIVE_GROUP_UNSUPPORTED`,
  `E_DATA_STRICT_POSITIVITY`, `E_INDUCTIVE_RECURSIVE_INVALID` and families
  `kappa.declaration.recursive-group`, `kappa.data.strict-positivity`,
  `kappa.data.inductive-recursion` are unregistered.
  `E_RECURSIVE_VALUE_CYCLE` is already registered and emitted, but under the
  old `kappa.termination.failure` family (src/Kappa/Explain.hs,
  src/Kappa/Check.hs) - it must be re-homed to
  `kappa.declaration.recursive-group` with the §3.2.11A payload.
* Inductive-inductive and inductive-recursive groups are rejected; there are
  no recursive operations, IR contexts, pointwise children, externality
  checks, joint eliminators, or operation-equation conversion rules.
* Hidden phases are the removed canonical source-order scheme; the
  phase-constraint graph of §15.10 does not exist.
* KCore/KCoreText have no `CoreDeclarationGroup` or
  `InductiveGroupCertificate`; interfaces record the old explicit-group
  metadata; semantic hashes are not certified permutation-invariant.
* `TestHarness.hs` implements none of the new Appendix T directives
  (`assertDeclarationGroupClass` through
  `assertInterfaceContainsRecursiveOperationEquation`, `assertStageDumpHas`/
  `assertStageDumpJsonPointer`, and the cross-step hash/group assertions).

### 1.3 Pending contract baseline

`tests/pending-import/module-scc-ir/manifest.json` owns 190 suites:

| category | suites | owner stage | contract |
| --- | ---: | --- | --- |
| `01_scope_signatures` | 23 | MSI-1 | module-wide scope, pairing, inline-signature recursion |
| `02_facet_scc_termination` | 18 | MSI-2, MSI-5 | facet SCCs, strict value cycles, hidden phases |
| `03_inductive_inductive` | 20 | MSI-3 | joint positivity, sort stratification, mutual data |
| `04_inductive_recursive` | 37 | MSI-4 | recursive operations, IR admissibility, equations |
| `05_indexed_inductive_recursive` | 24 | MSI-4 | family-indexed IR, GADT refinement interplay |
| `06_feature_intersections` | 28 | MSI-4, MSI-5 | IR x quantities, effects, traits, universes |
| `07_interfaces_kcore_hashes` | 14 | MSI-6 | group records, certificates, interface retention |
| `08_incremental_and_permutation` | 12 | MSI-7 | permutation invariance, incremental invalidation |
| `09_diagnostics_recovery` | 14 | MSI-2..4 | group root diagnostics, payloads, recovery |

The 2026-08-01 audited run over all 190 suites with the `f1e4161b` compiler
reports **9 passed, 29 failed, 0 unsupported, and 152 harness errors**; each
suite carries its individual result in a `-- STATUS(f1e4161b)` line. The
harness errors are the new Appendix T directives the pre-MSI-0 harness does
not know (they must become `Unsupported` or implemented per the MSI-0 gate);
the failures are the semantic gaps of §1.2 (dominated by `E_NAME_UNRESOLVED`
forward references and rejected mutual/IR groups); the nine passes cover
narrow already-conforming behavior and are not promotion evidence.

### 1.4 Retargeted conformance fixtures

The Spec-107 breakage audit swept `tests/conformance` (4,130 fixtures; eight
themed sweeps examined 1,407 in depth, yielding 40 candidates, of which an
independent adversarial verification confirmed 36 and refuted 4). The 36
confirmed fixtures — 20 diagnostic re-homings (positivity to
`kappa.data.strict-positivity`/`E_DATA_STRICT_POSITIVITY`, strict value
cycles to `kappa.declaration.recursive-group`/`E_RECURSIVE_VALUE_CYCLE`,
unsigned recursion to `E_MISSING_EXPLICIT_SIGNATURE`), 13 invalidated
premises (preceding-signature mechanics, source-order grouping, old hidden
phases), and 3 outcome flips (top-level forward references §7.1A now
accepts) — are rewritten to the new contract and staged under
`tests/pending-import/module-scc-ir/retargeted/` (34 single-file fixtures
plus 2 directory suites), each with a provenance comment naming its original
conformance path and a `-- STATUS(f1e4161b)` line; the retargeted baseline
is 12 passed / 5 failed / 0 unsupported / 19 harness errors (the harness
errors pin not-yet-registered Spec-107 codes and families). They are owned by the stage
that implements their area and promote back to their original directories at
MSI-8 at the latest; the twelve comment-only retargets whose directives are
already green SHOULD be returned at MSI-0 so the active gate keeps their
coverage. Per-file dispositions:
`tests/pending-import/module-scc-ir/retargeted/README.md`.

## 2. Architectural invariants

### 2.1 Order-freedom is end-to-end or it is a bug

Module-wide scope, SCC discovery, hidden phases, KCore serialization,
interface identity, and semantic hashes must all be invariant under top-level
declaration permutation *together*. A single source-order tiebreak anywhere
(worklist order, map iteration, first-wins duplicate handling, source-offset
phase assignment) reintroduces the observable order-dependence the revision
abolishes. Every tiebreak must be by stable semantic identity.

### 2.2 Facets exist to prevent false cycles

The facet graph is not bookkeeping: `formation`-vs-`default-body` separation
is what keeps "constructor default calls a function that consumes the formed
type" out of induction-recursion. Collapsing facets back into one vertex per
declaration would misclassify these programs and must be treated as a
correctness regression, not a simplification.

### 2.3 Groups are checked jointly and published atomically

No source-order prefix of a checking SCC is ever accepted, no constructor or
equation escapes from a rejected group, and a failed group yields one root
diagnostic with the complete group payload - never a cascade of
unresolved-name errors from a partial environment.

### 2.4 Induction-recursion admits nothing by accident

A recursive operation is admitted only with a complete explicit signature,
transparency, purity, static evaluability, structural totality on selected
subjects, and a certified `G`-external result and equations. Unsafe
assertions never substitute for any of these. The externality check is
semantic: opacity or an unsolved member is not evidence.

### 2.5 Certificates are the trust boundary

Group structure, positivity signatures, structural-child derivations,
operation equations, phase constraints, and eliminators are replayed by the
independent KCore checker from serialized inputs. A forged or stale
inductive-group certificate fails closed; downstream KBackendIR is never
built from an unverified group.

## 3. Stages, ordering, and gates

### MSI-0 - Freeze the contract and add harness observability

Deliverables:

* keep the 190-suite manifest and `scripts/validate_module_scc_ir_contract.py`
  authoritative for the staged tree, extending the validator to cover
  `retargeted/` provenance lines;
* add typed `TestHarness` directives for the full new Appendix T surface:
  `assertDeclarationGroupClass`, `assertDeclarationGroupMembers`,
  `assertDeclarationGroupFacets`, `assertDeclarationDependencyEdge`,
  `assertDeclarationGroupFeature`, `assertHeaderStratum`,
  `assertInductiveGroupCertificateValid`,
  `assertInductiveGroupCertificateMutationsReject`,
  `assertNoParameterIndexPartition`, `assertRecursiveOperation`,
  `assertRecursiveOperationEquation`, `assertStructuralChildEdge`,
  `assertHiddenPhase`, `assertPhaseConstraint`,
  `assertInterfaceContainsDeclarationGroup`,
  `assertInterfaceContainsRecursiveOperationEquation`,
  `assertStageDumpHas`, `assertStageDumpJsonPointer`, and the cross-step
  `assertStepSemanticHash*` / `assertStepInterfaceHash*` /
  `assertStepDeclarationGroup*` forms - routed through the same public
  compiler queries as tooling, never a test-only second implementation;
* register the three diagnostic families and five portable aliases with their
  §3.2.11A payload schemas;
* directives whose backing queries are not yet implemented report
  `Unsupported`, not `HarnessError`, so the baseline converts from 152
  harness errors to unsupported/fail as stages land.

Gate:

* every pending directive parses; unavailable queries report `Unsupported`;
* the validator still reports exactly 190 manifest suites plus the
  retargeted tree with no unowned files.

### MSI-1 - Module-wide declaration shapes and signature pairing

Deliverables (§7.1A, §9.1, §9.2, §36.12):

* collect top-level declaration shapes from every selected fragment before
  body checking (`DECLARATION_SHAPES` becomes module-wide);
* order-independent duplicate/binding-group detection over the effective
  module;
* signature/definition pairing in either order and across fragments, with
  the agreement rules for double signatures and modifiers;
* module-wide top-level reference resolution while imports/fixities/locals
  stay location-sensitive;
* inline complete signatures enable recursion; omitted-signature inference
  restricted to declarations established acyclic, with reclassification
  rejection when late dependencies appear.

Primary files: `src/Kappa/Check.hs`, `src/Kappa/Pipeline.hs`,
`src/Kappa/Syntax.hs`, `src/Kappa/Build/Types.hs`.

Gate: all 23 `tests/pending-import/module-scc-ir/01_scope_signatures/`
suites pass for their stated reasons; the retargeted forward-reference and
signature-order fixtures pass; no previously green conformance test regresses.

### MSI-2 - Facet graph, header strata, and checking SCCs

Deliverables (§9.5, §15.16):

* typed declaration facets and semantic dependency edges (§9.5.1-§9.5.2)
  with provenance, including generated-syntax recomputation;
* header graph, transparent-alias-aware acyclicity, header strata
  (`E_DECLARATION_HEADER_CYCLE`);
* checking-SCC formation at `BODY_RESOLVE`, declaration-group projection,
  classification, and features;
* strict value/pattern cycle rejection (`E_RECURSIVE_VALUE_CYCLE`),
  unsupported mixed cycles (`E_RECURSIVE_GROUP_UNSUPPORTED`), recursive
  members without complete signatures (`E_MISSING_EXPLICIT_SIGNATURE` with
  full-SCC payload);
* joint checking with atomic publication and group root diagnostics
  replacing incomplete-environment cascades;
* stage dumps expose edges, groups, strata, and classifications under the
  standardized JSON keys.

Primary files: `src/Kappa/Check.hs`, `src/Kappa/Pipeline.hs`,
`src/Kappa/Diagnostic.hs`.

Gate: the `02_facet_scc_termination/` SCC and value-cycle suites and the
`09_diagnostics_recovery/` group-root-diagnostic suites pass; a constructor
default calling a consumer of the formed type is classified `inductive`, not
`inductive-recursive`.

### MSI-3 - Joint inductive groups and positivity

Deliverables (§10.4-§10.4.3):

* joint family-header elaboration from header strata; mutual and
  inductive-inductive data in any source order;
* joint constructor universe checking over whole family telescopes (no
  parameter/index split);
* group greatest-fixed-point parameter positivity generalized to
  current-group heads, with the recursive-operation conservative rule;
* `kappa.data.strict-positivity` / `E_DATA_STRICT_POSITIVITY` with the
  §3.2.11A payload (polarity path, unfolded aliases, signatures consulted);
* nominal signature closure and check-order integration (§10.4.3.2 list).

Primary files: `src/Kappa/Check.hs`.

Gate: all 20 `03_inductive_inductive/` suites pass; existing positivity
conformance fixtures keep their verdicts under the new family/alias;
`Ctx`/`Extend`/`Ty` stratifies regardless of declaration order.

### MSI-4 - Induction-recursion

Deliverables (§10.4.4, §11.1.2.3A addition, §31.1 iota rule):

* recursive-operation identification and admissibility (complete signature,
  transparent, pure, static, structural subjects, externality);
* IR contexts, available subjects, saturation checks, pointwise children,
  and the rejection list of §10.4.4.3;
* group structural relation `<_s,G` and recursive-call certification;
* result/equation externality checking (§10.4.4.6);
* joint eliminators, induction hypotheses (direct and pointwise), and
  definitional equation reduction gated on certificate validity;
* interface-reachable private operation retention.

Primary files: `src/Kappa/Check.hs`, `src/Kappa/Termination.hs`,
`src/Kappa/Eval.hs`, `src/Kappa/CoreLint.hs`.

Gate: the canonical `Code`/`decode` suite and all 37 + 24
`04_inductive_recursive/` and `05_indexed_inductive_recursive/` suites pass;
the `06_feature_intersections/` suites owned here pass; every negative
(unsaturated, unavailable subject, non-external result, unsafe-assertion
justification) rejects with `E_INDUCTIVE_RECURSIVE_INVALID` and the correct
reason value.

### MSI-5 - Termination reforms

Deliverables (§15.3, §15.4, §15.10, §15.11):

* structural descent over `<_s,G` including tuple/closed-record projections
  and certified pointwise children;
* the phase-constraint graph and canonical longest-path phase assignment,
  replacing source-order phases end-to-end (certificates included);
* `decreases`-uniformity restricted to computational SCC members;
* minimum-acceptance extension to §10.4.4 groups.

Primary files: `src/Kappa/Termination.hs`, `src/Kappa/Check.hs`.

Gate: remaining `02_facet_scc_termination/` phase suites pass; every mutual
group accepted before the revision is still accepted (the call-graph scheme
must certify at least the old canonical assignments); phase values reported
by `assertHiddenPhase` are permutation-invariant.

### MSI-6 - KCore, interfaces, and hashes

Deliverables (§30.2.0B, §31.1, §33, §34.1, §34.3):

* `CoreDeclarationGroup` and `InductiveGroupCertificate` in KCore and
  KCoreText (grammar, canonical emission order, round-trips);
* independent checker verification of the full §30.2.0B obligation list and
  fail-closed mutation rejection (`E_INDUCTIVE_RECURSIVE_INVALID`,
  `E_KCORE_SCHEMA_CERTIFICATE_INVALID`, `E_CHECKPOINT_VERIFICATION_FAILED`);
* interface `DeclarationGroupSummary` / `InductiveGroupCertificateSummary`
  with private-but-reachable operation retention;
* permutation-invariant Easy/Hard hashes and interface identity;
* declaration-group / header / body / interface fingerprints.

Primary files: `src/Kappa/Core.hs`, `src/Kappa/CoreText.hs`,
`src/Kappa/CoreLint.hs`, `src/Kappa/SemanticHash.hs`,
`src/Kappa/Build/Types.hs`.

Gate: all 14 `07_interfaces_kcore_hashes/` suites pass, including
certificate-mutation rejection; KCoreText round-trips retain group records.

### MSI-7 - Incremental compilation and scheduling

Deliverables (§34.1.1, §34.2.x):

* invalidation keyed on `DeclarationGroupFingerprint`; edits that merge or
  split SCCs invalidate exactly the affected connected component;
* SCC recomputation when macro/derive/splice output retargets dependencies,
  before any published result;
* query rules: module-wide shape forcing, no source-order-prefix answers,
  blocked-result reporting;
* interface readiness for IR groups (heads alone are insufficient).

Primary files: `src/Kappa/Pipeline.hs`, `src/Kappa/Build/Types.hs`.

Gate: all 12 `08_incremental_and_permutation/` suites pass, including the
cross-step hash/group assertions.

### MSI-8 - Promotion, adversarial audit, and closeout

Deliverables:

* promote the 190-suite tree to
  `tests/conformance/spec-coverage/module-scc-ir/` and return every
  `retargeted/` fixture to its original conformance home, atomically with
  manifest/validator updates;
* adversarial audit: permutation fuzzing over accepted modules (hash and
  verdict invariance), forged-certificate probes, generated-syntax SCC
  retargeting, cross-fragment pairing edge cases, IR externality
  smuggling attempts (closures, aliases, erased fields, proof objects);
* unit/property tests for the facet-graph builder, GFP positivity over
  groups, phase-constraint assignment, and certificate replay;
* flip the ROADMAP ledger and record residual gaps as tracked issues.

Gate: zero pending module-scc-ir suites; full conformance and unit suites
green; interpreter/C/LLVM parity unaffected; both spec validators and both
contract validators green.

## 4. Dependency order

| stage | depends on | may proceed in parallel with |
| --- | --- | --- |
| MSI-0 | frozen spec and staged tree | early MSI-1 design |
| MSI-1 | MSI-0 observability for final promotion | MSI-2 facet-model design |
| MSI-2 | MSI-1 module-wide shapes | MSI-3 positivity generalization design |
| MSI-3 | MSI-2 header strata and joint checking | early MSI-4 operation admissibility |
| MSI-4 | MSI-2, MSI-3; MSI-5 structural relation | late MSI-5 |
| MSI-5 | MSI-2 SCCs (phase graph), MSI-4 for `<_s,G` closure | MSI-6 grammar design |
| MSI-6 | MSI-2..5 certificate payloads | early MSI-7 fingerprint plumbing |
| MSI-7 | MSI-2 groups, MSI-6 fingerprints | none at consuming checkpoints |
| MSI-8 | MSI-0 through MSI-7 | none |

The critical path is MSI-1 -> MSI-2 -> {MSI-3, MSI-5} -> MSI-4 -> MSI-6 ->
MSI-7 -> MSI-8. MSI-0 starts first because unknown harness directives
currently hide whether later failures occur at the intended checkpoint (152
of 190 baseline results are harness errors).

## 5. Correctness risks

* **Order-dependence resurrection (highest):** any worklist, map-iteration,
  or first-wins choice that survives into group formation, phase assignment,
  or serialization silently violates §9.5.8/§33. Property-test permutation
  invariance from MSI-2 onward, not only at MSI-8.
* **False cycles from facet collapse:** merging facets to simplify the graph
  turns legal default-body/back-edges into bogus inductive-recursive groups
  and rejects today-legal programs. The §9.5.2 false-cycle examples are gate
  fixtures.
* **Externality smuggling:** an operation result hiding a group occurrence
  behind a closure, alias, associated member, erased field, or proof object
  breaks positivity soundness end-to-end. The checker must normalize
  semantically, and MSI-8 probes it adversarially.
* **Phase-scheme regression:** the call-graph scheme must accept everything
  the removed source-order scheme accepted; otherwise green conformance
  breaks. Verify on the existing mutual-recursion corpus before deleting the
  old path.
* **Cascade regressions:** group root diagnostics replace unresolved-name
  cascades; recovery-path tests (`09_diagnostics_recovery/`) guard against
  double-reporting or lost payloads.
* **Certificate self-trust:** replaying group certificates with the emitting
  code instead of the independent checker defeats the trust boundary exactly
  as it would for arithmetic certificates.
* **Incremental staleness:** provisional groupings observable through
  queries, or fingerprints missing a decisive field (e.g. phase constraints),
  yield wrong reuse. Cross-step suites are the gate.

## 6. Verification

During every stage:

```sh
python3 scripts/validate.py docs/Spec.md
python3 scripts/validate_module_scc_ir_contract.py
python3 scripts/validate_nat_fin_contract.py
cabal test
```

Focused contract run:

```sh
$(cabal list-bin exe:kappa) test \
  tests/pending-import/module-scc-ir
```

Closeout additionally requires the promoted conformance path, KCoreText
round-trip and certificate-mutation fixtures, permutation fuzzing, and the
existing native parity and performance gates.

## 7. Spec anchors

* §3.1.4, §3.2.11A: portable aliases, group/positivity/IR diagnostic
  families and payloads.
* §7.1A: module-wide scope of top-level declarations.
* §9.1, §9.2, §9.5: definitions, signature pairing, facets, strata, SCCs,
  strict value cycles, source-order invariance.
* §10.4-§10.4.4: joint universe checking, strict positivity, nominal
  closure, inductive-inductive and inductive-recursive groups.
* §11.1.2.3A: recursive schemas across IR groups.
* §15.2-§15.4, §15.10, §15.11, §15.16: minimum acceptance, structural
  descent, phase-constraint hidden phases, `decreases`, group elaboration.
* §30.2.0B, §31.1: KCore group records, certificates, equation reduction.
* §33.1.3, §34.1-§34.3, §36.12: hashes, fingerprints, phases, stage dumps,
  interfaces, fragments.
* Appendix T (§T.5.x, §T.7): declaration-group assertions, stage-dump
  pointers, cross-step assertions; checklist items "Module-wide declaration
  scope and grouping", "Ordinary inductive groups", "Ordinary
  induction-recursion".
* `tests/pending-import/module-scc-ir/README.md` and `manifest.json`: the
  staged contract tree and its per-suite normative targets.
