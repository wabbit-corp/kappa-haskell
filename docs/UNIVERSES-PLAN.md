# Universes / First-Class Levels / Generalization / Nominal Variance / KCoreText — Implementation Plan

Status: **U-E, U-F, and U-G complete for the current language contract (2026-07-24).** `docs/Spec.md` includes the previous
parametric-package, explicit universe-schema, principal-inference, complete `TypeLevel`
algebra, observation-dependency, and KCoreText contracts plus declaration-universe roles,
nominal-signature closures, independently verified action certificates, and explicit KCore
`schemaLift` nodes. The latest patch additionally admits stable total first-class level terms,
separates constructor normalization from rigid entailment and portable meta inference, makes
declaration constraints erased proof binders, specifies rigid declaration generalization and
same-or-lower recursive schemas, and adds arithmetic KCoreText replay and solver versioning.

The working tree has advanced substantially beyond the 2026-07-19 review. It contains
implemented explicit global/local schemas, principal SCC inference,
commutative natural-sum `TypeLevel`, finite observation dependencies, parametric package
sealing, standard schema families, replayable structural level evidence, nominal role
inference, schema action summaries, explicit `CSchemaLift`, and the complete KCoreText grammar.
The focused universe ledger, full conformance/unit gate, native parity, RC detector lanes,
package builds, and performance gate are green. The current full conformance result is 3,788
passed, zero failed, and ten explicitly unsupported optional/future capabilities (3,798 total):
eight future variance suites and two optional compact Nat/Fin layout suites.
The focused owner gates are
47/47 ordinary/parametric/KCoreText, 88/88 package/schema (71 imported plus 17 strengthening),
34/34 current variance with eight future HIIT/HIRT/QIT/QIIT cases capability-gated, and 72/72
under the active first-class-level root (67 bundle contracts plus 5 implementation-strengthening
contracts).

The 2026-07-24 closeout additionally passed the spec and universe-ledger validators, focused
C/LLVM parity with the LLVM RC gate, poison-on-free RC, TSan RC, and native package test
binaries for Railyard, Voxelcraft, and Delve. Measured cold package builds were 7.85s, 9.17s,
and 42.36s respectively. Delve had previously taken roughly five minutes because every solver
update eagerly rewrote the complete installed level-substitution map. Assignment installation
now retains a substitution graph plus reverse dependencies, preserving semantic immutability
while revisiting only affected term metas; the same Delve build remains finite and produces
zero Perceus findings.

The preceding clean historical closeout recorded 2,715/2,715 active conformance cases, 43 universe
cases, 25 parametric-witness cases, solver/KCore/interface unit contracts, and the complete
native C/LLVM/RC/poison/TSan/package/performance gate. The first two design bundles contribute
118 independent suites, now active under
`tests/conformance/spec-coverage/ordinary-parametric-kcoretext/` and
`tests/conformance/spec-coverage/parametric-packages-universe-schemas/`; the latter root also
contains 17 active implementation-strengthening suites. The variance bundle adds 42 suites:
24 accepted programs and 18 required rejections. Of those, 34 exercise current nominal data,
interfaces, and KCoreText, while 8 are capability-gated future HIIT/HIRT/QIT/QIIT contracts.
U-F0 owns the resulting active ledger of 160 bundle suites plus the 17 strengthening suites.
The new first-class-level bundle contributes 67 additional suites: 47 accepts and 20 rejects,
split into 29 positive source, 17 negative source, 13 direct solver, and 8 KCoreText suites.
Its manifest, catalog, validator, and READMEs agree on 67. Those 67 plus 5 explicitly catalogued
implementation-strengthening contracts are active under
`tests/conformance/spec-coverage/first-class-levels-solver-generalization/`.

**Decision (recorded): the current `docs/Spec.md` is normative.** Completed U-P through U-D
work is retained only as the regression baseline summarized above. Phase E records the completed
implementation of the previous follow-up design. Phase F records the implemented certified
nominal-family implementation. Phase G applies the first-class-level and solver-generalization
delta. Where implementation, plan history, active tests, pending tests, and current
spec disagree, the current spec wins; tests are reclassified explicitly and never weakened
silently.

**Decision (recorded): observation, formation, and quantity are separate.** Every binder and
dependent field has independent observation mode, quantity, access mode, and explicitness.
Explicit `parametric` observation is legal for every well-formed domain. Parametric-kind
recognition controls defaults and eligibility for parametric Pi/Sigma formation; an explicit
observation tag alone does not select impredicative formation. Quantity controls demand and
erasure only. `E_PARAMETRIC_BINDER_DOMAIN` and its family are removed.

**Decision (recorded): bare `Type` floats and declarations generalize universes.** Each bare
`Type` introduces a fresh universe metavariable, grouped annotations share one, and remaining
observable metas are processed by the portable principal-inference algorithm. Minimizable
result metas take a certified principal solution only inside the assignable fragment;
out-of-fragment cases require annotation. Remaining legal generalizable metas form an explicit
or hidden declaration universe telescope. Local declaration SCCs use the same algorithm.

**Decision (recorded): declaration universe schemas are source-visible when requested.** The
optional `.{u, v}` schema appears after a declared name, is complete when written, and is
instantiated with the same syntax. Schema parameters are rigid static declaration identities,
not term-level `TypeLevel` binders or runtime captures.

**Decision (recorded): nominal declaration schemas have certified roles.** Each universe
parameter of a nominal signature block has effective role `invariant`, `covariant`, or
`irrelevant`; there is no contravariant role. Omitted roles are inferred by a deterministic
greatest fixed point. An explicit role may tighten the inferred role but may not loosen it.
Roles govern only cross-instance comparison of one fully saturated nominal family and remain
independent of positivity, observation mode, quantity, formation, proof relevance, and erasure.

**Decision (recorded): nominal cumulativity is explicit in KCore.** Different role-related
family instances are not judgmentally equal. Surface expected-type checking may insert a
`schemaLift`, but KCore must retain the source/target schemas, aligned full family arguments,
per-role evidence, and a verified nominal-signature action certificate. Lifts are
representation identity and erase before KBackendIR; a transformation requiring wrappers,
mapping, allocation, user code, or contravariant conversion forces `invariant`.

**Decision (recorded): certificates are an independent trust boundary.** Every nominal family
has a normalized signature closure and checked effective role vector. Local certificates are
recomputed from that closure; imported opaque families may lift only through a supported
verified interface summary. A stable ID or printed role vector is never proof. Missing, stale,
or unsupported summaries degrade to all-invariant behavior.

**Decision (recorded): `TypeLevel` is ordinary runtime-capable data with a complete algebra.**
`std.typelevel` owns the opaque `Level (omegaCoefficient : Nat) (finiteRemainder : Nat)`
representation. Addition is the commutative natural/Hessenberg sum on `omega*c+n`, not ordinal
addition. The prelude provides the required monoid, commutative monoid, ordered-additive, and
join-semilattice evidence and checked laws. The universe solver recognizes standard semantic
identities through a certified normalization bridge.

**Decision (recorded): every stable total `TypeLevel` term may index `Type`.** Standard
operations decompose into solver constructors; any other admissible term becomes an
alpha-stable rigid neutral atom. Level admissibility is checked after expression lifting and
requires typing, totality, lifetime stability, scope, KCore serialization, and absence of
unresolved metas at rigid checkpoints.

**Decision (recorded): level solving has three contracts.** AC/ACI constructor normalization
is deterministic but intentionally incomplete for semantic equality. Rigid entailment is exact
paired QF Presburger entailment. Portable metavariable inference implements only the specified
assignable fragment and reports solved, unsatisfiable, no-principal, out-of-fragment, and
blocked outcomes without implementation-specific guessing.

**Decision (recorded): parametric witness packages may be unbounded.** A package containing an
ordinary first-class level and a parametric `T : Type level` is small because the witness field
seals ordinary observation. An ordinary type-code field or any later ordinary payload depending
on `T` still needs an external ceiling. `TypeBelow` and `TypeAtMost` use declaration schemas,
not term-level universe Pis.

**Decision (recorded): KCore observation is an independently checked dependency calculus.**
The checker computes a finite origin set `D`; ordinary sinks require `D = {}`, parametric sinks
accept any `D`, and application/let/projection/construction/case follow the equations in
§30.2.0. KCoreText never serializes a trusted precomputed dependency set.

**Decision (recorded): declaration constraints are ordinary erased proof binders.** Generated
constraints are inserted after the declaration schema, deduplicated by semantic level equality,
and passed explicitly in KCore application spines. `DeclarationConstraintSummary` is a derived
cache, not a second source of authority.

**Decision (recorded): KCoreText is complete and explicit.** Global and local uses carry
universe instantiations, declaration constraints print as ordinary erased binders, generic
values are typed, extensions are declared, and cumulative lifts cite scoped proof binders or
independently verified level certificates. Arithmetic replay is the complete rigid-entailment
certificate form. Stable IDs and proof-object allocation identities are never proof.

**Decision (recorded): `forall` is implicit parametric quantification.** `forall A. T` lowers
to `(@parametric 0 A : Type ?u) -> T`. Explicit ordinary observation is written
`forall (ordinary A : Type). T`. Existing tests that pin the older explicit/implicit
asymmetry are migration inputs, not compatibility requirements.

**Decision (recorded): generalization occurs only at declaration boundaries.** Candidate
variables are replaced by rigid parametric binders and the complete declaration or SCC is
rechecked. Generalization never moves `forall` through a type constructor; such interchange
requires explicit `PreservesParametricForall` evidence. Monadic, pattern, lambda, handler, and
comprehension binders do not create fresh declaration polymorphism.

**Decision (recorded): recursive schema calls are same-or-lower.** Identity calls may omit
schema arguments; every non-identity call is explicit and requires complete signatures. A
strict schema decrease may contribute a static termination edge, while first-class
`TypeLevel` recursion remains ordinary dependent recursion.

## Implemented baseline and first-class-level delta (2026-07-21)

The pipeline remains lex -> parse -> resolve -> elaborate/check -> KCore -> KBackendIR -> C/LLVM.
The current implementation state is:

* `Kappa.Level` carries canonical neutral KCore-term identities, componentwise
  natural/Hessenberg addition, AC/ACI constructor normalization, exact paired-Presburger rigid
  entailment, and the portable principal-inference outcome lattice with checked witnesses.
* `Check.hs` performs declaration-boundary and local-SCC universe generalization, rigid
  rechecking, exact expected-type retention, same-or-lower recursive schema checking,
  bounded schema reification, direct schema lifts, and frozen `Monotone` evidence selection.
  Monadic and other non-declaration binders do not create fresh declaration polymorphism.
* `DeclarationUniverseTelescope` carries level parameters only. Generated declaration
  constraints are implicit erased `LevelLe` proof binders in Core. KCoreText declaration
  grammar has no side constraint block or constraint-index evidence; summaries and certificate
  dependency sets are derived and independently replayed.
* `Kappa.ObservationDeps` implements the finite dependency calculus used by rigid
  generalization rechecking and rejects parametric escape through ordinary sinks.
* `Kappa.NominalVariance` builds normalized signature closures, infers roles by fixed point,
  freezes selected standard/local/global `Monotone` evidence, and independently verifies
  schema action certificates. KCore retains explicit `CSchemaLift` nodes until verified
  representation-identity erasure.
* KCoreText supports stable neutral level terms, arithmetic and structural certificate replay,
  proof-irrelevant lift hashing, schema certificates/lifts, and all five independent semantic
  version fields.
* `Kappa.TestHarness` implements the §T.5.2 solver/generalization/recursive-schema and KCore
  evidence/hash directives. The exact 67-suite first-class-level tree is active and green.

## Phase E — reconciled working-tree implementation

Phase E owns the implemented pre-variance design. The original 118 leaves plus
17 local strengthening suites are active and green, and the clean full closeout required by E9
has passed. Phase F must preserve these contracts and may not make an old failure disappear by
treating nominal variance as general conversion.

- **U-E0 — 118-suite contract ledger and baseline (implemented; ledger green).** The 47 first-bundle
  leaves and 71 follow-up leaves are active under separate conformance roots with their original
  manifests; 17 strengthening leaves are recorded in `extension-manifest.json`.
  `scripts/validate_universe_contract.py` validates the resulting 47 + 71 + 17 inventory.
  The clean build/full-suite closeout is recorded, and no suite was promoted through an
  expectation weakening.

- **U-E1 — observation/formation separation (implemented; focused gate green).** Retain the explicit `ObservationMode` plumbing,
  but allow explicit parametric observation over every well-formed domain and borrowed access.
  Delete `E_PARAMETRIC_BINDER_DOMAIN` and its recovery-to-ordinary path. Preserve parametric-kind
  defaulting, split the Pi/Sigma formation judgment from binder observation mode, and make
  constructor-size/no-bump checks consume that judgment rather than raw observation. Grouped
  explicit binders share one annotation and one bare-`Type` meta. *Gate:* surface parser/pretty
  properties; `parametric_non_kind_domain_allowed`; ordinary-`0` predicative controls;
  higher-kinded and constructor-default formation suites.

- **U-E2 — commutative `TypeLevel` algebra end to end (implemented; focused gate green).** Replace ordinal `LAdd` normalization,
  symbolic Presburger translation, comparison reference semantics, evaluator/interpreter
  primitives, C/LLVM/runtime lowering, and closed-value encodings with natural/Hessenberg sum:
  `(ac,an)+(bc,bn)=(ac+bc,an+bn)`. Implement the opaque source definitions and checked
  `AdditiveMonoid`, `CommutativeAdditiveMonoid`, `OrderedAdditive`, and `JoinSemilattice`
  instances plus every required theorem. Remove old direction-sensitive tests. *Gate:* closed
  equations including `1 + omega = omega + 1`, algebra laws, exhaustive small-expression
  solver/runtime differential, mixed static/runtime use, and interpreter/C/LLVM parity.

- **U-E3 — explicit schemas and principal SCC inference (implemented; focused gate green).** Add `universeSchema?` after names in
  term signatures/definitions, aliases, data, constructors, traits, instances, effects,
  projections, module-signature members, and local declarations; add explicit reference
  instantiation and alpha-equivalent signature/definition checks. Represent schema parameters
  as rigid static identities and enforce arity/scope diagnostics. Replace all-meta
  generalization with generalizable/minimizable roles, unique least solutions, no-principal
  rejection, and one solve per top-level or local SCC. Local references instantiate local
  telescopes freshly. *Gate:* schema syntax/arity/scope, Phantom/Box/chooseType principal
  results, independent-meta and traversal-order properties, local generalization/recursion,
  interface and semantic-hash round trips.

- **U-E4 — parametric packages, equality, data grammar, and standard schemas (implemented; focused gate green).** Make a
  parametric field a true sealing boundary during package/data construction. Accept an
  unbounded `(level, parametric T : Type level)` package and projection/repackaging; reject
  ordinary reification, an ordinary `T`, and a later ordinary payload without a ceiling.
  Replace `TypeBelow`/`TypeAtMost` with `.{u}` schemas. Define `(=).{u}`, `Dec.{u}`,
  `pathInd.{u,v}`, and `subst.{u,v}` through the ordinary elaborator with parametric endpoints
  and no privileged bypass. Complete data/constructor/grouped-binder grammar and explicit
  constructor instantiation. *Gate:* all package, record, data, equality, sameDynRep, and
  proof-bounded-schema leaves; user-defined equality follows the same checker path as prelude
  equality.

- **U-E5 — exact KCore observation dependency calculus (implemented; focused gate green).** Introduce stable
  `ParametricOrigin` identities and compute finite dependency sets in checkpoint typing.
  Implement the normative variable/global, binder, application `propagate`, lambda, let,
  substitution, static-code construction, sealing, projection, case, alias, conversion, and
  lift equations. Remove `termObservation`'s single-mode approximation and every frontend side
  table consulted as authority. Record only derived result summaries needed by interfaces;
  KCoreText never supplies trusted sets. *Gate:* constant parametric application returns an
  ordinary result; dependent/higher-kinded partial application remains parametric; alias,
  projection, pattern, record, constructor, and nested-application laundering all reject;
  weakening/substitution/reduction property tests pass.

- **U-E6 — deterministic assumptions, lifts, and level-certificate checking (implemented; focused gate green).** Reject every
  inconsistent recognized level-assumption context: strict cycles use
  `E_UNIVERSE_SELF_CONTAINMENT`, all other inconsistencies use
  `E_UNIVERSE_CONSTRAINT_UNSATISFIABLE`. Preserve explicit lifts, but replace opaque solver
  stable IDs with scoped local proof refs, normalized declaration-constraint indices, or
  independently checked `LevelCertificate` proof trees. Substitute levels and evidence
  together. *Gate:* direct/transitive inconsistency leaves, forged certificate and bad-lift
  negatives, certificate proof-node unit tests, and identity/composition/erasure properties.

- **U-E7 — complete pre-variance KCoreText (implemented; focused gate green).** Remove free `KDUniverse`; introduce `globalUse` carrying
  optional instantiation everywhere, including constructor, case, evidence, static-object, and
  associated-member uses. Give local definitions telescopes/constraints and explicit `letrec
  ... in`; use typed generic payload wrappers; require one compatible extension declaration;
  add constraint-index and certificate evidence forms. Canonicalize SCCs topologically,
  members by stable identity, and certificates before use. Verify every global/local schema
  instantiation and every proof tree before checkpoint acceptance. *Gate:* all direct KCoreText
  leaves, local-schema and constructor-instantiation round trips, forged-certificate rejection,
  semantic-hash equality, and byte-identical canonical reprint.

- **U-E8 — artifacts, prelude, diagnostics, and migration (implemented; focused gate green).** Serialize explicit/inferred
  global schemas, emitted local schemas, normalized constraints, every binder/field mode,
  dependency summaries, and verified certificate identities. Update static facets, instance
  heads, constructor metadata, generated helpers, stage dumps, and semantic hashes. Remove all
  obsolete diagnostics and term-indexed standard-family declarations from source/prelude/tests.
  Reclassify historical fixed-Type0, ordinal-addition, invalid-parametric-domain, unbounded
  package, and equality-endpoint fixtures with a replacement ledger. *Gate:* two-module and
  local-artifact round trips, deterministic hashes, diagnostic registry/payload checks, and no
  stale spelling found by focused searches.

- **U-E9 — adversarial barrier audit and closeout (complete; full closeout green).** Run all direct Hurkens/Girard attempts and
  require rejection at parametric code promotion or ordinary universe self-containment, never
  an unrelated mismatch. Audit every ordinary sink, formation selection, package sealing
  boundary, constructor/pattern helper, local/global instantiation, certificate use, generic
  extension, interface load, and KCore-to-KBackendIR transition. Promote every passing leaf,
  regenerate counts, and run validator, unit/property, full conformance, interface/KCoreText,
  interpreter, C/LLVM native, RC/poison/TSan, package, and performance gates. *Exit:* zero
  pre-variance universe-design leaves remain pending; no quantity-derived mode, noncommutative `TypeLevel`
  addition, free KCore universe declaration, or unverified lift evidence remains.

## Phase F — certified nominal-family universe variance

Phase F implements §10.4.3, §10.5, §11.1.2.3A.2, §30.2.1B, and the associated interface and
KCoreText contracts. Its central rule is narrow: only fully saturated applications of the same
certified nominal family may cross declaration-universe instances. This is not general
subtyping and does not enlarge definitional equality. F1-F7 are implemented and all 42 bundle
suites are active; 34 current-feature suites are green and eight future-family suites remain
honestly capability-gated. The full repository closeout is green.

- **U-F0 — 42-suite variance ledger and honest baseline (implemented; ledger green).** The
  bundle is active at `tests/conformance/spec-coverage/universe-variance/` with 24 accepts and
  18 rejects. Thirty-four suites exercise current behavior and eight future HIIT/HIRT/QIT/QIIT
  suites remain capability-gated. `validate_universe_contract.py` checks the 47 + 71 + 42
  bundle leaves and 17 strengthening leaves. Exact manifest polarity is retained, every future
  skip is capability-based, and the ledger is included in the final full gate.

- **U-F1 — role syntax, typed metadata, rendering, and diagnostics (implemented; focused gate green).** Add
  `UniverseVariance = Invariant | Covariant | Irrelevant`; extend each source schema parameter
  with optional role and origin; parse role words contextually only inside declaration schemas.
  Reject explicit roles on non-nominal declarations with
  `E_UNIVERSE_VARIANCE_NOT_APPLICABLE`. Preserve explicit-vs-inferred role status separately
  from the declaration universe telescope. Add the four aliases and three diagnostic families
  with complete structured payloads. Verbose rendering and hover show effective roles; compact
  rendering may omit inferred words only when no diagnostic/identity fact is hidden. *Gate:*
  parse/pretty/alpha round trips, invalid applicability, diagnostic registry/payload tests, and
  stricter-vs-too-permissive annotation fixtures.

- **U-F2 — nominal signature closure and deterministic role fixed point (implemented; focused gate green).** Build a normalized
  `NominalSignatureClosure` after principal inference, constructor-size checking, and positivity.
  Include family telescope, constraints, point constructors/results, generated projections and
  eliminators, computation rules, every binder mode/quantity/access/explicitness fact, and a
  representation summary. Infer roles jointly per nominal SCC from all-irrelevant downward
  using the standardized monotone action checker. Fully supplied family arguments do not
  constrain a schema role; direct ordinary/parametric code fields are covariant; function
  domains, runtime transforms, coupled parameters, unknown operations, and unsupported clauses
  force invariant. Recognize monotonicity only for certified standard `succ`, natural `+`, and
  `max`. *Gate:* phantom/box/code/witness/consumer, mutual fixed-point, stricter annotation,
  parameter-vs-role orthogonality, and deterministic traversal/property tests.

- **U-F3 — explicit KCore `schemaLift` and surface insertion (implemented; focused gate green).** Add a typed `CSchemaLift` that
  records family identity, source/target schemas, effective roles, covariant evidence,
  certificate identity, and canonical aligned full family arguments. Insert it only during
  expected-type/ascription/constructor/pattern result checking after both applications are
  fully saturated and declaration constraints hold at both instances. Alignment may use only
  definitional conversion, classifier `universeLift`, and recursive certified `schemaLift`.
  Reject partial heads, downcasts, invariant mismatch, family-head/argument mismatch, or any
  runtime map. Keep role-related instances judgmentally distinct. *Gate:* up-lift,
  bidirectional irrelevant lift, downcast/invariant/GADT mismatch, unsaturated lift, identity
  elimination, composition, erasure, and KCore subject-reduction properties.

- **U-F4 — nominal action certificates and independent verification (implemented; focused gate green).** Define stable
  `SchemaActionCertificateId`, checker version, closure hash, role vector, saturation arity,
  clause kinds, and representation-identity result. Generate ordinary-data constructor and
  eliminator actions, then replay them in a checker that does not trust compiler output.
  Require identity/composition, constructor/iota/case coherence, observation/quantity
  preservation, and zero runtime transformation. Distinguish malformed/forged certificates
  (`E_KCORE_SCHEMA_CERTIFICATE_INVALID`) from invalid uses of a valid certificate
  (`E_UNIVERSE_SCHEMA_LIFT_INVALID`). *Gate:* forged role/hash/version, runtime-wrapper,
  clause-action, constructor/case coherence, and direct-vs-composed action tests.

- **U-F5 — KCoreText roles, certificates, and schema lifts (implemented; focused gate green).** Replace `KDData`'s plain universe
  telescope with a nominal role telescope and mandatory certificate reference. Add
  `schema-certificate` declarations, local/imported signature bindings, standardized clause
  kinds, `schema-lift` terms, and explicit per-role evidence. Canonicalize role order,
  certificate placement, identity/composition-normalized lifts, and full `targetArgs`.
  Resolve every family/certificate identity authoritatively and rerun the independent checker
  during checkpoint verification. *Gate:* all nine variance KCoreText suites, canonical
  parse-print-parse and semantic-hash stability, malformed version/hash rejection, and no
  printable valid partial-family lift.

- **U-F6 — interfaces, opacity, semantic identity, and trait coherence (implemented; focused gate green).** Serialize one
  `NominalCumulativitySummary` per exported family with roles, explicit flags, constraints,
  saturation arity, closure hash, certificate ID/version, clause kinds, representation result,
  and extension gate. Include it in semantic hashes, query keys, reproducibility inputs,
  hovers, and interface dumps. Imported opaque families use only verified summaries; absent or
  unsupported summaries degrade to invariant. Keep exact schema instantiations in instance
  heads and apply any evidence `schemaLift` only after ordinary candidate selection. *Gate:*
  opaque two-module lift, stale/missing summary rejection, role-sensitive hash difference,
  load-order determinism, and no role-created instance ambiguity.

- **U-F7 — standard families and generated coherence (implemented; focused gate green).** Publish verified summaries with
  equality `irrelevant`, `TypeBelow`/`TypeAtMost` `covariant`, and inferred summaries for every
  universe-polymorphic prelude nominal family. Preserve explicit constructor instantiations,
  GADT family arguments, pattern refinements, generated projections, recursors, and iota rules
  through lifts. Eta-expand source-level partial type formers only when every generated lift is
  fully saturated and no runtime wrapper survives. *Gate:* equality, bounded packages, trait
  evidence, GADT alignment, constructor/case coherence, partial-former controls, and native
  representation parity.

- **U-F8 — future-extension boundary, metatheory, and closeout (current contract green; eight future capabilities gated).** Add the shared nominal
  signature clause vocabulary and certificate interfaces needed by future HIIT/HIRT/QIT/QIIT
  implementations, but advertise none of those capabilities until all point/path/equation/
  recursive-operation/eliminator obligations are implemented. Keep the eight future suites
  capability-skipped meanwhile. Audit reflexivity/transitivity, substitution, subject
  reduction, action identity/composition, erasure, opacity, mutual fixed points, and every
  Core-to-backend boundary. Promote current passing leaves and run validator, unit/property,
  full conformance, interface/KCoreText, interpreter, C/LLVM native, RC/poison/TSan, package,
  and performance gates. *Exit:* all 34 current variance leaves are active, future skips are
  honest, no uncertified cross-instance nominal conversion exists, and no role changes runtime
  representation.

## Phase G — first-class levels, portable solving, and principled generalization

Phase G implements the 2026-07-21 first-class-level patch. It changes several U-E/U-F
representation choices: neutral level terms become legal rigid atoms, principal inference is
bounded by a named portable fragment, declaration constraints move from side lists to proof
binders, and monotonicity becomes ordinary trait evidence. Preserve every established
soundness barrier while making these migrations; compatibility with dirty internal structures
is not a reason to retain a superseded semantic contract.

- **U-G0 — import and classify the 67-suite contract (implemented; ledger green).** The exact bundle tree plus five
  implementation-strengthening suites is active at
  `tests/conformance/spec-coverage/first-class-levels-solver-generalization/`
  with its manifest, preserving 47 accepts and 20 rejects: 29 positive, 17 negative, 13
  solver, and 8 KCoreText suites. Extend `validate_universe_contract.py` to own every path and
  stage without capability skips. *Gate:* exact 67-path base inventory plus the exact five-path
  strengthening inventory, machine-checked provenance and current `docs/Spec.md` target, all
  source and `.kcore` files present, no harness errors misreported as language outcomes, and an
  owner stage for every suite.

- **U-G1 — level admissibility and neutral semantic identities (implemented; owner gate green).** Add a canonical level atom
  carrying an alpha-normalized KCore-term digest, resolved global identities, and free-variable
  identities. Check ordinary `TypeLevel` typing, totality, lifetime stability, scope,
  serializability, and rigid-checkpoint meta freedom after expression lifting. Decompose only
  canonical standard identities; retain every other admissible term as a neutral atom. Reject
  mutable current facets but accept immutable snapshots, record projections, opaque calls, and
  neutral schema instantiations with exact dependent results. *Gate:* opaque application,
  projection, snapshot, atom-identity/distinction, wrong-index, and mutable-current suites;
  alpha-renaming and definitional-equality atom properties.

- **U-G2 — normative solver layers and portable inference outcomes (implemented; owner gate green).** Refactor `Kappa.Level`
  around explicit constructor NF, exact rigid entailment, and selected-meta inference APIs.
  Preserve additive multiplicity and max idempotence; keep semantic distribution, dominance,
  cancellation, and equality in rigid entailment rather than constructor normalization.
  Implement common-addition/successor cancellation, max-only SCC reduction, direct lower-bound
  joins, closed residuation, selected single-meta max contexts, full substitution/recheck, and
  the five specified result classes. `NoPointwiseLeastSolution` requires a checked witness;
  out-of-fragment minimizable metas use `E_UNIVERSE_INFERENCE_REQUIRES_ANNOTATION`. Keep selected
  assignment solutions as a compact dependency graph until a checked materialization boundary;
  if either that graph or exact rigid entailment crosses the explicit node budget, return
  `IndeterminateResourceLimit` and fail closed instead of accepting, reporting contradiction, or
  expanding exponentially. *Gate:* all 13 direct solver suites plus permutation, alpha,
  satisfiability, differential, compact-DAG resource-limit, and no-exponential-materialization
  properties.

- **U-G3 — declaration-boundary generalization and proof-binder constraints (implemented; owner gate green).** Generalize only
  complete semantic declarations or SCCs. Select metas not free in the environment, replace
  them by rigid parametric variables, recheck the entire body/SCC with the finite dependency
  calculus, and reject ordinary escape with `E_GENERALIZATION_PARAMETRIC_ESCAPE`. Preserve
  existing polymorphism but never generalize lambda, pattern, handler, comprehension, or
  monadic `<-` binders. Replace `dutConstraints`, declaration `constraintBlock?`, and
  constraint-index lift evidence with generated implicit erased proof binders; derive summaries
  only as checked caches. Remove any remaining sealing-eliminator exception. *Gate:* local and
  action-value generalization, environment-free/escape/monadic negatives, generated/user proof
  binder reuse, package projection/repackaging, and pattern dependency suites.
  Inferred mutually recursive locals additionally pin one shared principal telescope across
  omitted identity calls and replay generated symbolic `LevelLe` binders through recursive
  calls and canonical KCoreText round trips.

- **U-G4 — complete arithmetic replay, canonical evidence, and versioning (implemented; owner gate green).** Extend KCoreText
  with `arithmetic [indices]` and `max-least`, replay exact paired-Presburger entailment, reject
  unavailable/duplicate/meta-bearing assumptions, and canonicalize every verified proof to an
  irredundant ordered dependency set. Make direct/composed lifts and structural/arithmetic
  proofs hash identically when theorem and dependencies agree. Record all five algebra,
  normalizer, entailment, inference, and certificate versions in KCoreText, interfaces, caches,
  certificates, and hashes. *Gate:* all eight direct KCoreText suites, round trips, version
  mismatch, forged assumption, proof-identity, and canonical AC hash tests.

- **U-G5 — same-or-lower recursive declaration schemas (implemented; owner gate green).** Distinguish first-class recursion
  over `(u : TypeLevel)` from recursive schema instantiation. Permit omitted identity calls;
  require explicit `.{...}` and complete signatures for every non-identity call; prove every
  target parameter `<=` its current SCC parameter; and diagnose upward/incomparable or implicit
  non-identity calls separately. Feed a proved strict decrease into size-change termination
  without treating non-strict `<=` as descent. *Gate:* identity/lower/strict positive suites,
  increase/implicit/nontermination negatives, interface edge round trips, and first-class
  increasing recursion control. Unconditional equality cycles between inferred local schema
  metas are quotient-ed by antisymmetry before telescope publication; explicit schema
  parameters remain distinct source identities.

- **U-G6 — expected-type schema operations and quantifier interchange (implemented; owner gate green).** Keep `schemaLift`
  insertion direct, fully saturated, same-family, and driven by an already-known synthesized
  and expected type; never use it to solve a meta or search intermediate instances. Add bounded
  expected-type eta-reification of declaration schemas with explicit KCore level lambdas and
  proof binders, while never supplying an omitted explicit term argument. Add ordinary
  `PreservesParametricForall` evidence for quantifier interchange and preserve existing
  polymorphism without commuting quantifiers implicitly. *Gate:* direct-lift/meta-solving,
  branch widening, bounded store/reify, explicit-argument, forall-evidence, and negative
  implicit-commutation suites.

- **U-G7 — ordinary `Monotone` evidence in nominal role inference (implemented; owner gate green).** Define and bootstrap the
  canonical erased `std.typelevel.Monotone` trait, standard evidence for `succ`, partial `+`,
  and partial `max`, and optional separate `OrderEmbedding`. Resolve local/instance/standard
  evidence once before the role fixed point and freeze it into the nominal closure. Never scan
  arbitrary theorem declarations; reject cyclic evidence depending on the role/certificate
  being established; force invariant when selection fails. *Gate:* global instance, local
  evidence, standard partial add, theorem-not-scanned, selected-evidence, and
  monotone-not-order-embedding suites plus F2/F4 certificate regressions.

- **U-G8 — diagnostics, artifacts, harness, metatheory, and closeout (complete; full closeout green).** Implement the four new
  aliases and three families with complete payloads; add all twelve Appendix T directives;
  serialize neutral terms, proof binders/summaries, recursive edges, selected monotonicity
  goals, canonical evidence dependencies, and version fields through interfaces and stage
  dumps. Replay the required substitution, subject-reduction, entailment, inference,
  generalization, recursion, eta-reification, role-evidence, cache, and noninterference
  obligations. Promote all 67 bundle leaves and 5 strengthening leaves only at their owner
  gates, then run the universe ledger,
  spec validator, unit/property, full conformance, KCoreText/interface, interpreter, C/LLVM,
  RC/poison/TSan, package, and performance gates. The 2026-07-24 closeout passed every listed
  lane.

**U-G exit:** every stable total level term has a deterministic admissibility and neutral-atom
story; rigid entailment and portable inference expose their distinct contracts; declaration
constraints have one proof-binder authority; recursive schema calls, schema reification, and
monotonicity evidence are explicit and replayable; all 67 bundle suites plus 5 strengthening
suites are active; and the full
U-E/U-F/U-G regression gate is clean.

## Correctness crux

- **Ordering/algebra agreement.** `Kappa.Level`, the source `TypeLevel` definitions, the
  Presburger translation, interpreter, C, and LLVM must denote the same `omega*c+n` values.
  Natural sum is componentwise and commutative; retaining ordinal-addition logic in any one
  lane makes principal solutions, runtime comparisons, and certificates disagree.
- **Principal inference, not traversal-dependent defaulting.** Generalizable and minimizable
  metas are classified before solving one complete declaration SCC. Result-only metas take a
  principal solution only when the portable assignment rules derive and rigidly recheck it;
  independent parameter metas remain independent, incomparable minima reject, and
  out-of-fragment minimizable metas require annotation. Property-test constraint permutations
  and alpha-renamed SCCs.
- **Constructor form is not semantic equality.** AC/ACI normalization exists for stable
  serialization and hashing. Distribution, dominance, cancellation, and opaque neutral facts
  belong to paired-Presburger entailment. No fast-path tree comparison may become the
  completeness boundary.
- **Neutral identity is contextual but non-circular.** A neutral atom depends on canonical
  KCore syntax, resolved identities, and free-variable identities, not on the enclosing type,
  current constraint, selected proof, source spelling, or allocation order.
- **Assumption hygiene is deterministic.** Recognized comparisons are lexical, ordered, and
  satisfiable. A strict cycle always rejects as self-containment; another inconsistency always
  rejects as an unsatisfiable universe constraint. No implementation path may demote the same
  recognized comparison and continue.
- **Observation, formation, and erasure remain orthogonal.** `ordinary 0` is erased but
  predicative. `parametric` over `Nat` is legal but does not gain impredicative formation merely
  from that tag. A parametric-kind field may select parametric Sigma formation even when its
  level is an ordinary first-class value.
- **The dependency set is authoritative.** A single `Parametric` bit cannot express sealing,
  constant application, let substitution, or multiple origins. Every KCore reduction and
  transformation must preserve the finite set equation; ordinary sinks accept only the empty
  set. Interfaces may cache summaries, but checkpoint verification recomputes them.
- **Package sealing is one-way.** Supplying a witness to a declared parametric field seals its
  dependencies in the container; projecting the field creates a fresh parametric origin.
  Ordinary fields, payloads, reflection, and reification never receive the same exemption.
- **Schema parameters are declaration identity.** Explicit and inferred schemas use the same
  telescope representation. Parameters are alpha-bound, rigid, static, and instantiated at
  every global/local use; they never become term Pis, closure fields, or runtime `TypeLevel`
  values. An explicit schema is complete and never silently extended.
- **Variance is a certified nominal action, not conversion.** A role vector relates only two
  fully saturated applications of the same nominal family. Family arguments are rechecked and
  aligned; they are not assigned inferred term variance. The resulting types remain
  judgmentally distinct, and every accepted crossing is represented by `schemaLift`.
- **Role inference is conservative and orthogonal.** The fixed point starts at irrelevant and
  only tightens. Positivity, observation, quantity, formation, and erasure remain independent
  judgments. A parametric or erased field is not irrelevant merely because it cannot be
  observed or survives no runtime demand.
- **Certificate checking is independent.** The normalized signature closure, role vector,
  generated action, representation-identity result, and checker version must agree. Imported
  opacity never licenses re-inference from a printed type; a missing trustworthy summary means
  invariant, not optimistic covariance.
- **Proof and lift evidence is replayable.** A stable ID identifies a certificate but proves
  nothing. Every lift uses a scoped erased proof binder or independently checked certificate;
  level substitution moves and rechecks evidence at the same time. Equivalent proof syntax
  and direct/composed derivations share semantic identity after dependency minimization.
- **Generalization is rigid rechecking.** Syntactic value shape is not the soundness test.
  Candidates must be absent from the environment and ordinary-observation dependency set after
  the complete declaration/SCC is rechecked under rigid parametric binders.
- **Recursive schemas are typing plus termination.** Pointwise same-or-lower is required for
  typing; only a proved strict decrease contributes to termination. Neither rule substitutes
  for the other, and first-class level recursion remains ordinary term recursion.
- **KCoreText is untrusted input.** Explicit modes, instantiations, stable identities,
  extensions, local schemas, and certificates remain claims until parsing, scope checking,
  certificate checking, KCore typing, and checkpoint verification all succeed.
- **Corpus reconciliation is explicit.** Each superseded expectation receives a replacement
  that preserves its original soundness purpose. No old test is merely deleted because the
  current implementation disagrees with the new contract.

## Verification

1. **The conformance gate:** active tests stay green at every stage; the 118 existing bundle
   leaves, 17 strengthening leaves, and all 42 variance leaves remain active. The 67 G-bundle
   leaves plus 5 strengthening leaves are discoverable at G0 and promote only after their
   owner stage passes; none has a capability-skip escape hatch.
2. **Level algebra properties (E2):** exhaustive small `omega*c+n` values establish source,
   solver, interpreter, C, and LLVM agreement for compare/succ/add/max and all required laws.
3. **Principal inference properties (E3):** alpha-renaming, constraint order, SCC traversal,
   and independent use-site instantiation do not change normalized schemas or hashes.
4. **Observation properties (E1/E5):** parser/pretty round trips preserve observation and
   formation separately; dependency equations satisfy weakening, substitution, beta/iota/zeta,
   projection reduction, and one-way ordinary-to-parametric subsumption.
5. **Package/equality properties (E4):** parametric package construction seals; projection
   restores parametric origin; ordinary payload/reification rejects; prelude and user equality
   pass the same elaboration/checkpoint path.
6. **Lift/certificate properties (E6):** identity/composition are canonical; bad scope,
   stated constraint, proof node, or substitution rejects with the specified diagnostic; all
   lifts erase before KBackendIR.
7. **KCoreText round trips (E7):** parse/print alpha-equivalence, semantic-hash equality,
   byte-identical canonical reprint, explicit global/local instantiations, extension checks,
   certificate verification, and unsupported-version rejection.
8. **Artifact properties (E8):** interfaces round-trip schemas, proof-binder-derived constraint
   summaries, modes, dependency summaries, and certificate identities without source access or
   load-order dependence.
9. **Soundness pins (E9):** ordinary unbounded codes, ordinary self-containment, parametric
   promotion, and all direct Hurkens/Girard fragments fail at an intended structural barrier.
10. **Nominal variance properties (F2-F7):** role inference reaches the deterministic greatest
    fixed point; schema actions are reflexive/transitive and preserve substitution,
    constructor/iota/case behavior, observation dependencies, quantities, and representation;
    invalid saturation, alignment, constraints, direction, or certificates reject.
11. **Interface and KCoreText variance properties (F5-F6):** role vectors and certificate
    identities round-trip, affect semantic identity, survive opaque import only through verified
    summaries, and never alter exact instance-head coherence.
12. **First-class level and solver properties (G1-G4):** atom identity survives alpha-renaming
    and definitional equality; admissibility is substitution-closed; constructor NF is
    deterministic; rigid entailment is complete; portable assignments recheck; arithmetic
    dependencies are irredundant; proof syntax and lift composition do not change semantic
    hashes.
13. **Generalization and recursion properties (G3/G5):** rigid rechecking is stable under SCC
    ordering, no non-boundary binder gains fresh polymorphism, proof binders are the only
    declaration-constraint authority, recursive schema edges are explicit same-or-lower, and
    only strict edges contribute to termination.
14. **Evidence-directed operations (G6/G7):** schema reification is expected-type-only and
    never fills explicit arguments; quantifier interchange and level monotonicity occur only
    through uniquely selected ordinary evidence frozen before role inference.
15. **Closeout gates (green 2026-07-24):** `python3 scripts/validate.py docs/Spec.md`, bundle-input validation,
    `git diff --check`, unit/property tests, full conformance, interfaces/KCoreText, interpreter,
    C/LLVM native, RC/poison/TSan, packaging, and performance all pass.

## Risks

- **R-variance-as-conversion (highest).** Treating related schema instances as judgmentally
  equal would leak roles into unification, instance overlap, GADT refinement, and definitional
  equality. Require an explicit `CSchemaLift` for every crossing and grep/audit conversion paths
  for any role-aware equality shortcut.
- **R-certificate-self-trust (highest).** A generator that also rubber-stamps its recorded
  role/hash is not independent verification. Canonicalize the closure, version the checker,
  replay every action/coherence obligation, and distinguish certificate corruption from a bad
  use of an otherwise valid certificate.
- **R-family-argument-variance (highest).** Reusing ordinary subtyping intuition can silently
  vary term arguments or GADT indices. Align the same arguments left-to-right under the target
  telescope with only definitional conversion and explicit certified lifts; reject every other
  mismatch.
- **R-runtime-transform-hidden-by-erasure (highest).** A role may look safe because a universe
  binder erases while a nested runtime field still needs mapping, wrapping, allocation, or user
  code. Certify the complete nominal closure and representation summary, not only constructor
  headers or universe binders.
- **R-mutual-role-fixed-point.** Per-family local inference is unsound for mutually recursive or
  future inductive-inductive blocks. Run one monotone greatest fixed point for the whole nominal
  block and record separate stable vectors per exported head.
- **R-opaque-import-optimism.** Re-inferring roles from an opaque printed signature can miss
  private clauses or stale checker semantics. Accept only a supported verified summary and
  otherwise degrade to all-invariant.
- **R-corpus-flag-day (highest).** Floating bare `Type`, implicit parametric `forall`, and
  recursive higher-kind defaults touch the prelude and most polymorphic declarations.
  Mitigation: E0 records every conflicting expectation; E1 settles observation/formation before
  E3 principal inference; each owner stage promotes only its passing tranche.
- **R-neutral-atom-aliasing (highest).** Hashing only rendered syntax can merge distinct opaque
  terms; hashing allocation IDs can split alpha-equivalent or definitionally equal terms. Build
  atom identity from canonical KCore structure, semantic globals, and free-variable identities,
  then property-test renaming, substitution, import, and cache replay.
- **R-universe-schema-identity (highest).** Solving/generalizing independently per declaration,
  silently extending explicit schemas, or forgetting local SCC constraints causes unstable
  interfaces and unsound instance identity. Use one telescope type for explicit/hidden and
  global/local schemas across references, artifacts, KCoreText, and hashing.
- **R-level-admissibility-split (highest).** Surface checking, KCoreText, interfaces, and the
  solver may disagree about totality, stability, scope, or neutral identity. Define one typed
  admissibility record and replay it at checkpoints rather than re-deriving four approximations.
- **R-KCoreText-trust-boundary (highest).** A parser that reconstructs omitted defaults or trusts
  stable ids is not KCoreText. Keep the parser syntax-only, require all binder facts, resolve
  identities authoritatively, and run ordinary checkpoint verification on every input.
- **R-add-solver-completeness (highest).** Natural sum changes normalization and every symbolic
  formula involving `LAdd`. A plausible rewrite may be commutative on closed inputs yet
  incomplete on open terms. Require componentwise reference semantics, exhaustive
  small-expression differential, assumption fuzzing, and runtime parity before E2 is accepted.
- **R-solver-subtlety.** Natural sum, successor, `max`, assumptions, and principal lower bounds
  interact on open expressions. Pin `1 + omega = omega + 1`, `omega + omega`, strict
  monotonicity, max laws, and consistent equality cycles such as `u ≤ v, v ≤ u`; accept a
  stable `Type (f u)` as a neutral atom without granting it the algebra of a standard head.
- **R-semantic-identity-laundering.** Name-based checks may decompose a shadowed `+`/`max`/`<`,
  while proof-object IDs may perturb otherwise equal artifacts. Carry resolved global and
  instance identities into normalization, keep user operations neutral, and derive hashes from
  normalized theorem/dependency content rather than proof allocation.
- **R-forall-flag-day.** `forall` now introduces an implicit parametric binder, opposite the
  historical plan. Reconcile all explicit-application tests in E1/E3 and require `ordinary`
  source syntax where ordinary observation was intended.
- **R-performance.** `leqLevel` runs inside conversion, and declaration solving installs many
  small substitutions. Keep the closed-finite fast path allocation-free, build assumption
  closures only when variables are present, and retain assignment composition as an indexed
  graph rather than eagerly normalizing every prior entry. The structural unit pin requires
  module closeout to retain neither assignment nor constraint history; Delve is the package
  performance gate.
- **R-hidden-promotion-paths.** `Check.hs` has many lookup/facet/reflection seams; a missed seam
  silently launders a parametric static witness. Use the E5 dependency-calculus audit, direct
  KCore negative inputs, and a grep-level invariant that no ordinary sink bypasses the computed
  dependency set.
- **R-defaulting-order-dependence.** §11.1.3's least-level instantiation must be
  order-independent or rejected; classify inference roles before solving and recompute under
  permuted constraints/SCC order in property tests rather than trusting traversal order.
- **R-evidence-substitution.** Rewriting only level terms while retaining stale ceiling/lift
  evidence can accept an invalid instantiated declaration. Evidence and level substitution
  share one operation and are always replayed by the checkpoint verifier.
- **R-package-oversealing.** Treating every parametric argument as sealing would make ordinary
  records/functions unsound; treating none as sealing rejects the new witness package. Sealing
  applies only at a declared parametric field/constructor boundary, and projection restores a
  fresh origin.
- **R-dual-constraint-authority (highest).** Leaving `dutConstraints` authoritative while also
  inserting proof binders permits interface, application, and certificate checking to disagree.
  Migrate producers and consumers together; summaries are recomputed caches only.
- **R-generalization-without-recheck (highest).** Abstracting inferred metas from a type without
  replaying the body can promote an ordinary observation into false parametric polymorphism.
  The complete declaration/SCC must pass rigid dependency rechecking before abstraction.
- **R-recursive-schema-confusion.** Treating pointwise `<=` as termination accepts loops;
  treating term-level `TypeLevel` recursion as schema recursion rejects ordinary programs.
  Record the edge kind explicitly and admit only strict schema edges into SCT.
- **R-monotonicity-search-cycle.** Launching trait search during the role fixed point can make
  evidence depend on the certificate it is meant to justify. Resolve and freeze ordinary
  `Monotone` evidence before iteration and reject same-block cycles.

## Active ordering and gates

U-E, U-F, and U-G are implemented and passed the combined 2026-07-24 closeout. U-G is the
current normative delta.

| sub | what | gate (abridged; full lists above) |
|---|---|---|
| **U-E0** | 118-suite ledger and implementation baseline | 47 + 71 + 17 active inventory validates; full re-gate green |
| **U-E1** | observation/formation separation | non-kind parametric, grouped binder, ordinary-`0` controls |
| **U-E2** | commutative `TypeLevel` algebra | laws plus solver/interpreter/C/LLVM differential |
| **U-E3** | explicit schemas + principal local/global SCC inference | schema/principal/local/interface gates |
| **U-E4** | witness packages, equality, data grammar, standard schemas | package/equality/data suites |
| **U-E5** | finite-origin KCore observation calculus | metatheory and laundering negatives |
| **U-E6** | deterministic assumptions + replayable lift certificates | inconsistency/certificate/lift properties |
| **U-E7** | pre-variance KCoreText candidate | global/local instantiation, extension, certificate round trips; full re-gate green |
| **U-E8** | artifacts, prelude, diagnostics, migration | interface/hash/registry and stale-contract sweep |
| **U-E9** | adversarial audit and closeout | intended Hurkens barriers; zero pending; full gate |
| **U-F0** | 42-suite variance ledger | 34 current outcomes honest; 8 future capability skips honest |
| **U-F1** | role syntax, metadata, rendering, diagnostics | parser/pretty/alpha; applicability and payload gates |
| **U-F2** | nominal closure + role fixed point | phantom/box/code/consumer/mutual role properties |
| **U-F3** | explicit saturated `schemaLift` | direction/alignment/saturation/composition/erasure gates |
| **U-F4** | independent schema-action certificates | forged/runtime-transform/coherence negatives |
| **U-F5** | KCoreText roles/certificates/lifts | nine direct suites; canonical round trips |
| **U-F6** | interfaces, opacity, identity, trait coherence | opaque import/hash/instance-order gates |
| **U-F7** | standard-family and generated coherence | equality/bounded/GADT/case/partial-former gates |
| **U-F8** | future boundary, metatheory, closeout | 34 current active; future capabilities honest; full gate |
| **U-G0** | first-class-level ledger | 67 bundle + 5 strengthening contracts; no capability skips |
| **U-G1** | admissibility + neutral atoms | opaque/projection/snapshot/identity/stability gates |
| **U-G2** | solver layers + portable outcomes | 13 solver suites; cancellation/residuation/classification |
| **U-G3** | rigid generalization + proof constraints | boundary/escape/proof-binder/package gates |
| **U-G4** | arithmetic replay + versioned identity | eight KCore suites; irredundant dependencies/hashes |
| **U-G5** | recursive schemas + termination edges | identity/lower/strict/increase/implicit controls |
| **U-G6** | direct lifts + schema/forall reification | expected-type and explicit-argument controls |
| **U-G7** | ordinary monotonicity evidence | local/global/standard/no-scan/cycle gates |
| **U-G8** | artifacts, harness, metatheory, closeout | all 67 + 5 active; full U-E/U-F/U-G gate green |

Current ordering rationale: E0 prevents silent expectation drift. E1 separates the three axes
before any formation fix. E2 settles the algebra consumed by principal solving. E3 establishes
the final schema identity used by equality, packages, interfaces, and KCoreText. E4 settles
surface/prelude contracts before E5 installs the authoritative KCore dependency calculus. E6
settles replayable evidence before E7 serializes it. E8 migrates all artifacts and expectations;
E9 performs the barrier audit and full closeout. Every stage ends active-conformance green.

F0 extends the contract without pretending that capability-gated future nominal forms exist.
F1 establishes stable syntax and metadata before F2 computes roles. F3 adds the only legal
cross-instance Core operation; F4 makes its proof independently replayable. F5 serializes the
typed facts only after their checker exists. F6 then exposes them across opacity and separate
compilation, F7 migrates standard/generated families, and F8 performs the metatheory and full
runtime-neutral closeout.

G0 fixes the contract ledger before implementation. G1 establishes the typed neutral identities
consumed by G2's solver. G3 then rebuilds declaration generalization and constraint authority on
those judgments. G4 serializes and versions the settled proof contract. G5 adds recursive use of
schemas only after proof binders and entailment are authoritative. G6 adds expected-type
transformations without contaminating meta solving. G7 integrates ordinary evidence into the
already-stable nominal closure, and G8 performs artifact migration and combined closeout.

## Implementation checks (resolve with tests, not design drift)

- **No quantity fallback (E1/E5).** Once explicit mode reaches KCore, delete every
  `q == Q0 && domain is Type` classification fallback. Keep temporary compatibility code only
  inside one migration commit and assert that canonical KCore never depends on it.
- **Grouped bare-Type sharing (E1/E3).** The parser must retain enough grouping identity for
  `(A B : Type)` to share one meta while separate binders remain independent. Do not recover
  this distinction from pretty-printed syntax.
- **Declaration telescope ownership (E3/E8).** Use one typed structure for globals, SCC
  generalization, references, interfaces, semantic hashing, and KCoreText. A second ad hoc
  interface representation is a future divergence bug.
- **Principal-role ownership (E3).** Assign generalizable/minimizable roles at meta creation or
  at one auditable SCC analysis. Do not infer the role from whether a lower-bound assignment
  happened to be discovered first.
- **TypeLevel bridge separation (E2).** Runtime evaluation uses ordinary opaque declarations;
  universe normalization recognizes their resolved identities and produces solver `Level`
  expressions. Neither implementation calls the other as an arbitrary evaluator.
- **Opaque representation range (E2).** Runtime arithmetic must preserve the specified
  `ω*c+n` normal form below `ω^2`, reject or make unreachable out-of-fragment results, and
  agree extensionally with solver normalization for admitted operations.
- **Declared sealing only (E4/E5).** Construction seals dependencies only at a declared
  parametric field/constructor slot. Projection creates a fresh origin; aliases and ordinary
  fields never synthesize a sealing boundary.
- **Evidence-carrying substitution (E6).** Level substitution, declaration-universe
  instantiation, ceiling certificates, and explicit lifts use one capture-avoiding operation.
  Unit tests must fail when any one component is intentionally left unsubstituted.
- **KCoreText generic nodes (E7).** Unknown portable tags reject unless an advertised extension
  owns them. Generic nodes do not bypass scope, mode, level, or checkpoint validation.
- **Harness capability truthfulness (E7).** Advertise `kcoreText` and `stageDumps` only when the
  requested parser/printer/checkpoint path is actually executed. A no-op assertion is a
  harness bug, not partial support.
- **Two role vocabularies (F1/F2).** Rename the current internal
  `DeclarationUniverseRoles` generalizable/minimizable analysis before introducing nominal
  `UniverseVariance`; code and diagnostics must not conflate inference-meta roles with
  cumulative family roles.
- **Closure authority (F2/F4).** Generate a typed normalized closure once and use it for role
  inference, certificate checking, interface hashing, and KCoreText verification. Rebuilding
  four similar clause lists guarantees semantic drift.
- **Saturation before relation (F3).** The checker must establish semantic family identity and
  exact declared term arity before consulting roles. Never ask a role checker to rescue a
  partially applied or mismatched head.
- **Argument alignment is restrictive (F3).** Alignment rechecks the same source arguments in
  telescope order. It may insert only classifier lifts and recursively certified nominal
  lifts; it must never invoke coercions, trait search, extensionality, or user code.
- **Certificate identity is not evidence (F4/F5).** A `SchemaActionCertificateId` is a lookup
  key. Every local certificate is replayed against the local closure and every imported one is
  matched to a verified interface summary before a `schemaLift` can typecheck.
- **Runtime-identity assertion (F4/F8).** Lowering may erase `schemaLift` only after checkpoint
  verification records `representationIdentity = true`. Backends never infer this from roles,
  quantity, or the absence of visible fields.
- **Instance-search firewall (F3/F6).** Exact schema instantiations remain in normalized heads.
  No role comparison or `schemaLift` insertion occurs until a unique ordinary candidate has
  been selected.
- **Future capability firewall (F0/F8).** Parsing storage for future clause kinds is not an
  implementation of HIIT/HIRT/QIT/QIIT variance. Keep each capability false until its complete
  clause action and naturality checker exists.
- **Admissibility before atomization (G1).** Never turn an arbitrary source term into a solver
  atom first and ask whether it was legal later. Typecheck, prove totality and lifetime
  stability, lift expressions, resolve identities, reject unresolved metas, and only then
  allocate the canonical neutral identity used by solving and serialization.
- **Constructor equality is deliberately weak (G1/G2).** AC/ACI normalization may identify
  constructor syntax, but semantic equalities such as cancellation, distribution, dominance,
  and opaque neutral facts belong to exact rigid entailment. Do not make elaboration depend on
  a stronger private normalizer than KCoreText can replay.
- **Inference outcomes are data (G2).** The five portable outcomes must survive solver API
  boundaries with checked witnesses where required. Do not collapse no-principal,
  out-of-fragment, and blocked into one residual-constraint path and recover the diagnostic by
  inspecting error text.
- **Rigid recheck is the generalization proof (G3).** Replacing metas with parametric binders is
  only a candidate transformation. Acceptance requires rechecking the complete declaration or
  recursive SCC, including generated terms and all ordinary observation sinks.
- **One constraint authority (G3/G4).** Generated level inequalities are ordinary implicit
  erased proof binders. Telescope summaries, certificate dependency lists, and interface
  indexes are derived views and must be rejected when they disagree with the checked binders.
- **Recursive schema edges are not term recursion (G5).** Compare explicit schema
  instantiations against the current SCC telescope and feed only proved strict decreases to
  termination. An ordinary first-class `TypeLevel` argument follows normal dependent
  termination and must never be reclassified as a schema edge.
- **Expected-type transformations cannot drive search (G6).** Schema lifting and bounded schema
  eta-reification run only after both endpoints are known. They cannot assign universe metas,
  invent omitted explicit arguments, search intermediate instances, or commute quantifiers
  without selected ordinary evidence.
- **Freeze monotonicity evidence (G7).** Resolve the ordinary `Monotone` goal before nominal
  role fixed-point analysis and store the selected evidence identity in the normalized closure.
  Never rescan theorem declarations or rerun open-ended instance search while replaying a
  certificate.
- **Version every semantic layer (G4/G8).** Algebra, constructor normalizer, rigid entailment,
  portable inference, and certificate format versions are independent hash inputs. A cache or
  interface mismatch must invalidate the artifact before any proof object is trusted.

## Critical files

- `src/Kappa/Syntax.hs`, `src/Kappa/Parser.hs`, and `src/Kappa/SyntaxOps.hs` — contextual mode
  syntax, grouped annotation identity, declaration-schema role annotations, defaults,
  substitutions, and binder-producing sugars.
- `src/Kappa/Core.hs`, `src/Kappa/CoreOps.hs`, `src/Kappa/Eval.hs`, and `src/Kappa/Pretty.hs` —
  explicit binder/field modes, declaration universe telescopes, `CSchemaLift`, conversion,
  substitution, normalization, erasure, and canonical/verbose rendering.
- `src/Kappa/NominalVariance.hs` (implemented; there is deliberately no separate
  `SchemaCertificate.hs` module) — the Core-term-free home of normalized nominal signature
  closures, monotone role transfer, fixed-point role inference, closure hashing, and
  certificate/summary verification. `Check.hs` only extracts the normalized clause
  requirements this module consumes; certificate serialization/verification at the text
  boundary lives in `CoreText.hs`. Keep it that way: no closure or replay logic may migrate
  into the already oversized `Check.hs`.
- `src/Kappa/Level.hs` — admissible neutral identities, natural-sum constructor NF, exact paired
  Presburger rigid entailment, the bounded portable meta-inference API and five outcomes,
  checked no-principal witnesses, assumption minimization, and replayable certificates.
- `src/Kappa/Check.hs` — floating bare `Type`, SCC generalization/reference instantiation,
  explicit schemas, principal meta roles, local SCC boundaries, observation/formation split,
  finite-origin dependency checking, constructor/pattern/alias/trait/reflection sinks,
  package sealing, standard-operation bridge, equality checking, nominal closure construction,
  declaration-boundary rigid rechecking, generated proof binders, same-or-lower recursive
  schema edges, expected-type `schemaLift` and eta-reification, restricted family-argument
  alignment, frozen `Monotone` evidence, and the trait-search firewall.
- `src/Kappa/Pipeline.hs` and typed global/module metadata — preserve declaration universes,
  modes, nominal role summaries, closure/certificate identities, lifts, and semantic identities
  through artifacts and checkpoint verification.
- `src/Kappa/Prelude.hs` and `src/Kappa/Builtins.hs` — opaque runtime `TypeLevel`, canonical
  `std.typelevel.Monotone` plus standard `succ`/partial-add/partial-max evidence, optional
  `OrderEmbedding`, universe-generalized standard families, and explicit higher-kinded mode
  headers.
- `src/Kappa/Backend/IR.hs`, `src/Kappa/Backend/Repr.hs`, and
  `src/Kappa/Backend/Verify.hs` — retain runtime `TypeLevel`, erase verified representation-
  identity lifts, and reject solver/certificate metadata or runtime dependence on erased
  occurrences.
- `src/Kappa/Backend/C.hs`, `src/Kappa/Backend/LLVM.hs`, `src/Kappa/Interp.hs` — runtime
  `TypeLevel` representation and operation semantics.
- `src/Kappa/CoreText.hs` — complete KCoreText schema, proof-binder declaration constraints,
  neutral level terms, arithmetic/max-least level proofs, irredundant dependency
  canonicalization, recursive schema edges, schema reification, selected monotonicity evidence,
  five semantic version fields, nominal-action certificates, `schema-lift`, diagnostics, and
  verified round trips.
- `src/Kappa/TestHarness.hs` and `test/Spec.hs` — KCoreText capabilities/directives, solver and
  mode/role properties, all twelve new Appendix T assertions, certificate replay, malformed
  KCoreText, interface identity, and backend differential tests.
- `tests/conformance/universes/`, `tests/conformance/spec-coverage/
  parametric-type-witnesses/`, the active 47 + 71 + 17 contracts, and the 42-leaf variance
  bundle — existing migration and re-gates. The 67-leaf
  `kappa_first_class_levels_solver_generalization_tests` bundle is active under
  `tests/conformance/spec-coverage/first-class-levels-solver-generalization/`.

## Spec anchors

- **§11.1.1** runtime-capable opaque `TypeLevel`, level admissibility, neutral semantic
  identities, expression lifting, and the certified solver bridge;
  **§11.1.2.1-2** ordering, natural-sum algebra, cumulativity, standard operations, and proof bounds;
  **§11.1.2.3** floating bare `Type`; **§11.1.2.3A** hidden declaration universe parameters;
  **§11.1.2.3A.1** explicit schemas, proof-binder declaration constraints, rigid
  declaration-boundary generalization, schema eta-reification, and same-or-lower recursion;
  **§11.1.2.3A.2** nominal roles, saturation, argument alignment, and non-judgmental
  cumulativity; **§11.1.2.3B** parametric kinds
  and observation mode; **§11.1.2.4A** constructor normalization and exact rigid entailment;
  **§11.1.2.4B** portable metavariable inference; **§11.1.2.7** unbounded witness
  packages; **§11.1.2.8** separate Pi/Sigma formation modes and ceilings; **§11.1.3** defaulting;
  **§11.1.4-6** first-class values, phases, and use-sensitive erasure.
- **§12.1.1** independent mode/quantity/access/explicitness syntax and defaults;
  **§11.3** implicit parametric `forall`; **§11.3.3** declaration universalization.
- **§10.4.1** mode-based constructor universe-size exception and generated-mode preservation;
  **§10.4.3** nominal signature closures, ordinary `Monotone` evidence, role inference, and
  action certification; **§15.4** recursive-schema termination measures;
  **§10.5** future nominal-extension contract.
- **§11.4.1** explicit-schema equality/Dec/eliminators with parametric endpoints;
  **§11.4.2** Boolean-to-type coercion at proof-binder positions (level-assumption recognition).
- **§7.6.1** static-object facets; **§13.2.4A** parametric fields; **§14.3.1A** trait evidence;
  **§17.1.7A** pattern mode; **§21.6.2** macros/reflection; **§7.1** lookup admissibility.
- **§30.2.0** finite-origin KCore observation dependency calculus and declaration universes;
  **§30.2.0A** KCoreText proof binders, arithmetic replay, canonical dependencies, and semantic
  version metadata; **§30.2.1A** proof-irrelevant classifier lifts; **§30.2.1B** nominal
  `schemaLift` and direct-composition identity;
  **§30.2.2.9** intrinsic types,
  levels, evidence, and erasure provenance; **§31.2** KBackendIR legality.
- **§14.3** instance-search firewall; **§30.2.5/§34.1.9** semantic identity and
  `NominalCumulativitySummary`; **Appendix T** role/lift/certificate assertions and future
  capability gates.
- **§28.2** standard `TypeLevel` declarations/instances and higher-kinded trait headers;
  **§37.18** mode-preserving tooling/refactorings.
- **§3.1.4/§3.2.3** promotion, schema arity/scope, inference-annotation, recursive-schema,
  parametric-generalization escape, no-principal-solution, variance, schema-lift, KCoreText,
  and level/schema-certificate diagnostics.
- **Hurkens/Girard barrier** under §11.1 and `docs/notes/KNOWN_SPEC_ISSUES.md` §16/§17.
