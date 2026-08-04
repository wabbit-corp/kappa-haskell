# Nat / Fin / Refinement / Arithmetic Certificates - Implementation Plan

Status: **NFR-0 through NFR-8 implemented for the portable contract
(2026-07-30).** `docs/Spec.md` contains the Nat/Fin/refinement patch
from `docs/Kappa-Nat-Fin-Refinement-Patch-Bundle/Spec-Nat-Fin-Refinement-v2.patch`
plus the 2026-07-26 evidence-canonicalization amendment (§15.8.2 canonicalizes
evidence occurrences at the same normalized trait application to the §16.3.3
step 1 deterministic representative, recording the identifying
`IsSubsingleton` equalities as quantity-`0` bridge evidence in proof terms and
certificates; the no-mixing prohibition is scoped to closures at distinct
normalized trait applications; §14.3.3 defers same-scope projected candidates
to the same rule), and passes the repository specification validator. The
contract is materialized as a **103-suite** tree under
`tests/conformance/spec-coverage/nat-fin-refinement/`: the 22 originally
derived suites, 49 added by the T.12 catalog-gap and corpus-reconciliation
pass (including four dx-issues probes whose dead-end premises the revision
turned into requirements, and re-based replacements for five green
conformance tests the revision invalidated), 12 non-range refinement
suites (equality/parity/congruence predicates, non-numeric and record bases,
custom and derived `RefinementView`, nested refinement, non-prop-fiber
rejection, finite-domain cardinality, user-`Dec` `tryRefine`), and 18
corner-case/interaction suites (the natAdd left-recursion asymmetry,
literal-spelling convergence, Presburger cancellation from assumptions,
checked-subtraction never-saturating boundary in both directions,
principal-solution multiplication pair, provider-closure boundaries,
automatic Fin weakening via refinement widening, source-level `Fin 0`
`case impossible`, linear-base refinement, alias-equal-base widening,
negative Integer range bounds, derive through Fin fields and recursive
trees, nested wrapper erasure, Fin literals in index position, and
beyond-word range synthesis), and the 2026-07-26 canonicalization rewrite
that replaced the corner-case pass's provider-closure negative with an
accepted evidence-canonicalization suite (implicit solving plus explicit law
projection from either named dictionary) and a retained-boundary negative at
distinct normalized trait applications. A same-day five-way adversarial
review of the whole tree against the spec then corrected roughly twenty
suites (forall-implicit application spellings, implicit constructor-field
payloads, invented or non-required prelude spellings, capability vocabulary,
premise collapses at concrete carriers), split the linear-refinement claim
into an elimination positive plus a construction negative, converted the
supertrait-incoherence negative the canonicalization amendment flipped, and
renamed the unsafe-assert probe to a direct IsProp demand, bringing the tree
to 103. The 2026-08-02 unified-derive revision retargeted two negatives
(handwritten-eq-missing-laws, derive-isset-function-field) into
`tests/pending-import/derive-automation/retargeted/`, leaving **102 active
suites**. The conservative profile passes the active tree except the two
compact-layout-only suites, which report `Unsupported` because it does not
advertise their optional representation capabilities.

The implementation retains the exact `Integer` substrate and now supplies the
language and evidence contract around it: source-visible logical `Nat`, checked
derivation, value-level arithmetic providers and replayable certificates,
`Fin`, `Refined`, symbolic cardinality, independently verified representation
certificates, exact non-unary native execution, and profile-aware backend
obligations. Compact finite-ordinal, packed-field, and unboxed-refinement
layouts remain optional and are selected only when the active profile
advertises the corresponding capability.

This plan is the implementation authority for that contract. `ROADMAP.md`
contains only the short stage ledger.

## 0. Objective and boundaries

Implement the current `docs/Spec.md` contract so that:

1. `Nat` is the ordinary logical inductive type with `Zero` and `Succ`, and its
   source computation rules remain visible through ordinary data elimination.
2. Every runnable backend represents and computes natural numbers exactly and
   non-unarily.
3. generated no-confusion packages and checked `derive IsSet` / `derive Eq`
   produce ordinary verified KCore evidence.
4. the value-level arithmetic solver uses selected coherent algebraic evidence,
   emits explicit proof terms or compact replayable certificates, and does not
   enlarge definitional equality.
5. `Fin`, `Refined`, `RefinementView`, `Contains`, and canonical ranges are
   ordinary library and elaboration features with real proof obligations.
6. symbolic cardinality and representation certificates are purpose-keyed,
   serialized, hashed, independently checked, and consumed only at allowed
   checkpoints.
7. proof erasure and optional compact layouts are justified in verified
   KBackendIR and preserve behavior across interpreter, C, and LLVM paths.

The following are deliberate non-goals:

* Do not reuse the universe-level `TypeLevel` solver or its certificates as the
  authority for value-level arithmetic. Shared generic normalization utilities
  are acceptable; domains, providers, evidence identities, versions, and
  diagnostics remain distinct.
* Do not make propositional arithmetic laws judgmental. In particular,
  `n + Zero = n` remains propositional when it does not reduce by the declared
  computation rules.
* Do not add special `x in range` syntax. Membership remains the ordinary
  `contains range x` operation selected through `Contains`.
* Do not treat `IsProp` or quantity `0` as evidence that a proposition is
  inhabited.
* Do not require compact finite-ordinal or packed refinement layouts from a
  backend profile that does not advertise them. Exact `Nat` and verified proof
  erasure are required for every runnable backend.
* Do not derive UIP, K, proof irrelevance, or no-confusion for unsupported
  higher/path constructor shapes.

## 1. Current implementation audit

### 1.1 Existing substrate to keep

* `src/Kappa/Core.hs` represents numeric literals as `LitInt Integer`.
* `src/Kappa/Eval.hs` computes integer arithmetic with exact Haskell
  `Integer`.
* `runtime/bignum.c`, `runtime/value.c`, and both native code generators
  support an immediate/`int64` fast path with boxed GMP fallback.
* `src/Kappa/Inhabitance.hs` already separates analysis purposes and represents
  finite bounds with exact `Natural`.
* `src/Kappa/Backend/Repr.hs` is the shared representation-selection authority
  used by native worker planning.
* `src/Kappa/CoreText.hs`, `src/Kappa/LevelEvidence.hs`,
  `src/Kappa/NominalVariance.hs`, and `src/Kappa/SemanticHash.hs` provide
  patterns for parsed, versioned, independently checked evidence.
* `src/Kappa/Syntax.hs` and `src/Kappa/Parser.hs` already preserve `DDerive`
  syntax.

### 1.2 Implemented contract surface

* `src/Kappa/Prelude.hs` exposes ordinary logical `Nat`, the revised algebraic
  hierarchy, `Fin`, `Refined`, `RefinementView`, and `Contains`.
* `src/Kappa/Check.hs` implements checked derivation, coherent local-first
  evidence selection, proof-producing value arithmetic, branch facts,
  refinement synthesis, and explicit transport at expected-type boundaries.
* `src/Kappa/Arithmetic.hs`, `src/Kappa/CoreText.hs`, and
  `src/Kappa/Representation.hs` provide reusable normalization, versioned
  certificates, independent replay, and semantic identities.
* `src/Kappa/Inhabitance.hs` provides purpose-keyed interval and symbolic
  cardinality analysis without feeding runtime layout back into source
  reachability.
* `src/Kappa/Backend/IR.hs` records verified exact-natural, finite-ordinal, and
  refinement decisions and fails closed when an advertised representation
  contract cannot be proved.
* `src/Kappa/TestHarness.hs` routes every Appendix T assertion through the
  production queries and verified checkpoints.

### 1.3 Active contract baseline

`tests/conformance/spec-coverage/nat-fin-refinement/manifest.json` owns 103
suites:

| owner | suites | contract |
| --- | ---: | --- |
| NFR-1 | 8 | logical Nat, constructor computation, definitional left identities, structural recursion |
| NFR-2 | 18 | no-confusion, GADT bridge judgment, checked h-level derivation, derive views |
| NFR-3 | 32 | algebraic providers, solver domains, inserted transport, certificates, determinism |
| NFR-4 | 32 | Fin, Refined (range and non-range), subsumption, ranges, Contains |
| NFR-5 | 6 | inhabitance, symbolic cardinality, ordinal evidence |
| NFR-6 | 2 | arithmetic and representation artifact mutation |
| NFR-7 | 5 | exact Nat, proof erasure, profile-aware compact layout |

The 2026-07-30 active owner gate reports 101 passed, zero failed, two
capability-gated optional compact-layout suites, and zero harness errors. The
validator
`scripts/validate_nat_fin_contract.py` fixes the suite tree, bundle
source-document hashes, categories, capabilities, owner stages, and T.12
coverage; it passes at 103 suites.

The applied specification includes one implementation-discovered correction
to the frozen input patch: `finLast` takes an ordinary explicit `n : Nat`.
The patch's implicitly universalized spelling would make `n` quantity-`0`
under §11.3 while using it as the returned runtime ordinal, contradicting the
erasure contract. The frozen bundle remains unchanged as provenance; the
current `docs/Spec.md` and active implementation carry the correction.

## 2. Architectural invariants

### 2.1 Logical and runtime Nat are different views

Source typing and KCore verification see the ordinary inductive `Nat` and its
constructor/eliminator computation rules. Runtime lowering may use an exact
compact representation only after a verified exact-natural certificate relates
that representation to the logical type. Backend layout never becomes an
additional conversion rule.

Large literals and arithmetic must not materialize unary successor chains in
the interpreter, generated C/LLVM, KBackendIR runtime fields, or serialized
runtime constants. A compact semantic literal node or certified intrinsic is
acceptable only when its typing and constructor/eliminator behavior replay to
the logical `Nat` contract.

### 2.2 Evidence is explicit at the trust boundary

Arithmetic normalization, refinement insertion, h-level derivation,
no-confusion, ordinal ranking, and erasure all produce ordinary proof terms or
versioned certificates. A backend, cache, interface, plugin, or imported
KCoreText file cannot assert the result through an unchecked flag.

### 2.3 Provider selection is coherent and deterministic

The arithmetic solver normalizes only with the exact law bundle selected by
ordinary implicit resolution. Commutativity requires
`CommutativeAdditiveMonoid`; distributivity without additive commutativity is
owned by `AdditivelyNoncommutativeSemiring`. Evidence occurrences at the same
normalized trait application canonicalize to the deterministic §16.3.3
representative before reification, with the identifying `IsSubsingleton`
equalities recorded as quantity-`0` bridge evidence; closures at distinct
normalized trait applications are never mixed (§15.8.2). Unrelated imports
cannot change the selected provider, certificate identity, or semantic hash.
The portable semiring normal form is a sum of ordered multiplicative words:
additive terms may be canonicalized, but factor order is preserved unless a
separate checked commutative-multiplication provider explicitly authorizes
reordering. Polynomial replay has deterministic limits of 4096 input nodes and
4096 materialized terms; exceeding either limit produces no proof.

### 2.4 Source analysis is not runtime-layout analysis

`SourceReachability` and `Completion` use logical constructors and actual proof
inhabitance. `RuntimeShape` and `Optimization` may use erased fields and
representation certificates. A compact representation cannot make an
uninhabited source type inhabited or remove a source-visible branch.

### 2.5 Refinement proof synthesis is exactly once

Implicit refinement insertion may solve a closed obligation and insert its
proof, but it cannot accept a value merely because the predicate is an h-prop.
The elaborated term has one owner for the proof field; erasure removes that
field only after KCore checking and erasure justification.

## 3. Stages, ordering, and gates

### NFR-0 - Freeze the contract and add harness observability (implemented)

Deliverables:

* keep the 103-suite manifest and provenance validator authoritative;
* add typed `TestHarness` directives for:
  `assertArithmeticCertificatesValid`, `assertInhabitance`,
  `assertSymbolicCardinality`, `assertOrdinalRepresentation`,
  `assertExactNaturalRepresentation`, `assertRefinementRepresentation`,
  `assertRepresentationClass`, and `assertRuntimeFieldAbsent`;
* route assertions through the same public compiler queries and verified
  checkpoint artifacts used by tools, never a second test-only implementation;
* add a checkpoint fixture proving that an untransported KCore term cannot use
  `natAdd n Nat.Zero` and `n` interchangeably, paired with the positive source
  fixture whose elaborated KCore contains solver-produced equality transport;
* extend the provider-determinism directory harness to compare the selected
  provider identity and generated proof/certificate bytes for both source
  variants; the existing nominal-summary `assertSemanticHashEquals` check is
  only a smoke check and is not a promotion gate by itself;
* expose capability names only when their complete contract is implemented;
* replace the two artifact `MUTATION.md` procedures with executable
  directory-suite mutation fixtures before promotion;
* define the canonical machine-readable renderings the analysis directives
  compare against — `CardExpr` output and representation-class spellings
  (`FiniteOrdinal n`, `ExactNatural`; the bundle catalog's `FiniteOrdinal8`
  is a lane spelling, not a class) — and specify how free `Nat` variables of
  `assertSymbolicCardinality`/`assertOrdinalRepresentation` type expressions
  are bound (both recorded as KNOWN_SPEC_ISSUES III.8);
* implement the newly listed §T.5.2 `assertEval` and `assertTotal`
  directives through the same public queries as the rest (both were
  corpus-load-bearing and are now standard; `assertTotal` the directive is
  disambiguated from the §4.4 unsafe modifier by position, KNOWN_SPEC_ISSUES
  III.9);
* reconcile the `E_INDEXED_IMPOSSIBLE_REACHABLE` portable alias with the
  implementation's `E_IMPOSSIBLE_REACHABLE` spelling in the diagnostic
  registry (the bundle's unknown-bridge suite asserts the spec alias).

Gate:

* every contract directive parses;
* unavailable capabilities report `Unsupported`, not `HarnessError` (the
  historical 22 harness errors are now passing assertions or the two
  explicitly unavailable optional representation capabilities);
* malformed assertions fail locally and deterministically;
* the validator still reports exactly 103 suites with no unowned files.

### NFR-1 - Logical Nat and exact numeric substrate (implemented)

Deliverables:

* replace the opaque prelude `Nat` authority with the canonical ordinary data
  declaration and stable `Zero`/`Succ` identities;
* lower natural literals and primitive arithmetic to exact operations while
  preserving constructor matching, structural recursion, and declared
  left-reduction behavior;
* ensure the logical constructor view and compact numeric view have one checked
  bridge, including literal patterns and generated eliminators;
* preserve exact evaluation and GMP fallback on C and LLVM while removing
  assumptions that every `Nat` is safely consumable through an `int64` slot;
* make portable `Int` definitionally the transparent `Integer` alias required
  by the spec and audit all primitive, FFI, array-index, time, and native-width
  conversion sites for explicit bounds;
* add exact successor, predecessor-on-positive, comparison, addition,
  multiplication, division, and modulo backend regressions above machine-word
  range;
* verify at KCore checking that an untransported term cannot use right identity
  or other algebraic laws not induced by constructor reduction; source
  expected-type checking may still accept such a term later by inserting
  explicit solver-produced transport under NFR-3.

Primary files:

* `src/Kappa/Prelude.hs`, `src/Kappa/Builtins.hs`, `src/Kappa/Check.hs`
* `src/Kappa/Core.hs`, `src/Kappa/Eval.hs`, `src/Kappa/Interp.hs`
* `src/Kappa/Backend/Repr.hs`, `src/Kappa/Backend/C.hs`,
  `src/Kappa/Backend/LLVM.hs`
* `runtime/bignum.c`, `runtime/value.c`, `runtime/prims.c`,
  `runtime/kappart.h`

Gate:

* NFR-1's constructor/computation suite passes for the intended reason;
* the checkpoint fixture rejects the untransported right-identity term while
  accepting the same term with explicit `subst`;
* closed constructor computation agrees in evaluator, interpreter, C, and LLVM;
* large natural arithmetic is exact and no runtime audit finds unary storage;
* existing arbitrary-precision `Integer` behavior and native fast paths remain
  green.

### NFR-2 - No-confusion, `Eq : IsSet`, and checked derivation (implemented)

Deliverables:

* generate the specified no-confusion package for supported ordinary data
  declarations, with stable names, constructor discrimination, constructor
  injectivity, and substitution-safe parameter handling;
* retain generated declarations as ordinary typed KCore with source
  provenance, interface identity, semantic hashing, and checkpoint validation;
* change the prelude hierarchy so `Eq a` refines `IsSet a`, and migrate all
  existing standard/user evidence without producing duplicate incoherent
  supertrait paths;
* implement `derive IsSet` and `derive Eq` as checked generation over supported
  field types and recursive SCCs;
* reject function fields, unresolved evidence, unsupported higher/path
  constructors, and recursive cycles that do not satisfy the derivation rules;
* keep derivation independent of runtime representation and never introduce
  UIP/K beyond the evidence justified by the declaration shape.

Primary files:

* `src/Kappa/Syntax.hs`, `src/Kappa/Parser.hs`, `src/Kappa/Check.hs`
* `src/Kappa/Core.hs`, `src/Kappa/CoreLint.hs`, `src/Kappa/CoreText.hs`
* `src/Kappa/Prelude.hs`, `src/Kappa/SemanticHash.hs`

Gate:

* NFR-2's positive and negative suites pass with the specified generated
  evidence and diagnostic;
* generated packages round-trip through KCoreText and interfaces;
* hostile unsupported shapes reject before backend lowering.

### NFR-3 - Algebraic hierarchy and proof-producing arithmetic solver (implemented)

Deliverables:

* migrate the prelude to
  `AdditiveMonoid` / `CommutativeAdditiveMonoid` /
  `AdditivelyNoncommutativeSemiring` / `Semiring` with coherent shared
  supertrait evidence;
* update the required `Nat`, `Integer`/`Int`, `Rational`, and ordered instances,
  and audit code that currently requests `Semiring` when it uses fewer or
  different laws;
* define typed arithmetic-domain expressions, stable semantic identities,
  canonical normal forms, and the required provider interface;
* select providers through ordinary local/global implicit resolution and freeze
  the selected evidence in the elaborated artifact;
* implement the required portable solver fragment, principal outcomes,
  underconstrained rejection, deterministic 4096-node/4096-term polynomial
  resource limits, and local diagnostics;
* insert explicit equality evidence and `subst` transport for indexed terms
  rather than extending conversion, including direct source expected-type
  checking from `NatIndex (natAdd n Nat.Zero)` to `NatIndex n`;
* canonicalize evidence occurrences at the same normalized trait application
  to the §16.3.3 step 1 deterministic representative before reification and
  record the identifying `IsSubsingleton` bridge equalities in the generated
  proof term or compact certificate (§15.8.2 amendment, 2026-07-26), while
  still rejecting law borrowing across distinct normalized trait
  applications;
* define compact arithmetic certificates with provider/domain/version/context/
  assumption/goal/normal-form identities and an independent replay checker;
* key interfaces, caches, semantic hashes, and incremental dependencies on all
  decisive provider and certificate fields.

Primary files:

* `src/Kappa/Prelude.hs`, `src/Kappa/Check.hs`, `src/Kappa/Core.hs`
* a dedicated value-arithmetic solver module, separate from
  `src/Kappa/Level.hs` and `src/Kappa/LevelEvidence.hs`
* `src/Kappa/CoreText.hs`, `src/Kappa/SemanticHash.hs`,
  `src/Kappa/Build/Types.hs`

Gate:

* all 32 NFR-3-owned suites pass;
* the evidence-canonicalization pair behaves per the amendment: the positive
  suite accepts through either named dictionary's law projection with bridge
  evidence visible in the certificate, and the distinct-goal-type negative
  still rejects;
* the right-identity source suite accepts and its verified KCore contains
  explicit transport evidence rather than an untransported conversion;
* the noncommutative and underconstrained cases reject with their portable
  diagnostics, multiplicative factors are not reordered without checked
  commutative-multiplication evidence, and polynomial expansion fails closed
  at the deterministic resource limit;
* adding an unrelated import leaves provider selection, certificate content,
  and semantic identity unchanged, checked by byte-identical canonical
  proof/certificate bodies from independently compiled variants;
* certificate mutation of every decisive field rejects independently.

### NFR-4 - Fin, Refined, subsumption, and ranges (implemented)

Deliverables:

* add the normative proof-carrying `Fin n` definition and standard constructor,
  value, weakening, equality/extensionality, and elimination API;
* add generic `Refined`, `RefinementView`, projections, constructors, and
  proof-preserving widening/subsumption;
* implement elaborator synthesis for closed literal refinements and other
  solver-supported obligations, producing ordinary proof terms;
* define `Contains`, inclusive `(..)` and exclusive `(..<)` range values, and
  canonical Nat range predicates as ordinary prelude declarations;
* preserve ordinary function lookup and implicit resolution for `contains`;
  keep `in` unavailable as expression syntax;
* preserve quantity and ownership through construction, projection,
  repackaging, patterns, generated accessors, and subsumption;
* diagnose missing proofs at the demand site without accepting an empty h-prop.

Cross-plan dependency: two bundle suites (`positive/fin-api`,
`positive/nat-no-confusion-derived-hlevel`) carry explicit notes tracking the
open forall-explicitness question (OQ-1, owned by the universes workstream);
their explicit-application spellings must be revisited when that decision
lands, before NFR-8 promotion.

Primary files:

* `src/Kappa/Prelude.hs`, `src/Kappa/Check.hs`, `src/Kappa/Core.hs`
* `src/Kappa/Parser.hs` and `src/Kappa/Pretty.hs` for range syntax only
* `src/Kappa/Usage.hs` and generated projection/pattern paths

Gate:

* all 32 NFR-4-owned suites pass;
* out-of-range and missing-proof cases reject with the specified evidence
  demand;
* `contains` passes while the paired `in` syntax suite still rejects;
* no proof field is silently duplicated or dropped before erasure checking.

### NFR-5 - Inhabitance, symbolic cardinality, and representation evidence (implemented)

Deliverables:

* extend the existing purpose-keyed inhabitance query with exact rules for
  `Nat`, `Fin`, `Refined`, canonical ranges, products, and supported finite
  ordinary data;
* add a canonical symbolic-cardinality expression AST with stable
  normalization, serialization, and semantic identity;
* produce ordinal certificates containing checked rank/unrank terms and
  round-trip evidence;
* produce exact-natural certificates connecting logical `Nat` to a non-unary
  exact runtime domain;
* produce refinement-representation certificates recording base identity,
  predicate/proof erasure, source evidence, and profile restrictions;
* reject certificates when cardinality, source identity, erased fields,
  evidence identity, or round-trip proof does not verify;
* keep purpose and backend profile in query/cache keys.

Primary files:

* `src/Kappa/Inhabitance.hs`, `src/Kappa/Check.hs`, `src/Kappa/Core.hs`
* `src/Kappa/Backend/Repr.hs`, `src/Kappa/SemanticHash.hs`
* new focused symbolic-cardinality and representation-certificate modules

Gate:

* all six NFR-5-owned suites pass;
* source reachability remains unchanged when only backend capabilities change;
* ordinal rank/unrank round trips are independently checked;
* symbolic forms are canonical and stable under alpha-renaming and import
  order.

### NFR-6 - KCoreText, interfaces, certificates, and mutation rejection (implemented)

Deliverables:

* add versioned arithmetic, ordinal, exact-natural, and refinement certificate
  declarations/references to KCore and KCoreText;
* parse, render, canonicalize, round-trip, and independently verify all
  certificate forms before any consuming checkpoint;
* serialize certificate identities and decisive fields through interfaces,
  caches, stage dumps, build artifacts, and semantic hashes;
* make missing, forged, stale, wrong-provider, wrong-context, wrong-goal,
  wrong-normal-form, wrong-rank/unrank, wrong-erasure, and wrong-profile
  mutations fail closed with the required portable aliases;
* ensure downstream KBackendIR is never constructed from an invalid artifact;
* turn both prose mutation procedures into executable fixtures.

Primary files:

* `src/Kappa/Core.hs`, `src/Kappa/CoreText.hs`, `src/Kappa/CoreLint.hs`
* `src/Kappa/SemanticHash.hs`, `src/Kappa/Build/Types.hs`,
  `src/Kappa/Pipeline.hs`
* `src/Kappa/TestHarness.hs`

Gate:

* both NFR-6 artifact suites accept original artifacts and reject every listed
  one-field mutation;
* parse/render/parse is canonical;
* an interface or cache hit cannot bypass certificate replay;
* invalid artifacts produce no accepted KBackendIR.

### NFR-7 - Verified backend representations and profile contracts (implemented)

Deliverables:

* extend the shared representation vocabulary with exact-natural,
  finite-ordinal, refinement, and conservative boxed classes backed by verified
  certificate identities;
* carry source field identity and erasure justification into KBackendIR so the
  verifier can prove quantity-`0` proof fields are absent;
* require every runnable backend to implement exact non-unary natural
  operations and reject a backend that cannot do so with
  `E_BACKEND_REQUIRED_REPRESENTATION_MISSING`;
* implement native compact finite-ordinal, packed finite-field, and unboxed
  refinement layouts only behind advertised capabilities and verified range/
  erasure evidence;
* make dynamic boundaries, FFI adapters, Kappa bridges, reflection, debug
  rendering, and ABI lowering preserve the nominal/source contract or use an
  explicit checked wrapper;
* keep overflow fallback correct in C and LLVM scalar workers, and prevent a
  certified exact natural from being narrowed at an unchecked native-width
  consumer;
* expose final verified representation queries to the harness.

Primary files:

* `src/Kappa/Backend/Repr.hs`, `src/Kappa/Backend/IR.hs`,
  `src/Kappa/Backend/Verify.hs`
* `src/Kappa/Backend/C.hs`, `src/Kappa/Backend/LLVM.hs`,
  `src/Kappa/Interp.hs`
* `runtime/kappart.h`, `runtime/value.c`, `runtime/bignum.c`,
  `runtime/prims.c`
* native FFI, bridge, dynamic, and stage-dump paths

Gate:

* all five NFR-7-owned suites pass on each applicable profile;
* exactness and proof erasure pass on every runnable backend;
* optional native compact-layout assertions run only when advertised, then are
  mandatory;
* C/LLVM/interpreter outputs agree above machine-word range;
* KBackendIR verification rejects missing certificates, stored proof fields,
  and unsupported required representations.

### NFR-8 - Promotion, adversarial audit, and closeout (implemented)

Deliverables:

* promote suites only after their declared source/artifact outcome and every
  assertion pass; never promote an incidental rejection;
* move the exact 103-suite tree to
  `tests/conformance/spec-coverage/nat-fin-refinement/` and update the manifest
  and validator atomically;
* audit generated no-confusion/derive code, local and imported providers,
  metas, refinement insertion, pattern/projection paths, interfaces, cache
  hits, KCoreText, KBackendIR, dynamic/FFI boundaries, and every backend;
* add focused unit/property tests for solver normalization, certificate replay,
  rank/unrank round trips, source/runtime inhabitance separation, overflow
  fallback, and profile capability selection;
* remove temporary compatibility primitives or document the remaining
  compiler-owned bridge with one authoritative invariant.

Gate:

* the 103-suite ledger is active with zero pending Nat/Fin/refinement suites;
* the full conformance and unit suite is green;
* interpreter/C/LLVM parity, native exactness, RC/poison/TSan lanes, package
  builds, KCoreText round trips, interface/cache tests, and performance
  non-regression gates are green;
* no advertised capability is partial and no required representation can
  silently fall back to an inexact one.

## 4. Dependency order

| stage | depends on | may proceed in parallel with |
| --- | --- | --- |
| NFR-0 | frozen spec and active ledger | early NFR-1 design |
| NFR-1 | NFR-0 observability for final promotion | NFR-2 generator design |
| NFR-2 | NFR-1 ordinary Nat/data identities | NFR-3 solver core after prelude hierarchy freeze |
| NFR-3 | NFR-0, coherent Eq/algebraic prelude | late NFR-2 implementation |
| NFR-4 | NFR-1, NFR-2 evidence, NFR-3 proof solver | none across shared elaboration paths |
| NFR-5 | NFR-4 logical definitions and NFR-3 evidence | NFR-6 grammar design |
| NFR-6 | NFR-3 and NFR-5 certificate payloads | early NFR-7 profile plumbing |
| NFR-7 | NFR-1 exact runtime and NFR-5/NFR-6 certificates | none at the consuming checkpoints |
| NFR-8 | NFR-0 through NFR-7 | none |

The implementation followed NFR-1 -> NFR-2/NFR-3 -> NFR-4 -> NFR-5 -> NFR-6
-> NFR-7 -> NFR-8. NFR-0 landed first so every later failure was observable at
its intended checkpoint; no unknown Nat/Fin harness directive remains.

## 5. Correctness risks

* **Logical/runtime Nat confusion (highest):** making the compact numeric view
  authoritative for conversion can validate false constructor equalities or
  break pattern computation. Keep the logical data view authoritative through
  KCore and require a checked representation certificate afterward.
* **Certificate self-validation:** trusting a normal form, provider ID, or
  rank/unrank claim because it was emitted by this compiler defeats the artifact
  boundary. Replay from serialized inputs with an independent checker.
* **Provider drift:** import order or overlapping instances can change which
  laws normalize an expression. Freeze coherent selected evidence and include
  it in semantic identity.
* **Proof-by-erasure:** erasing a field before proving it is a real proposition
  value can accept uninhabited refinements. Typecheck first; erase only from
  verified evidence.
* **Source/runtime analysis leakage:** using compact cardinality or field
  erasure in source reachability can delete valid branches. Keep purpose-keyed
  queries and separate cache entries.
* **Unchecked narrowing:** existing `int64` worker, array-index, timer, FFI, and
  ABI paths may consume exact naturals. Every narrowing needs an explicit range
  proof/check and a defined failure contract.
* **Generated-code authority:** no-confusion and derive output can bypass
  ordinary checks if inserted too late. Generate source-provenanced KCore and
  run the same lint/checkpoint verification as user code.
* **Performance collapse:** logical `Succ` must not imply unary runtime storage
  or iteration for large literals. Test both semantic behavior and runtime
  representation.

## 6. Verification

During every stage:

```sh
python3 scripts/validate.py docs/Spec.md
python3 scripts/validate_nat_fin_contract.py
python3 scripts/validate_universe_contract.py
cabal test
```

Focused contract run:

```sh
$(cabal list-bin exe:kappa) test \
  tests/conformance/spec-coverage/nat-fin-refinement
```

Closeout additionally requires:

* the corresponding active conformance path after promotion;
* KCoreText/interface round-trip and mutation fixtures;
* interpreter, C, and LLVM differential execution above machine-word range;
* native RC, poison, TSan, and required-representation verifier lanes;
* package builds and the existing performance gate;
* `git diff --check` and both contract validators.

## 7. Spec anchors

* §3.1.4 and §3.2: portable aliases and diagnostic families.
* §10.2.1: generated no-confusion packages.
* §14.5.2 and §28.2.2-§28.2.3: checked derivation, numeric hierarchy, and
  required instances.
* §15.8: shared proof-producing arithmetic and index solver.
* §16.1.9: refinement-view subsumption.
* §14.3.3 and §16.3.3 step 1: coherent candidate selection, deterministic
  representatives, and the §15.8.2 evidence-canonicalization boundary.
* §20.2.1: ordinary `Contains` range membership.
* §28.2: normative `Nat`, `Fin`, `Refined`, and numeric prelude surface.
* §30.2.7A-§30.2.7C: symbolic cardinality and representation certificates.
* §34.3.2A: required backend representation contracts.
* Appendix T §T.5.2: harness assertions.
* `Appendix-T-Nat-Fin-Refinement-Tests.md` §T.12.1-§T.12.9 and
  `Additional-Backend-and-Certificate-Pseudotests.md`: the active contract
  ledger and mutation requirements.
