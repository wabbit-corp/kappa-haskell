# Unified Derive / Canonical Evidence - Implementation Plan

Status: **Specification applied; implementation planned (2026-08-02).**
`docs/Spec.md` contains the unified-`derive` / canonical-evidence patch from
`docs/Kappa_Derive_Automation_v2/READY_TO_INSERT_SPEC_CHANGES.md` plus its
companion `APPENDIX_T_HARNESS_AMENDMENTS.md`, applied at the exact recorded
base (`Spec(108)` sha `719bab30`, compiler commit `3014a0d9`) and green under
`scripts/validate.py`. The prose patch's ~40 numbered amendments were applied
by an eight-batch sequential pass with independent per-instruction fidelity
verification; the only deliberate deviation is subsection numbering
`14.5.0`/`14.5.0A` for the patch's `14.5.0A`/`14.5.0B` (the repository
validator forbids a lettered first subsection), recorded here as provenance.

The contract is materialized as a **109-suite** tree under
`tests/pending-import/derive-automation/`, imported verbatim from
`docs/Kappa_Derive_Automation_v2/tests/` with per-suite
`-- STATUS(3014a0d9)` lines. `scripts/validate_derive_automation_contract.py`
fixes the manifest/tree contract and passes at 109. Conformance fixtures the
revision invalidates are rewritten and staged under
`tests/pending-import/derive-automation/retargeted/` (see §1.4). None of
these suites is eligible for active conformance yet.

The revision makes `derive` one expected-type-directed elaboration protocol
(expressions, instance bodies, synthesized members and supertraits,
declaration-level deriving, generated obligations), introduces independently
checked `evidence uniqueness` certificates beside sealed-coherent evidence,
adds `fallback instance` resolution (the `Eq -> Equiv` bridge becomes one),
lands portable binder-aware function extensionality (`funExt`/`forallExt`/
`borrowFunExt`) with `Reflects` and Hedberg, rebuilds the order hierarchy
(`Preorder` -> `PartialOrder` -> total `Ord`; `compareTotal` removed),
refines `Alternative` under `Applicative`, and specifies the proof-automation
engine (providers, induction, helper lemmas, logical-cost profiles, hammer
tier) with two-level evidence identity in §33.2.1.

This plan is the implementation authority for that contract. `ROADMAP.md`
contains only the short stage ledger.

## 0. Objective and boundaries

Implement the current `docs/Spec.md` contract so that:

1. `derive` / `derive (T)` are expression atoms elaborated by the unified
   judgment with deterministic providers, logical-cost budgets, and
   `DeriveRecord` observability (§14.5, §16.3.2A);
2. traits may carry verified independent `evidence uniqueness` certificates;
   sealed-coherent goals reject fresh expression-level construction
   (`E_EVIDENCE_CONSTRUCTION_SEALED`) while independently unique goals allow
   it, including the narrow local-orphan relaxation (§14.1.1A, §14.3,
   §30.1.1);
3. instance completion is facet-based and order-independent, with prefix
   `derive member : T` synthesized members, `derive C` supertrait items,
   automatic omitted-proposition completion, and no incomplete-self access
   (§14.2, §14.3.4A);
4. `fallback instance` resolution runs strictly after ordinary resolution
   with negative absence dependencies serialized for incremental correctness;
   the `Eq -> Equiv` bridge is the standard fallback (§14.3.1B, §14.3.5);
5. the portable foundation supplies `funExt`/`forallExt`/`borrowFunExt`,
   `Reflects`, Hedberg, and the h-level closure theorems as ordinary
   first-class functions (§11.4.1, §14.4);
6. the revised trait hierarchy lands: h-level traits with uniqueness
   certificates, relation-law traits over explicit `BoolRelation` indices,
   `Preorder`/`PartialOrder`/total `Ord` (no `compareTotal`), lawful
   `Alternative` under `Applicative`, and the prelude inventory of §14.x of
   the patch;
7. derivation, uniqueness checking, and fallback selection integrate with
   facet SCCs, KCore (no unresolved requests), interfaces, checkpoint
   verification, and the two-level `EvidenceSemanticIdentity` /
   `EvidenceArtifactFingerprint` coherence model (§9.5.2, §30.2, §33.2.1,
   §34.x); and
8. the new Appendix T surface (5 capabilities, ~30 directives, stage-dump and
   cross-step assertions) is typed and routed through public queries.

Deliberate non-goals: no `auto` spelling; no wall-clock-dependent acceptance;
no silent classical logic; no UIP/K or judgmental funext; learned/external
providers never enlarge portable acceptance beyond checked reconstruction;
`Equiv` stays non-reflecting and sealed; automation percentage targets
(§14.5.12) are benchmarks, not gates.

## 1. Current implementation audit

### 1.1 Existing substrate to keep

* `src/Kappa/Check.hs`: NFR-era checked derivation (`derive IsSet/Eq/...`),
  instance resolution and coherence, facet SCC machinery from the MSI
  campaign's substrate, branch-fact and solver integration points.
* `src/Kappa/Arithmetic.hs` and the §15.8 solver: the required decision
  procedures the derive portfolio reuses (Presburger, algebraic
  normalization, finite domains).
* `src/Kappa/CoreText.hs` / `src/Kappa/SemanticHash.hs` /
  `src/Kappa/Build/Types.hs`: versioned certificates, semantic identity, and
  fingerprint patterns for the new certificate and two-level identity model.
* `src/Kappa/TestHarness.hs`: typed-directive registry to host the new
  assertion surface.

### 1.2 Contract gaps

* No expression-level `derive` atom; no unified judgment, providers, plans,
  logical-cost profiles, `DeriveRecord`s, induction planner, helper-lemma
  synthesis, or counterexample records.
* No `evidence uniqueness` clause, certificates, construction modes, or
  local-orphan relaxation; all trait evidence is effectively sealed.
* No `fallback instance` form, ordering stage, or negative absence
  dependencies; the `Eq -> Equiv` bridge is an ordinary instance.
* No prefix `derive member : T` members, `derive C` supertrait items, facet
  completion (§14.3.4A), or automatic omitted-proposition completion.
* `funExt`/`forallExt`/`borrowFunExt`, `Reflects`, `hedberg`, `eqReflect`,
  the h-level closure terms, `BoolRelation`, the `Is*` relation-law traits,
  `Preorder`, `PartialOrder` are absent; `Ord` directly supplies `<=`
  (`compareTotal` was spec-only and never implemented).
* The 17 new `E_DERIVE_*`/`E_EVIDENCE_*`/`E_INSTANCE_*` aliases and their
  families are unregistered; none of the new Appendix T directives or
  capabilities exist.

### 1.3 Pending contract baseline

`tests/pending-import/derive-automation/manifest.json` owns 109 suites
(inventory: `docs/Kappa_Derive_Automation_v2/TEST_MANIFEST.md`):

| manifest group | theme | owner stage |
| --- | --- | --- |
| T12.1 (9) | expression forms, context, quantities, proof relevance | DA-1, DA-7 |
| T12.2 (11) | forall vs arrows, extensionality, h-level closure | DA-2 |
| T12.3 (5) | `Reflects` and equality reflection | DA-2 |
| T12.4 (13) | independent uniqueness, first-class evidence | DA-3 |
| T12.5 (11) | synthesized members, omitted propositions | DA-4 |
| T12.6 (12) | fallback instances, `Eq -> Equiv`, direct override | DA-5 |
| T12.7 (11) | `Preorder`/`PartialOrder`/total `Ord` | DA-6 |
| T12.8 (4) | lawful `Alternative` | DA-6 |
| T12.9 (11) | induction, helpers, structural/indexed proofs | DA-7 |
| T12.10 (12) | theorem scope, incremental, mutations, permutation | DA-8 |
| T12.11 (8) | whole-instance derivation | DA-4 |
| T12.12 (2) | decision procedures, arithmetic, normalization | DA-7 |

The 2026-08-02 audited run over all 109 suites with the clean `3014a0d9`
compiler reports **0 passed, 0 failed, 20 unsupported, and 89 harness
errors** - every suite requires the new capabilities, so suites whose
`requires capability` lines are evaluated before their unknown `assertDerive*`
directives report `Unsupported` and the rest are harness errors. Each suite
carries its result in a `-- STATUS(3014a0d9)` line.

### 1.4 Retargeted conformance fixtures

The revision's conformance-breakage audit (five themed sweeps plus
adversarial verification; 6 candidates, all 6 confirmed) stages the
invalidated fixtures, rewritten to the new contract, under
`tests/pending-import/derive-automation/retargeted/` (4 loose fixtures + 2
directory suites; two came from the ACTIVE nat-fin-refinement contract,
whose manifest now counts 102). Baseline at `3014a0d9`: 2 pass / 4 fail.
Per-file dispositions: that directory's README. They promote back to their
original homes at DA-9. Notably `handwritten-eq-missing-laws` already passes
its flipped accept expectation - the NFR-era derive machinery appears to
synthesize the Eq law members - which DA-0 must confirm is for the intended
reason before any early return.

## 2. Architectural invariants

* **Determinism before speed.** Provider parallelism must never change the
  accepted result, selected plan, generated KCore, or diagnostics; canonical
  logical order decides everything (§14.5.4, §14.5.10).
* **Checked or absent.** Every derivation result is ordinary checked KCore or
  an independently checked certificate; `Blocked` never crosses a completion
  boundary; KCore contains no unresolved request (§14.5, §30.2).
* **Uniqueness is earned, never assumed.** The independence conditions of
  §14.1.1A (no `IsTrait G`, no coherence-for-`G`, no self-reference) are the
  soundness boundary; the restricted evidence-extensionality principle exists
  only inside uniqueness checking.
* **Fallback absence is a dependency.** A fallback selection is only as valid
  as its serialized negative absence fact; stale absence must invalidate, not
  silently persist (§14.3.1B).
* **Two identities, never conflated.** `EvidenceSemanticIdentity` governs
  coherence; `EvidenceArtifactFingerprint` governs reproducibility and trust;
  fingerprint equality never substitutes for a failed coherence check
  (§33.2.1).

## 3. Stages, ordering, and gates

### DA-0 - Contract freeze and harness observability

Keep the 109-suite manifest and validator authoritative (extended over
`retargeted/`); register the five diagnostic families and 17 aliases with
§3.2.4A payloads; add the five §T.4 capabilities and every new §T.5.2/§T.5.3/
§T.7 directive as typed directives over public queries; unknown backing
queries report `Unsupported`. Gate: all 109 suites parse their directives;
the 89 harness errors convert to `Unsupported`/fail; validators green.

### DA-1 - Grammar and expression forms

`derive`/`derive (T)` atoms, prefix `derive member : T`, `derive C`
supertrait items, `evidence uniqueness = expr` clause, `fallback instance`,
soft keywords; `E_DERIVE_EXPECTED_TYPE_REQUIRED` for bare derive without a
rigid expected type; parser/AST plumbing only (elaboration may stub to
existing checked derivation). Files: `src/Kappa/Parser.hs`,
`src/Kappa/Syntax.hs`. Gate: T12.1 syntax suites parse; no conformance
regression.

### DA-2 - Foundation: extensionality, Reflects, h-level closure

`Reflects` + helpers, `funExt`/`forallExt`/`borrowFunExt` foundation
constants, `happly` family, `hedberg`, `eqReflect`, `piIsProp`/`piIsSet`/
`sigmaIsSet`, binder-sensitive h-level closure rules. Files:
`src/Kappa/Prelude.hs`, `src/Kappa/Check.hs`, `src/Kappa/Eval.hs`. Gate: all
T12.2/T12.3 suites pass.

### DA-3 - Evidence uniqueness and construction modes

`evidence uniqueness` checking with the independence dependency graph and
restricted extensionality principle; certificates serialized/rechecked;
`EvidenceConstructionMode` in KFrontIR/interfaces; sealed rejection
(`E_EVIDENCE_CONSTRUCTION_SEALED`); local-orphan relaxation. Files:
`src/Kappa/Check.hs`, `src/Kappa/CoreText.hs`, `src/Kappa/Build/Types.hs`.
Gate: all T12.4 suites pass, including circular-certificate rejection and
mutation fixtures.

### DA-4 - Instance facet completion

§14.3.4A completion graph; synthesized members/supertraits; automatic
omitted-proposition completion under the baseline profile;
`E_DERIVE_INCOMPLETE_SELF`; whole-instance `instance G = derive` /
declaration-level `derive G` unified over the same protocol. Gate: T12.5 and
T12.11 suites pass; completion is member-order-invariant.

### DA-5 - Fallback instances

The post-ordinary resolution stage, coherence among survivors
(`E_INSTANCE_FALLBACK_AMBIGUOUS`), negative absence dependencies through
queries/interfaces/caches, the `Eq -> Equiv` fallback bridge, size-change
instance termination (`E_INSTANCE_SEARCH_NONTERMINATING`). Gate: all T12.6
suites pass, including direct-`Equiv`-overrides-fallback and staleness
fixtures.

### DA-6 - Revised standard traits

H-level traits with uniqueness clauses (member spellings `pathIsProp`/
`pathIsSet`); `BoolRelation` + `IsEquivalence`/`IsPreorder`/`IsPartialOrder`/
`IsTotalOrder`; `Preorder`/`PartialOrder`/total `Ord` with the synthesized
`Eq` plan (`leq x y && leq y x`), comparison helpers, `compareTotal`
removal, `Ord TypeLevel` `<=` recognition via `Preorder.leq`; lawful
`Alternative` under `Applicative`; prelude inventory and required h-level
instances (`IsEmpty Void`, `IsProp Void`, `IsContr Unit`, `IsProp Unit`).
Gate: T12.7/T12.8 suites pass; the whole conformance corpus is re-run and
order/equality regressions triaged.

### DA-7 - The derivation engine

Provider model and obligation graph, required portfolio (§14.5.5), equality
engines with set/path-sensitive modes (§14.5.6), automatic induction
(§14.5.7), helper lemmas and refutation (§14.5.8), theorem scope (§14.5.9),
profiles/budgets/determinism (§14.5.10-11), inhabitation and hammer tiers
(§14.5.13), parametricity transfer (§14.5.14), reconstruction/minimization
(§14.5.15). Gate: T12.1 (semantic), T12.9, and T12.12 suites pass;
determinism verified under forced provider-order permutation.

### DA-8 - Pipeline, KCore, interfaces, incremental

§9.5.2 derive dependency roles; BODY_RESOLVE integration; KCore lowering
with retained provenance/certificates; §12.7 checkpoint verification;
interface serialization (§34.1.9); two-level identity in §33.2.1 coherence;
query determinism and absence-dependency invalidation. Gate: all T12.10
suites pass, including certificate-mutation and cross-step
fingerprint/identity assertions.

### DA-9 - Promotion, adversarial audit, closeout

Promote the 109 suites to `tests/conformance/spec-coverage/derive-automation/`
and return retargeted fixtures; adversarial probes (forged uniqueness
certificates, circular independence, fallback staleness, sealed-construction
smuggling via helpers, proof-relevant merges without `IsSet`); property tests
for determinism and budget monotonicity; ROADMAP flip. Gate: zero pending
suites; full gates green.

## 4. Dependency order

DA-0 first (observability); DA-1 -> DA-2 -> DA-3 -> DA-4 -> DA-5 -> DA-6,
with DA-7 incremental from DA-2 onward (its portfolio grows per stage) and
DA-8 consuming DA-3/DA-5/DA-7 artifacts; DA-9 last. DA-6 is deliberately
after DA-3/DA-4/DA-5 because the revised traits depend on synthesized
members, uniqueness certificates, and the fallback bridge.

## 5. Correctness risks

* **Circular uniqueness (highest):** a certificate that smuggles `IsTrait G`
  or coherence back in collapses the sealed/unique distinction; the
  independence graph check is load-bearing and must be adversarially probed.
* **Fallback staleness:** missing absence-dependency invalidation silently
  freezes bridge selections across builds.
* **Determinism erosion:** any completion-time or worker-order influence on
  plan selection breaks portability; permutation property tests from DA-1.
* **Order-hierarchy migration:** `compareTotal` removal and the
  `Preorder`-supplied `<=` touch every ordered API; conformance re-runs gate
  DA-6.
* **Proof-relevant merging:** merging path candidates without independent
  `IsSet` silently assumes UIP; path-sensitive mode is the default.
* **Engine scope creep:** providers must construct propositional evidence
  only - never extend conversion or bypass visibility.

## 6. Verification

```sh
python3 scripts/validate.py docs/Spec.md
python3 scripts/validate_derive_automation_contract.py
python3 scripts/validate_module_scc_ir_contract.py
python3 scripts/validate_nat_fin_contract.py
cabal test
```

Focused run: `$(cabal list-bin exe:kappa) test` over each suite root under
`tests/pending-import/derive-automation/` (roots are independent; never
compile the tree as one suite).

## 7. Spec anchors

* §3.1.4, §3.1.5A, §3.1.10, §3.2.4A: aliases, provenance, obligations,
  families.
* §5.2, §16.1, §14.1.4, §14.2, §14.3: grammar (soft keywords, deriveExpr,
  supertrait items, trait members, fallback instances).
* §11.3, §11.4.1, §11.5: forall audit rule, `Reflects`, extensionality,
  Hedberg, `eqReflect`.
* §11.1.4, §14.1.1, §14.1.1A: evidence modes and uniqueness certificates.
* §14.1.4, §14.2, §14.3.4A: completion modes, member forms, facet completion.
* §14.3.1B, §14.3.5: fallback instances and search termination.
* §14.4: h-level traits, closure theorems; §14.1 `Equiv`/`Eq`; relation-law
  traits; `Preorder`/`PartialOrder`/`Ord`; Chapter 28 `Alternative` and
  prelude inventory.
* §14.5-§14.5.15, §16.3.2A, §16.3.3: the unified derivation engine.
* §9.5.2, §30.2, §33.2.1, §34.1.9, §34.2.x: pipeline, KCore, coherence,
  interfaces, incremental.
* Appendix T §T.4/§T.5.2/§T.5.3/§T.7/§T.10: capabilities, directives,
  inventory; `std.prelude.eqToEquivFallback` selector.
* `tests/pending-import/derive-automation/` + `manifest.json` +
  `docs/Kappa_Derive_Automation_v2/TEST_MANIFEST.md`: the staged contract.
