# Kappa testing & verification strategies

How we get from "the conformance suite passes" to **high assurance that the
compiler is correct**. The organizing idea is **many independent oracles**: every
strategy below is a different, mostly-independent way to decide "is this program's
behavior right?", so a bug has to fool *all* of the relevant ones to survive.

Tracked in [`ROADMAP.md`](../ROADMAP.md) → *Track: Testing & verification
strategies*. Three of these are being **ported from the reference F#/.NET
implementation** at `/Users/wabbit/ws/kappa/`; the rest are new.

## The enabler — why most of this is cheap

Two facts make porting and cross-checking nearly free:

1. **The `--!` conformance format is shared.** Both implementations speak the same
   Appendix-T directive language (`--! mode run`, `assertNoErrors`, `assertType`,
   `assertEval`, `assertDiagnostic …`). A `.kp` fixture generated or imported by the
   reference repo runs unchanged in ours ([`src/Kappa/TestHarness.hs`](../src/Kappa/TestHarness.hs),
   [`test/Spec.hs`](../test/Spec.hs)).
2. **The CLI emits structured, portable diagnostics.** `kappa check --json` /
   `kappa run --json` produce machine-readable diagnostics keyed by **portable
   §3.1.4 codes** (the `requiredAliasTable` in [`src/Kappa/Diagnostic.hs`](../src/Kappa/Diagnostic.hs)),
   so two implementations can be compared on a stable key rather than impl-specific
   spelling.

## Current baseline (already have)

- **Conformance corpus** — `tests/conformance/**/*.kp` with `--!` assertions, run by
  `cabal test kappa-test` (1776 cases as of 2026-06-26).
- **`interp == C == LLVM` parity harness** — [`test/native/llvm-parity.sh`](../test/native/llvm-parity.sh)
  / [`run-native-tests.sh`](../test/native/run-native-tests.sh): every case must produce
  byte-identical output on the interpreter, the C backend, and the LLVM backend
  (104 cases). This is already a differential oracle — and it is *exactly* the oracle
  the ported fuzzer will feed.

## Strategy catalogue

| # | Strategy | Category | Oracle / property | Status |
| --- | --- | --- | --- | --- |
| 1 | Elpi synthesis corpus | imported | λProlog type system ⇒ well-typed ⇒ must accept | copy now |
| 2 | Elpi generator | imported | (same, fresh/deeper synthesis) | port later |
| 3 | OracleImport corpus | imported | upstream Kotlin/Scala behavior = ground truth | copy now |
| 4 | OracleImport importer | imported | (same, live refresh) | port later |
| 5 | Fuzzer | generative | crash / totality / backend-disagreement | rewire |
| 6 | Fuzzer retraining + variants | generative | (same; more generators) | follow-on |
| 7 | F#↔Haskell differential | differential | two impls of one spec cross-check | new, cheap |
| 8 | `interp/C/LLVM` parity | differential | three backends agree | ✅ have it |
| 9 | Type-preservation / subject-reduction | internal | each lowering preserves KCore types | folds into §34.3.3 |
| 10 | Metamorphic | internal | semantics-preserving transforms don't change result | new |
| 11 | Property-based (Hedgehog) | internal | totality / soundness / no-crash invariants | new |
| 12 | Roundtrip / idempotence | internal | parse∘print = id; normalize is a fixpoint | new |
| 13 | Mutation testing | suite-quality | mutating the compiler must fail a test | later |
| 14 | Elpi as a *live* checker | research | independent accept/reject adjudicator | deferred (large) |

---

## A. Imported & generated corpora

### 1–2. Elpi synthesis oracle
**What.** `/Users/wabbit/ws/kappa/tools/lambda_prolog/kappa_generator.elpi` (~2400
lines) is an independent encoding of Kappa's type system in λProlog (`typeof` /
`synth`), plus a *ranked synthesizer* over 54 expression families. `kappa_lp_generate.py`
runs Elpi to emit **5,000 provably-well-typed programs** into
`/Users/wabbit/ws/kappa/elpi-tests/lp_kappa_*/main.kp`, each carrying
`assertNoErrors` / `assertType` / `assertDeclKinds`. The oracle is a *second,
independent type checker*: anything λProlog proves well-typed, our compiler must
accept — every failure is a real divergence from the spec's typing rules.

**Move.**
- **(1) Copy the 5,000 fixtures** into `tests/conformance/elpi-generated/` and run
  them. Effort ~1h; value ⭐ highest cheap win. (Quarantine initially so a divergence
  doesn't red-bar the whole suite; promote once green.)
- **(2) Port the generator** — vendor the `.elpi`, add an Elpi opam dependency, copy
  `kappa_lp_generate.py`, point its `--validate` at our `kappa` binary. Effort ~1–2
  days. Only needed to synthesize *new* well-typed coverage as we add features.

**Deps.** Elpi (LGPL, ~2 MB, opam) for generation; none to *run* the committed `.kp`.

### 3–4. OracleImport — cross-language behavior
**What.** An F# tool ([`src/Kappa.OracleImport/OracleImport.fs`](file:///Users/wabbit/ws/kappa/src/Kappa.OracleImport/OracleImport.fs))
that harvests **other languages' regression suites** from the `/Users/wabbit/ws/datatron/`
corpus (86+ repos) — currently Kotlin `compiler/testData/codegen/box/` and Scala 3
`tests/patmat/` — and regex-translates them into Kappa `.kp` fixtures with
`assertEval`. Each upstream test encodes a real fixed bug, so this is real-world
behavior the synthetic generators miss. We already have **391 imported cases** in
[`tests/pending-import/`](../tests/pending-import).

**Move.**
- **(3) Land `pending-import/391`** (wire into the suite, triage failures) and copy
  any freshly generated oracle `.kp`. Effort ~1–2h.
- **(4) Port the importer** to Haskell (`aeson` + `regex-tdfa`, ~300 LOC core +
  CLI) for live refresh as upstream suites grow. Effort ~4–8h. The `.kp` outputs are
  language-agnostic, so the importer is only worth porting if we want to keep pulling.

**Deps.** The `datatron` corpus (already on disk) as the source; no Kotlin/Scala
toolchain (it reads pre-harvested source text).

---

## B. Differential oracles

### 7. F#↔Haskell differential — ⭐ highest-value new strategy
**What.** Two mature, independent implementations of one spec are oracles for each
other. Run every shared `.kp` through both `kappa` binaries and compare:
(a) **portable diagnostic codes** via the §3.1.4 `portableAlias` table (robust to
impl-specific spellings), and (b) **run-mode stdout + exit code**. Any disagreement
is a bug in one of them — and it tells us *which corpus case* exposes it.

**Build.** A wrapper script (`scripts/differential.sh` or a `cabal` test target)
that shells out to both binaries with `--json`, diffs the portable-code multiset and
the run output, and consults a small **known-divergence allowlist** (one impl is
sometimes ahead on a feature; that's an expected, annotated difference, not a
failure). Effort ~1 day. Pairs with every *generator* above: elpi/fuzzer/import
produce inputs, this cross-checks them.

**Deps.** A built reference binary (`Kappa.Compiler.Cli`) available in CI or locally.

### 8. interp/C/LLVM parity — ✅ already have it
Keep extending the case set; it is the fuzzer's runtime oracle.

---

## C. Generative fuzzing

### 5. Port the fuzzer
**What.** `/Users/wabbit/ws/kappa/scripts/kappa_fuzz_lib.py` (≈4400 lines) is a
generative fuzzer + differential oracle + trace-dedup/promote loop: it generates
random programs, runs them on multiple backends, **classifies** (ok / diagnostic /
crash / timeout / **backend-disagreement**), `ddmin`-**minimizes** failures,
**clusters** by execution-trace hash, and **promotes** representatives into the
permanent corpus. The bulk of it is compiler-agnostic (drives a CLI).

**Move.** Rewire the binary path and backend names to our `kappa` + `interp/C/LLVM`
(the parity harness *is* its oracle); reuse `bounded_run.py`, `triage_pending.py`,
the minimize/cluster/promote pipeline as-is. Effort ~1–2 days. Value ⭐ high — on the
reference it has caught real crashes, timeouts, and interp↔codegen mismatches. The
F#-specific bits (`promote_new_tests.py`, `test_fast.py` calling `dotnet`) are
replaced by our `cabal test` driver.

**Deps.** Python; PyTorch *only* for the LSTM generator (see #6 — swappable).

### 6. Retraining & generator variants
The neural generator is the *swappable* component; the pipeline is the value.
- **Auto-retrain on data change.** Training is fast, so make it cheap and frequent:
  hash the training corpus (committed fixtures + promoted finds) and **retrain
  whenever the hash changes** — a CI/pre-fuzz step, no manual trigger.
- **Try a transformer / LLM-style generator** instead of the char-LSTM — better
  long-range structure (balanced blocks, scoped binders) for a dependently-typed +
  effectful language. Keep the same generate→run→classify interface.
- **A grammar-directed generator is a *separate, parallel* fuzzer**, not a
  replacement — different bias, different bugs. *The more the merrier:* run the
  grammar generator and the learned generator side by side, both feeding the same
  oracle + promote pipeline. (A grammar/type-directed generator also has no PyTorch
  dependency, so it can run anywhere.)

---

## D. Internal property / consistency oracles (no external deps)

### 9. Type-preservation / KCore subject-reduction — highest-leverage internal
KCore is typed and Kappa targets Core-level verification, so a check that **each
lowering/reduction preserves types** is a strong, always-on oracle with no external
dependency. This is literally the **§34.3.3 legality verifier**
([`src/Kappa/Backend/Verify.hs`](../src/Kappa/Backend/Verify.hs), `kappa verify-kbackendir`):
our compiler-architecture work *doubles* as a testing strategy. Extend it from the
current legality checkpoints toward full subject-reduction across the pipeline.

### 10. Metamorphic testing
Apply **semantics-preserving transforms** to corpus/generated programs and assert
typeability and output are unchanged: α-renaming, η-expansion, let-inlining,
reordering independent bindings, dead-code insertion, adding redundant type
annotations. The program is its own oracle (no ground truth needed); especially good
at elaboration-order and flow-refinement bugs. Effort ~medium; integrates into
`cabal test`.

### 11. Property-based / typed-term generation (Hedgehog/QuickCheck)
A native, in-process type-directed term generator (the elpi oracle's idea, in
Haskell) checking invariants directly: *total programs terminate*, *well-typed ⇒
accepted*, *no compiler crash on any well-formed AST*, *interp ≡ compiled*. No
external toolchain; shrinking comes for free. Effort ~medium.

### 12. Roundtrip / idempotence
Cheap algebraic checks: `parse ∘ pretty-print = id`; `normalize ∘ normalize =
normalize`; the formatter is a fixpoint. Catches parser/printer asymmetries and
normalization bugs. Effort ~small.

---

## E. Suite quality

### 13. Mutation testing
Mutate the *compiler* (flip a comparison, drop a check) and confirm **some test
fails**. Measures where the corpus is thin rather than whether the compiler is
correct — most useful once the corpus above is large. Effort ~medium, ongoing.

---

## F. Research / deferred

### 14. Elpi as a *live* checker oracle
Today the λProlog encoding only *synthesizes* well-typed programs. Extending its
judgment to **classify arbitrary** programs (accept/reject, including deliberately
ill-typed ones) would let it adjudicate fuzzer output directly — *oracle-rejects but
compiler-accepts = a soundness bug*. **High effort:** this is essentially writing a
second, complete, independent type checker for Kappa (decidable inference over the
full dependent+effect surface), so it is **deferred** until the cheaper oracles
above are exhausted. The synthesis direction (#1–2) gives much of the value for a
fraction of the cost.

---

## Recommended sequencing

1. **Now (cheap, all differential):** copy the **5,000 elpi fixtures** (#1) and run
   them; land **pending-import/391** (#3); stand up the **F#↔Haskell differential**
   wrapper (#7). Each surfaces real divergences immediately.
2. **Force-multiplier:** port the **fuzzer** (#5) onto our CLI + `interp/C/LLVM`
   oracle; add **auto-retrain-on-change** + a **grammar generator** as a parallel
   fuzzer (#6). Now the generators feed both the parity oracle and the differential.
3. **Internal, always-on:** grow **type-preservation** into the §34.3.3 verifier
   (#9); add **metamorphic** (#10), **Hedgehog** (#11), and **roundtrip** (#12)
   targets to `cabal test`.
4. **Later:** **mutation testing** (#13) once the corpus is large; the **live Elpi
   checker** (#14) only if the cheaper oracles stop finding bugs.

---

## Coverage-guided test selection (the method)

When a generator/import produces a large candidate corpus, **do not bulk-import** —
most cases are coverage-redundant and only slow the suite. Select a minimal subset
that ticks *compiler* code the current suite doesn't, via HPC:

1. Build the compiler instrumented, into an **isolated builddir** so the shared
   `dist-newstyle` (and parallel work) is untouched:
   `cabal build --enable-coverage --builddir=/tmp/kappa-cov exe:kappa`.
2. **Baseline** `.tix` = the current suite's coverage — run the instrumented binary
   once over the whole suite (`kappa test tests/conformance`); it runs in-process so
   one exit writes one tix covering everything.
3. **Per candidate**, run instrumented `kappa check <file>` (in a clean cwd; the exe
   writes `kappa.tix` on exit). The tix is text — `Tix [TixModule "pkg/Mod" hash n
   [ticks…]]` — so parse the non-zero boxes directly; a candidate's *marginal* =
   its boxes − baseline.
4. **Greedy set-cover** over the marginals → the minimal subset that adds new
   coverage. (`hpc report` needs `--hpcdir` per mix parent:
   `<builddir>/…/hpc/vanilla/mix/{kappa-haskell-…-inplace, …-inplace-kappa}`.)

Reproducible scripts: `/tmp/elpi_greedy_cover.py` (parse-tix + greedy),
`/tmp/elpi_llvm_diff.py` (the backend differential). Lighter proxies when an HPC
build is too costly: pipeline-**trace hashing** (the fuzzer's, coarser) or
**AST-feature** coverage.

## Run log — 2026-06-26 (elpi + pending-import recon)

Ran both corpora read-only against the compiler (nothing bulk-imported):

- **elpi 5,000 → 1,821 pass (36%).** *Every* failure is "we reject a program the
  λProlog oracle proved well-typed" (0 are decl-kind/type-format divergences — our
  reporting matches the reference). They collapse to **one theme: block-local
  declarations** — 2,962 layout (`E_UNEXPECTED_INDENTATION`/`E_EXPECTED_SYNTAX_TOKEN`
  from nested `block`s) + 217 type/semantic (`E_UNSUPPORTED "local declaration form
  not supported inside block"` ×62, …). A focused, real spec-coverage gap (local
  `trait`/`instance`/`effect`/`summon` + nested-block layout), **not** 3,000
  scattered bugs — the highest-leverage thing the elpi corpus surfaced.
- **pending-import** is a **pre-triaged staging backlog** (per its README), not new
  breakage; soundness buckets to revisit are `we-accept-negative/` (67) and
  `we-reject-positive/` (177).
- **LLVM differential:** 122/122 sampled `result:Int` positives agree
  `interp == C == LLVM` (0 divergence, 0 backend build failures) — the backend is
  solid on the elpi constructs, so no backend-bug regression tests to harvest.
- **Coverage-guided import:** baseline suite = **59.0%** compiler-expression coverage.
  All 1,821 passing positives are individually distinct but **coverage-redundant**:
  greedy HPC set-cover → **13 tests** capture the entire **+0.16%** (248 boxes,
  almost all `Kappa.Check`) that the full 1,821 would add. Imported only those 13 →
  [`tests/conformance/elpi-generated/`](../tests/conformance/elpi-generated) (gate
  1781→1794, all pass). They exercise multi-shot `deep handle` effects, `Set`/`Map`
  comprehensions with conflict resolution, elvis chains — paths the curated suite
  missed.

## Coverage-driven new tests (2026-06-26)

Two uses of the coverage data beyond selection — generating tests and finding
redundancy.

### (A) New tests from untested error paths
The §3 contract defines ~236 emittable diagnostics; `(codes emitted in src/Kappa)
− (codes any conformance test references)` = **113 untested, 71 core-language**.
Each is an error path no test triggers. Crafted minimal trigger programs (find the
emission site → minimal `.kp` → confirm the code is emitted), then **independently
re-verified** every one with `kappa test`. Result: **52 negative tests** in
[`tests/conformance/diagnostics-coverage/`](../tests/conformance/diagnostics-coverage),
adding **+0.36% compiler coverage (558 boxes, ~83% in `Kappa.Check` error paths)** —
2× the elpi import. The other 19 are out of scope for single-file conformance
(`E_CONFIG_*`/`E_DEPENDENCY_*`/`E_BACKEND_*` need `build --manifest`; `E_INTERNAL*`
are invariants; `E_IMPORT_CYCLE` needs a multi-file set).

*Process lesson:* the crafting workflow's `args` reached the script as a JSON
**string** (not an array), so `slice(i,i+8)` cut 8-**character** fragments → 216
garbage-labelled agents (7.4M tokens). Guard in workflow scripts:
`const xs = typeof args === 'string' ? JSON.parse(args) : args;`. The run was
salvaged by filtering to the real target codes + independent re-verification — the
re-verification is why the bad batching didn't matter.

### (B) Coverage-based dedup (catches what naive dedup misses)
Per-test compiler-coverage signatures over the 1,362 real tests (those with `--!`
directives; auxiliary suite files excluded). Two signals: **identical coverage
signature** (same boxes ticked) and **no-unique-box** (adds no box another test
covers). The sharp one is identical-coverage: **87 strong-duplicate clusters**
(identical coverage AND identical assertions):

- **55 byte-identical** copies — the `X` vs `category-X` rename artifact; naive
  textual dedup already catches these.
- **32 textually differ but coverage + assertion identical** — *what naive dedup
  misses.* Two kinds: (i) trivial near-copies differing only in module name/comments
  (`elvis-positive-default` ↔ `expressions-elvis-positive-default`, the `queries-*`
  duplicates, …); (ii) **genuinely different programs, same behavior** — the
  positivity trio (`positivity-mutual-reject`/`-reject-negative`/`-reject-rose` all
  reject `E_DATA_NOT_STRICTLY_POSITIVE` via one path), `match/bool-missing-case` ↔
  `match/not-exhaustive`, and many `unicode-text-appendix-t-*` pairs (distinct
  invalid-scalar inputs hitting one validation path).
- 6 clusters share a path but assert *different* things → keep (distinct contracts).

These are **review candidates, not auto-deletes**: kind (ii) and the unicode pairs
pin distinct spec examples even though the compiler treats them identically. The
no-unique signal (1,021/1,362) is too weak to act on — conformance tests overlap by
design (they pin *behaviors*, not unique code paths). Reproduce via
`/tmp/pertest_collect.py` + `/tmp/dedup_analyze2.py`.
