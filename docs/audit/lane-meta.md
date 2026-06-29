# Lane META — Tests/Harness/Overfitting/Perf + Scope/Conformance

Hostile audit. Stance: disprove compliance. Every IMPLEMENTED row is backed by a probe
(input + observed output). MISSING/WEAK rows give the exposing probe and expected-vs-actual.
Binary used: `dist-newstyle/.../x/kappa/build/kappa/kappa` (built clean with `-Werror`).
Probe sources live under `/tmp/ht/` and `/tmp/probe/`.

Legend: IMPLEMENTED+TESTED | IMPLEMENTED-WEAKLY-TESTED | MISSING |
INTENTIONALLY-UNSUPPORTED(cite) | SPEC-CONFLICT(cite) | UNCLEAR.

---

## §2 Language profiles, feature gates, versions, conformance (CORE, Part I)

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §2.1 | MUST determine active language profile + feature-gate set before successful elaboration | IMPLEMENTED-WEAKLY-TESTED | There is a fixed implicit profile (kappa-v1, `unicode-names` off). No source pragma / manifest / flag can change it; cannot probe a *second* profile. | Single hard-coded profile; no profile-selection surface, but a fixed-profile impl is internally consistent. |
| §2.1 | Parser recognition ≠ acceptance; gated construct fails with feature-gating diagnostic | IMPLEMENTED+TESTED | `/tmp/probe/uni.kp` `let π = 3` → `error[E_FEATURE_INACTIVE] (kappa.feature.gated): unquoted Unicode identifiers require the 'unicode-names' feature gate (Spec §2.1A)`; exit 1. Parser tokenizes, lexer rejects. | Correct family `kappa.feature.gated`. |
| §2.1 | Feature-gate diagnostic MUST identify: construct, owning gate, **active language profile**, inactive/stronger-gate, **provenance of gate settings**, implication path, repair | IMPLEMENTED+TESTED | Feature-gate diagnostics carry structured payload fields including `constructKind`, `owningGate`, `activeProfile`, `activeGates`, `gateActive`, `gateProvenance`, and `strongerGateRequired`; harness fixtures assert these payloads. | Remaining work is broader profile-selection surface, not the payload/assertion mechanism. |
| §2.1A | `unicode-names` is a standardized optional gate; kappa-v1 does NOT imply it | INTENTIONALLY-UNSUPPORTED (§2.1A para "The `kappa-v1` portable language profile does not imply `unicode-names`") | Gate is inactive by default and rejected; backtick identifiers still available. | Correctly inactive-by-default per §2.1A. |
| §2.2 | Version terminology (Kappa v1) | IMPLEMENTED-WEAKLY-TESTED | Non-normative; impl targets v1. | n/a |

## §4 Unsafe and Debug Facilities (CORE classification, Part I)

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §4.1 | Safe portable subset excludes `unhide`/`clarify`/`assertTerminates`/`assertReducible`/`assertTotal`/`unsafeAssertProof`/`std.debug`; these remain part of the language spec | PARTIAL / IMPLEMENTED+TESTED for assertion/proof escapes | `assertTerminates`, `assertReducible`, legacy `assertTotal`, and `unsafeAssertProof` are recognized, gated, and audited in the current harness profile (`Parser.hs`, `Check.hs`, `TestHarness.hs`; fixtures under `tests/conformance/unsafe_debug/`). `std.debug` is still absent. `unhide`/`clarify` import semantics remain a separate import-surface gap. | This row was stale: the assertion/proof escape surface is no longer missing. Do not read this as full §4 package-mode compliance; profile/build-manifest provenance and `unhide`/`clarify` still need audit. |
| §4.2 | Build-level gating; violations are compile-time errors naming the offending form AND the disallowing build setting (`allow_*`) | PARTIAL / IMPLEMENTED+TESTED for assertion/proof escapes | Test directives wire `allow_assert_terminates`, `allow_assert_reducible`, and `allow_unsafe_assert_proof`; gated-negative fixtures produce unsafe/debug diagnostics when disabled and positive fixtures pass only when enabled. | Remaining gap: full build-profile provenance and `allow_unhiding`/`allow_clarify` are not proven by this lane. |
| §4.3 | `unhide`/`clarify` semantics + error if build setting disabled / definition inaccessible | MISSING | Parsed into `ImportItem` flags (`Parser.hs:872`) but no semantic effect and no gating error probed. | |
| §4.4 | `assertTerminates`/`assertReducible`/`assertTotal` escapes + δ-reduction/recording semantics | IMPLEMENTED+TESTED for current harness profile | `tests/conformance/unsafe_debug/assert-terminates-enabled.kp`, `assert-reducible-enabled.kp`, and gated-negative siblings exercise acceptance, reducibility behavior, and ledger recording. | Package-artifact recording beyond the harness-profile ledger is not separately audited here. |
| §4.5 | `unsafeAssertProof` prelude helper + interface recording | IMPLEMENTED+TESTED for current harness profile | `tests/conformance/unsafe_debug/unsafe-assert-proof-*.kp` cover the gated prelude helper, proof-use restrictions, and ledger entries. | Full interface/package artifact publication remains tied to the broader audit-ledger work. |
| §4.6 | Backend-specific surface escapes excluded from safe subset | INTENTIONALLY-UNSUPPORTED (§4.6 "If an implementation provides such a facility") | No backend escape facility is offered; §4.6 is conditional on *providing* one. | Not providing one is conforming. |
| §4.7 | Unsafe/debug audit ledger + `auditModule/auditPackage/auditArtifact` structured queries (MUST) | PARTIAL / IMPLEMENTED+TESTED in harness | Harness directive `assertAuditLedger` observes a machine-readable ledger for the implemented unsafe/debug escapes. | The source-level/package-level query surface (`auditModule`/`auditPackage`/`auditArtifact`) is still not claimed complete. |

## Appendix T — Standard test harness (CORE for this lane; `src/Kappa/TestHarness.hs`)

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §T.1 | If claiming standard-harness support, MUST accept the syntax and satisfy the behavior | IMPLEMENTED-WEAKLY-TESTED / partial SPEC-CONFLICT | TESTING.md claims Appendix-T support. Standard diagnostic/config directives are parsed and validated; remaining conflicts are narrower (for example numeric diagnostic-code validation and thin stage-dump capability). | The old structured-diagnostic/config downgrades are fixed; this row now tracks remaining harness-faithfulness gaps only. |
| §T.2 | Three test forms: single-file inline; directory suite (any dir with ≥1 `.kp`); incremental step suite | IMPLEMENTED-WEAKLY-TESTED | `--suite` form is correct (one dir = one suite root, `runTestSuitePath`). But the recursive walker `runTestPathAt False` treats a *nested* dir containing `.kp` files but no `suite.ktest`/`main.kp` as a **collection of independent single-file tests**, not one §T.2 directory suite (`src/Kappa/TestHarness.hs:1773-1793`, `isSuiteRoot` requires `suite.ktest`/`main.kp` or top-level). | Probe: `kappa test tests/conformance/staging` (dir of `.kp`, given non-top-level under a tree walk) does not compile them as one suite. Convenience-layer divergence; correct when pointed at a real suite. Minor. |
| §T.3 | `--!` directive lines; `--!!` inline markers (`.kp` only, after source text); `x-` extensions; **unknown standard directive / malformed / ill-typed arg = harnessError**; `x-` unsupported = unsupported (never silently ignored) | IMPLEMENTED+TESTED (one sub-gap) | `/tmp/ht/unknown.kp` `assertTotallyMadeUp` → HARNESS-ERROR. `/tmp/ht/mal.kp` `assertErrorCount notanumber` → HARNESS-ERROR. `--!!` with no preceding source → HARNESS-ERROR. Unknown `x-foo` → UNSUPPORTED. | Sub-gap: §T.5.1 "purely numeric codes are not valid" not enforced — see §T.5.1 row. |
| §T.4 | Config: `mode {analyze,check,compile,run}`, `packageMode`/`scriptMode`, `backend`, `entry`, `runArgs`, `stdinFile`, `dumpFormat`, `requires …`; capabilities `stageDumps/pipelineTrace/incremental/runTask` | IMPLEMENTED-WEAKLY-TESTED | `mode check`/`run`/`compile` accepted; `analyze` → unsupported; `backend interpreter` accepted, foreign backend → unsupported for compile/run; `requires …` gating works; capabilities `runTask`+`pipelineTrace` met, `stageDumps`+`incremental` → unsupported when required. `runArgs` is accepted for `mode run`; `stdinFile` is validated as a readable suite-relative file. | `mode compile` remains a weak pass when no concrete codegen assertion is made. |
| §T.4 | Capability `stageDumps` not provided | INTENTIONALLY-UNSUPPORTED (§T.4 makes unmet `requires capability` → unsupported; §34 stage dumps are profile-scoped — see §34 rows) | `requires capability stageDumps` → unsupported (`TestHarness.hs:303-305`). | Correct *when gated by `requires`*; the un-gated `assertStageDump` downgrade is the problem (see §T.5.3). |
| §T.5.1 | Diagnostic assertions: `assertNoErrors/NoWarnings/ErrorCount/WarningCount/Diagnostic/DiagnosticNext/At/Match/Family/ExplainExists`; `--!!` markers | IMPLEMENTED+TESTED | `/tmp/ht/ec.kp` assertErrorCount 1 → PASS; `/tmp/ht/ne.kp` assertNoErrors → PASS; `/tmp/ht/next.kp` assertDiagnosticNext → PASS; `/tmp/ht/match.kp` assertDiagnosticMatch (regex) → PASS; `/tmp/ht/fam.kp` assertDiagnosticFamily kappa.feature.gated → PASS; explain via `kappa explain` works. | Core diagnostic-code assertions faithful. |
| §T.5.1 | "Purely numeric codes are not valid standard-harness diagnostic codes" (so a numeric `<code>` is ill-typed → harnessError per §T.3) | SPEC-CONFLICT (minor) | `/tmp/ht/num.kp` `assertDiagnostic error 12345` → **FAIL** ("no diagnostic error[12345]"), not HARNESS-ERROR. The harness treats `12345` as a valid code. | Wrong classification; would falsely PASS if a diag with code "12345" ever existed. `parseDirective` does not validate code shape. |
| §T.5.1 | Structured diagnostic assertions: `assertDiagnosticPayload/Label/Related/Fix/FixCount/FixCompiles`, `assertSuppressedDiagnostic` (STANDARD directives) | IMPLEMENTED-WEAKLY-TESTED | The harness parses and checks these directives against the structured `Diagnostic` record (`dPayload`, `dRelated`, `dFixes`, `dSuppressed`) rather than rendered prose. Payload assertions are covered in-tree; related/fix/suppression assertions are supported by the harness but have thinner corpus coverage. | Stage dumps remain separately unsupported below. |
| §T.5.2 | `assertType`, `assertDeclKinds`, `assertFileDeclKinds` | IMPLEMENTED+TESTED | `/tmp/ht/type.kp` assertType n Int → PASS; `/tmp/ht/sig3.kp` `n : Int` + `let n = 5` → assertDeclKinds signature, let → PASS; `declKind` mapping faithful (`TestHarness.hs:1726`). | `assertType` uses definitional equality of the resolved type. |
| §T.5.3 | `assertStageDump <checkpoint> equals <path>` (Chapter-34 checkpoint, JSON/sexpr canonical compare) | IMPLEMENTED-WEAKLY-TESTED / profile-scoped | Ungated `assertStageDump` is parsed and classified as `harnessError` because this profile provides no named stage-dump checkpoint; `requires capability stageDumps` gates such tests to `unsupported`. | Dump content remains profile-scoped; the §T.8 classification is now fail-closed rather than an unconditional unsupported downgrade. |
| §T.5.4 | Run assertions `assertStdout/StdoutContains/StderrContains/StdoutFile/StderrFile/ExitCode` (mode run) | IMPLEMENTED+TESTED | `/tmp/ht/run2.kp` `mode run` + `let main = 42` + `assertStdout "42"` → FAIL (got `42\n`) which proves the comparison runs; `assertStdout "42\n"` variant passes; `assertExitCode` reads the run exit code. Run executes via in-process interpreter (`runMainCapturedValue`). | Functional. Golden-file forms `assertStdoutFile/StderrFile` present in dispatch. |
| §T.5.5 | Trace assertions `assertTraceCount <event> <subject> <relop> <n>` over the portable trace; exactly one count per `(event,subject)`; non-portable names rejected | IMPLEMENTED-WEAKLY-TESTED | `/tmp/ht/trace.kp` `assertTraceCount parse file >= 1` → PASS. Trace recorded in `cuTrace` (parse/buildKFrontIR per file, lowerKCore per module — `Pipeline.hs:125,282`). Non-portable event/subject → harnessError. | Only `parse`/`buildKFrontIR`/`lowerKCore` are genuinely produced; `mode compile` *synthesizes* a `lowerKBackendIR`/module step from each `lowerKCore`/module (`TestHarness.hs:718`) — a fabricated-but-documented analog, not a false pass. Portable subset is small; most events never occur. |
| §T.6 | Suite behavior; **same config key twice with different values ⇒ suite ill-formed** | SPEC-CONFLICT (minor) | Only `mode` conflict is checked (`TestHarness.hs:679`). `/tmp/ht/conf.kp` `dumpFormat json` + `dumpFormat sexpr` → **PASS** (should be ill-formed/harnessError). | Other config keys (dumpFormat, backend, scriptMode/packageMode) are not conflict-checked. |
| §T.7 | Incremental step suites (`step0..`, `incremental.ktest`, cross-step asserts) | INTENTIONALLY-UNSUPPORTED (§T.4 unmet `requires capability incremental`; §34 session reuse profile-scoped) | `runIncrementalDir` classifies the whole suite `unsupported` ("require capability 'incremental'"). `assertStep*` syntax validated then unsupported. | Defensible: §T.4 lists `incremental` as an optional capability and unmet `requires capability` → unsupported. |
| §T.8 | Result classification: pass/fail/unsupported/harnessError; `unsupported` ONLY for unmet `requires` or unsupported `x-` | IMPLEMENTED-WEAKLY-TESTED | `requires capability stageDumps`/`incremental` and unsupported `x-` directives classify as unsupported; malformed or unsupported ungated standard directives classify as harness errors. | Numeric diagnostic-code validation remains a smaller §T.5.1 classification gap. |
| §T.9 | Determinism (no dependence on worker count, hash-table order, line endings) | IMPLEMENTED-WEAKLY-TESTED | Single-threaded; diagnostics carried in deterministic order; LF normalization in run assertions (`assertStdout` normalizes). No randomness probed. | Plausibly deterministic; not independently stress-tested for ordering. |
| §T.10 | P0 diagnostic alias conformance suite (SHOULD) | IMPLEMENTED-WEAKLY-TESTED | Non-normative SHOULD; many P0 codes exist in `src/Kappa/Explain.hs`. | Out of strict scope (SHOULD). |

## §21–§23 Macros / Elab / Derivation-shape / Staged code (partially implemented)

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §21.1–21.2 | Quotation `'{ }`, splice `${ }`, top-level splice `$( )`, Elab monad | IMPLEMENTED-WEAKLY-TESTED | AST nodes `EQuote/ESpliceInQuote/DTopSplice` (`Syntax.hs:260-415`); `tests/conformance/macros/*` and `/tmp/macro_*.kp` macro-stress check clean (300/600/1200 splice sites, linear time). | Surface + interpreter macro expansion works for the tested forms; full §21 reflection-query surface not exhaustively verified. |
| §22 | Derivation-shape reflection | UNCLEAR | `tests/conformance/deriving/*` exist and pass; depth of §22 reflection API not independently disproven. | Needs the derivation lane; not disproved here. |
| §23.2 | Staged code `.<e>.` / `.~c` escape | IMPLEMENTED-WEAKLY-TESTED | AST `ECodeQuote/ECodeEscape` (`Syntax.hs:261-262`); `tests/conformance/staging/{borrow-escape,code-pipeline,escape-outside-quote}.kp` all PASS individually. | Tested for the conformance fixtures only. |

## §24–§26 Dynamics / Boundary / FFI / Bridges

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §24 | Dynamic values / runtime representations | INTENTIONALLY-UNSUPPORTED (interpretation is sanctioned per scope rule; §1.1 boundary honesty applies only if a foreign connection exists) | No `Dynamic`/`toDynamic`/`fromDynamic` in src (grep empty). | No spec clause *mandates* a dynamic-value surface for a pure interpreter with no host boundary; §24 governs runtime representations that only matter at a boundary (§25/§26), which this impl does not cross. |
| §25 | Boundary contracts / bridge packages | INTENTIONALLY-UNSUPPORTED (§25 is conditional on having a boundary; Appendix O frames graduality as roadmap) | Absent from src. | A frontend+interpreter with no foreign boundary has no §25 obligations to violate. |
| §26 | FFI / host bindings / native ABI / Kappa-to-Kappa bridges | INTENTIONALLY-UNSUPPORTED (§36.28 host bindings are build-system/profile-scoped) | Absent from src. | No FFI surface offered; nothing to gate. |

## §27 Backend profiles & runtime capability profiles

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §27.1–27.5A | Native/JVM/CLR/wasm/js/python backend profiles | INTENTIONALLY-UNSUPPORTED (§27.7: "A backend profile is conforming iff …" — backends are per-profile; an impl need not ship every profile) | No code generators in src; `backend <foreign>` → unsupported in harness. | §27.7 makes each backend independently conforming; interpretation is a sanctioned execution strategy (scope rule). |
| §27.6 | Runtime capability profiles (e.g. `rt-multishot-effects`) | INTENTIONALLY-UNSUPPORTED (§2.1 backend-capability gates; §27.6 capability profiles are backend-scoped) | Capability gates are part of backend profiles; interpreter exposes none. | |
| §27.7 | Backend conformance (per-profile) | N/A (scope) | The clause itself that makes backends profile-scoped. | Cited above. |

## §34 Compilation pipeline / IR dumps / checkpoints

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §34.1.3–34.1.7 | Compiler observability (stage dumps/checkpoints) — "ordinary required tooling facilities … not unsafe/debug" (§4.1) | MISSING-or-PROFILE (UNCLEAR) | No checkpoint serialization; `assertStageDump` → unsupported; no `dumpFormat`/checkpoint emission. The harness's stage-dump downgrade rests on this absence. | §4.1 calls §34.1.3-§34.1.7 "ordinary required tooling facilities," which argues *against* full optionality. But §37.3 tiers IDE/tooling profiles and the scope rule treats the compiler-pipeline dump machinery as profile-scoped. Best read: dump *content* is profile-scoped, but the §T.5.3 harness directive should then `harnessError` on an unknown checkpoint, not silently `unsupported`. Flagged in §T.5.3. |
| §34.1.6A | Conformance-verification mode | UNCLEAR / PROFILE | Not implemented; no `kappa` subcommand for it. | Profile-scoped per scope rule (compiler-pipeline machinery). |
| §34.2–34.5 | KFrontIR / KBackendIR / runtime obligations / intrinsics | PARTIAL | KFrontIR error-tolerance exists (pipeline); KBackendIR/target lowering absent (no backend). | Backend IR is profile-scoped (§27.7). |

## §35 Config mode

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §35.1–35.13 | Config units / profiles / evaluator / provenance / `.kcfg` / `kappa.build.kp` | INTENTIONALLY-UNSUPPORTED (§35 intro: config mode is selected "by role, file extension, command-line option, or embedding API" — a separate mode, not part of the ordinary compile pipeline) | No `.kcfg`/config-mode handling in CLI (only check/run/test/explain). | A frontend+interpreter that does not offer config-mode tooling is not running config units; §35 is a distinct evaluation profile. |

## §36 Build system

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §36.* | Manifest, build plan, lockfile, targets, providers, publish, etc. | INTENTIONALLY-UNSUPPORTED (build system is a separate tool layer; §36.28 host bindings, §36.30 bridges are profile-scoped; CLI is a single-file checker/runner) | No build-manifest parsing, no `kappa.build.kp` handling. | The language implementation (check/run/test) does not require the package build system; this is the build-tool profile. |

## §37 IDE / LSP / interactive semantic services

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §37.3.1 | Tooling Core profile (analysis session, structured diagnostics, LSP, semantic protocol, …) — "minimum acceptable profile for a serious Kappa implementation" | INTENTIONALLY-UNSUPPORTED for the *LSP/session surface* (§37.3 explicitly divides IDE support into conformance profiles; the scope rule tiers §37 IDE profiles) | No LSP server, no session model, no semantic queries in src. | BUT §37.3.1 lists "machine-readable structured diagnostics" as part of even the minimum profile — reinforcing that the no-JSON gap (anchored at §3.1.1, which is CORE) is real. The LSP/session machinery itself is profile-scoped. |
| §37.3.2–37.3.4 | First-Class / Broad-Compat / Syntax-Only client profiles | INTENTIONALLY-UNSUPPORTED (§37.3 profile tiers) | Not provided. | Profile-scoped. |

---

## Hostile overfitting sweep (findings)

Method: `grep -rn` over `src/` for fixture-name / path string matching, identifier
equality special-cases, and diagnostic "tolerances."

- **No fixture-name / path string matching found.** No references to `Fixtures`, the
  external corpus path, or fixture directory names in code paths (only in comments).
  The external driver lives in `tools/run-external-fixtures.sh` and uses the corpus
  purely as black-box inputs.
- **`assertDiagnosticCodes` alias matching (`TestHarness.hs` + `Explain.hs:requiredAliasTable`)**:
  matches only through §3.1.4 *required* portable aliases, in both directions; non-aliased
  codes are compared verbatim. This is a bounded, spec-anchored equivalence, NOT a free
  "tolerance" — verified by reading `requiredAliasTable`. Acceptable.
- **`assertEval` loose-list rendering (`TestHarness.hs:1107-1124, 1189-1194`)**: `assertEval`
  accepts EITHER the canonical rendering OR a corpus-compatible "loose cons" rendering
  (`Some 1 :: Nil` for `Some (1 :: Nil)`). This is a *tolerance*, but `assertEval` is a
  documented **nonstandard** compatibility directive (§T.1 permits nonstandard directives),
  not a standard-harness assertion — so it does not relax any spec-mandated check. Flag: it
  could mask a real precedence/printing bug in `assertEval`-based corpus tests. Low risk.
- **Type-checker "compatibility accommodations for the external corpus" (`Check.hs:2637, 2677`)**:
  (1) `IO a` is silently elaborated to `IO ?e a` by inserting a fresh metavariable when the
  head is the prelude `IO` and only one explicit arg is supplied; (2) `Array n elem` is
  accepted over the prelude `Array : Type -> Type` carrier via a phantom `__sizedOf` element.
  These are semantic special-cases motivated by passing another implementation's corpus.
  They are keyed to prelude globals (not fixture names) and are documented, but they are
  corpus-driven leniencies in the *type checker*, which is more concerning than harness-level
  tolerances. NOT in this lane's MUST set, but flagged for the type-system lane.
- **`divInt`/`modInt` zero-divisor and `intToNat` negative special-cases (`TestHarness.hs:1159-1166`)**:
  these are inside `assertEvalErrorContains` runtime-error *detection*, recognizing known
  prelude primitive failure shapes. Reasonable, bounded.

No code path was found that string-matches a fixture *name* to force pass/fail, and no
unimplemented assertion silently *passes* — the consistent failure mode is `unsupported`
(over-broad, but non-deceptive).

## Bounded perf check

Decl-scaling (`tools/gen-stress.sh`, `kappa check`, `/usr/bin/time -v`):

| decls | wall | maxRSS |
|---|---|---|
| 2000 | 0.21s | 33 MB |
| 4000 | 0.38s | 48 MB |
| 8000 | 0.73s | 77 MB |

Comprehension-pipeline stress (`tools/gen-comp-stress.sh`):

| comprehensions | wall | maxRSS |
|---|---|---|
| 200 | 0.41s | 38 MB |
| 400 | 0.72s | 74 MB |
| 800 | 1.38s | 82 MB |

Macro-expansion stress (`tools/gen-macro-stress.sh`):

| splice sites | wall | maxRSS |
|---|---|---|
| 300 | 0.28s | 35 MB |
| 600 | 0.30s | 41 MB |
| 1200 | 0.43s | 42 MB |

All three workloads scale **linearly** in time and memory; no superlinear blowup and
nothing approaching 1 GB. No perf gap.

The tables above are *valid-input* workloads (the success path). The
`E_NAME_UNRESOLVED` typo-suggestion **diagnostic** path — exercised when a
dropped/renamed import leaves many references unresolved at once — was a
separate quadratic the success-path scaling did not cover: the in-scope
candidate set was rebuilt and rescanned per diagnostic, O(N_errors ×
N_scope) (~2.6 / 7.3 / 18.8 s for 1,000 / 2,000 / 4,000 distinct
unresolved names). It is now linear (~2.08 / 4.02 / 8.14 s, ~2.0× per
doubling) via a once-built, incrementally-extended length-bucketed
candidate index in `Check.hs` (`csScopeNameCache`); each diagnostic
consults only the length-compatible buckets. See docs/notes/PERFORMANCE.md §2b and
the `tests/conformance/diagnostics/unresolved-typo-*` fixtures.

---

## Legitimate gaps (ranked)

In-scope, spec-grounded, MUST/SHALL-level unsatisfied requirements, each disproved by a probe.
Profile-scoped items are excluded (see next section).

### 1. Incomplete machine-readable diagnostic coverage — §3.1.1 (MAJOR)

- **§**: §3.1.1 (lines 493–496: "A conforming implementation MUST support both: 1. a
  human-readable diagnostic renderer; and 2. machine-readable diagnostic output in JSON.";
  line 529: "the JSON output MUST expose fields observationally equivalent to" the record
  incl. `labels/fixes/related/payload/suppressed`).
- **Probe**: `kappa check --json` renders structured diagnostic records, and
  `Diagnostic` includes payload, related, fixes, and suppressed fields. Harness
  payload/related/fix/suppression assertions read the structured record rather than prose.
- **Expected vs actual**: the JSON surface exists. Remaining gaps are incomplete
  producer coverage for some family-specific payloads/related origins and weak
  labels/provenance representation.
- **Severity**: MAJOR. This no longer blocks S2.3b mutable-variable payload work, but it
  remains a broader §3 audit item.
- **Fix locus**: continue producer-by-producer payload/related/provenance completion in
  `src/Kappa/Check.hs`, `src/Kappa/Resolve.hs`, and `src/Kappa/Usage.hs`.

### 2. Remaining Appendix-T harness classification gaps — §T.8 / §T.5.1 (MINOR)

- **§**: §T.8 ("`unsupported` means one or more `requires …` preconditions were not
  satisfied, or the test used one or more **extension directives** unsupported by this
  harness") read against §T.5.1 diagnostic-code validation.
- **Probe**: `runArgs`/`stdinFile` are standard config and are validated; ungated
  `assertStageDump` is a harness error, while `requires capability stageDumps` gates to
  unsupported. The remaining known classification gap is numeric diagnostic codes:
  `assertDiagnostic error 12345` fails as an ordinary unmet assertion rather than a
  harness error for an ill-typed code.
- **Severity**: MINOR. This can misclassify a malformed harness directive as a test
  failure, but it does not create false passes.
- **Fix locus**: `src/Kappa/TestHarness.hs` diagnostic-code parser.

### 3. §4 unsafe/debug facilities: assertion/proof escapes implemented; import/query surface still partial (MAJOR)

- **§**: §4.1 (these forms "remain part of the language specification"), §4.2 ("Violations
  are compile-time errors. Diagnostics … MUST identify both the offending … form and the
  build setting … that disallows it").
- **Probe**: current conformance fixtures under `tests/conformance/unsafe_debug/` show
  `assertTerminates`, `assertReducible`, legacy `assertTotal`, and `unsafeAssertProof`
  are recognized, gated by the matching `allow_*` settings, and recorded in the harness
  audit ledger. Gated-negative fixtures reject the escapes when the setting is absent.
- **Expected vs actual**: the stale generic parse/resolve-error finding is fixed for the
  assertion/proof escapes. Remaining partial areas are `unhide`/`clarify` import semantics
  and package/artifact audit-query surfaces beyond the harness ledger.
- **Severity**: MAJOR for the remaining import/query gaps; the old "entirely unrecognized"
  characterization is obsolete.
- **Fix locus**: import-surface semantics/gates for `unhide`/`clarify`, and structured
  package/artifact audit queries. Keep the existing assertion/proof fixtures as regressions.

### 4. §T.5.1 numeric diagnostic codes not rejected (MINOR)

- **§**: §T.5.1 ("Purely numeric codes are not valid standard-harness diagnostic codes") +
  §T.3 (ill-typed directive argument = harnessError).
- **Probe**: `/tmp/ht/num.kp` `assertDiagnostic error 12345` → **FAIL**, not HARNESS-ERROR.
- **Expected vs actual**: should be `harnessError` (ill-typed code argument); actual = treated
  as a valid code and evaluated, would false-PASS if such a code existed.
- **Severity**: MINOR. **Fix locus**: validate `<code>` shape in `parseDirective`
  (`src/Kappa/TestHarness.hs`, `withSevCode`/`ADiag*` construction).

### 5. §T.6 duplicate-config-key conflict only detected for `mode` (MINOR)

- **§**: §T.6 ("If the same configuration key is specified more than once with different
  values, the suite is ill-formed").
- **Probe**: `/tmp/ht/conf.kp` `dumpFormat json` + `dumpFormat sexpr` → **PASS** (should be
  ill-formed / harnessError).
- **Expected vs actual**: ill-formed suite; actual = PASS. Only `mode` is conflict-checked
  (`TestHarness.hs:679`).
- **Severity**: MINOR. **Fix locus**: generalize the dedup check in `runSuiteWith`
  (`src/Kappa/TestHarness.hs:679`) to all config keys (dumpFormat/backend/scriptMode).

### 6. §T.2 nested directory not treated as one directory suite (MINOR)

- **§**: §T.2 ("Directory suite: A directory containing one or more `.kp` source files …").
- **Probe**: under the recursive walk (`runTestPathAt False`), a nested dir of `.kp` files
  without `suite.ktest`/`main.kp` is run as independent single-file tests, not compiled
  together as one suite root (`src/Kappa/TestHarness.hs:1773-1793`, `isSuiteRoot`).
- **Expected vs actual**: spec = one directory suite; actual = a collection of single-file
  tests. Correct when invoked with `--suite` or when a `suite.ktest`/`main.kp` is present.
- **Severity**: MINOR (driver convenience-layer divergence; suite semantics themselves are
  correct). **Fix locus**: `isSuiteRoot`/`runTestPathAt` directory-walk policy.

---

## Profile-scoped / intentionally-unsupported (cited)

- **§4.6 backend-specific surface escapes** — conditional ("If an implementation provides
  such a facility"); none provided ⇒ conforming.
- **§24 / §25 / §26 dynamics, boundary contracts, FFI, bridges** — governed by foreign
  boundaries the pure interpreter does not cross; §1.1 boundary honesty applies only when a
  foreign connection exists; §36.28/§36.30 host-binding/bridge surfaces are build-system
  profile-scoped. Appendix O frames graduality as roadmap.
- **§27.1–27.6 backend & runtime-capability profiles** — §27.7 makes each backend profile
  independently conforming; interpretation is a sanctioned execution strategy. No code
  generator required for a conforming language implementation.
- **§34.1.6A conformance-verification mode; §34.3 KBackendIR / target lowering** —
  compiler-pipeline / backend machinery; backend IR profile-scoped under §27.7.
  (Caveat: §34.1.3-§34.1.7 stage-dump *observability* is called "ordinary required tooling"
  by §4.1 — see gap #2's §T.5.3 facet; the dump *content* is profile-scoped but the harness
  directive handling is not.)
- **§35 config mode** — separate evaluation mode selected by role/extension/flag/API
  (§35 intro); not part of the ordinary check/run pipeline.
- **§36 build system** — separate package/build tool layer; the language implementation
  (check/run/test) does not require it; host bindings/bridges/publish are profile-scoped.
- **§37 IDE/LSP profiles** — §37.3 explicitly divides IDE support into conformance profiles
  (Tooling Core / First-Class / Broad-Compat / Syntax-Only); shipping no LSP server is
  profile-scoped. (Caveat: §37.3.1's "machine-readable structured diagnostics" reinforces
  gap #1, which is anchored at the CORE §3.1.1, not at §37.)
- **Appendix-T §T.7 incremental step suites + `stageDumps` capability** — §T.4 lists
  `incremental`/`stageDumps` as optional capabilities; unmet `requires capability` → §T.8
  `unsupported`. Defensible *when gated by `requires`* (the un-gated downgrade is gap #2).
