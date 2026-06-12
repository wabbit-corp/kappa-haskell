# Testing

## How to run

```
cabal build                                       # zero warnings under -Wall
cabal run -v0 kappa -- test tests/conformance     # in-tree suite (84/84)
cabal run -v0 kappa -- test examples              # golden-output example
cabal run -v0 kappa -- test path/to/file.kp       # one fixture
cabal run -v0 kappa -- test --suite path/to/dir   # one §T.2 directory suite
cabal run -v0 kappa -- explain E_TYPE_MISMATCH    # §3.1.2A code registry
tools/run-external-fixtures.sh                    # external corpus (see below)
tools/triage-external.sh                          # per-category triage db
```

Exit code is non-zero if any test fails or the harness errors;
`unsupported` never fails a run (§T.8).

## Harness model (Appendix T subset)

Implemented in `src/Kappa/TestHarness.hs`, exposed as `kappa test PATH`.

* **Single-file inline tests (§T.2):** a `.kp` file whose `--!`
  directive lines configure mode and assertions. Programs run
  in-process with stdout captured. The containing directory is the
  suite root for relative paths.
* **Directory suites (§T.2):** a directory containing `suite.ktest`
  and/or `main.kp` — or a directory passed directly as the argument
  that contains `.kp` files — is one suite. With `--suite`, the
  argument directory is unconditionally one suite root even when all
  its `.kp` files live in subdirectories. All `.kp` files are compiled
  together in import order; directives are gathered from `suite.ktest`
  plus every file; the suite root is the §8.1 source root, so
  header-less `demo/value.kp` gets module name `demo.value`.
* **Incremental step suites (§T.7):** recognized (a directory with
  `step0`/`incremental.ktest`) and reported as one result. They are
  classified unsupported: this implementation keeps no Chapter 34
  session state between suite roots, so the `incremental` capability is
  not claimed. `assertStep*` directive syntax is validated.
* **Tree walking:** any other directory argument recurses over
  `**/*.kp`, treating qualifying subdirectories as suites.
* **Inline markers:** `--!! CODE` at the end of a source line asserts a
  diagnostic with that code on that line (§T.5.1).
* **Capabilities (§T.4):** `runTask` (programs execute in-process on
  the tree-walking interpreter) and `pipelineTrace` (see
  `assertTraceCount`) are provided; `backend interpreter` is the one
  provided profile. `stageDumps` and `incremental` are not claimed.

### Directive subset

Implemented:

| Directive | Notes |
| --- | --- |
| `mode check` / `mode run` | `analyze`/`compile` classify unsupported |
| `entry NAME` | alternate entry point |
| `packageMode`, `dumpFormat json\|sexpr`, `requires mode package` | accepted no-ops (defaults) |
| `backend interpreter`, `requires backend interpreter` | accepted (the in-process interpreter) |
| `requires capability runTask\|pipelineTrace` | met; other capabilities classify unsupported |
| `assertNoErrors`, `assertNoWarnings` | |
| `assertErrorCount N`, `assertWarningCount N` | |
| `assertDiagnostic SEV CODE` | portable alias matching (§3.1.4) |
| `assertDiagnosticNext` (+ deprecated `assertDiagnosticHere`) | |
| `assertDiagnosticFamily SEV FAMILY` | |
| `assertDiagnosticAt FILE SEV CODE LINE [COL]` and the `SL SC - EL EC` range form | range end is this implementation's exclusive end position |
| `assertDiagnosticMatch REGEX` | ECMAScript-style subset engine in `src/Kappa/Regex.hs` (literals, `.`, classes, groups, alternation, `* + ? {m,n}`, anchors, `\b \d \w \s`); matches the primary message text |
| `assertDiagnosticExplainExists CODE-OR-FAMILY` | backed by the §3.1.2A registry in `src/Kappa/Explain.hs` (also `kappa explain CODE`) |
| `assertType NAME TYPE` | expected type is elaborated in the origin file's module/import scope; a non-parsing or non-elaborating expected type **fails** the test (the directive is well-formed, so it is not a harness error) |
| `assertDeclKinds k1, k2, …` | declaration-shape check |
| `assertFileDeclKinds PATH k1, k2, …` | suite-root-relative file form |
| `assertStdout "…"`, `assertStdoutContains "…"` | exact golden / substring |
| `assertStderrContains "…"`, `assertExitCode N` | |
| `assertStdoutFile PATH`, `assertStderrFile PATH` | golden files, LF-normalized; unreadable golden file is a harness error (§T.8) |
| `assertTraceCount EVENT SUBJECT RELOP N` | portable trace counts; this pipeline records `parse`/file, `buildKFrontIR`/file, `lowerKCore`/module per compiled file (the prelude bootstrap contributes none); all other portable event/subject pairs count 0 |
| `assertDiagnosticCodes c1, c2, …`, `assertEval NAME EXPR` | compatibility extensions for the external corpus (§T.1 allows nonstandard directives) |

A `mode run` entry whose final value is not `Unit` is rendered to
stdout followed by a newline (matching the reference run task, e.g.
`let main = 42` prints `42`).

Classified **unsupported**: `assertDiagnosticPayload/Label/Related/Fix*`
and `assertSuppressedDiagnostic` (§T.5.1) and `assertStageDump` (§T.5.3)
— this implementation's diagnostic records carry no payloads, labels,
related origins, fix-its, or suppression summaries, and there is no
Chapter 34 stage-dump serialization, so the asserted data does not
exist; all unsupported `x-*` extensions (§T.3 mandates unsupported);
`scriptMode`, `mode analyze|compile`, non-`interpreter` backends,
`runArgs`, `stdinFile`; `requires` of unprovided capabilities (§T.4
mandates unsupported).

**Harness errors** (§T.3: "any unknown standard directive, malformed
directive, or ill-typed directive argument"): malformed directives and
all unknown non-`x-` directives — including the external corpus's
private `allow_unsafe_consume`, `assertRunStdout`, `assertExecute`,
`assertEvalErrorContains`, `assertParameterQuantities`,
`assertDoItemDescriptors`, `assertInoutParameters`, and
`assertContainsTokenTexts`, none of which appear anywhere in Spec.md
(checked against the §T.4/§T.5 directive lists).

## In-tree conformance suite

`tests/conformance/` — **84/84 passing**, zero unsupported, zero
harness errors. Layout by area:

| Directory | Covers |
| --- | --- |
| `lexer/` | bad escape, tabs in indent/source, unterminated string, §5.2 soft keywords as ordinary identifiers (argument/binder/assignment positions) |
| `parser/` | `E_LAYOUT_BAD_DEDENT`, multi-error parse recovery |
| `literals/` | radix forms, exponent-vs-suffix, suffix terms, defaulting, `FromFloat` literal elaboration |
| `names/` | `E_UNRESOLVED_NAME`, `E_DUPLICATE_DECLARATION` |
| `types/` | `E_TYPE_MISMATCH`, `E_NOT_A_TYPE` |
| `application/` | `E_APPLICATION_NON_CALLABLE`, ctor arity, multi-arg lambdas vs polymorphic HOFs |
| `match/` | exhaustiveness (Bool/or/guards/nested/literal/tuple/record) |
| `records/` | projection, patch, punning, unknown-field errors, constructor field defaults (§10.1.1) |
| `variants/` | closed unions, injection, missing member, `Int?` sugar |
| `traits/` | user traits, premise instance, defaults, `E_IMPLICIT_UNSOLVED`, `E_INSTANCE_INCOHERENT`, §28.2 base instances, supertrait premise enforcement (`E_SUPERTRAIT_UNSATISFIED`) |
| `equality/` | refl conversion, `subDefined` proof, symbolic failure |
| `recursion/` | no-signature error, structural (clean), unverified warning |
| `fixity/` | user fixity, `E_OPERATOR_NO_FIXITY`, parenthesized prefix negation (§5.5.1.1) |
| `run/` | hello, while/var, for+break/continue+else, defer LIFO, try/except/finally, `let?`-else, early return, interpolation, statement-if |
| `labels/` | §18.2.5 labeled loops: plain `break` confined to its labeled loop, `break@outer`/`continue@outer` across an inner loop, `E_LABEL_UNRESOLVED` for missing/non-loop targets, inert `label@match` |
| `do/` | implicit do-bindings `let (@x : T) = e` joining the local implicit context (§16.3.3) |
| `shape/` | `assertDeclKinds` |
| `unsupported/` | handle/seal/exists/`{}` map literal/`return@label`/`defer@label` → `E_UNSUPPORTED` |

`examples/` is also a harness suite: `examples/todo.kp` carries an
exact `assertStdout` golden transcript (see `examples/README.md`).

## External black-box corpus

`tools/run-external-fixtures.sh` runs `kappa test --suite` over each
fixture directory of the external corpus at
`/opt/workspaces/kappa/tests/Kappa.Compiler.Tests/Fixtures`
(a different implementation's suite, used strictly as black-box
fixtures, in place), writes `tests/external-results.md`, and leaves a
raw per-fixture log at `/tmp/external-raw.log`.
`tools/triage-external.sh` turns that log into a triage database:
`/tmp/triage.csv` (fixture, category prefix, outcome, first error code,
first error message) and `/tmp/triage-summary.txt` (per-category
outcome counts and top error codes).

Current tally over **922 fixture suites** (one result per fixture):

| outcome | count |
| --- | --- |
| pass | 178 |
| fail | 629 |
| unsupported | 74 |
| harness error | 41 |

All 41 harness errors are fixtures using the other implementation's
private, non-`x-` directives that Appendix T does not define
(`allow_unsafe_consume`, `assertRunStdout`, `assertExecute`,
`assertEvalErrorContains`, `assertParameterQuantities`,
`assertDoItemDescriptors`, `assertInoutParameters`,
`assertContainsTokenTexts`); per §T.3 an unknown non-extension
directive *is* a harness error. The unsupported and failure buckets,
and the §T.8 classification rationale with spec citations, are broken
down in `tests/external-results.md`: unsupported is now only unmet
capabilities/backends/modes, unsupported `x-*` extensions,
structured-diagnostic assertions, and incremental suites; failures are
dominated by unimplemented subsystems (flow typing, rows/dependent
records, staging/derive, std modules beyond the prelude, sealing,
statics, QTT borrow checking) and by the corpus asserting its own
implementation-defined diagnostic code names where the spec does not
pin a portable alias (e.g. `E_NAME_UNRESOLVED` vs this implementation's
`E_UNRESOLVED_NAME`).

## Conventions

* New fixtures: one feature per file, `--!` directives at the top,
  `--!!` markers next to the offending line for diagnostics.
* Run-mode fixtures should assert exact stdout where the output is
  stable, and `assertExitCode 0`.
* Keep `cabal build` warning-free; the suite is the gate for every
  commit.
