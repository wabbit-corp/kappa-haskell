# Testing

## How to run

```
cabal build                                   # zero warnings under -Wall
cabal run -v0 kappa -- test tests/conformance # in-tree suite (80/80)
cabal run -v0 kappa -- test examples          # golden-output example
cabal run -v0 kappa -- test path/to/file.kp   # one fixture
tools/run-external-fixtures.sh                # external corpus (see below)
```

Exit code is non-zero if any test fails or the harness errors;
`unsupported` never fails a run (§T.8).

## Harness model (Appendix T subset)

Implemented in `src/Kappa/TestHarness.hs`, exposed as `kappa test PATH`.

* **Single-file inline tests (§T.2):** a `.kp` file whose `--!`
  directive lines configure mode and assertions. Programs run
  in-process with stdout captured.
* **Directory suites (§T.2):** a directory containing `suite.ktest`
  and/or `main.kp` — or a directory passed directly as the argument
  that contains `.kp` files — is one suite. All its `.kp` files are
  compiled together in import order; directives are gathered from
  `suite.ktest` plus every file.
* **Tree walking:** any other directory argument recurses over
  `**/*.kp`, treating qualifying subdirectories as suites.
* **Inline markers:** `--!! CODE` at the end of a source line asserts a
  diagnostic with that code on that line (§T.5.1).

### Directive subset

Implemented:

| Directive | Notes |
| --- | --- |
| `mode check` / `mode run` | `analyze`/`compile` classify unsupported |
| `entry NAME` | alternate entry point |
| `packageMode`, `dumpFormat json\|sexpr`, `requires mode package` | accepted no-ops (defaults) |
| `requires backend/capability …` | classify unsupported |
| `assertNoErrors`, `assertNoWarnings` | |
| `assertErrorCount N`, `assertWarningCount N` | |
| `assertDiagnostic SEV CODE` | portable alias matching (§3.1.4) |
| `assertDiagnosticNext` (+ deprecated `assertDiagnosticHere`) | |
| `assertDiagnosticFamily SEV FAMILY` | |
| `assertDiagnosticAt FILE SEV CODE LINE [COL]` | point form only; range form unsupported |
| `assertType NAME TYPE` | |
| `assertDeclKinds k1, k2, …` | declaration-shape check |
| `assertStdout "…"`, `assertStdoutContains "…"` | exact golden / substring |
| `assertStderrContains "…"`, `assertExitCode N` | |
| `assertDiagnosticCodes c1, c2, …`, `assertEval NAME EXPR` | compatibility extensions for the external corpus |

Classified **unsupported** (recognized, not implemented):
`assertDiagnosticMatch`, `assertDiagnosticPayload/Label/Related/Fix*`,
`assertDiagnosticExplainExists`, `assertSuppressedDiagnostic`,
`assertStdoutFile`, `assertStderrFile`, `assertStageDump`,
`assertTraceCount`, `assertFileDeclKinds`, all `x-*` extensions,
`scriptMode`, `backend`, `runArgs`, `stdinFile`, and the non-standard
directives used by the external corpus (`assertRunStdout`,
`assertExecute`, `allow_unsafe_consume`, …). Unknown *standard*-looking
directives are harness errors.

## In-tree conformance suite

`tests/conformance/` — **80/80 passing**, zero unsupported, zero
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

`tools/run-external-fixtures.sh` runs `kappa test` over the external
fixture corpus at `/opt/workspaces/kappa/tests/Kappa.Compiler.Tests/Fixtures`
(a different implementation's suite, used strictly as black-box
fixtures, in place) and writes `tests/external-results.md`.

Current tally over **925 fixture suites**:

| outcome | count |
| --- | --- |
| pass | 163 |
| fail | 509 |
| unsupported | 219 |
| harness error | 34 |

(Two `traits.members.*` fixtures that passed in earlier tallies did so
only through a since-fixed unification bug that let ill-typed terms
through; they now fail honestly — one needs `Functor Option`-style
`map`, the other pins foreign diagnostic-code names.)

The unsupported and failure buckets are broken down in
`tests/external-results.md`: unsupported is dominated by non-portable
directives, capabilities, and backend modes; failures are dominated by
unimplemented subsystems (flow typing, rows/dependent records,
staging/derive, std modules beyond the prelude, sealing, statics) and
by the corpus asserting its own implementation-defined diagnostic code
names where the spec does not pin a portable alias (e.g.
`E_NAME_UNRESOLVED` vs this implementation's `E_UNRESOLVED_NAME`).

## Conventions

* New fixtures: one feature per file, `--!` directives at the top,
  `--!!` markers next to the offending line for diagnostics.
* Run-mode fixtures should assert exact stdout where the output is
  stable, and `assertExitCode 0`.
* Keep `cabal build` warning-free; the suite is the gate for every
  commit.
