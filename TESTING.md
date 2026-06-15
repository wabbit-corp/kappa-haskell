# Testing

## How to run

```
cabal build                                       # zero warnings under -Wall
cabal run -v0 kappa -- test tests/conformance     # in-tree suite (186/186)
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
| `mode check` / `mode run` / `mode compile` | `compile` runs the full pipeline without executing an entry, recording the per-module Term→Value lowering as the `lowerKBackendIR`/`module` portable trace step (§T.5.5); `analyze` classifies unsupported |
| `entry NAME` | alternate entry point |
| `scriptMode` | compiles the suite without §8.1 path-derived module names (§T.4; module headers stand alone); `requires mode script` still classifies unsupported |
| `packageMode`, `dumpFormat json\|sexpr`, `requires mode package` | accepted no-ops (defaults); in package mode a module header that disagrees with the §8.1 path-derived name is `E_MODULE_PATH_MISMATCH` |
| `backend interpreter`, `requires backend interpreter` | accepted (the in-process interpreter); a foreign `backend <profile>` selection classifies `compile`/`run` tests unsupported but leaves default-mode `check` tests unaffected (§T.4: it "selects the backend profile for compile and run tests") |
| `requires capability runTask\|pipelineTrace` | met; other capabilities classify unsupported |
| `requires capability legacyCharAlias\|unicodeSourceWarnings` | met (documented §T.1 compatibility extensions: the §28.2 `Char` compatibility alias; the §3.1.3 source-hygiene warnings) |
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
| `assertTraceCount EVENT SUBJECT RELOP N` | portable trace counts; this pipeline records `parse`/file, `buildKFrontIR`/file, `lowerKCore`/module per compiled file, plus `lowerKBackendIR`/module under `mode compile` (the prelude bootstrap contributes none); all other portable event/subject pairs count 0 |
| `assertDiagnosticCodes c1, c2, …`, `assertEval NAME EXPR` | compatibility extensions for the external corpus (§T.1 allows nonstandard directives). `assertDiagnosticCodes` matches codes through §3.1.4 portable aliases in **both** directions and through nothing else: an asserted spelling that is another implementation's nonportable code matches iff both spellings resolve to the same *required* portable alias (`requiredAliasTable` in `src/Kappa/Explain.hs`). There are no implementation-defined spelling "tolerances": a code §3.1.4 does not standardize is compared verbatim, so emitting a materially different code than a fixture pins (e.g. `kappa.implicit.unsolved`/`E_UNSOLVED_IMPLICIT`, §3.2.4, where the fixture pins `E_TYPE_MISMATCH`) is reported as a mismatch, never silently reconciled (§3.1.4 forbids reusing a portable alias for a materially different meaning). `assertEval` compares this harness's canonical value rendering, and additionally accepts the corpus formatter's loose list rendering (cons chains unparenthesized in constructor-argument position, e.g. `Some 1 :: Nil` for `Some (1 :: Nil)`). |
| `x-assertEval`, `x-assertEvalErrorContains`, `x-assertDeclDescriptors`, `x-assertTraitMembers` | supported `x-` extensions (§T.3/§T.1); `assertEval` subjects resolve in the directive file's own module (§T.6); `x-assertDeclDescriptors` renders fixity declarations by class only (`fixity infix ++`, no associativity word — the corpus descriptor format); unsupported `x-` directives still classify the test unsupported per §T.3 |
| `x-assertContainsTokenKinds k1, k2, …` | supported `x-` extension: portable token-kind names mapped onto this lexer (interpolation segment kinds map to fragment structure) |
| `x-assertModule NAME`, `x-assertModuleAttributes a1, …`, `x-assertDataConstructors TYPE c1, …` | supported `x-` extensions: the directive file's module-header name, its module attributes, and a data type's constructor names in declaration order |
| `allow_unsafe_consume` | compatibility config (no-op): the corpus gates its `unsafeConsume` linear sink behind it; this prelude always provides `unsafeConsume : (@0 a : Type) -> (1 x : a) -> Unit` (plus `printInt` and `integerToInt : Nat -> Int`, the corpus's literal-payload conversion — §6.1.5 makes the payload a `Nat`) as documented extras beyond the §28.2 minimum |
| `assertParameterQuantities NAME q1 q2 …` | compatibility extension: the named let's explicit parameters carry exactly these §12.1.1 binder prefixes (`0`/`1`/`ω`/`<=1`/`>=1`/`&`/`&[r]`; bare default renders `ω`, an `inout` parameter renders `1` per §18.9.3) |
| `assertExecute NAME EXPECTED`, `assertRunStdout NAME EXPECTED` | compatibility extensions: run the named IO global regardless of `mode` (compile errors fail the assertion) and compare the final value rendering / the trimmed captured stdout |
| `assertInoutParameters NAME p1 [p2 …]` | compatibility extension: the named let's `inout`-marked explicit parameter names, in order |
| `assertDoItemDescriptors NAME d1, d2, …` | compatibility extension: shape descriptors of the named let's do-block items (`let [prefix] x`, `let? x`, `using x`, `var x`, `assign x`, `expression`, `defer`, `return`, …) |
| `assertContainsTokenTexts t1, t2, …` | compatibility extension: each text occurs as the source text of some lexed token of the directive's file |

A `mode run` entry whose final value is not `Unit` is rendered to
stdout followed by a newline (matching the reference run task, e.g.
`let main = 42` prints `42`).

Classified **unsupported**: `assertDiagnosticPayload/Label/Related/Fix*`
and `assertSuppressedDiagnostic` (§T.5.1) and `assertStageDump` (§T.5.3)
— this implementation's diagnostic records carry no payloads, labels,
related origins, fix-its, or suppression summaries, and there is no
Chapter 34 stage-dump serialization, so the asserted data does not
exist; all unsupported `x-*` extensions (§T.3 mandates unsupported);
`mode analyze`, non-`interpreter` backends, `runArgs`, `stdinFile`,
`requires mode script`; `requires` of unprovided capabilities (§T.4
mandates unsupported).

**Harness errors** (§T.3: "any unknown standard directive, malformed
directive, or ill-typed directive argument"): malformed directives and
all unknown non-`x-` directives. The external corpus's private
directives do not appear anywhere in Spec.md (checked against the
§T.4/§T.5 directive lists); those with an evident portable meaning are
implemented as the documented compatibility extensions above (§T.1
permits nonstandard directives), and the rest remain harness errors.

## In-tree conformance suite

`tests/conformance/` — **186/186 passing**, zero unsupported, zero
harness errors. Layout by area:

| Directory | Covers |
| --- | --- |
| `lexer/` | bad escape, tabs in indent/source, unterminated string, multi-error recovery, §5.2 soft keywords as ordinary identifiers (argument/binder/assignment positions) |
| `lexical/` | multiline-string trailing newline (§6.3.3 closing-delimiter content line) |
| `parser/` | `E_LAYOUT_BAD_DEDENT`, multi-error parse recovery, misindented declarations (§5.4) |
| `data/` | constructor field defaults at `data` declarations (§10.1.1) |
| `prelude/` | container trait stack: `map`/`filter`/`foldr`/`traverse`/`(>>=)`/`(++)` over `List`/`Option`/`String` (§28.2) |
| `refinement/` | §16.4 flow refinement: `is`-tests through `&&`/`\|\|`, stable-alias transport, refined field projection; `?.` diagnostic codes |
| `literals/` | radix forms, exponent-vs-suffix, suffix terms, defaulting, `FromFloat` literal elaboration |
| `names/` | `E_UNRESOLVED_NAME`, `E_DUPLICATE_DECLARATION` |
| `types/` | `E_TYPE_MISMATCH`, `E_NOT_A_TYPE` |
| `application/` | `E_APPLICATION_NON_CALLABLE`, ctor arity, multi-arg lambdas vs polymorphic HOFs |
| `match/` | exhaustiveness (Bool/or/guards/nested/literal/tuple/record) |
| `patterns/` | §17.3 active patterns: Option/`Match`/total-view results, residue threading, `let?` over patterns, monadic/linearity rejections |
| `implicits/` | §16.3.3 local implicit candidates: quantity/borrow-aware resolution, shadowing, same-scope ambiguity (`E_IMPLICIT_AMBIGUOUS`), erased-candidate rejection |
| `qtt/` | §12.2–§12.4 usage counting: linear drop/overuse, erased runtime use, exit paths, demand scaling, latent closures, borrow escape, record paths, `using`+`defer`, Pi-quantity subsumption, capture-set type identity (§12.3.1: `captures-identity.kp`) |
| `queries/` | §20 comprehension clauses end to end (`order by`/`skip`/`take`/`distinct`/`group by`/`join`/left-join `into`, conflict policies) and §20.9–§20.10 query carriers with plan QTT checks (`E_QUERY_*`) |
| `collections/` | §20.1 set/map literals incl. empty `{}` |
| `records/` | projection, patch, punning, unknown-field errors, constructor field defaults (§10.1.1), dependent telescopes/`this` siblings (§13.2.1), open rows (§13.2.6), sealed packages — opaque-member stuckness and `E_SEAL_*` rejections (§13.2.10: `seal-opaque.kp`, `seal-errors.kp`) |
| `variants/` | closed unions, injection, missing member, `Int?` sugar |
| `traits/` | user traits, premise instance, defaults, `E_IMPLICIT_UNSOLVED`, `E_INSTANCE_INCOHERENT`, §28.2 base instances, supertrait premise enforcement (`E_SUPERTRAIT_UNSATISFIED`) |
| `equality/` | refl conversion, `subDefined` proof, symbolic failure, §31.1 conversion details — record η, projection-based tuple-let destructuring (`defeq-conversions.kp`) |
| `recursion/` | no-signature error, structural (clean), unverified warning |
| `fixity/` | user fixity, `E_OPERATOR_NO_FIXITY`, parenthesized prefix negation (§5.5.1.1) |
| `run/` | hello, while/var, for+break/continue+else, defer LIFO, try/except/finally, `let?`-else, early return, interpolation, statement-if |
| `labels/` | §18.2.5 labeled loops: plain `break` confined to its labeled loop, `break@outer`/`continue@outer` across an inner loop, `E_LABEL_UNRESOLVED` for missing/non-loop targets, inert `label@match` |
| `do/` | implicit do-bindings `let (@x : T) = e` joining the local implicit context (§16.3.3) |
| `shape/` | `assertDeclKinds` |
| `macros/` | §21 metaprogramming: quote/splice macros, §21.4 hygiene escape, macro-duplicated linear splices, Elab do reflection, §6.3.4 interpolated prefixed-string handlers, and the §21.6 convenience reflection queries (`defEqSyntax`/`headSymbolSyntax`/`sameSymbol` in ordinary positions with value asserts, plus their Elab-typed action forms) |
| `deriving/` | §22 `std.deriving.shape` reflection (`inspectAdt`, `matchAdt`, opacity) |
| `staging/` | §23 staged code: the quote/escape/`genlet`/`closeCode`/`runCode` pipeline with a user `Lift` instance, `E_QTT_BORROW_ESCAPE` for a quote capturing a borrowed parameter (§12.3), `E_CODE_ESCAPE_OUTSIDE_QUOTE` |
| `effects/` | §18.1 algebraic effects: deep/shallow handlers, multi-shot resumption, one-shot overuse, multi-shot linear-capture rejection |
| `projections/` | §9.1.1/§16.1.6 projection declarations: selectors, accessor bundles, footprints, zipper linear fill, `E_PROJECTION_CAPABILITY_REQUIRED` |
| `unicode/` | §3.1.3 source hygiene, invalid UTF-8 recovery, `g`/`b` quoted literals, §29.4 `std.unicode` runtime, scalar ranges |
| `unsupported/` | top-level `effect` declarations (`scoped effect` is the supported form), `exists`, `return@label`, `defer@label` → `E_UNSUPPORTED` |

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

Current tally over **950 fixture suites** (one result per fixture):

| outcome | count |
| --- | --- |
| pass | 920 |
| fail | 28 |
| unsupported | 2 |
| harness error | 0 |

There are no harness errors: every private, non-`x-` directive the
corpus actually uses has an evident portable meaning and is
implemented as a documented compatibility extension, as §T.1 permits
(`allow_unsafe_consume`, `assertParameterQuantities`, `assertEval`,
`assertDiagnosticCodes`, `assertExecute`, `assertRunStdout`,
`assertEvalErrorContains`, `assertDoItemDescriptors`,
`assertInoutParameters`, `assertContainsTokenTexts` — see the
directive table above); per §T.3 any future unknown non-extension
directive remains a harness error. The 2 unsupported are
spec-mandated: `requires capability incremental` (§T.7 presumes
Chapter 34 session reuse, which this implementation does not claim). `tests/external-results.md` carries the full
breakdown: a per-category table, the §T.8 classification rationale
with spec citations, and a "Blocked classifications" section
(maintained in `tests/external-blocked.md`, appended on regeneration;
`tools/run-external-fixtures.sh --regen` rebuilds the report from the
existing raw log without re-running the corpus) that classifies every
non-pass as outside-spec (mandated unsupported/harnessError), spec
conflict, or tracked gap. The §21–§23
metaprogramming lane (macros, deriving-shape, query sinks, the
§21.6 convenience reflection queries, §23 staged code), the
§14.2.1 associated-static-member/supertrait lane, static-object
kind selectors, import kind selectors/re-exports, and the
checked-arithmetic branch-refinement lane are fully clear; the 28
remaining failures are 11 cited spec conflicts and 17 tracked gaps
(recovery-cascade parity, §13.2.11 existentials, layout-continuation,
and diagnostic-code selection deltas at application boundaries — every
one is an honest spelling/cascade divergence, never a missed
rejection, and no cross-implementation code "tolerance" is applied) —
see the per-fixture tables at the end of
`tests/external-results.md`.

## Conventions

* New fixtures: one feature per file, `--!` directives at the top,
  `--!!` markers next to the offending line for diagnostics.
* Run-mode fixtures should assert exact stdout where the output is
  stable, and `assertExitCode 0`.
* Keep `cabal build` warning-free; the suite is the gate for every
  commit.
