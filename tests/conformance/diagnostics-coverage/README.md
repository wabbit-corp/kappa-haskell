# diagnostics-coverage — coverage-driven negative tests

52 negative conformance tests, each triggering a diagnostic the previous suite
**never exercised**, derived from coverage. See
[`docs/TESTING_STRATEGY.md`](../../../docs/TESTING_STRATEGY.md) → *coverage-driven
new tests*.

## How they were found
The §3 diagnostic contract defines ~236 emittable codes; cross-referencing the
codes the compiler can emit (`grep "E_…"/"W_…"` in `src/Kappa/`) against the codes
any conformance test references found **71 core-language codes with zero test
coverage** — concrete gaps in the diagnostic contract and the matching error paths
in `Kappa.Check`/`Lexer`/`Parser`. Each test here triggers one of them and asserts
it via `--! assertDiagnostic`.

Every test was **independently verified** (`kappa test <dir>` passes — the target
code is actually emitted). Together they add **558 compiler expressions (+0.36%
absolute)** the suite never reached, ~83% in `Kappa.Check` error-handling paths.

## Not all 71 are here
The rest are not triggerable from a single `.kp` under `check`/`run`:
`E_CONFIG_*`/`E_DEPENDENCY_*`/`E_BACKEND_*` need the `build --manifest` path;
`E_INTERNAL*`/`E_ELAB_STUCK` are internal invariants; `E_DO_EMPTY`/
`E_EXISTENTIAL_WITNESS_ESCAPE` are defensive guards the parser never reaches;
`E_IMPORT_CYCLE` needs a multi-file module set. Those are documented in the
strategy doc as out-of-scope for single-file conformance tests.
