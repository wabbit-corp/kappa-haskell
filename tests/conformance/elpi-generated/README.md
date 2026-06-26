# elpi-generated — coverage-selected λProlog synthesis tests

These 13 `.kp` files are a **coverage-greedy-selected minimal subset** of the
5,000-case λProlog (Elpi) type-synthesis corpus in the reference repo
(`../kappa/elpi-tests/lp_kappa_*/`). See
[`docs/TESTING_STRATEGY.md`](../../../docs/TESTING_STRATEGY.md) → *imported corpora*
for the full method.

## What they are
The reference repo encodes Kappa's type system in λProlog
(`tools/lambda_prolog/kappa_generator.elpi`) and uses it as an **independent second
type checker** to synthesize well-typed programs. Each file here was proven
well-typed by that oracle and is accepted by this compiler — so they double as a
differential check against the spec's typing rules.

## Why only 13 (not 5,000)
Of the 5,000, **1,821 pass this compiler's checker**. All 1,821 are structurally
distinct, but **coverage-redundant**: greedy HPC set-cover over compiler-expression
coverage collapses them to these **13**, which together tick **248 compiler
expressions (+0.16% absolute) the hand-written suite never reaches** — almost all in
`Kappa.Check` (type-checker elaboration). Importing all 1,821 would add the *same*
0.16% at 140× the test count, so we keep only the non-overlapping 13.

They exercise feature *combinations* the curated suite misses — multi-shot `deep
handle` effect programs with `ω`-quantity operations (`lp_kappa_4896`, +137 boxes),
`Set` literals (`lp_kappa_4034`), `Map` comprehensions with `on conflict` resolution
(`lp_kappa_2511`), elvis/`?:` chains, nested matches. The runnable (`result : Int`)
ones were verified `interp == C == LLVM`.

## Provenance
Each `lp_kappa_NNN.kp` is the `main.kp` from `../kappa/elpi-tests/lp_kappa_NNN/`.
Regenerate/refresh via the elpi generator (see the ROADMAP Testing track). The
selection is reproducible: `/tmp/elpi_greedy_cover.py` (baseline = the conformance
suite's tix, greedy over the passing positives' marginal coverage).
