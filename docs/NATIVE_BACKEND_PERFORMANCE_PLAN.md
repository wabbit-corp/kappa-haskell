# Native backend performance plan

Response to `docs/NATIVE_BACKEND_PERFORMANCE_REVIEW_NOTES.md` (2026-06-17).
The objection is accurate: the backend defaults to the generic boxed/string
ABI even where the compiler has the type/layout to do better. This plan
separates **quick wins** (this iteration) from **larger representation
changes** (staged), with concrete mechanisms, and ends with benchmark gates
and an adversarial performance review.

## Status (2026-06-17)

Quick wins **QW1–QW4 are DONE** (built `-Werror` clean; native suite ALL
PASSED incl. the new benchmark gates; conformance 242/242; native ≡
interpreter preserved). Measured: the `sum 1..1_000_000` perf smoke dropped
~0.45s → ~0.22s after QW1 (direct prim helpers eliminated per-iteration string
dispatch); a tight self-tail Int loop keeps `heap_size` ≈ 128 KB under QW2
(parameter env no longer rebuilt per iteration — confirmed by `bench.sh`'s
heap gate). The larger representation changes **LR1 (typed unboxed workers)**
and **LR2 (numeric ctor/variant/field IDs)** are STAGED (see below) with
benchmark evidence: the dominant remaining allocation in a tight Int loop is
`kint` result boxing (≈193 MB total / ≈1500 collections for `sum 1..2e6`,
`heap_size` tiny) — i.e. LR1's target, not the env (QW2 removed that). An
adversarial performance review (criterion #8) covers QW1–QW4's correctness and
efficacy and grounds the LR staging.

## Quick wins (this iteration) — DONE

### QW1 — Kill string dispatch for statically-known saturated primitives (notes §1)
- Add a `KPrimId` enum (`runtime/kappart.h`) and factor the hot pure ops in
  `prim_fire_pure` into direct C helpers (`kp_addInt`, `kp_leInt`,
  `kp_showInt`, …) that the string chain also calls (one source of truth).
- Codegen (`compileApp`): for a saturated application whose spine head is a
  known prim with a direct helper, emit the **direct helper call**
  (`kp_addInt(a,b)`) — no `kprim_call`, no `prim_arity`, no `prim_is_io`, no
  `strcmp`. Fall back to `kprim_call` only for IO/partial/unlisted prims.
- A Haskell `primDirect :: Text -> Maybe (Text, Int)` table (helper name +
  arity) is the codegen source of truth; the native suite catches drift.

### QW2 — No `KEnv` allocation in direct worker loops (notes §3, §5, criterion #4)
- A top-level function worker currently rebinds `kw_env = kpush(p1,kpush(p0,0))`
  every loop iteration and reads params via `kvar(kw_env,i)`. Map the leading
  de Bruijn indices `[0..n-1]` directly to the C locals `p0..p{n-1}`
  (`gsEnv` carries a "worker params" prefix), so the loop touches no `KEnv`.
- Only escaping closures/lambdas still build a `KEnv`. Self-tail loop already
  reassigns locals + `continue` (no `K_BOUNCE`); this removes the per-iter env.

### QW3 — Source-faithful generated C names + source-span comments (notes §6, criterion #6)
- Thread an enclosing-name hint into `freshN` for closures/lambdas/match
  blocks (`kfn_main_len__cons`, `kmatch_main_len`), with the global counter
  kept only as a uniqueness suffix.
- Emit a `/* <module.fn> : <role> */` comment before each generated helper.

### QW4 — Benchmarks + allocation/GC gates (notes §7, criterion #7)
- `test/native/bench.sh`: arithmetic loop, tail-recursive sum, list fold,
  record projection, variant match, bytes append/slice, IO loop — each timed
  native vs interpreter, with `GC_get_heap_size`/allocation counters in a
  `--bench` runtime mode. Wire a bounded smoke into the native suite so the
  optimized paths are *exercised*, not dead.

## Larger representation changes (STAGED — next iteration, with fallback to the boxed ABI)

Staging rationale: LR1/LR2 are whole-value-representation changes whose failure
mode is a *silent miscompile* (a wrong unboxing boundary or a ctor-tag
mismatch produces a wrong answer, not a crash) — the exact bug class the
native-backend conformance work (seven review rounds) fought. They are
sequenced as a distinct reviewed iteration rather than bundled with the
low-risk QW1–QW4 wins, each landing behind a boxed-ABI fallback and its own
native ≡ interpreter gate. Safe-design constraints captured now:

- **LR1** — an unboxed `int64_t` `Int` worker MUST escape to the GMP/boxed
  path on overflow (`Int`/`Integer` are unbounded, §6), so even a first pass
  needs the overflow-escape + boxed wrapper at every generic/HO/partial
  boundary; `Bool` (C `int`) and `Double` (IEEE, no overflow escape) are the
  lower-risk first targets. Target evidenced by the benchmark above (`kint`
  result boxing dominates a tight Int loop).
- **LR2** — ctor/variant tags must be CONSISTENT between codegen-emitted
  `kctor` calls and the runtime's own ctors (`knil`/`kcons`/`kbool`/`krat`);
  the safe scheme is a name-derived tag (e.g. a compile-time hash emitted by
  codegen + stored by `kctor`) with a `strcmp` confirm on tag-match (no
  collision miscompile), or record/tuple **fixed offsets** where the layout is
  statically known. The review's `remaining-cost` dimension picks the
  higher-value piece (note that short prelude-name `strcmp`s already
  early-exit, so record fixed-offset projection may outrank ctor tags).

### LR1 — Typed worker specialization for monomorphic first-order code (notes §2, criterion #3)
- For a non-polymorphic, first-order function whose parameter/result types
  are concrete `Int`/`Bool`/`Double` (and all call sites saturated), generate
  an **unboxed worker** (`int64_t kwi_…(int64_t…, int *overflow)` for `Int`
  with a GMP escape; C `int` for `Bool`; `double` for `Double`), plus a boxed
  wrapper at generic/higher-order/partial-application/variant boundaries.
- Start with leaf arithmetic/compare helpers operating on unboxed scalars;
  box only at boundaries. Fall back to the boxed worker when polymorphism,
  partial application, or existential/variant packaging needs generic values.

### LR2 — Numeric IDs for constructors / variants / record fields (notes §4, criterion #5)
- Assign per-program integer IDs to constructor names, variant tags, and
  record field labels (a codegen-built table). Store the int tag in
  `K_CTOR`/`K_VARIANT` (debug name retained for diagnostics only); compile
  pattern matching to a `switch` on the tag, and known record/tuple layouts
  to fixed offsets. Keep `strcmp`/linear-scan only for dynamic/open-record
  fallback. Staged: ship with tests proving the string path is not used in
  list/tuple/record hot cases.

## Adversarial performance review (criterion #8) — findings + remediation

The QW1–QW4 work was put through an adversarial performance reviewer (prebuilt
binary only). Outcome:

- **QW1 (direct prim helpers)** — verified behaviour-preserving: argument
  evaluation is forced into temps before the `kp_*` call; partial application
  correctly still curries via `kprim_call`; div/mod-by-zero, `INT64_MIN`,
  GMP-overflow promotion, and `eqDouble` (raw-bit) vs `floatEq` all match the
  interpreter. Reviewer-flagged gap (pure prims still on string dispatch):
  fixed by extending `primDirect` with `showInt`/`showDouble`/`showScalar`/
  `showStringLit`/`intToDouble`/`eqByte`/`ltByte`/`__intAnd`/`__intOr`/
  `__intXor`.
- **QW2 (in-place self-tail loop)** — reviewer found a **blocker**: an escaping
  closure/thunk capturing a loop parameter was corrupted because the in-place
  `cell->val =` mutation overwrote the snapshot it must observe. **Fixed**:
  `compileFunctionGlobal` now uses the in-place loop ONLY for a capture-free
  body (`bodyCapturesEnv`); a body that creates any env-capturing value
  (closure/thunk/do/letrec) falls back to the per-iteration env rebuild (the
  pre-QW2 behaviour), so each iteration's escaping closures capture a distinct
  env — matching the interpreter. Capture-free hot loops keep the no-alloc
  in-place path. The argument-aliasing case (`f a b = f b a`) was verified
  correct (args snapshotted into temps before any update).
- **QW4 (gates)** — reviewer found the `heap_size` gate **insensitive** to the
  per-iteration-allocation regression it claimed to catch (a reintroduced env
  rebuild moves `total_bytes` +65% but leaves `heap_size` byte-identical).
  **Fixed**: `bench.sh` now gates on `total_bytes` (cumulative, deterministic,
  sensitive) with per-bench bounds.
- **Remaining-cost** — confirmed the staged plan identifies the dominant costs:
  `kint` result boxing (~48 B/box, small-int cache `[-16,256]`) dominates a
  tight Int loop and is allocation-bound (LR1's target); the higher-value LR2
  sub-piece is record/tuple **fixed-offset projection** (`kproj` linear
  `strcmp` ~31 ns/op) over ctor tags (short prelude-name `strcmp`s already
  early-exit). This sharpens the LR staging above.

After remediation, a focused re-review (QW2 capture-correctness + gate
soundness + a regression sweep) returned **PASS / PASS, zero confirmed
serious**: `bodyCapturesEnv` is structurally total over all 25 `Term`
constructors (a missed capture is impossible by construction); every escaping
closure/thunk/do/letrec shape uses rebuild mode and matches the interpreter;
capture-free workers stay in the no-alloc in-place loop; the `total_bytes`
gate catches the +65% per-iteration-allocation regression a `heap_size` gate
would miss; and a 22-program sweep + the 25 native-suite cases show no
regression from the QW1 helper extension or the QW2 branching.

## Acceptance + review
- After QW1–QW4 (and as much of LR1/LR2 as lands), an **adversarial
  performance reviewer** (notes §8) checks for remaining string dispatch in
  generated hot paths, avoidable boxing, avoidable heap-env allocation, and
  opaque names — and that the optimized paths are exercised by the benchmarks.
- `KValue` stays the fallback ABI; the goal is that monomorphic first-order
  arithmetic / bool / projection / direct calls no longer route through it.
