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

## Raw-C review (`NATIVE_BACKEND_RAW_C_PERFORMANCE_REVIEW.md`) — status scorecard

The raw-C report is the governing performance standard. Honest status (NOT a
claim the backend is raw-C overall — only the LR1 Int-worker case meets it):

| Item | Status |
|---|---|
| **P0.1** monomorphic numeric boxed → scalar workers | **MET for `Int`** (LR1: scalar `int64` worker, zero per-iter alloc, 1.03× `cc -O2`); `Bool`/`Double` workers not yet done |
| **P0.2** `var` loops are heap-ref loops | **OPEN** — `arithloop` still ~145 MB / 81.5× C (reported, not claimed raw-C) |
| **P0.3** `KEnv`/`kvar` on hot paths | **MET for LR1 Int workers** (scalar locals, no `KEnv`/`kvar`); general first-order code still uses `kvar` (QW2 only removed the per-iter *rebuild*) |
| **P0.4** records/ADTs generic+string | **OPEN** — `recproj`/match still `kproj`/`kctor_is` strcmp (LR2) |
| **P0.5** known calls carry trampoline/closure | **MET for LR1 Int self-calls** (loop / direct, no trampoline); general known calls still trampoline |
| **P1.1** `-O2` perf builds | **DONE** (`bench.sh` builds native + raw-C at `-O2`) |
| **P1.2** raw-C baseline gates + ratios | **DONE** (raw-C baselines + native/C ratio; `tailsum` gated ≤5× C — actually 0.2×; `arithloop` reported as P0.2-pending) |
| **P1.3** QW2 doc overclaim | **FIXED** (QW2 = "env rebuild removed", not "env/kvar eliminated"; see below) |

LR1 is one piece of the raw-C goal. The remaining P0.2 (`var`-loop locals),
P0.4 (record/ADT fixed offsets + numeric tags), and the general P0.3/P0.5
(bare locals + direct calls for non-`Int` first-order code) are the subsequent
raw-C iterations, each to be landed behind the boxed-ABI fallback with its own
review and raw-C gate.

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

### QW2 — No per-iteration `KEnv` *allocation* in direct worker loops (notes §3, §5, criterion #4)
- **What QW2 actually does (corrects an earlier overclaim, raw-C review P1.3):**
  a capture-free worker builds its parameter `KEnv` cells ONCE before the
  `while(1)` loop and a self-tail call updates `cell->val` in place, so the
  loop performs no per-iteration `KEnv` *allocation*. It does NOT eliminate
  `KEnv`/`kvar` from the boxed worker's code path — params are still read via
  `kvar(kw_env,i)`. So QW2 = "env rebuild removed", NOT "env/kvar eliminated".
- Full elimination of `KEnv`/`kvar` (params as bare C locals, raw-C review
  P0.3) is achieved for **monomorphic Int workers by LR1** (the `kwi_*` worker
  uses scalar `int64_t` C params/locals — no `KEnv`/`kvar` at all). For general
  (non-Int / higher-order-adjacent) first-order code it remains open work.

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

### LR1 — Typed unboxed `Int` workers (notes §2, criterion #3; raw-C review P0.1) — **DONE (Int)**
A first-order monomorphic `Int` function gets an auxiliary scalar worker
`int64_t kwi_g(int64_t…, int *kovf)` beside the boxed `kw_g`:
- **Eligibility** (conservative; src/Kappa/Backend/C.hs `lr1Arity` + `i64Elig*`):
  n explicit, relevant (non-`Q0`) leading binders, and a body built ONLY from
  in-range `Int` literals, params, the int prims `{add,sub,mul,div,mod,neg,eq,
  lt,le}Int`, `if` with an int-compare condition, and SATURATED self-calls.
  Anything else (CLet, if-in-value-position, calls to other globals,
  ctor/proj/match/do/lambda, an implicit/erased binder, a user-shadowed prim)
  ⇒ ineligible ⇒ boxed-only.
- **Codegen**: tail self-calls become an int64 `while`-loop with direct param
  reassignment (no `KEnv`/`kvar`); non-tail self-calls recurse `kwi_g`; arith
  uses `__builtin_*_overflow`/`INT64_MIN` guards mirroring the `kp_*` helpers.
- **Overflow escape (§6 unbounded `Int`)**: the call site (`compileLr1Call`)
  unboxes `K_INT` args (`kunbox_i64`); a non-`K_INT` arg OR any int64 overflow
  sets `kovf` and re-runs the boxed worker `kw_g` from the ORIGINAL boxed args,
  so the result is identical to the interpreter (the boxed/GMP path is the
  reference). The unboxed worker is auxiliary — never the closure entry.
- **Verified**: a 20-program battery + two adversarial reviews (overflow/escape
  parity, eligibility soundness, regression) all PASS; `tailsum 1e6`:
  193 MB → **368 bytes**, and **1.03×** a handwritten `cc -O2` int64 loop at
  N=1e9 (raw-C review P0.1/P0.3/P0.5 met for the Int-worker case; gated in
  `bench.sh`). Soundness is enforced at runtime by `kunbox_i64` even if the
  body-structural classifier over-accepts: a non-`K_INT` arg always escapes
  before the unboxed worker runs.
- **Not yet done**: `Bool`/`Double` unboxed workers, and cross-function int64
  chaining (calls to OTHER eligible Int globals are currently a boxed
  boundary). These are follow-ups; `Int` self-recursive kernels are the win.

### LR2 — Numeric IDs for constructors / variants / record fields (notes §4, criterion #5)
- Assign per-program integer IDs to constructor names, variant tags, and

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
