# Kappa Native Backend — Benchmark Design

Date: 2026-06-18
Author: native-backend performance research worker (proposal only).
Inputs: `NATIVE_BACKEND_OPTIMIZATION_GUIDE.md` §5 (benchmark methodology — Mytkowicz, Georges,
Kalibera & Jones) and §4 (the gaps each bench must detect), the existing `test/native/bench.sh`
and `test/native/bench/*`. (This doc is the detailed bench-taxonomy companion to the guide's §8.)
Companion: proposed bench sources under `test/native/bench/proposed/` (one file per codegen
dimension, each carrying purpose / expected optimized lowering / raw-C baseline idea / failure
mode), with raw-C baselines under `test/native/bench/proposed/raw/`.

## 1. Why the current suite is insufficient (and what it does right)

`bench.sh` is a *regression gate*, not a performance proof. It does several things correctly
and those should be kept:
- raw-C baselines built at `-O2` with a `volatile` accumulator + runtime `N`, so the C compiler
  cannot fold the loop away (research §5: the single most common microbenchmark error);
- allocation gates on cumulative `total_bytes` (deterministic; sensitive to per-iteration churn
  that `heap_size` misses — a point its own adversarial review established);
- two raw-C *ratio* gates (`tailsum`, `arithloop`) at ≤5× C.

Its shortcomings, mapped to methodology and to the gaps it cannot see:
1. **No statistics.** A single timed run via `date +%s.%N`; no warmup, repetition, or confidence
   intervals (research §5, Georges). A 1.2× vs 0.8× difference is within noise and currently
   indistinguishable from signal.
2. **No setup randomization** (Mytkowicz): link order / env size can bias a tight loop by more
   than the effect measured. Low cost to add (shuffle link order, vary env padding across runs).
3. **Narrow coverage.** Four benches: two scalar loops, one list fold, one record loop. It
   exercises none of the paths the gap analysis flags as worst (P0-A constructor construction,
   P1-C pattern-match shape, P0-D non-`Int` scalars, higher-order calls), so it *cannot detect a
   regression in or an improvement to* exactly the code that needs work.
4. **Ratio gates only where it already passes.** `listfold`/`recproj` have allocation bounds but
   no raw-C ratio gate; the ADT/closure/string/IO dimensions have neither.
5. **Allocation reported only cumulatively.** `total_bytes` is good but a *per-iteration*
   allocation figure (total ÷ N) is what makes "zero per-iteration allocation on the fast path"
   claims checkable at a glance.

## 2. Methodology this suite adopts (research §5)

- **Defeat dead-code elimination.** Every bench consumes its result via a side effect the C
  compiler cannot prove dead (print the final value), and the raw-C baseline uses a `volatile`
  sink + runtime `N`. A bench that prints a constant the optimizer could fold is rejected.
- **Repetition + confidence intervals.** Run each bench `R` process invocations (default `R=10`),
  discard the first as warm-up of OS/file caches (AOT C-from-Kappa has little runtime warmup, so
  `R=10` suffices; research §5 notes the Java warmup emphasis is JIT-specific), report
  median and a nonparametric CI (e.g. min/max or 25th/75th percentile). Call a difference real
  only when intervals do not overlap.
- **Spend repetitions where variance lives** (Kalibera & Jones). If build-to-build variance
  dominates (it can, via code layout), repeat the *build*, not just the inner loop. The harness
  exposes a `REBUILD` knob.
- **Setup randomization** (Mytkowicz): vary link order and an environment-size pad across the `R`
  invocations; if the ranking flips, the result is layout noise, not a real difference.
- **Count allocations, separately from time.** Report `total_bytes`, `collections`, and
  `total_bytes / N` (per-iteration) from `KAPPA_GC_STATS=1`. For a functional language the
  allocation behavior *is* the story; a raw-C baseline that stack-allocates is not like-for-like
  on time alone unless allocation is reported beside it.
- **Honest baselines.** Each raw-C baseline computes the *same* result with the *same* I/O at the
  *same* `-O2`, and is "conservative" (volatile loop-carried state) so it is a fair *lower bound*
  on achievable time, not an unrealistically foldable one. Where the Kappa version must allocate
  a data structure the C baseline also allocates it (e.g. a real linked list), so the comparison
  is like-for-like; where the point is "should allocate nothing," the C baseline is scalar.
- **Pin the environment.** Document CPU, compiler + version, `-O` level, and (where possible) pin
  CPU frequency / disable turbo for the timed section; record these in the report output.

## 3. Bench taxonomy — dimensions, the gap each targets, and gates

Each dimension has (where useful) an **allocation-heavy** and an **allocation-free/optimized**
variant so the suite measures both the current cost and the headroom a roadmap item should
unlock. Gate types: **ratio** (native/raw-C time ≤ X), **alloc** (total_bytes or per-iter
bound), **report** (tracked, not gated yet).

| # | Bench (proposed file) | Dimension | Gap it detects | Gate (initial) |
|---|---|---|---|---|
| 1 | `scalar_intloop.kp` | scalar Int loop | LR1/P0.2 regression | ratio ≤5× C, ~0 alloc/iter |
| 2 | `scalar_doubleloop.kp` | scalar Double loop | P0-D (no Double worker) | report→ratio after R2.2 |
| 3 | `adtbuild.kp` | ADT/list construction | **P0-A** eta-ctor closure storm | alloc/iter ≤ 1 cell+1 box |
| 4 | `adtmatch.kp` | ADT/variant matching | **P1-C** if-chain (LR2 tags shipped) | report→`switch` after R1.2 |
| 5 | `mutualrec.kp` | mutual tail recursion | P1-E trampoline/bounce | constant stack; alloc bound |
| 6 | `hofmap.kp` | higher-order map/fold | eval/apply, arity-1 chain | report (R3.2 target) |
| 7 | `closure_capture.kp` | escaping closures | P1-H KEnv, safe-for-space | report + space-safety check |
| 8 | `optionchain.kp` | Option/Result-heavy | ADT box + match | alloc report |
| 9 | `polyvsmono.kp` | polymorphic vs monomorphic | P0-D specialization | ratio(poly/mono) report |
| 10 | `listops.kp` | small lists / map ops | KEnv + ctor + match combined | alloc report |
| 11 | `byteloop.kp` | byte/string loop | string/bytes path costs | ratio vs C byte loop |
| 12 | `strbuild.kp` | string building | quadratic append detection | alloc/time scaling check |
| 13 | `ioloop.kp` | IO boundary | krun_io / kio_tail per-step cost | alloc/iter bound |
| 14 | `deferloop.kp` | defer/using/effects | defer registration alloc | alloc/iter bound |
| 15 | `sqlite_shape.kp` | sqlite-shaped query loop | FFI boundary + per-row alloc | report (no real FFI) |
| 16 | `http_kernel.kp` | tiny HTTP/serialize kernel | realistic mixed workload | report ratio + alloc |

Notes:
- **Baseline coverage is partial and that is stated, not hidden.** Only 4 of the 16 benches
  ship a raw-C baseline file today (`scalar_intloop`, `scalar_doubleloop`, `adtbuild`,
  `byteloop`); the rest are **report-only** (time + allocation tracked, no ratio gate) or use a
  self-relative ratio (`polyvsmono`) or a constant-stack/allocation check (`mutualrec`). A ratio
  gate is only added once a fair like-for-like baseline exists for that dimension; until then the
  bench is a tracked number, never cited as a near-C claim (§4). The remaining baselines
  (`mutualrec` state-loop, `sqlite_shape` struct-row array, `http_kernel` enum-switch handler)
  are described in the bench files for when the corresponding roadmap item lands.
- **Allocation-heavy vs allocation-free pairing** is built into #1 (the optimized `Int` loop)
  vs #3 (the allocation-heavy ADT build), #6 (HOF, allocation-heavy) vs an inlined first-order
  variant, and the `_alloc` vs `_opt` suffixes used inside several files' comments.
- **#15 `sqlite_shape`** does not link real sqlite (the base runtime is FFI-stub); it *models the
  shape* — a prepare/step/reset loop over an in-memory list of "rows" (records) — so it stresses
  the same codegen (record construction, per-row projection, accumulation) a real query loop
  would, without depending on hidden non-spec primitives (review note §8). A real-FFI variant is
  described in the file for when the demo runtime is linked.
- **#16 `http_kernel`** is a tiny request-line parser + response serializer over `Bytes`/`String`
  — a realistic mixed kernel touching byte loops, ADT/Option, records, and string building at
  once; it is the closest thing to an end-to-end number.

## 4. Gate philosophy (avoid the trap the gap analysis warns about)

- Gate **only what is currently achievable**, and convert `report` → `ratio`/`alloc` gates as
  each roadmap item lands (e.g. #4 gets a "`switch`-emitted on the match path" check after R1.2 —
  `strcmp` was already removed by LR2; #3
  gets a tight alloc/iter gate after R1.1). This prevents a gate from blocking unrelated work
  while still ratcheting.
- Never cite a `report`-only bench as evidence of "near raw C." The research is explicit
  (§5/§6): a performance *claim* requires the ratio gate + allocation count + CI, not a single
  number.
- Keep a CI smoke subset (bounded N, the fast-path benches) wired into the native suite so the
  optimized paths stay *exercised*, not dead — extending the existing QW4 practice.

## 5. Reproducibility contract

Each run records: host CPU model, `cc`/`zig` version, `-O2`, `KAPPA_GC_STATS` output
(`total_bytes`, `heap_size`, `collections`), `R`/`REBUILD` settings, and the native-vs-raw-C
median ± interval and per-iteration allocation for every bench. The proposed
`test/native/bench/proposed/README.md` specifies the exact build/run commands and the schema of
the recorded results, so a third party can reproduce the numbers and check the provenance.
```
KAPPA_CC="cc -O2" cabal run -v0 kappa -- build test/native/bench/proposed/<b>.kp -o /tmp/<b>
KAPPA_GC_STATS=1 /tmp/<b>            # prints result + [kappa-gc] total_bytes/heap_size/collections
cc -O2 test/native/bench/proposed/raw/<b>.c -o /tmp/<b>_c && /tmp/<b>_c <N>
```
