# Proposed native-backend benchmarks

Date: 2026-06-18. Status: **proposals** accompanying `docs/KAPPA_NATIVE_BENCHMARK_DESIGN.md`
and `docs/NATIVE_BACKEND_OPTIMIZATION_GUIDE.md` §4 (the gaps each bench detects). These are design artifacts:
each `.kp` carries, in its header comment, the four required fields —

  * **Purpose** — which codegen/optimization dimension it exercises;
  * **Expected optimized lowering** — what good native code would look like;
  * **Raw-C baseline idea** — the fair handwritten-C comparison;
  * **Failure mode it detects** — the concrete gap (P0-A … etc.) it would catch.

They are written against the surface syntax used in `test/native/cases/*` (verified patterns:
`data`, `match/case`, `do`/`var`/`while`/`for`/`defer`, lambdas `\x -> e`, `Option`/`Result`,
list `::`/`Nil`, records `(x = …)` + `.field`, prims `addInt`/`leInt`/`showInt`/`stringAppend`).
Several are confirmed to build today (see the table); the rest are intended to build after the
roadmap items they target land, or may need a one-line syntactic tweak — they are *proposals*,
not a committed gate. **Self-contained on purpose:** HOF/list benches define their own
`map`/`fold` rather than relying on a particular prelude module path, so they isolate the
codegen dimension under test.

## Build / run / compare (per `KAPPA_NATIVE_BENCHMARK_DESIGN.md` §5)

```
# native, with allocation stats
KAPPA_CC="cc -O2" cabal run -v0 kappa -- build proposed/<bench>.kp -o /tmp/<bench>
KAPPA_GC_STATS=1 /tmp/<bench>        # prints result + [kappa-gc] total_bytes/heap_size/collections

# raw-C baseline (where provided)
cc -O2 proposed/raw/<bench>.c -o /tmp/<bench>_c && /tmp/<bench>_c <N>
```

For a real measurement use the methodology in the design doc: ≥10 invocations, median ±
interval, per-iteration allocation = total_bytes / N, setup randomization, pinned CPU frequency.

## Index

| File | Dimension | Targets gap | Raw-C baseline | Builds today? |
|---|---|---|---|---|
| `scalar_intloop.kp` | scalar Int loop (alloc-free) | LR1/P0.2 | `raw/scalar_intloop.c` | yes |
| `scalar_doubleloop.kp` | scalar Double loop | P0-D | `raw/scalar_doubleloop.c` | yes |
| `adtbuild.kp` | ADT/list construction (alloc-heavy) | **P0-A / P0-B** | `raw/adtbuild.c` | yes |
| `adtmatch.kp` | ADT + variant matching | **P0-C** | — | yes |
| `mutualrec.kp` | mutual tail recursion | P1-E | — | yes |
| `hofmap.kp` | higher-order map/fold | eval/apply, P1-H | — | yes |
| `closure_capture.kp` | escaping closures / space safety | P1-H | — | yes |
| `optionchain.kp` | Option/Result-heavy | ADT box + match | — | yes |
| `polyvsmono.kp` | polymorphic vs monomorphic call | P0-D | — | yes |
| `listops.kp` | small list map+filter+fold | ctor+match+KEnv | — | yes |
| `byteloop.kp` | byte loop | bytes path | `raw/byteloop.c` | yes |
| `strbuild.kp` | string building (quadratic check) | append scaling | — | yes |
| `ioloop.kp` | IO boundary per-step cost | krun_io/kio_tail | — | yes |
| `deferloop.kp` | defer/effects per-iteration | defer alloc | — | yes |
| `sqlite_shape.kp` | sqlite-shaped query loop (modeled) | record/proj/accum | — | yes |
| `http_kernel.kp` | tiny HTTP request/response kernel | mixed realistic | — | yes |

**Provenance:** all 16 benches were built AND run to completion at this commit with
`KAPPA_CC="cc -O2" cabal run -v0 kappa -- build proposed/<b>.kp` (then executed with
`KAPPA_GC_STATS=1`). Examples: `scalar_intloop` → `50000005000000`, `adtmatch` → `500000`,
`adtbuild` → `2000001000000`, `byteloop` → `1000000`, `hofmap` → `2000003000000`. "Builds
today: yes" therefore reflects a verified build *and run*, not just an expectation.

Earlier drafts of `hofmap`, `listops`, and `polyvsmono` were written with **non-tail** recursion
and segfaulted at their default N — deep non-tail recursion rides the C stack (only tail calls
are trampolined in the current backend), so a 5e5–1e6-deep non-tail call overflows it. They have
been rewritten to tail-recursive accumulator form so they run at scale while still exercising
their dimension; the original segfault is itself a noted robustness observation (native non-tail
recursion is not C-stack-bounded, unlike the interpreter's §32.1 depth guard). If a future syntax
change breaks one, it remains a documented target — adjust syntax to taste when adopting.
