# kappart2 microbenchmark

`make bench` (from `runtime/`) builds and runs `rt_bench.c` and the Go
comparison `go_pingpong.go`. It isolates the runtime's cost sources so the
"is this performant?" question is answered with numbers, not by eyeballing the
generated C.

## Representative numbers (Apple M-series, 1 worker, -O2, Boehm GC)

| workload | ns/op | bytes/op | note |
|---|---:|---:|---|
| **fork/await spawn+join** | ~1050 | 832 | the SUSPENSION cost (spawn a fiber, park, wake, detach) |
| &nbsp;&nbsp;CPS tree build (per bind) | – | 416 | structural cost of one `krt2_bind`+`kclo`+`KEnv`+`fork`+`pure` |
| CK-machine `then`-step | ~32 | 48 | driving one `OP_THEN` through `deliver` |
| **boxed `addInt`** | ~13 | 64 | the VALUE-BOXING cost (one heap `KValue` per op) |
| raw int64 add | ~0.23 | 0 | the floor |
| **Go goroutine spawn+join** | ~293 | 128 | comparison point for fork/await |

## What the numbers say

1. **Value boxing is the dominant inefficiency, and it is orthogonal to the
   CPS/do-kernel work.** A boxed `addInt` is ~50× a raw int64 add and allocates
   64 bytes; every `Int`, every value, is a ~40-byte GC'd `KValue` (inherited
   from the interpreter-era `kappart`). For compute-bound code this is the whole
   Go/Rust gap. **Unboxing / representation specialization is the highest-leverage
   performance milestone** — bigger than anything in the continuation strategy.

2. **The CPS suspension cost is real but modest — ~3.5× a Go goroutine
   spawn+join (≈1 µs vs 293 ns), with ~6.5× the allocation (832 vs 128 B).** This
   is the price *at a concurrency boundary* (not per do-step). It is the same
   latency class as a goroutine park (O(1) capture + CAS + enqueue, no stack
   copy); the gap is allocation — a fresh `Fiber` + `Cont` frames each fork where
   Go reuses pooled `g` structs. Closeable with a fiber/continuation free-list and
   Perceus reuse (turn the per-bind alloc into an in-place write).

3. **The per-do-step cost (~32 ns, 48 B) is only paid for SUSPENDING binds.** The
   §3.3 suspendability analysis keeps non-suspending binds straight-line C, so a
   sequential/arithmetic loop never touches `krt2_bind` — its cost is item 1
   (boxing), not the CK-machine.

## Takeaway

The indirection that *looks* expensive in the generated C (CPS nodes, `kclo`
chains, `kpf_` wrappers) is **not** the dominant cost: the wrappers inline under
`-O2`, the curry chains are elided on saturated calls, and the CPS bind is only
at suspension points. The real lever is **value unboxing** (a 50× factor),
followed by **fiber/continuation pooling + Perceus** for the suspension path.
The shape we are building (heap-reified one-shot continuations) is what LLVM
coroutines + Perceus were designed to collapse — see `docs/CPS-DESIGN.md §5–§6`.
