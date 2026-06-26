# kappart2 microbenchmark

`make bench` (from `runtime/`) builds and runs `rt_bench.c` and the Go
comparison `go_pingpong.go`. It isolates the runtime's cost sources so the
"is this performant?" question is answered with numbers, not by eyeballing the
generated C.

## Representative numbers (Apple M-series, 1 worker, -O2, Boehm GC)

| workload | ns/op | bytes/op | note |
|---|---:|---:|---|
| **fork/await ping-pong (run)** | ~630 | 704 | the SUSPENSION cost (spawn a fiber, park, wake, detach) |
| &nbsp;&nbsp;CPS tree build (per bind) | – | 304 | structural cost of one `krt2_bind`+`kclo`+`KEnv`+`fork`+`pure` |
| **scalar across a park (run)** | ~320 | 1184 | a counter Int carried across a fork/await park, sum-checked — UNBOXING Stage-0 #4 |
| CK-machine `then`-step | ~26 | 48 | driving one `OP_THEN` through `deliver` |
| **boxed `addInt`** | ~12.5 | 48 | the Int VALUE-BOXING cost (one heap `KValue`/op; `sizeof(KValue)=48`) |
| **boxed `addDouble`** | ~5.2 | 48 | the binary64 boxing COST; Stage 2b's unboxed worker drives it to the 0-box floor (no Double cache) |
| **ctor-build (n-ary Cons)** | ~31 | 112 | boxed 2-arg ctor = Cons(48)+args(16)+`kint` head(48); STAYS boxed in Stage 1 (control) |
| **ctor0-build (nullary None)** | ~8 | 48 | nullary ctor heap box — Stage 1 makes it a 0-alloc `b010` immediate (the ctor-immediate WIN) |
| **ctor deref boxed (tagid+arg)** | ~1.2 | 0 | match-dispatch + projection on a boxed ctor — the TAG-TEST-TAX detector (go/no-go gate) |
| **ctor0 dispatch (nullary tagid)** | ~0.7 | 0 | match-dispatch on a value that becomes an immediate (the WIN half of the match requirement) |
| raw int64 add | ~0.22 | 0 | the floor |
| **Go goroutine spawn+join** | ~232 | 128 | comparison point for fork/await |

> `bytes/op` is exact (a GC byte counter, bit-identical across runs); `ns/op` carries
> ~10–15% hardware/thermal variance, so treat it as a same-machine reference, not an
> absolute. Numbers refreshed 2026-06-25 (`sizeof(KValue)` is now 48 B).

## UNBOXING Stage-0 baseline (the Stage-1 go/no-go gate)

Rows 3 and 6–10 are the UNBOXING-DESIGN §7/§8 **Stage-0 baselines**, recorded
*before* immediate-int/ctor tagging so Stage 1's effect is a measurable delta on
this same machine. What each gates:

- **`addDouble` (48 B/op)** — the F64 boxing COST (the ceiling); Stage 2b's unboxed
  worker drives it to the 0-box floor in fused regions. No Double cache exists, so it
  is a clean one-box-per-op analogue of `addInt` (the 7.0 literal is hoisted; an
  in-loop `kdbl` would box twice).
- **`ctor-build` (112 B/op) vs `ctor0-build` (48 B/op)** — Stage 1 splits exactly along
  the nullary/n-ary line: n-ary ctors STAY boxed (`ctor-build` must not move — the
  control), while nullary `Bool`/`Unit`/`Nil`/`None` become 0-alloc `b010` immediates
  (`ctor0-build` should drop 48 → 0 — the ctor-immediate win). `None` is used because
  `Unit` is canonicalized to `the_unit` and `Bool` is statically cached (both would
  understate the per-call alloc).
- **`ctor deref boxed` (~1.2 ns) + `ctor0 dispatch` (~0.7 ns)** — the tag-test tax/win.
  Stage 1 adds a low-bit tag test to every `->tag`/`->as.*` deref: on a BOXED ctor that
  is pure overhead (the deref still happens), so **`ctor-build` + `ctor deref boxed` are
  the go/no-go gate — Stage 1 must keep them within ~5–10%**; on a value that BECOMES an
  immediate the tag test REPLACES the deref (`ctor0 dispatch` should not regress).
- **`scalar across a park` (1184 B/op, sum-checked)** — a counter Int genuinely crosses
  a fork/await park (1 worker, so the child parks before the await) and is recovered
  correctly in the `KEnv` slot — the cross-park property a Stage-1 tagged immediate must
  preserve. The bench ASSERTS the recovered sum, flipping its label to `FAIL!!` on
  mismatch (so a regression that drops the carried value is loud, not silent).

## What the numbers say

1. **Value boxing is the dominant inefficiency, and it is orthogonal to the
   CPS/do-kernel work.** A boxed `addInt` is ~57× a raw int64 add (12.5 ns vs
   0.22) and allocates 48 bytes; every `Int`, every value, is a 48-byte GC'd
   `KValue` (inherited from the interpreter-era `kappart`). For compute-bound code
   this is the whole Go/Rust gap. **Unboxing / representation specialization is the
   highest-leverage performance milestone** — bigger than anything in the
   continuation strategy. The Stage-0 baseline above is what its win is measured
   against.

2. **The CPS suspension cost is real but modest — ~2.7× a Go goroutine
   spawn+join (~630 ns vs 232 ns), with ~5.5× the allocation (704 vs 128 B).** This
   is the price *at a concurrency boundary* (not per do-step). It is the same
   latency class as a goroutine park (O(1) capture + CAS + enqueue, no stack
   copy); the gap is allocation — a fresh `Fiber` + `Cont` frames each fork where
   Go reuses pooled `g` structs. Closeable with a fiber/continuation free-list and
   Perceus reuse (turn the per-bind alloc into an in-place write).

3. **The per-do-step cost (~26 ns, 48 B) is only paid for SUSPENDING binds.** The
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
