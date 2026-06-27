# Cross-Language Benchmarking

How we measure Kappa against other languages — *which* suites, *why* each one,
what is runnable **today** vs. what needs library work, and how to run them
fairly. This is the external apples-to-apples layer on top of the internal cost
model in [`runtime/bench`](../runtime/bench/README.md) (`make bench`), which
already isolates the runtime's own cost sources and carries a Go-goroutine
comparison point.

## Philosophy — pick the suite by what we want to prove

Kappa has two very different stories, and they call for different benchmarks:

- **Strength — the concurrency runtime** (M:N fibers, libuv reactor, STM,
  structured concurrency, effect handlers). `make bench` already shows
  `fork/await ≈ 3.5× a goroutine` (≈630 ns vs ≈232 ns), **not** the 50× of the
  boxing path. This is where Kappa is genuinely competitive, so concurrency
  suites are the ones to **lead** with.
- **Current weakness — allocation / boxing** (the "50× lever" in the bench
  baseline). Allocation-heavy benchmarks will lose badly until the
  unboxing / Perceus / layout tracks land — but that is exactly why they are
  worth running: they are a **diagnostic gate** for that work, an honesty metric,
  **not** a headline number.

Rule of thumb: **lead public comparisons with concurrency** (where the runtime
shines); keep the allocation benchmarks as an internal progress tracker until
unboxing closes the gap.

## What the internal bench already gives us (and what it doesn't)

[`runtime/bench/rt_bench.c`](../runtime/bench/rt_bench.c) + `go_pingpong.go`
(`make bench`) measure the runtime's *own* cost sources in isolation —
suspension (fork/await), CPS-node structural cost, value boxing, CK-machine step
— in `ns/op` **and exact `bytes/op`** (a GC byte counter, bit-identical across
runs), with a single cross-language point (Go goroutine spawn+join). That answers
"where does our time/allocation go?" It does **not** answer "how do we compare to
GHC / OCaml / Rust / Erlang on a real program?" — which is what the suites below
add.

## Feasibility constraints (from the current implementation)

Verified against the repo so the plan is honest about what runs now:

- **Console output exists** (the conformance suite compares stdout; the
  image-loader test runner prints `IMAGE TESTS: ALL PASS`) via `std.debug` /
  a host-write FFI — enough to print a result line. There is **no polished
  `putStrLn`**.
- **No `getArgs` / stdin surface.** CLBG passes `N` via `argv` and several
  programs consume stdin. Mitigation: **hardcode `N`** (standard for internal
  benchmarking) or add a tiny args/stdin FFI. This defers the stdin-consuming
  CLBG programs (k-nucleotide, reverse-complement, regex-redux) until input
  exists; the numeric + tree ones are self-contained.
- **No HTTP / socket / DB stack.** The `http_sqlite` item is a *C runtime test*,
  not a Kappa web stack. TFB therefore needs an HTTP server + JSON encoder +
  Postgres driver built via FFI (the runtime already links **libuv**, so the
  reactor half is in place).
- **GMP bignums present** (`kint` / GMP, [`runtime/kappart.c`](../runtime/kappart.c))
  → `pidigits` and other bignum work look *good*.
- **`Double` present** (`addDouble`/`mulDouble`, the `kp_showDouble` Dragon4
  printer) → the FP benchmarks (n-body, mandelbrot, spectral-norm) are feasible;
  the scalar-`Double` worker keeps the hot loop at the 0-box floor.
- **Concurrency surface present** — `fork`/`forkDaemon`/`forkIn`, `newScope`/
  `shutdownScope`, `atomically`/`newTVar`, `newPromise`/`await`
  ([`src/Kappa/Prelude.hs`](../src/Kappa/Prelude.hs)) → Savina / skynet /
  thread-ring are expressible now.

---

## Tier 1 — Computer Language Benchmarks Game (CLBG) — *do first*

The canonical cross-language micro-benchmark set: ~10 small algorithms, each with
a precise spec + reference output, with existing entries for GHC, OCaml, Go,
Rust, C, Java, etc. — so porting one program instantly yields a multi-language
comparison **including the GHC number** (the Haskell comparison, without fighting
GHC-isms). Self-contained; low effort.

| Program | Measures | Runnable now? | Expected Kappa standing |
|---|---|---|---|
| **binary-trees** | allocate/free many small tree nodes — pure **GC/allocation** | ✅ (hardcode depth) | **Loses until unboxing** — THE boxing-lever tracker |
| **n-body** | tight FP loop, fixed working set | ✅ | OK once the scalar-Double worker engages |
| **spectral-norm** | FP matrix-vector, parallelizable | ✅ | OK; a parallel version exercises fibers |
| **mandelbrot** | FP + bit-packed output | ✅ | OK |
| **fannkuch-redux** | integer + array permutation | ✅ (needs `Array`) | OK |
| **pidigits** | arbitrary-precision integer | ✅ (GMP) | **Strong** — GMP-backed |
| fasta | RNG + bulk stdout | ⚠ output-heavy | OK once output is cheap |
| k-nucleotide | hash tables over stdin DNA | ✗ needs stdin + hash | deferred |
| regex-redux | regex over stdin | ✗ needs regex lib + stdin | deferred |
| reverse-complement | stdin transform | ✗ needs stdin | deferred |

**Headline: `binary-trees`.** It is a pure allocation/GC stress test, so it
quantifies the boxing lever against GHC/OCaml/Go/Rust in one number. Wire it in
next to `make bench` as a standing metric and watch it improve as the unboxing /
Perceus / layout work lands. Do **not** market it; it is an honesty gate.

Start with the self-contained numeric set (**n-body, spectral-norm, mandelbrot,
fannkuch, pidigits**) for immediate cross-language numbers + `binary-trees` as the
tracker.

Reference: <https://benchmarksgame-team.pages.debian.net/benchmarksgame/>

## Tier 1.5 — Are We Fast Yet (AWFY) — *the fair compiler-vs-compiler story*

Marr/Daloze/Mössenböck (DLS '16). Explicitly **designed for fair cross-language
implementation comparison**: every benchmark uses only a common core (objects,
closures, arrays) and forbids language-specific tricks, so it isolates "is your
**compiler/runtime** fast yet?" rather than rewarding library cleverness — the
best-designed suite for a young language positioning against JS/JVM/Truffle.

- **Micro:** Bounce, List, Mandelbrot, NBody, Permute, Queens, Sieve, Storage,
  Towers.
- **Macro:** Richards (OS-kernel sim), DeltaBlue (constraint solver), Havlak
  (loop recognition), Json (parser), CD (collision detection).

Port effort: medium — map objects → records + traits, arrays → `Array`. Worth it
once Tier 1 is established and the basics are fast, because this is the suite a
reviewer trusts for "is the implementation good," and the macro benchmarks
(Richards/DeltaBlue) stress dispatch + allocation the way real code does.

Reference: <https://github.com/smarr/are-we-fast-yet> ·
paper <https://stefan-marr.de/papers/dls-marr-et-al-cross-language-compiler-benchmarking-are-we-fast-yet/>

---

## Tier 2 — Concurrency — *Kappa's differentiator, runnable now*

These exercise the runtime that is the active work, where Kappa is genuinely
strong. The existing `runtime/bench` fork/await-vs-goroutine point is the seed —
extend it into the standard shapes below.

### skynet

Spawn 1,000,000 lightweight tasks as a 10-ary tree of depth 6; each leaf returns
its ordinal, summed back up to `499999500000`. Measures lightweight-task
**spawn + join + scheduler** throughput. Reference numbers exist for Go, Erlang,
.NET, Java/Loom. Direct test of `fork`/`await` at scale; the bench already has the
1-pair version. <https://github.com/atemerev/skynet>

### thread-ring (CLBG) + chameneos-redux (CLBG)

- **thread-ring** — 503 fibers in a ring pass a token N times: pure
  **context-switch / message-passing latency** (Erlang/Go territory).
- **chameneos-redux** — creature rendezvous through a broker:
  message-passing + synchronization under contention.

Both express cleanly over `fork` + a `TVar`/`Promise` mailbox.

### Savina

~30 actor/concurrency benchmarks. Kappa is not actor-model, but the patterns map
directly: a mailbox is a `TVar` queue or `Promise`; **bank-transaction maps onto
STM verbatim**. Most relevant subset:

- *Microbenchmarks:* Ping-Pong, Thread-Ring, Counting, Fork-Join (actor
  creation + throughput), Fibonacci, Big (all-to-all), Chameneos.
- *Concurrency:* **Bank Transaction (STM)**, Dining Philosophers, Sleeping
  Barber, Cigarette Smokers, Concurrent Dictionary, Concurrent Sorted List,
  Producer-Consumer (bounded buffer).
- *Parallelism:* N-Queens, Radix Sort, Trapezoidal integration, Recursive
  matrix-multiply, All-pairs shortest path, Quicksort.

Pick a starter set: Ping-Pong, Fork-Join, Thread-Ring, **Bank-Transaction (STM)**,
Dining Philosophers — they cover spawn, message-passing, STM contention, and
deadlock-free resource arbitration. <https://github.com/shamsimam/savina>

---

## Tier 3 — TechEmpower Framework Benchmarks (TFB) — *the gated flagship*

The famous web-framework throughput benchmark (Round 23: six tests, measured
under massive concurrency on fast NICs). The ultimate showcase for the
**libuv-reactor + M:N fiber** runtime — but gated on library work Kappa does not
have yet.

| Test | Needs | On-ramp? |
|---|---|---|
| **Plaintext** | HTTP/1.1 server + pipelining | ✅ **start here** (HTTP only, reuse libuv) |
| **JSON serialization** | HTTP + JSON encoder | ✅ **start here** (no DB) |
| Single Query | + Postgres/MySQL driver (FFI) | after a DB driver lands |
| Multiple Queries | + driver, N rows | "" |
| Fortunes | + driver + server-side HTML template + XSS escaping + sort | "" |
| Data Updates | + driver, read-modify-write | "" |

**On-ramp plan:** build a minimal HTTP/1.1 server over the **already-linked
libuv** reactor + a JSON encoder, and run **Plaintext + JSON only** (TFB accepts
partial submissions). That alone exercises request routing + serialization + the
fiber scheduler under load — the runtime's home turf — and proves the reactor
end-to-end. A standalone "HTTP hello-world req/s" is a meaningful first datapoint
before even touching TFB's harness. The DB tests follow once a Postgres driver
exists via FFI. Treat the **full six-test, multi-week** effort as aspirational.

Reference: <https://www.techempower.com/benchmarks/> ·
test types
<https://github.com/TechEmpower/FrameworkBenchmarks/wiki/Project-Information-Framework-Tests-Overview>

---

## nofib (Haskell) — *cherry-pick, do not port wholesale*

GHC's own benchmark suite (imaginary / spectral / real). It is **GHC-specific**
(GHC libraries, laziness idioms, GHC-isms), so it does not port cleanly. Its
honest value to Kappa:

- a **source of pure-functional kernels** — mine the *imaginary* / *spectral*
  programs (queens, tak, primes, wheel-sieve, digits-of-e, bernouilli, rfib),
  which overlap CLBG/AWFY anyway;
- the **vs-GHC** comparison — but you get that for free from CLBG (GHC has
  entries there) without the porting pain.

So: cherry-pick a handful of kernels, don't adopt the harness.
Reference: <https://gitlab.haskell.org/ghc/nofib>

## Honorable mentions

- **kostya/benchmarks** & **programming-language-benchmarks** — community
  cross-language suites (binary-trees, nbody, json, mandelbrot, brainfuck, …)
  with lots of reference data and very low port cost; good for quick extra
  comparison points.
- **Classic recursion microbenchmarks** — ackermann, fib, tak — trivial to port,
  useful as call-overhead sanity checks (and they overlap nofib's imaginary set).

---

## Methodology

- **Same machine, same conditions.** Report a median + variance; treat `ns/op`
  as a same-machine reference (≈10–15% hardware/thermal variance) and `bytes/op`
  as exact (the GC byte counter) — mirror the `make bench` table format.
- **Fairness.** Use the idiomatic-but-comparable version of each program (CLBG
  rules); for AWFY honor its no-language-specific-tricks rule. Note GC settings
  (Boehm, worker count) explicitly, as they materially affect allocation
  benchmarks.
- **Fixed inputs.** Until `getArgs`/stdin land, hardcode the size parameter and
  record it; keep it identical across languages.
- **Reference implementations to compare against:** GHC (the Haskell peer),
  OCaml (functional native), Go (concurrency + the existing bench point),
  Rust/C (the floor), Java/JVM (AWFY peer), Erlang/Elixir (concurrency peer for
  thread-ring / skynet).
- **Honesty.** Until unboxing lands, present allocation-bound results
  (binary-trees, ctor-heavy programs) as a *tracked gap with a trend*, not a
  headline.

## Sequencing (recommendation)

1. **Now (cheap, diagnostic):** CLBG numeric subset (n-body, spectral-norm,
   mandelbrot, fannkuch, pidigits) + **binary-trees wired in next to
   `make bench` as the standing boxing-lever gate**. Immediate cross-language
   numbers; doubles as an unboxing-progress metric.
2. **Next (the differentiator):** extend `runtime/bench`'s Go comparison into
   **skynet + thread-ring**, then port ~5 **Savina** benchmarks (Ping-Pong,
   Fork-Join, Thread-Ring, Bank-Transaction/STM, Dining Philosophers).
3. **Later (fair + flagship):** **AWFY** for the compiler-vs-compiler story;
   **TFB Plaintext + JSON** once a minimal libuv HTTP server + JSON encoder land;
   the TFB DB tests after a Postgres FFI driver.

## Track tie-ins

- **Performance track** — `binary-trees` and the numeric set become
  non-regression / progress gates alongside `make bench`; they quantify the
  boxing lever the unboxing/Perceus work targets.
- **Value unboxing track** — `binary-trees` is the external proxy for the
  internal `ctor-build` / boxing benches; track both together.
- **Testing track** — a benchmark with a reference output is also a differential
  fixture (`interp == C == LLVM`), so ports double as correctness oracles.

---

# Results — first cross-language run (2026-06-27)

First end-to-end pass of the [`bench/xlang`](../bench/xlang) harness: 12 ports
populated alongside the `sumloop` sanity bench, each pitted against idiomatic
Go / GHC / C references on one machine in one session. Every number below is
**wall-clock median in milliseconds** with the **ratio vs. the fastest impl in
that row**; a benchmark is only timed **after** its stdout matches `expected.txt`
byte-for-byte (the correctness gate). The harness is auto-discovering
(`make xbench`, or `bench/xlang/run-xbench.sh`); these numbers reproduce with it.

## Methodology (read this before quoting a number)

- **One machine, one session.** Apple M-series, macOS Darwin 25.3.0;
  `go1.26.1`, `GHC 9.14.1` (`-O2`), Apple clang 21 (`cc -O2`, `-lgmp` for
  bignum). Timer is `python3 perf_counter_ns`, best+median over `REPS` runs.
- **Hardcoded `N`.** There is no `getArgs`/stdin yet, so every impl hardcodes
  the same `N` (in a greppable comment). `Int` is 64-bit and auto-promotes to
  GMP on overflow.
- **`REPS`.** Most rows are `REPS=5`. The two pathologically-slow Kappa rows
  (`mandelbrot`, `fannkuch`) are `REPS=1` — a single Kappa run there is minutes,
  and they are progress gates, not headline numbers. `spectralnorm`'s reference
  columns are `REPS=5`; its Kappa column does not run (see below).
- **Idiomatic, not hyper-tuned refs.** The Go/GHC/C references are clean,
  single-threaded, `-O2` implementations of the canonical algorithm — **not** the
  hand-vectorised / multi-threaded CLBG "fastest" entries. Where a comparison is
  not apples-to-apples (GHC strictness-analysis allocation elision in
  `binary-trees`; single-capability non-`-threaded` RTS for the concurrency
  refs), it is flagged inline. The goal is an honest "what does an idiomatic
  program compile to", not a leaderboard win.
- **kappa-llvm is the uniform-boxed backend.** It has no scalar-`Double`/`Int`
  worker and no concurrency/STM lowering yet, so on compute loops it is
  ~2–3 orders slower than kappa-c, and on STM/await benches it does not build.
  This is the documented boxing/concurrency lever surfaced honestly, not a
  regression — read it as a Stage-progress datapoint per the tracks above.

## The table

| benchmark | tier | kappa-c | kappa-llvm | go | hs | c | fastest |
|---|---|---|---|---|---|---|---|
| sumloop | 0 | 25ms 1.21x | 9077ms 428x | 23ms 1.16x | 35ms 1.84x | **20ms 1.00x** | c |
| binarytrees | 1 | 1397ms 29.1x | 3391ms 70.6x | 912ms 19.0x | **48ms 1.00x** | 1174ms 24.5x | hs |
| mandelbrot | 1 | 137335ms 138x | 387747ms 388x | **999ms 1.00x** | 2077ms 2.08x | 1301ms 1.30x | go |
| fannkuch | 1 | 342310ms 194x | ≳20min (slow) | 1847ms 1.04x | 3852ms 2.18x | **1769ms 1.00x** | c |
| pidigits | 1 | 4752ms 32.8x | 5376ms 37.1x | 265ms 1.83x | 182ms 1.26x | **145ms 1.00x** | c |
| nbody | 1 | FAIL — blocked | FAIL — blocked | 218ms 1.22x | 285ms 1.60x | **178ms 1.00x** | c |
| spectralnorm | 1 | builds, intractable | builds, intractable | 1568ms 1.33x | 1237ms 1.05x | **1182ms 1.00x** | c |
| forkjoin | 2 | 664ms 12.5x | builderr | **53ms 1.00x** | 129ms 2.43x | — | go |
| skynet | 2 | 12132ms 35.2x | builderr | **345ms 1.00x** | 2479ms 7.19x | — | go |
| threadring | 2 | 6678ms 94.1x | builderr | 171ms 2.41x | **71ms 1.00x** | — | hs |
| pingpong | 2 | 14691ms 173x | builderr | 276ms 3.25x | **85ms 1.00x** | — | hs |
| bankstm | 2 | 8517ms 90.6x | builderr | **94ms 1.00x** | 191ms 2.03x | — | go |
| philosophers | 2 | 21072ms 251x | builderr | **84ms 1.00x** | 161ms 1.92x | — | go |

`—` = ref not requested for that bench (`refs` line in `meta`). `builderr` =
the LLVM backend cannot compile the port (documented gap, below). `FAIL` = the
port cannot emit the gated output (blocked on a missing prim). `builds,
intractable` = the Kappa port compiles on both backends and is verified correct
at small `N`, but the gated `N` is super-polynomially out of reach on the
current data structures (so it is not timed). `≳20min (slow)` = the `fannkuch`
kappa-llvm column builds and runs correctly (verified at small `N`) but a single
`N=11` run is tens of minutes on the uniform-boxed backend over the list-backed
permutation; it is not separately timed because the row's story is already
pinned by kappa-c (194× C) and by `mandelbrot`'s kappa-llvm/kappa-c ratio
(388×/138×). `mandelbrot` and `fannkuch` are `REPS=1`.

Every buildable column that ran **agreed byte-for-byte** with the reference
output, so each row also doubles as a cross-runtime differential fixture
(`interp == kappa-c == kappa-llvm == go == hs == c`).

## Three headline stories

### 1. Concurrency: the runtime *runs* the hard benches Go/GHC run — kappa-c is single-digit-to-low-hundreds× off, on a single agent

This is the intended strength, and the honest read is mixed-but-real. The
kappart2 M:N runtime **correctly executes** the whole Savina/skynet/thread-ring
family — fork/await, one-shot Promises, STM `TVar` with `retry`-park/unpark,
deadlock-free atomic two-fork pickup — and every one matches Go and GHC
bit-for-bit. On raw throughput kappa-c is **12.5×** the fastest on `forkjoin`
(spawn/join throughput), **35×** on `skynet` (1.1M fibers), and **90–250×** on
the STM-contention benches (`bankstm`, `philosophers`) and per-hop
message-passing (`threadring` 94×, `pingpong` 173×). The STM/message rows are
dominated by per-operation fiber park/unpark and per-rendezvous Promise
allocation on a **single runtime agent** — i.e. the same boxing/allocation lever,
not a concurrency-model defect. `make bench` already isolates the floor here
(`fork/await ≈ 3.5× a goroutine`); these end-to-end numbers are higher because
they fold in allocation + STM commit cost. **Lead with "it runs the suite and is
correct", track the multiplier as the allocation lever closes.** Note GHC wins
`threadring`/`pingpong` outright (lightweight `MVar` handoff) while Go wins the
fork-heavy and contention rows.

### 2. binary-trees: the boxing trend, recorded to track

`binary-trees` is the pure allocation/GC stress test and **the** standing
boxing-lever gate. Today every `Tree` node is a boxed heap constructor with no
Perceus reuse, so:

> **kappa-c = 1397 ms ≈ 1.19× C (1174 ms), ≈ 1.53× Go (912 ms); kappa-llvm =
> 3391 ms ≈ 2.43× kappa-c.**

Record these. `kappa-c ≈ 1.2× C` on the same allocation shape is the meaningful
datapoint to watch collapse toward 1.0× (or below) as value-unboxing + RC-reuse
land; `kappa-llvm/kappa-c ≈ 2.4×` is the uniform-boxed-backend gap to watch
collapse as the scalar worker lands. **Caveat:** GHC is fastest here (48 ms) but
largely by *allocation elision* — the idiomatic lazy formulation lets
strictness analysis fuse away most per-node allocation, so it is not an
alloc-throughput peer. **C vs Go vs kappa-c is the clean same-allocation
comparison.**

### 3. Numerics + GMP: pidigits is the strong-vs-GHC story; the FP loop is the lever

- **pidigits (GMP bignum spigot)** is where Kappa's auto-promoting
  arbitrary-precision `Int` shows up well: kappa-c **4752 ms** and kappa-llvm
  **5376 ms** are nearly tied (~33–37× the GMP C ref), because the work is
  dominated by GMP arithmetic routed through the runtime — **not** the
  uniform-boxing loop lever that blows kappa-llvm out on `sumloop`/`mandelbrot`.
  So this is an honest "GMP-Integer representation" datapoint: correct, and the
  C/LLVM backends agree, with the ~35× gap being per-op bignum
  allocation/boxing vs. the refs' in-place `mpz_t` mutation. GHC (Integer=GMP,
  182 ms) and Go (`math/big`, 265 ms) both beat C-via-GMP's 145 ms only modestly;
  Kappa trails the field but is correct to all 5000 digits on both backends.
- **The compute-FP loop is the scalar-Double lever, surfaced honestly.**
  `sumloop` (int loop) and `mandelbrot` (Double + bit-packing) show the boxing
  cost rawest: kappa-c is **1.2×** C on `sumloop` (the int worker fires) but
  **138×** on `mandelbrot` (the scalar-Double worker does **not** fire on the
  recursive monomorphic Double helper — confirmed in the emitted C: boxed
  `KValue*` params + boxed `kp_mulDouble`/`kp_addDouble`, zero `kwd_` unboxed
  workers). kappa-llvm is **428×** (`sumloop`) / **388×** (`mandelbrot`) — the
  uniform-boxed backend. All four impls are bit-identical (explicit
  non-FMA temporaries in every language). Read `mandelbrot`/`sumloop` as the
  unboxing progress gate, not a headline.

## Blocked on a compiler/language gap (roadmap)

Concrete, prioritised items each of which currently blocks or kneecaps a port.
The first three are **hard blockers** (no in-language workaround); the rest cap
performance or the LLVM column.

1. **`sqrt` (and the FP transcendental set) is missing.** The entire `Double`
   prim set is add/sub/mul/div/neg/eq/lt/`intToDouble`/`showDouble`/
   `ratOfDouble` ([`src/Kappa/Prelude.hs`](../src/Kappa/Prelude.hs) ~L287–462) —
   no `sqrt`/`pow`/`rsqrt`/transcendentals. A pure-Kappa Newton sqrt is not
   IEEE-754 correctly-rounded, so it diverges in the low ULPs and fails any
   byte-exact `%.9f` gate. **Blocks `nbody` and `spectralnorm` outright.**
2. **No fixed-precision `Double` formatting.** `showDouble` (behind
   `println @Double`) emits only the *shortest round-trip* decimal, and there is
   no `%.9f` prim nor any `doubleToInt`/`floor`/`trunc`/`round` to hand-roll a
   9-decimal formatter. So even with `sqrt`, the gated `-0.169075164` /
   `1.274224153` forms are unprintable. **Co-blocks `nbody`, `spectralnorm`.**
3. **No mutable / O(1) random-access array.** `Array a` is a `newtype` over a
   cons `List`; `__arrayIndexUnsafe` is an O(n) walk and there is no in-place
   update/swap (`runtime/prims.c`). This makes the archetypal in-place
   array benches super-linear: `fannkuch` becomes O(n) per "array write"
   (~200× the mutable-array refs), `spectralnorm`'s power method is O(n³) and
   **intractable at N=5500** (extrapolates to hours — not timed), and `bankstm`'s
   K=1000 accounts are walked O(K) per transfer so its wall-clock is
   list-traversal-bound, **not** STM-throughput-bound. **An unboxed mutable
   array primitive is the single highest-leverage missing data structure.**
4. **LLVM backend lacks concurrency/STM lowering.** `await`/`__awaitFiber`/
   `__reraiseCause` and the STM surface (`newTVar`/`readTVar`/`writeTVar`/
   `atomically`/`retry`) are recognised by the LLVM backend only as node-builders
   inside a `do`-block, never as curried/partially-applied values
   ([`src/Kappa/Backend/LLVM.hs`](../src/Kappa/Backend/LLVM.hs) ~L564–582), so
   any helper (`recv`, `makeBoxes`, `pong`, `spawnAll`) using them fails
   `E_BACKEND_UNSUPPORTED`. **`builderr` on all six Tier-2 benches** under
   `KAPPA_BACKEND=llvm`; the C backend runs them all.
5. **Scalar-`Double` (and ctor) unboxing worker.** The boxing lever behind the
   138× `mandelbrot` / 1.2× `binary-trees` / 35× `pidigits` gaps. Stage 1.5
   witness + scalar worker (per `stage2-layout-staging` /
   `representation-is-llvm-layout`) is the headline-collapsing item; until it
   lands, present the compute/alloc rows as a tracked trend.
6. **C-backend CPS gaps (worked around, worth fixing).** (a) A *suspending* op
   (`join`/`await`) inside a `for x in xs do …` loop is not yet CPS-lowered
   (`skynet` had to collect via a recursive helper). (b) An IO/STM `do`-block
   that tail-calls itself across an `atomically` bind is not flat-trampolined and
   overflows the fiber stack (~7000 rounds, SIGBUS) — `philosophers` had to use a
   `var`+`while` loop. (c) A `var g : Double` cell in a non-`main` Double-returning
   helper miscompiles (`kas_dbl: not a Double`) on both backends — isolated by
   the `nbody` port; forces inlining FP helpers into `main`.

## Reproduce

```sh
cd bench/xlang
make xbench                              # all rows, REPS=5
REPS=1 ./run-xbench.sh mandelbrot fannkuch   # the slow compute rows
# spectralnorm: the Kappa port builds on both backends and is verified correct
# at small N, but the gated N=5500 is intractable on list-backed arrays, so run
# its references only and report the Kappa column as blocked.
```

On Apple Silicon the C `pidigits` ref needs GMP on the include/lib path:
`CPATH=/opt/homebrew/include LIBRARY_PATH=/opt/homebrew/lib make xbench`.
The runner exits non-zero whenever any column FAILs the gate or fails to build
(the Tier-2 `kappa-llvm` `builderr`s and the `nbody`/`spectralnorm` blocks make
the full-suite exit non-zero by design — that is the CI signal for the gaps
above, not a harness failure).
