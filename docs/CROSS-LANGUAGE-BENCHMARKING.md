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
