# `kappa-runtime` — a real concurrency runtime for Kappa native

`kappart2` is a from-scratch native runtime that implements Kappa's Spec §18 and
§32 concurrency model — **M:N work-stealing fibers, structured-concurrency
supervision, a libuv async-I/O reactor, parallel STM, atomics, interruption and
masking, and algebraic-effect handlers** — as a layer over the existing boxed
`KValue` runtime (`runtime/kappart.c`).

It is built to advertise the **full** Spec §27.6 capability set, not a subset:

| Capability             | What it gives you                                       |
|------------------------|---------------------------------------------------------|
| `rt-core`              | fibers, scheduler, timers, promises, scopes, STM        |
| `rt-parallel`          | runnable fibers on multiple cores at once               |
| `rt-shared-stm`        | TVars valid across parallel workers                     |
| `rt-blocking`          | the `blocking` combinator + blocking-FFI offload lane   |
| `rt-atomics`           | `std.atomic` with C11 memory orders                     |
| `rt-multishot-effects` | persistent multi-shot effect resumptions                |

> This is **not** a toy. The architecture is drawn from Go (P/M work-stealing),
> GHC's RTS (HECs, parallel STM, heap-reified continuations), Erlang/BEAM
> (reductions, supervision trees, dirty schedulers), Rust/Tokio (reactor/executor
> split, wakers, `spawn_blocking`), the JVM/CLR (safepoints, structured
> concurrency), and libuv/Node (the event loop as reactor). See
> [`DESIGN.md`](DESIGN.md) for the full architecture and the spec-obligation →
> implementation map.

## Why it exists

The bundled `runtime/kappart.c` is a single-threaded recursive IO trampoline with
no scheduler, no fibers, and no async I/O. The reference semantics in
`src/Kappa/Interp.hs` get all of this *for free* from GHC's RTS (a Kappa fiber is
a GHC green thread). The native backend cannot lean on GHC — so this package is
the native equivalent of the GHC RTS, built on libuv + Boehm GC.

## Architecture at a glance

```
            ┌──────────────────────── Rt (one per program) ───────────────────────┐
            │                                                                      │
  worker 0  │  [Chase–Lev deque]  ──steal──►  worker 1  [deque]  ◄──steal──  ...   │   N = #cores
  (OS thr)  │      │  step fibers (CK-machine, stackless)  │                       │   run fibers in PARALLEL
            │      ▼                                        ▼                       │
            │   ┌─────────────────── global injection queue ──────────────────┐    │
            │   └──────────────────────────▲───────────────────────────────────┘   │
            │                               │ wake (Waker)                          │
            │   ┌─── reactor thread ────────┴──────┐    ┌─── blocking lane ───┐     │
            │   │ one libuv loop: timers, TCP/FS,   │    │ libuv threadpool:   │     │
            │   │ uv_async wakeups, I/O completion  │    │ `blocking` + FFI    │     │
            │   └──────────────────────────────────┘    └─────────────────────┘     │
            └──────────────────────────────────────────────────────────────────────┘
                         all threads under Boehm GC (thread/parallel mode)
```

A **fiber** is a heap-reified continuation (a CK-machine over `KValue`), so it is
a relocatable GC pointer — work-stealing is trivial and the GC traces a parked
fiber without scanning any C stack. Blocking on I/O / a promise / a timer / STM
retry / `cede` *suspends* the fiber and lets the worker run something else;
a libuv callback or another fiber wakes it later, possibly on a different core.

## Status

The architecture was hardened by an 8-lens adversarial review before any code
was written — see [`REVIEW.md`](REVIEW.md) (verdict: *proceed; the design is the
right one*).

**Working now (`make test` green, all stress-looped clean):**

- *Spine* — the M:N work-stealing scheduler over a worker-per-core pool, the
  stackless CK-machine IO driver, `fork`/`await`/`cede`, one-shot promises
  (new/await/complete with cross-fiber wakeup), the libuv reactor thread driving
  `sleepFor` timers, typed failure + `catchIO`, the idempotent CAS park/wake
  handshake, and the explicit GC root set that keeps parked fibers live.
- *Structured concurrency* — supervision scopes (`newScope`/`forkIn`/
  `shutdownScope` with the §32.2.3 ordering: interrupt children → await their
  termination → drain), `monitor`/`awaitMonitor`, **interruption** (`interrupt`/
  `interruptFork` with structured `InterruptCause` tags, delivered only at
  interruption points), and **masking** (`uninterruptible`/`poll`).
- *Do-kernel completion channel* — `defer`/`finally` that run on **every** exit
  path (normal, typed fail, early `return`, loop `break`/`continue`, interruption)
  in LIFO order, as **heap-reified, suspendable** finalizers (`KK_DOSCOPE`/
  `KK_FINSEQ`) that survive a cross-worker resume; early `return`; `while` loops
  with `break`/`continue` (`KK_LOOP`); and mutable refs.
- *`race` / `timeout`* — first-wins with the mandated tie-break (left/io wins),
  loser interrupted **and awaited** before returning ([`race.c`](native/race.c),
  composed from the primitives as the reference `Interp.hs` does).
- *Cancellation surface (ZIO-grade)* — `uninterruptible`/`poll`, **`mask` + `restore`**
  (uninterruptibleMask: a restored region is interruptible inside an otherwise
  masked one), **`acquireRelease`** (bracket: acquire uninterruptible, use
  interruptible, release **always** runs even on interrupt), and `ensuring`.
- *Parallel STM* (`rt-shared-stm`) — GHC-style optimistic transactions
  ([`native/stm.c`](native/stm.c)): `atomically`/`TVar`/`readTVar`/`writeTVar`/
  `retry`/`check`/`orElse`, with lock-free versioned reads, commit-lock
  validation, and `retry` parking on watcher lists. Verified **serializable under
  real parallelism** — 16 fibers × 200 transfers contending on 2 TVars across 12
  cores conserve their total (60× clean).

Nine harnesses: [`spine`](test/spine.c) (fork+promise+sleep+throw/catch, byte-exact),
[`parallel`](test/parallel.c) (200 fibers across 12 cores), [`scopes`](test/scopes.c)
(a scope cancels a child parked on a 30-second sleep and drains in **1 ms**),
[`completion`](test/completion.c) (defer/return/while/break+continue),
[`race`](test/race.c) (race+timeout, loser cancelled), [`cancel`](test/cancel.c)
(`acquireRelease` release-on-interrupt + `mask`/`restore`), [`stm`](test/stm.c)
(parallel serializability), [`stm_retry`](test/stm_retry.c) (retry parks+wakes,
orElse), and [`stm_orelse`](test/stm_orelse.c) (orElse write-isolation). All
stress-looped clean.

The FFI + dynamic/static-linking + deployment plan for wiring this runtime into a
native Kappa binary (link modes, `$ORIGIN`/`@rpath`, the §36 load modes, the
threaded-libgc + blocking-lane discipline) is in [`DEPLOYMENT.md`](DEPLOYMENT.md).

The combinator surface is benchmarked against ZIO's + Cats-Effect's test suites
(cloned for study) — see [`COVERAGE.md`](COVERAGE.md): 54 of ZIO's primitives are
covered, the rest are derivable library compositions or the staged STM subsystem.
The `cancel` test caught a real deadlock (a fiber dropped mid-finalizer-unwind on
interrupt) — exactly the class ZIO's suite targets.

**Next increments (well-specified by [`DESIGN.md`](DESIGN.md) + `REVIEW.md`):**
every-do-block-is-a-scope wiring; `race`/`timeout` with the reactor-resolved
tie-break (REVIEW.md B6); parallel STM (§11); atomics (§10); the `rt-blocking`
offload lane (§7.4); and the v2 backend integration ([`INTEGRATION.md`](INTEGRATION.md)).
The prior-art that grounds all of this — and the cited v3 performance path
(C11 Chase–Lev work-stealing, evidence-passing multishot effects, a bespoke
Perceus-style GC) — is in [`RESEARCH.md`](RESEARCH.md).

**v2 — backend integration** ([`INTEGRATION.md`](INTEGRATION.md)): wire
`Kappa.Backend.C` so `fork`/`await`/… compile to `krt2_*` calls (the do-kernel
CPS rewrite — tractable because the backend already threads an explicit de Bruijn
`KEnv`, REVIEW.md B1), link `libkappart2.a` in the Driver, run the native
conformance suite, and flip `Capabilities.hs` to advertise the runtime's
capability set (§17). `rt-multishot-effects` is staged here behind its
escape-check gate.

**v3 — performance:** per-worker libuv loops, a generational nursery GC,
Chase–Lev work-stealing deques, and Go-1.14-style async preemption.

## Build

Standalone (no Kappa compiler needed — builds the runtime lib + C demos):

```sh
make            # builds libkappart2.a and the test harnesses
make test       # runs the C harness conformance demos
```

Requires `libuv` (`pkg-config --exists libuv`), Boehm GC (`-lgc`), and GMP
(`-lgmp`) — the same dependency set as the existing native examples plus libuv.

Via the Kappa build system (once backend integration lands):

```sh
kappa build --manifest examples/packages/kappa-runtime --target rt-demos
```

The [`kappa.build.kp`](kappa.build.kp) manifest declares libuv via `pkgConfig`
and the runtime C sources as a native binding shim.

## Layout

See [`DESIGN.md`](DESIGN.md) §20 for the full file map. In short:
`include/kappart2.h` is the public C ABI, `native/` holds the runtime C sources,
`src/rt/` the Kappa surface facade + `rt.supervisor`, and `test/` the harnesses.
