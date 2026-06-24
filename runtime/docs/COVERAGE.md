# Combinator coverage — matching ZIO's bar

Goal: as rich and as well-tested a concurrency surface as ZIO, **especially
cancellation**. This file maps ZIO's (and Cats-Effect's) tested combinators onto
kappart2 and tracks the path to parity. It is derived from a study of ZIO's
`ZIOSpec`/`FiberSpec`/`PromiseSpec`/`ScopeSpec`/`CauseSpec`/`ZSTMSpec` and CE's
`IOSpec`/`ResourceSpec` (cloned under `~/ws/refs/`): **99 combinators, 422
distinct asserted behaviors**, by category:

| category | # | what it stresses |
|----------|---|------------------|
| error-classification | 65 | fail vs interrupt vs defect, and their composition (`Both`/`Then`) |
| interruption | 62 | who/what gets interrupted, and when delivery happens |
| edge-case | 62 | ties, zero/negative durations, already-done, re-entry |
| happy-path | 58 | the obvious behavior |
| composition | 49 | combinators nesting correctly |
| masking | 46 | uninterruptible/restore/mask boundaries |
| concurrency-race | 43 | lost-wakeups, simultaneity, ordering under parallelism |
| finalizer-ordering | 30 | LIFO, run-once, run-on-every-exit |
| tie-break | 7 | left-wins / io-wins on a true tie |

## The thesis (why this is tractable)

ZIO's enormous surface is **a small set of runtime primitives + a large derived
library + an exhaustive behavior suite.** kappart2 follows the same shape: the C
runtime provides the irreducible primitives (those that touch the scheduler,
interruption, or the continuation); everything else is a pure Kappa/builder
composition. So "as rich as ZIO" = finish the primitive set, then derive.

## Primitive set — status

**Have, with tests (the cancellation core is here):**

| primitive | kappart2 | test |
|-----------|----------|------|
| `fork` / `forkDaemon` | `krt2_fork` / `krt2_fork_daemon` | spine, parallel |
| `await` / `join` | `krt2_await` (+ `tryExit` peek) | spine |
| `interrupt` / `interruptFork` / `interruptAs` | `krt2_interrupt*` | scopes, cancel |
| `cede`, `sleepFor` | `krt2_cede`, `krt2_sleep_for` | spine |
| `race`, `timeout` | `krt2_race`, `krt2_timeout` | race |
| **`uninterruptible` / `poll`** | `krt2_uninterruptible`, `krt2_poll` | cancel |
| **`mask` + `restore`** (uninterruptibleMask) | `krt2_mask` | cancel |
| **`acquireRelease`** (bracket) | `krt2_acquire_release` (= `mask`+`finally`+`bind`) | cancel |
| **`ensuring` / `finally`** | `krt2_ensuring` / `krt2_finally` | cancel, completion |
| `defer` / do-scope finalizers | `krt2_defer` / `krt2_doscope` | completion |
| `return` / `break` / `continue` / `while` | `krt2_return`/`break`/`continue`/`while` | completion |
| promises | `krt2_new_promise`/`await`/`complete` | spine, race |
| scopes + monitors | `krt2_new_scope`/`forkIn`/`shutdown_scope`/`monitor` | scopes |
| refs | `krt2_new_ref`/`read`/`write` | completion |
| `now`, `fiberId` | `krt2_now_monotonic`, `krt2_fiber_id` | — |

The cancellation story already matches ZIO's hard cases (verified by `test/cancel.c`
and the deadlock it caught): **interrupt waits for the target's finalizers;
`acquireRelease`'s release always runs even when `use` is interrupted; a `restore`d
region is interruptible inside an otherwise-uninterruptible `mask`; finalizers run
masked.** (REVIEW.md: the deliver-interrupt-then-run-finalizers fix.)

**Missing primitives to add (small, scheduler-touching):**

- `onInterrupt` / `onExit` — a finalizer that receives the exit *reason* (run
  only on interrupt / on every exit with the `Exit`). Needs the do-scope finalizer
  to carry the `Reason` to its action — a small extension of `KK_FINSEQ`.
- `disconnect` — detach a fiber's interruption so `interrupt` returns immediately
  while finalization proceeds in the background (forkDaemon + a detached interrupt).
- `Promise.poll` / `isDone` — non-blocking peek (we have `tryExit` for fibers; add
  the promise analog).
- `Fiber.status` / `interruptAll` / `awaitAll` — diagnostics + batch (over the
  primitives + `krt2_dump`).
- ~~**STM**~~ — **DONE** (`native/stm.c`): `atomically`/`TVar`/`readTVar`/`writeTVar`/
  `retry`/`check`/`orElse`, GHC-style optimistic, serializable under real
  parallelism. Adversarially reviewed; two bugs found+fixed (orElse in-place-write
  isolation; stale-retry-watcher spurious wakeups). Tests: `stm` (serializability),
  `stm_retry` (retry+orElse), `stm_orelse` (the isolation regression guard).
- `FiberRef.modify` + true fork-inheritance/independence under concurrency — we
  have get/set/locally; modify and the copy-on-fork snapshot need wiring.

## Derivable as a Kappa library (no new runtime primitive)

These are ZIO-rich-surface combinators that compose from the primitives above —
exactly how ZIO/CE implement them, and how `race`/`timeout`/`acquireRelease`
already work here:

- `raceWith`, `raceFirst`, `raceAll`, `firstSuccessOf` — over `race`.
- `zipPar` / `zipParLeft/Right`, `both`, `parTupled` — `fork` a + `fork` b + await
  both, interrupt-the-other-on-failure.
- `foreachPar` / `collectAllPar` / `*ParN` — fan-out `fork` + fan-in `await` (the
  `parallel` test already does the unbounded form).
- `racePair` / `raceOutcome` — `race` returning the loser's fiber.
- `timeoutTo`, `timeoutFail` — over `timeout`.
- `Cause` projections (`failures`/`defects`/`interruptors`/`isDie`/`stripFailures`/
  `prettyPrint`/`filter`/`keepDefects`/…) — pure folds over the `Cause` tree
  (`Fail`/`Interrupt`/`Defect`/`Both`/`Then`).
- `std.supervisor` (OTP one/all/rest-for-one + restart intensity) — over
  `forkIn`/`interrupt`/`await`/`monitor`/`now` (DESIGN.md §9.3; RESEARCH.md §3).
- `Memoize`, semaphores, queues, hubs — over promises + STM.

## The test-coverage plan

ZIO asserts ~422 behaviors; kappart2 has **6 harnesses** today covering the
happy-path + the hardest interruption/finalizer/tie-break cases for the primitives
that exist. To reach ZIO's bar:

1. **Per-primitive behavior tests** mirroring the matrix categories — for each
   primitive, assert: happy-path, interruption-during-it, finalizer-ordering,
   masking interaction, error-classification, and the documented edge cases. The
   matrix in this study is the checklist (the `~422` scenarios are the test bodies).
2. **A property/fuzz layer** for the concurrency-race (43) and tie-break (7)
   categories: run under `KAPPA_RT_WORKERS=N` and under TSan, asserting
   order-insensitive invariants (REVIEW.md M13).
3. **Once the v2 codegen lands**, port ZIO's specs as Kappa `.kp` conformance
   tests run on the native runtime — the genuine apples-to-apples coverage bar.

The raw study (every combinator × every asserted behavior) is archived at
`tasks/wck7xb06f.output`; this file is the actionable distillation.
