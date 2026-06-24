# Missing-primitives analysis — the kappart2 native runtime

A decision document mapping the spec's concurrency surface (Spec §18.1, §28, §29)
and the ZIO/Cats-Effect coverage matrix (99 combinators / 422 behaviors, see
[`COVERAGE.md`](COVERAGE.md)) onto the runtime's public ABI ([`../kappart2.h`](../kappart2.h)),
and deciding **ADD / DERIVE / SKIP** for every gap. The authoritative reference
set is the reference interpreter (`src/Kappa/Interp.hs`, `runPrimIO'`), which the
native runtime must eventually match.

**Headline:** the cancellation core is already complete and matches ZIO's hard
cases. The real gaps are: (1) **`std.atomic` is declared in the header but has no
implementation** — there is no `atomic.c` and no `krt2_atomic_*` definition, and
the header itself flags `rt-atomics` as "NOT yet built"; (2) a handful of small
scheduler/continuation-touching primitives (`onInterrupt`/`onExit`, `disconnect`,
`Promise.poll`/`isDone`, `FiberRef.modify` + copy-on-fork); everything else is a
derivable library.

> Status note (single-agent STM): the native backend now lowers
> `newTVar`/`readTVar`/`writeTVar`/`atomically` to single-agent cell semantics
> (matching the reference interpreter) via the IO do-kernel — see `kpf_io_*TVar`
> in [`../kappart.c`](../kappart.c). The journaled multi-fiber STM in
> [`../stm.c`](../stm.c) becomes reachable from `.kp` once the do-kernel is
> CPS-lowered (see [`INTEGRATION.md`](INTEGRATION.md)).

---

## Already implemented

These `krt2_*` entry points cover the corresponding spec §18.1 / §28 `expect
term`s and the ZIO/CE primitive core:

| Spec surface | runtime |
|---|---|
| `fork` / `forkDaemon` / `forkIn` (§18.1.4, §18.1.8) | `krt2_fork` / `krt2_fork_daemon` / `krt2_fork_in` |
| `await` / `join` (§18.1.4) | `krt2_await` / `krt2_join` |
| `interrupt` / `interruptFork` / `interruptAs` / `interruptForkAs` (§18.1.4) | `krt2_interrupt` / `krt2_interrupt_fork` / `krt2_interrupt_as` / `krt2_interrupt_fork_as` |
| `cede` (§18.1.5) | `krt2_cede` (+ `krt2_safepoint` for loop back-edges) |
| `nowMonotonic` / `sleepFor` / `sleepUntil` / `timeout` / `race` (§18.1.6) | `krt2_now_monotonic` / `krt2_sleep_for` / `krt2_sleep_until` / `krt2_timeout` / `krt2_race` |
| `newFiberRef` / `getFiberRef` / `setFiberRef` / `locallyFiberRef` (§18.1.7) | `krt2_new_fiber_ref` / `get` / `set` / `locally` (**partial — ADD #4**) |
| `newScope` / `withScope` / `forkIn` / `shutdownScope` / `monitor` / `awaitMonitor` / `demonitor` (§18.1.8) | `krt2_new_scope` / `with_scope` / `fork_in` / `shutdown_scope` / `monitor` / `await_monitor` / `demonitor` |
| `newPromise` / `awaitPromiseExit` / `awaitPromise` / `completePromise` (§18.1.9) | `krt2_new_promise` / `await_promise_exit` / `await_promise` / `complete_promise` (**poll/isDone missing — ADD #3**) |
| `fiberId` / `currentFiberId` / `getFiberLabel` / `setFiberLabel` / `locallyFiberLabel` (§18.1.10) | `krt2_fiber_id` / `current_fiber_id` / `get_fiber_label` / `set_fiber_label` / `locally_fiber_label` |
| `blocking` (§18.1.11) | `krt2_blocking` |
| `poll` / `uninterruptible` / `mask`+restore / `ensuring` / `acquireRelease` (§18.1.12) | `krt2_poll` / `uninterruptible` / `mask` / `ensuring` / `acquire_release` |
| `sandbox` / `unsandbox` (§18.1.2) | `krt2_sandbox` / `krt2_unsandbox` |
| STM: `newTVar` / `readTVar` / `writeTVar` / `retry` / `check` / `atomically` / `orElse` + `stm_pure`/`stm_bind` (§18.1.13) | `krt2_new_tvar` / `read_tvar` / `write_tvar` / `retry` / `check` / `atomically` / `or_else` — implemented in `stm.c`, adversarially reviewed |
| do-kernel: `defer` / `return` / `break` / `continue` / `while` + do-scope finalizers (§18.7/§18.8) | `krt2_defer` / `return` / `break` / `continue` / `while` / `doscope` |
| MonadRef: `newRef` / `readRef` / `writeRef` (§18.6.1) | `krt2_new_ref` / `read_ref` / `write_ref` |
| IO kernel + Exit/Cause construction (§28) | `krt2_pure`/`bind`/`then`/`catch`/`finally`/`throw`; `krt2_success`/`failure`/`cause_fail`/`cause_interrupt`/`cause_defect`/`cause_both`/`cause_then`/`interrupt_cause` |

The cancellation contract is verified by `tests/cancel.c`: interrupt waits for the
target's finalizers; `acquireRelease`'s release runs even when `use` is
interrupted; a `restore`d region is interruptible inside a `mask`; finalizers run
masked. The deliver-interrupt-then-run-finalizers fix is the key correctness
result.

---

## Missing — should ADD as a runtime primitive

These genuinely need scheduler / interruption / continuation access and cannot be
a pure Kappa library.

### 1. `std.atomic` — the entire atomics module (§29.1, `rt-atomics`) — HIGHEST PRIORITY
- **Spec ref:** §29.1; capability gate §27.6 (`rt-atomics`, listed in `KRT2_CAPABILITIES`).
- **Status:** the ABI is declared in `kappart2.h` (`krt2_new_atomic_ref`,
  `krt2_atomic_load/store/exchange/compare_exchange/fetch_add/sub/and/or/xor`) but
  **there is no implementation** — no `atomic.c`, zero `krt2_atomic_*` definitions.
  The header comment itself says "rt-atomics — NOT yet built." This is a
  *declared-but-empty* ABI: the capability flag is advertised while the code is absent.
- **Why a primitive:** `AtomicRef` is a distinct cell kind (§29.1: "not an ordinary
  `var`, `Ref`, `TVar`, or `MonadRef`"), and the operations must lower to C11
  `atomic_*` with the exact `LoadOrder`/`StoreOrder`/`RmwOrder`/`CasFailureOrder`
  memory-order mapping and the cross-fiber happens-before contract. No pure Kappa
  expression can produce a `memory_order_acquire` load.
- **Approach:** add `atomic.c`: `AtomicRef` as a `K_FGN` box wrapping a C11
  `_Atomic` word; map the boxed order constructors to `memory_order_*`;
  `compare_exchange` returns the `CompareExchangeResult` (`Exchanged old` /
  `NotExchanged current`) ADT; fetch-ops return the old value. Provide
  `AtomicValue` instances for `Bool` + fixed/pointer-width ints. **Only flip the
  `rt-atomics` capability flag to "real" once this lands** (§28.305).

### 2. `onInterrupt` / `onExit` (interruption finalizers that receive the exit reason)
- **Ref:** ZIO `onExit` / `onInterrupt`; composes the §18.1.12 finalizer model.
- **Why a primitive (extension, not new entity):** unlike `ensuring`/`finally`, the
  finalizer must *receive the terminal `Exit`/`Reason`* (run-only-on-interrupt, or
  run-on-every-exit-with-the-cause). Ordinary `defer`/`ensuring` finalizers run
  with no argument.
- **Approach:** a small extension of the existing `KK_FINSEQ` continuation frame.
  The `FinSeq` struct in `rt.c` **already carries the saved Reason**
  (`rkind`, `rval`, `rlabel`) — add a finalizer variant that applies the registered
  handler to the reconstructed `Exit`/`InterruptCause` before resuming.
  `onInterrupt` = the same, guarded to fire only when `rkind` is the interrupt tag.

### 3. `Promise.poll` / `Promise.isDone` (non-blocking peek)
- **Ref:** ZIO PromiseSpec `poll`/`isDone`; CE `Deferred.tryGet`. (`krt2_poll` is the
  *fiber* interruption checkpoint — a different thing.)
- **Why a primitive:** must atomically read the promise cell's state without
  parking — it touches runtime-owned promise state. Cannot be expressed over
  `await_promise` (which blocks).
- **Approach:** `krt2_poll_promise(p) -> UIO (Option (Exit e a))` and
  `krt2_is_done_promise(p) -> UIO Bool` reading the existing cell non-blockingly.

### 4. `FiberRef.modify` + copy-on-fork inheritance
- **Spec ref:** §18.1.7 ("the child inherits a snapshot copy of the parent's
  currently visible `FiberRef` values; after fork, parent and child updates are
  independent").
- **Status:** `get`/`set`/`locally` exist; `modify` and the copy-on-fork snapshot
  are **not wired**.
- **Why a primitive:** the per-fiber FiberRef map lives in runtime fiber state;
  `modify` must be an atomic get-apply-set against it, and the fork-time snapshot
  copy must happen inside `krt2_fork`/`fork_daemon`/`fork_in` at fiber creation.
- **Approach:** `krt2_modify_fiber_ref(ref, f)`; and in the fork builders,
  deep-copy the parent's FiberRef map into the child at spawn. The §18.1.7
  parent/child-independence contract is the test oracle. **This is a semantic
  conformance gap, not just convenience.**

### 5. `disconnect` (detach interruption)
- **Ref:** ZIO `disconnect` (heavily exercised by disconnect/timeout-disconnect tests).
- **Why a primitive:** changes who-waits-for-whom — `interrupt` on a disconnected
  fiber must *return immediately* while finalization continues in the background
  (vs. the default "wait for finalizers"). A scheduler-level reparenting of the
  interrupt-completion edge.
- **Approach:** "disconnect = forkDaemon + a detached interrupt." **Lower
  confidence on 'pure library'** — first verify whether forkDaemon's existing
  detach is sufficient; if so this drops to DERIVE.

### 6. `interruptAll` / `awaitAll` (batch over a fiber set) — borderline
- `interruptAll` over an explicit *scope* is already `krt2_shutdown_scope`.
  Over an arbitrary user-held list of `Fiber` handles it is a fold over
  `krt2_interrupt`/`krt2_await` — **DERIVE first**; promote to a primitive only if
  the fold loses required atomicity (the "interrupters are accretive" tests).

---

## Missing — DERIVE as a Kappa library

All compose from existing primitives, exactly as ZIO/CE implement them and as
`race`/`timeout`/`acquireRelease` already work here. No new runtime primitive.

| Combinator | One-line derivation (over existing `krt2_*`) |
|---|---|
| `raceWith` / `raceFirst` / `raceAll` / `firstSuccessOf` | fold over `krt2_race`; `firstSuccessOf` keeps the first `Success`. |
| `zipPar` / `zipParLeft (<&)` / `zipParRight (&>)` / `both` | `fork` a + `fork` b + `await` both; on either failure `interrupt` the other; project the side(s). |
| `foreachPar` / `foreachParDiscard` / `foreachParN` / `collectAllPar*` | fan-out `krt2_fork` (in a `with_scope`) + fan-in `krt2_await`; `*ParN` adds a TVar/semaphore permit gate. |
| `racePair` / `raceOutcome` | `race` but return the loser's `Fiber` handle instead of interrupting it. |
| `timeoutTo` / `timeoutFail` / `timeoutAndForget` | over `krt2_timeout` (or `race` vs `sleep_for`) folding the `Option`/`Exit`. |
| `Cause` projections — `failures`/`defects`/`interruptors`/`isDie`/`isInterrupted`/`stripFailures`/`prettyPrint` | **pure folds** over the `Cause` tree (`Fail`/`Interrupt`/`Defect`/`Both`/`Then`) — pure Kappa, no runtime access. |
| `TRef.update`/`getAndUpdate`/`updateAndGet`/`modify`/`summarized` | `readTVar` + `writeTVar` inside one `STM` bind. |
| STM composition: `zip`/`zipWith`/`flatMap`/`collectAll`/`foreach`/`mergeAll`/`validate` | monadic bind/`stm_pure` over `STM` (§18.1.13). |
| `std.supervisor` (OneForOne/OneForAll/RestForOne + `RestartIntensity`) (§29.2) | library over `forkIn`/`interrupt`/`await`/`monitor`/`now` + a restart loop; restart-window bookkeeping in a `Ref`/`TVar`. The §29.2 `Supervisor` is explicitly a std-library layer. |
| `Concurrent.memoize` | `newPromise` + a `Ref`/`TVar` guard: first caller forks the compute and completes the promise, others `awaitPromise`. |
| Semaphores / queues / channels / hubs | over `TVar` + `Promise` (permits in a TVar with `retry`-based blocking; queue = TVar of list + retry). |
| `withEarlyRelease` | `acquireRelease`/`doscope` returning the `release` action as a value (idempotent guard in a `Ref`). |
| CE `Resource` (`make`/`makeCase`/`use`/`both`/`race`/`memoize`) | over `acquire_release` + `with_scope`/`shutdown_scope`. |
| CE `Ref` extras (`getAndSet`/`modify`/`access`/`tryUpdate`) | over `new_ref`/`read_ref`/`write_ref` (or `AtomicRef` CAS once #1 lands). |

---

## SKIP / not-applicable

Things ZIO/CE have that Kappa's spec deliberately does **not** standardize:

- **Stack traces / `Cause.untraced` / `Cause.Stackless`** — §18.1.3 keeps
  `DefectInfo` to diagnostic `message` text only. Kappa's `Cause` carries no
  portable StackTrace projection.
- **`Cause.Empty` identity + `Cause` as a monad** — Kappa's §28 `data Cause` is the
  5-constructor failure algebra only (`Fail`/`Interrupt`/`Defect`/`Both`/`Then`),
  with no `Empty` and no `flatMap`.
- **Environment / `ZLayer` / `ZIO.provide` / `FiberRef.currentEnvironment`** —
  Kappa models effects via `Eff`/`EffRow` (§18.1.14) and implicit values, not a
  reader-style `R` environment.
- **`FiberRef.unsafe` / `asThreadLocal`** — fibers are not host threads (§18.1.4);
  no thread-local escape hatch in portable semantics.
- **Execution tracing / `Fiber.roots` as a programmatic API** — §32.2.11 diagnostics
  are served by `krt2_dump`; a structured roots/status query is optional.
- **`Fiber.inheritAll` / `inheritRefs`** (merge a child's FiberRefs back on join) —
  not in §18.1.7 (which specifies only fork-time snapshot + independence).

---

## Recommended priority order

1. **`std.atomic` (`atomic.c`) — ADD #1.** The only place where an advertised
   capability (`rt-atomics` in `KRT2_CAPABILITIES`) is a lie: the ABI is declared
   but unimplemented. Highest correctness/credibility risk; self-contained C11
   work, no scheduler entanglement. Flip the flag only on completion.
2. **`FiberRef.modify` + copy-on-fork — ADD #4.** Completes a half-built §18.1.7
   primitive; the fork-snapshot is a *semantic conformance* gap (parent/child
   independence is normative). Unblocks the FiberRef test column and `std.supervisor`.
3. **`onInterrupt` / `onExit` — ADD #2.** Smallest change (extend `KK_FINSEQ`,
   which already carries the Reason) for the largest ZIO-parity payoff.
4. **`Promise.poll` / `isDone` — ADD #3.** Tiny; unblocks Memoize/Deferred-style
   derivations and non-blocking-peek tests.
5. **`disconnect` — ADD #5 (verify-then-add).** Confirm it isn't already
   expressible via forkDaemon + detached-interrupt before adding a primitive.
6. **Derive the library layer** (zipPar/foreachPar/raceWith/raceAll/timeoutTo,
   Cause projections as pure folds, `std.supervisor`, memoize, semaphores/queues).
   Pure composition — gated only on #1–#5 and on the v2 codegen that lets `.kp`
   call these primitives.
7. **Diagnostics (`Fiber.status`/`interruptAll`/`awaitAll` as structured queries)
   — last.** Observability, not semantics; `krt2_dump` covers the immediate need.

**Key load-bearing facts:**
- There is no `atomic.c`; `krt2_atomic_*` are declared-only in `kappart2.h`. This
  is the single biggest gap.
- The `FinSeq` struct in `rt.c` already carries `rkind`/`rval`/`rlabel` — so
  onInterrupt/onExit is a genuinely small extension.
- STM's journaled multi-fiber engine is fully done (`stm.c`, reviewed, two bugs
  fixed); the native `.kp` surface currently uses single-agent cell semantics
  pending the do-kernel CPS rewrite.
- The reference interpreter (`Interp.hs` `runPrimIO'`) also lacks
  onInterrupt/onExit/disconnect/modifyFiberRef/atomics — add them to the
  interpreter in lockstep to keep the authoritative set aligned.
