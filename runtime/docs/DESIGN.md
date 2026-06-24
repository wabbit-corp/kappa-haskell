# Kappa Runtime (`kappart2`) — Design

> A real concurrency + async-I/O runtime for Kappa's native backend: M:N
> work-stealing fibers, structured-concurrency supervision, a libuv reactor,
> parallel STM, atomics, interruption/masking, and algebraic-effect handlers —
> implementing the observable behavior mandated by Spec §18 and §32.
>
> **Status:** design + standalone core. Not yet wired into `Kappa.Backend.C`
> (that is the documented integration milestone, §17 below). The runtime is
> built and exercised on its own via C harnesses that construct `KValue` IO
> actions and drive them on the real scheduler.
>
> **This design was hardened by an 8-lens adversarial review — see
> [`REVIEW.md`](REVIEW.md).** The architecture below is the validated one
> ("proceed with fixes; keep the design"). Where REVIEW.md records a correction,
> the body here reflects it. Two consequences are load-bearing: (1) v1 advertises
> **five** capabilities — `rt-core`, `rt-parallel`, `rt-shared-stm`,
> `rt-blocking`, `rt-atomics` — and **stages `rt-multishot-effects` to v2** behind
> a real gate (REVIEW.md "Capability staging"); (2) making *already-compiled*
> do-blocks suspend at every IO boundary needs a `C.hs` codegen rewrite (v2, §17)
> — the v1 runtime is proven by C harnesses that build the same CK-machine action
> trees that rewrite will emit.

---

## 1. Goals and non-goals

### Goals

1. Implement the **full** runtime contract of Spec §18 (Effects, fibers,
   structured concurrency, timers, promises, fiber-local state, interruption,
   masking, STM) and §32.2 (the abstract runtime state machine and its
   observable transitions) — *not a subset*.
2. Advertise the **complete** capability set (Spec §27.6):
   `rt-core`, `rt-parallel`, `rt-shared-stm`, `rt-blocking`, `rt-atomics`,
   `rt-multishot-effects`. A flag is advertised only when the runtime actually
   backs it — advertising a syntactic surface while weakening semantics is
   itself non-conforming (§27.6).
3. **True multicore**: runnable fibers execute on more than one host thread at a
   time (`rt-parallel`), with cross-worker STM (`rt-shared-stm`) and hardware
   atomics (`rt-atomics`).
4. Reuse the existing boxed `KValue` model and Boehm GC unchanged, so the
   runtime is a *layer over* `runtime/kappart.{c,h}`, not a fork of it.
5. Be a clean, documented C ABI the native backend can target (§17), and a
   self-contained, testable artifact *before* that integration lands.
6. Borrow deliberately and creditably from Go, GHC's RTS, Erlang/BEAM,
   Rust/Tokio, the JVM/CLR, and libuv/Node (§18, "Borrowed-ideas ledger").

### Non-goals (v1)

- A bespoke garbage collector. We use **Boehm GC in thread/parallel mode**
  (`GC_THREADS`, parallel mark). A generational, per-worker-nursery collector
  (à la GHC/Go) is future work (§16, §19).
- Signal-based asynchronous preemption. Cooperative **reduction-budget safe
  points** satisfy §32.2.6 fairness; async preemption is an optional latency
  optimization documented as future work (§6.4).
- Replacing the compiler's `Kappa.Backend.C` lowering. v1 ships the runtime and
  the ABI seam; rewiring codegen to emit scheduler calls is milestone §17.
- Distribution / multi-node. `FiberId` and STM are single-program-execution
  (§32.2.8, §32.2.9). No remote fibers.

---

## 2. What already exists, and the gap

`runtime/kappart.c` (the bundled native runtime) is a **single-threaded,
boxed-value, Boehm-GC trampoline**:

- Every value is a uniformly boxed `KValue` on the GC heap (`kappart.h`).
- An IO action is a *suspended* `KValue` (a saturated `K_PRIM`/`K_NATIVE`, or a
  `K_IO` thunk). It fires only under **`krun_io`**, a recursive C dispatch loop.
- Sequencing (`ioBind`/`ioThen`), error handling (`catchIO`/`finallyIO`), and
  `defer` (`K_IOFINALLY` + a heap `kdefer_frame` stack) are expressed as
  **re-entrant recursive `krun_io` calls**; a tail-call trampoline
  (`ktrampoline`, `K_BOUNCE`, `K_IOTAIL`/`K_IOEFFECT`) folds only the *tail* legs
  back into the loop to keep the C stack bounded.
- Algebraic effects are **already CPS-reified** as a free-monad tree
  (`KCT_EFFPURE`/`KCT_EFFOP`, walked by `kpf___handleEff`); the resumption is an
  ordinary GC closure (`kclo`). This is the one place a continuation is already a
  first-class heap value — but it runs *purely*, outside `krun_io`.

There is **no scheduler, no fiber, no async I/O**. The only libuv in-tree
(`examples/native/http_uv`) is a *per-call blocking shim* that runs its own loop
and blocks the whole process per I/O op.

The **reference semantics** live in `src/Kappa/Interp.hs`: it maps each Kappa
fiber to a **GHC green thread** (`forkIOWithUnmask`), interruption to `throwTo`,
`await` to `MVar`, STM to GHC STM, timers to `threadDelay`. That is the exact
observable behavior this runtime must reproduce in C without GHC. `Interp.hs` is
our executable oracle: every conformance test that runs `main` and checks stdout
(`--! assertRunStdout`) is a behavior we must match.

**The crux:** `krun_io`'s recursion captures a fiber's continuation only as a C
return address. To suspend a fiber on I/O, a promise, a timer, an STM retry, or
`cede`, the continuation must become a **heap object the scheduler can re-enter**.
The suspension sites are well-localized (verified against `kappart.c`): the
non-tail leg of `ioBind`/`ioThen`, the `catchIO`/`finallyIO` body, the per-defer
run in `krun_finish`, and the saturated `K_NATIVE` fire site. We convert exactly
those into a continuation-stack machine (§5).

---

## 3. Conformance target → capability map

| Capability              | Meaning (§27.6)                                            | How `kappart2` backs it                                                        |
|-------------------------|------------------------------------------------------------|-------------------------------------------------------------------------------|
| `rt-core`               | Full IO/fiber/scheduler/STM/timer/promise/supervision      | §5–§12: the whole runtime                                                      |
| `rt-parallel`           | Runnable fibers on >1 host thread simultaneously           | §6: M:N work-stealing over N worker threads                                   |
| `rt-shared-stm`         | TVars valid across parallel workers                        | §11: GHC-style optimistic STM with per-TVar versions, commit lock, wait-sets  |
| `rt-blocking`           | `blocking` combinator + blocking foreign-call bridge       | §7.4: libuv threadpool offload lane                                           |
| `rt-atomics`            | `std.atomic`: ordered atomic cells                         | §10: C11 `<stdatomic.h>`, enum→`memory_order_*`                               |
| `rt-multishot-effects`  | Persistent multi-shot resumptions, segment cloning (§32.2.16) | §13: immutable heap-reified continuation segments, logical clone-on-resume |

> **`Capabilities.hs` correction.** `src/Kappa/Backend/Capabilities.hs` currently
> advertises only `["rt-core","rt-blocking","rt-atomics"]`. Per the user, omitting
> `rt-parallel` (and the others) was an expedient under-claim. The target is the
> full six. The flip is part of milestone §17: we advertise a flag only once
> `kappart2` is wired in and backs it, because §27.6 makes advertising an unbacked
> capability non-conforming.

---

## 4. The abstract runtime state machine (§32.2.1) → concrete structures

Spec §32.2.1 fixes the observable state a conforming runtime must preserve. We
realize it directly:

| §32.2.1 abstract state            | `kappart2` structure                                                  |
|-----------------------------------|-----------------------------------------------------------------------|
| runtime agents                    | the runtime `Rt` (one per program); workers are *not* separate agents  |
| a fiber table                     | `Fiber` objects, GC-kept while reachable; an id→fiber weak map for trace|
| runnable queues per agent         | per-worker Chase–Lev deque + a global injection queue (`runq.c`)       |
| supervision scopes                | `Scope` objects forming a tree; each holds its attached-children set    |
| timer registrations               | a libuv `uv_timer_t` per sleeping fiber / one min-heap timer wheel      |
| promise cells                     | `Promise` objects: a single-assignment `Exit` slot + a waiter list      |
| a TVar store + parked wait-sets   | `TVar` objects with version + watcher list; the STM manager (`stm.c`)   |
| handler/resumption storage        | heap-reified continuation segments (`Cont`, §5/§13)                    |
| exit-action stacks                | per-fiber `defer`/`using` stack (`Fiber.exits`)                        |

Each **live fiber** (§32.2.1) carries: its current control segment / suspended
continuation; status (`RUNNING`/`RUNNABLE`/`PARKED`/`DONE`); current supervision
scope; current masking depth; pending interruption request (if any); pending
exit-action stack; current `FiberRef` map; and its terminal `Exit` once done.
This is precisely the `Fiber` struct (§5.1).

The required transition families (§32.2.1) — step/suspend/wake, interrupt
request/deliver, scope attach/shutdown/exit, timer fire, promise
complete/wake, STM read/write/retry/commit, handler capture/resume/abandon — are
the operations in §5–§13.

---

## 5. Fibers and the CK-machine IO driver

### 5.1 The `Fiber`

```c
typedef enum { F_RUNNABLE, F_RUNNING, F_PARKED, F_DONE } FStatus;

typedef struct Fiber {
  uint64_t      id;            // unique FiberId (atomic counter)
  _Atomic FStatus status;
  Cont         *k;             // suspended continuation: the rest of the computation
  KValue       *cur;           // value being returned into k (when resuming)
  Scope        *scope;         // current supervision scope
  uint32_t      mask_depth;    // 0 == interruptible; >0 masked (§18.1.12)
  _Atomic int   interrupt_pending;   // a request arrived
  KValue       *interrupt_cause;     // the structured InterruptCause (§18.1.2)
  ExitFrame    *exits;         // per-fiber defer/using stack (heap, LIFO)
  FiberRefMap  *locals;        // copy-on-fork fiber-local map (§18.1.7)
  KValue       *label;         // Option String diagnostic label (§18.1.10)
  KValue       *exit;          // terminal Exit, once F_DONE (§18.8)
  WaiterList    waiters;       // fibers parked in await/join on this one
  struct Worker*home;          // last worker (scheduling hint; not affinity)
  uint32_t      reductions;    // budget remaining before a forced cede (§6.4)
} Fiber;
```

The fiber is an ordinary GC object. **Nothing about a fiber lives on a C stack**
between steps — that is what makes it relocatable across workers and trivially
GC-traced.

### 5.2 The continuation, `Cont`

`krun_io`'s recursion is replaced by an explicit, heap-allocated continuation —
a defunctionalized return stack (the GHC-RTS "return stack as heap objects"
idea, the CEK-machine "K" component):

```c
typedef enum {
  KK_DONE,        // bottom: the fiber's result is its terminal value
  KK_BIND,        // after `m`, apply `k : a -> IO b`     (ioBind / do-bind)
  KK_THEN,        // after `m`, run `next : IO b`          (ioThen / do-seq)
  KK_CATCH,       // if `m` failed with K_FAIL, apply handler; else pass through
  KK_RESTORE,     // pop a masking frame (un-mask) on the way out (§18.1.12)
  KK_POPEXIT,     // run-and-pop one exit action, then continue (§18.7 defer/using)
  KK_HANDLE,      // an algebraic-effect handler boundary (§13)
  KK_UNSCOPE      // leave a structured do-scope: shut down attached children (§32.2.3)
} KKind;

typedef struct Cont {
  KKind        kind;
  KValue      *a;     // payload: the k closure / next action / handler / exit action
  KValue      *b;     // secondary payload (e.g. handler return clause)
  void        *aux;   // structure pointer (Scope* for UNSCOPE, ExitFrame* for POPEXIT…)
  struct Cont *next;  // the rest of the stack (immutable; sharing enables multi-shot)
} Cont;
```

`Cont` cells are **immutable and shared**. Pushing a frame allocates a new cell
whose `next` points at the existing stack. This immutability is the foundation
of multi-shot resumption (§13): a captured continuation segment is just a `Cont*`,
and resuming it twice re-runs forward from the same shared structure.

### 5.3 The step loop

The scheduler runs a fiber by calling `fiber_run(rt, w, f)`, which drives a CK
loop *until the fiber suspends or finishes*:

```
fiber_run(f):
  loop:
    if f->interrupt_pending and f->mask_depth == 0:   // §32.2.5 interruption point
        deliver_interrupt(f); continue                // unwinds via KK_POPEXIT frames
    if f->reductions-- == 0:                           // §6.4 fairness safe point
        f->reductions = QUANTUM; reschedule(f); return SUSPENDED
    step = run_one(f->cur)        // run the current action ONE IO step (no nesting)
    switch step.tag:
      VALUE v:        // the action produced a value; feed it to the continuation
        (f->cur, f->k, ctl) = apply_cont(f->k, v)
        if ctl == FINISH: f->exit = Success(v); finish(f); return DONE
      FAIL e:         // typed failure; search k for KK_CATCH, running KK_POPEXIT en route
        f->k = unwind_to_catch(f->k, e); ...
      BLOCK(reason):  // await/join/promise/sleep/STM-retry/I/O: PARK
        park(f, reason); return SUSPENDED      // the woken-by side re-enqueues f
      CEDE:           // explicit yield (§18.1.5)
        reschedule(f); return SUSPENDED
```

`run_one` performs exactly one non-nesting IO step: it fires a saturated
`K_NATIVE`/`K_PRIM`, evaluates a `K_IO` thunk, or recognizes a scheduler
primitive (`fork`, `await`, `cede`, `newPromise`, …) and returns a `BLOCK`/`CEDE`
signal instead of recursing. The key invariant: **`run_one` never calls
`krun_io` recursively** — every "and then do the rest" is a `Cont` frame, not a C
frame. This is the refactor that makes suspension possible.

### 5.4 Where blocking native calls go

A saturated `is_io` `K_NATIVE` whose binding is classified `nonblocking`
(§26.1.4) runs **inline** on the worker (it does not block). One classified
`blocking` is **not** run inline: the fiber parks and the call is dispatched to
the blocking lane (§7.4), which resumes the fiber with the result. This is the
direct realization of §32.2.6 ("blocking foreign work MUST NOT monopolize
scheduler resources") and of `blocking` requiring `rt-blocking`.

---

## 6. The scheduler (M:N, work-stealing)

### 6.1 Workers

`N` worker threads (default `min(ncpu, RT_MAX_WORKERS)`, override via
`KAPPA_RT_WORKERS`), each an OS thread registered with Boehm (`GC_register_my_thread`).
A worker is Go's `P`+`M` fused, GHC's HEC, a BEAM scheduler. Each worker owns a
**Chase–Lev work-stealing deque** of runnable fibers (`push`/`pop` at the bottom
by the owner; `steal` from the top by thieves — the classic lock-free deque).

### 6.2 Queues and load balancing

- **Local deque** (per worker): LIFO for the owner (cache-friendly, like Go),
  stealable FIFO-ish from the top.
- **Global injection queue** (MPMC, lock + ring or a Michael–Scott queue): newly
  forked fibers and reactor/cross-thread wakeups land here or are pushed to a
  chosen worker; periodically polled to prevent global-queue starvation
  (Go's `schedtick % 61` trick).
- **Steal**: an idle worker scans peers in random order and steals half (BEAM/Go).
- **Park**: a worker with nothing to run and nothing to steal parks on a futex/
  condvar; it is woken when work is injected (`signal`) or by the reactor.

### 6.3 Fairness (§32.2.6)

Weak fairness is guaranteed by: (a) a continuously-runnable fiber re-enters a
run queue every time its **reduction budget** (`QUANTUM`) is exhausted (§6.4),
so it cannot monopolize a worker; (b) `cede` immediately reschedules behind other
runnable fibers; (c) the global-queue poll prevents local-deque favoritism from
starving injected work. With N>1 workers, one CPU-bound fiber cannot starve the
others at all (they run elsewhere and steal).

### 6.4 Safe points and reduction budgets (BEAM/Tokio coop/Go)

Each fiber has a `reductions` counter. It is decremented at every IO step (§5.3)
and **must** be decremented by generated code at loop back-edges and function
entries — the §27.5A.4 safe-point obligation (whose violation is
`E_BACKEND_PYTHON_SAFEPOINT_MISSING` for the Python profile; the native analog is
the codegen's responsibility, §17). The runtime exposes `krt2_safepoint()` for
codegen to emit. When the budget hits zero, the fiber yields cooperatively: this
is simultaneously the fairness mechanism and an interruption-delivery point. We
do **not** use signal-based async preemption in v1; §32.2.6 explicitly permits
"reduction budgets / loop-backedge checks" as the safe-point mechanism. Async
preemption (Go 1.14-style, signal a worker to dump its current fiber) is a
documented latency upgrade (§19).

---

## 7. libuv integration: the reactor + the blocking lane

### 7.1 One reactor thread

libuv loops are **not** thread-safe to share. Rather than fight handle-affinity
across N workers (the multi-loop Tokio model — a future upgrade, §19), v1 runs a
single **reactor thread** owning one `uv_loop_t`. This is the BEAM poll-thread /
Node loop / Tokio current-thread-reactor split: the reactor does only readiness
and dispatch; the actual fiber work runs in parallel on the workers. The reactor
is rarely the bottleneck because it touches no user computation.

### 7.2 Submitting interest

A worker that needs I/O for a fiber:
1. builds an `IoReq` (op, args, the parked `Fiber*`),
2. pushes it to the reactor's **MPSC request queue**,
3. signals the reactor with **`uv_async_send`** (the only thread-safe libuv call),
4. parks the fiber and returns to the scheduler.

The reactor's `uv_async` callback drains the queue and starts the libuv
operations (`uv_timer_start`, `uv_read_start`, `uv_write`, `uv_fs_*`, …) with C
callbacks that, on completion, package the result and **wake** the fiber.

### 7.3 Waking a fiber from the reactor

On an I/O/timer callback the reactor: stores the result into the fiber's `cur`,
sets `status = F_RUNNABLE`, pushes it to the **global injection queue**, and wakes
a parked worker (futex signal). This is Tokio's `Waker`. The happens-before edge
(§32.2.10) — the I/O result published before the fiber's next step — is
established by the queue's release/acquire (§12).

### 7.4 The blocking lane (`rt-blocking`)

`blocking body` and `blocking`-classified foreign calls run on libuv's worker
threadpool via `uv_queue_work` (configurable size, `UV_THREADPOOL_SIZE`). The
fiber parks; the work runs on a pool thread (registered with Boehm); the
`after_work` callback on the reactor wakes the fiber. This is Tokio
`spawn_blocking` / BEAM dirty schedulers / JVM virtual-thread carrier offload. A
program that uses `blocking` without `rt-blocking` is rejected (§27.6) — but the
native profile advertises it, so this is the supported path.

### 7.5 Idle and shutdown

When *all* workers are parked and the run queues are empty, the only thing that
can make progress is a timer or I/O completion — so the system blocks in the
reactor's `uv_run` until a callback fires (zero busy-waiting). The program ends
when the main fiber completes (`Exit` is delivered to the C entrypoint), at which
point the runtime shuts scopes (§9), stops the reactor (`uv_stop`), joins
workers, and returns the main `Exit` to `main`.

---

## 8. Interruption and masking (§18.1.12, §32.2.5)

Interruption is an **asynchronous request**, delivered only at interruption
points (§32.2.5): runtime suspension points, `await`/`join`, STM `retry` parking,
and explicit `poll`. It is *never* forced.

- `interrupt`/`interruptAs` set `f->interrupt_pending` + `f->interrupt_cause`
  (the structured `InterruptCause`, §18.1.2), then **park the caller** on the
  target's waiter list until the target is `F_DONE` and its finalizers have run
  (§18.1.4). `interruptFork` does not wait.
- A fiber observes its pending interrupt at the next interruption point **iff
  `mask_depth == 0`** (§5.3). Delivery converts the rest of the computation into
  an unwind: `unwind_to_done` runs every `KK_POPEXIT` / `KK_RESTORE` /
  `KK_UNSCOPE` frame in masked LIFO order (finalizers run masked, §32.2.5), then
  sets `exit = Failure (Interrupt cause)`.
- `mask f` / `uninterruptible body` raise `mask_depth`; `restore` lowers it for a
  sub-computation (a `KK_RESTORE` frame restores depth on the way out). `poll`
  delivers a pending interrupt *even while masked* (§18.1.12).
- A fiber carries **at most one** pending request (§18.1.12); the first
  determines the portable cause; later ones may be recorded diagnostically.

This is GHC's async-exception model (`throwTo` + `mask`/`unmask` + finalizers
unwind before the handler observes) reproduced explicitly, which is exactly what
`Interp.hs` does with `forkIOWithUnmask`.

---

## 9. Structured concurrency: scopes and supervision (§32.2.3/.4)

### 9.1 Scopes

A `Scope` is a node in a tree with a set of **attached** live children and its
own exit-action obligations. The runtime behaves as if **every IO `do` block
introduces a nested supervision scope** (§32.2.3). On scope exit (`KK_UNSCOPE`):

1. interrupt every still-live attached child with tag `ScopeShutdown` (§32.2.8),
2. **wait** until each child is `F_DONE` and all its finalizers have run,
3. *then* run the scope's own `defer`/`using`/release actions.

This ordering is mandatory (§32.2.3): child termination (incl. child finalizers)
completes **before** parent-scope release of resources owned by that scope.

- `fork` attaches to the **innermost** current scope; `forkDaemon` does not
  attach; `forkIn scope` attaches to an explicit `scope`.
- `withScope` brackets a fresh scope with masked shutdown on exit; `newScope` /
  `shutdownScope` are the low-level primitives; `shutdownScope` is idempotent.

### 9.2 Unacknowledged-child defects (§32.2.4)

A child that exits `Failure (Fail e | Defect d)` and remains **unacknowledged**
(no `await`/`join`/`awaitMonitor` observed it) at scope exit makes the scope
acquire `Defect (DefectInfo UnhandledChildFailure …)`. Multiple such combine with
`Both` in child-creation order, before later finalizer causes append with `Then`
(§32.2.12). The scope tracks, per child, whether its exit was acknowledged.

### 9.3 `std.supervisor` (§29.2)

OTP-style supervision (`OneForOne`/`OneForAll`/`RestForOne`,
`Permanent`/`Transient`/`Temporary`, `RestartIntensity` sliding window) is a
**library** over Scope/Fiber/Monitor/Promise/timers (§29.2 permits runtime *or*
library). We implement it as Kappa (`rt.supervisor`) over the primitives, so the
runtime surface stays small. Restart-storm shutdown and original-child-order
restart sequencing (BEAM) are reproduced; cause composition uses `Both`/`Then`.

---

## 10. Atomics (`rt-atomics`, §29.1)

`AtomicRef a` is a **distinct cell kind** (not `Ref`/`TVar`/`var`), holding a
single GC-pointer slot operated on with C11 atomics. The memory-order enums map
directly:

| Kappa order            | C11                       |
|------------------------|---------------------------|
| `LoadRelaxed`          | `memory_order_relaxed`    |
| `LoadAcquire`          | `memory_order_acquire`    |
| `LoadSeqCst`           | `memory_order_seq_cst`    |
| `StoreRelease`         | `memory_order_release`    |
| `RmwAcqRel`            | `memory_order_acq_rel`    |
| `CasFail*`             | load-like only, never release |

`atomicLoad/Store/Exchange/CompareExchange` operate on the pointer slot;
`atomicFetchAdd/Sub/And/Or/Xor` require `AtomicInteger` and operate on
fixed-width integer atomics (we provide instances for the `std.ffi` exact/pointer-
width integer types; **not** for the arbitrary-precision `Int`, per §29.1).
Compare-exchange uses **representation equality** of the `AtomicValue` instance.
The §32.2.10 synchronizes-with / release-sequence / SeqCst-global-order semantics
are exactly C11's, so the mapping is sound by construction.

---

## 11. STM (`rt-shared-stm`, §18.1.13, §32.2.9)

GHC-style optimistic STM, valid across parallel workers:

- A `TVar` holds a current value + a monotonic **version** + a **watcher** list.
- A transaction runs against a thread-local **read-set** (tvar→version-seen) and
  **write-set** (tvar→new-value); reads see prior writes in the same txn.
- **Commit** (§32.2.9, uninterruptible once begun): take a global commit lock (or
  lock the write-set's TVars in address order — fine-grained, v2), validate that
  every read TVar's version is unchanged; if valid, install writes, bump
  versions, wake watchers; else abort and retry. (v1 uses a single global commit
  mutex — correct and simple; the read phase is lock-free and parallel. v2 moves
  to per-TVar locks for commit scalability.)
- `retry` aborts the attempt and **parks** the fiber on the watcher lists of
  every TVar it read (an interruption point, §32.2.5); a later commit that bumps
  one of those versions wakes it.
- `orElse l r` runs `r` only if `l` retried (transactional choice;
  `Alternative STM` `empty = retry`).

Serializability relative to all `atomically` in the same TVar domain (§32.2.9) is
guaranteed by commit-time validation under the lock. The happens-before edge
"successful commit happens-before any later observing transaction" (§32.2.10) is
the version bump under release/acquire.

---

## 12. Memory visibility / happens-before (§32.2.10)

We place real release/acquire edges at exactly the four mandated points:

1. **fork publication**: the parent's writes (and the inherited `FiberRef`
   snapshot) are released before the child's first step acquires them — the
   run-queue push/pop is the barrier.
2. **fiber termination → await/join**: `finish(f)` releases `f->exit`; the woken
   waiter acquires it.
3. **promise completion → waiters**: the first `completePromise` releases the
   `Exit`; `awaitPromise*` acquires.
4. **STM commit → later txn**: the version bump (§11).

Ordinary `K_REF`/`var` are **not** cross-fiber sync primitives (§32.2.10): races
on them have no portable ordering and need no locks. They stay lock-free; pointer-
slot writes are naturally atomic on aligned 64-bit, so racing is memory-safe (no
torn pointers) even though it is semantically the program's responsibility. Same-
fiber ref ordering is preserved (we never reorder same-fiber operations).

---

## 13. Algebraic-effect handlers and multi-shot resumptions (`rt-multishot-effects`, §32.2.13–.20)

The existing `KCT_EFFPURE`/`KCT_EFFOP` effect tree already reifies resumptions as
GC closures, but purely. We unify it with the IO CK-machine:

- A `handle label e with …` pushes a **`KK_HANDLE`** frame recording the
  *exact effect-label value* (identity match, §18.1.18), the return clause, and
  the operation clauses.
- `label.op args` walks `f->k` to the nearest matching `KK_HANDLE` (skipping other
  labels), **capturing the `Cont` suffix** from the op site to that handler as the
  resumption segment `r` (§32.2.13). Because `Cont` cells are immutable and shared
  (§5.2), `r` is just the captured `Cont*` plus the captured mask state.
- Resuming `r v` re-enters that suffix with `v` (§32.2.13–.18). The captured env's
  heap objects stay **shared** (§32.2.18): a `var`/`newRef` allocated before the
  op site is the *same* object across resumption uses; pre-op effects are not
  rolled back; post-resumption effects occur anew on each use.
- **Multi-shot** (`rt-multishot-effects`): resuming `r` more than once is sound
  because re-entering an immutable `Cont*` re-runs forward without mutating the
  segment. Each use gets **independent exit-action obligations** (§32.2.16/.19):
  the `KK_POPEXIT` frames in the segment fire once *per use*. (Captured `var`s are
  shared per §32.2.18; the *control* obligations clone.)
- **Abortive** (quantity-0) clauses MUST still unwind the captured segment's
  `defer`/`using` exactly once in masked LIFO order (§32.2.17/.20) — we do not
  drop the segment silently. A resumption whose captured segment carries pending
  exit actions must not escape its clause (§32.2.20); the elaborator enforces this
  statically (the runtime trusts the checked program).

Reclamation: abandoned segments are ordinary GC garbage (Boehm reclaims them);
no segment is freed while a one-shot resumption that needs it is still live, and
no host-GC promptness is required for source-level release (§34.4.1).
`deep handle` desugars (already in the prelude/codegen) to a recursive driver that
reinstalls itself around each resumption — we reuse the existing `eff_reinstall_k`
shape, lifted into the CK-machine.

**Continuation-representation documentation (the §34.4.1 deliverable for
advertising `rt-multishot-effects`):**
- *Segment representation:* immutable singly-linked heap `Cont` frames + captured
  mask depth; closures captured by reference (shared env).
- *One-shot destructiveness:* none — one-shot is multi-shot used once; segments
  are never mutated, so a one-shot resume cannot invalidate a sibling clone.
- *Multi-shot per-use:* re-entry allocates only the new forward frames it
  produces; the captured prefix is shared structurally (no copy, no stack walk).
- *Reclamation events:* GC. A segment becomes unreachable when no fiber holds the
  resumption and it is not on any fiber's `k`; Boehm collects it. No special
  reclamation trigger is required.

---

## 14. Finalizers: `defer` / `using` / `bracket` (§18.7, §34.4.1)

`defer`/`using`/`MonadFinally` are **language-level** exit actions, never lowered
to host finalizers and never dependent on prompt GC (§34.4.1). They are
`KK_POPEXIT` frames on the fiber's exit stack, run **exactly once** in **masked
LIFO** order on every way out — normal completion, typed failure, interruption,
defect (§18.8, §32.2.19). First-error-wins propagation: a finalizer that fails
composes its cause with the in-flight cause via `Then` (§32.2.12). `using`
schedules `Release[A] rel resource` onto the current scope's exit stack at
acquire time (§19.5). This mirrors `Interp.hs`'s `runScope` exit-action queue
exactly.

---

## 15. The `Exit` / `Cause` model and composition (§28, §32.2.12)

```
Exit e a  = Success a | Failure (Cause e)
Cause e   = Fail e | Interrupt InterruptCause | Defect DefectInfo
          | Both (Cause e) (Cause e)     -- concurrent/sibling failures
          | Then (Cause e) (Cause e)     -- sequential: earlier `Then` later (e.g. body then finalizer)
InterruptCause = InterruptCause InterruptTag (Option FiberId)
InterruptTag   = Requested | ScopeShutdown | TimedOut | RaceLost | External | Custom String
```

The runtime classifies every fiber outcome into this algebra (the C `causeOf`
analog of `Interp.hs`): a typed `K_FAIL` → `Fail e`; a delivered interrupt →
`Interrupt cause`; a host/runtime panic → `Defect`. Scope shutdown of multiple
failing children composes with `Both` in creation order; body-then-finalizer
composes with `Then` (§32.2.12). `interrupt`/`shutdownScope`/`timeout`/`race`
stamp `Requested`/`ScopeShutdown`/`TimedOut`/`RaceLost`, with `by` = the
initiating `FiberId` (§32.2.8). `sandbox` exposes the full `Cause` in the typed
channel; `unsandbox` re-raises it.

---

## 16. Garbage collection (§32.2.8, §34.4.1)

- **Boehm GC in thread/parallel mode** (`GC_THREADS`, `GC_MARKERS`), reusing the
  existing `KValue` model unchanged. Every worker, the reactor, and each
  blocking-pool thread calls `GC_register_my_thread`. Stop-the-world parallel
  mark; all thread stacks + the heap are roots. Because fibers are heap-reified
  (§5), a parked fiber's entire state is reachable from the fiber table /
  promise / scope / timer that holds it — no stack scanning of suspended fibers
  is needed (the §A footgun of stackful designs is avoided).
- **Handle reachability (§32.2.8):** dropping the last *user* handle to a
  `Fiber`/`Scope`/`Promise`/`Monitor`/`TVar`/`FiberRef` must **not** alter it. So
  the runtime keeps its own strong references to *live* runtime entities
  (a running fiber is kept by its scope / run queue / waiters, not by the user's
  `Fiber` value). Source-level interruption/shutdown/release/finalization must
  **not** depend on host-GC finalization (§34.4.1) — they are all explicit.
- A bespoke generational, per-worker-nursery collector (GHC/Go-style) is the main
  future performance lever (§19); the design does not depend on Boehm specifics
  beyond "a precise-enough conservative tracing GC over `KValue`."

---

## 17. The integration seam (native backend → `kappart2`)

The runtime is usable standalone *now* (C harnesses build `KValue` IO actions and
call `krt2_run_main`). Wiring it into the compiler is a separate, well-defined
milestone:

1. **Driver:** `Kappa.Backend.Driver` links `kappart2` (and `kappart`) and
   `-luv`/`pkg-config libuv` instead of the bare `kappart.c`.
2. **`main`:** `Kappa.Backend.C` emits `krt2_run_main(<main_action>)` instead of
   `krun_io_checked(...)` — the runtime owns the top-level loop.
3. **Scheduler primitives:** the prelude `expect term`s `fork`, `forkDaemon`,
   `await`, `join`, `interrupt*`, `cede`, `sleepFor`, `sleepUntil`, `timeout`,
   `race`, `newScope`, `forkIn`, `shutdownScope`, `withScope`, `monitor`,
   `newPromise`, `completePromise`, `awaitPromise*`, `newFiberRef`/`get`/`set`/
   `locally`, `newTVar`/`readTVar`/`writeTVar`/`atomically`/`retry`/`check`,
   `newAtomicRef`/`atomic*`, `blocking`, `mask`/`uninterruptible`/`poll`,
   `acquireRelease`/`ensuring` lower to the corresponding `krt2_*` entry points
   (a table in `C.hs`, parallel to the existing `kpf_io_*` table). Their C ABI is
   `include/kappart2.h` (§ the header).
4. **IO driver:** `ioBind`/`ioThen`/`catchIO`/`finallyIO`/`defer` codegen targets
   the CK-machine builders (`krt2_bind`/`krt2_then`/`krt2_catch`/`krt2_finally`/
   `krt2_defer`) so the non-tail legs become `Cont` frames, not nested
   `krun_io`. The existing `K_IOTAIL`/`K_BOUNCE` markers keep meaning "continue
   this fiber's step loop."
5. **Safe points:** `C.hs` emits `krt2_safepoint()` at loop back-edges (§6.4).
6. **Capabilities:** flip `Capabilities.hs` to the full six once 1–5 land and
   the conformance suite passes natively.

Until then, the runtime keeps the `KValue`/`KTag`/`krun_io` ABI **stable** and
**adds no `KTag`** (REVIEW.md M22): scheduler ops are reserved *primitive names*
the step loop recognizes — reusing the existing string dispatch and matching the
oracle's `__forkRun`/`__awaitFiber` — and the runtime entities
(`Fiber`/`Scope`/`Promise`/`TVar`/`AtomicRef`/`FiberRef`/`Monitor`) are `K_FGN`
boxes (§ the header's `KRT2_KIND_*`). So the two runtimes coexist with zero layout
change and the existing native backend keeps working.

**Build/link (REVIEW.md M14):** the runtime is ~14 translation units and its
`krt2_*` symbols are codegen intrinsics, *not* FFI host-binding symbols — so it
**cannot** ride a `hostBinding`/`pkgConfig` manifest entry. It ships as
`libkappart2.a` (built by the `Makefile`, or as Driver-owned TUs), and the Driver
links it **unconditionally** together with `-luv` (libuv via `pkg-config`),
threaded `-lgc`, and `-pthread` when the target uses kappart2. Both `kappart` and
`kappart2` TUs MUST be compiled with identical `-DGC_THREADS -pthread`; a
`_Static_assert` + a runtime `GC_get_parallel()` check fail closed on a mismatch.

---

## 18. Borrowed-ideas ledger

| Idea                                                | Borrowed from           | Where (§)        |
|-----------------------------------------------------|-------------------------|------------------|
| M:N work-stealing, per-worker LIFO deque + global Q | Go (P/M), GHC HECs, BEAM | §6               |
| Chase–Lev lock-free work-stealing deque             | Go, JVM ForkJoinPool    | §6.1             |
| Reduction-budget cooperative safe points            | BEAM reductions, Tokio coop, Go | §6.4     |
| Heap-reified return stack (stackless continuations)  | GHC RTS / STG           | §5               |
| Reactor/executor split; Waker wakeups; spawn_blocking | Tokio                   | §7               |
| Single event-loop reactor + threadpool offload      | libuv / Node, BEAM dirty schedulers | §7   |
| Async-exception masking + finalizers-before-observe | GHC RTS                 | §8               |
| Supervision trees = scopes; OTP restart strategies  | Erlang/BEAM             | §9               |
| StructuredTaskScope / structured concurrency        | JVM Loom, Trio, Kotlin  | §9               |
| Optimistic STM (read/write-set, version validation)  | GHC STM                 | §11              |
| JMM/C++ happens-before edge catalog                 | JVM JMM, C++ MM         | §12              |
| C11 atomics + memory orders                         | C++11/LLVM atomics      | §10              |
| Delimited continuations as heap data; multi-shot    | OCaml 5 / multicore effects, GHC | §13     |
| Safepoints for cooperative preemption               | JVM/CLR safepoints      | §6.4             |
| Parallel-mark conservative GC (start), gen-nursery (later) | Boehm; GHC/Go (future) | §16        |

---

## 19. Roadmap

- **v1 (this work):** standalone runtime: scheduler, fibers, libuv reactor +
  blocking lane, timers/sleep/timeout/race, promises, scopes/structured shutdown,
  monitors, fiber-local state, interruption/masking, STM, atomics, effect
  handlers (incl. multi-shot); C test harnesses; build via `kappa.build.kp` +
  Makefile; `rt.supervisor` library.
- **v2:** backend integration (§17); native conformance suite green; flip
  `Capabilities.hs`.
- **v3 perf:** per-worker libuv loops (multi-reactor, handle-affinity) for I/O
  scalability; generational per-worker-nursery GC; fine-grained STM commit locks;
  Go-1.14-style async preemption for tail-latency.

---

## 20. File map

The runtime lives in `runtime/`, flat alongside `kappart.c` (the boxed-value
model it layers over). The scheduler is consolidated into a handful of
translation units rather than the finer-grained split this design originally
sketched (`sched.c`/`fiber.c`/`runq.c`/`timer.c`/`promise.c`/`interrupt.c`/
`cause.c`/`fiberlocal.c` all fold into `rt.c`/`reactor.c`/`scope.c`; `atomic.c`
is not yet built — see [`PRIMITIVES.md`](PRIMITIVES.md)).

```
runtime/
  kappart.c            the boxed-value model: KValue, Boehm GC, pure + IO primitives
  kappart.h            its public header (KValue/KTag, kint/kctor/kapp/krun_io, …)
  kappa_ucd.h          Unicode tables used by the string primitives
  kappart2.h           the public C ABI: Fiber/Scope/Promise/TVar/AtomicRef + all krt2_* entry points
  kappart2_harness.h   test-harness helpers (build IO actions directly + run them)
  internal.h           private structs/opcodes shared by the scheduler TUs
  rt.c                 lifecycle + scheduler: workers, run queue, the CK-machine step
                       loop, Cont builders, fork/await/cede, promises, mask/restore, refs
  reactor.c            the libuv reactor thread, sleep timers, IoReq queue, uv_async wakeups
  scope.c              supervision scopes, structured shutdown, monitors, interrupt delivery/unwind
  race.c               race/timeout, composed from fork + promise + interrupt
  stm.c                TVars, optimistic transactions, commit/retry/orElse, wait-sets
  Makefile             standalone build of the runtime lib + C harnesses (no compiler needed)
  docs/                DESIGN.md (this), README, REVIEW, RESEARCH, COVERAGE, DEPLOYMENT, INTEGRATION, PRIMITIVES
  tests/               C harnesses: spine, parallel, scopes, completion, race, cancel, stm, stm_retry, stm_orelse
```

The Kappa backend (`Kappa.Backend.Driver`) links these TUs directly; there is no
separate package manifest.
