# Kappa Runtime (`kappart2`) — Design

> A real concurrency + async-I/O runtime for Kappa's native backend: M:N
> fibers on a global FIFO run queue, structured-concurrency supervision, a libuv reactor,
> parallel STM, atomics, interruption/masking, and algebraic-effect handlers —
> implementing the observable behavior mandated by Spec §18 and §32.
>
> **Status:** compiler-wired runtime core. The C and LLVM backends link
> `kappart2` and use its CK-machine builders for generated do-kernel paths such
> as scopes, loops, mutable refs, finalizers, early return, and fiber primitives.
> Legacy `krun_io` bridge paths still exist for older boxed IO producers.
> `rt-blocking` is wired for source-level `blocking` and classified native calls through an off-worker lane;
> per-worker work-stealing deques remain future work.
>
> **This design was hardened by an 8-lens adversarial review — see
> [`REVIEW.md`](REVIEW.md).** The architecture below is the validated one
> ("proceed with fixes; keep the design"). Where REVIEW.md records a correction,
> the body here reflects it. Two consequences are load-bearing: (1) the C runtime
> contains machinery for parallel workers, shared STM, `rt-blocking`, and atomics,
> while the Haskell native backend advertises only the binding-relevant verified
> profile `rt-core`, `rt-blocking`, `rt-atomics`; `rt-multishot-effects` remains
> staged to a later gate (REVIEW.md "Capability staging"); (2) making *already-compiled*
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
2. Keep the Spec §27.6 capability story authoritative at each layer: the C
   runtime documents the implementation machinery it contains, while the Haskell
   native build profile advertises only capabilities wired end-to-end through
   compiler lowering and conformance gates. Today that profile is `rt-core`,
   `rt-blocking`, and `rt-atomics`; `rt-parallel`, `rt-shared-stm`, and
   `rt-multishot-effects` are advertised there only after their gates are
   actually backed. Advertising a syntactic surface while weakening semantics is
   itself non-conforming (§27.6).
3. **True multicore substrate**: the C runtime can execute runnable fibers on
   more than one host thread at a time and contains cross-worker STM and hardware
   atomics. The build profile exposes the corresponding capability tokens only
   when the compiler/backend profile treats those semantics as authoritative.
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
- Replacing every legacy `krun_io` producer in one step. Compiler-generated
  do-kernel paths target `kappart2` today; older boxed IO/library paths may still
  enter through the bridge until they are retired incrementally.
- Distribution / multi-node. `FiberId` and STM are single-program-execution
  (§32.2.8, §32.2.9). No remote fibers.

---

## 2. What already exists, and the gap

The old bundled native runtime was a **single-threaded, boxed-value,
Boehm-GC trampoline**. Its boxed-value pieces now live in the split
`gc.c`/`value.c`/`bignum.c`/`show.c`/`unicode.c`/`prims.c` files:

- Runtime APIs still pass a `KValue*`-shaped word, but not every value is a
  heap `KValue`: immediates and packed small values live in the tag bits, while
  non-immediate values are heap objects traced by Boehm (`kappart.h`).
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
The suspension sites are well-localized (verified against the split boxed-runtime TUs):
non-tail leg of `ioBind`/`ioThen`, the `catchIO`/`finallyIO` body, the per-defer
run in `krun_finish`, and the saturated `K_NATIVE` fire site. We convert exactly
those into a continuation-stack machine (§5).

---

## 3. Conformance target → capability map

| Capability              | Meaning (§27.6)                                            | How `kappart2` backs it                                                        |
|-------------------------|------------------------------------------------------------|-------------------------------------------------------------------------------|
| `rt-core`               | Full IO/fiber/scheduler/STM/timer/promise/supervision      | §5–§12: the whole runtime                                                      |
| `rt-parallel`           | Runnable fibers on >1 host thread simultaneously           | §6: M:N workers over a global FIFO run queue                                  |
| `rt-shared-stm`         | TVars valid across parallel workers                        | §11: GHC-style optimistic STM with per-TVar versions, commit lock, wait-sets  |
| `rt-blocking`           | `blocking` combinator + blocking foreign-call bridge       | §7.4: fiber parks; blocking native call runs off-worker                       |
| `rt-atomics`            | `std.atomic`: ordered atomic cells                         | §10: C11 `<stdatomic.h>`, enum→`memory_order_*`                               |
| `rt-multishot-effects`  | Persistent multi-shot resumptions, segment cloning (§32.2.16) | **withheld today**; staged behind escape checks and persistent continuations |

> **Backend profile boundary.** `src/Kappa/Backend/Capabilities.hs` advertises the
> binding-relevant native profile `["rt-core","rt-blocking","rt-atomics"]`.
> Blocking-classified native calls are accepted because the backend preserves the
> classification into blocking `K_NATIVE` actions; source-level `blocking` builds
> the same lane's OP_BLOCKING node. Both route off-worker. `blocking-cancellable` remains rejected until a cancellation-aware
> bridge exists.

---

## 4. The abstract runtime state machine (§32.2.1) → concrete structures

Spec §32.2.1 fixes the observable state a conforming runtime must preserve. We
realize it directly:

| §32.2.1 abstract state            | `kappart2` structure                                                  |
|-----------------------------------|-----------------------------------------------------------------------|
| runtime agents                    | the runtime `Rt` (one per program); workers are *not* separate agents  |
| a fiber table                     | `Fiber` objects, GC-kept while reachable; an id→fiber weak map for trace|
| runnable queues per agent         | one mutex-protected global FIFO run queue today; per-worker Chase-Lev deques are a future performance path |
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
  struct Cont *next;  // the rest of the stack
} Cont;
```

Current native continuations are heap allocated, but the implemented effect
runtime is **one-shot**. Captured continuation segments may be severed and
spliced during resume; `rt-multishot-effects` is not advertised. Multi-shot
requires persistent/cloned continuation segments plus independent exit-action
obligations, and remains future work.

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
(§26.1.4) runs **inline** on the worker (it does not block). A classified
`blocking` native binding lowers to a blocking `K_NATIVE`; the CK-machine parks
the fiber, dispatches the host call off the scheduler worker, and resumes the
fiber with the result. A binding classified `blocking-cancellable` still requires
a safe cancellation mechanism and is rejected by the native profile today.

---

## 6. The scheduler (M:N, global FIFO today)

### 6.1 Workers

`N` worker threads (default `min(ncpu, RT_MAX_WORKERS)`, override via
`KAPPA_RT_WORKERS`), each an OS thread registered with Boehm (`GC_register_my_thread`).
A worker steps one runnable fiber at a time. Today workers draw from one
mutex-protected global FIFO run queue; per-worker Chase-Lev work-stealing deques
are the future performance path, not the current implementation.

### 6.2 Queues and load balancing

- **Global FIFO queue**: newly forked fibers, yields, reactor wakeups, and
  cross-thread wakeups are pushed here.
- **No stealing yet**: an idle worker waits on the global queue condition
  variable. Sharded/per-worker deques can be added later without changing the
  fiber semantics.
- **Park**: a worker with nothing to run and nothing to steal parks on a futex/
  condvar; it is woken when work is injected (`signal`) or by the reactor.

### 6.3 Fairness (§32.2.6)

Weak fairness is guaranteed by: (a) a continuously-runnable fiber re-enters the
run queue every time its **reduction budget** (`QUANTUM`) is exhausted (§6.4),
so it cannot monopolize a worker; and (b) `cede` immediately reschedules behind
other runnable fibers. The FIFO queue is a simple correctness baseline; work
stealing is a throughput optimization.

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

The runtime routes a blocking `K_NATIVE` or `krt2_blocking body` by parking the
fiber and running the action on a GC-registered off-worker pthread. Completion
wakes the parked fiber through the normal `krt2i_wake` path with the exact result
value, including typed failure or re-raise nodes. Interruption of a plain
`blocking` call is non-cancellable: the request is recorded, but the parked fiber
is not woken until the host call returns; the pending interrupt is then observed
at that resume point. This is a correctness lane, not the final throughput
design: a bounded pool or libuv-backed work queue can replace the thread-per-call
implementation without changing the observable contract.

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

`std.supervisor` is intended to be a **library** over
Scope/Fiber/Monitor/Promise/timers (§29.2 permits runtime *or* library), keeping
the runtime surface small. The current tree exposes the module surface, but the
OTP-style semantics (`OneForOne`/`OneForAll`/`RestForOne`,
`Permanent`/`Transient`/`Temporary`, restart-intensity windows, and
original-child-order restart sequencing) remain future-stage library work.

---

## 10. Atomics (`rt-atomics`, §29.1)

`AtomicRef a` is a **distinct cell kind** (not `Ref`/`TVar`/`var`), holding a
boxed `KValue *` slot protected by a per-cell mutex. This preserves the current
surface instances (`Bool` and arbitrary-precision `Integer`) exactly. The
memory-order enums are validated at the runtime boundary:

| Kappa order            | C11                       |
|------------------------|---------------------------|
| `LoadRelaxed`          | `memory_order_relaxed`    |
| `LoadAcquire`          | `memory_order_acquire`    |
| `LoadSeqCst`           | `memory_order_seq_cst`    |
| `StoreRelease`         | `memory_order_release`    |
| `RmwAcqRel`            | `memory_order_acq_rel`    |
| `CasFail*`             | load-like only, never release |

`atomicLoad/Store/Exchange/CompareExchange` operate on the boxed pointer slot.
`atomicFetchAdd/Sub/And/Or/Xor` require `AtomicInteger`; the current provided
surface covers arbitrary-precision `Integer` by performing the update while
holding the cell mutex. Compare-exchange uses **representation equality** of the
`AtomicValue` instance. The memory-order arguments are accepted and validated,
but this implementation gives mutex-backed atomicity rather than lock-free C11
integer operations. Fixed-width, lock-free specializations remain future work.

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

## 13. Algebraic-effect handlers and resumptions (§32.2.13–.20)

The existing `KCT_EFFPURE`/`KCT_EFFOP` effect tree already reifies resumptions as
GC closures, but purely. We unify it with the IO CK-machine:

- A `handle label e with …` pushes a **`KK_HANDLE`** frame recording the
  *exact effect-label value* (identity match, §18.1.18), the return clause, and
  the operation clauses.
- `label.op args` walks `f->k` to the nearest matching `KK_HANDLE` (skipping other
  labels), **capturing the `Cont` suffix** from the op site to that handler as the
  resumption segment `r` (§32.2.13). In the current native runtime this is a
  one-shot segment.
- Resuming `r v` re-enters that suffix with `v` (§32.2.13–.18). The captured env's
  heap objects stay **shared** (§32.2.18): a `var`/`newRef` allocated before the
  op site is the *same* object across resumption uses; pre-op effects are not
  rolled back; post-resumption effects occur anew on each use.
- **Multi-shot** (`rt-multishot-effects`) is not implemented by the native
  runtime and the capability is not advertised. Reachable multi-shot programs are
  rejected by the native backends. The future implementation must clone or
  otherwise persist captured control obligations so each resume gets independent
  exit-action obligations (§32.2.16/.19).
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

The runtime is usable both from standalone C harnesses and from compiler-generated
C/LLVM do-kernel paths. Remaining integration work is incremental:

1. **Driver/main:** `Kappa.Backend.Driver` links `kappart2` and generated native
   mains enter through the `krt2_run_main` path for `kappart2` do-kernel actions.
2. **Scheduler primitives:** the prelude `expect term`s `fork`, `forkDaemon`,
   `await`, `join`, `interrupt*`, `cede`, `sleepFor`, `sleepUntil`, `timeout`,
   `race`, `newScope`, `forkIn`, `shutdownScope`, `withScope`, `monitor`,
   `newPromise`, `completePromise`, `awaitPromise*`, `newFiberRef`/`get`/`set`/
   `locally`, `newTVar`/`readTVar`/`writeTVar`/`atomically`/`retry`/`check`,
   `newAtomicRef`/`atomic*`, `blocking`, `mask`/`uninterruptible`/`poll`,
   `acquireRelease`/`ensuring` lower through the protected-scope CK-machine
   builders (`krt2_finally`, `krt2_mask`, and `krt2_acquire_release` where the
   compiler emits the resource kernel). Their C ABI is `include/kappart2.h`
   (§ the header).
3. **IO driver:** `ioBind`/`ioThen`/`catchIO`/`finallyIO`/`defer` codegen targets
   the CK-machine builders (`krt2_bind`/`krt2_then`/`krt2_catch`/`krt2_finally`/
   `krt2_defer`) so the non-tail legs become `Cont` frames, not nested
   `krun_io`. The existing `K_IOTAIL`/`K_BOUNCE` markers keep meaning "continue
   this fiber's step loop."
4. **Safe points:** C and LLVM codegen emit `krt2_safepoint()` at generated loop
   back-edges (§6.4).
5. **Capabilities:** advertise additional capabilities only after the corresponding
   backend path is wired and verified. `rt-blocking` is now wired for
   source-level `blocking` and classified native calls; `rt-multishot-effects`
   remains withheld.

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
`kappart2` TUs MUST be compiled with identical `-D_GNU_SOURCE -DGC_THREADS -pthread`; a
`_Static_assert` + a runtime `GC_get_parallel()` check fail closed on a mismatch.

---

## 18. Borrowed-ideas ledger

| Idea                                                | Borrowed from           | Where (§)        |
|-----------------------------------------------------|-------------------------|------------------|
| M:N worker scheduler, global FIFO baseline          | Go (P/M), GHC HECs, BEAM | §6               |
| Future Chase–Lev work-stealing deque                | Go, JVM ForkJoinPool    | §6.1             |
| Reduction-budget cooperative safe points            | BEAM reductions, Tokio coop, Go | §6.4     |
| Heap-reified return stack (stackless continuations)  | GHC RTS / STG           | §5               |
| Reactor/executor split; Waker wakeups               | Tokio                   | §7               |
| Future blocking-work offload lane                   | libuv / Node, BEAM dirty schedulers | §7   |
| Async-exception masking + finalizers-before-observe | GHC RTS                 | §8               |
| Supervision trees = scopes; OTP restart strategies  | Erlang/BEAM             | §9               |
| StructuredTaskScope / structured concurrency        | JVM Loom, Trio, Kotlin  | §9               |
| Optimistic STM (read/write-set, version validation)  | GHC STM                 | §11              |
| JMM/C++ happens-before edge catalog                 | JVM JMM, C++ MM         | §12              |
| Atomic modification orders + memory-order validation | C++11/LLVM atomics      | §10              |
| Delimited continuations as heap data; multi-shot    | OCaml 5 / multicore effects, GHC | §13     |
| Safepoints for cooperative preemption               | JVM/CLR safepoints      | §6.4             |
| Parallel-mark conservative GC (start), gen-nursery (later) | Boehm; GHC/Go (future) | §16        |

---

## 19. Roadmap

- **v1 (this work):** standalone runtime and compiler-wired native profile:
  scheduler, fibers, libuv reactor + blocking lane, timers/sleep/timeout/race,
  promises, scopes/structured shutdown, monitors, fiber-local state,
  interruption/masking, STM core, boxed atomic cells, one-shot handler substrate,
  abandonment drain, C test harnesses, and build via `kappa.build.kp` + Makefile.
  The Haskell native backend advertises `rt-core`, `rt-blocking`, and `rt-atomics`.
- **v2:** remaining runtime surface gaps: supervisor library semantics, fiber
  labels, STM `orElse`, sandbox/unsandbox lowering, child-failure aggregation,
  and any capability-profile reconciliation for `rt-parallel` / `rt-shared-stm`.
- **v3 perf:** per-worker libuv loops (multi-reactor, handle-affinity) for I/O
  scalability; generational per-worker-nursery GC; fine-grained STM commit locks;
  Go-1.14-style async preemption for tail-latency.

---

## 20. File map

The runtime lives in `runtime/`, flat alongside the split boxed-value runtime TUs
(`gc.c`, `value.c`, `bignum.c`, `show.c`, `unicode.c`, and `prims.c`). The scheduler is consolidated into a handful of
translation units rather than the finer-grained split this design originally
sketched (`sched.c`/`fiber.c`/`runq.c`/`timer.c`/`promise.c`/`interrupt.c`/
`cause.c`/`fiberlocal.c` all fold into `rt.c`/`reactor.c`/`scope.c`; `atomic.c`
owns the boxed atomic cells — see [`PRIMITIVES.md`](PRIMITIVES.md)).

```
runtime/
  gc.c/value.c/...     the boxed-value model: KValue, Boehm GC, pure + IO primitives
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
  atomic.c             AtomicRef cells, C11 memory orders, CAS/fetch operations
  Makefile             standalone build of the runtime lib + C harnesses (no compiler needed)
  docs/                DESIGN.md (this), README, REVIEW, RESEARCH, COVERAGE, DEPLOYMENT, INTEGRATION, PRIMITIVES
  tests/               C harnesses: spine, parallel, scopes, completion, race, cancel, stm, stm_retry, stm_orelse
```

The Kappa backend (`Kappa.Backend.Driver`) links these TUs directly; there is no
separate package manifest.
