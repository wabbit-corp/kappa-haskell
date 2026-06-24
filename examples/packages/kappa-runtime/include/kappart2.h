/* kappart2.h — public C ABI of the Kappa runtime (`kappart2`).
 *
 * This is the runtime layer the native backend targets for the §18/§32 fiber,
 * scheduler, structured-concurrency, timer, promise, STM, atomics, and
 * algebraic-effect-handler model.  It sits *over* the existing boxed-value
 * runtime (runtime/kappart.{c,h}): every Kappa value is still a `KValue` on the
 * Boehm GC heap, and the runtime entities introduced here (Fiber, Scope,
 * Promise, TVar, AtomicRef, Monitor, FiberRef) are exposed to Kappa as opaque
 * `K_FGN` handles (the `expect data` types of §28 — abstract, runtime-owned).
 * No change to kappart.h's KTag layout is required: kappart2 is additive.
 *
 * EXECUTION MODEL.  An IO action is, as in kappart, a *suspended* `KValue`.  The
 * difference is the driver: instead of kappart's recursive `krun_io`, kappart2
 * runs each action inside a FIBER, stepping it with a stackless CK-machine
 * (see native/fiber.c).  Every "and then do the rest" is a heap `Cont` frame,
 * not a nested C call, so a fiber can SUSPEND at any IO boundary (await, sleep,
 * STM retry, blocking I/O, cede) and be resumed later — possibly on a different
 * worker thread.  See DESIGN.md §5 for the CK-machine and §6 for the M:N
 * work-stealing scheduler.
 *
 * THREADING.  The runtime is multicore (capability rt-parallel): N worker
 * threads run runnable fibers in parallel, a single libuv reactor thread drives
 * async I/O and timers, and a libuv threadpool backs the rt-blocking offload
 * lane.  All threads are registered with Boehm GC.  Ordinary refs (K_REF/var)
 * are NOT cross-fiber synchronization (§32.2.10); cross-fiber coordination uses
 * await/join, scopes/monitors, promises, STM, or atomics.
 *
 * CODEGEN CONTRACT.  Functions in the "IO CK-machine builders" and
 * "scheduler primitives" sections are what `Kappa.Backend.C` emits in place of
 * the bare kappart IO calls once integration (DESIGN.md §17) lands.  Each
 * returns a suspended `KValue` IO action; the fiber step loop interprets it.
 */
#ifndef KAPPART2_H
#define KAPPART2_H

#include <stdint.h>
#include <stddef.h>
#include "kappart.h"   /* KValue, KTag, kint/kstr/kctor/..., krun_io (legacy) */

#ifdef __cplusplus
extern "C" {
#endif

/* ── opaque runtime entities (Kappa sees these as K_FGN boxes) ──────────── */
typedef struct Rt        Rt;          /* the runtime (one per program execution) */
typedef struct Fiber     Fiber;       /* a lightweight Kappa thread (§18.1.4)     */
typedef struct Scope     Scope;       /* a supervision scope (§18.1.8, §32.2.3)   */
typedef struct Promise   Promise;     /* a one-shot promise cell (§18.1.9)        */
typedef struct Monitor   Monitor;     /* one-way termination observation (§18.1.8)*/
typedef struct TVar      TVar;        /* a transactional variable (§18.1.13)      */
typedef struct AtomicRef AtomicRef;   /* an atomic cell (§29.1, rt-atomics)       */
typedef struct FiberRef  FiberRef;    /* fiber-local cell (§18.1.7)               */

/* The `kind` strings stamped on the K_FGN boxes (for diagnostics + dispatch). */
#define KRT2_KIND_FIBER     "rt.Fiber"
#define KRT2_KIND_SCOPE     "rt.Scope"
#define KRT2_KIND_PROMISE   "rt.Promise"
#define KRT2_KIND_MONITOR   "rt.Monitor"
#define KRT2_KIND_TVAR      "rt.TVar"
#define KRT2_KIND_ATOMIC    "rt.AtomicRef"
#define KRT2_KIND_FIBERREF  "rt.FiberRef"

/* ── lifecycle ─────────────────────────────────────────────────────────── */

/* Initialize the runtime: GC, worker pool, libuv reactor, blocking lane.
 * `nworkers <= 0` selects min(ncpu, RT_MAX_WORKERS) (override: KAPPA_RT_WORKERS).
 * Idempotent-safe to call once at process start (after krt_init from kappart). */
Rt *krt2_new(int nworkers);

/* Run `action` (an IO computation) as the MAIN fiber on its root scope, drive
 * the scheduler until the main fiber terminates, then return its terminal
 * `Exit e a` value (Success a | Failure (Cause e), §28).  Shuts down the root
 * scope (interrupting/awaiting any still-live children), stops the reactor, and
 * joins workers before returning.  This is what generated `main` calls. */
KValue *krt2_run_main(KValue *action);

/* Tear down the runtime (stop reactor, join workers).  Normally implicit in
 * krt2_run_main; exposed for embedders. */
void krt2_shutdown(Rt *rt);

/* The active runtime (NULL before krt2_new). */
Rt *krt2_current(void);

/* ── IO CK-machine builders (codegen targets; DESIGN.md §5, §17.4) ──────── */
/* These replace kappart's nested `krun_io` legs with heap `Cont` frames so the
 * non-tail leg of each becomes a suspension point.  All return suspended IO. */
KValue *krt2_pure(KValue *v);                       /* ioPure  : a -> IO a       */
KValue *krt2_bind(KValue *m, KValue *k);            /* ioBind  : IO a -> (a->IO b) -> IO b */
KValue *krt2_then(KValue *m, KValue *next);         /* ioThen  : IO a -> IO b -> IO b */
KValue *krt2_catch(KValue *body, KValue *handler);  /* catchIO : IO a -> (e->IO a) -> IO a */
KValue *krt2_finally(KValue *body, KValue *fin);    /* finallyIO : IO a -> IO () -> IO a   */
KValue *krt2_throw(KValue *err);                    /* throwIO : e -> IO a (typed failure) */

/* do-kernel completion channel (§18.7, §18.8): a do-scope whose `defer` actions
 * run on EVERY exit path — normal completion, typed fail, early `return`, loop
 * `break`/`continue`, and interruption — in masked LIFO order (§32.2.19, never a
 * host finalizer per §34.4.1).  The codegen wraps each IO do-block in krt2_doscope. */
KValue *krt2_doscope(KValue *body);                 /* a supervised do-scope        */
KValue *krt2_defer(KValue *action);                 /* register an exit action      */
KValue *krt2_return(KValue *value);                 /* early return from the fiber  */
KValue *krt2_while(KValue *condIO, KValue *bodyIO); /* loop while condIO is True    */
KValue *krt2_break(void);                           /* break the innermost loop     */
KValue *krt2_continue(void);                        /* continue the innermost loop  */
/* mutable references (§18.6.1 MonadRef) */
KValue *krt2_new_ref(KValue *init);                 /* newRef  : a -> IO (Ref a)    */
KValue *krt2_read_ref(KValue *ref);                 /* readRef : Ref a -> IO a      */
KValue *krt2_write_ref(KValue *ref, KValue *val);   /* writeRef: Ref a -> a -> IO () */

/* A cooperative safe point: decrement the current fiber's reduction budget and
 * yield if it is exhausted (also an interruption-delivery point).  Codegen MUST
 * emit this at loop back-edges and unbounded-recursion entries (§27.5A.4 /
 * DESIGN.md §6.4).  A no-op when not running inside a fiber. */
void krt2_safepoint(void);

/* ── fibers (§18.1.4) ──────────────────────────────────────────────────── */
KValue *krt2_fork(KValue *action);                  /* (IO e a) -> UIO (Fiber e a) */
KValue *krt2_fork_daemon(KValue *action);
KValue *krt2_await(KValue *fiber);                  /* Fiber e a -> UIO (Exit e a) */
KValue *krt2_join(KValue *fiber);                   /* Fiber e a -> IO e a          */
KValue *krt2_interrupt(KValue *fiber);              /* request + wait for done      */
KValue *krt2_interrupt_fork(KValue *fiber);         /* request, no wait             */
KValue *krt2_interrupt_as(KValue *cause, KValue *fiber);      /* explicit InterruptCause */
KValue *krt2_interrupt_fork_as(KValue *cause, KValue *fiber);
KValue *krt2_fiber_id(KValue *fiber);               /* Fiber e a -> UIO FiberId     */
KValue *krt2_current_fiber_id(void);                /* UIO FiberId                  */
KValue *krt2_cede(void);                            /* UIO Unit (§18.1.5)           */

/* ── time, timers, deadlines, racing (§18.1.6) ─────────────────────────── */
KValue *krt2_now_monotonic(void);                   /* UIO Instant (ns)             */
KValue *krt2_sleep_for(KValue *dur);                /* Duration -> UIO Unit         */
KValue *krt2_sleep_until(KValue *instant);          /* Instant  -> UIO Unit         */
KValue *krt2_timeout(KValue *dur, KValue *action);  /* -> IO (TimeoutError|e) a     */
KValue *krt2_race(KValue *l, KValue *r);            /* -> IO (e|f) (RaceResult a b) */

/* ── one-shot promises (§18.1.9) ───────────────────────────────────────── */
KValue *krt2_new_promise(void);                     /* UIO (Promise e a)            */
KValue *krt2_await_promise_exit(KValue *p);         /* Promise e a -> UIO (Exit e a)*/
KValue *krt2_await_promise(KValue *p);              /* Promise e a -> IO e a        */
KValue *krt2_complete_promise(KValue *p, KValue *exit); /* -> UIO Bool (first wins) */

/* ── explicit scopes and monitors (§18.1.8) ────────────────────────────── */
KValue *krt2_new_scope(void);                       /* UIO Scope                    */
KValue *krt2_with_scope(KValue *use_fn);            /* (Scope -> IO e a) -> IO e a  */
KValue *krt2_fork_in(KValue *scope, KValue *action);/* Scope -> IO e a -> UIO Fiber */
KValue *krt2_shutdown_scope(KValue *scope);         /* UIO Unit (idempotent)        */
KValue *krt2_monitor(KValue *fiber);                /* UIO (Monitor e a)            */
KValue *krt2_await_monitor(KValue *mon);            /* UIO (Exit e a)               */
KValue *krt2_demonitor(KValue *mon);                /* UIO Unit                     */

/* ── fiber-local state (§18.1.7) ───────────────────────────────────────── */
KValue *krt2_new_fiber_ref(KValue *init);           /* a -> UIO (FiberRef a)        */
KValue *krt2_get_fiber_ref(KValue *ref);            /* FiberRef a -> UIO a          */
KValue *krt2_set_fiber_ref(KValue *ref, KValue *v); /* FiberRef a -> a -> UIO Unit  */
KValue *krt2_locally_fiber_ref(KValue *ref, KValue *v, KValue *body);

/* ── fiber identity labels (§18.1.10) ──────────────────────────────────── */
KValue *krt2_get_fiber_label(void);                 /* UIO (Option String)          */
KValue *krt2_set_fiber_label(KValue *label_opt);    /* Option String -> UIO Unit    */
KValue *krt2_locally_fiber_label(KValue *label_opt, KValue *body);

/* ── interruption, masking, resources (§18.1.11, §18.1.12) ─────────────── */
KValue *krt2_poll(void);                            /* UIO Unit (explicit ckpt)     */
KValue *krt2_uninterruptible(KValue *body);         /* IO e a -> IO e a             */
KValue *krt2_mask(KValue *f);                       /* (restore -> IO e a) -> IO e a*/
KValue *krt2_ensuring(KValue *body, KValue *fin);   /* IO e a -> IO e () -> IO e a  */
KValue *krt2_acquire_release(KValue *acq, KValue *rel, KValue *use);
KValue *krt2_blocking(KValue *body);                /* IO e a -> IO e a (rt-blocking)*/
KValue *krt2_sandbox(KValue *action);               /* expose full Cause as typed Fail */
KValue *krt2_unsandbox(KValue *action);             /* reverse of sandbox           */

/* ── STM (§18.1.13, §32.2.9, rt-shared-stm) ────────────────────────────── */
KValue *krt2_stm_pure(KValue *v);                   /* a -> STM a                   */
KValue *krt2_stm_bind(KValue *m, KValue *k);        /* STM a -> (a -> STM b) -> STM b */
KValue *krt2_new_tvar(KValue *v);                   /* a -> STM (TVar a)            */
KValue *krt2_read_tvar(KValue *tv);                 /* TVar a -> STM a              */
KValue *krt2_write_tvar(KValue *tv, KValue *v);     /* TVar a -> a -> STM Unit      */
KValue *krt2_retry(void);                           /* STM a                        */
KValue *krt2_check(KValue *b);                      /* Bool -> STM Unit             */
KValue *krt2_or_else(KValue *l, KValue *r);         /* STM a -> STM a -> STM a      */
KValue *krt2_atomically(KValue *stm);               /* STM a -> UIO a               */

/* ── atomics (§29.1, rt-atomics) ───────────────────────────────────────── */
/* `order` args are the §29.1 LoadOrder/StoreOrder/RmwOrder/CasFailureOrder
 * constructors (boxed Kappa values); see native/atomic.c for the enum mapping. */
KValue *krt2_new_atomic_ref(KValue *v);             /* a -> UIO (AtomicRef a)       */
KValue *krt2_atomic_load(KValue *order, KValue *ref);
KValue *krt2_atomic_store(KValue *order, KValue *ref, KValue *v);
KValue *krt2_atomic_exchange(KValue *order, KValue *ref, KValue *v);
KValue *krt2_atomic_compare_exchange(KValue *succ, KValue *fail,
                                     KValue *ref, KValue *expected, KValue *desired);
KValue *krt2_atomic_fetch_add(KValue *order, KValue *ref, KValue *v);
KValue *krt2_atomic_fetch_sub(KValue *order, KValue *ref, KValue *v);
KValue *krt2_atomic_fetch_and(KValue *order, KValue *ref, KValue *v);
KValue *krt2_atomic_fetch_or(KValue *order, KValue *ref, KValue *v);
KValue *krt2_atomic_fetch_xor(KValue *order, KValue *ref, KValue *v);

/* ── Exit / Cause construction (§28, §32.2.12) ─────────────────────────── */
KValue *krt2_success(KValue *v);                    /* Exit: Success v              */
KValue *krt2_failure(KValue *cause);                /* Exit: Failure cause          */
KValue *krt2_cause_fail(KValue *err);               /* Cause: Fail e                */
KValue *krt2_cause_interrupt(KValue *interrupt_cause);
KValue *krt2_cause_defect(KValue *defect_info);
KValue *krt2_cause_both(KValue *a, KValue *b);      /* concurrent composition       */
KValue *krt2_cause_then(KValue *a, KValue *b);      /* sequential composition       */
/* Build an InterruptCause from a tag name ("Requested"/"ScopeShutdown"/
 * "TimedOut"/"RaceLost"/"External") and an Option FiberId (`by`). */
KValue *krt2_interrupt_cause(const char *tag, KValue *by_opt);

/* ── tracing / diagnostics (§32.2.11) ──────────────────────────────────── */
/* Dump live fibers (id, scope, parent, status, mask, interrupt-pending, wait
 * reason, label, terminal Exit) and per-agent runnable/parked counts to `out`. */
void krt2_dump(void *out /* FILE* */);

/* ── advertised runtime capability set (§27.6) ─────────────────────────── */
/* NUL-terminated array; the backend's Capabilities.hs must agree once wired.
 * v1 advertises FIVE flags: rt-core, rt-parallel, rt-shared-stm, rt-blocking,
 * rt-atomics.  rt-multishot-effects is STAGED to v2 behind a real gate (the
 * static §32.2.20 escape check + per-use clone protocol + native reachability
 * rejection do not exist yet) — see REVIEW.md "Capability staging".  The pure
 * __EffOp closure encoding (multishot-capable for pure effects) still works;
 * only the multishot-with-IO-segments contract is deferred. */
extern const char *const KRT2_CAPABILITIES[]; /* rt-core, rt-parallel, rt-shared-stm,
                                               * rt-blocking, rt-atomics, NULL */

#ifdef __cplusplus
}
#endif
#endif /* KAPPART2_H */
