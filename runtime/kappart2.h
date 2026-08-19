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
 * worker thread.  See DESIGN.md §5 for the CK-machine and §6 for the current
 * M:N FIFO scheduler; per-worker work stealing is future performance work.
 *
 * THREADING.  The runtime is multicore (capability rt-parallel): N worker
 * threads run runnable fibers in parallel, and a single libuv reactor thread
 * drives async I/O and timers.  Blocking native calls park their fiber and run
 * on an off-worker lane (capability rt-blocking).  All threads are registered
 * with Boehm GC.  Ordinary refs (K_REF/var) are NOT cross-fiber synchronization
 * (§32.2.10); cross-fiber coordination uses await/join, scopes/monitors,
 * promises, STM, or atomics.
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
#define KRT2_KIND_RESUMPTION "rt.Resumption" /* §18.1.21 captured one-shot k */

/* §18.1.21/.22 effect-handler nodes (Stage 4a): build the scheduler actions a
 * `handle`/`perform`/`resume` lowers to (see rt.c for the operational model). */
KValue *krt2_handle(KValue *deep, KValue *label, KValue *ret, KValue *ops, KValue *body);
KValue *krt2_perform(KValue *label, KValue *op, KValue *payload);
KValue *krt2_resume(KValue *k, KValue *value);

/* ── lifecycle ─────────────────────────────────────────────────────────── */

/* Initialize the GC and runtime state.  The worker pool and reactor start
 * lazily on the first krt2_run_main; blocking threads start on demand.
 * `nworkers <= 0` selects min(ncpu, RT_MAX_WORKERS) (override: KAPPA_RT_WORKERS).
 * Idempotent-safe to call once at process start (after krt_init from kappart). */
Rt *krt2_new(int nworkers);

/* Run `action` (an IO computation) as the MAIN fiber on its root scope, drive
 * the scheduler until the main fiber terminates, then return its terminal
 * `Exit e a` value (Success a | Failure (Cause e), §28).  Shuts down the run's
 * root scope (interrupting/awaiting any still-live children), but keeps the
 * worker pool and reactor alive for later calls.  This is what generated `main`
 * calls. */
KValue *krt2_run_main(KValue *action);

/* Final process teardown: stop the reactor and join workers.  Normal process
 * exit invokes this automatically.  Embedders may call it only after all
 * krt2_run_main calls and native blocking work have quiesced. */
void krt2_shutdown(Rt *rt);

/* 1 if a terminal `Exit` is Success, 0 if Failure.  Used by generated `main` for
 * the process exit code (kept here so the generated C carries no kctor_is). */
int krt2_exit_is_success(KValue *exit);

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
KValue *krt2_reraise(KValue *cause);                /* __reraiseCause : Cause e -> IO a (re-raise as-is) */
/* §18.1.4 reason-carrying finalizers (ZIO onExit/onInterrupt): run body, then on
 * exit apply the handler to the reconstructed Exit (onExit, EVERY exit) or the
 * InterruptCause (onInterrupt, ONLY on interrupt).  The body's result is kept. */
KValue *krt2_on_exit(KValue *body, KValue *handler);      /* IO e a -> (Exit e a -> IO e ()) -> IO e a */
KValue *krt2_on_interrupt(KValue *body, KValue *handler); /* IO e a -> (InterruptCause -> IO e ()) -> IO e a */

/* do-kernel completion channel (§18.7, §18.8): a do-scope whose `defer` actions
 * run on EVERY exit path — normal completion, typed fail, early `return`, loop
 * `break`/`continue`, and interruption — in masked LIFO order (§32.2.19, never a
 * host finalizer per §34.4.1).  The codegen wraps each IO do-block in krt2_doscope. */
KValue *krt2_doscope(KValue *body);                 /* a supervised do-scope        */
KValue *krt2_defer(KValue *action);                 /* register an exit action      */
KValue *krt2_return(KValue *value);                 /* early return from the fiber  */
KValue *krt2_retscope(KValue *body);                /* delimit `return` to body     */
KValue *krt2_while(KValue *condIO, KValue *bodyIO); /* loop while condIO is True    */
KValue *krt2_break(void);                           /* break the innermost loop     */
KValue *krt2_continue(void);                        /* continue the innermost loop  */
/* mutable references (§18.6.1 MonadRef) */
KValue *krt2_new_ref(KValue *init);                 /* newRef  : a -> IO (Ref a)    */
KValue *krt2_read_ref(KValue *ref);                 /* readRef : Ref a -> IO a      */
KValue *krt2_write_ref(KValue *ref, KValue *val);   /* writeRef: Ref a -> a -> IO () */

/* §32.2.6 safe point for a codegen-emitted NATIVE loop.  Returns 1 iff the loop
 * should ABORT to let the runtime deliver a pending interrupt at this back-edge
 * (interrupt_pending && effective mask state is Interruptible) — the generated loop
 * then aborts through the scalar-worker boundary so the CK-machine delivers
 * before later source effects run.  Returns 0 when masked (suppression holds) or off any fiber.  Codegen
 * emits this at native loop back-edges, counter-gated so the hot unboxed loop is
 * not slowed (§32.2.6 / DESIGN.md §6.4).  In-place CK loops (OP_WHILE/KK_LOOP)
 * get their safe point + fairness cede inside the runtime, not via this call. */
int krt2_safepoint(void);
/* Called after a scalar worker reports KRT2_SCALAR_ABORT. This does not return
 * to generated Kappa code; it unwinds to the active fiber-step boundary so the
 * scheduler delivers the pending interrupt before later source effects run. */
void krt2_scalar_abort(void);
/* §18.7/§19.5/§32.2.6: register a dynamically-active exit action for generated
 * synchronous safe-point aborts. The returned token is captured by the ordinary
 * finalizer wrapper; normal finalization and abort-drain both mark it inactive
 * so the action runs at most once. */
KValue *krt2_abort_exit_push(KValue *exit_action);
KValue *krt2_abort_exit_finalizer(KValue *token);
/* Legacy synchronous do-code still owns some C-local defer frames for shapes not
 * yet expressed as OP_DOSCOPE trees. Drain one frame through the same
 * reason/cause composition rules as the CK finalizer sequence, and set *count to
 * zero so later control paths cannot run the actions twice. */
KValue *krt2_run_legacy_finalizers(KValue *primary, KValue **defers, int *count);

/* How many native scalar-loop iterations between krt2_safepoint() calls (fix SP).
 * The emitted loop decrements a counter each iteration and only calls
 * krt2_safepoint when it reaches 0, so the per-iteration cost in the hot unboxed
 * loop is a register decrement + predictable branch — the function call (and the
 * interrupt check) is amortized over QUANTUM iterations.  Large enough to be free
 * in the steady state, small enough that interrupt responsiveness stays bounded. */
#ifndef KRT2_SP_QUANTUM
#define KRT2_SP_QUANTUM 65536
#endif

/* Scalar-worker side-channel values.  1 is the historical "rerun boxed" escape
 * for int overflow/wrong unbox; 2 is a runtime safe-point abort and must not
 * fall back to boxed computation. */
#define KRT2_SCALAR_OVERFLOW 1
#define KRT2_SCALAR_ABORT    2

/* ── fibers (§18.1.4) ──────────────────────────────────────────────────── */
KValue *krt2_fork(KValue *action);                  /* (IO e a) -> UIO (Fiber e a) */
KValue *krt2_fork_daemon(KValue *action);
KValue *krt2_await(KValue *fiber);                  /* Fiber e a -> UIO (Exit e a) */
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
KValue *krt2_timeout(KValue *dur, KValue *action);  /* -> IO (TimeoutError|e) a     */
KValue *krt2_race(KValue *l, KValue *r);            /* -> IO (e|f) (RaceResult a b) */

/* ── one-shot promises (§18.1.9, §18.11) ───────────────────────────────── */
KValue *krt2_new_promise(void);                     /* UIO (Promise e a)            */
KValue *krt2_await_promise_exit(KValue *p);         /* Promise e a -> UIO (Exit e a)*/
KValue *krt2_complete_promise(KValue *p, KValue *exit); /* -> UIO Bool (first wins) */
KValue *krt2_poll_promise(KValue *p);               /* §18.11 -> UIO (Option (Exit e a)) (non-blocking) */
KValue *krt2_is_done_promise(KValue *p);            /* §18.11 -> UIO Bool (non-blocking)                */

/* ── fiber-local state (§18.1.7; copy-on-fork at fork) ─────────────────── */
KValue *krt2_new_fiber_ref(KValue *init);                   /* a -> UIO (FiberRef a)        */
KValue *krt2_get_fiber_ref(KValue *ref);                    /* FiberRef a -> UIO a          */
KValue *krt2_set_fiber_ref(KValue *ref, KValue *val);       /* FiberRef a -> a -> UIO Unit  */
KValue *krt2_modify_fiber_ref(KValue *ref, KValue *fn);     /* FiberRef a -> (a->a) -> UIO a (atomic) */
KValue *krt2_locally_fiber_ref(KValue *ref, KValue *val, KValue *body); /* install for body's extent */

/* ── explicit scopes and monitors (§18.1.8) ────────────────────────────── */
KValue *krt2_new_scope(void);                       /* UIO Scope                    */
KValue *krt2_with_scope(KValue *use_fn);            /* (Scope -> IO e a) -> IO e a  */
KValue *krt2_fork_in(KValue *scope, KValue *action);/* Scope -> IO e a -> UIO Fiber */
KValue *krt2_shutdown_scope(KValue *scope);         /* UIO Unit (idempotent)        */
KValue *krt2_monitor(KValue *fiber);                /* UIO (Monitor e a)            */
KValue *krt2_await_monitor(KValue *mon);            /* UIO (Exit e a)               */
KValue *krt2_demonitor(KValue *mon);                /* UIO Unit                     */

/* ── Planned ABI — NOT yet implemented in the archive ──────────────────────
 * These entry points are part of the intended kappart2 surface but have no C
 * definition yet, so they are NOT declared here (a declaration without a
 * definition is a link-fail trap, and the capability check would pass while the
 * symbol is absent).  Some are reached today via the Kappa-level prelude over
 * implemented primitives (for example `join`/`awaitPromise` over `await` plus
 * a `match`), and the krt2_* C ABI for each pending surface lands as that
 * surface is wired.  See
 * docs/PRIMITIVES.md for the plan:
 *   - krt2_join, krt2_await_promise            (Fiber/Promise -> IO e a: re-raise the Cause)
 *   - krt2_sleep_until                          (Instant -> UIO Unit)
 *   - krt2_get/set/locally_fiber_label          (§18.1.10: needs a per-fiber label field)
 * §18.1.7 FiberRef (new/get/set/modify/locally) + copy-on-fork is implemented
 * (see the fiber-local-state declarations above; PRIMITIVES.md ADD #4 — DONE).
 *   - krt2_sandbox, krt2_unsandbox              (§18.1.2: expose/absorb the full Cause)
 */

/* ── interruption, masking, resources (§18.1.11, §18.1.12) ─────────────── */
KValue *krt2_poll(void);                            /* UIO Unit (explicit ckpt)     */
KValue *krt2_uninterruptible(KValue *body);         /* IO e a -> IO e a             */
KValue *krt2_mask(KValue *f);                       /* (restore -> IO e a) -> IO e a*/
KValue *krt2_uninterruptible_mask(KValue *f);       /* uninterruptible mask + restore*/
KValue *krt2_ensuring(KValue *body, KValue *fin);   /* IO e a -> IO e () -> IO e a  */
KValue *krt2_acquire_release(KValue *acq, KValue *rel, KValue *use);
KValue *krt2_blocking(KValue *body);                /* IO e a -> IO e a (rt-blocking)*/

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
/* Each `order` arg is a small Integer CODE — the §29.1 canonical declaration-
 * order index of the LoadOrder/StoreOrder/RmwOrder/CasFailureOrder constructor
 * (computed by the std.atomic prelude, NOT the codegen-assigned ctor tag id);
 * see atomic.c for the memory_order mapping.  These are wired into both backends
 * via the kpf_io___atomic* wrappers in atomic.c (knative_sat IO prims). */
KValue *krt2_new_atomic_ref(KValue *v);             /* a -> UIO (AtomicRef a)       */
KValue *krt2_atomic_load(KValue *order, KValue *ref);
KValue *krt2_atomic_store(KValue *order, KValue *ref, KValue *v);
KValue *krt2_atomic_exchange(KValue *order, KValue *ref, KValue *v);
/* Returns the WITNESSED old value (== expected on success); the std.atomic
 * prelude reconstructs Exchanged/NotExchanged from witnessed==expected so the
 * runtime never stamps a codegen-assigned result-constructor tag. */
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
/* Number of not-yet-DONE fibers in the strong root set (rt->all).  A test uses
 * this to assert the persistent runtime does not leak fibers across run_main. */
long krt2_live_fiber_count(void);

/* ── advertised runtime capability set (§27.6) ─────────────────────────── */
/* NUL-terminated array; the backend's Capabilities.hs consumes the
 * binding-relevant subset. v1 advertises rt-core, rt-parallel, rt-blocking,
 * rt-shared-stm, rt-atomics. rt-multishot-effects is staged behind a real gate
 * (the static §32.2.20 escape check + per-use clone protocol + native
 * reachability rejection do not exist yet). The pure __EffOp closure encoding
 * (multishot-capable for pure effects) still works; only the
 * multishot-with-IO-segments contract is deferred. */
extern const char *const KRT2_CAPABILITIES[]; /* rt-core, rt-parallel,
                                               * rt-blocking, rt-shared-stm,
                                               * rt-atomics, NULL */

#ifdef __cplusplus
}
#endif
#endif /* KAPPART2_H */
