/* internal.h — private structures shared across the kappart2 C sources.
 *
 * NOT a public header (the public ABI is include/kappart2.h).  See DESIGN.md
 * for the architecture and REVIEW.md for why the concurrency protocols look the
 * way they do.  v1 SCOPE: this implements the validated SPINE — the M:N
 * scheduler, the stackless CK-machine, fork/await/cede, promises, and libuv
 * timers (sleep).  STM, scopes/supervision, interruption/masking, atomics,
 * race/timeout, and the blocking lane are the well-specified next increments.
 *
 * Two concurrency protocols, applied uniformly (REVIEW.md B3, B4):
 *   1. PARK/WAKE.  A waitable object (Fiber, Promise) owns a mutex.  A fiber
 *      that blocks checks-and-enqueues itself onto the object's waiter list
 *      UNDER that mutex; the waker snapshots-and-clears the list UNDER the same
 *      mutex.  Both sides holding the lock closes the lost-wakeup window with no
 *      futex/CAS gymnastics.  The run queue is a mutex+condvar FIFO (the
 *      proven-correct shape of the worker-park handshake; a Chase-Lev
 *      work-stealing deque is a perf upgrade, not a correctness need).
 *   2. GC LIVENESS.  Boehm scans the static data segment, so everything
 *      reachable from the static `g_rt` pointer is traced.  Every not-yet-DONE
 *      fiber is held in rt->all (an explicit strong root set); all scheduler
 *      nodes (run-queue nodes, waiters, I/O requests) are GC_MALLOC'd and
 *      reachable from Rt.  libuv-internal memory (timer->data, &c.) is NOT a GC
 *      root, so a fiber parked only in a libuv handle stays live via rt->all.
 */
#ifndef KRT2_INTERNAL_H
#define KRT2_INTERNAL_H

#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <uv.h>

#include "kappart2.h" /* -> kappart.h: KValue, kctor/kfgn/kapp/..., GC via kgc_alloc */

/* ── action-node opcodes ────────────────────────────────────────────────
 * An IO action is a K_CTOR whose `tagid` is one of these opcodes (a private
 * range far above codegen-assigned user ctor ids, which start at
 * KCT_USER_BASE=16), and whose args are the operands.  The CK-machine
 * dispatches on kctor_tagid(action).  This needs NO new KTag (REVIEW.md M22). */
enum {
  KRT2_OP_BASE = 0x40000000,
  OP_PURE = KRT2_OP_BASE, /* [v]              ioPure                       */
  OP_BIND,                /* [m, kclo]        ioBind  (kclo : a -> IO b)   */
  OP_THEN,                /* [m, next]        ioThen                       */
  OP_CATCH,               /* [body, hclo]     catchIO (hclo : e -> IO a)   */
  OP_THROW,               /* [err]            throwIO                      */
  OP_RERAISE,             /* [cause]          __reraiseCause (full Cause)  */
  OP_PRINT,               /* [str]            printString  (no newline)    */
  OP_PRINTLN,             /* [str]            printlnString                */
  OP_FORK,                /* [action]         fork        -> Fiber         */
  OP_FORK_DAEMON,         /* [action]         forkDaemon  -> Fiber         */
  OP_AWAIT,               /* [fiber]          await       -> Exit          */
  OP_CEDE,                /* []               cede                         */
  OP_SLEEP,               /* [durNanos:Int]   sleepFor                     */
  OP_NOW,                 /* []               nowMonotonic -> Instant      */
  OP_NEW_PROMISE,         /* []               newPromise  -> Promise       */
  OP_COMPLETE_PROMISE,    /* [p, exit]        completePromise -> Bool      */
  OP_AWAIT_PROMISE_EXIT,  /* [p]              awaitPromiseExit -> Exit     */
  OP_CURRENT_FIBER_ID,    /* []               currentFiberId -> Int        */
  OP_FIBER_ID,            /* [fiber]          fiberId -> Int               */
  /* interruption + masking (§18.1.4, §18.1.12) */
  OP_INTERRUPT,           /* [fiber]          interrupt (request + wait)   */
  OP_INTERRUPT_FORK,      /* [fiber]          interruptFork (no wait)      */
  OP_UNINTERRUPTIBLE,     /* [body]           uninterruptible body         */
  OP_POLL,                /* []               poll (deliver even if masked)*/
  OP_MASK,                /* [f]              mask: f gets `restore` (§18.1.12) */
  OP_RESTORE,             /* [act, outerDepth] run act at the mask-entry interruptibility */
  /* structured concurrency (§18.1.8, §32.2.3) */
  OP_NEW_SCOPE,           /* []               newScope -> Scope            */
  OP_FORK_IN,             /* [scope, action]  forkIn -> Fiber              */
  OP_SHUTDOWN_SCOPE,      /* [scope]          shutdownScope (parks)        */
  OP_MONITOR,             /* [fiber]          monitor -> Monitor           */
  OP_AWAIT_MONITOR,       /* [monitor]        awaitMonitor -> Exit         */
  /* do-kernel completion channel (§18.7, §18.8, §30.2.2.6) */
  OP_DOSCOPE,             /* [body]           a do-scope: its defers run on
                           *                  EVERY exit (normal/fail/return/
                           *                  break/continue/interrupt) LIFO   */
  OP_DEFER,               /* [action]         register an exit action on the
                           *                  innermost do-scope (§18.7)        */
  OP_RETURN,              /* [value]          early return from the fiber       */
  OP_RETSCOPE,            /* [body]           DELIMIT `return`: run body; an
                           *                  OP_RETURN inside it delivers its
                           *                  value HERE (as this scope's result)
                           *                  instead of escaping to the fiber.
                           *                  Used to scope a do-block VALUE's
                           *                  `return` to the do-block (§18.8) when
                           *                  the block is CPS-lowered into a
                           *                  larger continuation chain.            */
  OP_WHILE,               /* [condIO, bodyIO] a loop; body is a do-scope        */
  OP_BREAK,               /* []               break the innermost loop          */
  OP_CONTINUE,            /* []               continue the innermost loop        */
  /* mutable references (§18.6.1 MonadRef; synchronous, single-fiber ordering) */
  OP_NEW_REF,             /* [init]           newRef -> Ref                      */
  OP_READ_REF,            /* [ref]            readRef -> a                        */
  OP_WRITE_REF,           /* [ref, val]       writeRef -> Unit                    */
  OP_TRY_EXIT,            /* [fiber]          non-blocking: Option Exit (DONE?)   */
  OP_ATOMICALLY,          /* [stm]            run an STM transaction (§18.1.13)    */
  /* §18.1.21/.22 algebraic-effect handlers as prompt frames (Stage 4a).  These
   * run an `Eff` computation ON the scheduler so a handler clause can park —
   * the unification of the §30.2.2.7 OpCall tree with the CK-machine Cont
   * chain.  ONE-SHOT only; multi-shot is gated behind rt-multishot (absent). */
  OP_HANDLE,              /* [deep, label, ret, ops, body]  install a KK_HANDLER
                           *                  prompt frame and run `body`         */
  OP_PERFORM,             /* [label, op, payload]  outward-search f->k for the
                           *                  nearest matching KK_HANDLER, capture
                           *                  the op-site->handler Cont sub-chain
                           *                  as the resumption, run the clause    */
  OP_RESUME,              /* [k, value]       splice the captured sub-chain back
                           *                  onto f->k and deliver `value`        */
  /* §18.1.4 reason-carrying finalizers (ZIO onExit/onInterrupt).  Unlike a plain
   * `defer`, these run a HANDLER applied to the scope's terminal Exit/cause.  An
   * OP_ONEXIT_FIN/OP_ONINT_FIN node is REGISTERED on the enclosing do-scope's
   * ExitStack (it never runs as an ordinary action); when the masked-LIFO
   * KK_FINSEQ drain reaches it, it reconstructs the Exit from the saved Reason
   * and substitutes the handler application.  onInterrupt fires ONLY when the
   * scope exits via interrupt; onExit fires on EVERY exit. */
  OP_ONEXIT_FIN,          /* [handler]        onExit:      handler : Exit e a -> IO e' Unit */
  OP_ONINT_FIN,           /* [handler]        onInterrupt: handler : InterruptCause -> IO e' Unit */
  /* §18.1.7 FiberRef ops (fiber-local cells with copy-on-fork).  newFiberRef
   * allocates a cell id + records its init; get/set/modify index the current
   * fiber's FiberRef map (snapshotted into a child at fork). */
  OP_NEW_FIBER_REF,       /* [init]           newFiberRef -> FiberRef a            */
  OP_GET_FIBER_REF,       /* [ref]            getFiberRef -> a                     */
  OP_SET_FIBER_REF,       /* [ref, val]       setFiberRef -> Unit                  */
  OP_MODIFY_FIBER_REF,    /* [ref, f]         modifyFiberRef: atomic get-apply-set -> b */
  /* §18.11 Promise non-blocking peek. */
  OP_POLL_PROMISE,        /* [p]              poll  -> Option (Exit e a)           */
  OP_IS_DONE_PROMISE,     /* [p]              isDone -> Bool                       */
  OP_LAST
};

/* STM action opcodes (a separate node family interpreted by stm_run, never by
 * fiber_step).  An STM action is a pure transaction tree; the only suspension is
 * `retry`, handled at the OP_ATOMICALLY boundary. */
enum {
  KRT2_STM_BASE = 0x40001000,
  STM_PURE = KRT2_STM_BASE, /* [v]            STM.pure                            */
  STM_BIND,                 /* [m, k]         STM bind (k : a -> STM b)            */
  STM_READ,                 /* [tvar]         readTVar                            */
  STM_WRITE,                /* [tvar, val]    writeTVar                           */
  STM_RETRY,                /* []             retry                               */
  STM_ORELSE,               /* [l, r]         orElse                              */
  STM_NEW                   /* [init]         newTVar                             */
};

/* Reason kinds carried by an abnormal unwind through the continuation.
 * RK_DRAIN is internal-only (§32.2.20/.21): it walks an ABANDONED captured
 * resumption slice running its KK_DOSCOPE exit actions masked-LIFO, matching no
 * KK_CATCH/KK_LOOP/KK_RETSCOPE special arm (so they fall through transparently)
 * and terminating at the slice's KK_ABANDEND frame instead of finishing the
 * fiber.  It never originates from user control flow. */
enum { RK_NORMAL, RK_FAIL, RK_RETURN, RK_BREAK, RK_CONTINUE, RK_INTERRUPT, RK_RERAISE, RK_DRAIN };

/* Constructor-id used for the prelude-shaped result ctors (Success/Failure/...).
 * Pattern matching in harnesses is name-based (kctor_is), so the id is inert. */
#define KRT2_RESULT_ID 0

/* ── continuation frames (the stackless "K" of the CK-machine) ──────────── */
typedef struct Cont Cont;
typedef enum {
  KK_DONE, KK_BIND, KK_THEN, KK_CATCH,
  KK_POPMASK,   /* lower the fiber's mask_depth by 1 on the way out (uninterruptible) */
  KK_SETMASK,   /* restore mask_depth to a stored level on the way out (mask/restore) */
  KK_DOSCOPE,   /* a do-scope boundary: run its exit actions on any way out       */
  KK_FINSEQ,    /* run a do-scope's exit actions LIFO, then resume a saved Reason  */
  KK_LOOP,      /* a loop boundary: break/continue target it                      */
  KK_RETSCOPE,  /* a `return` boundary: RK_RETURN delivers its value here (§18.8)  */
  KK_HANDLER,   /* §18.1.21 an effect-handler prompt: `perform` searches f->k for
                 * the nearest matching one; the captured op-site->handler Cont
                 * sub-chain becomes the resumption (Stage 4a, one-shot)          */
  KK_ABANDON,   /* §32.2.20 sits BENEATH a general-path handler clause, carrying
                 * the severed Resumption (Cont.aux).  When the clause completes
                 * (deliver/unwind reach it) WITHOUT having resumed, it drains the
                 * severed slice's do-scope exit actions before the clause result
                 * proceeds; if the clause DID resume it is transparent.          */
  KK_ABANDEND   /* §32.2.20 terminal frame spliced onto the severed slice's tail:
                 * when the RK_DRAIN walk reaches it the slice's defers have run,
                 * so it restores the clause's continuation + cur_exits and resumes
                 * the clause's original (saved) reason.                          */
} KKind;
struct Cont {
  KKind   kind;
  KValue *a;    /* KK_BIND/KK_CATCH: closure; KK_LOOP: the loop spec [cond,body];
                 * KK_HANDLER: the installed effect-label VALUE (matched by id)    */
  void   *aux;  /* KK_DOSCOPE: this scope's ExitStack*; KK_FINSEQ: FinSeq*;
                 * KK_HANDLER: this prompt's Handler*                              */
  void   *aux2; /* KK_DOSCOPE: the saved (parent) ExitStack* to restore on exit;
                 * KK_HANDLER: the saved cur_exits to reinstate when the prompt is
                 * removed (the handler clause runs OUTSIDE the body's do-scopes)  */
  Cont   *next;
};

/* §18.1.21 an installed effect handler: the return clause, the per-op clause
 * record, and the deep-vs-shallow reinstall flag.  Carried on a KK_HANDLER
 * Cont frame (the label value itself is Cont.a, matched by ctor-id identity). */
typedef struct Handler {
  KValue *ret;   /* the `case return x -> ...` clause (a -> Eff res)               */
  KValue *ops;   /* the per-operation clause record (op -> payload -> k -> Eff)    */
  int     deep;  /* 1 = deep (k reinstalls this handler around the resumption)     */
} Handler;

/* A do-scope's stack of registered exit actions (defer/using/finally), run LIFO
 * on every way out of the scope (§18.7, §32.2.19).  GC_MALLOC'd. */
typedef struct { KValue **items; int n, cap; } ExitStack;

/* ── fibers ─────────────────────────────────────────────────────────────── */
typedef enum { F_RUNNABLE, F_RUNNING, F_PARKED, F_DONE } FStatus;

typedef struct Waiter Waiter;   /* a parked fiber on some object's waiter list */
typedef struct Fiber  Fiber;
typedef struct Scope  Scope;
typedef struct ScopeLink ScopeLink;

/* A parked fiber on a waiter list.  `want_exit` selects the resume value when
 * the awaited entity terminates: 1 => the terminal Exit (await/awaitPromise/
 * awaitMonitor); 0 => Unit (interrupt-wait, shutdownScope-wait). */
struct Waiter { Fiber *f; int want_exit; Waiter *next; };

/* A child's membership node in its supervision scope's child set (§32.2.3). */
struct ScopeLink { Fiber *f; ScopeLink *prev, *next; };

/* §18.1.7 a fiber's private FiberRef overrides: a flat array indexed by cell id
 * (ids are dense, allocated sequentially by newFiberRef).  vals[id]==NULL means
 * "no override" (the cell's recorded init value is used).  The whole array is
 * deep-copied into a child at fork (copy-on-fork independence). */
typedef struct FiberLocals { KValue **vals; int n; } FiberLocals; /* n = slots allocated */

struct Fiber {
  uint64_t        id;
  _Atomic int     status;       /* FStatus */
  KValue         *cur;          /* the action currently being stepped         */
  Cont           *k;            /* the continuation stack                     */
  KValue         *exit;         /* terminal Exit (Success v | Failure cause)  */
  Waiter         *waiters;      /* fibers parked in `await` on THIS fiber     */
  pthread_mutex_t lock;         /* guards status/waiters/exit at termination  */
  int             daemon;       /* forkDaemon (no structured attachment)      */
  /* interruption + masking (§18.1.4, §18.1.12) */
  _Atomic int     interrupt_pending;
  KValue         *interrupt_cause;   /* the InterruptCause value (set under lock) */
  uint32_t        mask_depth;        /* 0 == interruptible                       */
  /* §32.2.5 interruption-point gate (fix 2).  A pending interrupt becomes
   * observable only AT an interruption point — a runtime suspension/resume
   * (sleep/await/STM-retry/cede) or an explicit poll — NOT at a mask-region exit.
   * Set to 1 each time the fiber (re-)enters fiber_step from the run queue (a fork
   * resume or a park wake); cleared after the first delivery check of that turn.
   * So `pending && mask_depth==0 && resumed` is true ONLY on the genuine resume
   * turn — dropping mask_depth to 0 mid-step (KK_POPMASK/KK_SETMASK) no longer
   * makes the next non-suspending step a delivery point (the masked-sleep
   * suppression bug §18.1.12/§32.2.5).  OP_POLL delivers regardless of this flag. */
  int             resumed;
  ExitStack      *cur_exits;         /* the innermost do-scope's exit-action stack
                                      * (where `defer` registers); NULL outside a
                                      * do-scope.  §18.7 */
  /* §32.2.21 cause symmetry (fix 1): the AbandonEnd* of the abandonment drain
   * currently in progress, or NULL when not draining.  A drained do-scope's
   * finseq reads it to seed its compose-primary with the running clause reason
   * (so cleanup failures fold left-associatively, matching ordinary scope exit)
   * and writes the composed reason back into it.  Saved/restored across NESTED
   * drains (the H1 recursion) at begin_abandon_drain / KK_ABANDEND. */
  void           *drain_ae;
  struct TVar   **stm_reads;         /* TVars this fiber is currently retry-parked on;
                                      * unlinked on re-entry to `atomically` so a
                                      * moved-on fiber leaves no stale watchers (STM
                                      * review MAJOR). */
  int             stm_nreads;
  /* structured concurrency: the scope this fiber is ATTACHED to (its parent's
   * scope at fork), and its O(1) membership node therein. */
  Scope          *att_scope;
  ScopeLink      *att_link;
  /* the scope NEW child forks of this fiber attach to (its current scope). */
  Scope          *cur_scope;
  /* §18.1.7 this fiber's FiberRef overrides (NULL until first setFiberRef);
   * snapshotted into a child at fork so parent/child updates are independent. */
  FiberLocals    *locals;
  /* §32.2.5 sleep-timer dedup (fix S2): the active uv_timer for THIS fiber's
   * current sleep park, owned exclusively by the REACTOR thread (start_sleep
   * sets it; sleep_timer_cb / cancel_sleep clear it) — workers never deref it.
   * `sleep_armed` is the worker-visible mirror: set when a sleep is submitted,
   * cleared when the timer fires or the sleep is abandoned, so the abandonment
   * path can route a cancel without touching libuv.  Without the dedup, a masked
   * sleep woken by an interrupt re-armed a FRESH timer and orphaned the original,
   * whose later callback could CAS-win an unrelated park and spuriously resume it. */
  void           *sleep_timer;       /* reactor-owned: the active SleepTimer*, or NULL */
  _Atomic int     sleep_armed;       /* worker-visible: a sleep timer may be live      */
  /* doubly-linked membership in rt->all (the strong GC root set) */
  Fiber          *all_prev, *all_next;
};

/* A supervision scope (§18.1.8, §32.2.3): a set of attached, not-yet-terminated
 * child fibers, plus fibers parked waiting for it to drain (shutdownScope /
 * withScope exit).  Exposed to Kappa as an opaque K_FGN handle. */
struct Scope {
  pthread_mutex_t lock;
  ScopeLink      *children;     /* attached, not-yet-DONE children            */
  _Atomic long    live;         /* count of attached not-DONE children        */
  _Atomic int     shutting;     /* shutdownScope has begun                     */
  Waiter         *drain_waiters;/* fibers parked until live hits 0             */
  pthread_cond_t  drain_cv;     /* host-side bounded drain wait (fix 1, R2): the
                                 * run_main thread — NOT a fiber — parks here on
                                 * the daemon scope, woken when live hits 0 under
                                 * a draining scope; see krt2i_scope_drain_bounded */
};

/* A monitor: one-way observation of a target fiber's terminal Exit (§18.1.8).
 * Exposed as an opaque K_FGN handle; dropping it does not affect the target. */
typedef struct Monitor { Fiber *target; } Monitor;

/* ── STM (§18.1.13, §32.2.9, rt-shared-stm) ─────────────────────────────── */
/* A versioned value box: immutable, GC_MALLOC'd, atomically swapped into a TVar
 * on commit so a single acquire-load yields a consistent (value, version) pair
 * (REVIEW.md M16 — no torn old-value/new-version snapshot). */
typedef struct { KValue *val; uint64_t version; } VBox;
struct TVar {
  _Atomic(VBox *) box;       /* current {value, version}                          */
  Waiter         *watchers;  /* fibers parked in `retry` that read this TVar       */
};                            /* guarded by the global STM commit mutex (stm.c)    */

/* The atomically handler (stm.c), dispatched from fiber_step on OP_ATOMICALLY.
 * Returns 1 if the transaction committed (value placed in f->cur via pure), 0 if
 * the fiber parked on `retry`. */
int     krt2i_op_atomically(Rt *rt, Fiber *f, KValue *stm);

/* ── promises (§18.1.9) ─────────────────────────────────────────────────── */
typedef struct Promise {
  _Atomic int     completed;
  KValue         *exit;         /* the single-assignment terminal Exit        */
  Waiter         *waiters;
  pthread_mutex_t lock;
} Promise;

/* ── run queue (mutex+condvar FIFO) ─────────────────────────────────────── */
typedef struct RQNode { Fiber *f; struct RQNode *next; } RQNode;

/* ── reactor I/O requests (worker -> reactor, drained on the uv_async cb) ── */
/* IO_CANCEL_SLEEP (fix S2): stop+close f's active sleep timer on the reactor
 * thread (handle ops are reactor-confined).  Submitted when a sleep park is
 * ABANDONED by an interrupt (masked re-park OR unmasked unwind) so the original
 * timer cannot fire later and spuriously resume an unrelated park. */
typedef enum { IO_SLEEP, IO_CANCEL_SLEEP } IoOp;
typedef struct IoReq { IoOp op; Fiber *f; uint64_t nanos; struct IoReq *next; } IoReq;

/* ── the runtime ────────────────────────────────────────────────────────── */
struct Rt {
  int             nworkers;
  pthread_t      *workers;
  int             workers_started;  /* §1 persistent runtime: the worker pool +
                                     * reactor are spun up ONCE (first run_main)
                                     * and kept alive across every subsequent
                                     * run_main; only krt2_shutdown joins them. */
  pthread_t       reactor_thr;
  int             reactor_started;

  /* run queue */
  pthread_mutex_t rq_lock;
  pthread_cond_t  rq_cv;
  RQNode         *rq_head, *rq_tail;
  int             rq_idle;          /* workers blocked in rq_pop */
  _Atomic int     shutting_down;

  /* strong GC root set: every not-yet-DONE fiber (REVIEW.md B4) */
  Fiber          *all;
  pthread_mutex_t all_lock;
  _Atomic uint64_t next_id;

  /* main-fiber completion.  `main_fiber` is written by krt2_run_main (under
   * done_lock) and read by any worker's fiber_finish to decide whether a finishing
   * fiber is the run's main one; the persistent runtime keeps workers alive across
   * runs, so that read races the next run's write unless it is atomic.  Make it
   * _Atomic with acquire/release so the cross-thread read is well-defined (no UB)
   * and never observes a torn pointer. */
  _Atomic(Fiber *) main_fiber;
  pthread_mutex_t done_lock;
  pthread_cond_t  done_cv;
  int             main_done;

  /* fix 6 (R2): the CURRENT run's daemon supervision scope.  forkDaemon children
   * (§18) are unattached to ordinary structured scopes, but the PERSISTENT runtime
   * must still reap them at the run boundary — a daemon parked forever otherwise
   * stays in rt->all (a Boehm root via static g_rt), pinning one fiber + its Cont
   * chain per run forever.  Each run_main installs a fresh scope here; the spawn
   * path attaches daemons to it; main's wrapper shuts it down (interrupt + await)
   * before the run returns.  _Atomic: set once per run (release) before any fiber
   * that could fork a daemon runs, read (acquire) on the lock-free spawn path. */
  _Atomic(Scope *) daemon_scope;

  /* libuv reactor */
  uv_loop_t       loop;
  uv_async_t      async;
  pthread_mutex_t io_lock;
  IoReq          *io_head, *io_tail;
  _Atomic int     reactor_stop;
};

/* The single live runtime (a static => a Boehm GC root => keeps rt->all et al). */
extern Rt *g_rt;

/* ── cross-file internal entry points ───────────────────────────────────── */
void    krt2i_rq_push(Rt *rt, Fiber *f);      /* enqueue a runnable fiber + signal */
void    krt2i_resume(Rt *rt, Fiber *f);       /* status=RUNNABLE then rq_push (fork/cede; fiber not parked) */
/* Idempotent wake of a PARKED fiber (REVIEW.md B3d): CAS F_PARKED -> F_RUNNABLE;
 * only the winner enqueues, so two wakers racing (e.g. a promise completion and
 * an interrupt) cannot double-enqueue, and a late waker of an already-resumed or
 * DONE fiber is a safe no-op.  `resume_val`, if non-NULL, becomes the fiber's
 * next `cur` (interrupt delivery, checked at step entry, takes precedence). */
void    krt2i_wake(Rt *rt, Fiber *f, KValue *resume_val);
void    krt2i_all_add(Rt *rt, Fiber *f);      /* add to strong root set             */
void    krt2i_all_remove(Rt *rt, Fiber *f);   /* drop from strong root set          */

/* reactor */
void    krt2i_reactor_init(Rt *rt);           /* uv_loop_init + uv_async_init (main thr) */
void    krt2i_reactor_start(Rt *rt);          /* spawn the reactor thread            */
void    krt2i_reactor_stop(Rt *rt);           /* signal stop + join                  */
void    krt2i_submit_sleep(Rt *rt, Fiber *f, uint64_t nanos); /* park f on a uv_timer */
void    krt2i_cancel_sleep(Rt *rt, Fiber *f);                 /* fix S2: cancel f's active sleep timer */

/* result-value constructors (Exit / Cause), shared across files */
KValue *krt2i_success(KValue *v);
KValue *krt2i_unit(void);
KValue *krt2i_failure(KValue *cause);
KValue *krt2i_cause_interrupt(KValue *ic);
KValue *krt2i_some(KValue *v);            /* Option: Some v   */
KValue *krt2i_none(void);                 /* Option: None     */
KValue *krt2i_try_exit(KValue *fiber);    /* action: non-blocking peek -> Option Exit */

/* fiber spawn/attach (rt.c) — used by both fork and forkIn */
Fiber  *krt2i_spawn(Rt *rt, KValue *action, Scope *attach, int daemon);
/* like krt2i_spawn but the child inherits a snapshot of `parent`'s FiberRef
 * overrides (§18.1.7 copy-on-fork); `parent` NULL => no inherited locals. */
Fiber  *krt2i_spawn_from(Rt *rt, Fiber *parent, KValue *action, Scope *attach, int daemon);
Scope  *krt2i_scope_new(void);                      /* (scope.c) */
void    krt2i_scope_attach(Rt *rt, Scope *sc, Fiber *child);/* (scope.c) att_scope+link+live; born-interrupted if sc is draining */
void    krt2i_scope_detach(Rt *rt, Fiber *child);   /* (scope.c) called from fiber_finish */
/* fix 1 (R2 / §32.2.3): best-effort daemon teardown at the run boundary.  Mark the
 * scope draining, interrupt every still-live child (so ordinary INTERRUPTIBLE daemons
 * self-terminate, run finalizers, and leave rt->all), then park the CALLING HOST
 * thread (run_main, not a fiber) until live hits 0 OR `budget_ns` elapses.  Unlike
 * shutdownScope it does NOT await unboundedly: an uninterruptible daemon that never
 * delivers the interrupt is LEFT parked (leak-and-return) rather than hanging run_main
 * forever — §32.2.3 does not await unattached daemons at scope close. */
void    krt2i_scope_drain_bounded(Rt *rt, Scope *sc, uint64_t budget_ns);
KValue *krt2i_interrupt_cause(const char *tag, KValue *by_opt);
int     krt2i_interrupt_tag_id(const char *tag);    /* (scope.c) InterruptTag name -> KCT_ id */
void    krt2i_interrupt_request(Rt *rt, Fiber *target, KValue *cause);

/* interruption + structured-concurrency op handlers (scope.c).  A "parking"
 * handler returns 1 when the result is ready (it has set f->cur to pure(result),
 * keep stepping) or 0 when the fiber parked (suspended); a "value" handler
 * returns the boxed result directly. */
KValue *krt2i_op_new_scope(void);
KValue *krt2i_op_fork_in(Rt *rt, Fiber *parent, KValue *scope_h, KValue *action);
int     krt2i_op_shutdown_scope(Rt *rt, Fiber *f, KValue *scope_h);
int     krt2i_op_interrupt(Rt *rt, Fiber *f, KValue *target_h, KValue *cause, int wait);
KValue *krt2i_op_monitor(KValue *fiber_h);
int     krt2i_op_await_monitor(Rt *rt, Fiber *f, KValue *mon_h);

#endif /* KRT2_INTERNAL_H */
