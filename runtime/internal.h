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
  OP_WHILE,               /* [condIO, bodyIO] a loop; body is a do-scope        */
  OP_BREAK,               /* []               break the innermost loop          */
  OP_CONTINUE,            /* []               continue the innermost loop        */
  /* mutable references (§18.6.1 MonadRef; synchronous, single-fiber ordering) */
  OP_NEW_REF,             /* [init]           newRef -> Ref                      */
  OP_READ_REF,            /* [ref]            readRef -> a                        */
  OP_WRITE_REF,           /* [ref, val]       writeRef -> Unit                    */
  OP_TRY_EXIT,            /* [fiber]          non-blocking: Option Exit (DONE?)   */
  OP_ATOMICALLY,          /* [stm]            run an STM transaction (§18.1.13)    */
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

/* Reason kinds carried by an abnormal unwind through the continuation. */
enum { RK_NORMAL, RK_FAIL, RK_RETURN, RK_BREAK, RK_CONTINUE, RK_INTERRUPT };

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
  KK_LOOP       /* a loop boundary: break/continue target it                      */
} KKind;
struct Cont {
  KKind   kind;
  KValue *a;    /* KK_BIND/KK_CATCH: closure; KK_LOOP: the loop spec [cond,body]   */
  void   *aux;  /* KK_DOSCOPE: this scope's ExitStack*; KK_FINSEQ: FinSeq*         */
  void   *aux2; /* KK_DOSCOPE: the saved (parent) ExitStack* to restore on exit    */
  Cont   *next;
};

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
  ExitStack      *cur_exits;         /* the innermost do-scope's exit-action stack
                                      * (where `defer` registers); NULL outside a
                                      * do-scope.  §18.7 */
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
typedef enum { IO_SLEEP } IoOp;
typedef struct IoReq { IoOp op; Fiber *f; uint64_t nanos; struct IoReq *next; } IoReq;

/* ── the runtime ────────────────────────────────────────────────────────── */
struct Rt {
  int             nworkers;
  pthread_t      *workers;
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

  /* main-fiber completion */
  Fiber          *main_fiber;
  pthread_mutex_t done_lock;
  pthread_cond_t  done_cv;
  int             main_done;

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
Scope  *krt2i_scope_new(void);                      /* (scope.c) */
void    krt2i_scope_attach(Rt *rt, Scope *sc, Fiber *child);/* (scope.c) att_scope+link+live; born-interrupted if sc is draining */
void    krt2i_scope_detach(Rt *rt, Fiber *child);   /* (scope.c) called from fiber_finish */
KValue *krt2i_interrupt_cause(const char *tag, KValue *by_opt);
void    krt2i_interrupt_request(Rt *rt, Fiber *target, KValue *cause);

/* interruption + structured-concurrency op handlers (scope.c).  A "parking"
 * handler returns 1 when the result is ready (it has set f->cur to pure(result),
 * keep stepping) or 0 when the fiber parked (suspended); a "value" handler
 * returns the boxed result directly. */
KValue *krt2i_op_new_scope(void);
KValue *krt2i_op_fork_in(Rt *rt, KValue *scope_h, KValue *action);
int     krt2i_op_shutdown_scope(Rt *rt, Fiber *f, KValue *scope_h);
int     krt2i_op_interrupt(Rt *rt, Fiber *f, KValue *target_h, KValue *cause, int wait);
KValue *krt2i_op_monitor(KValue *fiber_h);
int     krt2i_op_await_monitor(Rt *rt, Fiber *f, KValue *mon_h);

#endif /* KRT2_INTERNAL_H */
