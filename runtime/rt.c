/* rt.c — kappart2 core: lifecycle, the M:N scheduler, the stackless CK-machine,
 * fibers (fork/await/cede), promises, the action-node builders, and the
 * Exit/Cause constructors.  See internal.h for the two concurrency protocols
 * (park/wake under a per-object lock; GC liveness via the rt->all strong set)
 * and DESIGN.md for the architecture.  This file is the v1 spine; STM, scopes,
 * interruption/masking, atomics, and race/timeout are the next increments. */
#include "internal.h"

#include <gc.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

Rt *g_rt = NULL;

const char *const KRT2_CAPABILITIES[] = {
  "rt-core", "rt-parallel", "rt-shared-stm", "rt-blocking", "rt-atomics", NULL
};

/* ── Exit / Cause / outcome constructors (§28 shapes) ───────────────────────
 * All result ctors the runtime builds now carry their FIXED KCT_ id (kappart.h)
 * so a .kp id-based `match` dispatches correctly; the old by-name ctor1/ctor2
 * (KRT2_RESULT_ID = KCT_OTHER) are gone — use idc1/idc2 below. */
KValue *krt2i_unit(void)            { return kunit(); }
/* idc1/idc2: like ctor1/ctor2 but with the ctor's FIXED KCT_ id (kappart.h), so
 * a runtime-built Exit/Cause matches a codegen id-based `case` (not just the
 * name-based harness matcher).  Without the id these carried KCT_OTHER and every
 * such match from .kp was non-exhaustive. */
static KValue *idc1(int id, const char *name, KValue *a) {
  KValue *args[1] = { a };
  return kctor(id, name, 1, args);
}
static KValue *idc2(int id, const char *name, KValue *a, KValue *b) {
  KValue *args[2] = { a, b };
  return kctor(id, name, 2, args);
}
KValue *krt2i_success(KValue *v)    { return idc1(KCT_SUCCESS, "Success", v); }
KValue *krt2i_failure(KValue *c)    { return idc1(KCT_FAILURE, "Failure", c); }
KValue *krt2i_cause_interrupt(KValue *ic) { return idc1(KCT_INTERRUPT, "Interrupt", ic); }
KValue *krt2i_some(KValue *v)       { return idc1(KCT_SOME, "Some", v); }
KValue *krt2i_none(void)            { return kctor0(KCT_NONE, "None"); }
KValue *krt2_success(KValue *v)     { return idc1(KCT_SUCCESS, "Success", v); }
KValue *krt2_failure(KValue *c)     { return idc1(KCT_FAILURE, "Failure", c); }
KValue *krt2_cause_fail(KValue *e)  { return idc1(KCT_FAIL, "Fail", e); }
KValue *krt2_cause_interrupt(KValue *ic) { return idc1(KCT_INTERRUPT, "Interrupt", ic); }
KValue *krt2_cause_defect(KValue *di)    { return idc1(KCT_DEFECT, "Defect", di); }
KValue *krt2_cause_both(KValue *a, KValue *b) { return idc2(KCT_BOTH, "Both", a, b); }
KValue *krt2_cause_then(KValue *a, KValue *b) { return idc2(KCT_THEN, "Then", a, b); }
KValue *krt2_interrupt_cause(const char *tag, KValue *by_opt) {
  return krt2i_interrupt_cause(tag, by_opt); /* one impl (scope.c); this was a divergent dup */
}

/* ── action-node builders (codegen + harness targets) ──────────────────── */
static KValue *op0(int op, const char *n) { return kctor0(op, n); }
static KValue *op1(int op, const char *n, KValue *a) {
  KValue *args[1] = { a }; return kctor(op, n, 1, args);
}
static KValue *op2(int op, const char *n, KValue *a, KValue *b) {
  KValue *args[2] = { a, b }; return kctor(op, n, 2, args);
}
KValue *krt2_pure(KValue *v)              { return op1(OP_PURE, "rt.pure", v); }
KValue *krt2_bind(KValue *m, KValue *k)   { return op2(OP_BIND, "rt.bind", m, k); }
KValue *krt2_then(KValue *m, KValue *n)   { return op2(OP_THEN, "rt.then", m, n); }
KValue *krt2_catch(KValue *b, KValue *h)  { return op2(OP_CATCH, "rt.catch", b, h); }
KValue *krt2_throw(KValue *e)             { return op1(OP_THROW, "rt.throw", e); }
KValue *krt2_reraise(KValue *c)           { return op1(OP_RERAISE, "rt.reraise", c); }
KValue *krt2_fork(KValue *a)              { return op1(OP_FORK, "rt.fork", a); }
KValue *krt2_fork_daemon(KValue *a)       { return op1(OP_FORK_DAEMON, "rt.forkDaemon", a); }
KValue *krt2_await(KValue *f)             { return op1(OP_AWAIT, "rt.await", f); }
KValue *krt2_cede(void)                   { return op0(OP_CEDE, "rt.cede"); }
KValue *krt2_sleep_for(KValue *d)         { return op1(OP_SLEEP, "rt.sleep", d); }
KValue *krt2_now_monotonic(void)          { return op0(OP_NOW, "rt.now"); }
/* nowMonotonic as a kpf shim (reads the monotonic clock directly) so it works in
 * a non-suspending do-block on the bridge, not only the CK-machine OP_NOW node. */
KValue *kpf_now(KValue **a)               { (void)a; return kint((int64_t)uv_hrtime()); }
KValue *krt2_new_promise(void)            { return op0(OP_NEW_PROMISE, "rt.newPromise"); }
KValue *krt2_complete_promise(KValue *p, KValue *e) { return op2(OP_COMPLETE_PROMISE, "rt.completeP", p, e); }
KValue *krt2_await_promise_exit(KValue *p){ return op1(OP_AWAIT_PROMISE_EXIT, "rt.awaitP", p); }
KValue *krt2_current_fiber_id(void)       { return op0(OP_CURRENT_FIBER_ID, "rt.curFiberId"); }
KValue *krt2_fiber_id(KValue *f)          { return op1(OP_FIBER_ID, "rt.fiberId", f); }
/* interruption + masking */
KValue *krt2_interrupt(KValue *f)         { return op1(OP_INTERRUPT, "rt.interrupt", f); }
KValue *krt2_interrupt_fork(KValue *f)    { return op1(OP_INTERRUPT_FORK, "rt.interruptFork", f); }
KValue *krt2_interrupt_as(KValue *c, KValue *f)      { return op2(OP_INTERRUPT, "rt.interruptAs", f, c); }
KValue *krt2_interrupt_fork_as(KValue *c, KValue *f) { return op2(OP_INTERRUPT_FORK, "rt.interruptForkAs", f, c); }
KValue *krt2_uninterruptible(KValue *b)   { return op1(OP_UNINTERRUPTIBLE, "rt.uninterruptible", b); }
KValue *krt2_poll(void)                   { return op0(OP_POLL, "rt.poll"); }
KValue *krt2_mask(KValue *f)              { return op1(OP_MASK, "rt.mask", f); }
KValue *krt2_ensuring(KValue *body, KValue *fin) { return krt2_finally(body, fin); } /* = finally */
/* §18.1.11 blocking (rt-blocking): run a potentially-blocking action.  v1 runs it
 * inline on the current worker — semantically faithful (the action runs and its
 * result/failure propagate).  The dedicated offload lane (uv_queue_work, so a
 * blocking syscall does not occupy a scheduler worker) is the future increment;
 * see reactor.c.  Implemented as identity so the advertised rt-blocking
 * capability is actually backed, not just declared. */
KValue *krt2_blocking(KValue *body)       { return body; }

/* §34.5.3 do-kernel CPS wrappers.  The codegen's curried/array path calls a prim
 * via fn(KValue**), but the krt2_* node builders take individual args; these
 * thin wrappers adapt the convention so fork/await/cede/sleepFor/promises lower
 * to their OP_* nodes.  (The saturated fast path calls the builders directly via
 * primDirect; these serve a bare/curried reference.) */
KValue *kpf_fork(KValue **a)               { return krt2_fork(a[0]); }
KValue *kpf_fork_daemon(KValue **a)        { return krt2_fork_daemon(a[0]); }
KValue *kpf_await(KValue **a)              { return krt2_await(a[0]); }
KValue *kpf_cede(KValue **a)               { (void)a; return krt2_cede(); }
KValue *kpf_sleep_for(KValue **a)          { return krt2_sleep_for(a[0]); }
KValue *kpf_new_promise(KValue **a)        { (void)a; return krt2_new_promise(); }
KValue *kpf_complete_promise(KValue **a)   { return krt2_complete_promise(a[0], a[1]); }
KValue *kpf_await_promise_exit(KValue **a) { return krt2_await_promise_exit(a[0]); }
/* §18.1.8 structured scopes + monitors (Stage 3): scheduler OP_* nodes. */
KValue *kpf_new_scope(KValue **a)          { (void)a; return krt2_new_scope(); }
KValue *kpf_fork_in(KValue **a)            { return krt2_fork_in(a[0], a[1]); }
KValue *kpf_shutdown_scope(KValue **a)     { return krt2_shutdown_scope(a[0]); }
KValue *kpf_monitor(KValue **a)            { return krt2_monitor(a[0]); }
KValue *kpf_await_monitor(KValue **a)      { return krt2_await_monitor(a[0]); }

/* structured concurrency */
KValue *krt2_new_scope(void)              { return op0(OP_NEW_SCOPE, "rt.newScope"); }
KValue *krt2_fork_in(KValue *s, KValue *a){ return op2(OP_FORK_IN, "rt.forkIn", s, a); }
KValue *krt2_shutdown_scope(KValue *s)    { return op1(OP_SHUTDOWN_SCOPE, "rt.shutdownScope", s); }
KValue *krt2_monitor(KValue *f)           { return op1(OP_MONITOR, "rt.monitor", f); }
KValue *krt2_await_monitor(KValue *m)     { return op1(OP_AWAIT_MONITOR, "rt.awaitMonitor", m); }
KValue *krt2_demonitor(KValue *m)         { (void)m; return krt2_pure(kunit()); } /* drop is a no-op (§18.1.8) */
/* demonitor delivers Unit immediately (a no-op): a kpf shim returning the Unit
 * VALUE works on both the bridge and the CK-machine, so it needs no krt2_ node. */
KValue *kpf_demonitor(KValue **a)         { (void)a; return kunit(); }

/* withScope: newScope; run `use scope`; shut the scope down on EVERY exit
 * (normal, failure, interrupt) while PRESERVING the body's result — i.e.
 * `ensuring`, not `then`.  `then` would discard the body's `a` (returning the
 * shutdown's Unit, contradicting the `IO e a` type) and would skip shutdown on
 * the failure/interrupt path, leaking child fibers past a failed scoped body
 * (§32.2.3).  Build via a continuation closure that captures `use` in env[0]. */
static KValue *with_scope_cont(KEnv *env, KValue *sc) {
  KValue *use = kvar(env, 0);
  return krt2_ensuring(kapp(use, sc), krt2_shutdown_scope(sc));
}
KValue *krt2_with_scope(KValue *use) {
  return krt2_bind(krt2_new_scope(), kclo(with_scope_cont, kpush(use, NULL)));
}

/* ── do-kernel completion channel (§18.7, §18.8) ───────────────────────── */
KValue *krt2_doscope(KValue *body) { return op1(OP_DOSCOPE, "rt.doscope", body); }
KValue *krt2_defer(KValue *a)      { return op1(OP_DEFER, "rt.defer", a); }
KValue *krt2_return(KValue *v)     { return op1(OP_RETURN, "rt.return", v); }
KValue *krt2_retscope(KValue *b)   { return op1(OP_RETSCOPE, "rt.retscope", b); }
KValue *krt2_break(void)           { return op0(OP_BREAK, "rt.break"); }
KValue *krt2_continue(void)        { return op0(OP_CONTINUE, "rt.continue"); }
KValue *krt2_while(KValue *cond, KValue *body) { return op2(OP_WHILE, "rt.while", cond, body); }
KValue *krt2_new_ref(KValue *v)              { return op1(OP_NEW_REF, "rt.newRef", v); }
KValue *krt2_read_ref(KValue *r)             { return op1(OP_READ_REF, "rt.readRef", r); }
KValue *krt2_write_ref(KValue *r, KValue *v) { return op2(OP_WRITE_REF, "rt.writeRef", r, v); }
KValue *krt2i_try_exit(KValue *fiber)        { return op1(OP_TRY_EXIT, "rt.tryExit", fiber); }
/* finally body fin = doscope { defer fin; body } — fin runs on EVERY exit path
 * (normal completion, typed fail, return, break/continue, interruption). */
KValue *krt2_finally(KValue *body, KValue *fin) {
  return krt2_doscope(krt2_then(krt2_defer(fin), body));
}

/* ── §18.1.21/.22 effect-handler nodes (Stage 4a, one-shot) ──────────────────
 * `handle`/`perform`/`resume` lower to these so an `Eff` computation runs ON
 * the scheduler (a handler clause may park).  See the deliver/unwind arms and
 * the OP_PERFORM capture-sub-chain primitive below for the operational model. */
static KValue *op5(int op, const char *n, KValue *a, KValue *b, KValue *c,
                  KValue *d, KValue *e) {
  KValue *args[5] = { a, b, c, d, e }; return kctor(op, n, 5, args);
}
static KValue *op3(int op, const char *n, KValue *a, KValue *b, KValue *c) {
  KValue *args[3] = { a, b, c }; return kctor(op, n, 3, args);
}
KValue *krt2_handle(KValue *deep, KValue *label, KValue *ret, KValue *ops, KValue *body) {
  return op5(OP_HANDLE, "rt.handle", deep, label, ret, ops, body);
}
KValue *krt2_perform(KValue *label, KValue *op, KValue *payload) {
  return op3(OP_PERFORM, "rt.perform", label, op, payload);
}
KValue *krt2_resume(KValue *k, KValue *v) {
  return op2(OP_RESUME, "rt.resume", k, v);
}
/* kpf shims: the codegen's curried/array prim path calls fn(KValue**). */
KValue *kpf_rt_handle(KValue **a)  { return krt2_handle(a[0], a[1], a[2], a[3], a[4]); }
KValue *kpf_rt_perform(KValue **a) { return krt2_perform(a[0], a[1], a[2]); }
KValue *kpf_rt_resume(KValue **a)  { return krt2_resume(a[0], a[1]); }
/* __effBind m f -> OP_BIND node (the monadic bind of the Eff carrier). */
KValue *kpf_eff_bind(KValue **a)   { return krt2_bind(a[0], a[1]); }
/* §18.7/§32.2.19 Eff-carrier do-scope / exit-action nodes (Stage 4a): reuse the
 * IO do-kernel's OP_DOSCOPE/OP_DEFER, so an Eff do-block's defers run masked-LIFO
 * on EVERY way out (normal completion AND a handler's §32.2.20 abandonment). */
KValue *kpf_eff_doscope(KValue **a) { return krt2_doscope(a[0]); }
KValue *kpf_eff_defer(KValue **a)   { return krt2_defer(a[0]); }

/* Convenience console builders (raw C strings). */
KValue *krt2_print_c(const char *s)   { return op1(OP_PRINT, "rt.print", kstr0(s)); }
KValue *krt2_println_c(const char *s) { return op1(OP_PRINTLN, "rt.println", kstr0(s)); }

/* ── synchronous bridge for CK-machine action nodes ─────────────────────────
 * A do-bind whose action is an IO combinator that BUILDS a krt2_* node — e.g.
 * the prelude's `liftA2 f a b = ioBind a (\x -> ioBind b (\y -> ioPure (f x y)))`,
 * and `<*>`/`traverse`/`bracketM` — lowers that `ioBind`-over-PARAMETER to a
 * krt2_bind node (mayActSuspend via spineHeadIsLocal), so the combinator RETURNS
 * a krt2_* action tree.  But it is reached through the `Applicative (IO e)`
 * dictionary, which the §3.3 (suspenderGlobals) analysis cannot see through, so
 * the do-bind stays on the legacy `krun_io` bridge — which used to hit krun_io's
 * `default` arm and bind the raw NODE (e.g. `r <- liftA2 f a b` gave a wrong-typed
 * value: the `traverse`/delve crash, and the C != interp baseline gap).
 *
 * Drive the NON-suspending OPs here with exactly the legacy bridge's semantics
 * (krun_io recursion for sub-actions; the kpf_io_catchIO fail/handler shape),
 * trampolining bind/then/catch so a straight chain stays flat.  A genuinely
 * suspending node (OP_FORK/OP_AWAIT/…) never reaches the bridge — those blocks
 * are CPS-lowered onto the CK-machine — and a non-OP value (a data ctor, a
 * `return`ed result) is returned unchanged.  (This is also why `catchIO (do …)`
 * over a non-suspending do-block body now runs correctly on the bridge: its
 * kpf_io_catchIO body runs through krun_io, which drives the krt2_* tree here.) */
KValue *krt2_run_op_sync(KValue *action) {
  for (;;) {
    switch (kctor_tagid(action)) {
      case OP_PURE:
        return kctor_arg(action, 0);
      case OP_BIND: {
        KValue *r = krun_io(kctor_arg(action, 0));
        if (kis_fail(r)) return r;
        action = kapp(kctor_arg(action, 1), r);
        if (kctor_tagid(action) >= KRT2_OP_BASE) continue; /* another OP tree: trampoline */
        return krun_io(action);                            /* legacy node / value: run it */
      }
      case OP_THEN: {
        KValue *r = krun_io(kctor_arg(action, 0));
        if (kis_fail(r)) return r;
        action = kctor_arg(action, 1);
        if (kctor_tagid(action) >= KRT2_OP_BASE) continue;
        return krun_io(action);
      }
      case OP_CATCH: {
        KValue *r = krun_io(kctor_arg(action, 0));
        if (!kis_fail(r)) return r;
        action = kapp(kctor_arg(action, 1), r->as.fail.err); /* run handler on the error */
        if (kctor_tagid(action) >= KRT2_OP_BASE) continue;
        return krun_io(action);
      }
      case OP_THROW:
        return kfail(kctor_arg(action, 0));
      default:
        /* not a non-suspending OP node: a value / data ctor (returned as-is), or
         * a node the synchronous bridge does not drive (never a codegen-reachable
         * suspending OP — those are CPS-lowered onto the CK-machine). */
        return action;
    }
  }
}

/* The while-loop's per-iteration branch: \cond_result ->
 *   if True then doscope(body) (run an iteration), else break (exit the loop).
 * `body` is captured in env[0].  After an iteration's doscope completes
 * normally, KK_LOOP re-runs `iterate`, which re-evaluates the condition. */
static KValue *loop_branch(KEnv *env, KValue *c) {
  KValue *body = kvar(env, 0);
  if (kas_bool(c)) return krt2_doscope(body);   /* condition True: run an iteration */
  return krt2_break();                          /* condition False: exit the loop   */
}

/* `restore` (the function `mask` hands to its body): runs `act` at the
 * interruptibility level that held at mask entry, captured in env[0]. */
static KValue *restore_fn(KEnv *env, KValue *act) {
  return op2(OP_RESTORE, "rt.restore", act, kvar(env, 0));  /* [act, outerDepth] */
}

/* acquireRelease (§18.1.12 / §19.5) as a composition over mask+finally+bind:
 *   mask (\restore -> acquire >>= \r -> finally (restore (use r)) (release r))
 * acquire runs uninterruptibly (under the mask), `use r` is restored
 * (interruptible), and `release r` is a finalizer (runs masked, on every exit). */
static KValue *ar_with_r(KEnv *env, KValue *r) {     /* env = [release, use, restore] */
  KValue *release = kvar(env, 0), *use = kvar(env, 1), *restore = kvar(env, 2);
  return krt2_finally(kapp(restore, kapp(use, r)), kapp(release, r));
}
static KValue *ar_masked(KEnv *env, KValue *restore) { /* env = [acquire, release, use] */
  KValue *acq = kvar(env, 0), *rel = kvar(env, 1), *use = kvar(env, 2);
  return krt2_bind(acq, kclo(ar_with_r, kpush(rel, kpush(use, kpush(restore, NULL)))));
}
KValue *krt2_acquire_release(KValue *acquire, KValue *release, KValue *use) {
  return krt2_mask(kclo(ar_masked, kpush(acquire, kpush(release, kpush(use, NULL)))));
}

/* ── strong root set (rt->all) ──────────────────────────────────────────── */
void krt2i_all_add(Rt *rt, Fiber *f) {
  pthread_mutex_lock(&rt->all_lock);
  f->all_prev = NULL;
  f->all_next = rt->all;
  if (rt->all) rt->all->all_prev = f;
  rt->all = f;
  pthread_mutex_unlock(&rt->all_lock);
}
void krt2i_all_remove(Rt *rt, Fiber *f) {
  pthread_mutex_lock(&rt->all_lock);
  if (f->all_prev) f->all_prev->all_next = f->all_next;
  else if (rt->all == f) rt->all = f->all_next;
  if (f->all_next) f->all_next->all_prev = f->all_prev;
  f->all_prev = f->all_next = NULL;
  pthread_mutex_unlock(&rt->all_lock);
}

/* ── run queue ──────────────────────────────────────────────────────────── */
void krt2i_rq_push(Rt *rt, Fiber *f) {
  RQNode *n = (RQNode *)GC_MALLOC(sizeof(RQNode)); /* scanned: keeps f reachable */
  n->f = f; n->next = NULL;
  pthread_mutex_lock(&rt->rq_lock);
  if (rt->rq_tail) rt->rq_tail->next = n; else rt->rq_head = n;
  rt->rq_tail = n;
  if (rt->rq_idle) pthread_cond_signal(&rt->rq_cv);
  pthread_mutex_unlock(&rt->rq_lock);
}
void krt2i_resume(Rt *rt, Fiber *f) {
  atomic_store_explicit(&f->status, F_RUNNABLE, memory_order_release);
  krt2i_rq_push(rt, f);
}
void krt2i_wake(Rt *rt, Fiber *f, KValue *resume_val) {
  /* Idempotent: only the waker that wins the F_PARKED -> F_RUNNABLE CAS may
   * touch the fiber.  Writing `cur` BEFORE the CAS would let a late/duplicate
   * wake (one that loses the CAS because the fiber is already runnable, running,
   * or done) clobber a live fiber's action — a data race.  Once we win the CAS
   * the fiber is parked (not running) and not yet enqueued, so writing `cur`
   * here and enqueuing it afterwards is safe; the rq_lock in rq_push publishes
   * the write to the worker that later pops the fiber. */
  int expected = F_PARKED;
  if (atomic_compare_exchange_strong_explicit(&f->status, &expected, F_RUNNABLE,
                                              memory_order_acq_rel, memory_order_relaxed)) {
    if (resume_val) f->cur = resume_val;
    krt2i_rq_push(rt, f);
  }
}
/* Block until a runnable fiber is available, or NULL when shutting down. */
static Fiber *rq_pop(Rt *rt) {
  pthread_mutex_lock(&rt->rq_lock);
  for (;;) {
    if (atomic_load_explicit(&rt->shutting_down, memory_order_acquire)) {
      pthread_mutex_unlock(&rt->rq_lock);
      return NULL;
    }
    RQNode *n = rt->rq_head;
    if (n) {
      rt->rq_head = n->next;
      if (!rt->rq_head) rt->rq_tail = NULL;
      pthread_mutex_unlock(&rt->rq_lock);
      return n->f;
    }
    rt->rq_idle++;
    pthread_cond_wait(&rt->rq_cv, &rt->rq_lock);
    rt->rq_idle--;
  }
}

/* ── fibers ─────────────────────────────────────────────────────────────── */
static Cont g_done = { KK_DONE, NULL, NULL, NULL, NULL }; /* shared; immutable */

static Fiber *fiber_new(Rt *rt, KValue *action) {
  Fiber *f = (Fiber *)GC_MALLOC(sizeof(Fiber));
  f->id = atomic_fetch_add_explicit(&rt->next_id, 1, memory_order_relaxed) + 1;
  atomic_store(&f->status, F_RUNNABLE);
  f->cur = action;
  f->k = &g_done;
  f->exit = NULL;
  f->waiters = NULL;
  f->daemon = 0;
  f->all_prev = f->all_next = NULL;
  pthread_mutex_init(&f->lock, NULL);
  return f;
}

static Cont *cont_new(KKind kind, KValue *a, Cont *next) {
  Cont *c = (Cont *)GC_MALLOC(sizeof(Cont));
  c->kind = kind; c->a = a; c->next = next;
  return c;
}
static Cont *cont_new2(KKind kind, KValue *a, void *aux, void *aux2, Cont *next) {
  Cont *c = (Cont *)GC_MALLOC(sizeof(Cont));
  c->kind = kind; c->a = a; c->aux = aux; c->aux2 = aux2; c->next = next;
  return c;
}

/* ── do-scope exit-action stacks (defer / using / finally) ──────────────── */
static ExitStack *exitstack_new(void) {
  ExitStack *s = (ExitStack *)GC_MALLOC(sizeof(ExitStack));
  s->items = NULL; s->n = 0; s->cap = 0;
  return s;
}
static void exitstack_push(ExitStack *s, KValue *action) {
  if (s->n == s->cap) {
    int nc = s->cap ? s->cap * 2 : 4;
    KValue **ni = (KValue **)GC_MALLOC(sizeof(KValue *) * nc);
    for (int i = 0; i < s->n; i++) ni[i] = s->items[i];
    s->items = ni; s->cap = nc;
  }
  s->items[s->n++] = action;
}

/* KK_FINSEQ state: run xs[i], xs[i-1], ..., xs[0], then apply the saved Reason. */
typedef struct { ExitStack *xs; int i; int rkind; KValue *rval; KValue *rlabel; } FinSeq;

/* §18.1.21 a captured ONE-SHOT resumption.  `head` is the op-site Cont frame;
 * `tail` is the LAST frame of the captured sub-chain (its `next` is severed and
 * points at &g_done at capture time so the slice is self-terminated).  `used`
 * enforces the one-shot discipline at runtime as a defense-in-depth backstop —
 * the compile-time E_QTT_CONTINUATION_CAPTURE gate already rejects >1 use, so a
 * second `resume` here is an internal invariant break, not a user error.  The
 * saved `cur_exits` is reinstated on splice so the resumed body re-enters under
 * the do-scope/exit-action state that held at capture (§32.2.13). */
typedef struct Resumption {
  Cont      *head;       /* op-site frame: the start of the captured sub-chain    */
  Cont      *tail;       /* last captured frame (tail->next severed to &g_done)   */
  ExitStack *cur_exits;  /* the fiber's cur_exits at the capture point (body's)   */
  KValue    *label;      /* §32.2.22 deep reinstall: the handler's installed label */
  void      *handler;    /* the Handler* to re-push on a deep resume; NULL=shallow */
  void      *handler_exits; /* the cur_exits the reinstalled handler restores to   */
  int        used;       /* 0 until resumed; one-shot guard                       */
} Resumption;

static int deliver(Rt *rt, Fiber *f, KValue *v);  /* normal value path  */
static int unwind(Rt *rt, Fiber *f, int rkind, KValue *rval, KValue *rlabel); /* abnormal */

/* Terminate `f` with `exitv`, wake its awaiters, drop it from the root set. */
static void fiber_finish(Rt *rt, Fiber *f, KValue *exitv) {
  pthread_mutex_lock(&f->lock);
  f->exit = exitv;
  atomic_store_explicit(&f->status, F_DONE, memory_order_release);
  Waiter *w = f->waiters;
  f->waiters = NULL;
  pthread_mutex_unlock(&f->lock);

  for (; w; w = w->next)              /* wake EVERY awaiter (idempotent CAS)  */
    krt2i_wake(rt, w->f, krt2_pure(w->want_exit ? exitv : kunit()));
  krt2i_scope_detach(rt, f);          /* leave att_scope; may drain a shutdownScope */
  krt2i_all_remove(rt, f);            /* DONE: kept now only by a user handle */

  if (f == rt->main_fiber) {
    pthread_mutex_lock(&rt->done_lock);
    rt->main_done = 1;
    pthread_cond_signal(&rt->done_cv);
    pthread_mutex_unlock(&rt->done_lock);
  }
}

/* Create, attach, root, and enqueue a child fiber.  `attach` is the supervision
 * scope the child is attached to (NULL or daemon => unattached).  The child's
 * own forks attach to `attach` too (flat nesting in v1; per-do-block nested
 * scopes arrive with the do-kernel completion increment). */
Fiber *krt2i_spawn(Rt *rt, KValue *action, Scope *attach, int daemon) {
  Fiber *child = fiber_new(rt, action);
  child->daemon = daemon;
  child->cur_scope = attach;
  if (!daemon && attach) krt2i_scope_attach(rt, attach, child); /* att_scope+link+live++ */
  krt2i_all_add(rt, child);
  krt2i_resume(rt, child);
  return child;
}

/* await: returns 1 if the child is already done (continue stepping with its
 * Exit), 0 if `f` parked onto the child's waiter list (suspended). */
static int do_await(Rt *rt, Fiber *f, KValue *handle) {
  (void)rt;
  Fiber *child = (Fiber *)kas_fgn(handle);
  pthread_mutex_lock(&child->lock);
  if (atomic_load_explicit(&child->status, memory_order_acquire) == F_DONE) {
    KValue *ex = child->exit;
    pthread_mutex_unlock(&child->lock);
    f->cur = krt2_pure(ex);
    return 1;
  }
  Waiter *w = (Waiter *)GC_MALLOC(sizeof(Waiter));
  w->f = f; w->want_exit = 1; w->next = child->waiters; child->waiters = w;
  atomic_store(&f->status, F_PARKED);
  pthread_mutex_unlock(&child->lock);
  return 0;
}

/* ── promises ───────────────────────────────────────────────────────────── */
static KValue *promise_new(void) {
  Promise *p = (Promise *)GC_MALLOC(sizeof(Promise));
  atomic_store(&p->completed, 0);
  p->exit = NULL; p->waiters = NULL;
  pthread_mutex_init(&p->lock, NULL);
  return kfgn(p, KRT2_KIND_PROMISE);
}
static KValue *promise_complete(Rt *rt, KValue *ph, KValue *exitv) {
  Promise *p = (Promise *)kas_fgn(ph);
  pthread_mutex_lock(&p->lock);
  int first = !atomic_load(&p->completed);
  Waiter *w = NULL;
  if (first) {
    p->exit = exitv;
    atomic_store_explicit(&p->completed, 1, memory_order_release);
    w = p->waiters; p->waiters = NULL;
  }
  pthread_mutex_unlock(&p->lock);
  for (; w; w = w->next) krt2i_wake(rt, w->f, krt2_pure(exitv));
  return kbool(first);
}
static int do_await_promise(Rt *rt, Fiber *f, KValue *ph) {
  (void)rt;
  Promise *p = (Promise *)kas_fgn(ph);
  pthread_mutex_lock(&p->lock);
  if (atomic_load_explicit(&p->completed, memory_order_acquire)) {
    KValue *ex = p->exit;
    pthread_mutex_unlock(&p->lock);
    f->cur = krt2_pure(ex);
    return 1;
  }
  Waiter *w = (Waiter *)GC_MALLOC(sizeof(Waiter));
  w->f = f; w->want_exit = 1; w->next = p->waiters; p->waiters = w;
  atomic_store(&f->status, F_PARKED);
  pthread_mutex_unlock(&p->lock);
  return 0;
}

/* ── the CK-machine ─────────────────────────────────────────────────────── */
static void emit_kstr(KValue *s, int newline) {
  /* kas_str returns NUL-terminated bytes of a K_STR. */
  fputs(kas_str(s), stdout);
  if (newline) fputc('\n', stdout);
}

/* Feed value `v` to the continuation.  Returns 1 to keep stepping, 0 if the
 * fiber finished. */
/* Apply a saved Reason (from KK_FINSEQ, once a scope's finalizers have run). */
static int apply_reason(Rt *rt, Fiber *f, int rkind, KValue *rval, KValue *rlabel) {
  if (rkind == RK_NORMAL) return deliver(rt, f, rval);
  return unwind(rt, f, rkind, rval, rlabel);
}

/* Run a do-scope's exit actions LIFO, then resume the Reason.  `restore` is the
 * parent exit stack to reinstate as the fiber's current one.  Finalizers run via
 * the CK-machine, so a finalizer that itself blocks suspends the whole unwind
 * (the KK_FINSEQ frame is on the heap continuation — §34.4.1: defer is never a
 * host finalizer). */
static int begin_finseq(Rt *rt, Fiber *f, ExitStack *xs, ExitStack *restore,
                        int rkind, KValue *rval, KValue *rlabel) {
  f->cur_exits = restore;
  if (!xs || xs->n == 0) return apply_reason(rt, f, rkind, rval, rlabel);
  /* §32.2.5: finalizers run MASKED.  Push a KK_POPMASK beneath the KK_FINSEQ and
   * raise mask_depth now, so the entire drain — every finalizer body's internal
   * steps AND the sequence itself — is uninterruptible, and mask is restored
   * exactly once when the drain completes: on the normal path (KK_FINSEQ done ->
   * apply_reason descends through the KK_POPMASK) and on the abnormal/abandonment
   * path (unwind through KK_FINSEQ also descends through it).  Without this an
   * async interrupt delivered between finalizer steps (the fiber_step-top check
   * fires while mask_depth==0) would unwind into the KK_FINSEQ and silently
   * abandon the scope's remaining defers — a §18.7 exactly-once violation. */
  f->k = cont_new(KK_POPMASK, NULL, f->k);
  f->mask_depth++;
  FinSeq *fs = (FinSeq *)GC_MALLOC(sizeof(FinSeq));
  fs->xs = xs; fs->i = xs->n - 1; fs->rkind = rkind; fs->rval = rval; fs->rlabel = rlabel;
  f->k = cont_new2(KK_FINSEQ, NULL, fs, NULL, f->k);
  f->cur = krt2_pure(kunit());  /* kick: deliver() -> KK_FINSEQ runs xs[n-1] */
  return 1;
}

/* ── §18.1.21/.22 effect handlers (Stage 4a, one-shot) ───────────────────────
 * `perform label.op payload` searches f->k OUTWARD for the nearest KK_HANDLER
 * whose installed label (Cont.a) has the same ctor-id as the op's label — the
 * exact structural twin of unwind's KK_CATCH/RK_FAIL search (rt.c §2.3), but
 * RESUMABLE: instead of dropping the popped frames, it SEVERS the op-site->
 * handler sub-chain and hands it back as a one-shot resumption.  `resume k v`
 * re-links that sub-chain onto f->k and delivers v — the splice twin of
 * deliver's KK_BIND arm (§2.4).  ONE-SHOT only: the splice is a destructive
 * pointer move, exactly how f->k already works everywhere. */

/* §18.1.18 label identity: the native backend gives each effect label a unique
 * string token (the label GName's effLabelKey, recorded as the label global's
 * core body; see Check.elabTopEffect / elabScopedEffect).  Both `handle` and the
 * `perform` site reference the SAME label global, so identity is string equality
 * on that token — exactly as the legacy kpf___handleEff eff_label_eq did.  A
 * ctor-id compare would be WRONG: every label is a K_STR, so kctor_tagid yields
 * -1 for all of them and distinct effects would falsely match. */
static int eff_label_same(KValue *a, KValue *b) {
  return a && b && a->tag == K_STR && b->tag == K_STR &&
         a->as.str.len == b->as.str.len &&
         memcmp(a->as.str.p, b->as.str.p, a->as.str.len) == 0;
}

/* The resumption is handed to the clause as an ORDINARY one-argument function so
 * that `resume k v` — surface-elaborated to the application `k v` — naturally
 * produces an OP_RESUME node.  This closure captures the K_FGN resumption box in
 * env[0] and builds `krt2_resume(box, v)` when applied. */
static KValue *resume_thunk(KEnv *env, KValue *v) {
  return krt2_resume(kvar(env, 0), v);
}

/* Run a handler clause `clause payload kfn`, where kfn is the resumption wrapped
 * as a function.  The clause body is itself an Eff computation that runs on the
 * scheduler (so it may park / perform further ops). */
static int run_op_clause(Rt *rt, Fiber *f, KValue *clause, KValue *payload, KValue *kbox) {
  KValue *kfn = kclo(resume_thunk, kpush(kbox, NULL));
  f->cur = kapp(kapp(clause, payload), kfn);
  return 1;
}

/* OP_PERFORM: capture op-site -> handler, run the matching clause (§2.3).  Returns
 * 1 to keep stepping, 0 if the fiber finished (an unhandled op aborts the fiber). */
static int do_perform(Rt *rt, Fiber *f, KValue *label, KValue *op, KValue *payload) {
  /* Walk outward from the op site for the nearest matching KK_HANDLER.  `prev`
   * trails one frame behind `c` so we can sever the captured sub-chain's tail. */
  Cont *head = f->k;        /* the op-site frame begins the captured sub-chain   */
  Cont *prev = NULL;
  for (Cont *c = f->k; ; prev = c, c = c->next) {
    if (c->kind == KK_DONE) {
      /* no enclosing handler for this label: an escaped operation.  The type
       * system forbids this (a handled row), so it is an internal mis-lowering;
       * fail the fiber rather than silently dropping the op. */
      const char *nm = (op && op->tag == K_STR) ? (const char *)op->as.str.p : "?";
      char msg[160];
      snprintf(msg, sizeof msg,
               "internal: perform '%s' escaped all handlers (unhandled effect op)", nm);
      return unwind(rt, f, RK_FAIL, kstr0(msg), NULL);
    }
    if (c->kind == KK_HANDLER && eff_label_same(c->a, label)) {
      Handler *h = (Handler *)c->aux;
      KValue *clause = h->ops ? kproj(h->ops, (const char *)op->as.str.p) : NULL;
      if (!clause) {
        char msg[160];
        snprintf(msg, sizeof msg, "internal: handler has no clause for op '%s'",
                 (const char *)op->as.str.p);
        return unwind(rt, f, RK_FAIL, kstr0(msg), NULL);
      }
      ExitStack *body_exits = f->cur_exits;       /* the captured body's exits   */
      ExitStack *handler_exits = (ExitStack *)c->aux2; /* what the prompt restores */
      /* Build the one-shot resumption from the captured sub-chain [head .. prev].
       * The captured slice runs from the op site up to (and EXCLUDING) the handler
       * frame `c` (§2.3).  We POP the handler frame: the clause is the handler's
       * own code and runs OUTSIDE the prompt (its result flows to c->next, the
       * handler's own continuation).  The resumption re-splices [head..prev] onto
       * c->next when invoked; a deep handler additionally re-pushes a fresh copy
       * of this KK_HANDLER around the resumed body (§32.2.22). */
      Resumption *r = (Resumption *)GC_MALLOC(sizeof(Resumption));
      r->cur_exits = body_exits;
      r->used = 0;
      if (prev == NULL) {
        r->head = NULL; r->tail = NULL;  /* tail perform: identity resumption     */
      } else {
        prev->next = &g_done;            /* sever op-site..prev from the handler   */
        r->head = head; r->tail = prev;
      }
      /* §32.2.22 deep handlers reinstall themselves around the resumption; a
       * shallow handler does not.  Carry the reinstall context so the splice path
       * (do_resume) can re-push the SAME (label, ret, ops) beneath the body. */
      if (h->deep) {
        r->label = c->a; r->handler = h; r->handler_exits = handler_exits;
      } else {
        r->label = NULL; r->handler = NULL; r->handler_exits = NULL;
      }
      f->k = c->next;                  /* pop the handler: the clause runs outside  */
      f->cur_exits = handler_exits;    /* under the cur_exits the prompt restores   */
      return run_op_clause(rt, f, clause, payload, kfgn(r, KRT2_KIND_RESUMPTION));
    }
  }
}

/* OP_RESUME: splice the captured sub-chain back onto f->k and deliver `value`
 * (§2.4 — the twin of deliver's KK_BIND arm).  ONE-SHOT: a destructive pointer
 * move; the `used` guard is a backstop for the already-enforced compile gate. */
static int do_resume(Rt *rt, Fiber *f, KValue *kbox, KValue *value) {
  if (!kbox || kbox->tag != K_FGN) {
    return unwind(rt, f, RK_FAIL, kstr0("internal: resume of a non-resumption value"), NULL);
  }
  Resumption *r = (Resumption *)kas_fgn(kbox);
  if (r->used) {
    /* the compile-time E_QTT_CONTINUATION_CAPTURE gate rejects >1 use, so this
     * is an internal invariant break (rt-multishot is not advertised). */
    return unwind(rt, f, RK_FAIL,
                  kstr0("internal: one-shot resumption used more than once (rt-multishot absent)"), NULL);
  }
  r->used = 1;
  /* §32.2.22 deep reinstall: re-push the handler beneath the spliced body so the
   * resumed computation is re-handled.  do_perform POPPED the handler frame
   * (f->k advanced to c->next), so f->k now points at the handler's own
   * continuation; re-pushing a fresh KK_HANDLER here re-delimits the resumed
   * sub-chain, and a perform inside it finds this fresh handler again — exactly
   * the §18.1.22 deep recursive driver.  A shallow handler skips this (no
   * auto-reinstall, §18.1.21). */
  if (r->handler) {
    Handler *h = (Handler *)r->handler;
    f->k = cont_new2(KK_HANDLER, r->label, h, r->handler_exits, f->k);
  }
  /* Reinstate the captured body's exit-action state, then splice the sub-chain. */
  if (r->head) {
    r->tail->next = f->k;        /* re-link the severed tail onto the live chain  */
    f->k = r->head;              /* re-root at the op-site frame                  */
    f->cur_exits = r->cur_exits; /* re-enter under the captured do-scope state    */
  } else {
    /* identity resumption: nothing captured, deliver at the (re)installed point   */
    if (r->handler) f->cur_exits = r->cur_exits;
  }
  return deliver(rt, f, value);
}

/* Normal value path: feed v to the continuation.  Returns 1 to keep stepping,
 * 0 if the fiber finished. */
static int deliver(Rt *rt, Fiber *f, KValue *v) {
  Cont *c = f->k;
  switch (c->kind) {
    case KK_DONE:
      fiber_finish(rt, f, krt2_success(v));
      return 0;
    case KK_BIND:                       /* result v of m; run (k v) next      */
      f->k = c->next; f->cur = kapp(c->a, v); return 1;
    case KK_THEN:                       /* discard v; run the next action     */
      f->k = c->next; f->cur = c->a; return 1;
    case KK_CATCH:                       /* success path: catch is transparent */
      f->k = c->next; f->cur = krt2_pure(v); return 1;
    case KK_POPMASK:                     /* leaving an uninterruptible region   */
      if (f->mask_depth > 0) f->mask_depth--;
      f->k = c->next; f->cur = krt2_pure(v); return 1;
    case KK_SETMASK:                     /* restore mask to the stored level     */
      f->mask_depth = (uint32_t)(uintptr_t)c->aux;
      f->k = c->next; f->cur = krt2_pure(v); return 1;
    case KK_LOOP:                        /* an iteration body completed normally */
      f->cur = c->a;                     /* re-run `iterate`; KEEP the KK_LOOP    */
      return 1;
    case KK_RETSCOPE:                    /* body completed normally: transparent  */
      f->k = c->next; f->cur = krt2_pure(v); return 1;
    case KK_DOSCOPE: {                    /* normal exit: run exit actions, deliver v */
      ExitStack *xs = (ExitStack *)c->aux;
      ExitStack *restore = (ExitStack *)c->aux2;
      f->k = c->next;
      return begin_finseq(rt, f, xs, restore, RK_NORMAL, v, NULL);
    }
    case KK_FINSEQ: {                    /* a finalizer completed; run the next */
      FinSeq *fs = (FinSeq *)c->aux;
      if (fs->i >= 0) { KValue *e = fs->xs->items[fs->i]; fs->i--; f->cur = e; return 1; }
      f->k = c->next;
      return apply_reason(rt, f, fs->rkind, fs->rval, fs->rlabel);
    }
    case KK_HANDLER: {                    /* §18.1.21 body completed: run `return` */
      Handler *h = (Handler *)c->aux;
      f->k = c->next;
      f->cur_exits = (ExitStack *)c->aux2; /* leave the handled body's do-scopes  */
      f->cur = kapp(h->ret, v);            /* `case return x -> ...` (Eff res)     */
      return 1;
    }
  }
  return 0;
}

/* Abnormal propagation: a fail / return / break / continue / interrupt unwinding
 * the continuation, running do-scope exit actions en route (§18.8, §32.2.19). */
static int unwind(Rt *rt, Fiber *f, int rkind, KValue *rval, KValue *rlabel) {
  (void)rlabel;
  for (;;) {
    Cont *c = f->k;
    switch (c->kind) {
      case KK_DONE:
        switch (rkind) {
          case RK_RETURN:    fiber_finish(rt, f, krt2_success(rval)); return 0;
          case RK_FAIL:      fiber_finish(rt, f, krt2_failure(krt2_cause_fail(rval))); return 0;
          case RK_INTERRUPT: fiber_finish(rt, f, krt2_failure(krt2_cause_interrupt(rval))); return 0;
          case RK_RERAISE:   fiber_finish(rt, f, krt2_failure(rval)); return 0; /* rval IS the Cause */
          default:           /* break/continue with no enclosing loop (rejected upstream) */
            fiber_finish(rt, f, krt2_failure(krt2_cause_fail(
                kstr0("internal: break/continue escaped its loop")))); return 0;
        }
      case KK_BIND: case KK_THEN:
        f->k = c->next; continue;       /* the sequel does not run on an abnormal exit */
      case KK_POPMASK:
        if (f->mask_depth > 0) f->mask_depth--;
        f->k = c->next; continue;
      case KK_SETMASK:
        f->mask_depth = (uint32_t)(uintptr_t)c->aux;
        f->k = c->next; continue;
      case KK_CATCH:
        if (rkind == RK_FAIL) { f->k = c->next; f->cur = kapp(c->a, rval); return 1; }
        /* a re-raised Fail cause is still a typed failure — deliver its e to the
         * handler; a non-Fail reraise (Interrupt/Defect/…) skips catch. */
        if (rkind == RK_RERAISE && kctor_tagid(rval) == KCT_FAIL) {
          f->k = c->next; f->cur = kapp(c->a, kctor_arg(rval, 0)); return 1;
        }
        f->k = c->next; continue;       /* return/break/continue/interrupt skip catch */
      case KK_LOOP:
        if (rkind == RK_BREAK)    { f->k = c->next; f->cur = krt2_pure(kunit()); return 1; } /* exit loop */
        if (rkind == RK_CONTINUE) { f->cur = c->a; return 1; }   /* re-iterate, KEEP KK_LOOP */
        f->k = c->next; continue;       /* return/fail/interrupt pass through the loop */
      case KK_RETSCOPE:
        /* a `return` delimited by this scope: deliver its value HERE as the
         * scope's normal result (§18.8 — `return` exits the do-block, not the
         * fiber).  fail/break/continue/interrupt are not delimited here. */
        if (rkind == RK_RETURN) { f->k = c->next; f->cur = krt2_pure(rval); return 1; }
        f->k = c->next; continue;
      case KK_DOSCOPE: {
        ExitStack *xs = (ExitStack *)c->aux;
        ExitStack *restore = (ExitStack *)c->aux2;
        f->k = c->next;
        return begin_finseq(rt, f, xs, restore, rkind, rval, rlabel);
      }
      case KK_FINSEQ:
        /* A finalizer itself unwound.  With finalizers now masked (begin_finseq),
         * an ASYNC interrupt can no longer land mid-finseq, so this is reachable
         * only from a finalizer that itself fails; we abandon this scope's
         * remaining finalizers and keep propagating.  (Composing the failing
         * finalizer's cause with the primary via §32.2.12 `Then` is a remaining
         * refinement.)  c->next is the begin_finseq KK_POPMASK, so the mask
         * raised for this drain is restored as we continue unwinding. */
        f->k = c->next; continue;
      case KK_HANDLER:
        /* §18.1.21 a handler intercepts `perform`, NOT abrupt control flow: a
         * fail/return/break/continue/interrupt unwinding through the handled body
         * propagates past the prompt transparently (the body's captured do-scope
         * defers already ran on the KK_DOSCOPE frames crossed before reaching
         * here).  Restore the cur_exits the prompt would reinstate, then drop. */
        f->cur_exits = (ExitStack *)c->aux2;
        f->k = c->next; continue;
    }
    return 0;
  }
}

/* Deliver a pending interruption: unwind with Failure (Interrupt cause), running
 * exit actions in masked LIFO order on the way (§32.2.5).  Returns like unwind:
 * 1 if the fiber should keep stepping (a finalizer is now running), 0 if it
 * finished.  The caller MUST honor this — dropping a fiber whose finalizers are
 * still unwinding would deadlock anyone awaiting it. */
static int deliver_interrupt(Rt *rt, Fiber *f) {
  atomic_store_explicit(&f->interrupt_pending, 0, memory_order_relaxed);
  return unwind(rt, f, RK_INTERRUPT, f->interrupt_cause, NULL);
}

/* Step `f` until it suspends (parks / cedes) or finishes. */
static void fiber_step(Rt *rt, Fiber *f) {
  for (;;) {
    /* §32.2.5 interruption point: every loop turn (i.e. every IO step boundary)
     * is one.  Outside a masked region a pending request is delivered here. */
    if (atomic_load_explicit(&f->interrupt_pending, memory_order_acquire) && f->mask_depth == 0) {
      if (!deliver_interrupt(rt, f)) return; /* finished; else fall through to run finalizers */
    }
    KValue *cur = f->cur;
    int op = kctor_tagid(cur);
    switch (op) {
      case OP_PURE:
        if (!deliver(rt, f, kctor_arg(cur, 0))) return;
        break;
      case OP_BIND:
        f->k = cont_new(KK_BIND, kctor_arg(cur, 1), f->k);
        f->cur = kctor_arg(cur, 0);
        break;
      case OP_THEN:
        f->k = cont_new(KK_THEN, kctor_arg(cur, 1), f->k);
        f->cur = kctor_arg(cur, 0);
        break;
      case OP_CATCH:
        f->k = cont_new(KK_CATCH, kctor_arg(cur, 1), f->k);
        f->cur = kctor_arg(cur, 0);
        break;
      case OP_THROW:
        if (!unwind(rt, f, RK_FAIL, kctor_arg(cur, 0), NULL)) return;
        break;
      case OP_RERAISE:
        /* §18.1.4 re-raise a captured Cause as-is: catchable only if it is a
         * Fail (delivers the typed e); Interrupt/Defect/Both/Then propagate to
         * the fiber's Failure(cause) outcome.  Mirrors Interp.reraiseCauseValue. */
        if (!unwind(rt, f, RK_RERAISE, kctor_arg(cur, 0), NULL)) return;
        break;
      case OP_PRINT:
        emit_kstr(kctor_arg(cur, 0), 0);
        if (!deliver(rt, f, kunit())) return;
        break;
      case OP_PRINTLN:
        emit_kstr(kctor_arg(cur, 0), 1);
        if (!deliver(rt, f, kunit())) return;
        break;
      case OP_FORK:
        if (!deliver(rt, f, kfgn(krt2i_spawn(rt, kctor_arg(cur, 0), f->cur_scope, 0), KRT2_KIND_FIBER))) return;
        break;
      case OP_FORK_DAEMON:
        if (!deliver(rt, f, kfgn(krt2i_spawn(rt, kctor_arg(cur, 0), f->cur_scope, 1), KRT2_KIND_FIBER))) return;
        break;
      case OP_AWAIT:
        if (do_await(rt, f, kctor_arg(cur, 0))) break; else return;
      case OP_CEDE:
        f->cur = krt2_pure(kunit());
        krt2i_resume(rt, f);           /* re-enqueue behind other runnables  */
        return;
      case OP_SLEEP:
        krt2i_submit_sleep(rt, f, (uint64_t)kas_int(kctor_arg(cur, 0)));
        return;                        /* parked; reactor resumes it          */
      case OP_NOW:
        if (!deliver(rt, f, kint((int64_t)uv_hrtime()))) return;
        break;
      case OP_NEW_PROMISE:
        if (!deliver(rt, f, promise_new())) return;
        break;
      case OP_COMPLETE_PROMISE:
        if (!deliver(rt, f, promise_complete(rt, kctor_arg(cur, 0), kctor_arg(cur, 1)))) return;
        break;
      case OP_AWAIT_PROMISE_EXIT:
        if (do_await_promise(rt, f, kctor_arg(cur, 0))) break; else return;
      case OP_CURRENT_FIBER_ID:
        if (!deliver(rt, f, kint((int64_t)f->id))) return;
        break;
      case OP_FIBER_ID: {
        Fiber *tf = (Fiber *)kas_fgn(kctor_arg(cur, 0));
        if (!deliver(rt, f, kint((int64_t)tf->id))) return;
        break;
      }
      /* ── interruption + masking ─────────────────────────────────────── */
      case OP_INTERRUPT: {
        KValue *cause = (kctor_argc(cur) >= 2) ? kctor_arg(cur, 1)
            : krt2i_interrupt_cause("Requested", krt2i_some(kint((int64_t)f->id)));
        if (krt2i_op_interrupt(rt, f, kctor_arg(cur, 0), cause, 1)) break; else return;
      }
      case OP_INTERRUPT_FORK: {
        KValue *cause = (kctor_argc(cur) >= 2) ? kctor_arg(cur, 1)
            : krt2i_interrupt_cause("Requested", krt2i_some(kint((int64_t)f->id)));
        krt2i_op_interrupt(rt, f, kctor_arg(cur, 0), cause, 0);
        if (!deliver(rt, f, kunit())) return;
        break;
      }
      case OP_UNINTERRUPTIBLE:
        f->mask_depth++;
        f->k = cont_new(KK_POPMASK, NULL, f->k);
        f->cur = kctor_arg(cur, 0);
        break;
      case OP_POLL:                          /* deliver a pending interrupt even if masked */
        if (atomic_load_explicit(&f->interrupt_pending, memory_order_acquire)) {
          if (!deliver_interrupt(rt, f)) return; /* finished; else run its finalizers */
          break;
        }
        if (!deliver(rt, f, kunit())) return;
        break;
      case OP_MASK: {                          /* mask f: f gets `restore` (§18.1.12) */
        uint32_t outer = f->mask_depth;
        f->mask_depth++;
        f->k = cont_new2(KK_SETMASK, NULL, (void *)(uintptr_t)outer, NULL, f->k);
        KValue *restore = kclo(restore_fn, kpush(kint((int64_t)outer), NULL));
        f->cur = kapp(kctor_arg(cur, 0), restore);
        break;
      }
      case OP_RESTORE: {                       /* run an action at the mask-entry level */
        uint32_t saved = f->mask_depth;
        f->mask_depth = (uint32_t)kas_int(kctor_arg(cur, 1));
        f->k = cont_new2(KK_SETMASK, NULL, (void *)(uintptr_t)saved, NULL, f->k);
        f->cur = kctor_arg(cur, 0);
        break;
      }
      /* ── structured concurrency ─────────────────────────────────────── */
      case OP_NEW_SCOPE:
        if (!deliver(rt, f, krt2i_op_new_scope())) return;
        break;
      case OP_FORK_IN:
        if (!deliver(rt, f, krt2i_op_fork_in(rt, kctor_arg(cur, 0), kctor_arg(cur, 1)))) return;
        break;
      case OP_SHUTDOWN_SCOPE:
        if (krt2i_op_shutdown_scope(rt, f, kctor_arg(cur, 0))) break; else return;
      case OP_MONITOR:
        if (!deliver(rt, f, krt2i_op_monitor(kctor_arg(cur, 0)))) return;
        break;
      case OP_AWAIT_MONITOR:
        if (krt2i_op_await_monitor(rt, f, kctor_arg(cur, 0))) break; else return;
      /* ── do-kernel completion channel ───────────────────────────────── */
      case OP_DOSCOPE: {
        ExitStack *xs = exitstack_new();
        f->k = cont_new2(KK_DOSCOPE, NULL, xs, f->cur_exits, f->k);
        f->cur_exits = xs;
        f->cur = kctor_arg(cur, 0);          /* the do-scope body */
        break;
      }
      case OP_DEFER:
        /* §18.7: a defer must run exactly once on every exit, so it must land on
         * an enclosing do-scope's ExitStack.  A defer with no current scope is a
         * mis-lowering; silently skipping it (the old behavior) fails OPEN —
         * trap so a mis-lowered defer is a diagnosed error, not a dropped action. */
        if (!f->cur_exits) krt_fail("internal: defer outside any do-scope (mis-lowered §18.7 defer)");
        exitstack_push(f->cur_exits, kctor_arg(cur, 0));
        if (!deliver(rt, f, kunit())) return;
        break;
      case OP_RETURN:
        if (!unwind(rt, f, RK_RETURN, kctor_arg(cur, 0), NULL)) return;
        break;
      case OP_RETSCOPE:                       /* delimit `return` to this body */
        f->k = cont_new(KK_RETSCOPE, NULL, f->k);
        f->cur = kctor_arg(cur, 0);
        break;
      case OP_BREAK:
        if (!unwind(rt, f, RK_BREAK, NULL, NULL)) return;
        break;
      case OP_CONTINUE:
        if (!unwind(rt, f, RK_CONTINUE, NULL, NULL)) return;
        break;
      case OP_WHILE: {
        KValue *iterate = krt2_bind(kctor_arg(cur, 0),
                                    kclo(loop_branch, kpush(kctor_arg(cur, 1), NULL)));
        f->k = cont_new2(KK_LOOP, iterate, NULL, NULL, f->k);
        f->cur = iterate;
        break;
      }
      case OP_NEW_REF:
        if (!deliver(rt, f, kref_new(kctor_arg(cur, 0)))) return;
        break;
      case OP_READ_REF:
        if (!deliver(rt, f, kref_get(kctor_arg(cur, 0)))) return;
        break;
      case OP_WRITE_REF:
        kref_set(kctor_arg(cur, 0), kctor_arg(cur, 1));
        if (!deliver(rt, f, kunit())) return;
        break;
      case OP_TRY_EXIT: {                       /* non-blocking: Some Exit iff DONE */
        Fiber *tf = (Fiber *)kas_fgn(kctor_arg(cur, 0));
        pthread_mutex_lock(&tf->lock);
        KValue *r = (atomic_load_explicit(&tf->status, memory_order_acquire) == F_DONE)
                        ? krt2i_some(tf->exit) : krt2i_none();
        pthread_mutex_unlock(&tf->lock);
        if (!deliver(rt, f, r)) return;
        break;
      }
      case OP_ATOMICALLY:                       /* run an STM transaction (§18.1.13) */
        if (krt2i_op_atomically(rt, f, kctor_arg(cur, 0))) break; else return;
      /* ── §18.1.21/.22 effect handlers (Stage 4a, one-shot) ──────────────── */
      case OP_HANDLE: {                          /* install a KK_HANDLER prompt   */
        Handler *h = (Handler *)GC_MALLOC(sizeof(Handler));
        h->deep = (kctor_tagid(kctor_arg(cur, 0)) == KCT_TRUE);
        h->ret  = kctor_arg(cur, 2);
        h->ops  = kctor_arg(cur, 3);
        /* aux2 saves the cur_exits to reinstate when the prompt is removed (the
         * return clause and op clauses run OUTSIDE the handled body's scopes). */
        f->k = cont_new2(KK_HANDLER, kctor_arg(cur, 1), h, f->cur_exits, f->k);
        f->cur = kctor_arg(cur, 4);              /* the handled body (an Eff comp) */
        break;
      }
      case OP_PERFORM:                           /* perform label.op payload      */
        if (do_perform(rt, f, kctor_arg(cur, 0), kctor_arg(cur, 1), kctor_arg(cur, 2)))
          break; else return;
      case OP_RESUME:                            /* resume k value                */
        if (do_resume(rt, f, kctor_arg(cur, 0), kctor_arg(cur, 1))) break; else return;
      default:
        /* §18.1.21 UNIFICATION: the §30.2.2.7 OpCall free-monad tree IS the same
         * algebraic-effect term as a CK-machine Cont chain.  When an Eff node
         * reaches the scheduler (under a KK_HANDLER prompt installed by OP_HANDLE)
         * interpret it directly so the handler clause runs on the scheduler and
         * may park — instead of the pure kpf___handleEff tree rewrite.
         *
         * These checks come BEFORE the kis_imm bare-value delivery: an `__EffPure v`
         * whose v is itself immediate is UNBOXING-packed (b011), so kis_imm(cur) is
         * true even though it is a constructor we must UNWRAP, not deliver raw.
         * kctor_tagid decodes a packed immediate correctly. */
        if (kctor_tagid(cur) == KCT_EFFPURE) {   /* __EffPure v: finished -> v     */
          if (!deliver(rt, f, kctor_arg(cur, 0))) return;
          break;
        }
        if (kctor_tagid(cur) == KCT_EFFOP) {     /* __EffOp label op payload cont  */
          /* perform the op; feed its result to `cont` (the captured continuation
           * carried in the tree node).  cont yields a further Eff node, so bind it
           * with KK_BIND and step the perform. */
          f->k = cont_new(KK_BIND, kctor_arg(cur, 3), f->k);
          f->cur = krt2_perform(kctor_arg(cur, 0), kctor_arg(cur, 1), kctor_arg(cur, 2));
          break;
        }
        /* UNBOXING Stage 1: an immediate Int (or any other immediate value) is a
         * bare result, not a krt2_* node or legacy IO action — hand it straight
         * to the continuation, never dereferencing the odd word. */
        if (kis_imm(cur)) { if (!deliver(rt, f, cur)) return; break; }
        switch (cur->tag) {
          /* v2 BRIDGE: a legacy kappart IO action — emitted by generated code
           * not yet CPS-lowered to krt2_* nodes (the do-kernel still uses
           * krun_io/kpf_io_*).  Drive it via the legacy krun_io synchronously on
           * this worker.  Sequential programs run on the scheduler this way;
           * concurrency (fork/await suspension) needs the do-kernel CPS rewrite
           * (INTEGRATION.md).  A typed K_FAIL propagates as RK_FAIL. */
          case K_IO: case K_IOTAIL: case K_IOEFFECT: case K_IOFINALLY:
          case K_BOUNCE: case K_NATIVE: case K_FAIL: {
            KValue *r = krun_io(cur);
            if (kis_fail(r)) { if (!unwind(rt, f, RK_FAIL, r->as.fail.err, NULL)) return; break; }
            if (!deliver(rt, f, r)) return;
            break;
          }
          default:
            /* a bare value reached the driver — hand it to the continuation. */
            if (!deliver(rt, f, cur)) return;
            break;
        }
        break;
    }
  }
}

/* §18.1.14 runPure : Eff <[]> a -> a.  Drive a FULLY-HANDLED Eff computation to
 * its value on a private CK-machine, SYNCHRONOUSLY on the calling thread.  A
 * pure Eff (empty residual row) has no scheduler effects, so fiber_step never
 * parks; it steps the OP_HANDLE/OP_PERFORM/OP_RESUME (and __EffOp/__EffPure)
 * tree to a single delivered value.  This is the unified driver that lets a
 * handler installed by `handle` run on the CK-machine (so its clause may park)
 * while `runPure` remains a pure eliminator usable in expression position.
 *
 * The private fiber's KK_DONE arm sets f->exit = Success(v); we read it back.
 * No workers/reactor run — the steps are all synchronous (pure) — so a stray
 * park would leave f not-DONE and we trap rather than hang. */
KValue *krt2_run_eff(KValue *comp) {
  Rt *rt = g_rt ? g_rt : krt2_new(0);
  Fiber *f = fiber_new(rt, comp);
  /* keep it GC-reachable for the duration (it holds the live Cont chain);
   * fiber_finish drops it from rt->all on the KK_DONE arm. */
  krt2i_all_add(rt, f);
  atomic_store(&f->status, F_RUNNING);
  fiber_step(rt, f);
  if (atomic_load_explicit(&f->status, memory_order_acquire) != F_DONE) {
    krt_fail("runPure: computation parked (a pure Eff must not reach the scheduler)");
    return 0;
  }
  KValue *ex = f->exit;
  if (kctor_tagid(ex) == KCT_SUCCESS) return kctor_arg(ex, 0);
  /* a Failure escaped runPure: surface it (an unhandled op / clause failure). */
  krt_fail("runPure: computation is not fully handled (an operation escaped its handlers)");
  return 0;
}
KValue *kpf_run_eff(KValue **a) { return krt2_run_eff(a[0]); }

void krt2_safepoint(void) { /* spine: cooperative budget is a perf/fairness TODO (§6.4) */ }

/* ── workers ────────────────────────────────────────────────────────────── */
static void *worker_main(void *arg) {
  /* Created via GC_pthread_create, so this thread is already known to the
   * collector (registered on entry, unregistered on exit) — do NOT call
   * GC_register_my_thread here or the double registration corrupts the
   * per-thread freelists. */
  Rt *rt = (Rt *)arg;
  for (;;) {
    Fiber *f = rq_pop(rt);
    if (!f) break;
    atomic_store(&f->status, F_RUNNING);
    fiber_step(rt, f);
  }
  return NULL;
}

/* ── lifecycle ──────────────────────────────────────────────────────────── */
static int default_workers(void) {
  const char *env = getenv("KAPPA_RT_WORKERS");
  if (env && *env) { int n = atoi(env); if (n > 0) return n; }
  long ncpu = sysconf(_SC_NPROCESSORS_ONLN);
  if (ncpu < 1) ncpu = 1;
  if (ncpu > 64) ncpu = 64;
  return (int)ncpu;
}

/* Pre-populate the kappart value singletons on the main thread BEFORE workers
 * start, so their lazy-init store-store races never happen in parallel
 * (REVIEW.md M6). */
static void prepopulate_singletons(void) {
  (void)kunit();
  (void)kbool(1); (void)kbool(0);
  for (int i = -16; i <= 256; i++) (void)kint(i); /* warms kint_cache */
}

Rt *krt2_new(int nworkers) {
  if (g_rt) return g_rt;
  krt_init();                  /* GC_INIT + GMP-through-GC (kappart) */
  GC_allow_register_threads(); /* permit worker/reactor thread registration */
  prepopulate_singletons();

  Rt *rt = (Rt *)GC_MALLOC(sizeof(Rt));
  rt->nworkers = nworkers > 0 ? nworkers : default_workers();
  rt->workers = (pthread_t *)GC_MALLOC(sizeof(pthread_t) * rt->nworkers);
  pthread_mutex_init(&rt->rq_lock, NULL);
  pthread_cond_init(&rt->rq_cv, NULL);
  pthread_mutex_init(&rt->all_lock, NULL);
  pthread_mutex_init(&rt->done_lock, NULL);
  pthread_cond_init(&rt->done_cv, NULL);
  pthread_mutex_init(&rt->io_lock, NULL);
  atomic_store(&rt->next_id, 0);
  atomic_store(&rt->shutting_down, 0);
  atomic_store(&rt->reactor_stop, 0);
  rt->rq_head = rt->rq_tail = NULL;
  rt->io_head = rt->io_tail = NULL;
  rt->all = NULL;
  rt->main_fiber = NULL;
  rt->main_done = 0;
  rt->rq_idle = 0;
  rt->reactor_started = 0;

  krt2i_reactor_init(rt);      /* uv_loop_init + uv_async_init (main thread) */
  g_rt = rt;
  return rt;
}

Rt *krt2_current(void) { return g_rt; }

int krt2_exit_is_success(KValue *exit) { return kctor_is(exit, "Success"); }

KValue *krt2_run_main(KValue *action) {
  Rt *rt = g_rt ? g_rt : krt2_new(0);

  /* The root supervision scope (§32.2.3).  Wrap main so that on EVERY exit
   * (normal, failure, interrupt) it shuts the root scope down — interrupting and
   * awaiting any root-level forked children before main terminates — instead of
   * abandoning them when the workers are joined.  With no root children the
   * shutdown is a no-op, so the common case is unaffected. */
  Scope *root = krt2i_scope_new();
  KValue *root_h = kfgn(root, KRT2_KIND_SCOPE);
  KValue *wrapped = krt2_ensuring(action, krt2_shutdown_scope(root_h));

  Fiber *m = fiber_new(rt, wrapped);
  m->cur_scope = root;
  rt->main_fiber = m;
  krt2i_all_add(rt, m);

  krt2i_reactor_start(rt);
  for (int i = 0; i < rt->nworkers; i++)
    GC_pthread_create(&rt->workers[i], NULL, worker_main, rt);

  krt2i_resume(rt, m);         /* enqueue the main fiber */

  pthread_mutex_lock(&rt->done_lock);
  while (!rt->main_done) pthread_cond_wait(&rt->done_cv, &rt->done_lock);
  pthread_mutex_unlock(&rt->done_lock);

  krt2_shutdown(rt);
  return m->exit;
}

void krt2_shutdown(Rt *rt) {
  if (!rt) return;
  atomic_store_explicit(&rt->shutting_down, 1, memory_order_release);
  pthread_mutex_lock(&rt->rq_lock);
  pthread_cond_broadcast(&rt->rq_cv);
  pthread_mutex_unlock(&rt->rq_lock);
  for (int i = 0; i < rt->nworkers; i++) GC_pthread_join(rt->workers[i], NULL);
  krt2i_reactor_stop(rt);
  /* A shut-down runtime must not remain the active one: clearing g_rt lets a
   * subsequent krt2_run_main / krt2_new build a fresh runtime instead of reusing
   * one with workers joined and shutting_down/main_done still set. */
  if (g_rt == rt) g_rt = NULL;
}

void krt2_dump(void *out) {
  FILE *o = out ? (FILE *)out : stderr;
  Rt *rt = g_rt;
  if (!rt) { fprintf(o, "[kappart2] no runtime\n"); return; }
  pthread_mutex_lock(&rt->all_lock);
  int live = 0;
  for (Fiber *f = rt->all; f; f = f->all_next) live++;
  pthread_mutex_unlock(&rt->all_lock);
  fprintf(o, "[kappart2] workers=%d live_fibers=%d\n", rt->nworkers, live);
}
