/* rt.c — kappart2 core: lifecycle, the M:N scheduler, the stackless CK-machine,
 * fibers (fork/await/cede), promises, the action-node builders, and the
 * Exit/Cause constructors.  See internal.h for the two concurrency protocols
 * (park/wake under a per-object lock; GC liveness via the rt->all strong set)
 * and DESIGN.md for the architecture.  This file is the v1 spine; STM, scopes,
 * interruption/masking, atomics, and race/timeout are the next increments. */
#include "internal.h"

#include <assert.h>
#include <gc.h>
#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

Rt *g_rt = NULL;

/* §32.2.6 safe points (fix SP): the fiber the calling worker thread is currently
 * stepping.  Set on entry to fiber_step and cleared on exit, so a codegen-emitted
 * native loop running ON this worker (inside the synchronous K_NATIVE bridge) can
 * reach its fiber from a bare `krt2_safepoint()` call with no extra plumbing.  A
 * worker steps exactly one fiber at a time, so a thread-local is exactly right
 * (and never shared across workers). */
static _Thread_local Fiber *g_cur_fiber = NULL;
static _Thread_local Rt    *g_cur_rt = NULL;
static _Thread_local jmp_buf *g_scalar_abort_jmp = NULL;
static _Thread_local int g_safepoint_yielding = 0;
static _Thread_local int g_on_blocking_lane = 0;

/* Back-edges between fairness cedes (fix SP).  A power of two so the budget reload
 * is a single store.  Large enough that the per-iteration check is free in the hot
 * loop (a register decrement + predictable branch), small enough that a tight loop
 * yields to other runnables within a bounded number of iterations (weak fairness). */
#define KRT2_BACKEDGE_QUANTUM 4096u

const char *const KRT2_CAPABILITIES[] = {
  "rt-core", "rt-parallel", "rt-blocking", "rt-shared-stm", "rt-atomics", NULL
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
KValue *krt2_blocking(KValue *body)       { return op1(OP_BLOCKING, "rt.blocking", body); }

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
KValue *kpf_blocking(KValue **a)           { return krt2_blocking(a[0]); }
/* §18.1.10 fiber identity: build the OP_CURRENT_FIBER_ID / OP_FIBER_ID nodes;
 * the CK-machine delivers the running/target fiber's integer id (rt.c case). */
KValue *kpf_current_fiber_id(KValue **a)   { (void)a; return krt2_current_fiber_id(); }
KValue *kpf_fiber_id(KValue **a)           { return krt2_fiber_id(a[0]); }
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

/* §18.1.4 onExit/onInterrupt: run `body`, then on exit run `handler` applied to
 * the scope's terminal Exit (onExit, EVERY exit) or InterruptCause (onInterrupt,
 * ONLY on interrupt).  Built exactly like `finally` — a do-scope whose first
 * registered exit-action is a REASON-CARRYING marker node.  The marker carries
 * the handler; the KK_FINSEQ drain detects it (OP_ONEXIT_FIN/OP_ONINT_FIN),
 * reconstructs the Exit/cause, and substitutes the handler application.  The
 * marker itself never runs as an ordinary action.  `body`'s result is preserved
 * (the do-scope is `ensuring`, not `then`).  */
KValue *krt2_on_exit(KValue *body, KValue *handler) {
  KValue *marker = op1(OP_ONEXIT_FIN, "rt.onExitFin", handler);
  return krt2_doscope(krt2_then(krt2_defer(marker), body));
}
KValue *krt2_on_interrupt(KValue *body, KValue *handler) {
  KValue *marker = op1(OP_ONINT_FIN, "rt.onIntFin", handler);
  return krt2_doscope(krt2_then(krt2_defer(marker), body));
}
KValue *kpf_on_exit(KValue **a)      { return krt2_on_exit(a[0], a[1]); }
KValue *kpf_on_interrupt(KValue **a) { return krt2_on_interrupt(a[0], a[1]); }

/* §18.1.7 FiberRef node-builders + kpf shims. */
KValue *krt2_new_fiber_ref(KValue *init)        { return op1(OP_NEW_FIBER_REF, "rt.newFiberRef", init); }
KValue *krt2_get_fiber_ref(KValue *r)           { return op1(OP_GET_FIBER_REF, "rt.getFiberRef", r); }
KValue *krt2_set_fiber_ref(KValue *r, KValue *v){ return op2(OP_SET_FIBER_REF, "rt.setFiberRef", r, v); }
KValue *krt2_modify_fiber_ref(KValue *r, KValue *fn) { return op2(OP_MODIFY_FIBER_REF, "rt.modifyFiberRef", r, fn); }
KValue *kpf_new_fiber_ref(KValue **a)    { return krt2_new_fiber_ref(a[0]); }
KValue *kpf_get_fiber_ref(KValue **a)    { return krt2_get_fiber_ref(a[0]); }
KValue *kpf_set_fiber_ref(KValue **a)    { return krt2_set_fiber_ref(a[0], a[1]); }
KValue *kpf_modify_fiber_ref(KValue **a) { return krt2_modify_fiber_ref(a[0], a[1]); }

/* §18.11 Promise.poll / Promise.isDone node-builders + kpf shims. */
KValue *krt2_poll_promise(KValue *p)    { return op1(OP_POLL_PROMISE, "rt.pollP", p); }
KValue *krt2_is_done_promise(KValue *p) { return op1(OP_IS_DONE_PROMISE, "rt.isDoneP", p); }
KValue *kpf_poll_promise(KValue **a)    { return krt2_poll_promise(a[0]); }
KValue *kpf_is_done_promise(KValue **a) { return krt2_is_done_promise(a[0]); }

/* §18.1.7 locallyFiberRef ref val body = install `val` for the dynamic extent of
 * `body`, restoring the prior value on EVERY exit (a masked finalizer, via the
 * same doscope/defer machinery as `finally`).  Composed over the get/set/finally
 * node-builders so the read of the prior value is a CK-machine action (read at
 * entry, not captured at build time):
 *   bind(getFiberRef ref, \old -> then(setFiberRef ref val,
 *                                       finally(body, setFiberRef ref old))) */
static KValue *locally_with_old(KEnv *env, KValue *old) { /* env = [ref, val, body] */
  KValue *ref = kvar(env, 0), *val = kvar(env, 1), *body = kvar(env, 2);
  return krt2_then(krt2_set_fiber_ref(ref, val),
                   krt2_finally(body, krt2_set_fiber_ref(ref, kdup(old))));
}
KValue *krt2_locally_fiber_ref(KValue *ref, KValue *val, KValue *body) {
  return krt2_bind(krt2_get_fiber_ref(ref),
                   kclo(locally_with_old, kpush(ref, kpush(val, kpush(body, NULL)))));
}
KValue *kpf_locally_fiber_ref(KValue **a) { return krt2_locally_fiber_ref(a[0], a[1], a[2]); }

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

static ExitStack *exitstack_new(void);
static void exitstack_push(ExitStack *s, KValue *action);
static KValue *exit_of_reason(int rkind, KValue *rval);
static void compose_reason_into(int *io_kind, KValue **io_val, int c_kind, KValue *c_val);
static void emit_kstr(KValue *s, int newline);
static KValue *abort_exit_take(KValue *token);
static ExitStack *abort_exit_drain_stack(Fiber *f);
static KValue *abort_exit_scope_finalizer(KValue *exit_action);
static KValue *finalizer_action_for_reason(KValue *fin, int erkind, KValue *rval);
static KValue *interrupt_cause_of_reason(int rkind, KValue *rval);
static int deliver_interrupt(Rt *rt, Fiber *f);

int krt2_is_reraise_action(KValue *v) {
  return v && !kis_imm(v) && kctor_tagid(v) == OP_RERAISE;
}

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
 * Drive the NON-suspending OPs here with exactly the legacy bridge's semantics:
 * krun_io recursion for sub-actions; OP_BIND/OP_THEN/OP_CATCH trampolined so a
 * straight chain stays flat; and OP_DOSCOPE/OP_DEFER using a local ExitStack so
 * lazy deferred actions that build a `finallyIO` tree still use the same
 * language-level do-kernel nodes.  A genuinely suspending node
 * (OP_FORK/OP_AWAIT/…) never reaches the bridge — those blocks are CPS-lowered
 * onto the CK-machine — and a non-OP value (a data ctor, a `return`ed result) is
 * returned unchanged. */
static KValue *krt2_run_op_sync_ret(KValue *action, ExitStack *scope, int *control);

static KValue *krt2_run_sync_operand(KValue *action, ExitStack *scope, int *control) {
  if (kis_imm(action) && kctor_tagid(action) < KRT2_OP_BASE) return action;
  return krt2_run_op_sync_ret(action, scope, control);
}

static void krt2_sync_reason(KValue *r, int control, int *rkind, KValue **rval) {
  if (control == RK_RETURN) {
    *rkind = RK_RETURN;
    *rval = r;
  } else if (control == RK_BREAK) {
    *rkind = RK_BREAK;
    *rval = NULL;
  } else if (control == RK_CONTINUE) {
    *rkind = RK_CONTINUE;
    *rval = NULL;
  } else if (control == RK_RERAISE) {
    *rkind = RK_RERAISE;
    *rval = r;
  } else if (krt2_is_reraise_action(r)) {
    *rkind = RK_RERAISE;
    *rval = kctor_arg(r, 0);
  } else if (kis_fail(r)) {
    *rkind = RK_FAIL;
    *rval = r->as.fail.err;
  } else {
    *rkind = RK_NORMAL;
    *rval = r;
  }
}

static KValue *krt2_sync_apply_reason(int rkind, KValue *rval, int *control) {
  switch (rkind) {
    case RK_NORMAL:
      return rval;
    case RK_RETURN:
      *control = RK_RETURN;
      return rval;
    case RK_BREAK:
      *control = RK_BREAK;
      return kunit();
    case RK_CONTINUE:
      *control = RK_CONTINUE;
      return kunit();
    case RK_FAIL:
      return kfail(rval);
    case RK_RERAISE:
      if (!kis_imm(rval) && kctor_tagid(rval) == KCT_FAIL) return kfail(kctor_arg(rval, 0));
      *control = RK_RERAISE;
      return rval;
    default:
      krt_fail("internal: abrupt control escaped synchronous IO bridge");
      return 0;
  }
}

static KValue *krt2_sync_reify_reason(int rkind, KValue *rval) {
  int control = RK_NORMAL;
  KValue *r = krt2_sync_apply_reason(rkind, rval, &control);
  if (control == RK_RERAISE) return krt2_reraise(r);
  return r;
}

static KValue *krt2_run_op_sync_ret(KValue *action, ExitStack *scope, int *control) {
  for (;;) {
    if (kis_imm(action)) {
      if (kctor_tagid(action) < KRT2_OP_BASE) return action;
    } else {
      switch (action->tag) {
        case K_IOTAIL:
          action = action->as.bounce.fn;
          continue;
        case K_IO: {
          KValue *r = action->as.io.fn(action->as.io.env);
          if (kis_imm(r)) {
            if (kctor_tagid(r) < KRT2_OP_BASE) return r;
            action = r;
            continue;
          }
          if (r->tag == K_IOTAIL) { action = r->as.bounce.fn; continue; }
          if (r->tag == K_IOEFFECT || r->tag == K_IOFINALLY) {
            KValue *rr = krun_io(r);
            if (krt2_is_reraise_action(rr)) {
              *control = RK_RERAISE;
              return kctor_arg(rr, 0);
            }
            return rr;
          }
          if (krt2_is_reraise_action(r)) {
            *control = RK_RERAISE;
            return kctor_arg(r, 0);
          }
          return r;
        }
        case K_NATIVE:
          if (action->as.native.argc < action->as.native.arity)
            krt_fail("internal: native action run before saturation");
          {
            KValue *r = action->as.native.fn(action->as.native.args);
            if (krt2_is_reraise_action(r)) {
              *control = RK_RERAISE;
              return kctor_arg(r, 0);
            }
            return r;
          }
        case K_FAIL:
          return action;
        default:
          break;
      }
    }
    switch (kctor_tagid(action)) {
      case OP_PURE:
        return kctor_arg(action, 0);
      case OP_BIND: {
        int sub_control = RK_NORMAL;
        KValue *r = krt2_run_sync_operand(kctor_arg(action, 0), scope, &sub_control);
        if (sub_control != RK_NORMAL) { *control = sub_control; return r; }
        if (kis_fail(r)) return r;
        action = kapp(kctor_arg(action, 1), r);
        continue;
      }
      case OP_THEN: {
        int sub_control = RK_NORMAL;
        KValue *r = krt2_run_sync_operand(kctor_arg(action, 0), scope, &sub_control);
        if (sub_control != RK_NORMAL) { *control = sub_control; return r; }
        if (kis_fail(r)) return r;
        action = kctor_arg(action, 1);
        continue;
      }
      case OP_CATCH: {
        int sub_control = RK_NORMAL;
        KValue *r = krt2_run_sync_operand(kctor_arg(action, 0), scope, &sub_control);
        if (sub_control != RK_NORMAL) { *control = sub_control; return r; }
        if (!kis_fail(r)) return r;
        action = kapp(kctor_arg(action, 1), r->as.fail.err); /* run handler on the error */
        continue;
      }
      case OP_THROW:
        return kfail(kctor_arg(action, 0));
      case OP_PRINT:
        emit_kstr(kctor_arg(action, 0), 0);
        return kunit();
      case OP_PRINTLN:
        emit_kstr(kctor_arg(action, 0), 1);
        return kunit();
      case OP_RERAISE: {
        KValue *cause = kctor_arg(action, 0);
        if (!kis_imm(cause) && kctor_tagid(cause) == KCT_FAIL) return kfail(kctor_arg(cause, 0));
        *control = RK_RERAISE;
        return cause;
      }
      case OP_RETURN:
        *control = RK_RETURN;
        return kctor_arg(action, 0);
      case OP_RETSCOPE: {
        int body_control = RK_NORMAL;
        KValue *r = krt2_run_sync_operand(kctor_arg(action, 0), scope, &body_control);
        if (kis_fail(r)) return r;
        if (body_control == RK_RERAISE) {
          *control = RK_RERAISE;
          return r;
        }
        if (body_control == RK_BREAK || body_control == RK_CONTINUE) {
          *control = body_control;
          return r;
        }
        return r; /* catch OP_RETURN here; normal completion is transparent. */
      }
      case OP_DOSCOPE: {
        ExitStack *xs = exitstack_new();
        int body_control = RK_NORMAL;
        KValue *r = krt2_run_sync_operand(kctor_arg(action, 0), xs, &body_control);
        int rkind = RK_NORMAL;
        KValue *rval = NULL;
        krt2_sync_reason(r, body_control, &rkind, &rval);
        int origin_kind = rkind;
        KValue *origin_val = rval;
        Fiber *masked_fiber = g_cur_fiber;
        if (masked_fiber) masked_fiber->mask_depth++;
        for (int i = xs->n - 1; i >= 0; i--) {
          KValue *fin = finalizer_action_for_reason(xs->items[i], origin_kind, origin_val);
          int fin_control = RK_NORMAL;
          KValue *fr = krt2_run_sync_operand(fin, scope, &fin_control);
          int ckind = RK_NORMAL;
          KValue *cval = NULL;
          krt2_sync_reason(fr, fin_control, &ckind, &cval);
          compose_reason_into(&rkind, &rval, ckind, cval);
        }
        if (masked_fiber && masked_fiber->mask_depth > 0) masked_fiber->mask_depth--;
        return krt2_sync_apply_reason(rkind, rval, control);
      }
      case OP_DEFER:
        if (!scope) krt_fail("internal: defer outside any do-scope (mis-lowered §18.7 defer)");
        exitstack_push(scope, abort_exit_scope_finalizer(kctor_arg(action, 0)));
        return kunit();
      case OP_ABORT_EXIT_FIN: {
        KValue *exit_action = abort_exit_take(kctor_arg(action, 0));
        if (!exit_action) return kunit();
        return krt2_run_sync_operand(exit_action, scope, control);
      }
      case OP_WHILE: {
        KValue *cond = kctor_arg(action, 0);
        KValue *body = kctor_arg(action, 1);
        uint32_t spc = KRT2_SP_QUANTUM;
        for (;;) {
          int cond_control = RK_NORMAL;
          KValue *c = krt2_run_sync_operand(cond, scope, &cond_control);
          if (cond_control != RK_NORMAL) { *control = cond_control; return c; }
          if (kis_fail(c)) return c;
          if (!kas_bool(c)) return kunit();

          int body_control = RK_NORMAL;
          KValue *r = krt2_run_sync_operand(krt2_doscope(body), scope, &body_control);
          if (kis_fail(r)) return r;
          if (body_control == RK_BREAK) return kunit();
          if (--spc == 0) {
            spc = KRT2_SP_QUANTUM;
            if (krt2_safepoint()) krt2_scalar_abort();
          }
          if (body_control == RK_CONTINUE) continue;
          if (body_control != RK_NORMAL) { *control = body_control; return r; }
        }
      }
      case OP_BREAK:
        *control = RK_BREAK;
        return kunit();
      case OP_CONTINUE:
        *control = RK_CONTINUE;
        return kunit();
      case OP_NEW_REF:
        return kref_new(kctor_arg(action, 0));
      case OP_READ_REF:
        return kref_get(kctor_arg(action, 0));
      case OP_WRITE_REF:
        kref_set(kctor_arg(action, 0), kctor_arg(action, 1));
        return kunit();
      default:
        if (!kis_imm(action) && kctor_tagid(action) >= KRT2_OP_BASE)
          krt_fail("internal: unsupported OP reached synchronous IO bridge; block must be CPS-lowered");
        /* not an OP node: a value / data ctor, returned as-is. */
        return action;
    }
  }
}

KValue *krt2_run_op_sync(KValue *action) {
  int control = RK_NORMAL;
  KValue *r = krt2_run_sync_operand(action, NULL, &control);
  if (control == RK_RETURN) return krt2_return(r);
  if (control == RK_RERAISE) return krt2_sync_reify_reason(RK_RERAISE, r);
  if (control == RK_BREAK || control == RK_CONTINUE)
    krt_fail("internal: loop control escaped synchronous IO bridge");
  return r;
}

typedef struct BlockingReq {
  Rt *rt;
  Fiber *fiber;
  KValue *action;
  int resume_existing;
} BlockingReq;

static BlockingReq *blocking_req_alloc(void) {
  BlockingReq *req = (BlockingReq *)GC_MALLOC_UNCOLLECTABLE(sizeof(BlockingReq));
  if (!req) krt_fail("rt.blocking: failed to allocate blocking request");
  return req;
}

static void blocking_req_free(BlockingReq *req) {
  kgc_free(req);
}

static void fiber_step(Rt *rt, Fiber *f);

static void *blocking_worker_main(void *arg) {
  BlockingReq *req = (BlockingReq *)arg;
  Fiber *f = req->fiber;

  /* Source-level `blocking body` accepts arbitrary IO (§18.1.11), not just the
   * legacy sync-bridge subset.  Once the off-worker thread owns the parked
   * fiber, run the ordinary CK machine on that same fiber.  If the body parks
   * (sleep/await/STM/etc.) or cedes, those operations publish the next status
   * and enqueue/wake through the normal scheduler paths; if it completes or
   * fails, deliver/unwind/finalizers run here exactly as they would on a worker. */
  pthread_mutex_lock(&f->lock);
  if (!req->resume_existing) f->cur = req->action;
  f->blocking_armed = 0;
  atomic_store_explicit(&f->status, F_RUNNING, memory_order_release);
  pthread_mutex_unlock(&f->lock);

  int saved_blocking_lane = g_on_blocking_lane;
  g_on_blocking_lane = 1;
  if (atomic_load_explicit(&f->interrupt_pending, memory_order_acquire)
      && f->mask_depth == 0) {
    if (deliver_interrupt(req->rt, f)) fiber_step(req->rt, f);
  } else {
    fiber_step(req->rt, f);
  }
  g_on_blocking_lane = saved_blocking_lane;
  blocking_req_free(req);
  return NULL;
}

static int krt2i_submit_blocking(Rt *rt, Fiber *f, KValue *action) {
  BlockingReq *req = blocking_req_alloc();
  krc_mark_shared_recursive(action);
  krt2i_mark_fiber_shared(f);
  req->rt = rt;
  req->fiber = f;
  req->action = action;
  req->resume_existing = 0;
  pthread_mutex_lock(&f->lock);
  f->blocking_armed = 1;
  atomic_store_explicit(&f->status, F_PARKED, memory_order_release);
  pthread_mutex_unlock(&f->lock);
  pthread_t t;
  if (krt2i_spawn_thread(&t, blocking_worker_main, req) != 0) {
    pthread_mutex_lock(&f->lock);
    f->blocking_armed = 0;
    atomic_store_explicit(&f->status, F_RUNNING, memory_order_release);
    pthread_mutex_unlock(&f->lock);
    blocking_req_free(req);
    return 0;
  }
  (void)pthread_detach(t);
  return 1;
}

static void krt2i_resume_blocking_lane(Rt *rt, Fiber *f) {
  BlockingReq *req = blocking_req_alloc();
  req->rt = rt;
  req->fiber = f;
  req->action = NULL;
  req->resume_existing = 1;
  pthread_t t;
  if (krt2i_spawn_thread(&t, blocking_worker_main, req) != 0) {
    blocking_req_free(req);
    krt_fail("rt.blocking: failed to resume blocking worker");
  }
  (void)pthread_detach(t);
}

static void enter_blocking_region(Fiber *f) {
  atomic_fetch_add_explicit(&f->blocking_depth, 1, memory_order_acq_rel);
}

static void leave_blocking_region(Fiber *f) {
  int old = atomic_fetch_sub_explicit(&f->blocking_depth, 1, memory_order_acq_rel);
  if (old <= 0) krt_fail("internal: source blocking delimiter underflow");
}

KValue *krt2_run_legacy_finalizers(KValue *primary, KValue **defers, int *count) {
  int rkind = RK_NORMAL;
  KValue *rval = NULL;
  krt2_sync_reason(primary, RK_NORMAL, &rkind, &rval);
  int origin_kind = rkind;
  KValue *origin_val = rval;

  Fiber *masked_fiber = g_cur_fiber;
  if (masked_fiber) masked_fiber->mask_depth++;
  while (*count > 0) {
    KValue *fin = defers[--(*count)];
    fin = finalizer_action_for_reason(fin, origin_kind, origin_val);
    int fin_control = RK_NORMAL;
    KValue *fr = krt2_run_sync_operand(fin, NULL, &fin_control);
    int ckind = RK_NORMAL;
    KValue *cval = NULL;
    krt2_sync_reason(fr, fin_control, &ckind, &cval);
    compose_reason_into(&rkind, &rval, ckind, cval);
  }
  if (masked_fiber && masked_fiber->mask_depth > 0) masked_fiber->mask_depth--;

  return krt2_sync_reify_reason(rkind, rval);
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

/* §18.7/§19.5/§32.2.6 abort-exit tokens for legacy native do-scopes.
 *
 * Generated synchronous C can be interrupted at a scalar/boxed-loop safe point
 * while pure helper frames are still on the C stack. A lexical cleanup at the
 * scalar call site is insufficient because the scalar worker may be inside a
 * helper called from a scope with active defers/releases. The active exit
 * actions therefore live on the Fiber. Normal finalization and safe-point abort
 * both mark the same token inactive, so each action runs at most once. */
#define KRT2_KIND_ABORT_EXIT "krt2.abortExit"

static AbortExit *abort_exit_from_token(KValue *token) {
  if (!token || kis_imm(token) || token->tag != K_FGN) {
    krt_fail("internal: invalid abort-exit token");
    return NULL;
  }
  if (strcmp(token->as.fgn.kind, KRT2_KIND_ABORT_EXIT) != 0) {
    krt_fail("internal: wrong foreign token kind for abort-exit finalizer");
    return NULL;
  }
  return (AbortExit *)token->as.fgn.p;
}

static void abort_exit_remove(Fiber *f, AbortExit *target) {
  if (!f || !target) return;
  AbortExit **p = &f->abort_exits;
  while (*p) {
    if (*p == target) {
      *p = target->next;
      target->next = NULL;
      return;
    }
    p = &(*p)->next;
  }
}

KValue *krt2_abort_exit_push(KValue *exit_action) {
  AbortExit *ae = (AbortExit *)GC_MALLOC(sizeof(AbortExit));
  ae->action = exit_action;
  ae->active = 1;
  Fiber *f = g_cur_fiber;
  if (f) {
    ae->next = f->abort_exits;
    f->abort_exits = ae;
  } else {
    ae->next = NULL;
  }
  return kfgn(ae, KRT2_KIND_ABORT_EXIT);
}

static KValue *abort_exit_take(KValue *token) {
  AbortExit *ae = abort_exit_from_token(token);
  if (!ae || !ae->active) return NULL;
  ae->active = 0;
  abort_exit_remove(g_cur_fiber, ae);
  return ae->action;
}

KValue *krt2_abort_exit_finalizer(KValue *token) {
  return op1(OP_ABORT_EXIT_FIN, "rt.abortExitFin", token);
}

static KValue *abort_exit_scope_finalizer(KValue *exit_action) {
  if (kctor_tagid(exit_action) == OP_ABORT_EXIT_FIN) {
    return exit_action;
  }
  KValue *exit_token = krt2_abort_exit_push(exit_action);
  return krt2_abort_exit_finalizer(exit_token);
}

static KValue *finalizer_action_for_reason(KValue *fin, int erkind, KValue *rval) {
  int tag = kctor_tagid(fin);
  if (tag == OP_ABORT_EXIT_FIN) {
    fin = abort_exit_take(kctor_arg(fin, 0));
    if (!fin) return krt2_pure(kunit());
    tag = kctor_tagid(fin);
  }
  if (tag == OP_ONEXIT_FIN) {
    return kapp(kctor_arg(fin, 0), exit_of_reason(erkind, rval));
  }
  if (tag == OP_ONINT_FIN) {
    KValue *cause = interrupt_cause_of_reason(erkind, rval);
    if (cause) return kapp(kctor_arg(fin, 0), cause);
    return krt2_pure(kunit());
  }
  return fin;
}

static ExitStack *abort_exit_drain_stack(Fiber *f) {
  if (!f || !f->abort_exits) return NULL;
  ExitStack *xs = exitstack_new();
  for (;;) {
    AbortExit *ae = f->abort_exits;
    if (!ae) break;
    f->abort_exits = ae->next;
    ae->next = NULL;
    if (!ae->active) continue;
    ae->active = 0;
    exitstack_push(xs, ae->action);
  }
  /* abort_exits is newest-first; begin_finseq runs from the end. */
  for (int i = 0, j = xs->n - 1; i < j; i++, j--) {
    KValue *tmp = xs->items[i];
    xs->items[i] = xs->items[j];
    xs->items[j] = tmp;
  }
  return xs;
}

/* acquireRelease (§18.1.12 / §19.5) as a composition over mask+finally+bind:
 *   mask (\restore -> acquire >>= \r -> finally (restore (pure r >>= use)) (release r))
 * acquire runs uninterruptibly (under the mask), `use r` is restored
 * (interruptible), and `release r` is a finalizer (runs masked, on every exit).
 * The `pure r >>= use` shape is load-bearing: calling `use r` here would build
 * the use action while still masked, which can evaluate pure lets in the
 * generated continuation (including scalar workers) before `restore` takes
 * effect. */
static KValue *ar_with_r(KEnv *env, KValue *r) {     /* env = [release, use, restore] */
  KValue *release = kvar(env, 0), *use = kvar(env, 1), *restore = kvar(env, 2);
  KValue *release_action = kapp(release, r);
  KValue *release_token = krt2_abort_exit_push(release_action);
  KValue *use_action = krt2_bind(krt2_pure(r), use);
  return krt2_finally(kapp(restore, use_action), krt2_abort_exit_finalizer(release_token));
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
  /* fix 2: this enqueue precedes a fiber_step (initial spawn / cede / re-enqueue),
   * which is an interruption point — mark it so a pending interrupt is observable
   * on the first turn.  The whole fiber-owned value graph is also published
   * across the run queue, so mark it shared before the rq_lock makes the fiber
   * visible to another worker. */
  krt2i_mark_fiber_shared(f);
  f->resumed = 1;
  atomic_store_explicit(&f->status, F_RUNNABLE, memory_order_release);
  krt2i_rq_push(rt, f);
}

void krt2i_register_park_waiter(Fiber *f, KParkKind kind, void *owner, Waiter *w) {
  f->park_kind = kind;
  f->park_owner = owner;
  f->park_waiter = w;
}

void krt2i_clear_park_waiter(Fiber *f) {
  f->park_kind = KPARK_NONE;
  f->park_owner = NULL;
  f->park_waiter = NULL;
}

void krt2i_cleanup_parked_wait(Fiber *f) {
  KParkKind kind = f->park_kind;
  void *owner = f->park_owner;
  Waiter *w = f->park_waiter;
  if (kind != KPARK_NONE && owner && w) {
    switch (kind) {
      case KPARK_FIBER_WAITERS: {
        Fiber *target = (Fiber *)owner;
        pthread_mutex_lock(&target->lock);
        krt2i_unlink_waiter(&target->waiters, w);
        pthread_mutex_unlock(&target->lock);
        break;
      }
      case KPARK_PROMISE_WAITERS: {
        Promise *p = (Promise *)owner;
        pthread_mutex_lock(&p->lock);
        krt2i_unlink_waiter(&p->waiters, w);
        pthread_mutex_unlock(&p->lock);
        break;
      }
      case KPARK_SCOPE_DRAIN: {
        Scope *sc = (Scope *)owner;
        pthread_mutex_lock(&sc->lock);
        krt2i_unlink_waiter(&sc->drain_waiters, w);
        pthread_mutex_unlock(&sc->lock);
        break;
      }
      case KPARK_NONE:
        break;
    }
  }
  if (kind != KPARK_NONE) {
    krt2i_clear_park_waiter(f);
  }
  krt2i_stm_unpark(f);
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
    if (resume_val) {
      f->cur = resume_val;
      krt2i_clear_park_waiter(f);
    }
    krt2i_mark_fiber_shared(f);
    /* fix 2: a wake re-enters fiber_step at a genuine resume point (the park this
     * wakes was a suspension: sleep/await/STM-retry/scope-drain).  Mark it so a
     * pending interrupt is delivered on the first turn (only the CAS winner runs
     * this, so there is no torn write; rq_push's rq_lock publishes it). */
    f->resumed = 1;
    if (atomic_load_explicit(&f->blocking_depth, memory_order_acquire) > 0)
      krt2i_resume_blocking_lane(rt, f);
    else
      krt2i_rq_push(rt, f);
  } else if (resume_val) {
    kdrop(resume_val);
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

/* Non-blocking run-queue poll used by native-loop safe points.  A scalar worker
 * cannot park and later resume from a saved continuation because its live state is
 * in C locals, not in f->k/KEnv.  Instead, the safe point briefly lends this OS
 * worker to one already-runnable sibling fiber, then returns to the scalar loop
 * with those locals intact. */
static Fiber *rq_try_pop(Rt *rt) {
  pthread_mutex_lock(&rt->rq_lock);
  if (atomic_load_explicit(&rt->shutting_down, memory_order_acquire)) {
    pthread_mutex_unlock(&rt->rq_lock);
    return NULL;
  }
  RQNode *n = rt->rq_head;
  if (!n) {
    pthread_mutex_unlock(&rt->rq_lock);
    return NULL;
  }
  rt->rq_head = n->next;
  if (!rt->rq_head) rt->rq_tail = NULL;
  pthread_mutex_unlock(&rt->rq_lock);
  return n->f;
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
  f->locals = NULL;               /* §18.1.7 FiberRef overrides (lazily allocated) */
  f->all_prev = f->all_next = NULL;
  f->mask_depth = 0;
  f->resumed = 0;                 /* fix 2: set on each (re)entry to fiber_step    */
  /* §32.2.20 abandonment drain: no drain is in progress on a fresh fiber.  This
   * is the empty drain_ae stack.  GC_MALLOC already zeroes, but making it
   * explicit keeps the fresh-fiber invariant non-fragile — a drain_ae left
   * dangling from a previous run/fiber would otherwise be read by the first
   * begin_abandon_drain as a bogus prev_drain (cf. the foreign-terminal hang). */
  f->drain_ae = NULL;
  f->stm_reads = NULL;
  f->stm_nreads = 0;
  krt2i_clear_park_waiter(f);
  f->sleep_timer = NULL;          /* fix S2: no sleep timer armed yet              */
  atomic_store(&f->sleep_armed, 0);
  atomic_store(&f->sleep_seq, 0);
  f->blocking_armed = 0;
  atomic_store(&f->blocking_depth, 0);
  f->safepoint_hit = 0;           /* fix SP: §32.2.6 loop-backedge safe point      */
  f->backedge_budget = 0;
  f->abort_exits = NULL;
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

static void mark_exit_stack_shared(ExitStack *xs);
static void mark_cont_stack_shared(Cont *c);
static void mark_abandon_end_shared(AbandonEnd *ae);
static void mark_finseq_shared(FinSeq *fs);
static void mark_resumption_shared(Resumption *r);

static void mark_exit_stack_shared(ExitStack *xs) {
  if (!xs || !xs->items) return;
  for (int i = 0; i < xs->n; i++) krc_mark_shared_recursive(xs->items[i]);
}

static void mark_handler_shared(Handler *h) {
  if (!h) return;
  krc_mark_shared_recursive(h->ret);
  krc_mark_shared_recursive(h->ops);
}

static void mark_fiber_locals_shared(FiberLocals *locals) {
  if (!locals || !locals->vals) return;
  for (int i = 0; i < locals->n; i++) krc_mark_shared_recursive(locals->vals[i]);
}

static void mark_abort_exits_shared(AbortExit *ae) {
  for (; ae; ae = ae->next)
    if (ae->active) krc_mark_shared_recursive(ae->action);
}

static void mark_abandon_end_shared(AbandonEnd *ae) {
  for (; ae; ae = ae->prev_drain) {
    mark_cont_stack_shared(ae->kont);
    mark_exit_stack_shared(ae->saved_exits);
    krc_mark_shared_recursive(ae->rval);
    krc_mark_shared_recursive(ae->rlabel);
  }
}

static void mark_finseq_shared(FinSeq *fs) {
  if (!fs) return;
  mark_exit_stack_shared(fs->xs);
  krc_mark_shared_recursive(fs->rval);
  krc_mark_shared_recursive(fs->rlabel);
  krc_mark_shared_recursive(fs->origin_val);
  mark_abandon_end_shared(fs->drain_ae);
}

static void mark_resumption_shared(Resumption *r) {
  if (!r) return;
  mark_cont_stack_shared(r->head);
  if (!r->head) mark_cont_stack_shared(r->tail);
  mark_exit_stack_shared(r->cur_exits);
  krc_mark_shared_recursive(r->label);
  mark_handler_shared((Handler *)r->handler);
  mark_exit_stack_shared((ExitStack *)r->handler_exits);
}

static void mark_cont_aux_shared(Cont *c) {
  switch (c->kind) {
    case KK_DOSCOPE:
      mark_exit_stack_shared((ExitStack *)c->aux);
      mark_exit_stack_shared((ExitStack *)c->aux2);
      break;
    case KK_FINSEQ:
      mark_finseq_shared((FinSeq *)c->aux);
      break;
    case KK_HANDLER:
      mark_handler_shared((Handler *)c->aux);
      mark_exit_stack_shared((ExitStack *)c->aux2);
      break;
    case KK_ABANDON:
      mark_resumption_shared((Resumption *)c->aux);
      break;
    case KK_ABANDEND:
      mark_abandon_end_shared((AbandonEnd *)c->aux);
      break;
    default:
      break;
  }
}

static void mark_cont_stack_shared(Cont *c) {
  for (; c; c = c->next) {
    krc_mark_shared_recursive(c->a);
    mark_cont_aux_shared(c);
    if (c == &g_done) break;
  }
}

void krt2i_mark_fiber_shared(Fiber *f) {
  if (!f) return;
  pthread_mutex_lock(&f->lock);
  KValue *cur = f->cur;
  KValue *exit = f->exit;
  KValue *interrupt_cause = f->interrupt_cause;
  Cont *k = f->k;
  ExitStack *cur_exits = f->cur_exits;
  FiberLocals *locals = f->locals;
  AbortExit *abort_exits = f->abort_exits;
  AbandonEnd *drain_ae = (AbandonEnd *)f->drain_ae;
  pthread_mutex_unlock(&f->lock);
  krc_mark_shared_recursive(cur);
  krc_mark_shared_recursive(exit);
  krc_mark_shared_recursive(interrupt_cause);
  mark_cont_stack_shared(k);
  mark_exit_stack_shared(cur_exits);
  mark_fiber_locals_shared(locals);
  mark_abort_exits_shared(abort_exits);
  mark_abandon_end_shared(drain_ae);
}

void krt2i_mark_fgn_payload_shared(const char *kind, void *payload) {
  if (!kind || !payload) return;
  if (strcmp(kind, KRT2_KIND_RESUMPTION) == 0) {
    mark_resumption_shared((Resumption *)payload);
  } else if (strcmp(kind, KRT2_KIND_ABORT_EXIT) == 0) {
    mark_abort_exits_shared((AbortExit *)payload);
  } else if (strcmp(kind, KRT2_KIND_FIBER) == 0) {
    /* Fiber payloads are marked at spawn/resume/park publication sites. Do not
     * recursively walk from the handle: this function can run while a waiter is
     * being enqueued under another object's mutex and the fiber's current action
     * may contain that same handle. */
  } else if (strcmp(kind, KRT2_KIND_SCOPE) == 0) {
    /* Scope child/waiter fibers are marked at attach/shutdown park sites under
     * the scope lock; recursive handle walking here would self-deadlock there. */
  } else if (strcmp(kind, KRT2_KIND_PROMISE) == 0) {
    /* Promise exits are marked at completePromise and waiters before enqueue. */
  } else if (strcmp(kind, KRT2_KIND_MONITOR) == 0) {
    /* Monitor targets are ordinary Fiber handles; the target fiber is rooted in
     * rt->all and publication marks happen at the fiber boundary. */
  } else if (strcmp(kind, KRT2_KIND_TVAR) == 0) {
    /* TVar values are marked on newTVar/commit before the versioned box publish. */
  } else if (strcmp(kind, KRT2_KIND_ATOMIC) == 0) {
    /* AtomicRef cells mark incoming values while holding the cell mutex before
     * store/exchange/CAS/fetch-* publication. */
  } else if (strcmp(kind, KRT2_KIND_FIBERREF) == 0) {
    /* FiberRef handles are immediate ids today; this branch pins the exported
     * kind as carrying no hidden KValue payload if a host wraps one as K_FGN. */
#ifndef NDEBUG
  } else if (strncmp(kind, "rt.", 3) == 0 || strncmp(kind, "krt2.", 5) == 0) {
    assert(!"unhandled runtime K_FGN kind in krt2i_mark_fgn_payload_shared");
#endif
  }
}

#ifndef NDEBUG
static void assert_exit_stack_shared(ExitStack *xs, Krt2AssertSharedChild assert_child, void *ctx);
static void assert_cont_stack_shared(Cont *c, Krt2AssertSharedChild assert_child, void *ctx);
static void assert_abandon_end_shared(AbandonEnd *ae, Krt2AssertSharedChild assert_child, void *ctx);
static void assert_finseq_shared(FinSeq *fs, Krt2AssertSharedChild assert_child, void *ctx);
static void assert_resumption_shared(Resumption *r, Krt2AssertSharedChild assert_child, void *ctx);

static void assert_exit_stack_shared(ExitStack *xs, Krt2AssertSharedChild assert_child, void *ctx) {
  if (!xs || !xs->items) return;
  for (int i = 0; i < xs->n; i++) assert_child(ctx, xs->items[i]);
}

static void assert_handler_shared(Handler *h, Krt2AssertSharedChild assert_child, void *ctx) {
  if (!h) return;
  assert_child(ctx, h->ret);
  assert_child(ctx, h->ops);
}

static void assert_abort_exits_shared(AbortExit *ae, Krt2AssertSharedChild assert_child, void *ctx) {
  for (; ae; ae = ae->next) {
    if (ae->active) assert_child(ctx, ae->action);
  }
}

static void assert_abandon_end_shared(AbandonEnd *ae, Krt2AssertSharedChild assert_child, void *ctx) {
  for (; ae; ae = ae->prev_drain) {
    assert_cont_stack_shared(ae->kont, assert_child, ctx);
    assert_exit_stack_shared(ae->saved_exits, assert_child, ctx);
    assert_child(ctx, ae->rval);
    assert_child(ctx, ae->rlabel);
  }
}

static void assert_finseq_shared(FinSeq *fs, Krt2AssertSharedChild assert_child, void *ctx) {
  if (!fs) return;
  assert_exit_stack_shared(fs->xs, assert_child, ctx);
  assert_child(ctx, fs->rval);
  assert_child(ctx, fs->rlabel);
  assert_child(ctx, fs->origin_val);
  assert_abandon_end_shared(fs->drain_ae, assert_child, ctx);
}

static void assert_resumption_shared(Resumption *r, Krt2AssertSharedChild assert_child, void *ctx) {
  if (!r) return;
  assert_cont_stack_shared(r->head, assert_child, ctx);
  if (!r->head) assert_cont_stack_shared(r->tail, assert_child, ctx);
  assert_exit_stack_shared(r->cur_exits, assert_child, ctx);
  assert_child(ctx, r->label);
  assert_handler_shared((Handler *)r->handler, assert_child, ctx);
  assert_exit_stack_shared((ExitStack *)r->handler_exits, assert_child, ctx);
}

static void assert_cont_aux_shared(Cont *c, Krt2AssertSharedChild assert_child, void *ctx) {
  switch (c->kind) {
    case KK_DOSCOPE:
      assert_exit_stack_shared((ExitStack *)c->aux, assert_child, ctx);
      assert_exit_stack_shared((ExitStack *)c->aux2, assert_child, ctx);
      break;
    case KK_FINSEQ:
      assert_finseq_shared((FinSeq *)c->aux, assert_child, ctx);
      break;
    case KK_HANDLER:
      assert_handler_shared((Handler *)c->aux, assert_child, ctx);
      assert_exit_stack_shared((ExitStack *)c->aux2, assert_child, ctx);
      break;
    case KK_ABANDON:
      assert_resumption_shared((Resumption *)c->aux, assert_child, ctx);
      break;
    case KK_ABANDEND:
      assert_abandon_end_shared((AbandonEnd *)c->aux, assert_child, ctx);
      break;
    default:
      break;
  }
}

static void assert_cont_stack_shared(Cont *c, Krt2AssertSharedChild assert_child, void *ctx) {
  for (; c; c = c->next) {
    assert_child(ctx, c->a);
    assert_cont_aux_shared(c, assert_child, ctx);
    if (c == &g_done) break;
  }
}

void krt2i_assert_fgn_payload_shared(const char *kind, void *payload,
                                     Krt2AssertSharedChild assert_child,
                                     void *ctx) {
  if (!kind || !payload) return;
  if (strcmp(kind, KRT2_KIND_RESUMPTION) == 0) {
    assert_resumption_shared((Resumption *)payload, assert_child, ctx);
  } else if (strcmp(kind, KRT2_KIND_ABORT_EXIT) == 0) {
    assert_abort_exits_shared((AbortExit *)payload, assert_child, ctx);
  } else if (strcmp(kind, KRT2_KIND_FIBER) == 0 ||
             strcmp(kind, KRT2_KIND_SCOPE) == 0 ||
             strcmp(kind, KRT2_KIND_PROMISE) == 0 ||
             strcmp(kind, KRT2_KIND_MONITOR) == 0 ||
             strcmp(kind, KRT2_KIND_TVAR) == 0 ||
             strcmp(kind, KRT2_KIND_ATOMIC) == 0 ||
             strcmp(kind, KRT2_KIND_FIBERREF) == 0) {
    return;
  } else if (strncmp(kind, "rt.", 3) == 0 || strncmp(kind, "krt2.", 5) == 0) {
    assert(!"unhandled runtime K_FGN kind in krt2i_assert_fgn_payload_shared");
  }
}
#endif

/* A non-failing record projection (kproj krt_fails on a missing field).  Used to
 * read the §4b reserved "__tailResumptive" marker off a handler's ops record:
 * absent ⇒ the op takes the general 4a path. */
static KValue *kproj_opt(KValue *rec, const char *name) {
  if (!rec || kis_imm(rec) || rec->tag != K_REC) return NULL;
  for (int i = 0; i < rec->as.rec.n; i++)
    if (strcmp(rec->as.rec.names[i], name) == 0) return rec->as.rec.vals[i];
  return NULL;
}

/* §4b: is operation `opn` (a NUL-terminated op token) tail-resumptive under the
 * handler `h`?  True iff h->ops carries the reserved "__tailResumptive" record
 * AND that record names `opn`.  The elaborator (Check.elabHandle) only marks a
 * clause whose sole `resume` is `k v` in tail position, on a DEEP handler — the
 * exact shape the fast path preserves observably (Usage.tailResumptiveClause). */
static int op_is_tail_resumptive(Handler *h, const char *opn) {
  if (!h || !h->ops) return 0;
  KValue *tailRec = kproj_opt(h->ops, "__tailResumptive");
  return tailRec && kproj_opt(tailRec, opn) != NULL;
}

static int deliver(Rt *rt, Fiber *f, KValue *v);  /* normal value path  */
static int unwind(Rt *rt, Fiber *f, int rkind, KValue *rval, KValue *rlabel); /* abnormal */

/* Terminate `f` with `exitv`, wake its awaiters, drop it from the root set. */
static void fiber_finish(Rt *rt, Fiber *f, KValue *exitv) {
  krc_mark_shared_recursive(exitv);
  pthread_mutex_lock(&f->lock);
  f->exit = exitv;
  atomic_store_explicit(&f->status, F_DONE, memory_order_release);
  Waiter *w = f->waiters;
  f->waiters = NULL;
  pthread_mutex_unlock(&f->lock);

  for (; w; w = w->next)              /* wake EVERY awaiter (idempotent CAS)  */
    krt2i_wake(rt, w->f, krt2_pure(w->want_exit ? kdup(exitv) : kunit()));
  krt2i_scope_detach(rt, f);          /* leave att_scope; may drain a shutdownScope */
  krt2i_all_remove(rt, f);            /* DONE: kept now only by a user handle */

  /* fix 5: acquire-load the run's main fiber (written release in krt2_run_main).
   * A worker reaching here on the persistent pool may race the next run's store;
   * the atomic makes the comparison well-defined and never torn. */
  if (f == atomic_load_explicit(&rt->main_fiber, memory_order_acquire)) {
    pthread_mutex_lock(&rt->done_lock);
    rt->main_done = 1;
    pthread_cond_signal(&rt->done_cv);
    pthread_mutex_unlock(&rt->done_lock);
  }
}

/* ── §18.1.7 FiberRef cells (fiber-local state with copy-on-fork) ──────────── */
/* A FiberRef is identified by a dense integer id; the cell's INIT value (the
 * fallback for fibers that never set it) lives in a single shared, append-only
 * registry, mirroring the reference interpreter's `fiberRefInit` global.  A
 * fiber's per-cell OVERRIDES live in its own `f->locals` (FiberLocals), which is
 * deep-copied into a child at fork so post-fork updates are independent. */
static pthread_mutex_t g_fref_lock = PTHREAD_MUTEX_INITIALIZER;
static KValue **g_fref_init = NULL;   /* init value per cell id (scanned: GC root) */
static int      g_fref_n = 0;         /* number of allocated cells                 */
static int      g_fref_cap = 0;

/* Allocate a fresh FiberRef id recording `init`; returns the FiberRef handle. */
static KValue *fiber_ref_new(KValue *init) {
  krc_mark_shared_recursive(init);
  pthread_mutex_lock(&g_fref_lock);
  if (g_fref_n == g_fref_cap) {
    int nc = g_fref_cap ? g_fref_cap * 2 : 8;
    KValue **ni = (KValue **)GC_MALLOC(sizeof(KValue *) * nc); /* scanned */
    for (int i = 0; i < g_fref_n; i++) ni[i] = g_fref_init[i];
    g_fref_init = ni; g_fref_cap = nc;
  }
  int id = g_fref_n++;
  g_fref_init[id] = init;
  pthread_mutex_unlock(&g_fref_lock);
  /* the handle is just the cell id boxed (an immediate int); the id indexes both
   * the shared init registry and each fiber's override array. */
  return kint((int64_t)id);
}
static KValue *fiber_ref_init_of(int id) {
  pthread_mutex_lock(&g_fref_lock);
  KValue *v = (id >= 0 && id < g_fref_n) ? g_fref_init[id] : kunit();
  pthread_mutex_unlock(&g_fref_lock);
  return v ? v : kunit();
}
/* The current fiber's value for cell `id`: its override if set, else the init. */
static KValue *fiber_local_get(Fiber *f, int id) {
  if (f->locals && id >= 0 && id < f->locals->n && f->locals->vals[id])
    return f->locals->vals[id];
  return fiber_ref_init_of(id);
}
/* Set the current fiber's override for cell `id` (growing its array as needed). */
static void fiber_local_set(Fiber *f, int id, KValue *v) {
  if (id < 0) return;
  if (!f->locals) {
    f->locals = (FiberLocals *)GC_MALLOC(sizeof(FiberLocals));
    f->locals->vals = NULL; f->locals->n = 0;
  }
  if (id >= f->locals->n) {
    int nc = f->locals->n ? f->locals->n : 8;
    while (nc <= id) nc *= 2;
    KValue **nv = (KValue **)GC_MALLOC(sizeof(KValue *) * nc); /* scanned, zeroed */
    for (int i = 0; i < f->locals->n; i++) nv[i] = f->locals->vals[i];
    f->locals->vals = nv; f->locals->n = nc;
  }
  KValue *old = f->locals->vals[id];
  f->locals->vals[id] = v;
  if (old) kdrop(old);
}
/* §18.1.7 copy-on-fork: deep-copy the parent's override array into the child so
 * the two diverge independently after fork. */
static FiberLocals *fiber_locals_snapshot(FiberLocals *src) {
  if (!src || src->n == 0) return NULL;
  FiberLocals *dst = (FiberLocals *)GC_MALLOC(sizeof(FiberLocals));
  dst->n = src->n;
  dst->vals = (KValue **)GC_MALLOC(sizeof(KValue *) * src->n); /* scanned */
  for (int i = 0; i < src->n; i++) {
    if (src->vals[i]) krc_mark_shared_recursive(src->vals[i]);
    dst->vals[i] = src->vals[i] ? kdup(src->vals[i]) : NULL;
  }
  return dst;
}

/* Create, attach, root, and enqueue a child fiber.  `attach` is the supervision
 * scope the child is attached to (NULL or daemon => unattached).  The child's
 * own forks attach to `attach` too (flat nesting in v1; per-do-block nested
 * scopes arrive with the do-kernel completion increment).  The child inherits a
 * SNAPSHOT of `parent`'s FiberRef overrides (§18.1.7); pass NULL for a root. */
Fiber *krt2i_spawn_from(Rt *rt, Fiber *parent, KValue *action, Scope *attach, int daemon) {
  krc_mark_shared_recursive(action);
  Fiber *child = fiber_new(rt, action);
  child->daemon = daemon;
  child->cur_scope = attach;
  if (parent) child->locals = fiber_locals_snapshot(parent->locals); /* copy-on-fork */
  Scope *dscope = atomic_load_explicit(&rt->daemon_scope, memory_order_acquire);
  if (!daemon && attach) {
    krt2i_scope_attach(rt, attach, child); /* att_scope+link+live++ */
  } else if (daemon && dscope) {
    /* fix 6 (R2): a daemon is unattached to ordinary structured scopes (its parent
     * never awaits it), but the persistent runtime must still reap it at the run
     * boundary.  Attach it to the run's daemon scope so main's wrapper can interrupt
     * + await it; without this a parked daemon stays in rt->all (a static-g_rt Boehm
     * root) forever, growing the live set by one fiber + Cont chain per run.  Its
     * own forks still use cur_scope (set above), so daemon child semantics are
     * unchanged — only the daemon itself becomes drainable. */
    krt2i_scope_attach(rt, dscope, child);
  }
  krt2i_all_add(rt, child);
  krt2i_resume(rt, child);
  return child;
}
Fiber *krt2i_spawn(Rt *rt, KValue *action, Scope *attach, int daemon) {
  return krt2i_spawn_from(rt, NULL, action, attach, daemon);
}

/* Companion to krt2i_deliver_pending_before_park (§18.1.12): called by a
 * park-op AFTER it has committed f->status = F_PARKED and registered its waiter.
 * `park_unmasked` must be captured BEFORE publishing F_PARKED; after publication
 * another worker may win a wake and own the fiber, so this function only reads
 * atomics.  The seq_cst fence pairs with krt2i_interrupt_request so
 * {store F_PARKED; fence; load pending} and {store pending; fence; CAS status}
 * cannot both miss (Dekker). */
int krt2i_claim_pending_after_park(Fiber *f, int park_unmasked) {
  atomic_thread_fence(memory_order_seq_cst);
  if (!park_unmasked || !atomic_load_explicit(&f->interrupt_pending, memory_order_acquire))
    return 0;
  int expected = F_PARKED;
  return atomic_compare_exchange_strong_explicit(&f->status, &expected, F_RUNNING,
                                                 memory_order_acq_rel, memory_order_relaxed);
}

int krt2i_deliver_claimed_interrupt(Rt *rt, Fiber *f) {
  return deliver_interrupt(rt, f) ? 1 : 0;
}

/* await: returns 1 if the child is already done (continue stepping with its
 * Exit), 0 if `f` parked onto the child's waiter list (suspended). */
static int do_await(Rt *rt, Fiber *f, KValue *handle) {
  Fiber *child = (Fiber *)kas_fgn_kind(handle, KRT2_KIND_FIBER);
  krt2i_mark_fiber_shared(f);
  pthread_mutex_lock(&child->lock);
  if (atomic_load_explicit(&child->status, memory_order_acquire) == F_DONE) {
    KValue *ex = child->exit;
    pthread_mutex_unlock(&child->lock);
    f->cur = krt2_pure(kdup(ex));
    return 1;
  }
  Waiter *w = (Waiter *)GC_MALLOC(sizeof(Waiter));
  w->f = f; w->want_exit = 1; w->next = child->waiters; child->waiters = w;
  krt2i_register_park_waiter(f, KPARK_FIBER_WAITERS, child, w);
  int park_unmasked = (f->mask_depth == 0);
  atomic_store(&f->status, F_PARKED);
  pthread_mutex_unlock(&child->lock);
  if (krt2i_claim_pending_after_park(f, park_unmasked)) {
    pthread_mutex_lock(&child->lock);
    krt2i_unlink_waiter(&child->waiters, w);
    pthread_mutex_unlock(&child->lock);
    krt2i_clear_park_waiter(f);
    return krt2i_deliver_claimed_interrupt(rt, f) ? 1 : 0;
  }
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
  Promise *p = (Promise *)kas_fgn_kind(ph, KRT2_KIND_PROMISE);
  pthread_mutex_lock(&p->lock);
  int first = !atomic_load(&p->completed);
  Waiter *w = NULL;
  if (first) {
    krc_mark_shared_recursive(exitv);
    p->exit = exitv;
    atomic_store_explicit(&p->completed, 1, memory_order_release);
    w = p->waiters; p->waiters = NULL;
  }
  pthread_mutex_unlock(&p->lock);
  if (!first) kdrop(exitv);
  for (; w; w = w->next) krt2i_wake(rt, w->f, krt2_pure(kdup(exitv)));
  return kbool(first);
}
static int do_await_promise(Rt *rt, Fiber *f, KValue *ph) {
  Promise *p = (Promise *)kas_fgn_kind(ph, KRT2_KIND_PROMISE);
  krt2i_mark_fiber_shared(f);
  pthread_mutex_lock(&p->lock);
  if (atomic_load_explicit(&p->completed, memory_order_acquire)) {
    KValue *ex = p->exit;
    pthread_mutex_unlock(&p->lock);
    f->cur = krt2_pure(kdup(ex));
    return 1;
  }
  Waiter *w = (Waiter *)GC_MALLOC(sizeof(Waiter));
  w->f = f; w->want_exit = 1; w->next = p->waiters; p->waiters = w;
  krt2i_register_park_waiter(f, KPARK_PROMISE_WAITERS, p, w);
  int park_unmasked = (f->mask_depth == 0);
  atomic_store(&f->status, F_PARKED);
  pthread_mutex_unlock(&p->lock);
  if (krt2i_claim_pending_after_park(f, park_unmasked)) {
    pthread_mutex_lock(&p->lock);
    krt2i_unlink_waiter(&p->waiters, w);
    pthread_mutex_unlock(&p->lock);
    krt2i_clear_park_waiter(f);
    return krt2i_deliver_claimed_interrupt(rt, f) ? 1 : 0;
  }
  return 0;
}
/* §18.11 non-blocking peek: NEVER parks.  poll -> Some Exit iff completed, else
 * None; isDone -> Bool.  A single acquire-load of the cell's state suffices (the
 * exit is single-assignment under p->lock, so reading it after observing
 * completed==1 is a consistent snapshot — REVIEW.md happens-before §35.041). */
static KValue *promise_poll(KValue *ph) {
  Promise *p = (Promise *)kas_fgn_kind(ph, KRT2_KIND_PROMISE);
  pthread_mutex_lock(&p->lock);
  KValue *r = atomic_load_explicit(&p->completed, memory_order_acquire)
                  ? krt2i_some(kdup(p->exit)) : krt2i_none();
  pthread_mutex_unlock(&p->lock);
  return r;
}
static KValue *promise_is_done(KValue *ph) {
  Promise *p = (Promise *)kas_fgn_kind(ph, KRT2_KIND_PROMISE);
  return kbool(atomic_load_explicit(&p->completed, memory_order_acquire) != 0);
}

/* ── the CK-machine ─────────────────────────────────────────────────────── */
static void emit_kstr(KValue *s, int newline) {
  /* kas_str returns NUL-terminated bytes of a K_STR. */
  fputs(kas_str(s), stdout);
  if (newline) fputc('\n', stdout);
}

/* §18.1.4 reconstruct the terminal `Exit e a` a scope is exiting with, from the
 * saved KK_FINSEQ Reason — the value an `onExit` finalizer receives.  Mirrors
 * unwind's KK_DONE classification:
 *   RK_NORMAL / RK_RETURN  -> Success rval
 *   RK_FAIL                -> Failure (Fail rval)
 *   RK_INTERRUPT           -> Failure (Interrupt rval)   (rval is the InterruptCause)
 *   RK_RERAISE             -> Failure rval               (rval IS the Cause)
 *   RK_BREAK/RK_CONTINUE   -> Success Unit               (loop control, not a real exit)
 */
static KValue *exit_of_reason(int rkind, KValue *rval) {
  switch (rkind) {
    case RK_NORMAL:    return krt2_success(rval);
    case RK_RETURN:    return krt2_success(rval ? rval : kunit());
    case RK_FAIL:      return krt2_failure(krt2_cause_fail(rval));
    case RK_INTERRUPT: return krt2_failure(krt2_cause_interrupt(rval));
    case RK_RERAISE:   return krt2_failure(rval);
    default:           return krt2_success(kunit());
  }
}

/* §32.2.12 the `Cause` a failing reason carries, or NULL for a NON-failing one
 * (RK_NORMAL/RK_RETURN/RK_BREAK/RK_CONTINUE/RK_DRAIN — none of which records a
 * Cause).  Used to compose a finalizer's own failure with the reason the scope
 * was already exiting with (the §18.7/§32.2.12 `Then` composition). */
static KValue *reason_to_cause(int rkind, KValue *rval) {
  switch (rkind) {
    case RK_FAIL:      return krt2_cause_fail(rval);
    case RK_INTERRUPT: return krt2_cause_interrupt(rval);
    case RK_RERAISE:   return rval;          /* rval IS already a Cause           */
    default:           return NULL;          /* normal/return/break/continue/drain */
  }
}

/* §32.2.12 sequential cause composition.  `*io_kind`/`*io_val` carry the PRIMARY
 * reason (the body/clause result the scope was exiting with); `(c_kind, c_val)`
 * is a CLEANUP reason that arose while running an exit action.  On return the
 * primary is updated in place to the composed reason:
 *   - primary non-failing, cleanup failing  -> the cleanup cause (RK_RERAISE)
 *   - primary failing,    cleanup failing    -> Then(primary, cleanup) (RK_RERAISE)
 *   - cleanup non-failing                     -> primary unchanged
 * The first failure stays leftmost in the `Then` spine (§18.8.3: the primary is
 * not replaced — later cleanup failures are appended), so an `Exit`/`sandbox`
 * observer sees `Then primary cleanup` while ordinary `catchError` keeps reading
 * the leftmost `Fail` branch (§32.2.12). */
static void compose_reason_into(int *io_kind, KValue **io_val, int c_kind, KValue *c_val) {
  KValue *cleanup = reason_to_cause(c_kind, c_val);
  if (!cleanup) return;                       /* cleanup was non-failing: no change */
  KValue *primary = reason_to_cause(*io_kind, *io_val);
  KValue *composed = primary ? krt2_cause_then(primary, cleanup) : cleanup;
  *io_kind = RK_RERAISE;                       /* a raw Cause re-raised as-is        */
  *io_val  = composed;
}

static KValue *interrupt_cause_of_cause(KValue *cause) {
  if (!cause || kis_imm(cause)) return NULL;
  switch (kctor_tagid(cause)) {
    case KCT_INTERRUPT:
      return kctor_arg(cause, 0);
    case KCT_THEN:
      /* Then(primary, cleanup): onInterrupt is keyed to the body's terminal
       * interruption, not to later cleanup failures appended to the cause. */
      return interrupt_cause_of_cause(kctor_arg(cause, 0));
    case KCT_BOTH: {
      KValue *left = interrupt_cause_of_cause(kctor_arg(cause, 0));
      return left ? left : interrupt_cause_of_cause(kctor_arg(cause, 1));
    }
    default:
      return NULL;
  }
}

static KValue *interrupt_cause_of_reason(int rkind, KValue *rval) {
  switch (rkind) {
    case RK_INTERRUPT:
      return rval;
    case RK_RERAISE:
      return interrupt_cause_of_cause(rval);
    default:
      return NULL;
  }
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
                        int rkind, KValue *rval, KValue *rlabel,
                        AbandonEnd *drain_ae) {
  f->cur_exits = restore;
  if (!xs || xs->n == 0) {
    /* No exit actions to run.  A drain do-scope with no defers leaves the running
     * composed reason (drain_ae->*) untouched and simply continues the walk. */
    if (drain_ae) return unwind(rt, f, RK_DRAIN, NULL, NULL);
    return apply_reason(rt, f, rkind, rval, rlabel);
  }
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
  fs->xs = xs; fs->i = xs->n - 1; fs->rlabel = rlabel; fs->drain_ae = drain_ae;
  fs->origin_kind = drain_ae ? RK_DRAIN : rkind;
  fs->origin_val = drain_ae ? NULL : rval;
  if (drain_ae) {
    /* fix 1: seed the finseq PRIMARY with the RUNNING composed drain reason (the
     * clause result, possibly already carrying earlier abandoned do-scopes'
     * cleanup failures) so a failing finalizer here folds in left-associatively
     * — exactly the spine ordinary scope exit builds. */
    fs->rkind = drain_ae->rkind; fs->rval = drain_ae->rval;
  } else {
    fs->rkind = rkind; fs->rval = rval;
  }
  f->k = cont_new2(KK_FINSEQ, NULL, fs, NULL, f->k);
  f->cur = krt2_pure(kunit());  /* kick: deliver() -> KK_FINSEQ runs xs[n-1] */
  return 1;
}

/* §32.2.20/.21 ABANDONMENT DRAIN.  A general-path (severed) handler clause
 * completed WITHOUT resuming its captured one-shot resumption, so the severed
 * op-site→handler slice [r->head .. r->tail] (tail->next == &g_done) — and every
 * `using` release / `defer` registered in its do-scopes — would otherwise be
 * dropped GC'd-unrun.  Instead we walk that slice once with RK_DRAIN, running its
 * KK_DOSCOPE exit actions masked-LIFO via the same begin_finseq machinery as a
 * normal unwind, then resume the clause's own result (`post_*`) at its saved
 * continuation `kont`.  We splice a KK_ABANDEND terminal onto the slice's tail so
 * the RK_DRAIN walk lands there (not on the fiber's &g_done) and hands control
 * back.  `kont` is the clause's post-handler continuation (already f->k here),
 * and `f->cur_exits` is the clause's exit-state, both restored after the drain.
 * This runs only on the GENERAL/abortive path; a tail-resumptive or resumed
 * clause never reaches here. */
#ifdef KRT2_ABANDON_INSTRUMENT
/* §32.2.20 test-only instrumentation: count how often the FOREIGN-terminal and
 * ACTIVE-terminal branches of finish_abandon_drain fire, and how many drains
 * begin.  Used by tests/abandon_foreign_chain.c to PROVE it exercises the
 * foreign path.  Compiled in only under -DKRT2_ABANDON_INSTRUMENT (the runtime
 * Makefile passes it); no effect on production builds. */
unsigned long g_rt_foreign_hits = 0;   /* finish_abandon_drain FOREIGN branch    */
unsigned long g_rt_active_hits  = 0;   /* finish_abandon_drain ACTIVE branch      */
unsigned long g_rt_begin_hits   = 0;   /* begin_abandon_drain entries             */
#endif

static int begin_abandon_drain(Rt *rt, Fiber *f, Resumption *r,
                               int post_kind, KValue *post_val, KValue *post_label) {
#ifdef KRT2_ABANDON_INSTRUMENT
  g_rt_begin_hits++;
#endif
  AbandonEnd *ae = (AbandonEnd *)GC_MALLOC(sizeof(AbandonEnd));
  ae->kont        = f->k;          /* the clause's continuation (after KK_ABANDON) */
  ae->saved_exits = f->cur_exits;  /* the clause's exit-state, resumed post-drain  */
  ae->rkind = post_kind; ae->rval = post_val; ae->rlabel = post_label;
  /* Land the RK_DRAIN walk on KK_ABANDEND rather than the fiber's &g_done.  The
   * slice was self-terminated at capture (r->tail->next == &g_done); re-point it
   * at the terminal (its `next` is kont so a stray fall-through is still safe). */
  /* fix 1: record the previous drain (for a NESTED H1 recursion) on the terminal
   * so KK_ABANDEND can restore it, and make THIS drain the active one.  The
   * abandoned do-scopes' finseqs read f->drain_ae to compose against the running
   * clause reason left-associatively. */
  ae->prev_drain = (AbandonEnd *)f->drain_ae;
  r->tail->next = cont_new2(KK_ABANDEND, NULL, ae, NULL, ae->kont);
  f->drain_ae = ae;
  f->k = r->head;                  /* re-root at the op-site frame to drain it     */
  f->cur_exits = r->cur_exits;     /* under the captured body's exit-action state  */
  return unwind(rt, f, RK_DRAIN, NULL, NULL);
}

/* §32.2.20/.21 the RK_DRAIN walk reached a slice's KK_ABANDEND terminal frame `c`
 * with the live reason (live_kind, live_val) — RK_DRAIN normally, or a finalizer
 * failure that escaped this slice's finseq (e.g. a restoring finalizer interrupted).
 * `ae->rkind/rval` is the running composed reason (clause result + this slice's
 * cleanup failures, folded left-associatively by the drained finseqs, fix 1).
 *
 * fix 2 (§32.2.20 PERFORM-DURING-DRAIN): the clause reason resumes at the
 * terminal frame's LIVE successor `c->next`, NOT at the captured-at-install
 * `ae->kont`.  KK_ABANDEND is a DELIMITED boundary (modelled on KK_RETSCOPE): a
 * `perform` by an abandoned `defer` searches OUTWARD past it and finds the
 * enclosing handler in ae->kont, and when that handler RESUMES the drain it
 * re-splices the captured slice — leaving the live continuation that the clause
 * result must flow into at `c->next`.  The pre-fix `f->k = ae->kont` hard-
 * overwrote that resume-spliced continuation, orphaning the performed effect and
 * delivering the clause's post-value to the intervening handler's return instead.
 *
 * The terminal reached can be EITHER the ACTIVE drain's own (the common case, plus
 * fix 2's resume case where it was re-spliced) OR — when an abandoned `defer`
 * PERFORMS OUTWARD into an ENCLOSING handler whose clause ITSELF abandons — a
 * DIFFERENT (outer) drain's terminal captured into the inner abandoned slice and
 * re-walked by the inner drain.  The two are told apart by whether c->aux is the
 * fiber's currently active drain (f->drain_ae).  For such a FOREIGN terminal the
 * clause reason cannot resume at the live successor c->next (it points INSIDE the
 * still-draining inner slice — an infinite re-walk); it escapes to the captured-
 * at-install ae->kont, OUTSIDE both abandoned slices.
 *
 * fix 3 (FOREIGN-terminal drain_ae pop): escaping to ae->kont terminates this
 * outer drain AND tears down every inner drain layered on top of it, so the
 * drain_ae stack MUST be popped down to this terminal's prev_drain — exactly the
 * pop the normal/active branch performs.  Leaving it untouched (the pre-fix
 * behavior) stranded f->drain_ae at the dead inner AbandonEnd; the next
 * begin_abandon_drain on the same fiber then inherited that dead pointer as its
 * prev_drain, wrongly took the nested-fold path at its own KK_ABANDEND, and
 * RK_DRAIN-walked a slice with no live terminal -> HANG (the single-fiber
 * foreign-escape-then-drain regression).
 *
 * For the ACTIVE drain's terminal, two sub-cases:
 *   - NESTED inside an enclosing one (ae->prev_drain != NULL — the H1 recursion):
 *     fold the composed inner reason into the ENCLOSING drain and continue the
 *     OUTER walk as RK_DRAIN, so the inner slice's cleanup failures compose into
 *     the outer clause result exactly like an ordinary nested scope.
 *   - top-level: continue the clause's (now composed) reason at c->next. */
static int finish_abandon_drain(Rt *rt, Fiber *f, Cont *c,
                                int live_kind, KValue *live_val) {
  AbandonEnd *ae = (AbandonEnd *)c->aux;
  int    okind = ae->rkind;
  KValue *oval = ae->rval;
  compose_reason_into(&okind, &oval, live_kind, live_val); /* H2: don't swallow it  */
  f->cur_exits = ae->saved_exits;
  if (ae != (AbandonEnd *)f->drain_ae) {
#ifdef KRT2_ABANDON_INSTRUMENT
    g_rt_foreign_hits++;
#endif
    /* FOREIGN terminal (perform-into-an-ENCLOSING-aborting-handler nested
     * capture, §32.2.20).  Geometry: an OUTER drain (`ae`) is active; one of its
     * abandoned `defer`s performs an op that resolves OUTWARD to an ENCLOSING
     * handler whose clause ALSO abandons.  That second abandonment opens an INNER
     * drain (now `f->drain_ae`), and the slice it captured for the inner abort
     * INCLUDES `ae`'s own KK_ABANDEND terminal — so the inner RK_DRAIN walk
     * reaches `ae`, a terminal that is NOT the active drain (`ae != f->drain_ae`).
     *
     * The drain_ae stack at this point is strictly LIFO (verified):
     *     f->drain_ae (inner) -> ... -> ae (this outer terminal) -> ae->prev_drain
     * `ae->kont` is the outer clause's post-handler continuation, captured at
     * install OUTSIDE both abandoned slices.  Escaping to it terminates `ae`'s
     * drain AND tears down every inner drain layered on top of it (we jump clean
     * past all of them), so the next live drain is the one that was active BEFORE
     * `ae` began: `ae->prev_drain`.
     *
     * THE BUG THIS FIXES: the pre-fix branch left `f->drain_ae` UNTOUCHED here,
     * dangling at the dead inner AbandonEnd.  The next begin_abandon_drain on the
     * same fiber then read that dead pointer as its `prev_drain`, wrongly took the
     * nested-fold path at its own KK_ABANDEND, and RK_DRAIN-walked a slice with no
     * live KK_ABANDEND terminal -> the walk never terminated -> HANG.  Popping the
     * stack down to `ae->prev_drain` restores the correct pre-outer-drain state,
     * matching the normal finish_abandon_drain pop discipline. */
    f->k = ae->kont;
    f->drain_ae = ae->prev_drain;
    return apply_reason(rt, f, okind, oval, ae->rlabel);
  }
#ifdef KRT2_ABANDON_INSTRUMENT
  g_rt_active_hits++;
#endif
  /* fix 2: the ACTIVE drain's terminal — resume at its LIVE successor c->next so a
   * perform that RESUMED during this drain (re-splicing the captured slice) keeps
   * its threaded continuation, rather than having it hard-overwritten by ae->kont. */
  f->k = c->next;
  f->drain_ae = ae->prev_drain;        /* pop to the enclosing drain (if any)      */
  if (ae->prev_drain) {
    /* fold into the enclosing drain, then keep walking it as a drain */
    compose_reason_into(&ae->prev_drain->rkind, &ae->prev_drain->rval, okind, oval);
    return unwind(rt, f, RK_DRAIN, NULL, NULL);
  }
  return apply_reason(rt, f, okind, oval, ae->rlabel);
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
  kassert_live(a);
  kassert_live(b);
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
      kassert_live(op);
      const char *nm = (op && op->tag == K_STR) ? (const char *)op->as.str.p : "?";
      char msg[160];
      snprintf(msg, sizeof msg,
               "internal: perform '%s' escaped all handlers (unhandled effect op)", nm);
      return unwind(rt, f, RK_FAIL, kstr0(msg), NULL);
    }
    if (c->kind == KK_HANDLER && eff_label_same(c->a, label)) {
      Handler *h = (Handler *)c->aux;
      kassert_live(op);
      if (!op || op->tag != K_STR)
        return unwind(rt, f, RK_FAIL, kstr0("internal: effect operation name is not a string"), NULL);
      KValue *clause = h->ops ? kproj(h->ops, (const char *)op->as.str.p) : NULL;
      if (!clause) {
        char msg[160];
        snprintf(msg, sizeof msg, "internal: handler has no clause for op '%s'",
                 (const char *)op->as.str.p);
        return unwind(rt, f, RK_FAIL, kstr0(msg), NULL);
      }
      ExitStack *body_exits = f->cur_exits;       /* the captured body's exits   */
      ExitStack *handler_exits = (ExitStack *)c->aux2; /* what the prompt restores */
      Resumption *r = (Resumption *)GC_MALLOC(sizeof(Resumption));
      r->cur_exits = body_exits;
      r->used = 0;
      r->tail_res = 0;
      /* §4b TAIL-RESUMPTIVE FAST PATH.  When the clause resumes its continuation
       * exactly once, in tail position (Usage.tailResumptiveClause marked this op
       * on a DEEP handler), the op-site→handler segment is never abandoned and is
       * resumed in place.  So we DO NOT sever it and we DO NOT pop+later-re-push
       * the KK_HANDLER: the captured `head` still links — through the UNTOUCHED
       * frame c (the prompt) — to c->next, so do_resume restores the whole live
       * chain (handler included) with one pointer write, allocating no Cont and
       * re-installing the deep handler for free.  The clause itself still runs
       * OUTSIDE the prompt (f->k = c->next), exactly like the general path, so its
       * own perform/return observably matches; only the resumption is lighter.
       * Constant Cont depth + no per-perform Cont allocation across an effect loop
       * — the whole point of Stage 4b (§32.2.15). */
      if (h->deep && op_is_tail_resumptive(h, (const char *)op->as.str.p)) {
        r->tail_res = 1;
        /* `head` is the op-site frame; its `next` chain is UNTOUCHED and still
         * runs through this very KK_HANDLER (frame c) to c->next.  Even in the
         * tail-perform case (prev==NULL) head == c, so re-rooting at head re-enters
         * the still-installed prompt: do_resume delivers v into KK_HANDLER, which
         * runs `h->ret` — exactly the general path, without any sever or re-push. */
        r->head = head;
        r->tail = NULL;                  /* unused on the fast path (no re-link)    */
        r->label = NULL; r->handler = NULL; r->handler_exits = NULL;
        f->k = c->next;                  /* the clause runs outside the prompt      */
        f->cur_exits = handler_exits;    /* under the cur_exits the prompt restores */
        return run_op_clause(rt, f, clause, payload, kfgn(r, KRT2_KIND_RESUMPTION));
      }
      /* ── general 4a path (sever + re-link + deep re-push) ──────────────────────
       * Build the one-shot resumption from the captured sub-chain [head .. prev].
       * The captured slice runs from the op site up to (and EXCLUDING) the handler
       * frame `c` (§2.3).  We POP the handler frame: the clause is the handler's
       * own code and runs OUTSIDE the prompt (its result flows to c->next, the
       * handler's own continuation).  The resumption re-splices [head..prev] onto
       * c->next when invoked; a deep handler additionally re-pushes a fresh copy
       * of this KK_HANDLER around the resumed body (§32.2.22). */
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
      /* §32.2.20/.21 abandonment guard.  When the clause completes WITHOUT having
       * resumed, the severed slice [head..prev] (and its `using`/`defer` exit
       * actions) must still drain.  Sit a KK_ABANDON frame BENEATH the clause
       * carrying this resumption: on clause completion (deliver/unwind reach it),
       * an unused `r` triggers begin_abandon_drain; a resumed `r` is transparent.
       * Only needed when something was actually severed (r->head != NULL); a tail
       * perform (identity resumption) captured no slice, so there is nothing to
       * drain and no frame is added. */
      if (r->head) f->k = cont_new2(KK_ABANDON, NULL, r, NULL, f->k);
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
  Resumption *r = (Resumption *)kas_fgn_kind(kbox, KRT2_KIND_RESUMPTION);
  if (r->used) {
    /* the compile-time E_QTT_CONTINUATION_CAPTURE gate rejects >1 use, so this
     * is an internal invariant break (rt-multishot-effects is not advertised). */
    return unwind(rt, f, RK_FAIL,
                  kstr0("internal: one-shot resumption used more than once (rt-multishot-effects absent)"), NULL);
  }
  r->used = 1;
  /* §4b tail-resume: the segment was never severed and the KK_HANDLER was never
   * removed, so restoring is a single pointer write — f->k = head re-roots the
   * whole live chain (op-site frames → the still-installed prompt → its
   * continuation), the deep handler reinstated for free, no Cont allocated.  The
   * tail-perform case (head == the KK_HANDLER frame itself) re-enters the prompt
   * directly, so deliver(value) runs `h->ret` — matching the general path. */
  if (r->tail_res) {
    f->k = r->head;
    f->cur_exits = r->cur_exits;
    return deliver(rt, f, value);
  }
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
      /* fix SP (§32.2.6): this CK loop re-runs `iterate` IN PLACE without
       * re-entering from the run queue, so a tight non-ceding loop would ignore a
       * pending interrupt AND starve the worker.  Treat the back-edge as a safe
       * point: (1) flag a deliverable interrupt so the fiber_step gate delivers it
       * on the next turn (mask_depth>0 keeps it suppressed — held until mask exit);
       * (2) spend a fairness quantum and, when it runs out, CEDE — re-enqueue this
       * fiber behind other runnables and stop stepping (a yield, not a finish; the
       * `if (!deliver(...)) return;` caller just returns from fiber_step, leaving the
       * re-enqueued fiber owned by the run queue). */
      if (atomic_load_explicit(&f->interrupt_pending, memory_order_acquire)
          && f->mask_depth == 0)
        f->safepoint_hit = 1;
      if (f->backedge_budget == 0) {
        f->backedge_budget = KRT2_BACKEDGE_QUANTUM;
        krt2i_resume(rt, f);             /* fairness cede: re-enqueue + stop stepping */
        return 0;
      }
      f->backedge_budget--;
      return 1;
    case KK_RETSCOPE:                    /* body completed normally: transparent  */
      f->k = c->next; f->cur = krt2_pure(v); return 1;
    case KK_DOSCOPE: {                    /* normal exit: run exit actions, deliver v */
      ExitStack *xs = (ExitStack *)c->aux;
      ExitStack *restore = (ExitStack *)c->aux2;
      f->k = c->next;
      return begin_finseq(rt, f, xs, restore, RK_NORMAL, v, NULL, NULL);
    }
    case KK_FINSEQ: {                    /* a finalizer completed; run the next */
      FinSeq *fs = (FinSeq *)c->aux;
      if (fs->i >= 0) {
        KValue *e = fs->xs->items[fs->i]; fs->i--;
        /* §18.1.4 reason-carrying finalizers: an onExit/onInterrupt item is a
         * MARKER ctor carrying the handler; substitute the handler applied to
         * the reconstructed Exit/cause (so it runs MASKED-LIFO like any defer).
         * onInterrupt fires only on an interrupt exit; otherwise it is a no-op.
         * fix 1: during an abandonment drain (drain_ae set) the finseq PRIMARY is
         * the running composed clause reason, used as the cause-composition base;
         * but the Exit handed to an onExit IN the abandoned slice keeps its
         * pre-fix drain semantics (the slice's body did not terminate normally,
         * so it is not the clause's exit) — reconstruct from RK_DRAIN there. */
        e = finalizer_action_for_reason(e, fs->origin_kind, fs->origin_val);
        f->cur = e; return 1;
      }
      f->k = c->next;
      if (fs->drain_ae) {
        /* fix 1: an abandoned do-scope finished draining.  Persist the running
         * composed reason (clause result folded with this scope's cleanup
         * failures, left-associatively) into the drain terminal, then CONTINUE
         * the slice walk as RK_DRAIN so it stays transparent at every control
         * frame and reaches the KK_ABANDEND terminal (which reads the final
         * composed reason).  Do NOT apply_reason fs->rkind here: that would
         * unwind the clause reason through the rest of the abandoned slice. */
        fs->drain_ae->rkind = fs->rkind;
        fs->drain_ae->rval  = fs->rval;
        return unwind(rt, f, RK_DRAIN, NULL, NULL);
      }
      return apply_reason(rt, f, fs->rkind, fs->rval, fs->rlabel);
    }
    case KK_HANDLER: {                    /* §18.1.21 body completed: run `return` */
      Handler *h = (Handler *)c->aux;
      f->k = c->next;
      f->cur_exits = (ExitStack *)c->aux2; /* leave the handled body's do-scopes  */
      f->cur = kapp(h->ret, v);            /* `case return x -> ...` (Eff res)     */
      return 1;
    }
    case KK_BLOCKING:
      leave_blocking_region(f);
      f->k = c->next;
      f->cur = krt2_pure(v);
      return 1;
    case KK_ABANDON: {                    /* §32.2.20 clause completed (normal v)  */
      Resumption *r = (Resumption *)c->aux;
      f->k = c->next;
      if (r->used) { f->cur = krt2_pure(v); return 1; } /* resumed: transparent    */
      /* abandoned: drain the severed slice's exit actions, then deliver v.       */
      return begin_abandon_drain(rt, f, r, RK_NORMAL, v, NULL);
    }
    case KK_ABANDEND:                     /* §32.2.20 slice drained: resume clause  */
      /* Reached via a delivered value (no failure escaped the finseq): the live
       * reason is RK_NORMAL, which composes to nothing. */
      return finish_abandon_drain(rt, f, c, RK_NORMAL, v);
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
          case RK_DRAIN:     /* §32.2.20 an abandonment drain that reached the
                              * fiber base instead of its KK_ABANDEND terminal:
                              * the slice's defers all ran; there is no clause
                              * result left to resume, so simply stop (do NOT
                              * finish the fiber — the clause already delivered). */
            return 0;
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
        if (rkind == RK_CONTINUE) {                              /* re-iterate, KEEP KK_LOOP */
          f->cur = c->a;
          /* fix SP: a `continue` is a loop back-edge too — same safe point as the
           * normal KK_LOOP completion (interrupt-observation + fairness cede). */
          if (atomic_load_explicit(&f->interrupt_pending, memory_order_acquire)
              && f->mask_depth == 0)
            f->safepoint_hit = 1;
          if (f->backedge_budget == 0) {
            f->backedge_budget = KRT2_BACKEDGE_QUANTUM;
            krt2i_resume(rt, f);
            return 0;
          }
          f->backedge_budget--;
          return 1;
        }
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
        /* fix 1: during an abandonment drain (rkind == RK_DRAIN, f->drain_ae set),
         * thread the active drain terminal so the finseq composes this scope's
         * cleanup failures against the running clause reason left-associatively. */
        AbandonEnd *drain_ae = (rkind == RK_DRAIN) ? (AbandonEnd *)f->drain_ae : NULL;
        return begin_finseq(rt, f, xs, restore, rkind, rval, rlabel, drain_ae);
      }
      case KK_FINSEQ: {
        /* §32.2.12/§18.7 a finalizer itself FAILED mid-drain.  With finalizers now
         * masked (begin_finseq), an async interrupt can no longer land here, so the
         * only reachable cause is a finalizer body that failed (or re-raised, or
         * restored-then-was-interrupted).  We MUST NOT drop this scope's remaining
         * finalizers (a §18.7 exactly-once violation) and we MUST compose the
         * failing finalizer's cause with the reason the scope was already exiting
         * with via §32.2.12 `Then`.  So: fold the live (rkind,rval) into the saved
         * FinSeq reason, then RE-ENTER the finseq (keep this very KK_FINSEQ frame,
         * fs->i already points at the next-LIFO finalizer) to run the rest under the
         * composed reason.  When the sequence completes, apply_reason propagates the
         * composed cause; the begin_finseq KK_POPMASK below us (c->next) restores the
         * mask exactly once on that final descent.  A NON-failing escape through a
         * finalizer (which §18.7 forbids in source, but defend anyway) leaves the
         * saved reason untouched and simply falls through to the next finalizer. */
        FinSeq *fs = (FinSeq *)c->aux;
        compose_reason_into(&fs->rkind, &fs->rval, rkind, rval);
        f->cur = krt2_pure(kunit());   /* kick: deliver -> KK_FINSEQ runs the next */
        return 1;                       /* KEEP f->k == c (the KK_FINSEQ frame)     */
      }
      case KK_HANDLER:
        /* §18.1.21 a handler intercepts `perform`, NOT abrupt control flow: a
         * fail/return/break/continue/interrupt unwinding through the handled body
         * propagates past the prompt transparently (the body's captured do-scope
         * defers already ran on the KK_DOSCOPE frames crossed before reaching
         * here).  Restore the cur_exits the prompt would reinstate, then drop. */
        f->cur_exits = (ExitStack *)c->aux2;
        f->k = c->next; continue;
      case KK_BLOCKING:
        leave_blocking_region(f);
        f->k = c->next; continue;
      case KK_ABANDON: {
        /* §32.2.20 a KK_ABANDON guard frame was reached during an unwind.  Three
         * cases, distinguished by whether this inner resumption was already used and
         * whether we are already inside an OUTER abandonment drain:
         *
         *  (1) r->used — the inner perform resumed, so its captured slice was spliced
         *      back and already drained itself; the guard is transparent.  `continue`.
         *
         *  (2) !r->used and rkind == RK_DRAIN — an UNRESUMED inner resumption whose
         *      KK_ABANDON frame lies INSIDE an outer abandoned slice now being walked.
         *      The inner slice [r->head..r->tail] was severed off this chain at its
         *      own perform, so the outer RK_DRAIN does NOT traverse it — its do-scope
         *      `defer`/`using` exit actions would be lost (H1) unless we drain it too.
         *      Recurse via begin_abandon_drain: run the inner slice's exit actions,
         *      then (its KK_ABANDEND restores) resume THIS outer RK_DRAIN walk where it
         *      left off.  The saved reason carried to the inner KK_ABANDEND is the
         *      outer RK_DRAIN, so the outer walk continues correctly afterward.
         *
         *  (3) !r->used and rkind != RK_DRAIN — the clause itself unwound
         *      (fail/return/interrupt/break/continue) without resuming.  Drain the
         *      severed slice, then continue the clause's own abnormal propagation. */
        Resumption *r = (Resumption *)c->aux;
        f->k = c->next;
        if (r->used) continue;                       /* (1) resumed: transparent     */
        return begin_abandon_drain(rt, f, r, rkind, rval, rlabel); /* (2) drain / (3) */
      }
      case KK_ABANDEND:
        /* §32.2.21 the RK_DRAIN walk reached the slice terminal.  fix 1 already
         * folded every abandoned do-scope's cleanup failure into ae->rkind/rval
         * LEFT-ASSOCIATIVELY against the clause result as the drain ran (each
         * finseq seeded its compose-primary from the running drain reason and
         * wrote the result back), so ae->* holds the fully composed reason —
         * exactly the spine ordinary scope exit produces (Then(Then(clause,ce),cl)),
         * not the old right-leaning Then(clause,Then(ce,cl)).  The live (rkind,rval)
         * is normally RK_DRAIN (composes to nothing); a finalizer failure that
         * ESCAPED this slice's finseq (e.g. a restoring finalizer interrupted)
         * arrives non-RK_DRAIN and finish_abandon_drain composes it in so it is not
         * swallowed (H2). */
        return finish_abandon_drain(rt, f, c, rkind, rval);
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
  krt2i_cleanup_parked_wait(f);
  atomic_store_explicit(&f->interrupt_pending, 0, memory_order_relaxed);
  return unwind(rt, f, RK_INTERRUPT, f->interrupt_cause, NULL);
}

int krt2i_deliver_pending_before_park(Rt *rt, Fiber *f) {
  if (atomic_load_explicit(&f->interrupt_pending, memory_order_acquire)
      && f->mask_depth == 0) {
    return deliver_interrupt(rt, f) ? 1 : -1;
  }
  return 0;
}

/* Step `f` until it suspends (parks / cedes) or finishes. */
static void fiber_step_run(Rt *rt, Fiber *f) {
  for (;;) {
    KValue *cur = f->cur;
    int op = kctor_tagid(cur);
    /* fix S2 (sleep-timer dedup): a fiber resuming from a sleep park with a pending
     * interrupt and `cur` STILL the OP_SLEEP node was woken by the INTERRUPT, not by
     * its timer (the timer would have set cur to pure(Unit) and cleared sleep_armed).
     * That sleep is now abandoned — masked => the OP_SLEEP below re-arms a fresh FULL
     * timer; unmasked => the delivery gate unwinds past it.  EITHER way the original
     * timer must be cancelled so it cannot fire later and CAS-win an unrelated park
     * (spurious resume).  Route the cancel to the reactor BEFORE the delivery gate so
     * the unmasked-unwind path cancels too.  (start_sleep also cancels a replaced
     * timer, but the unwind path never re-runs OP_SLEEP — only this hook covers it.) */
    if (f->resumed
        && atomic_load_explicit(&f->interrupt_pending, memory_order_acquire)
        && atomic_load_explicit(&f->sleep_armed, memory_order_acquire)
        && op == OP_SLEEP) {
      krt2i_cancel_sleep(rt, f);
    }
    /* §32.2.5 interruption point: a pending request becomes observable only at a
     * genuine suspension/resume point (sleep/await/STM-retry/cede wake) or an
     * explicit poll — NOT at a mask-region exit.  `resumed` is set when the fiber
     * (re-)enters fiber_step from the run queue and is consumed on the first turn,
     * so this gate fires ONLY on that resume turn.  Without the `resumed` guard,
     * dropping mask_depth to 0 mid-step (KK_POPMASK/KK_SETMASK) would make the very
     * next non-suspending step a delivery point and wrongly interrupt a fiber whose
     * whole body was masked — the §18.1.12/§32.2.5 masked-sleep suppression bug.
     * OP_POLL delivers independently of this flag (§18.1.12: poll delivers even
     * when masked).  Entering OP_UNINTERRUPTIBLE/OP_MASK is not itself an
     * unmasked interruption point: install the mask first, then let the body (or
     * an explicit poll/restore) decide where the pending request is observable. */
    /* fix SP (§32.2.6): a loop back-edge is ALSO an interruption point.  A tight
     * CK loop (KK_LOOP re-running `iterate` in place) or a codegen native loop
     * (which sets safepoint_hit via krt2_safepoint) never re-enters from the run
     * queue, so `resumed` stays 0 — yet the spec requires a pending interrupt to be
     * observable at such safe points.  Deliver on `safepoint_hit` too.  This does
     * NOT reintroduce the masked-sleep suppression bug: safepoint_hit is set ONLY at
     * a genuine back-edge (and only when mask_depth==0), never on a mask-region exit. */
    int entering_mask = (op == OP_UNINTERRUPTIBLE || op == OP_MASK);
    if (!entering_mask
        && (f->resumed || f->safepoint_hit)
        && atomic_load_explicit(&f->interrupt_pending, memory_order_acquire)
        && f->mask_depth == 0) {
      f->resumed = 0;
      f->safepoint_hit = 0;
      if (!deliver_interrupt(rt, f)) return; /* finished */
      continue;                              /* run the action installed by unwind */
    }
    f->resumed = 0;   /* consumed: only the FIRST turn after a resume is a delivery point */
    f->safepoint_hit = 0;
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
      case OP_FORK:                          /* child inherits f's FiberRef snapshot (§18.1.7) */
        if (!deliver(rt, f, kfgn(krt2i_spawn_from(rt, f, kctor_arg(cur, 0), f->cur_scope, 0), KRT2_KIND_FIBER))) return;
        break;
      case OP_FORK_DAEMON:
        if (!deliver(rt, f, kfgn(krt2i_spawn_from(rt, f, kctor_arg(cur, 0), f->cur_scope, 1), KRT2_KIND_FIBER))) return;
        break;
      case OP_AWAIT: {
        int dp = krt2i_deliver_pending_before_park(rt, f);
        if (dp < 0) return;
        if (dp > 0) break;
        if (do_await(rt, f, kctor_arg(cur, 0))) break; else return;
      }
      case OP_CEDE: {
        int dp = krt2i_deliver_pending_before_park(rt, f);
        if (dp < 0) return;
        if (dp > 0) break;
        f->cur = krt2_pure(kunit());
        krt2i_resume(rt, f);           /* re-enqueue behind other runnables  */
        return;
      }
      case OP_SLEEP: {
        /* §18.1.6: read the duration as a SIGNED int.  A nonpositive ns —
         * notably `sleepUntil` of a PAST Instant, whose `instantDiff` is
         * negative — must complete immediately.  Without this guard the
         * `(uint64_t)` cast wrapped a negative value to a huge unsigned and
         * the fiber parked ~forever (never woken). */
        int64_t ns = kas_int(kctor_arg(cur, 0));
        if (ns <= 0) {
          if (!deliver(rt, f, kunit())) return;  /* sleepFor returns Unit */
          break;
        }
        int dp = krt2i_deliver_pending_before_park(rt, f);
        if (dp < 0) return;
        if (dp > 0) break;
        int park_unmasked = (f->mask_depth == 0);
        krt2i_submit_sleep(rt, f, (uint64_t)ns);
        if (krt2i_claim_pending_after_park(f, park_unmasked)) {
          krt2i_cancel_sleep(rt, f);
          if (!krt2i_deliver_claimed_interrupt(rt, f)) return;
          break;
        }
        return;                        /* parked; reactor resumes it          */
      }
      case OP_NOW:
        if (!deliver(rt, f, kint((int64_t)uv_hrtime()))) return;
        break;
      case OP_NEW_PROMISE:
        if (!deliver(rt, f, promise_new())) return;
        break;
      case OP_COMPLETE_PROMISE:
        if (!deliver(rt, f, promise_complete(rt, kctor_arg(cur, 0), kctor_arg(cur, 1)))) return;
        break;
      case OP_AWAIT_PROMISE_EXIT: {
        int dp = krt2i_deliver_pending_before_park(rt, f);
        if (dp < 0) return;
        if (dp > 0) break;
        if (do_await_promise(rt, f, kctor_arg(cur, 0))) break; else return;
      }
      case OP_CURRENT_FIBER_ID:
        if (!deliver(rt, f, kint((int64_t)f->id))) return;
        break;
      case OP_FIBER_ID: {
        Fiber *tf = (Fiber *)kas_fgn_kind(kctor_arg(cur, 0), KRT2_KIND_FIBER);
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
        /* `restore` re-enters an action at the mask-entry interruptibility level.
         * If that level is interruptible and a request is already pending, the
         * restored action itself is the interruption point; otherwise an already
         * pending interrupt can be missed until the restored action later parks. */
        if (atomic_load_explicit(&f->interrupt_pending, memory_order_acquire)
            && f->mask_depth == 0)
          f->safepoint_hit = 1;
        break;
      }
      /* ── structured concurrency ─────────────────────────────────────── */
      case OP_NEW_SCOPE:
        if (!deliver(rt, f, krt2i_op_new_scope())) return;
        break;
      case OP_FORK_IN:
        if (!deliver(rt, f, krt2i_op_fork_in(rt, f, kctor_arg(cur, 0), kctor_arg(cur, 1)))) return;
        break;
      case OP_SHUTDOWN_SCOPE:
        if (krt2i_op_shutdown_scope(rt, f, kctor_arg(cur, 0))) break; else return;
      case OP_MONITOR:
        if (!deliver(rt, f, krt2i_op_monitor(kctor_arg(cur, 0)))) return;
        break;
      case OP_AWAIT_MONITOR: {
        int dp = krt2i_deliver_pending_before_park(rt, f);
        if (dp < 0) return;
        if (dp > 0) break;
        if (krt2i_op_await_monitor(rt, f, kctor_arg(cur, 0))) break; else return;
      }
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
         * trap so a mis-lowered defer is a diagnosed error, not a dropped action.
         *
         * Register the action with the abort-exit stack too.  A generated C scalar
         * worker or boxed-loop safe point can longjmp out while this CK do-scope is
         * active but before the ordinary KK_DOSCOPE frame is reached again; the
         * abort-exit finalizer makes normal scope exit and scalar-abort unwinding
         * share the same exactly-once action. */
        if (!f->cur_exits) krt_fail("internal: defer outside any do-scope (mis-lowered §18.7 defer)");
        exitstack_push(f->cur_exits, abort_exit_scope_finalizer(kctor_arg(cur, 0)));
        if (!deliver(rt, f, kunit())) return;
        break;
      case OP_ABORT_EXIT_FIN: {
        KValue *exit_action = abort_exit_take(kctor_arg(cur, 0));
        f->cur = exit_action ? exit_action : krt2_pure(kunit());
        break;
      }
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
        Fiber *tf = (Fiber *)kas_fgn_kind(kctor_arg(cur, 0), KRT2_KIND_FIBER);
        pthread_mutex_lock(&tf->lock);
        KValue *r = (atomic_load_explicit(&tf->status, memory_order_acquire) == F_DONE)
                        ? krt2i_some(kdup(tf->exit)) : krt2i_none();
        pthread_mutex_unlock(&tf->lock);
        if (!deliver(rt, f, r)) return;
        break;
      }
      /* ── §18.1.7 FiberRef (fiber-local cells; copy-on-fork at OP_FORK) ──── */
      case OP_NEW_FIBER_REF:
        if (!deliver(rt, f, fiber_ref_new(kctor_arg(cur, 0)))) return;
        break;
      case OP_GET_FIBER_REF:
        if (!deliver(rt, f, kdup(fiber_local_get(f, (int)kas_int(kctor_arg(cur, 0)))))) return;
        break;
      case OP_SET_FIBER_REF:
        fiber_local_set(f, (int)kas_int(kctor_arg(cur, 0)), kctor_arg(cur, 1));
        if (!deliver(rt, f, kunit())) return;
        break;
      case OP_MODIFY_FIBER_REF: {               /* atomic get-apply-set -> new value */
        /* A FiberRef cell is private to THIS fiber, which runs single-threaded on
         * the CK-machine, so the read-modify-write is trivially atomic: no other
         * agent observes or races the cell.  `fn` is a pure (a -> a). */
        int id = (int)kas_int(kctor_arg(cur, 0));
        KValue *old = fiber_local_get(f, id);
        KValue *nv = kapp(kctor_arg(cur, 1), old);  /* fn old (pure) */
        /* If fn returns the old cell by alias, storage and result need distinct owns. */
        KValue *ret = (nv == old) ? kdup(nv) : nv;
        fiber_local_set(f, id, kdup(nv));
        if (!deliver(rt, f, ret)) return;
        break;
      }
      /* ── §18.11 Promise non-blocking peek (never parks) ─────────────────── */
      case OP_POLL_PROMISE:
        if (!deliver(rt, f, promise_poll(kctor_arg(cur, 0)))) return;
        break;
      case OP_IS_DONE_PROMISE:
        if (!deliver(rt, f, promise_is_done(kctor_arg(cur, 0)))) return;
        break;
      case OP_BLOCKING:
        {
          int dp = krt2i_deliver_pending_before_park(rt, f);
          if (dp < 0) return;
          if (dp > 0) break;
        }
        enter_blocking_region(f);
        f->k = cont_new(KK_BLOCKING, NULL, f->k);
        if (krt2i_submit_blocking(rt, f, kctor_arg(cur, 0))) return;
        leave_blocking_region(f);
        f->k = f->k->next;
        if (!unwind(rt, f, RK_FAIL, kstr0("rt.blocking: failed to start blocking worker"), NULL)) return;
        break;
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
            if (cur->tag == K_NATIVE && cur->as.native.blocking && !g_on_blocking_lane) {
              int dp = krt2i_deliver_pending_before_park(rt, f);
              if (dp < 0) return;
              if (dp > 0) break;
              if (krt2i_submit_blocking(rt, f, cur)) return;
              if (!unwind(rt, f, RK_FAIL, kstr0("rt.blocking: failed to start blocking worker"), NULL)) return;
              break;
            }
            int completed_blocking_native =
              (cur->tag == K_NATIVE && cur->as.native.blocking && g_on_blocking_lane);
            KValue *r = krun_io(cur);
            if (completed_blocking_native
                && atomic_load_explicit(&f->interrupt_pending, memory_order_acquire)
                && f->mask_depth == 0) {
              if (!deliver_interrupt(rt, f)) return;
              break;
            }
            /* fix SP (§32.2.6): a codegen-emitted NATIVE loop inside this synchronous
             * do-block runs entirely under krun_io — it never re-enters the gate at
             * the top of this loop, so krt2_safepoint() could only SET safepoint_hit,
             * not act on it.  Honor it HERE, right after the bridge returns: if the
             * native loop hit a safe point with a deliverable interrupt, deliver it
             * now (the bridge's result is discarded — the fiber unwinds).  Masked
             * suppression already held inside krt2_safepoint (it never sets the flag
             * when mask_depth>0). */
            if (f->safepoint_hit
                && atomic_load_explicit(&f->interrupt_pending, memory_order_acquire)
                && f->mask_depth == 0) {
              f->safepoint_hit = 0;
              if (kis_fail(r)) {
                KValue *primary = krt2_cause_interrupt(f->interrupt_cause);
                KValue *cleanup = krt2_cause_fail(r->as.fail.err);
                atomic_store_explicit(&f->interrupt_pending, 0, memory_order_relaxed);
                if (!unwind(rt, f, RK_RERAISE, krt2_cause_then(primary, cleanup), NULL)) return;
              } else if (krt2_is_reraise_action(r)) {
                KValue *primary = krt2_cause_interrupt(f->interrupt_cause);
                KValue *cleanup = kctor_arg(r, 0);
                atomic_store_explicit(&f->interrupt_pending, 0, memory_order_relaxed);
                if (!unwind(rt, f, RK_RERAISE, krt2_cause_then(primary, cleanup), NULL)) return;
              } else if (!deliver_interrupt(rt, f)) return;
              break;
            }
            f->safepoint_hit = 0;
            if (krt2_is_reraise_action(r)) {
              if (!unwind(rt, f, RK_RERAISE, kctor_arg(r, 0), NULL)) return;
              break;
            }
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

/* fix SP: publish the fiber being stepped (g_cur_fiber) for the duration of the
 * step so a codegen-emitted native loop on THIS worker can reach it from a bare
 * krt2_safepoint().  Save/restore for re-entrancy: runPure (krt2_run_eff) drives
 * a private CK-machine via fiber_step, which may itself run a native loop, so the
 * outer fiber must be restored when the nested step returns. */
static void fiber_step(Rt *rt, Fiber *f) {
  Fiber *saved = g_cur_fiber;
  Rt *saved_rt = g_cur_rt;
  jmp_buf *saved_scalar_abort_jmp = g_scalar_abort_jmp;
  jmp_buf scalar_abort_jmp;
  g_cur_fiber = f;
  g_cur_rt = rt;
  g_scalar_abort_jmp = &scalar_abort_jmp;
  f->backedge_budget = KRT2_BACKEDGE_QUANTUM;   /* fresh fairness quantum per step */
  if (setjmp(scalar_abort_jmp) == 0) {
    fiber_step_run(rt, f);
  } else {
    if (f->safepoint_hit
        && atomic_load_explicit(&f->interrupt_pending, memory_order_acquire)
        && f->mask_depth == 0) {
      f->resumed = 0;
      f->safepoint_hit = 0;
      atomic_store_explicit(&f->interrupt_pending, 0, memory_order_relaxed);
      ExitStack *xs = abort_exit_drain_stack(f);
      int keep_stepping =
        (xs && xs->n > 0)
          ? begin_finseq(rt, f, xs, f->cur_exits, RK_INTERRUPT, f->interrupt_cause, NULL, NULL)
          : unwind(rt, f, RK_INTERRUPT, f->interrupt_cause, NULL);
      if (keep_stepping) {
        fiber_step_run(rt, f);
      }
    } else {
      krt_fail("internal: scalar-worker abort reached runtime without a deliverable interrupt");
    }
  }
  g_scalar_abort_jmp = saved_scalar_abort_jmp;
  g_cur_rt = saved_rt;
  g_cur_fiber = saved;
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

/* §32.2.6 safe point for a CODEGEN-EMITTED native loop (the unboxed scalar
 * while-loops the C/LLVM backends emit).  Such a loop runs synchronously on the
 * worker inside the K_NATIVE bridge — the CK-machine is not iterating, so a
 * pending interrupt would otherwise be ignored until the whole loop finishes.
 * The generated loop calls this at its back-edge (cheaply, counter-gated — see the
 * backends).  If an interrupt is deliverable, it returns non-zero so generated
 * code can break/abort back to the CK-machine; the next fiber_step turn then
 * delivers via the safepoint_hit gate.  If no interrupt is deliverable but a
 * sibling fiber is runnable, this function briefly runs that sibling on the same
 * worker and then returns 0, preserving the current scalar loop's C-local state.
 *
 * Returns 1 iff the loop should abort to let the runtime deliver a pending
 * interrupt at this safe point — i.e. interrupt_pending && mask_depth==0.  A
 * masked fiber (mask_depth>0) returns 0: suppression holds, the interrupt is
 * delivered only after the mask exits (an interruption point reached unmasked).
 * 0 if there is no current fiber (a pure top-level native call off any fiber).
 *
 * This is a cooperative safe point, not a suspension of the current fiber: native
 * scalar workers keep live state in C locals, so a true park/resume would require
 * a different worker ABI.  Running one queued sibling inline provides weak
 * fairness without losing those locals. */
int krt2_safepoint(void) {
  Fiber *f = g_cur_fiber;
  if (!f) return 0;
  if (atomic_load_explicit(&f->interrupt_pending, memory_order_acquire)
      && f->mask_depth == 0) {
    f->safepoint_hit = 1;   /* the fiber_step gate delivers on the next turn */
    return 1;
  }
  Rt *rt = g_cur_rt ? g_cur_rt : g_rt;
  if (rt && !g_safepoint_yielding) {
    Fiber *other = rq_try_pop(rt);
    if (other && other != f) {
      atomic_store(&other->status, F_RUNNING);
      g_safepoint_yielding++;
      fiber_step(rt, other);
      g_safepoint_yielding--;
    } else if (other == f) {
      krt2i_rq_push(rt, other);
    }
  }
  return 0;
}

void krt2_scalar_abort(void) {
  Fiber *f = g_cur_fiber;
  if (f && f->safepoint_hit && g_scalar_abort_jmp) {
    longjmp(*g_scalar_abort_jmp, 1);
  }
  krt_fail("internal: scalar-worker abort without an active runtime safe-point");
}

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

/* §1 process-exit teardown: with the runtime now PERSISTENT (run_main no longer
 * shuts down), the worker pool/reactor would otherwise outlive main().  Register
 * a single atexit hook to join them cleanly on normal process exit, so a
 * compiled program (one run_main) keeps the old "workers joined before exit"
 * flush/quiescence guarantee.  Registered AFTER krt_init's atexit(krt_at_exit),
 * so it runs FIRST (atexit is LIFO) — workers join while the GC is still up. */
static void krt2_atexit_shutdown(void) { if (g_rt) krt2_shutdown(g_rt); }

Rt *krt2_new(int nworkers) {
  if (g_rt) return g_rt;
  krt_init();                  /* GC_INIT + GMP-through-GC (kappart) */
  GC_allow_register_threads(); /* permit worker/reactor thread registration */
  prepopulate_singletons();
  atexit(krt2_atexit_shutdown); /* join the persistent pool on process exit (§1) */

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
  atomic_store_explicit(&rt->main_fiber, NULL, memory_order_relaxed);   /* fix 5 */
  atomic_store_explicit(&rt->daemon_scope, NULL, memory_order_relaxed); /* fix 6 */
  rt->main_done = 0;
  rt->rq_idle = 0;
  rt->reactor_started = 0;
  rt->workers_started = 0;

  krt2i_reactor_init(rt);      /* uv_loop_init + uv_async_init (main thread) */
  g_rt = rt;
  return rt;
}

Rt *krt2_current(void) { return g_rt; }

int krt2_exit_is_success(KValue *exit) { return kctor_is(exit, "Success"); }

/* §1 PERSISTENT RUNTIME.  Spin up the reactor + worker pool exactly ONCE, the
 * first time a fiber needs to run, and keep them alive across every subsequent
 * krt2_run_main.  rq_pop blocks on rq_cv while idle and returns NULL only once
 * `shutting_down` is set (krt2_shutdown), so an idle pool simply waits for the
 * next run's main fiber — no per-run thread create/join, no per-run krt_init
 * side effects, and crucially no shutdown→reinit cycle (the GC under-retention
 * that crashed repeated run_main at ~call 60-80; see RUNTIME-EFFICIENCY-REVIEW
 * §1).  The reactor's ref'd uv_async handle keeps its uv_loop alive identically.
 * Idempotent + thread-safe-by-construction: only ever called from the single
 * krt2_run_main caller (the runtime is single-entrant at the run_main boundary). */
/* The worker + reactor threads host the running fibers' C stacks: a pure deep
 * recursion in a total program (e.g. repro/native-stack-repro's ~8372 non-tail
 * `go` frames) runs HERE, not on the 8MB main-thread stack the interpreter uses.
 * A secondary pthread's default stack is small (512KB on macOS), so even modest
 * depth overflows — the C backend (a fatter frame per level than LLVM) hit it
 * first.  Give these threads a stack matching the main thread (default 8 MiB, env
 * KAPPA_STACK_MB) — lazily committed, so the reservation is virtual (VSZ), not
 * resident (RSS), until the recursion actually goes deep.  This is a FLOOR: the
 * principled fix is a tail-call/stack transform (see STACK-SAFETY-DESIGN.md) that
 * runs the common deep-recursion shapes in constant stack. */
static size_t krt2i_thread_stack_bytes(void) {
  const char *e = getenv("KAPPA_STACK_MB");
  long mb = e ? atol(e) : 8;   /* main-thread parity; lazily committed (VSZ != RSS) */
  if (mb < 1) mb = 1;
  return (size_t)mb * 1024u * 1024u;
}

int krt2i_spawn_thread(pthread_t *t, void *(*fn)(void *), void *arg) {
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, krt2i_thread_stack_bytes());
  int rc = GC_pthread_create(t, &attr, fn, arg);
  pthread_attr_destroy(&attr);
  return rc;
}

static void krt2i_ensure_started(Rt *rt) {
  if (rt->workers_started) return;
  krt2i_reactor_start(rt);
  for (int i = 0; i < rt->nworkers; i++)
    krt2i_spawn_thread(&rt->workers[i], worker_main, rt);
  rt->workers_started = 1;
}

KValue *krt2_run_main(KValue *action) {
  Rt *rt = g_rt ? g_rt : krt2_new(0);

  /* The root supervision scope (§32.2.3).  Wrap main so that on EVERY exit
   * (normal, failure, interrupt) it shuts the root scope down — interrupting and
   * awaiting any root-level forked children before main terminates — instead of
   * abandoning them when the workers are joined.  With no root children the
   * shutdown is a no-op, so the common case is unaffected. */
  Scope *root = krt2i_scope_new();
  KValue *root_h = kfgn(root, KRT2_KIND_SCOPE);
  /* fix 6 (R2): a fresh daemon supervision scope for THIS run.  forkDaemon children
   * attach here (krt2i_spawn_from) so the run boundary can reap them, instead of
   * leaving a parked daemon pinned in rt->all across persistent runs.
   *
   * fix 1 (regression): main's in-fiber wrapper shuts down ONLY the root scope —
   * §32.2.3 awaits attached STRUCTURED children at scope close, and that await is
   * sound because they ARE interruptible-and-awaited.  The daemon scope is NOT
   * awaited here: §32.2.3 does not await unattached daemons, and a daemon parked
   * inside `uninterruptible` never delivers the ScopeShutdown interrupt, so an
   * in-fiber `shutdownScope(daemonScope)` (which blocks on live==0) would hang
   * run_main forever.  Daemons are instead torn down best-effort + BOUNDED on the
   * host thread after main_done (krt2i_scope_drain_bounded below). */
  Scope *daemons = krt2i_scope_new();
  KValue *wrapped = krt2_ensuring(action, krt2_shutdown_scope(root_h));

  krc_mark_shared_recursive(wrapped);
  Fiber *m = fiber_new(rt, wrapped);
  m->cur_scope = root;

  /* Per-run state.  The persistent pool/loop and rt->all (which may still hold a
   * handful of just-finished bookkeeping fibers being GC-reclaimed) are LEFT
   * INTACT; only the main-fiber completion latch is reset for this run. */
  pthread_mutex_lock(&rt->done_lock);
  rt->main_done = 0;
  /* fix 5: release-store so fiber_finish's acquire-load (outside done_lock) sees a
   * fully-published pointer; done_lock alone does not order that lock-free read. */
  atomic_store_explicit(&rt->main_fiber, m, memory_order_release);
  /* fix 6: publish the daemon scope BEFORE main runs, so a daemon forked during the
   * run attaches to it (acquire-read in krt2i_spawn_from).  Release-store under
   * done_lock for the same publication discipline as main_fiber. */
  atomic_store_explicit(&rt->daemon_scope, daemons, memory_order_release);
  pthread_mutex_unlock(&rt->done_lock);
  krt2i_all_add(rt, m);

  krt2i_ensure_started(rt);    /* lazily start the pool+reactor ONCE; reuse after */
  krt2i_resume(rt, m);         /* enqueue the main fiber */

  pthread_mutex_lock(&rt->done_lock);
  while (!rt->main_done) pthread_cond_wait(&rt->done_cv, &rt->done_lock);
  pthread_mutex_unlock(&rt->done_lock);

  /* fix 1 (R2 / §32.2.3): main has terminated; reap this run's daemons best-effort
   * WITHOUT awaiting them unboundedly.  Interrupt + bounded-drain this scope's
   * children.  Ordinary interruptible daemons (e.g. a parked sleepFor) deliver the
   * ScopeShutdown interrupt, run their finalizers, and leave rt->all promptly — so
   * the persistent runtime's live-fiber count stays bounded (R2).  An uninterruptible
   * daemon that never delivers is LEFT parked when the budget expires: run_main
   * RETURNS rather than hanging (the regression this fixes).  The budget is generous
   * relative to a finalizer's runtime but finite.
   *
   * fix D1 (daemon-ordering leak): keep rt->daemon_scope PUBLISHED through the drain
   * and null it only AFTER the drain returns.  Nulling it BEFORE the drain opened a
   * window: a daemon forked between main_done and the drain's `shutting` store read
   * daemon_scope==NULL in krt2i_spawn_from, took NEITHER attach branch, and was rooted
   * only in rt->all — invisible to the drain, so it leaked across persistent runs
   * (defeating R2 for that window).  With the scope still published,
   * krt2i_scope_drain_bounded sets sc->shutting=1 UNDER sc->lock FIRST; since
   * scope_attach also reads `shutting` under the SAME lock, a daemon forked in the
   * window either lands in the drain's child snapshot or is born-interrupted via the
   * `shutting` guard (and counted in `live`) — every daemon is reaped, none escapes.
   * Nulling AFTER the drain still stops a daemon forked by the NEXT run from
   * attaching to the now-dead scope. */
  krt2i_scope_drain_bounded(rt, daemons, (uint64_t)2 * 1000 * 1000 * 1000 /* 2s */);
  atomic_store_explicit(&rt->daemon_scope, NULL, memory_order_release);

  /* Do NOT shut down: the pool, reactor, loop, and rt->all stay alive for the
   * next run_main (persistence is the default; krt2_shutdown is explicit-only). */
  return m->exit;
}

/* Explicit FINAL teardown (atexit / process exit).  NOT called per run_main —
 * persistence is the default (see krt2_run_main).  This sets `shutting_down` so
 * rq_pop returns NULL and the worker pool drains, joins the workers + reactor,
 * and clears g_rt so any later krt2_new rebuilds from scratch.  A rebuild after
 * teardown re-enters the shutdown→reinit cycle the persistent path was written
 * to avoid, so it must establish quiescence first: this teardown only runs when
 * the process is exiting (no concurrent run_main), which is the quiescence
 * barrier — a full GC + pthread_*_destroy of the never-destroyed mutexes/condvars
 * would be required before a *reinit*, but at process exit the OS reclaims them. */
void krt2_shutdown(Rt *rt) {
  if (!rt) return;
  atomic_store_explicit(&rt->shutting_down, 1, memory_order_release);
  pthread_mutex_lock(&rt->rq_lock);
  pthread_cond_broadcast(&rt->rq_cv);
  pthread_mutex_unlock(&rt->rq_lock);
  if (rt->workers_started) {
    for (int i = 0; i < rt->nworkers; i++) GC_pthread_join(rt->workers[i], NULL);
    krt2i_reactor_stop(rt);
    rt->workers_started = 0;
  }
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

/* Count fibers currently in the strong root set rt->all (every not-yet-DONE
 * fiber kept GC-live; a fiber leaves on fiber_finish -> all_remove).  Exposed so
 * a test can assert the persistent runtime does not accumulate leaked fibers
 * (e.g. parked daemons) across repeated run_main calls (fix 6 / R2). */
long krt2_live_fiber_count(void) {
  Rt *rt = g_rt;
  if (!rt) return 0;
  pthread_mutex_lock(&rt->all_lock);
  long live = 0;
  for (Fiber *f = rt->all; f; f = f->all_next) live++;
  pthread_mutex_unlock(&rt->all_lock);
  return live;
}
