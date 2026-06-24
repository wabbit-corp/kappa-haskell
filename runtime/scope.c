/* scope.c — structured concurrency, interruption, and monitors (§18.1.8,
 * §18.1.4, §32.2.3).  The CK-machine (rt.c) dispatches the scheduler opcodes to
 * the krt2i_op_* handlers here; rt.c owns fiber spawn/finish and calls
 * krt2i_scope_attach / krt2i_scope_detach.
 *
 * Concurrency discipline (REVIEW.md B3/B4): a fiber that blocks (shutdownScope
 * waiting for children, interrupt-wait, awaitMonitor) check-and-enqueues itself
 * onto a waiter list UNDER the relevant object's lock; the waker (a child's
 * fiber_finish -> scope_detach, or a target's fiber_finish) snapshots-and-wakes
 * UNDER the same lock via the idempotent CAS krt2i_wake.  Child interruption is
 * issued OUTSIDE the scope lock (snapshot under the lock, interrupt after
 * release) so the only nested lock order is none — no inversion with the
 * target/fiber locks taken by krt2i_interrupt_request. */
#include "internal.h"

#include <gc.h>

/* ── interruption (§18.1.4) ─────────────────────────────────────────────── */

/* Build InterruptCause(tag, by) — `by` is an Option FiberId (§18.1.2). */
KValue *krt2i_interrupt_cause(const char *tag, KValue *by_opt) {
  KValue *args[2] = { kctor0(KRT2_RESULT_ID, tag), by_opt };
  return kctor(KRT2_RESULT_ID, "InterruptCause", 2, args);
}

/* Record a pending interruption on `target` (first request wins, §18.1.12) and,
 * if it is parked, wake it so it reaches an interruption point and delivers. */
void krt2i_interrupt_request(Rt *rt, Fiber *target, KValue *cause) {
  pthread_mutex_lock(&target->lock);
  if (!atomic_load(&target->interrupt_pending)) {
    target->interrupt_cause = cause;
    atomic_store_explicit(&target->interrupt_pending, 1, memory_order_release);
  }
  pthread_mutex_unlock(&target->lock);
  krt2i_wake(rt, target, NULL); /* no-op if RUNNING/DONE; the running fiber
                                 * observes the flag at its next step */
}

/* interrupt / interruptFork.  wait=1 also parks the caller until the target has
 * terminated (and, once finalizers land, run them); wait=0 returns immediately.
 * Returns 1 if the caller may continue (result Unit placed in f->cur on the wait
 * path), 0 if the caller parked. */
int krt2i_op_interrupt(Rt *rt, Fiber *f, KValue *target_h, KValue *cause, int wait) {
  Fiber *target = (Fiber *)kas_fgn(target_h);
  krt2i_interrupt_request(rt, target, cause);
  if (!wait) return 1;
  pthread_mutex_lock(&target->lock);
  if (atomic_load_explicit(&target->status, memory_order_acquire) == F_DONE) {
    pthread_mutex_unlock(&target->lock);
    f->cur = krt2_pure(krt2i_unit());
    return 1;
  }
  Waiter *w = (Waiter *)GC_MALLOC(sizeof(Waiter));
  w->f = f; w->want_exit = 0; w->next = target->waiters; target->waiters = w;
  atomic_store(&f->status, F_PARKED);
  pthread_mutex_unlock(&target->lock);
  return 0;
}

/* ── supervision scopes (§18.1.8, §32.2.3) ──────────────────────────────── */

Scope *krt2i_scope_new(void) {
  Scope *sc = (Scope *)GC_MALLOC(sizeof(Scope));
  pthread_mutex_init(&sc->lock, NULL);
  sc->children = NULL;
  atomic_store(&sc->live, 0);
  atomic_store(&sc->shutting, 0);
  sc->drain_waiters = NULL;
  return sc;
}

KValue *krt2i_op_new_scope(void) {
  return kfgn(krt2i_scope_new(), KRT2_KIND_SCOPE);
}

void krt2i_scope_attach(Rt *rt, Scope *sc, Fiber *child) {
  ScopeLink *l = (ScopeLink *)GC_MALLOC(sizeof(ScopeLink));
  l->f = child;
  pthread_mutex_lock(&sc->lock);
  /* Read `shutting` UNDER the lock, serialized with shutdownScope's snapshot:
   * either shutdown already saw this child (it is in `children` and will be
   * interrupted), or it has not run yet and we observe `shutting` here and
   * interrupt the child ourselves.  No child forked into a draining scope can
   * escape interruption (§32.2.3). */
  int shutting = atomic_load(&sc->shutting);
  l->prev = NULL; l->next = sc->children;
  if (sc->children) sc->children->prev = l;
  sc->children = l;
  atomic_fetch_add_explicit(&sc->live, 1, memory_order_relaxed);
  pthread_mutex_unlock(&sc->lock);
  child->att_scope = sc;
  child->att_link = l;
  /* A child born into an already-draining scope is interrupted immediately so
   * it terminates promptly; it is still counted in `live`, so the drain's
   * live==0 wait remains correct (it neither returns early nor waits forever). */
  if (shutting)
    krt2i_interrupt_request(rt, child,
        krt2i_interrupt_cause("ScopeShutdown", krt2i_none()));
}

/* A child has terminated: unlink it from its scope, decrement the live count,
 * and if the scope is draining and this was the last child, wake every parked
 * shutdownScope / withScope-exit waiter (§32.2.3). */
void krt2i_scope_detach(Rt *rt, Fiber *child) {
  Scope *sc = child->att_scope;
  if (!sc) return;
  pthread_mutex_lock(&sc->lock);
  ScopeLink *l = child->att_link;
  if (l) {
    if (l->prev) l->prev->next = l->next; else if (sc->children == l) sc->children = l->next;
    if (l->next) l->next->prev = l->prev;
  }
  long now = atomic_fetch_sub_explicit(&sc->live, 1, memory_order_acq_rel) - 1;
  Waiter *w = NULL;
  if (now == 0 && atomic_load(&sc->shutting)) { w = sc->drain_waiters; sc->drain_waiters = NULL; }
  pthread_mutex_unlock(&sc->lock);
  child->att_scope = NULL; child->att_link = NULL;
  for (; w; w = w->next) krt2i_wake(rt, w->f, krt2_pure(krt2i_unit()));
}

KValue *krt2i_op_fork_in(Rt *rt, KValue *scope_h, KValue *action) {
  Scope *sc = (Scope *)kas_fgn(scope_h);
  return kfgn(krt2i_spawn(rt, action, sc, 0), KRT2_KIND_FIBER);
}

/* shutdownScope: mark the scope draining, interrupt every still-live child with
 * tag ScopeShutdown, and park the caller until the last child has terminated
 * (its finalizers run before detach, §32.2.3).  Idempotent: a re-issue with no
 * live children returns immediately.  Returns 1 (continue, Unit in f->cur) when
 * already drained, 0 when the caller parked. */
int krt2i_op_shutdown_scope(Rt *rt, Fiber *f, KValue *scope_h) {
  Scope *sc = (Scope *)kas_fgn(scope_h);

  pthread_mutex_lock(&sc->lock);
  atomic_store(&sc->shutting, 1);
  int n = 0;
  for (ScopeLink *l = sc->children; l; l = l->next) n++;
  Fiber **kids = n ? (Fiber **)GC_MALLOC(sizeof(Fiber *) * n) : NULL;
  int i = 0;
  for (ScopeLink *l = sc->children; l; l = l->next) kids[i++] = l->f;
  int parked = 0;
  if (atomic_load(&sc->live) > 0) {
    Waiter *w = (Waiter *)GC_MALLOC(sizeof(Waiter));
    w->f = f; w->want_exit = 0; w->next = sc->drain_waiters; sc->drain_waiters = w;
    atomic_store(&f->status, F_PARKED);
    parked = 1;
  }
  pthread_mutex_unlock(&sc->lock);

  /* interrupt children outside sc->lock (no nested lock with target->lock) */
  KValue *cause = krt2i_interrupt_cause("ScopeShutdown", krt2i_some(kint((int64_t)f->id)));
  for (i = 0; i < n; i++) krt2i_interrupt_request(rt, kids[i], cause);

  if (parked) return 0;       /* a detach will wake us when live hits 0       */
  f->cur = krt2_pure(krt2i_unit());
  return 1;
}

/* ── monitors (§18.1.8) ─────────────────────────────────────────────────── */

KValue *krt2i_op_monitor(KValue *fiber_h) {
  Monitor *m = (Monitor *)GC_MALLOC(sizeof(Monitor));
  m->target = (Fiber *)kas_fgn(fiber_h);
  return kfgn(m, KRT2_KIND_MONITOR);
}

int krt2i_op_await_monitor(Rt *rt, Fiber *f, KValue *mon_h) {
  (void)rt;
  Monitor *m = (Monitor *)kas_fgn(mon_h);
  Fiber *t = m->target;
  pthread_mutex_lock(&t->lock);
  if (atomic_load_explicit(&t->status, memory_order_acquire) == F_DONE) {
    KValue *ex = t->exit;
    pthread_mutex_unlock(&t->lock);
    f->cur = krt2_pure(ex);
    return 1;
  }
  Waiter *w = (Waiter *)GC_MALLOC(sizeof(Waiter));
  w->f = f; w->want_exit = 1; w->next = t->waiters; t->waiters = w;  /* observe Exit */
  atomic_store(&f->status, F_PARKED);
  pthread_mutex_unlock(&t->lock);
  return 0;
}
