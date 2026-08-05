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
#include <string.h>
#include <time.h>
#include <errno.h>

/* ── interruption (§18.1.4) ─────────────────────────────────────────────── */

/* Map an InterruptTag diagnostic name to its fixed KCT_ id (kappart.h) so a .kp
 * `match` on the tag dispatches by id.  Only the tags the runtime builds need an
 * entry; an unknown tag stays KCT_OTHER (inert — no .kp match names it). */
int krt2i_interrupt_tag_id(const char *tag) {
  if (!strcmp(tag, "Requested"))     return KCT_IT_REQUESTED;
  if (!strcmp(tag, "ScopeShutdown")) return KCT_IT_SCOPE_SHUTDOWN;
  if (!strcmp(tag, "TimedOut"))      return KCT_IT_TIMED_OUT;
  if (!strcmp(tag, "RaceLost"))      return KCT_IT_RACE_LOST;
  if (!strcmp(tag, "External"))      return KCT_IT_EXTERNAL;
  return KCT_OTHER;
}

/* Build MkInterruptCause(tag, by) — `by` is an Option FiberId (§18.1.2).  The
 * outer ctor and the inner tag carry their fixed KCT_ ids; "InterruptCause" is a
 * diagnostic name (the prelude ctor is MkInterruptCause — matching is by id). */
KValue *krt2i_interrupt_cause(const char *tag, KValue *by_opt) {
  KValue *args[2] = { kctor0(krt2i_interrupt_tag_id(tag), tag), by_opt };
  return kctor(KCT_MK_INTERRUPT_CAUSE, "InterruptCause", 2, args);
}

/* Record a pending interruption on `target` (first request wins, §18.1.12) and,
 * if it is interruptibly parked, wake it so it reaches an interruption point and
 * delivers. A fiber parked in a non-cancellable blocking native call is not
 * woken by the request; the call's completion wakes it, and the pending
 * interrupt is observed at that resume point. */
void krt2i_interrupt_request(Rt *rt, Fiber *target, KValue *cause) {
  int wake_now;
  pthread_mutex_lock(&target->lock);
  if (!atomic_load(&target->interrupt_pending)) {
    krc_mark_shared_recursive(cause);
    target->interrupt_cause = cause;
    atomic_store_explicit(&target->interrupt_pending, 1, memory_order_release);
  }
  wake_now = !target->blocking_armed;
  pthread_mutex_unlock(&target->lock);
  /* Pair with the seq_cst fence in krt2i_claim_pending_after_park: order this
   * interrupt_pending store before the wake's F_PARKED->F_RUNNABLE CAS so a fiber
   * committing F_PARKED concurrently cannot BOTH miss our wake (CAS fails because
   * it is still F_RUNNING) AND miss our flag (it re-checks after parking).  Closes
   * the lost-interrupt / scope-drain hang (§18.1.12). */
  atomic_thread_fence(memory_order_seq_cst);
  if (wake_now) {
    krt2i_wake(rt, target, NULL); /* no-op if RUNNING/DONE; a fiber that is still
                                   * RUNNING observes the flag at its next step or
                                   * in its post-park re-check */
  }
}

/* interrupt / interruptFork.  wait=1 also parks the caller until the target has
 * terminated (and, once finalizers land, run them); wait=0 returns immediately.
 * Returns 1 if the caller may continue (result Unit placed in f->cur on the wait
 * path), 0 if the caller parked. */
int krt2i_op_interrupt(Rt *rt, Fiber *f, KValue *target_h, KValue *cause, int wait) {
  Fiber *target = (Fiber *)kas_fgn_kind(target_h, KRT2_KIND_FIBER);
  krt2i_interrupt_request(rt, target, cause);
  if (!wait) return 1;
  int dp = krt2i_deliver_pending_before_park(rt, f);
  if (dp != 0) return dp > 0 ? 1 : 0;
  krt2i_mark_fiber_shared(f);
  pthread_mutex_lock(&target->lock);
  if (atomic_load_explicit(&target->status, memory_order_acquire) == F_DONE) {
    pthread_mutex_unlock(&target->lock);
    f->cur = krt2_pure(krt2i_unit());
    return 1;
  }
  Waiter *w = (Waiter *)GC_MALLOC(sizeof(Waiter));
  w->f = f; w->want_exit = 0; w->next = target->waiters; target->waiters = w;
  krt2i_register_park_waiter(f, KPARK_FIBER_WAITERS, target, w);
  int park_unmasked = krt2i_mask_interruptible(f);
  atomic_store(&f->status, F_PARKED);
  pthread_mutex_unlock(&target->lock);
  if (krt2i_claim_pending_after_park(f, park_unmasked)) {
    pthread_mutex_lock(&target->lock);
    krt2i_unlink_waiter(&target->waiters, w);
    pthread_mutex_unlock(&target->lock);
    krt2i_clear_park_waiter(f);
    return krt2i_deliver_claimed_interrupt(rt, f) ? 1 : 0;
  }
  return 0;
}

/* ── supervision scopes (§18.1.8, §32.2.3) ──────────────────────────────── */

Scope *krt2i_scope_new(void) {
  Scope *sc = (Scope *)GC_MALLOC(sizeof(Scope));
  pthread_mutex_init(&sc->lock, NULL);
  pthread_cond_init(&sc->drain_cv, NULL);
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
  if (now == 0 && atomic_load(&sc->shutting)) {
    w = sc->drain_waiters; sc->drain_waiters = NULL;
    /* fix 1 (R2): wake a host thread bounded-draining this scope (run_main on the
     * daemon scope).  Signal UNDER the lock so the timedwait, which reacquires the
     * lock to recheck live, cannot miss the transition to 0. */
    pthread_cond_broadcast(&sc->drain_cv);
  }
  pthread_mutex_unlock(&sc->lock);
  child->att_scope = NULL; child->att_link = NULL;
  for (; w; w = w->next) krt2i_wake(rt, w->f, krt2_pure(krt2i_unit()));
}

KValue *krt2i_op_fork_in(Rt *rt, Fiber *parent, KValue *scope_h, KValue *action) {
  Scope *sc = (Scope *)kas_fgn_kind(scope_h, KRT2_KIND_SCOPE);
  /* §18.1.7: a forkIn child also inherits the parent's FiberRef snapshot. */
  return kfgn(krt2i_spawn_from(rt, parent, action, sc, 0), KRT2_KIND_FIBER);
}

/* shutdownScope: mark the scope draining, interrupt every still-live child with
 * tag ScopeShutdown, and park the caller until the last child has terminated
 * (its finalizers run before detach, §32.2.3).  Idempotent: a re-issue with no
 * live children returns immediately.  Returns 1 (continue, Unit in f->cur) when
 * already drained, 0 when the caller parked. */
int krt2i_op_shutdown_scope(Rt *rt, Fiber *f, KValue *scope_h) {
  Scope *sc = (Scope *)kas_fgn_kind(scope_h, KRT2_KIND_SCOPE);

  krt2i_mark_fiber_shared(f);
  pthread_mutex_lock(&sc->lock);
  atomic_store(&sc->shutting, 1);
  int n = 0;
  for (ScopeLink *l = sc->children; l; l = l->next) n++;
  Fiber **kids = n ? (Fiber **)GC_MALLOC(sizeof(Fiber *) * n) : NULL;
  int i = 0;
  for (ScopeLink *l = sc->children; l; l = l->next) kids[i++] = l->f;
  int parked = 0;
  int park_unmasked = 0;
  Waiter *w = NULL;
  if (atomic_load(&sc->live) > 0) {
    w = (Waiter *)GC_MALLOC(sizeof(Waiter));
    w->f = f; w->want_exit = 0; w->next = sc->drain_waiters; sc->drain_waiters = w;
    krt2i_register_park_waiter(f, KPARK_SCOPE_DRAIN, sc, w);
    park_unmasked = krt2i_mask_interruptible(f);
    atomic_store(&f->status, F_PARKED);
    parked = 1;
  }
  pthread_mutex_unlock(&sc->lock);

  /* interrupt children outside sc->lock (no nested lock with target->lock) */
  KValue *cause = krt2i_interrupt_cause("ScopeShutdown", krt2i_some(kint((int64_t)f->id)));
  for (i = 0; i < n; i++) krt2i_interrupt_request(rt, kids[i], cause);

  if (parked) {
    if (krt2i_claim_pending_after_park(f, park_unmasked)) {
      pthread_mutex_lock(&sc->lock);
      krt2i_unlink_waiter(&sc->drain_waiters, w);
      pthread_mutex_unlock(&sc->lock);
      krt2i_clear_park_waiter(f);
      return krt2i_deliver_claimed_interrupt(rt, f) ? 1 : 0;
    }
    return 0;                 /* a detach will wake us when live hits 0       */
  }
  f->cur = krt2_pure(krt2i_unit());
  return 1;
}

/* fix 1 (R2 / §32.2.3): best-effort daemon-scope teardown at the run boundary.
 *
 * The §1 persistent runtime keeps rt->all (the strong GC root set) alive across
 * run_main calls, so a daemon that PARKS must still be reaped at the run boundary
 * or it pins one fiber + Cont chain forever (review finding R2).  An earlier fix
 * wrapped main with `shutdownScope(daemonScope)`, but shutdownScope AWAITS live==0
 * — and a daemon parked inside `uninterruptible` never receives the ScopeShutdown
 * interrupt (a non-interruptible effective mask suppresses delivery), so live
 * never reaches 0 and the
 * await HANGS run_main forever.  §32.2.3 only awaits *attached structured* children
 * at scope close; unattached daemons are NOT awaited.  So this teardown is purely
 * best-effort: interrupt every daemon (ordinary INTERRUPTIBLE ones then wake, deliver,
 * run finalizers, and leave rt->all via fiber_finish), but BOUND the wait — an
 * uninterruptible daemon that never delivers is left parked (leak-and-return) rather
 * than hanging the run.
 *
 * Runs on the run_main HOST thread (not a fiber), so it parks on a plain condvar
 * (sc->drain_cv) with an absolute-deadline timedwait rather than the fiber waiter
 * machinery.  scope_detach broadcasts drain_cv when live hits 0 under a draining
 * scope, so the common case (all daemons interruptible) wakes promptly and exact. */
void krt2i_scope_drain_bounded(Rt *rt, Scope *sc, uint64_t budget_ns) {
  /* Mark draining and snapshot the live children under the lock, then interrupt each
   * outside the lock (no nested lock with target->lock — same discipline as
   * krt2i_op_shutdown_scope).  The `shutting` store and the child snapshot happen
   * under the SAME sc->lock that scope_attach takes to read `shutting`, so this point
   * is the linearization barrier for daemons forked in the run-boundary window: a
   * daemon that attached BEFORE we snapshot is in `kids` and interrupted below; one
   * that attaches AFTER observes `shutting==1` and is born-interrupted by scope_attach
   * (and is counted in `live`, so the bounded wait neither returns early nor hangs).
   * This relies on run_main keeping rt->daemon_scope PUBLISHED across this call (fix
   * D1) — a daemon forked while the scope was already nulled would take neither attach
   * branch in krt2i_spawn_from and escape the drain entirely (the leak D1 closes). */
  pthread_mutex_lock(&sc->lock);
  atomic_store(&sc->shutting, 1);
  int n = 0;
  for (ScopeLink *l = sc->children; l; l = l->next) n++;
  Fiber **kids = n ? (Fiber **)GC_MALLOC(sizeof(Fiber *) * n) : NULL;
  int i = 0;
  for (ScopeLink *l = sc->children; l; l = l->next) kids[i++] = l->f;
  pthread_mutex_unlock(&sc->lock);

  KValue *cause = krt2i_interrupt_cause("ScopeShutdown", krt2i_none());
  for (i = 0; i < n; i++) krt2i_interrupt_request(rt, kids[i], cause);

  if (n == 0) return;        /* nothing forked this run: no wait, no leak */

  /* Bounded wait for live to reach 0 (interruptible daemons reaping themselves).
   * Absolute deadline so spurious/partial wakeups re-wait against the SAME budget
   * (a fresh relative timeout each iteration could extend the wait unboundedly). */
  struct timespec deadline;
  clock_gettime(CLOCK_REALTIME, &deadline);
  uint64_t ns = (uint64_t)deadline.tv_nsec + budget_ns;
  deadline.tv_sec += (time_t)(ns / 1000000000ull);
  deadline.tv_nsec = (long)(ns % 1000000000ull);

  pthread_mutex_lock(&sc->lock);
  while (atomic_load(&sc->live) > 0) {
    int rc = pthread_cond_timedwait(&sc->drain_cv, &sc->lock, &deadline);
    if (rc == ETIMEDOUT) break;   /* leak-and-return: an uninterruptible daemon
                                   * never delivered; do NOT hang the run */
  }
  pthread_mutex_unlock(&sc->lock);
}

/* ── monitors (§18.1.8) ─────────────────────────────────────────────────── */

KValue *krt2i_op_monitor(KValue *fiber_h) {
  Monitor *m = (Monitor *)GC_MALLOC(sizeof(Monitor));
  m->target = (Fiber *)kas_fgn_kind(fiber_h, KRT2_KIND_FIBER);
  return kfgn(m, KRT2_KIND_MONITOR);
}

int krt2i_op_await_monitor(Rt *rt, Fiber *f, KValue *mon_h) {
  (void)rt;
  Monitor *m = (Monitor *)kas_fgn_kind(mon_h, KRT2_KIND_MONITOR);
  Fiber *t = m->target;
  int dp = krt2i_deliver_pending_before_park(rt, f);
  if (dp != 0) return dp > 0 ? 1 : 0;
  krt2i_mark_fiber_shared(f);
  pthread_mutex_lock(&t->lock);
  if (atomic_load_explicit(&t->status, memory_order_acquire) == F_DONE) {
    KValue *ex = t->exit;
    pthread_mutex_unlock(&t->lock);
    f->cur = krt2_pure(kdup(ex));
    return 1;
  }
  Waiter *w = (Waiter *)GC_MALLOC(sizeof(Waiter));
  w->f = f; w->want_exit = 1; w->next = t->waiters; t->waiters = w;  /* observe Exit */
  krt2i_register_park_waiter(f, KPARK_FIBER_WAITERS, t, w);
  int park_unmasked = krt2i_mask_interruptible(f);
  atomic_store(&f->status, F_PARKED);
  pthread_mutex_unlock(&t->lock);
  if (krt2i_claim_pending_after_park(f, park_unmasked)) {
    pthread_mutex_lock(&t->lock);
    krt2i_unlink_waiter(&t->waiters, w);
    pthread_mutex_unlock(&t->lock);
    krt2i_clear_park_waiter(f);
    return krt2i_deliver_claimed_interrupt(rt, f) ? 1 : 0;
  }
  return 0;
}
