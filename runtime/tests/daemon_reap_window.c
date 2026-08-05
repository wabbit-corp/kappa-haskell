/* daemon_reap_window.c — fix D1 (daemon-ordering leak at the run boundary).
 *
 * THE BUG: krt2_run_main nulled rt->daemon_scope BEFORE calling
 * krt2i_scope_drain_bounded.  A daemon forked DURING the drain window (after
 * main_done, before the drain finished) read daemon_scope==NULL in
 * krt2i_spawn_from, so the `else if (daemon && dscope)` branch was false: the
 * daemon attached to NO scope and was rooted only in rt->all.  The drain
 * snapshots/awaits only the daemon SCOPE's children, so this daemon was
 * invisible to the drain — it leaked across persistent runs, defeating R2 for
 * exactly that window.
 *
 * THE FIX: keep rt->daemon_scope PUBLISHED through the drain; the drain sets
 * sc->shutting=1 under sc->lock FIRST, so a daemon forked in the window either
 * lands in the drain's child snapshot or is born-interrupted via the `shutting`
 * guard (scope_attach reads `shutting` under the same lock) — and is counted in
 * `live`, so the bounded wait reaps it.  daemon_scope is nulled only AFTER the
 * drain returns.
 *
 * HITTING THE WINDOW DETERMINISTICALLY: main forks a daemon A that parks forever
 * (one-hour sleep).  At the run boundary the drain interrupts A; A's `ensuring`
 * finalizer — which runs on a worker, CONCURRENTLY with the host-thread drain
 * still waiting on live==0 — forks a NEW daemon B (another forever-sleeper).  B
 * is therefore forked DURING the drain.  With the fix B attaches to the still-
 * published daemon scope, is born-interrupted, and is reaped before the drain
 * returns.  A finalizer runs Masked and B inherits that state as its base under
 * Spec §§18.1.12/32.2.5, so B explicitly polls before parking; ordinary sleep
 * cannot puncture the inherited mask.  WITHOUT the publication fix B reads
 * daemon_scope==NULL, attaches to nothing, and leaks — one extra fiber pinned in
 * rt->all per run.
 *
 * The test runs run_main many times and asserts the live-fiber count stays
 * bounded (does NOT grow ~linearly with the run count).  Before the fix it grows
 * by (at least) one leaked B per run.  A watchdog turns a hang into a hard fail.
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <gc.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdatomic.h>
#include <pthread.h>
#include <time.h>

static int fails = 0;
#define CHECK(c, m) do { if (!(c)) { fprintf(stderr, "  FAIL: %s\n", m); fails++; } } while (0)

#define NRUNS 40
#define HOUR_NANOS ((int64_t)3600 * 1000 * 1000 * 1000)

/* a body that parks "forever" (one-hour sleep): only an interrupt ends it. */
static KValue *forever_sleep(void) {
  return krt2_then(krt2_sleep_for(kint(HOUR_NANOS)), krt2_pure(kint(0)));
}

/* The inner daemon B is forked from A's masked finalizer.  Child fibers inherit
 * the parent's effective state as a non-restorable base state, so B must opt in
 * to delivery with poll before it parks.  There is no further fork, hence the
 * cascade still stops at one extra fiber. */
static KValue *daemon_b_body(void) {
  return krt2_then(krt2_poll(), forever_sleep());
}

/* A's finalizer: forkDaemon(B), then unit.  This runs while the run-boundary
 * drain is in progress (A is being interrupted), so B is forked in the window.
 * We discard the fiber handle (daemon: nobody awaits it). */
static KValue *fin_after_fork(KEnv *e, KValue *d) { (void)e; (void)d; return krt2_pure(kunit()); }
static KValue *finalizer_body(void) {
  return krt2_bind(krt2_fork_daemon(daemon_b_body()), kclo(fin_after_fork, NULL));
}

/* daemon A: ensuring(forever-sleep, finalizer_body).  When the drain interrupts
 * the sleep, the finalizer runs and forks B during the drain. */
static KValue *daemon_a_body(void) {
  return krt2_ensuring(forever_sleep(), finalizer_body());
}

static KValue *after_fork(KEnv *e, KValue *d) { (void)e; (void)d; return krt2_pure(kint(1)); }
static KValue *prog(void) {
  return krt2_bind(krt2_fork_daemon(daemon_a_body()), kclo(after_fork, NULL));
}

/* Watchdog: if a run hangs (a regression in the drain accounting — e.g. B is
 * counted in `live` but never reaped), abort so the test FAILS loudly. */
static _Atomic int g_done = 0;
#define WATCHDOG_SECS 60
static void *watchdog(void *arg) {
  (void)arg;
  struct timespec start, now;
  clock_gettime(CLOCK_MONOTONIC, &start);
  for (;;) {
    if (atomic_load(&g_done)) return NULL;
    clock_gettime(CLOCK_MONOTONIC, &now);
    if (now.tv_sec - start.tv_sec >= WATCHDOG_SECS) {
      fprintf(stderr, "  FAIL: run_main HUNG (>%ds) — a daemon forked during the "
                      "drain window was counted but never reaped\n", WATCHDOG_SECS);
      fprintf(stderr, "FAIL: daemon_reap_window (hang)\n");
      abort();
    }
    struct timespec s = { 0, 50 * 1000 * 1000 }; /* 50ms poll */
    nanosleep(&s, NULL);
  }
}

int main(void) {
  /* 2 workers: A parks in the reactor while main runs; the run-boundary drain
   * interrupts A, A's finalizer forks B on a worker concurrently with the drain. */
  krt2_new(2);

  pthread_t wd;
  pthread_create(&wd, NULL, watchdog, NULL);

  long baseline = -1;
  long max_live = 0;
  for (int i = 0; i < NRUNS; i++) {
    KValue *ex = krt2_run_main(prog());
    if (!krt2_exit_is_success(ex)) { fails++; fprintf(stderr, "  FAIL: run %d not Success\n", i); break; }
    long live = krt2_live_fiber_count();
    if (i == 2) baseline = live;          /* steady state after warmup */
    if (live > max_live) max_live = live;
    if ((i & 7) == 0) GC_gcollect();      /* reclaim finished-fiber bookkeeping */
  }

  atomic_store(&g_done, 1);
  pthread_join(wd, NULL);

  /* The decisive assertion: the live-fiber count does NOT grow ~linearly with the
   * run count.  Before the fix the window-forked daemon B leaks once per run, so
   * the count reaches >= NRUNS; after the fix it stays a small constant. */
  long final_live = krt2_live_fiber_count();
  fprintf(stderr, "  daemon_reap_window: baseline=%ld max=%ld final=%ld over %d runs\n",
          baseline, max_live, final_live, NRUNS);
  CHECK(final_live < NRUNS / 2,
        "live-fiber count did NOT grow per-run (window-forked daemons reaped)");
  CHECK(max_live < NRUNS / 2,
        "live-fiber count stayed bounded across ALL runs (no window-daemon accumulation)");

  if (fails == 0) {
    fprintf(stderr, "PASS: daemon_reap_window (daemon forked DURING the run-boundary drain "
                    "is attached + reaped; rt->all bounded across persistent runs)\n");
    return 0;
  }
  fprintf(stderr, "FAIL: daemon_reap_window (%d checks failed)\n", fails);
  return 1;
}
