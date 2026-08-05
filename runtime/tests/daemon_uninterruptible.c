/* daemon_uninterruptible.c — fix 1 regression: run_main must RETURN when a daemon
 * is parked inside `uninterruptible` (§32.2.3 / §32.2.5).
 *
 * THE REGRESSION: an earlier R2 fix wrapped main with
 *   then(shutdownScope(daemonScope), shutdownScope(rootScope))
 * and force-attached every daemon to the per-run daemon scope.  shutdownScope parks
 * the caller until the scope's live==0, but a ScopeShutdown interrupt is delivered
 * only when the target's effective state is Interruptible. A daemon parked inside
 * `uninterruptible` remains Uninterruptible and never receives the shutdown interrupt, so live never reaches 0 and
 * run_main parks FOREVER.  §32.2.3 does NOT await unattached daemons at scope close.
 *
 * THE FIX: daemon teardown is best-effort + BOUNDED (krt2i_scope_drain_bounded):
 * interrupt the daemons, wait a bounded time for the interruptible ones to reap,
 * then RETURN — leaving an uninterruptible daemon parked (leak-and-return) rather
 * than hanging.  This test forks a daemon running uninterruptible(one-hour sleep)
 * and asserts run_main returns promptly.
 *
 * A watchdog thread bounds the whole run: if run_main hangs (the regression), the
 * watchdog aborts the process so the hang is a HARD failure, not a silent timeout.
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

#define HOUR_NANOS ((int64_t)3600 * 1000 * 1000 * 1000)

/* the daemon body: uninterruptible(sleepFor 1h ; pure 0).  The whole sleep is
 * masked, so the run-boundary ScopeShutdown interrupt is suppressed — this daemon
 * cannot be reaped by interruption.  run_main must still return. */
static KValue *daemon_body(void) {
  KValue *inner = krt2_then(krt2_sleep_for(kint(HOUR_NANOS)), krt2_pure(kint(0)));
  return krt2_uninterruptible(inner);
}
static KValue *after_fork(KEnv *e, KValue *d) { (void)e; (void)d; return krt2_pure(kint(1)); }
static KValue *prog(void) {
  return krt2_bind(krt2_fork_daemon(daemon_body()), kclo(after_fork, NULL));
}

/* Watchdog: if run_main has not signalled completion within WATCHDOG_SECS, the
 * run is HUNG (the regression) — abort so the test FAILS loudly instead of the
 * harness sitting forever. */
static _Atomic int g_done = 0;
#define WATCHDOG_SECS 30
static void *watchdog(void *arg) {
  (void)arg;
  struct timespec start, now;
  clock_gettime(CLOCK_MONOTONIC, &start);
  for (;;) {
    if (atomic_load(&g_done)) return NULL;
    clock_gettime(CLOCK_MONOTONIC, &now);
    if (now.tv_sec - start.tv_sec >= WATCHDOG_SECS) {
      fprintf(stderr, "  FAIL: run_main HUNG (>%ds) — a daemon parked inside "
                      "uninterruptible blocked the daemon-scope teardown\n", WATCHDOG_SECS);
      fprintf(stderr, "FAIL: daemon_uninterruptible (hang)\n");
      abort();   /* hard failure: nonzero exit, no silent hang */
    }
    struct timespec s = { 0, 50 * 1000 * 1000 }; /* 50ms poll */
    nanosleep(&s, NULL);
  }
}

int main(void) {
  /* 2 workers: the daemon parks in the reactor while main runs on a worker; the
   * run-boundary teardown must NOT block on the masked parked daemon. */
  krt2_new(2);

  pthread_t wd;
  pthread_create(&wd, NULL, watchdog, NULL);

  /* The decisive check: this call RETURNS.  Before the fix it hangs forever (the
   * watchdog would abort).  After the fix the bounded drain times out on the
   * uninterruptible daemon and run_main returns with main's Success. */
  KValue *ex = krt2_run_main(prog());
  atomic_store(&g_done, 1);
  pthread_join(wd, NULL);

  CHECK(krt2_exit_is_success(ex), "run_main returned and main succeeded (did NOT hang)");

  /* Run it a few more times to confirm the bounded-drain path is repeatable on the
   * persistent runtime (each run leaks at most its own uninterruptible daemon; the
   * point of THIS test is termination, not the leak bound — daemon_reap covers the
   * interruptible-reaping invariant). */
  for (int i = 0; i < 3; i++) {
    atomic_store(&g_done, 0);
    pthread_create(&wd, NULL, watchdog, NULL);
    KValue *ex2 = krt2_run_main(prog());
    atomic_store(&g_done, 1);
    pthread_join(wd, NULL);
    CHECK(krt2_exit_is_success(ex2), "repeat run_main returned and succeeded");
  }

  if (fails == 0) {
    fprintf(stderr, "PASS: daemon_uninterruptible (run_main returns; masked parked "
                    "daemon does not hang the run-boundary teardown)\n");
    return 0;
  }
  fprintf(stderr, "FAIL: daemon_uninterruptible (%d checks failed)\n", fails);
  return 1;
}
