/* reactor_shutdown_timers.c — fix S3: a clean shutdown (krt2_shutdown ->
 * krt2i_reactor_stop) must uv_close any STILL-ARMED sleep timer, so uv_loop_close
 * sees no open handle and the SleepTimer is freed.
 *
 * THE BUG (pre-fix): reactor_async_cb on reactor_stop uv_close'd only the async
 * handle and uv_stop'd the loop, ABANDONING still-armed SleepTimers un-closed.
 * uv_loop_close then saw open handles (UV_EBUSY) and each SleepTimer leaked.  The
 * symptom only surfaces at a clean shutdown that races an armed timer — e.g. an
 * uninterruptible daemon still parked on sleepFor when the runtime shuts down.
 *
 * THE FIX: on reactor_stop, uv_walk closes EVERY remaining handle (timers via
 * sleep_close_cb, the embedded async with no cb); uv_run drains the close callbacks
 * and returns on its own; uv_loop_close then closes cleanly.
 *
 * THE TEST: fork an uninterruptible daemon parked on a one-hour sleepFor — its
 * timer is armed and cannot be interrupt-cancelled (effective state Uninterruptible).  run_main returns
 * (the bounded daemon drain leaves it parked).  THEN krt2_shutdown -> reactor_stop
 * -> the walk closes the armed timer.  The live-SleepTimer counter must be 0.
 *   PASS (fixed):   krt2_live_sleep_timers() == 0  (the armed timer was closed)
 *   FAIL (pre-fix): >= 1                            (the daemon's timer leaked)
 *
 * A watchdog turns any shutdown hang into a hard failure.
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <gc.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdatomic.h>
#include <pthread.h>
#include <time.h>

extern int krt2_live_sleep_timers(void);   /* reactor.c — armed-timer accounting */

static int fails = 0;
#define CHECK(c, m) do { if (!(c)) { fprintf(stderr, "  FAIL: %s\n", m); fails++; } } while (0)

#define HOUR_NANOS ((int64_t)3600 * 1000 * 1000 * 1000)

/* the daemon: uninterruptible(sleepFor 1h ; pure 0).  Masked throughout, so the
 * run-boundary ScopeShutdown interrupt cannot reap it — it stays parked on an armed
 * sleep timer, which is exactly the handle the shutdown walk must close. */
static KValue *daemon_body(void) {
  KValue *inner = krt2_then(krt2_sleep_for(kint(HOUR_NANOS)), krt2_pure(kint(0)));
  return krt2_uninterruptible(inner);
}
static KValue *after_fork(KEnv *e, KValue *d) { (void)e; (void)d; return krt2_pure(kint(1)); }
static KValue *prog(void) {
  return krt2_bind(krt2_fork_daemon(daemon_body()), kclo(after_fork, NULL));
}

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
      fprintf(stderr, "  FAIL: reactor_shutdown_timers HUNG (>%ds)\n", WATCHDOG_SECS);
      fprintf(stderr, "FAIL: reactor_shutdown_timers (hang)\n");
      abort();
    }
    struct timespec s = { 0, 50 * 1000 * 1000 };
    nanosleep(&s, NULL);
  }
}

int main(void) {
  /* 2 workers: the daemon parks in the reactor while main runs on a worker. */
  krt2_new(2);

  pthread_t wd;
  pthread_create(&wd, NULL, watchdog, NULL);

  KValue *ex = krt2_run_main(prog());
  CHECK(krt2_exit_is_success(ex), "run_main returned and main succeeded");

  /* the daemon's sleep timer is armed here (leaked-and-returned by the bounded
   * drain).  A clean shutdown must walk-close it — pre-fix it leaks. */
  krt2_shutdown(krt2_current());

  atomic_store(&g_done, 1);
  pthread_join(wd, NULL);

  int live = krt2_live_sleep_timers();
  fprintf(stderr, "  reactor_shutdown_timers: live SleepTimers after shutdown = %d (expect 0)\n", live);
  CHECK(live == 0, "the still-armed sleep timer was uv_closed on shutdown (no SleepTimer leak, no UV_EBUSY)");

  if (fails == 0) {
    fprintf(stderr, "PASS: reactor_shutdown_timers (shutdown uv_closes still-armed sleep "
                    "timers; no leak, clean uv_loop_close)\n");
    return 0;
  }
  fprintf(stderr, "FAIL: reactor_shutdown_timers (%d checks failed)\n", fails);
  return 1;
}
