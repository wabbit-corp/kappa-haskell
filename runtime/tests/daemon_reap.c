/* daemon_reap.c — §18 forkDaemon + the §1 persistent runtime (review finding R2;
 * fix 6).  A daemon is unattached to ordinary structured scopes, so the root-scope
 * shutdown wrapper never interrupted it.  Combined with the persistent runtime
 * (workers + rt->all survive across run_main), a daemon that PARKS forever (long
 * sleep / forever / blocked await) never reached fiber_finish -> all_remove, so it
 * stayed pinned in rt->all — which is reachable from the static g_rt Boehm root.
 * Each persistent run that forked a lingering daemon therefore leaked one fiber +
 * its Cont chain, growing rt->all without bound.
 *
 * After the fix, each run_main installs a per-run daemon supervision scope; daemons
 * attach to it; main's wrapper shuts it down (interrupt + await) on exit.  A parked
 * daemon is interrupted at the run boundary, runs its finalizers, and is removed
 * from rt->all — so the live-fiber count does NOT grow across runs.
 *
 * The test forks a daemon that sleeps for an hour (so it is genuinely parked in the
 * reactor, only terminable via interruption), runs run_main many times, and asserts
 * the live-fiber count after each run stays bounded.  Before the fix it grows by
 * (at least) one per run; after the fix it is flat.
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <gc.h>
#include <stdio.h>
#include <stdatomic.h>

static int fails = 0;
#define CHECK(c, m) do { if (!(c)) { fprintf(stderr, "  FAIL: %s\n", m); fails++; } } while (0)

#define NRUNS 40
#define HOUR_NANOS ((int64_t)3600 * 1000 * 1000 * 1000)

/* a daemon that parks "forever" (one-hour sleep): only an interrupt ends it. */
static KValue *daemon_body(void) {
  return krt2_then(krt2_sleep_for(kint(HOUR_NANOS)), krt2_pure(kint(0)));
}
/* main: forkDaemon(sleeper); then return a value (main does NOT await the daemon —
 * that is the whole point of a daemon).  With the fix, the run-boundary daemon-scope
 * shutdown interrupts + awaits it before run_main returns. */
static KValue *after_fork(KEnv *e, KValue *d) { (void)e; (void)d; return krt2_pure(kint(1)); }
static KValue *prog(void) {
  return krt2_bind(krt2_fork_daemon(daemon_body()), kclo(after_fork, NULL));
}

int main(void) {
  /* 2 workers: the daemon parks in the reactor while main runs on a worker; the
   * run-boundary shutdown must interrupt the parked daemon across that boundary. */
  krt2_new(2);

  long baseline = -1;
  long max_live = 0;
  for (int i = 0; i < NRUNS; i++) {
    KValue *ex = krt2_run_main(prog());
    if (!krt2_exit_is_success(ex)) { fails++; fprintf(stderr, "  FAIL: run %d not Success\n", i); break; }
    /* after run i the daemon must have been reaped: live count is the steady-state
     * bookkeeping (a few just-finished fibers awaiting GC), NOT growing by one per
     * run.  Record the value once it settles (after a couple of warmup runs). */
    long live = krt2_live_fiber_count();
    if (i == 2) baseline = live;          /* steady state after warmup */
    if (live > max_live) max_live = live;
    if ((i & 7) == 0) GC_gcollect();      /* reclaim finished-fiber bookkeeping */
  }

  /* The decisive assertion: the live-fiber count does NOT grow ~linearly with the
   * run count.  Before the fix it would be >= NRUNS (one leaked daemon per run);
   * after the fix it stays a small constant.  Use a generous bound (well under
   * NRUNS) so transient just-finished bookkeeping fibers do not flake the test. */
  long final_live = krt2_live_fiber_count();
  fprintf(stderr, "  daemon_reap: baseline=%ld max=%ld final=%ld over %d runs\n",
          baseline, max_live, final_live, NRUNS);
  CHECK(final_live < NRUNS / 2,
        "live-fiber count did NOT grow per-run (parked daemons reaped at run boundary)");
  CHECK(max_live < NRUNS / 2,
        "live-fiber count stayed bounded across ALL runs (no daemon accumulation)");

  if (fails == 0) {
    fprintf(stderr, "PASS: daemon_reap (parked daemons reaped per run; rt->all bounded across persistent runs)\n");
    return 0;
  }
  fprintf(stderr, "FAIL: daemon_reap (%d checks failed)\n", fails);
  return 1;
}
