/* sleep_orphan_timer.c — fix S2 (orphan sleep-timer after a masked re-park).
 *
 * THE BUG: a fiber parked on `sleepFor` is woken by an interrupt while MASKED
 * (uninterruptible).  The interrupt cannot be delivered in that effective state, so the
 * fiber re-runs OP_SLEEP and re-arms a FRESH uv_timer — but the ORIGINAL timer
 * was never cancelled.  That orphan timer fires later and calls
 * krt2i_wake(f, pure(Unit)); if the fiber has since parked on an UNRELATED
 * operation, the wake CAS-wins that park and clobbers f->cur with a bogus Unit —
 * a SPURIOUS resume of a park that was waiting for something else entirely.
 *
 * THE FIX: a masked-sleep abandonment routes a cancel of the original timer to
 * the reactor (krt2i_cancel_sleep) before the re-arm; the re-arm starts a fresh
 * FULL-duration timer (matching the interpreter's masked re-park).  So no orphan
 * timer survives to spuriously resume a later park.
 *
 * THE TEST (single worker, deterministic ordering by sleeps):
 *   Fiber A:  uninterruptible( sleepFor D        -- masked sleep, parks on timer1
 *                            ; awaitPromiseExit(gate)  -- a LATER, independent park
 *                            ; record the await's Exit payload )
 *             ; complete(done)
 *   Main:     fork A
 *             ; sleep S  (< D)                    -- let A park on the masked sleep
 *             ; interruptFork(A)                  -- masked => A re-parks; pre-fix
 *                                                    this orphans timer1
 *             ; sleep W  (>> D)                   -- long enough that the orphan
 *                                                    timer WOULD fire AND A would
 *                                                    reach + spuriously-resume the
 *                                                    await
 *             ; complete(gate, Success 777)       -- the ONLY legitimate resume
 *             ; awaitPromiseExit(done)
 *
 * The WHOLE of A is `uninterruptible`, so the interrupt that wakes the masked
 * sleep is never DELIVERED (effective state Uninterruptible throughout) — it only triggers the
 * masked re-park.  A therefore survives to reach the LATER await, which is the
 * independent park the orphan timer can clobber.  (A simple `catch` cannot absorb
 * an Interrupt — interrupts skip KK_CATCH and terminate the fiber — so masking the
 * whole body is the way to keep A alive past the interrupt.)
 *
 *   PASS (fixed):   A's await payload == 777 (only `gate` resumed it).
 *   FAIL (pre-fix): A's await payload == Unit/other (the orphan timer resumed the
 *                   masked sleep early AND/OR the re-park timer resumed the await
 *                   before main completed `gate`).
 *
 * A watchdog turns any hang into a hard failure.
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

#define MS (1000000LL)
#define D_NANOS  (40 * MS)    /* the masked sleep duration                     */
#define S_NANOS  (10 * MS)    /* main waits this before interrupting A          */
#define W_NANOS  (250 * MS)   /* main waits this (>> D) before completing gate   */
#define SENTINEL 777

/* shared (set by A's continuation, read by main after `done`) */
static _Atomic long g_await_payload = -1;   /* -1 = unset, 777 = gate, 0 = Unit/other */

static KValue *gate_h;   /* the promise A awaits AFTER its masked sleep */
static KValue *done_h;   /* A completes this last so main can join      */

/* A's continuation after awaitPromiseExit(gate): classify the resume value.
 * Runs INSIDE the uninterruptible region, so a still-pending interrupt is not
 * delivered here. */
static KValue *a_after_await(KEnv *e, KValue *exitv) {
  (void)e;
  long payload = 0;  /* default: Unit / unexpected (the orphan-timer spurious resume) */
  if (kctor_is(exitv, "Success") && kctor_argc(exitv) == 1) {
    payload = (long)kas_int(kctor_arg(exitv, 0));
  }
  atomic_store(&g_await_payload, payload);
  return krt2_pure(kunit());
}

/* A's body: uninterruptible( sleepFor D ; awaitPromiseExit(gate) ; classify )
 * ; complete(done).  The whole sleep+await is masked so the interrupt only
 * triggers the masked re-park, never a delivery — A survives to the await. */
static KValue *a_body(void) {
  KValue *inner = krt2_then(krt2_sleep_for(kint(D_NANOS)),
                            krt2_bind(krt2_await_promise_exit(gate_h), kclo(a_after_await, NULL)));
  return krt2_then(krt2_uninterruptible(inner),
                   krt2_then(krt2_complete_promise(done_h, krt2_success(kunit())),
                             krt2_pure(kunit())));
}

/* main, after forking A (handle in `fA`): sleep S, interrupt A (no wait — A is
 * masked so it re-parks), sleep W, complete gate(777), await done. */
static KValue *k_after_fork(KEnv *e, KValue *fA) {
  (void)e;
  return krt2_then(krt2_sleep_for(kint(S_NANOS)),
         krt2_then(krt2_interrupt_fork(fA),
         krt2_then(krt2_sleep_for(kint(W_NANOS)),
         krt2_then(krt2_complete_promise(gate_h, krt2_success(kint(SENTINEL))),
         krt2_then(krt2_await_promise_exit(done_h),
                   krt2_pure(kunit()))))));
}

/* program: make the two promises, then fork A and run the main sequence. */
static KValue *k_done(KEnv *e, KValue *d) { (void)e; done_h = d; return krt2_bind(krt2_fork(a_body()), kclo(k_after_fork, NULL)); }
static KValue *k_gate(KEnv *e, KValue *g) { (void)e; gate_h = g; return krt2_bind(krt2_new_promise(), kclo(k_done, NULL)); }
static KValue *program(void) {
  return krt2_bind(krt2_new_promise(), kclo(k_gate, NULL));
}

static _Atomic int g_done_flag = 0;
#define WATCHDOG_SECS 30
static void *watchdog(void *arg) {
  (void)arg;
  struct timespec start, now;
  clock_gettime(CLOCK_MONOTONIC, &start);
  for (;;) {
    if (atomic_load(&g_done_flag)) return NULL;
    clock_gettime(CLOCK_MONOTONIC, &now);
    if (now.tv_sec - start.tv_sec >= WATCHDOG_SECS) {
      fprintf(stderr, "  FAIL: sleep_orphan_timer HUNG (>%ds)\n", WATCHDOG_SECS);
      fprintf(stderr, "FAIL: sleep_orphan_timer (hang)\n");
      abort();
    }
    struct timespec s = { 0, 50 * 1000 * 1000 };
    nanosleep(&s, NULL);
  }
}

int main(void) {
  /* 1 worker: deterministic — A parks in the reactor, main runs the sequence. */
  krt2_new(1);

  pthread_t wd;
  pthread_create(&wd, NULL, watchdog, NULL);

  KValue *ex = krt2_run_main(program());

  atomic_store(&g_done_flag, 1);
  pthread_join(wd, NULL);

  CHECK(krt2_exit_is_success(ex), "run_main succeeded");
  long payload = atomic_load(&g_await_payload);
  fprintf(stderr, "  sleep_orphan_timer: await payload = %ld (expect %d)\n", payload, SENTINEL);
  CHECK(payload == SENTINEL,
        "A's later await was resumed ONLY by the gate completion (no orphan-timer spurious resume)");

  if (fails == 0) {
    fprintf(stderr, "PASS: sleep_orphan_timer (masked-sleep re-park cancels the original "
                    "timer; no spurious resume of a later independent park)\n");
    return 0;
  }
  fprintf(stderr, "FAIL: sleep_orphan_timer (%d checks failed)\n", fails);
  return 1;
}
