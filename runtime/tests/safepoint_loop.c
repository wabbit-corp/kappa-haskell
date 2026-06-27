/* safepoint_loop.c — §32.2.6 loop-backedge safe points (fix SP).
 *
 * A long-running NON-CEDING loop (a CK-machine OP_WHILE/KK_LOOP that re-runs
 * `iterate` IN PLACE, never re-entering fiber_step from the run queue) used to
 * ignore a pending interrupt AND starve its worker: f->resumed stayed 0 across
 * iterations, so the masked-sleep delivery gate (`resumed && pending`) never
 * fired.  A tight CPU loop with no await/sleep/cede/poll ran to completion
 * ignoring an interrupt — a §32.2.6 interruption-observation + weak-fairness
 * violation.
 *
 * THE FIX: the KK_LOOP back-edge is a safe point.  It (a) flags a deliverable
 * interrupt (interrupt_pending && mask_depth==0) so the gate delivers it on the
 * next turn, and (b) spends a fairness quantum, ceding (re-enqueue behind other
 * runnables) when it runs out.  Masked suppression still holds: mask_depth>0 at
 * the back-edge does NOT deliver — the interrupt is held until the mask exits.
 *
 * TEST 1 (unmasked tight loop IS interrupted):
 *   A = while(true) { i := i+1 }            -- infinite, non-ceding, no suspension
 *   main: fork A; sleep; interrupt A; await A's Exit
 *   => A's Exit is Failure(Interrupt): the interrupt was delivered at a loop
 *      safe point, breaking the otherwise-infinite loop.  (Pre-fix: A spins
 *      forever and the watchdog aborts.)
 *
 * TEST 2 (masked tight loop is NOT interrupted mid-loop; delivered after mask):
 *   A = uninterruptible( while(i < N) { i := i+1 } ) ; record(i)
 *   main: fork A; sleep; interrupt A; await A's Exit
 *   => the masked loop runs to COMPLETION (record == N): suppression holds, the
 *      interrupt is NOT delivered mid-loop.  A then completes Success (no
 *      interruption point after the masked region, so the pending interrupt is
 *      dropped, exactly like the mask-suppress-interrupt parity case).
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

#define N_ITERS 5000000LL   /* the masked finite loop bound (well past one fairness quantum) */

/* ── shared observation ──────────────────────────────────────────────────── */
static _Atomic long g_masked_final = -1;   /* i after the masked loop (== N if it completed) */

/* ── TEST 1: infinite unmasked loop `while(true){ i := i+1 }` ─────────────── */
static KValue *t1_body_k(KEnv *env, KValue *v) {           /* i := i+1 */
  return krt2_write_ref(kvar(env, 0), kp_addInt(v, kint(1)));
}
static KValue *t1_loop(KValue *i) {
  KValue *body = krt2_bind(krt2_read_ref(i), kclo(t1_body_k, kpush(i, NULL)));
  return krt2_while(krt2_pure(kbool(1)), body);            /* while True (never exits normally) */
}
static KValue *t1_after_ref(KEnv *e, KValue *i) { (void)e; return t1_loop(i); }
static KValue *t1_A(void) {
  return krt2_bind(krt2_new_ref(kint(0)), kclo(t1_after_ref, NULL));
}

/* ── TEST 2: finite masked loop `uninterruptible(while(i<N){i:=i+1}); record` ─ */
static KValue *t2_cond_k(KEnv *env, KValue *v) { (void)env; return krt2_pure(kp_ltInt(v, kint(N_ITERS))); } /* i < N */
static KValue *t2_body_k(KEnv *env, KValue *v) { return krt2_write_ref(kvar(env, 0), kp_addInt(v, kint(1))); }
static KValue *t2_record_k(KEnv *e, KValue *v) { (void)e; atomic_store(&g_masked_final, (long)kas_int(v)); return krt2_pure(kunit()); }
static KValue *t2_after_loop(KEnv *env, KValue *u) {       /* record final i */
  (void)u;
  return krt2_bind(krt2_read_ref(kvar(env, 0)), kclo(t2_record_k, NULL));
}
static KValue *t2_after_ref(KEnv *e, KValue *i) {
  (void)e;
  KValue *cond = krt2_bind(krt2_read_ref(i), kclo(t2_cond_k, NULL));
  KValue *body = krt2_bind(krt2_read_ref(i), kclo(t2_body_k, kpush(i, NULL)));
  KValue *loop = krt2_uninterruptible(krt2_while(cond, body));
  return krt2_then(loop, kapp(kclo(t2_after_loop, kpush(i, NULL)), kunit()));
}
static KValue *t2_A(void) {
  return krt2_bind(krt2_new_ref(kint(0)), kclo(t2_after_ref, NULL));
}

/* ── driver: fork A, let it spin, interrupt it, await its Exit ────────────── */
static KValue *g_a_exit = NULL;
static KValue *drv_got_exit(KEnv *e, KValue *exitv) { (void)e; g_a_exit = exitv; return krt2_pure(kunit()); }
/* sleep so A is deep inside its loop, then interrupt (no wait), then await A's Exit. */
static KValue *drv_after_fork(KEnv *e, KValue *fA) {
  (void)e;
  return krt2_then(krt2_sleep_for(kint(20 * 1000000LL)),     /* 20ms: A spins */
         krt2_then(krt2_interrupt_fork(fA),
                   krt2_bind(krt2_await(fA), kclo(drv_got_exit, NULL))));
}
static KValue *prog(KValue *(*mkA)(void)) {
  return krt2_bind(krt2_fork(mkA()), kclo(drv_after_fork, NULL));
}

/* ── watchdog: a hung run (loop never interrupted) is a HARD failure ──────── */
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
      fprintf(stderr, "  FAIL: safepoint_loop HUNG (>%ds) — a tight loop ignored the interrupt\n", WATCHDOG_SECS);
      fprintf(stderr, "FAIL: safepoint_loop (hang)\n");
      abort();
    }
    struct timespec s = { 0, 50 * 1000 * 1000 };
    nanosleep(&s, NULL);
  }
}

static KValue *run_with_watchdog(KValue *(*mkA)(void)) {
  pthread_t wd;
  atomic_store(&g_done, 0);
  pthread_create(&wd, NULL, watchdog, NULL);
  KValue *ex = krt2_run_main(prog(mkA));
  atomic_store(&g_done, 1);
  pthread_join(wd, NULL);
  return ex;
}

/* ── TEST 3: weak fairness on a single worker ─────────────────────────────── */
static KValue *fair_sig = NULL;       /* C completes this; main awaits it     */
/* B: spin forever in a tight loop (the same infinite while as test 1). */
static KValue *fair_B(void) { return t1_A(); }
/* C: complete the signal promise, then return. */
static KValue *fair_C(void) {
  return krt2_then(krt2_complete_promise(fair_sig, krt2_success(kint(1))), krt2_pure(kunit()));
}
static KValue *fair_after_C(KEnv *e, KValue *fc) {
  (void)e; (void)fc;
  /* main awaits C's signal: reachable ONLY if B yields the single worker to C. */
  return krt2_then(krt2_await_promise_exit(fair_sig), krt2_pure(kunit()));
}
static KValue *fair_after_B(KEnv *e, KValue *fb) {
  (void)e; (void)fb;
  return krt2_bind(krt2_fork(fair_C()), kclo(fair_after_C, NULL));
}
static KValue *fair_after_sig(KEnv *e, KValue *sig) {
  (void)e; fair_sig = sig;
  return krt2_bind(krt2_fork(fair_B()), kclo(fair_after_B, NULL));
}
static KValue *fair_prog(void) {
  return krt2_bind(krt2_new_promise(), kclo(fair_after_sig, NULL));
}

static void run_fairness_case(void) {
  /* SINGLE worker (set process-wide below): B, C, and main share one OS thread,
   * so fairness depends ENTIRELY on B's back-edge cede.  Without it, B
   * monopolizes the worker and C never runs — main's await of C's signal hangs
   * (watchdog abort). */
  pthread_t wd;
  atomic_store(&g_done, 0);
  pthread_create(&wd, NULL, watchdog, NULL);
  KValue *ex = krt2_run_main(fair_prog());
  atomic_store(&g_done, 1);
  pthread_join(wd, NULL);
  CHECK(krt2_exit_is_success(ex),
        "test3: single worker — a spinning B did NOT starve sibling C (weak fairness; main awaited C's signal)");
  fprintf(stderr, "  test3: fairness run %s\n", krt2_exit_is_success(ex) ? "completed (C ran while B spun)" : "FAILED");
}

int main(void) {
  /* ONE worker, process-wide: main, the spinner, and any sibling share a single
   * OS thread.  This is the strongest configuration — test 1 then needs BOTH the
   * fairness cede (main must reclaim the worker from the spinner to issue the
   * interrupt) AND interrupt-delivery at the safe point; test 3 isolates fairness.
   * Set BEFORE krt2_new (the runtime is a persistent singleton; a later
   * krt2_new(1) would be a no-op). */
  setenv("KAPPA_RT_WORKERS", "1", 1);
  krt2_new(1);

  /* TEST 1: the unmasked infinite loop IS interrupted (and main reclaimed the
   * single worker to issue the interrupt — fairness + delivery together). */
  g_a_exit = NULL;
  KValue *m1 = run_with_watchdog(t1_A);
  CHECK(krt2_exit_is_success(m1), "test1: run_main returned (main Success)");
  CHECK(g_a_exit != NULL && kctor_is(g_a_exit, "Failure"),
        "test1: the tight unmasked loop was INTERRUPTED at a safe point (A Exit == Failure)");
  fprintf(stderr, "  test1: A exit = %s\n", g_a_exit ? (kctor_is(g_a_exit, "Failure") ? "Failure(interrupt)" : "Success") : "(none)");

  /* TEST 2: the masked finite loop runs to completion (not interrupted mid-loop). */
  atomic_store(&g_masked_final, -1);
  g_a_exit = NULL;
  KValue *m2 = run_with_watchdog(t2_A);
  CHECK(krt2_exit_is_success(m2), "test2: run_main returned (main Success)");
  long mf = atomic_load(&g_masked_final);
  fprintf(stderr, "  test2: masked loop final i = %ld (expect %lld)\n", mf, N_ITERS);
  CHECK(mf == N_ITERS,
        "test2: the masked tight loop ran to COMPLETION (suppression held; not interrupted mid-loop)");

  /* TEST 3 (weak fairness): a sibling C must still be scheduled while B spins. */
  run_fairness_case();

  if (fails == 0) {
    fprintf(stderr, "PASS: safepoint_loop (tight unmasked loop interrupted at a safe point; "
                    "masked loop runs full — suppression holds)\n");
    return 0;
  }
  fprintf(stderr, "FAIL: safepoint_loop (%d checks failed)\n", fails);
  return 1;
}
