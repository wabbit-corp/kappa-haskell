/* adv_scalar_flush.c — ADVERSARIAL: native-scalar-loop FLUSH-on-abort + masked
 * suppression for the krt2_safepoint() path (fix SP), the part the merged
 * safepoint_loop.c does NOT cover (it only exercises the CK-machine OP_WHILE).
 *
 * We hand-build a K_NATIVE IO leaf that mimics EXACTLY what compileScalarWhile /
 * @kscalarloop_ emit: two scalar vars x,y in i64 registers, a counter-gated
 * krt2_safepoint() at the BACK-EDGE (after the body commits), and on a deliverable
 * interrupt a FINAL-value flush of both vars to their ref cells, then the loop
 * exits (returns Unit) and the CK-machine delivers via the post-bridge gate.
 *
 * The loop body each iteration:   x := x+1 ;  y := x*2
 * so the invariant AT EVERY iteration boundary is  y == 2*x.  An async interrupt
 * arrives from a sibling driver; the loop aborts at SOME back-edge.  The flushed
 * cells MUST satisfy y==2*x (a complete iteration, never a half-updated x with a
 * stale y) and the loop must flush exactly once.
 *
 * Assertions:
 *   T1 (flush-once, boundary-exact): after the unmasked loop is interrupted, the
 *       ref cells satisfy y==2*x AND the abort path ran exactly once; the fiber
 *       Exit is Failure(Interrupt).
 *   T2 (masked suppression): the SAME loop body under uninterruptible() with a
 *       finite bound runs to COMPLETION despite an async interrupt — krt2_safepoint()
 *       returns 0 throughout (mask_depth>0), no mid-loop abort.
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

/* ── observation ─────────────────────────────────────────────────────────── */
static _Atomic long g_flush_x = -1, g_flush_y = -1;  /* values flushed to cells   */
static _Atomic int  g_abort_count = 0;               /* times the loop hit flush  */
static KValue      *g_xref = NULL, *g_yref = NULL;    /* the two var ref cells     */
static _Atomic int  g_masked = 0;                     /* run the loop masked?       */
static _Atomic long g_bound = 0;                      /* masked-finite loop bound   */
static _Atomic int  g_loop_started = 0;               /* loop is spinning           */

/* The native scalar loop leaf.  args[0]=xref, args[1]=yref.  Mimics the emitted
 * scalar loop: i64 registers, in-place commit, FINAL-value flush on safepoint. */
static KValue *scalar_loop_fn(KValue **args) {
  KValue *xref = args[0], *yref = args[1];
  KValue *xv = kref_get(xref);                    /* load cells -> registers       */
  KValue *yv = kref_get(yref);
  int64_t x = kas_int(xv);
  int64_t y = kas_int(yv);
  kdrop(xv);
  kdrop(yv);
  int64_t bound  = atomic_load(&g_bound);
  int masked = atomic_load(&g_masked);
  int64_t spc = 256;  /* small quantum: responsive but still amortized             */
  atomic_store(&g_loop_started, 1);
  for (;;) {
    /* condition (masked finite test; unmasked is "infinite") */
    if (masked && !(x < bound)) break;
    /* body: x := x+1 ; y := x*2   (in-place commit, sequential) */
    x = x + 1;
    y = x * 2;
    /* §32.2.6 back-edge safe point: counter-gated krt2_safepoint(). */
    if (--spc <= 0) {
      spc = 256;
      if (krt2_safepoint()) {
        /* FLUSH the FINAL (complete-iteration) values, record, and exit. */
        kref_set(xref, kint(x));
        kref_set(yref, kint(y));
        atomic_store(&g_flush_x, (long)x);
        atomic_store(&g_flush_y, (long)y);
        atomic_fetch_add(&g_abort_count, 1);
        return kunit();
      }
    }
  }
  /* normal completion (masked finite path): flush the final values. */
  kref_set(xref, kint(x));
  kref_set(yref, kint(y));
  atomic_store(&g_flush_x, (long)x);
  atomic_store(&g_flush_y, (long)y);
  return kunit();
}

static KValue *scalar_loop_action(KValue *xref, KValue *yref) {
  KValue *a[2] = { xref, yref };
  return knative_sat(scalar_loop_fn, 2, a, /*is_io=*/1);
}

/* The loop fiber body: newRef x=0, newRef y=0, stash refs, run the loop (masked
 * if g_masked). */
static KValue *body_run_loop(KEnv *e, KValue *yref) {
  KValue *xref = kvar(e, 0);
  g_xref = xref; g_yref = yref;
  KValue *loop = scalar_loop_action(xref, yref);
  if (atomic_load(&g_masked)) loop = krt2_uninterruptible(loop);
  return loop;
}
static KValue *body_after_x(KEnv *e, KValue *xref) {
  (void)e;
  return krt2_bind(krt2_new_ref(kint(0)), kclo(body_run_loop, kpush(xref, NULL)));
}
static KValue *loop_fiber_body(void) {
  return krt2_bind(krt2_new_ref(kint(0)), kclo(body_after_x, NULL));
}

/* driver: fork the loop fiber, sleep so it is deep in the loop, interrupt (no
 * wait), await its Exit. */
static KValue *g_loop_exit = NULL;
static KValue *got_exit(KEnv *e, KValue *exv) { (void)e; g_loop_exit = exv; return krt2_pure(kunit()); }
static KValue *after_fork(KEnv *e, KValue *fib) {
  (void)e;
  return krt2_then(krt2_sleep_for(kint(30 * 1000000LL)),       /* 30ms: loop spins */
         krt2_then(krt2_interrupt_fork(fib),
                   krt2_bind(krt2_await(fib), kclo(got_exit, NULL))));
}
static KValue *prog(void) {
  return krt2_bind(krt2_fork(loop_fiber_body()), kclo(after_fork, NULL));
}

/* watchdog */
static _Atomic int g_done = 0;
static void *watchdog(void *arg) {
  (void)arg; struct timespec start, now; clock_gettime(CLOCK_MONOTONIC, &start);
  for (;;) {
    if (atomic_load(&g_done)) return NULL;
    clock_gettime(CLOCK_MONOTONIC, &now);
    if (now.tv_sec - start.tv_sec >= 30) {
      fprintf(stderr, "  FAIL: adv_scalar_flush HUNG (native loop ignored interrupt)\n");
      fprintf(stderr, "FAIL: adv_scalar_flush (hang)\n"); abort();
    }
    struct timespec s = { 0, 50 * 1000 * 1000 }; nanosleep(&s, NULL);
  }
}
static KValue *run_watched(void) {
  pthread_t wd; atomic_store(&g_done, 0); pthread_create(&wd, NULL, watchdog, NULL);
  KValue *ex = krt2_run_main(prog());
  atomic_store(&g_done, 1); pthread_join(wd, NULL);
  return ex;
}

int main(void) {
  /* 2 workers: the driver and the loop fiber run CONCURRENTLY so the driver can
   * deliver the interrupt while the native loop spins (the native loop cannot cede
   * mid-K_NATIVE, so a single worker would let it monopolize until done). */
  setenv("KAPPA_RT_WORKERS", "2", 1);
  krt2_new(2);

  /* ── T1: unmasked loop interrupted async — boundary-exact, flush once ────── */
  atomic_store(&g_masked, 0);
  atomic_store(&g_flush_x, -1); atomic_store(&g_flush_y, -1);
  atomic_store(&g_abort_count, 0);
  atomic_store(&g_loop_started, 0);
  g_loop_exit = NULL;
  KValue *m1 = run_watched();
  CHECK(krt2_exit_is_success(m1), "T1: run_main Success");
  CHECK(g_loop_exit && kctor_is(g_loop_exit, "Failure"),
        "T1: native loop interrupted at a safe point (Exit == Failure)");
  long fx = atomic_load(&g_flush_x), fy = atomic_load(&g_flush_y);
  long ac = atomic_load(&g_abort_count);
  fprintf(stderr, "  T1: flushed x=%ld y=%ld abort_count=%ld (expect y==2x, ac==1)\n", fx, fy, ac);
  CHECK(fx > 0, "T1: the loop ran at least one iteration before aborting");
  CHECK(fy == 2 * fx, "T1: iteration-boundary invariant y==2x held in the FLUSHED cells (no half-updated state)");
  CHECK(ac == 1, "T1: the loop flushed-and-exited EXACTLY ONCE (no double-apply / re-entry)");
  KValue *cxv = kref_get(g_xref);
  KValue *cyv = kref_get(g_yref);
  long cx = (long)kas_int(cxv);
  long cy = (long)kas_int(cyv);
  kdrop(cxv);
  kdrop(cyv);
  fprintf(stderr, "  T1: ref cells x=%ld y=%ld\n", cx, cy);
  CHECK(cx == fx && cy == fy, "T1: ref cells hold the flushed boundary values");
  CHECK(cy == 2 * cx, "T1: ref cells satisfy y==2x (exactly-once, boundary-exact flush)");

  /* ── T2: masked finite loop runs to completion despite an async interrupt ── */
  atomic_store(&g_masked, 1);
  atomic_store(&g_bound, 50000000LL);   /* big enough that the 30ms interrupt lands mid-loop */
  atomic_store(&g_flush_x, -1); atomic_store(&g_flush_y, -1);
  atomic_store(&g_abort_count, 0);
  atomic_store(&g_loop_started, 0);
  g_loop_exit = NULL;
  KValue *m2 = run_watched();
  CHECK(krt2_exit_is_success(m2), "T2: run_main Success");
  long fx2 = atomic_load(&g_flush_x), ac2 = atomic_load(&g_abort_count);
  fprintf(stderr, "  T2: masked loop final x=%ld abort_count=%ld (expect x==bound, ac==0)\n", fx2, ac2);
  CHECK(fx2 == atomic_load(&g_bound), "T2: the masked loop ran to COMPLETION (suppression held mid-loop)");
  CHECK(ac2 == 0, "T2: krt2_safepoint() never aborted a masked loop (no flush-abort)");

  if (fails == 0) {
    fprintf(stderr, "PASS: adv_scalar_flush (native-loop flush boundary-exact + once; masked suppression holds)\n");
    return 0;
  }
  fprintf(stderr, "FAIL: adv_scalar_flush (%d checks failed)\n", fails);
  return 1;
}
