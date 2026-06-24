/* rt_bench.c — microbenchmark isolating the cost sources in the kappart2 runtime,
 * to ground the "is this performant?" question in numbers rather than the
 * scary-looking generated C.  Reports ns/op and bytes/op (Boehm cumulative) for:
 *
 *   1. fork/await ping-pong  — the SUSPENSION cost (spawn a fiber, park, wake,
 *      detach).  This is the price you pay AT a concurrency boundary.
 *   2. CPS bind-tree build   — the structural cost of one krt2_bind+kclo+KEnv
 *      (what a continuation node costs to construct).
 *   3. CK-machine step       — driving one OP_THEN node through deliver/unwind.
 *   4. boxed addInt          — the VALUE-BOXING cost (axis #2): one ~KValue per
 *      arithmetic op, orthogonal to CPS.  THIS is the big Go/Rust gap.
 *   5. raw int64 add         — the absolute floor (what Go/Rust actually do).
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <gc.h>
#include <stdio.h>
#include <time.h>
#include <stdint.h>

static double now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}
static size_t allocated(void) { return (size_t)GC_get_total_bytes(); }

/* ── fork/await ping-pong ──────────────────────────────────────────────── */
static KValue *pp_after(KEnv *env, KValue *f) {
  return krt2_then(krt2_await(f), kvar(env, 0)); /* await the child, then the rest */
}
static KValue *pingpong(int n) {
  KValue *acc = krt2_pure(kunit());
  for (int i = 1; i <= n; i++)
    acc = krt2_bind(krt2_fork(krt2_pure(kint(i))), kclo(pp_after, kpush(acc, NULL)));
  return acc;
}

/* ── a chain of OP_THEN nodes (CK-machine step cost) ───────────────────── */
static KValue *then_chain(int n) {
  KValue *acc = krt2_pure(kint(0));
  for (int i = 0; i < n; i++) acc = krt2_then(acc, krt2_pure(kint(1)));
  return acc;
}

int main(void) {
  krt2_new(1); /* single worker: isolate the per-op cost from scheduling noise */
  const int FA = 200000;   /* fork/await iterations */
  const int ST = 1000000;  /* CK-steps / arithmetic iterations */

  printf("=== kappart2 microbenchmark (1 worker) ===\n");
  printf("%-34s %10s %12s\n", "workload", "ns/op", "bytes/op");

  /* 1+2. fork/await ping-pong: split build (CPS nodes) from run (suspension). */
  {
    size_t b0 = allocated();
    KValue *prog = pingpong(FA);
    size_t b1 = allocated();
    double t0 = now_ns();
    size_t r0 = allocated();
    KValue *ex = krt2_run_main(prog);
    size_t r1 = allocated();
    double t1 = now_ns();
    printf("%-34s %10.1f %12.0f\n", "fork/await ping-pong (run)",
           (t1 - t0) / FA, (double)(r1 - r0) / FA);
    printf("%-34s %10s %12.0f\n", "  CPS tree build (per bind)", "-", (double)(b1 - b0) / FA);
    (void)ex;
  }

  /* 3. CK-machine OP_THEN step. */
  {
    KValue *prog = then_chain(ST);
    double t0 = now_ns();
    size_t r0 = allocated();
    (void)krt2_run_main(prog);
    size_t r1 = allocated();
    double t1 = now_ns();
    printf("%-34s %10.1f %12.0f\n", "CK-machine then-step (run)",
           (t1 - t0) / ST, (double)(r1 - r0) / ST);
  }

  /* 4. boxed arithmetic (kp_addInt): the value-boxing cost. */
  {
    double t0 = now_ns();
    size_t a0 = allocated();
    KValue *acc = kint(0);
    for (int i = 0; i < ST; i++) acc = kp_addInt(acc, kint(7)); /* grows past the int cache */
    size_t a1 = allocated();
    double t1 = now_ns();
    printf("%-34s %10.2f %12.0f\n", "boxed addInt (kp_addInt)",
           (t1 - t0) / ST, (double)(a1 - a0) / ST);
    if (acc->tag == K_INT && acc->as.i == 0) printf("x"); /* keep acc live */
  }

  /* 5. raw int64 add: the floor. */
  {
    volatile int64_t acc = 0;
    double t0 = now_ns();
    for (int i = 0; i < ST; i++) acc += 7;
    double t1 = now_ns();
    printf("%-34s %10.2f %12s\n", "raw int64 add", (t1 - t0) / ST, "0");
  }
  return 0;
}
