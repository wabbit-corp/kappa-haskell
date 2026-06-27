/* run_main_persist.c — §1 (RUNTIME-EFFICIENCY-REVIEW) the repeated-run_main
 * crash regression.  Calling krt2_run_main many times in ONE process used to
 * crash deterministically around the 60th-80th call with "applying a non-
 * function value": the per-run krt2_shutdown cleared g_rt and joined+rebuilt the
 * workers/reactor/uv_loop, and the shutdown->reinit cycle triggered a GC under-
 * retention that reclaimed a still-root-reachable Cont chain — deliver()'s
 * KK_BIND arm then read a reused box as the bind closure.
 *
 * The fix makes the runtime PERSISTENT: the pool/reactor/loop init once and stay
 * alive across runs; per call we only build+run+drain the main fiber.  This test
 * runs WAY past the old crash window (>5000 runs) under forced GC pressure,
 * checking the result of EVERY run.  Two programs alternate so the repeated runs
 * cover the crash-relevant Cont families:
 *   P1 — bind/then sequencing + a Ref + a do-scope defer + fork/await/promise
 *        (the KK_BIND deliver arm — the exact crash site — plus suspension).
 *   P2 — a deep effect handler perform/resume (KK_HANDLER + KK_DOSCOPE + the new
 *        KK_ABANDON-bearing severed slice), the heaviest Cont shape.
 * No per-run thread create/join happens anymore (also cheaper).
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <gc.h>
#include <stdio.h>

#define NRUNS   6000
#define EXPECT1 23   /* (Ref accumulate) 10 + (await child) 13 = 23                */
#define EXPECT2 7    /* handler: perform E.add (); resume k 7 -> 7                 */

/* ── P1: a do-scope with a defer, accumulating into a Ref via bind/then ────
 * kvar index convention: kpush(a, kpush(b, NULL)) => index 0 == a, 1 == b. */
static KValue *acc_read(KEnv *env, KValue *v) { (void)env; return krt2_pure(v); }  /* result == acc */
static KValue *acc_write(KEnv *env, KValue *cur) {       /* env[0]=ref; arg=cur acc */
  return krt2_write_ref(kvar(env, 0), kp_addInt(cur, kint(7)));   /* acc: 3 -> 10 */
}
static KValue *acc_body(KEnv *env, KValue *ref) { (void)env;       /* ref initialized to 3 */
  KValue *bump = krt2_bind(krt2_read_ref(ref), kclo(acc_write, kpush(ref, NULL)));
  KValue *rd   = krt2_bind(krt2_read_ref(ref), kclo(acc_read, NULL));
  KValue *seq  = krt2_then(krt2_defer(krt2_pure(kunit())), krt2_then(bump, rd));
  return krt2_doscope(seq);
}
static KValue *part_ref(void) {  /* => 10 */
  return krt2_bind(krt2_new_ref(kint(3)), kclo(acc_body, NULL));
}

/* fork/await/promise: child completes a promise with 13; parent awaits it. */
static KValue *child_body(KEnv *env, KValue *p) { (void)env;
  return krt2_complete_promise(p, krt2_success(kint(13))); }
static KValue *got_exit(KEnv *env, KValue *exitv) { (void)env;
  return krt2_pure(kctor_arg(exitv, 0)); }                 /* Success 13 -> 13 */
static KValue *await_after_fork(KEnv *env, KValue *child) { (void)child;   /* env[0]=promise */
  return krt2_bind(krt2_await_promise_exit(kvar(env, 0)), kclo(got_exit, NULL)); }
static KValue *with_promise(KEnv *env, KValue *p) { (void)env;
  return krt2_bind(krt2_fork(child_body(NULL, p)), kclo(await_after_fork, kpush(p, NULL))); }
static KValue *part_await(void) {  /* => 13 */
  return krt2_bind(krt2_new_promise(), kclo(with_promise, NULL));
}

static KValue *p1_sum(KEnv *env, KValue *r2) { return krt2_pure(kp_addInt(kvar(env, 0), r2)); } /* r1+r2 */
static KValue *p1_after_ref(KEnv *env, KValue *r1) { (void)env;
  return krt2_bind(part_await(), kclo(p1_sum, kpush(r1, NULL))); }
static KValue *program1(void) {  /* => 23 */
  return krt2_bind(part_ref(), kclo(p1_after_ref, NULL));
}

/* ── P2: deep effect handler perform/resume.  The body is wrapped in a
 * doscope+defer — the shape real codegen emits for a do-block — so the captured
 * op-site->handler slice includes a KK_DOSCOPE, exercising KK_HANDLER +
 * KK_DOSCOPE + the new KK_ABANDON guard frame (resumed => transparent). */
static KValue *h_clause_k(KEnv *e, KValue *k) { (void)e; return kapp(k, kint(7)); }  /* resume k 7 */
static KValue *h_clause(KEnv *e, KValue *payload) { (void)e; (void)payload; return kclo(h_clause_k, NULL); }
static KValue *h_ret(KEnv *e, KValue *x) { (void)e; return krt2_pure(x); }
static KValue *h_after(KEnv *e, KValue *v) { (void)e; return krt2_pure(v); }  /* v == 7 */
static KValue *program2(void) {  /* => 7 */
  const char *names[1] = { "add" };
  KValue *vals[1]      = { kclo(h_clause, NULL) };
  KValue *ops = krec(1, names, vals);
  KValue *perf   = krt2_bind(krt2_perform(kstr0("E"), kstr0("add"), kunit()), kclo(h_after, NULL));
  KValue *scoped = krt2_doscope(krt2_then(krt2_defer(krt2_pure(kunit())), perf));
  return krt2_handle(kbool(1), kstr0("E"), kclo(h_ret, NULL), ops, scoped);
}

static int check(const char *which, int run, KValue *ex, int64_t expect) {
  if (!kctor_is(ex, "Success") || kctor_argc(ex) != 1 || kas_int(kctor_arg(ex, 0)) != expect) {
    fprintf(stderr, "  FAIL: %s run %d wrong result (isSucc=%d)\n", which, run, kctor_is(ex, "Success"));
    return 1;
  }
  return 0;
}

int main(void) {
  /* a single worker keeps the result deterministic and isolates the lifecycle,
   * not scheduling; the bug reproduced at 1 worker too. */
  krt2_new(1);

  int bad = 0;
  for (int run = 0; run < NRUNS && bad <= 3; run++) {
    bad += check("P1", run, krt2_run_main(program1()), EXPECT1);
    bad += check("P2", run, krt2_run_main(program2()), EXPECT2);
    /* force collections through the run N+1 region — the documented trigger. */
    if ((run & 0x1f) == 0) GC_gcollect();
  }

  if (bad == 0) {
    fprintf(stderr, "PASS: run_main_persist (%d x 2 persistent runs, results %d/%d; the ~call-60-80 crash is gone)\n",
            NRUNS, EXPECT1, EXPECT2);
    return 0;
  }
  fprintf(stderr, "FAIL: run_main_persist (%d bad runs)\n", bad);
  return 1;
}
