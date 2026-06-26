/* rt_bench.c — microbenchmark isolating the cost sources in the kappart2 runtime,
 * to ground the "is this performant?" question in numbers rather than the
 * scary-looking generated C.  Reports ns/op and bytes/op (Boehm cumulative) for:
 *
 *   1. fork/await ping-pong  — the SUSPENSION cost (spawn a fiber, park, wake,
 *      detach).  This is the price you pay AT a concurrency boundary.
 *   2. scalar across a park   — a counter Int carried across a fork/await park
 *      (UNBOXING Stage-0 #4): the cross-park property Stage 1's tagged immediate
 *      must preserve.  Asserts the recovered sum is correct.
 *   3. CPS bind-tree build   — the structural cost of one krt2_bind+kclo+KEnv.
 *   4. CK-machine step       — driving one OP_THEN node through deliver/unwind.
 *   5. boxed addInt          — the Int VALUE-BOXING cost (axis #2): one ~KValue
 *      per arithmetic op, orthogonal to CPS.  THIS is the big Go/Rust gap.
 *   6. boxed addDouble        — the binary64 boxing cost; the floor Stage 2b's
 *      unboxed F64 worker must beat (no Double cache, so always one box/op).
 *   7. ctor-build (n-ary)     — the boxed n-ary constructor ALLOCATION cost; the
 *      CONTROL for the Stage-1 go/no-go gate (n-ary ctors stay boxed).
 *   8. ctor0-build (nullary)  — the NULLARY constructor allocation cost; the case
 *      Stage 1 turns into a zero-alloc b010 immediate (the ctor-immediate WIN).
 *   9. ctor deref (tagid+arg) — the boxed-ctor DEREF cost: the TAG-TEST-TAX
 *      detector Stage 1 must regress <=~5-10% (UNBOXING §7/§8 go/no-go gate).
 *  10. ctor0 dispatch         — match-dispatch on a value that becomes an
 *      immediate (the win half of the match requirement, paired with #9's tax).
 *  11. raw int64 add          — the absolute floor (what Go/Rust actually do).
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

/* ── scalar across a park ──────────────────────────────────────────────────
 * Each step forks `pure(i)`, awaits the resulting fiber (a real CK-machine
 * SUSPENSION), then threads the recovered child Int into a running accumulator
 * that was captured in the KEnv slot ACROSS the park.  The accumulator is the
 * value threaded through the bind chain; `kvar(env,0)` is the captured acc that
 * must survive the park and be recovered correctly on resume. */
static KValue *ap_recover(KEnv *env, KValue *exitv) {
  /* exitv is the awaited child's terminal Exit = Success(kint(i)); unwrap it.
   * kvar(env,0) is the accumulator that crossed the await park. */
  KValue *child = kctor_arg(exitv, 0);              /* Success(i) -> kint(i)      */
  return krt2_pure(kp_addInt(kvar(env, 0), child)); /* acc' = acc + i (lives on)  */
}
static KValue *ap_after_fork(KEnv *env, KValue *fiber) {
  /* fiber is the handle delivered by running fork; await it, then on resume add
   * the recovered child Int to the accumulator we carry across the park. */
  return krt2_bind(krt2_await(fiber), kclo(ap_recover, kpush(kvar(env, 0), NULL)));
}
static KValue *ap_step(KEnv *env, KValue *acc) {
  /* acc is the running accumulator from the prior bind; capture it so it lives
   * across the await park, then fork this step's child `pure(i)`. */
  return krt2_bind(krt2_fork(krt2_pure(kvar(env, 0))),
                   kclo(ap_after_fork, kpush(acc, NULL)));
}
static KValue *across_park(int n) {
  KValue *acc = krt2_pure(kint(0));
  for (int i = 1; i <= n; i++)
    acc = krt2_bind(acc, kclo(ap_step, kpush(kint(i), NULL)));
  return acc;
}

int main(void) {
  krt2_new(1); /* single worker: isolate the per-op cost from scheduling noise */
  const int FA = 200000;   /* fork/await iterations */
  const int ST = 1000000;  /* CK-steps / arithmetic iterations */

  printf("=== kappart2 microbenchmark (1 worker) ===\n");
  printf("%-34s %10s %12s\n", "workload", "ns/op", "bytes/op");

  /* 1. fork/await ping-pong: split build (CPS nodes) from run (suspension). */
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

  /* 2. scalar across a park (UNBOXING Stage-0 #4): a counter Int must genuinely
   *    live across a fork/await park and be recovered correctly on resume
   *    (Stage 1's structural claim).  Re-create a 1-worker runtime (the prior
   *    krt2_run_main shut g_rt down) so the child PARKS before the await rather
   *    than racing to F_DONE on a second worker.  ASSERT the final accumulator
   *    == sum 1..FA; the printed label is derived from the live result (defeats
   *    DCE) and flips to a FAIL marker on mismatch. */
  {
    krt2_new(1); /* 1 worker: guarantee the just-forked child parks before await */
    KValue *prog = across_park(FA);
    double t0 = now_ns();
    size_t r0 = allocated();
    KValue *ex = krt2_run_main(prog);                 /* ex = Success(finalAcc)  */
    size_t r1 = allocated();
    double t1 = now_ns();
    int64_t got  = kctor_arg(ex, 0)->as.i;            /* unwrap Success -> acc   */
    int64_t want = (int64_t)FA * (FA + 1) / 2;        /* sum 1..FA               */
    const char *tag = (got == want) ? "scalar across park (run)"
                                    : "scalar across park FAIL!!";
    printf("%-34s %10.1f %12.0f\n", tag, (t1 - t0) / FA, (double)(r1 - r0) / FA);
    if (got != want) printf("  FAIL: got %lld want %lld\n",
                            (long long)got, (long long)want);
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

  /* 4. boxed Int arithmetic (kp_addInt): the value-boxing cost. */
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

  /* 5. boxed Double arithmetic (kp_addDouble): the binary64 value-boxing cost —
   *    the analogue of boxed addInt (item 4) for F64, and the floor Stage 2b's
   *    unboxed worker must beat.  Hoist the 7.0 literal out of the loop: there
   *    is no Double cache (kdbl always allocates), so an in-loop kdbl(7.0) would
   *    box TWICE per op and double the bytes/op vs the single-box addInt row. */
  {
    KValue *seven = kdbl(7.0); /* hoisted: count only the per-op RESULT box */
    double t0 = now_ns();
    size_t a0 = allocated();
    KValue *acc = kdbl(0.0);
    for (int i = 0; i < ST; i++) acc = kp_addDouble(acc, seven); /* one heap KValue per op */
    size_t a1 = allocated();
    double t1 = now_ns();
    printf("%-34s %10.2f %12.0f\n", "boxed addDouble (kp_addDouble)",
           (t1 - t0) / ST, (double)(a1 - a0) / ST);
    if (acc->tag == K_DBL && acc->as.d == 0.0) printf("x"); /* keep acc live */
  }

  /* 6. ctor-build (kctor): the boxed n-ary constructor ALLOCATION cost — the
   *    CONTROL half of the go/no-go gate (n-ary ctors stay boxed in Stage 1, so
   *    this number should NOT move). */
  {
    KValue *prev = kctor0(KCT_NIL, "[]"); /* chain tail keeps every cell live */
    double t0 = now_ns();
    size_t a0 = allocated();
    for (int i = 0; i < ST; i++) {
      KValue *args[2] = { kint(i), prev };
      prev = kctor(KCT_CONS, "::", 2, args); /* a Cons cell per iter */
    }
    size_t a1 = allocated();
    double t1 = now_ns();
    printf("%-34s %10.2f %12.0f\n", "ctor-build (kctor 2-arg Cons)",
           (t1 - t0) / ST, (double)(a1 - a0) / ST);
    /* DCE defense: read tag + head field of the last cell into the output. */
    if (kctor_tagid(prev) != KCT_CONS || kctor_arg(prev, 0) == NULL) printf("x");
  }

  /* 7. ctor0-build (nullary None): the NULLARY constructor allocation cost — the
   *    case Stage 1 turns into a zero-alloc b010 immediate (Bool/Unit/Nil/None),
   *    while the n-ary Cons above stays boxed.  Use None: Unit is canonicalized
   *    to the_unit and Bool is statically cached, so they understate the alloc;
   *    None is the clean per-call kctor0 allocator.  bytes/op -> 0 under Stage 1. */
  {
    KValue *last = kctor0(KCT_NONE, "None");
    double t0 = now_ns();
    size_t a0 = allocated();
    for (int i = 0; i < ST; i++) last = kctor0(KCT_NONE, "None"); /* a heap box today */
    size_t a1 = allocated();
    double t1 = now_ns();
    printf("%-34s %10.2f %12.0f\n", "ctor0-build (nullary None)",
           (t1 - t0) / ST, (double)(a1 - a0) / ST);
    if (kctor_tagid(last) != KCT_NONE) printf("x"); /* keep last live */
  }

  /* 8. constructor deref (kctor_tagid + kctor_arg): the TAG-TEST-TAX detector.
   *    Build ONE boxed Cons before timing; per iter do a match-dispatch (tagid)
   *    and a projection (arg), with NO allocation in the loop.  Stage 1 adds a
   *    tag-test branch to every ->tag/->as.* deref; this is the go/no-go baseline
   *    that tax is measured against (must stay within ~5-10%). */
  {
    KValue *args[2] = { kint(11), kint(22) };          /* arg0=11, arg1=22 */
    KValue *v = kctor(KCT_CONS, "::", 2, args);        /* one hot boxed Cons cell */
    volatile int64_t sink = 0;
    double t0 = now_ns();
    size_t a0 = allocated();
    for (int i = 0; i < ST; i++) {
      int t = kctor_tagid(v);                  /* match dispatch: the tag test  */
      KValue *a = kctor_arg(v, i & 1);         /* projection: pick arg 0/1      */
      sink += (int64_t)t + a->as.i;            /* fold both into a volatile sink */
    }
    size_t a1 = allocated();
    double t1 = now_ns();
    printf("%-34s %10.2f %12.0f\n", "ctor deref boxed (tagid+arg)",
           (t1 - t0) / ST, (double)(a1 - a0) / ST);
    if (sink == 0) printf("x"); /* keep sink live: defeat DCE */
  }

  /* 9. ctor0 dispatch (nullary None tagid): the match-dispatch cost on a value
   *    that BECOMES an immediate — today a ->tag deref, under Stage 1 a tag-test
   *    with NO deref (the WIN half of the match requirement, paired with #8's
   *    boxed-deref tax). */
  {
    KValue *none = kctor0(KCT_NONE, "None");
    volatile int64_t sink = 0;
    double t0 = now_ns();
    size_t a0 = allocated();
    for (int i = 0; i < ST; i++) sink += kctor_tagid(none);
    size_t a1 = allocated();
    double t1 = now_ns();
    printf("%-34s %10.2f %12.0f\n", "ctor0 dispatch (nullary tagid)",
           (t1 - t0) / ST, (double)(a1 - a0) / ST);
    if (sink == 0) printf("x"); /* keep sink live */
  }

  /* 10. raw int64 add: the floor. */
  {
    volatile int64_t acc = 0;
    double t0 = now_ns();
    for (int i = 0; i < ST; i++) acc += 7;
    double t1 = now_ns();
    printf("%-34s %10.2f %12s\n", "raw int64 add", (t1 - t0) / ST, "0");
  }
  return 0;
}
