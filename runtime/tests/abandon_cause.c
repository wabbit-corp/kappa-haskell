/* abandon_cause.c — three review findings on the §32.2.20/.21 handler-abandonment
 * drain path, all of which the existing abandon_drain.c structurally missed:
 *
 *   fix 1 (H1) — NESTED abandon drain recursion.  An UNRESUMED inner resumption
 *     whose KK_ABANDON guard frame is captured into an OUTER abandoned slice was
 *     SKIPPED during the outer RK_DRAIN walk (`if (r->used || rkind==RK_DRAIN)
 *     continue;`), so the inner captured do-scope's `defer`/`using` exit actions
 *     never ran.  After the fix, an unused inner resumption reached during a drain
 *     recurses into begin_abandon_drain, so its defers run exactly once.
 *
 *   fix 2 (H2) — drain-time finalizer failure SWALLOWED.  When a defer in the
 *     abandoned slice itself FAILS (and the failure ESCAPES — unlike abandon_drain
 *     scenario C which catches its own throw), the KK_ABANDEND arm unconditionally
 *     restored the saved clause result, discarding the live failure.  After the fix
 *     the live cleanup failure is composed with the clause result via §32.2.12.
 *
 *   fix 3 (C2) on the ABANDONMENT path — a failing abandoned-slice defer composes
 *     `Then` and does not drop the slice's remaining defers (§18.7/§32.2.12).
 *
 * All shapes use krt2_new(1) for determinism PLUS a krt2_new(2) concurrent variant
 * of the H2 escaping-failure case (review: add a multi-worker case).
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <gc.h>
#include <stdio.h>
#include <stdatomic.h>
#include <string.h>

static int fails = 0;
#define CHECK(c, m) do { if (!(c)) { fprintf(stderr, "  FAIL: %s\n", m); fails++; } } while (0)

/* ── cause matchers (shared) ────────────────────────────────────────────── */
static int cause_is_fail(KValue *cause, const char *tag) {
  if (kctor_tagid(cause) != KCT_FAIL || kctor_argc(cause) != 1) return 0;
  KValue *e = kctor_arg(cause, 0);
  return e && e->tag == K_STR && e->as.str.len == (int)strlen(tag) &&
         memcmp(e->as.str.p, tag, e->as.str.len) == 0;
}
static int is_failure_fail(KValue *ex, const char *tag) {
  return kctor_is(ex, "Failure") && kctor_argc(ex) == 1 &&
         cause_is_fail(kctor_arg(ex, 0), tag);
}
static int is_failure_then(KValue *ex, const char *a, const char *b) {
  if (!kctor_is(ex, "Failure") || kctor_argc(ex) != 1) return 0;
  KValue *cause = kctor_arg(ex, 0);
  if (kctor_tagid(cause) != KCT_THEN || kctor_argc(cause) != 2) return 0;
  return cause_is_fail(kctor_arg(cause, 0), a) && cause_is_fail(kctor_arg(cause, 1), b);
}

/* ── shared abortive clause / return clause builders ────────────────────── */
/* abortive: \payload -> \k -> pure V   (k IGNORED => abandon).  V is captured. */
static KValue *ret_pure(KEnv *e, KValue *x) { (void)e; return krt2_pure(x); }

/* =========================================================================
 * fix 2 (H2) + fix 3 (C2) abandonment path: an abortive clause whose captured
 * slice contains a defer that THROWS (escaping).  The drain runs the defer, it
 * fails, and the failure composes with the clause result.
 * ====================================================================== */

/* H2a: clause result is SUCCESS (pure 99); abandoned defer throws "cleanup".
 * Expect Failure(Fail "cleanup") — the cleanup failure replaces a successful
 * clause result (§32.2.21: cleanup cause composed with the clause result; a
 * success body composes to just the cleanup cause). */
static _Atomic int h2a_defer_ran = 0;
static KValue *h2a_clause_k(KEnv *e, KValue *k) { (void)e; (void)k; return krt2_pure(kint(99)); }
static KValue *h2a_clause(KEnv *e, KValue *p) { (void)e; (void)p; return kclo(h2a_clause_k, NULL); }
static KValue *h2a_mark(KEnv *e) { (void)e; atomic_store(&h2a_defer_ran, 1); return kunit(); }
static KValue *h2a_defer_body(void) { return krt2_then(kio(h2a_mark, NULL), krt2_throw(kstr0("cleanup"))); }
static KValue *h2a_body(void) {
  KValue *after = krt2_then(krt2_perform(kstr0("E"), kstr0("abort"), kunit()), krt2_pure(kint(0)));
  return krt2_doscope(krt2_then(krt2_defer(h2a_defer_body()), after));
}
static KValue *scenarioH2a(void) {
  static const char *names[1] = { "abort" };
  KValue *vals[1]      = { kclo(h2a_clause, NULL) };
  return krt2_handle(kbool(1), kstr0("E"), kclo(ret_pure, NULL), krec(1, names, vals), h2a_body());
}

/* H2b: clause FAILS (throw "clause"); abandoned defer throws "cleanup".
 * Expect Failure(Then (Fail "clause") (Fail "cleanup")). */
static KValue *h2b_clause_k(KEnv *e, KValue *k) { (void)e; (void)k; return krt2_throw(kstr0("clause")); }
static KValue *h2b_clause(KEnv *e, KValue *p) { (void)e; (void)p; return kclo(h2b_clause_k, NULL); }
static KValue *h2b_defer_body(void) { return krt2_throw(kstr0("cleanup")); }
static KValue *h2b_body(void) {
  KValue *after = krt2_then(krt2_perform(kstr0("E"), kstr0("abort"), kunit()), krt2_pure(kint(0)));
  return krt2_doscope(krt2_then(krt2_defer(h2b_defer_body()), after));
}
static KValue *scenarioH2b(void) {
  static const char *names[1] = { "abort" };
  KValue *vals[1]      = { kclo(h2b_clause, NULL) };
  return krt2_handle(kbool(1), kstr0("E"), kclo(ret_pure, NULL), krec(1, names, vals), h2b_body());
}

/* C2-abandon: clause result SUCCESS; TWO abandoned defers, the LIFO-first throws.
 * Both must run; result Failure(Fail "d-early"). */
static _Atomic int c2_late = 0, c2_early = 0;
static KValue *c2_clause_k(KEnv *e, KValue *k) { (void)e; (void)k; return krt2_pure(kint(7)); }
static KValue *c2_clause(KEnv *e, KValue *p) { (void)e; (void)p; return kclo(c2_clause_k, NULL); }
static KValue *c2_mark_late(KEnv *e)  { (void)e; atomic_store(&c2_late, 1);  return kunit(); }
static KValue *c2_mark_early(KEnv *e) { (void)e; atomic_store(&c2_early, 1); return kunit(); }
static KValue *c2_body(void) {
  KValue *early = krt2_then(kio(c2_mark_early, NULL), krt2_throw(kstr0("d-early")));
  KValue *after = krt2_then(krt2_perform(kstr0("E"), kstr0("abort"), kunit()), krt2_pure(kint(0)));
  return krt2_doscope(
      krt2_then(krt2_defer(kio(c2_mark_late, NULL)),     /* LIFO-last  (runs 2nd) */
      krt2_then(krt2_defer(early),                       /* LIFO-first (runs 1st, throws) */
                after)));
}
static KValue *scenarioC2(void) {
  static const char *names[1] = { "abort" };
  KValue *vals[1]      = { kclo(c2_clause, NULL) };
  return krt2_handle(kbool(1), kstr0("E"), kclo(ret_pure, NULL), krec(1, names, vals), c2_body());
}

/* =========================================================================
 * fix 1 (H1): nested abandon.  OUTER handler is abortive; INNER handler's clause
 * performs OUTER.op and never resumes its own k_inner.  The inner body's do-scope
 * (with an inner defer) is k_inner's captured slice; the inner KK_ABANDON guard is
 * captured into the OUTER abandoned slice.  The outer drain must RECURSE to drain
 * k_inner's slice so the inner defer runs.
 * ====================================================================== */
static _Atomic int h1_inner_defer = 0;
static KValue *h1_inner_mark(KEnv *e) { (void)e; atomic_fetch_add(&h1_inner_defer, 1); return kunit(); }

/* OUTER clause: \p -> \k_outer -> pure 0   (abandons k_outer). */
static KValue *h1_outer_k(KEnv *e, KValue *k) { (void)e; (void)k; return krt2_pure(kint(0)); }
static KValue *h1_outer_clause(KEnv *e, KValue *p) { (void)e; (void)p; return kclo(h1_outer_k, NULL); }

/* INNER clause: \p -> \k_inner -> do { perform OUTER.op; pure 1 }
 * (k_inner is IGNORED; performing OUTER.op suspends this clause into OUTER's
 * captured slice, so the inner KK_ABANDON for k_inner ends up ON that slice.) */
static KValue *h1_inner_k(KEnv *e, KValue *k) { (void)e; (void)k;
  return krt2_then(krt2_perform(kstr0("OUT"), kstr0("o"), kunit()), krt2_pure(kint(1))); }
static KValue *h1_inner_clause(KEnv *e, KValue *p) { (void)e; (void)p; return kclo(h1_inner_k, NULL); }

/* inner body: doscope { defer inner_mark; perform INNER.in (); pure 2 }
 * the doscope (with the defer) is captured by INNER as k_inner's slice. */
static KValue *h1_inner_body(void) {
  KValue *after = krt2_then(krt2_perform(kstr0("IN"), kstr0("in"), kunit()), krt2_pure(kint(2)));
  return krt2_doscope(krt2_then(krt2_defer(kio(h1_inner_mark, NULL)), after));
}
/* OUTER body: handle INNER (deep) inner_body.  (No extra outer doscope needed —
 * the inner KK_ABANDON rides OUTER's slice directly.) */
static KValue *h1_outer_body(void) {
  static const char *in_names[1] = { "in" };
  KValue *in_vals[1]      = { kclo(h1_inner_clause, NULL) };
  return krt2_handle(kbool(1), kstr0("IN"), kclo(ret_pure, NULL), krec(1, in_names, in_vals),
                     h1_inner_body());
}
static KValue *scenarioH1(void) {
  static const char *out_names[1] = { "o" };
  KValue *out_vals[1]      = { kclo(h1_outer_clause, NULL) };
  return krt2_handle(kbool(1), kstr0("OUT"), kclo(ret_pure, NULL), krec(1, out_names, out_vals),
                     h1_outer_body());
}

/* ── concurrent H2a variant (multi-worker) ──────────────────────────────── */
#define NKIDS 24
static _Atomic int conc_count = 0;
static KValue *conc_clause_k(KEnv *e, KValue *k) { (void)e; (void)k; return krt2_pure(kint(99)); }
static KValue *conc_clause(KEnv *e, KValue *p) { (void)e; (void)p; return kclo(conc_clause_k, NULL); }
static KValue *conc_defer_body(void) { return krt2_throw(kstr0("cleanup")); }
static KValue *conc_body(void) {
  KValue *after = krt2_then(krt2_perform(kstr0("E"), kstr0("abort"), kunit()), krt2_pure(kint(0)));
  return krt2_doscope(krt2_then(krt2_defer(conc_defer_body()), after));
}
static KValue *conc_child(void) {
  static const char *names[1] = { "abort" };
  KValue *vals[1]      = { kclo(conc_clause, NULL) };
  return krt2_handle(kbool(1), kstr0("E"), kclo(ret_pure, NULL), krec(1, names, vals), conc_body());
}
static KValue *conc_after_await(KEnv *e, KValue *exitv) { (void)e;
  if (is_failure_fail(exitv, "cleanup")) atomic_fetch_add(&conc_count, 1);
  return krt2_pure(kunit()); }
static KValue *conc_await(KEnv *e, KValue *child) { (void)e;
  return krt2_bind(krt2_await(child), kclo(conc_after_await, NULL)); }
static KValue *conc_loop(KEnv *env, KValue *unit);
static KValue *conc_spawn1(KEnv *env, KValue *child) {
  int i = (int)kas_int(kvar(env, 0));
  return krt2_then(conc_await(NULL, child), conc_loop(kpush(kint(i + 1), NULL), kunit())); }
static KValue *conc_loop(KEnv *env, KValue *unit) { (void)unit;
  int i = (int)kas_int(kvar(env, 0));
  if (i >= NKIDS) return krt2_pure(kint(0));
  return krt2_bind(krt2_fork(conc_child()), kclo(conc_spawn1, kpush(kint(i), NULL))); }
static KValue *scenarioConc(void) { return conc_loop(kpush(kint(0), NULL), kunit()); }

int main(void) {
  krt2_new(1);

  /* H2a: success clause + escaping throwing defer => Failure(Fail cleanup) */
  KValue *e2a = krt2_run_main(scenarioH2a());
  CHECK(atomic_load(&h2a_defer_ran) == 1, "H2a: abandoned defer body ran");
  CHECK(is_failure_fail(e2a, "cleanup"),
        "H2a: escaping drain failure NOT swallowed => Failure(Fail cleanup)");

  /* H2b: failing clause + escaping throwing defer => Then(clause, cleanup) */
  KValue *e2b = krt2_run_main(scenarioH2b());
  CHECK(is_failure_then(e2b, "clause", "cleanup"),
        "H2b: clause-fail composed with drain-fail => Failure(Then (Fail clause) (Fail cleanup))");

  /* C2-abandon: two defers, LIFO-first throws — both run, composed */
  KValue *ec2 = krt2_run_main(scenarioC2());
  CHECK(atomic_load(&c2_early) == 1, "C2: LIFO-first abandoned defer (throwing) ran");
  CHECK(atomic_load(&c2_late)  == 1, "C2: LIFO-last abandoned defer ALSO ran (not dropped)");
  CHECK(is_failure_fail(ec2, "d-early"), "C2: result is the composed cleanup cause");

  /* H1: nested abandon — inner unresumed resumption's defer must drain */
  KValue *e1 = krt2_run_main(scenarioH1());
  CHECK(atomic_load(&h1_inner_defer) == 1,
        "H1: inner unresumed resumption's defer ran exactly once during the outer drain");
  CHECK(kctor_is(e1, "Success") && kas_int(kctor_arg(e1, 0)) == 0,
        "H1: outer abortive clause result == 0 (the recursion did not corrupt it)");

  /* concurrent (multi-worker) under forced GC pressure: forked children each run an
   * abortive clause whose abandoned defer fails.  Exercises the abandonment drain
   * OFF the main fiber with a live concurrent allocator + repeated run_main, so a
   * collection can land mid-drain (the GC-under-retention shape the review asked
   * for).  Names arrays MUST be `static` here: krec() stores the names pointer
   * verbatim (codegen emits a static literal), so a stack array would dangle under
   * concurrent forking — a harness contract, not a runtime requirement. */
  krt2_new(2);
  for (int rep = 0; rep < 50; rep++) {
    KValue *ec = krt2_run_main(scenarioConc());
    if (!kctor_is(ec, "Success")) { fails++; fprintf(stderr, "  FAIL: Conc rep %d not Success\n", rep); break; }
    if ((rep & 3) == 0) GC_gcollect();
  }
  CHECK(atomic_load(&conc_count) == NKIDS * 50,
        "Conc: every concurrent abandoned-defer failure surfaced as Failure(Fail cleanup) (50x24)");

  if (fails == 0) {
    fprintf(stderr, "PASS: abandon_cause (nested-drain recursion + escaping drain-fail composition; multi-worker)\n");
    return 0;
  }
  fprintf(stderr, "FAIL: abandon_cause (%d checks failed)\n", fails);
  return 1;
}
