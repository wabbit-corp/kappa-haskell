/* finalizer_cause.c — §32.2.12 / §18.7 failing-finalizer cause composition on the
 * ORDINARY scope-unwind path (review finding C2; fix 3).  Before the fix the
 * KK_FINSEQ unwind arm did `f->k = c->next; continue;` when a finalizer itself
 * failed: it DROPPED the scope's remaining LIFO-later finalizers (a §18.7
 * exactly-once violation) and propagated a BARE cause with NO `Then` composition
 * of the failing finalizer with the reason the scope was already exiting with.
 *
 * After the fix:
 *   - a finalizer that fails does NOT abandon the remaining finalizers — they all
 *     still run (§18.7: "All deferred actions in the scope are attempted, even if
 *     some deferred actions propagate monadic errors");
 *   - the failing finalizer's cause is composed with the incoming reason via
 *     §32.2.12 `Then` (body-fail then cleanup-fail => Then(body, cleanup));
 *   - the composed cause propagates once the sequence completes.
 *
 * Scenarios:
 *   A. body SUCCEEDS; two defers, the LIFO-FIRST (registered last) throws.  Both
 *      defers must run; the propagated Exit is Failure(Fail "d-first") (cleanup
 *      cause only — there is no body failure to compose with).
 *   B. body FAILS ("boom"); two defers, the LIFO-FIRST throws.  Both defers run;
 *      the propagated Exit is Failure(Then (Fail "boom") (Fail "d-first")).
 *   C. concurrent (krt2_new(>1)): N forked children each run scenario B; every
 *      awaited child Exit is the composed Then, proving the path is correct under
 *      real multi-worker scheduling (review: add a multi-worker case).
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <gc.h>
#include <stdio.h>
#include <stdatomic.h>
#include <string.h>

static int fails = 0;
#define CHECK(c, m) do { if (!(c)) { fprintf(stderr, "  FAIL: %s\n", m); fails++; } } while (0)

/* ── A: body succeeds; the LIFO-first defer throws ──────────────────────── */
static _Atomic int a_d_late = 0, a_d_early = 0;
static KValue *a_mark_late(KEnv *e)  { (void)e; atomic_store(&a_d_late, 1);  return kunit(); }
static KValue *a_mark_early(KEnv *e) { (void)e; atomic_store(&a_d_early, 1); return kunit(); }
static KValue *a_body(void) {
  /* doscope { defer d_late; defer (d_early; throw "d-first"); pure 0 }
   * defer registered LAST (d_early) runs FIRST (LIFO). */
  KValue *early = krt2_then(kio(a_mark_early, NULL), krt2_throw(kstr0("d-first")));
  return krt2_doscope(
      krt2_then(krt2_defer(kio(a_mark_late, NULL)),
      krt2_then(krt2_defer(early),
                krt2_pure(kint(0)))));
}

/* ── B: body fails "boom"; same two defers ──────────────────────────────── */
static _Atomic int b_d_late = 0, b_d_early = 0;
static KValue *b_mark_late(KEnv *e)  { (void)e; atomic_store(&b_d_late, 1);  return kunit(); }
static KValue *b_mark_early(KEnv *e) { (void)e; atomic_store(&b_d_early, 1); return kunit(); }
static KValue *b_body(void) {
  KValue *early = krt2_then(kio(b_mark_early, NULL), krt2_throw(kstr0("d-first")));
  return krt2_doscope(
      krt2_then(krt2_defer(kio(b_mark_late, NULL)),
      krt2_then(krt2_defer(early),
                krt2_throw(kstr0("boom")))));
}

/* ── cause matchers ─────────────────────────────────────────────────────── */
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

/* ── C: concurrent — fork N children running B's shape, await each Exit ──── */
#define NKIDS 32
static _Atomic int c_then_count = 0;
/* the child body: same shape as B but with NON-marking defers (the markers are
 * single global atomics; here we only care about the Exit cause per child). */
static KValue *c_child_body(void) {
  KValue *early = krt2_then(krt2_pure(kunit()), krt2_throw(kstr0("d-first")));
  return krt2_doscope(
      krt2_then(krt2_defer(krt2_pure(kunit())),
      krt2_then(krt2_defer(early),
                krt2_throw(kstr0("boom")))));
}
/* await one child handle and tally if its Exit is the composed Then. */
static KValue *c_after_await(KEnv *e, KValue *exitv) { (void)e;
  if (is_failure_then(exitv, "boom", "d-first")) atomic_fetch_add(&c_then_count, 1);
  return krt2_pure(kunit());
}
static KValue *c_await_child(KEnv *e, KValue *child) { (void)e;
  return krt2_bind(krt2_await(child), kclo(c_after_await, NULL));
}
/* spawn child i, then recurse to spawn the rest, then await them all in order. */
static KValue *c_spawn_then_await(KEnv *env, KValue *unit);
static KValue *c_spawn_one(KEnv *env, KValue *child) {
  int i = (int)kas_int(kvar(env, 0));
  /* await this child, then continue spawning the remaining (i+1..NKIDS). */
  return krt2_then(c_await_child(NULL, child),
                   c_spawn_then_await(kpush(kint(i + 1), NULL), kunit()));
}
static KValue *c_spawn_then_await(KEnv *env, KValue *unit) { (void)unit;
  int i = (int)kas_int(kvar(env, 0));
  if (i >= NKIDS) return krt2_pure(kint(0));
  return krt2_bind(krt2_fork(c_child_body()), kclo(c_spawn_one, kpush(kint(i), NULL)));
}
static KValue *scenarioC(void) { return c_spawn_then_await(kpush(kint(0), NULL), kunit()); }

int main(void) {
  /* ── single-worker A and B ─────────────────────────────────────────────── */
  krt2_new(1);

  KValue *ea = krt2_run_main(a_body());
  CHECK(is_failure_fail(ea, "d-first"), "A: body-success + throwing defer => Failure(Fail d-first)");
  CHECK(atomic_load(&a_d_early) == 1, "A: LIFO-first (throwing) defer RAN");
  CHECK(atomic_load(&a_d_late)  == 1, "A: LIFO-last defer ALSO ran (not dropped after the throw)");

  KValue *eb = krt2_run_main(b_body());
  CHECK(is_failure_then(eb, "boom", "d-first"),
        "B: body-fail + throwing defer => Failure(Then (Fail boom) (Fail d-first))");
  CHECK(atomic_load(&b_d_early) == 1, "B: LIFO-first (throwing) defer RAN");
  CHECK(atomic_load(&b_d_late)  == 1, "B: LIFO-last defer ALSO ran (composed, not dropped)");

  /* ── multi-worker concurrent variant ───────────────────────────────────── */
  krt2_new(4);
  KValue *ec = krt2_run_main(scenarioC());
  CHECK(kctor_is(ec, "Success"), "C: parent completed (children all awaited)");
  CHECK(atomic_load(&c_then_count) == NKIDS,
        "C: every concurrent child's Exit is the composed Then (32/32)");

  if (fails == 0) {
    fprintf(stderr, "PASS: finalizer_cause (failing finalizer composes Then + remaining defers still run; multi-worker)\n");
    return 0;
  }
  fprintf(stderr, "FAIL: finalizer_cause (%d checks failed)\n", fails);
  return 1;
}
