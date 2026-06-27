/* abandon_perform.c — §32.2.20 PERFORM-DURING-DRAIN.  An abandoned-slice `defer`
 * that PERFORMS an algebraic op into an INTERVENING enclosing handler must thread
 * its performed result EXACTLY like ordinary scope exit threads such a defer —
 * native MUST equal the sound interpreter.
 *
 * Shape (the minimal "tell-add-5", spec value = 5):
 *
 *   handle TELL (deep-summing) {            -- return _ -> pure 0
 *     handle ABORT (abortive) {             -- go p k -> pure 0   (k IGNORED)
 *       doscope {
 *         defer (perform TELL.tell 5)       -- performs into the OUTER handler
 *         perform ABORT.go ()               -- abandons -> drains the do-scope
 *         pure 7
 *       }
 *     }
 *   }
 *
 * The deep TELL handler folds each `tell n` into the SUM of the tells performed by
 * the rest of the computation: `tell n -> \k -> bind (resume k ()) (\rest -> n+rest)`,
 * `return _ -> pure 0`.  So the whole expression's value is the SUM of every tell
 * that reaches the handler.  Exactly one tell (5) is performed — by the abandoned
 * `defer` during the drain — so the SOUND value is 5.
 *
 * The pre-fix bug (§32.2.20): begin_abandon_drain captured ae->kont = f->k INCLUDING
 * the intervening TELL KK_HANDLER and spliced KK_ABANDEND as next = ae->kont.  When
 * the defer performed `tell 5` during the drain and the TELL handler resumed, the
 * resume re-spliced through that terminal; on completion KK_ABANDEND did
 * `f->k = ae->kont`, HARD-OVERWRITING the resume-spliced continuation — so the
 * performed `+5` was computed then ORPHANED and the abort clause's post-value (0)
 * reached the TELL return, yielding 0 instead of 5.
 *
 * A CONTROL scenario threads the SAME `defer (perform TELL.tell 5)` through an
 * ORDINARY scope exit (no abort/abandon — the body just falls off the end): it too
 * must yield 5, proving §32.2.20's "same masked-LIFO order/semantics as ordinary
 * scope exit".  And a TWO-TELL variant (a tell BEFORE the abort + the abandoned
 * defer's tell) pins the §32.2.13 deep-sum interaction (spec value 3+5 = 8).
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <gc.h>
#include <stdio.h>
#include <stdatomic.h>

static int fails = 0;
#define CHECK(c, m) do { if (!(c)) { fprintf(stderr, "  FAIL: %s\n", m); fails++; } } while (0)

/* ── deep-summing TELL handler ──────────────────────────────────────────────
 * tell n -> \k -> bind (resume k ()) (\rest -> pure (n + rest))
 * return _ -> pure 0
 * Each `tell n` adds n to the sum of the tells the continuation performs; the
 * handled expression evaluates to the total of every tell that reaches here. */
static KValue *tell_add(KEnv *env, KValue *rest) {       /* \rest -> pure (n + rest) */
  int64_t n = kas_int(kvar(env, 0));                     /* n captured in env slot 0 */
  return krt2_pure(kint(n + kas_int(rest)));
}
static KValue *tell_clause_k(KEnv *env, KValue *k) {     /* \k -> bind (k ()) (n+·)  */
  int64_t n = kas_int(kvar(env, 0));                     /* n captured in env slot 0 */
  return krt2_bind(kapp(k, kunit()), kclo(tell_add, kpush(kint(n), NULL)));
}
static KValue *tell_clause(KEnv *e, KValue *n) { (void)e;  /* \n -> \k -> ...        */
  return kclo(tell_clause_k, kpush(n, NULL)); }
static KValue *tell_ret(KEnv *e, KValue *x) { (void)e; (void)x; return krt2_pure(kint(0)); }

static KValue *with_tell(KValue *body) {                 /* handle TELL (deep) body  */
  static const char *names[1] = { "tell" };
  KValue *vals[1]      = { kclo(tell_clause, NULL) };
  return krt2_handle(kbool(1), kstr0("TELL"), kclo(tell_ret, NULL), krec(1, names, vals), body);
}

/* ── abortive ABORT handler (ignores its continuation) ──────────────────────
 * go p -> \k -> pure 0    (k IGNORED => the body's do-scope is abandoned)
 * return x -> pure x */
static KValue *abort_clause_k(KEnv *e, KValue *k) { (void)e; (void)k; return krt2_pure(kint(0)); }
static KValue *abort_clause(KEnv *e, KValue *p) { (void)e; (void)p; return kclo(abort_clause_k, NULL); }
static KValue *abort_ret(KEnv *e, KValue *x) { (void)e; return krt2_pure(x); }
static KValue *with_abort(KValue *body) {
  static const char *names[1] = { "go" };
  KValue *vals[1]      = { kclo(abort_clause, NULL) };
  return krt2_handle(kbool(1), kstr0("ABORT"), kclo(abort_ret, NULL), krec(1, names, vals), body);
}

/* a `defer (perform TELL.tell N)` — the abandoned-slice defer that performs. */
static KValue *defer_tell(int64_t n) {
  return krt2_defer(krt2_then(krt2_perform(kstr0("TELL"), kstr0("tell"), kint(n)),
                              krt2_pure(kunit())));
}

/* =========================================================================
 * MINIMAL: one abandoned-defer tell.  SOUND VALUE = 5.
 *   doscope { defer (tell 5); perform ABORT.go (); pure 7 }
 * ====================================================================== */
static KValue *minimal_inner(void) {
  KValue *after = krt2_then(krt2_perform(kstr0("ABORT"), kstr0("go"), kunit()), krt2_pure(kint(7)));
  return krt2_doscope(krt2_then(defer_tell(5), after));
}
static KValue *scenarioMinimal(void) { return with_tell(with_abort(minimal_inner())); }

/* =========================================================================
 * CONTROL: the SAME defer over an ORDINARY scope exit — no abort/abandon, the
 * body simply completes; its defer's `tell 5` must thread identically.  SOUND = 5.
 *   doscope { defer (tell 5); pure 7 }
 * (still under the abort handler so the two scenarios are structurally identical
 * except for whether the body abandons.)
 * ====================================================================== */
static KValue *control_inner(void) {
  return krt2_doscope(krt2_then(defer_tell(5), krt2_pure(kint(7))));
}
static KValue *scenarioControl(void) { return with_tell(with_abort(control_inner())); }

/* =========================================================================
 * TWO-TELL (§32.2.13 deep-sum interaction): a tell BEFORE the abort (3) PLUS the
 * abandoned defer's tell (5).  The pre-abort tell folds the continuation's tells
 * (which include the abandoned defer's) => SOUND VALUE = 3 + 5 = 8.
 *   doscope { defer (tell 5); perform TELL.tell 3; perform ABORT.go (); pure 7 }
 * ====================================================================== */
static KValue *two_inner(void) {
  KValue *after = krt2_then(krt2_perform(kstr0("TELL"), kstr0("tell"), kint(3)),
                  krt2_then(krt2_perform(kstr0("ABORT"), kstr0("go"), kunit()),
                            krt2_pure(kint(7))));
  return krt2_doscope(krt2_then(defer_tell(5), after));
}
static KValue *scenarioTwo(void) { return with_tell(with_abort(two_inner())); }

/* =========================================================================
 * RESUME-THEN-MORE: the abandoned defer performs tell 5, the TELL handler resumes,
 * and the resumed drain continuation performs ANOTHER tell 4 (in the SAME defer
 * after the first tell).  Both must thread => SOUND VALUE = 5 + 4 = 9.  This pins
 * that the resume-spliced continuation (which the fix preserves at c->next) itself
 * stays able to perform again.
 *   doscope { defer (tell 5; tell 4); perform ABORT.go (); pure 7 }
 * ====================================================================== */
static KValue *defer_two_tells(void) {
  return krt2_defer(
      krt2_then(krt2_perform(kstr0("TELL"), kstr0("tell"), kint(5)),
      krt2_then(krt2_perform(kstr0("TELL"), kstr0("tell"), kint(4)),
                krt2_pure(kunit()))));
}
static KValue *resume_more_inner(void) {
  KValue *after = krt2_then(krt2_perform(kstr0("ABORT"), kstr0("go"), kunit()), krt2_pure(kint(7)));
  return krt2_doscope(krt2_then(defer_two_tells(), after));
}
static KValue *scenarioResumeMore(void) { return with_tell(with_abort(resume_more_inner())); }

static int success_int(KValue *ex, int64_t want) {
  return kctor_is(ex, "Success") && kctor_argc(ex) == 1 && kas_int(kctor_arg(ex, 0)) == want;
}

int main(void) {
  krt2_new(1);  /* single worker: sequential program on the main fiber */

  /* CONTROL first: ordinary scope exit threads the performing defer => 5. */
  KValue *ectl = krt2_run_main(scenarioControl());
  CHECK(success_int(ectl, 5),
        "control: ordinary scope-exit defer (perform tell 5) threads => Success 5");

  /* MINIMAL: the abandoned defer's perform must thread identically => 5
   * (pre-fix native yielded 0 — the +5 was computed then orphaned). */
  KValue *emin = krt2_run_main(scenarioMinimal());
  CHECK(success_int(emin, 5),
        "minimal: abandoned-slice defer (perform tell 5) threads during the drain => Success 5 "
        "(pre-fix: orphaned, == 0)");

  /* TWO-TELL: pre-abort tell 3 deep-sums with the abandoned defer's tell 5 => 8. */
  KValue *etwo = krt2_run_main(scenarioTwo());
  CHECK(success_int(etwo, 8),
        "two-tell: tell 3 (pre-abort) deep-sums the abandoned defer's tell 5 => Success 8");

  /* RESUME-THEN-MORE: a defer that performs twice (5 then 4) — the resume-spliced
   * drain continuation must itself stay performable => 5 + 4 = 9. */
  KValue *erm = krt2_run_main(scenarioResumeMore());
  CHECK(success_int(erm, 9),
        "resume-more: abandoned defer performs tell 5 then tell 4 across resumes => Success 9");

  if (fails == 0) {
    fprintf(stderr, "PASS: abandon_perform (perform-during-drain threads into the enclosing handler; native==sound)\n");
    return 0;
  }
  fprintf(stderr, "FAIL: abandon_perform (%d checks failed)\n", fails);
  return 1;
}
