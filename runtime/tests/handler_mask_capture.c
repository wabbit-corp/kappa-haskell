/* handler_mask_capture.c -- Spec section 32.2.13 dynamic mask capture.
 *
 * A handled body and its operation clause may each have a distinct active mask
 * frame.  The resumption must run with the body's captured frame, then return
 * to the clause's frame.  Abandonment must likewise drain the captured segment
 * under the body's frame.  Treating mask_top as ambient Fiber state makes both
 * paths pop the wrong frame and trap with a mask-stack mismatch. */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <stdio.h>

static int fails = 0;
#define CHECK(c, m) do { if (!(c)) { fprintf(stderr, "  FAIL: %s\n", m); fails++; } } while (0)

static KValue *ret_clause(KEnv *env, KValue *value) {
  (void)env;
  return krt2_pure(value);
}

/* Body: mask (\_ -> perform E.go ()). */
static KValue *masked_body(KEnv *env, KValue *restore) {
  (void)env;
  (void)restore;
  return krt2_perform(kstr0("E"), kstr0("go"), kunit());
}

/* Resume scenario clause: \_ -> \k -> mask (\_ -> k 7). */
static KValue *resume_inside_clause_mask(KEnv *env, KValue *restore) {
  (void)restore;
  return kapp(kvar(env, 0), kint(7));
}

static KValue *resume_clause_k(KEnv *env, KValue *resumption) {
  (void)env;
  return krt2_mask(kclo(resume_inside_clause_mask, kpush(resumption, NULL)));
}

static KValue *resume_clause(KEnv *env, KValue *payload) {
  (void)env;
  (void)payload;
  return kclo(resume_clause_k, NULL);
}

/* Abandon scenario clause: \_ -> \_ -> mask (\_ -> pure 99). */
static KValue *abandon_inside_clause_mask(KEnv *env, KValue *restore) {
  (void)env;
  (void)restore;
  return krt2_pure(kint(99));
}

static KValue *abandon_clause_k(KEnv *env, KValue *resumption) {
  (void)env;
  (void)resumption;
  return krt2_mask(kclo(abandon_inside_clause_mask, NULL));
}

static KValue *abandon_clause(KEnv *env, KValue *payload) {
  (void)env;
  (void)payload;
  return kclo(abandon_clause_k, NULL);
}

static KValue *scenario(KValue *clause) {
  const char *names[1] = { "go" };
  KValue *values[1] = { clause };
  KValue *ops = krec(1, names, values);
  return krt2_handle(
      kbool(1), kstr0("E"), kclo(ret_clause, NULL), ops,
      krt2_mask(kclo(masked_body, NULL)));
}

int main(void) {
  krt2_new(1);

  KValue *resumed = krt2_run_main(scenario(kclo(resume_clause, NULL)));
  CHECK(kctor_is(resumed, "Success"), "resume under a clause-local mask succeeds");
  CHECK(kctor_argc(resumed) == 1 && kas_int(kctor_arg(resumed, 0)) == 7,
        "resumed body returns 7");

  KValue *abandoned = krt2_run_main(scenario(kclo(abandon_clause, NULL)));
  CHECK(kctor_is(abandoned, "Success"), "abandonment under a clause-local mask succeeds");
  CHECK(kctor_argc(abandoned) == 1 && kas_int(kctor_arg(abandoned, 0)) == 99,
        "abortive clause returns 99");

  if (fails == 0) {
    fprintf(stderr, "PASS: handler_mask_capture (resume and abandonment restore dynamic masks)\n");
    return 0;
  }
  fprintf(stderr, "FAIL: handler_mask_capture (%d checks failed)\n", fails);
  return 1;
}
