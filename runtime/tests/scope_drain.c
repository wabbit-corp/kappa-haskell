/* scope_drain.c — regressions for two structured-concurrency fixes:
 *
 *   #5  krt2_run_main must drain the ROOT scope on exit: a root-level forked
 *       child that is never awaited must be interrupted (and its finalizers
 *       run) before run_main returns, rather than abandoned when the workers
 *       are joined.  We fork a child that blocks forever on a never-completed
 *       promise, with an `ensuring` finalizer that records it ran; main returns
 *       without awaiting it.  After run_main, the finalizer MUST have run.
 *
 *   #3  krt2_with_scope must return the BODY's result (IO e a), not Unit, and
 *       run the shutdown via `ensuring` (not `then`).  withScope (\s -> pure 42)
 *       must yield Exit Success 42.
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <stdio.h>
#include <stdatomic.h>

static int fails = 0;
#define CHECK(c, m) do { if (!(c)) { fprintf(stderr, "  FAIL: %s\n", m); fails++; } } while (0)

/* ── #5: root-scope drain ─────────────────────────────────────────────── */

static _Atomic int child_finalized = 0;

static KValue *set_finalized(KEnv *env) { (void)env; atomic_store(&child_finalized, 1); return kunit(); }

/* The root child: ensuring(do { complete ready; awaitExit block }, setFinalized).
 * It completes `ready` only AFTER its `ensuring` frame is installed and its body
 * is entered, then blocks forever on `block`.  So once main observes `ready`,
 * a subsequent interrupt is guaranteed to unwind through the ensuring frame and
 * run the finalizer — making the drain's effect deterministic (an interrupt that
 * beat the body's entry would legitimately skip the finalizer, bracket-style). */
static KValue *make_child(KValue *ready, KValue *block) {
  KValue *signal = krt2_complete_promise(ready, krt2_success(kunit()));
  KValue *body = krt2_then(signal, krt2_await_promise_exit(block));
  return krt2_ensuring(body, kio(set_finalized, NULL));
}

/* env[0]=ready, arg=block: fork the child, await `ready`, then return (drain). */
static KValue *k_block(KEnv *env, KValue *block) {
  KValue *ready = kvar(env, 0);
  return krt2_then(krt2_fork(make_child(ready, block)),
                   krt2_then(krt2_await_promise_exit(ready), krt2_pure(kunit())));
}
static KValue *k_ready(KEnv *env, KValue *ready) {
  (void)env;
  return krt2_bind(krt2_new_promise(), kclo(k_block, kpush(ready, NULL)));
}
static KValue *drain_main(void) {
  return krt2_bind(krt2_new_promise(), kclo(k_ready, NULL));
}

/* ── #3: withScope returns the body's result ──────────────────────────── */

static KValue *ws_body(KEnv *env, KValue *s) { (void)env; (void)s; return krt2_pure(kint(42)); }

int main(void) {
  /* #5 */
  krt2_new(0);
  KValue *e1 = krt2_run_main(drain_main());
  CHECK(kctor_is(e1, "Success"), "drain: main Exit == Success");
  CHECK(atomic_load(&child_finalized) == 1,
        "drain: unawaited root child was interrupted + its finalizer ran (no leak)");

  /* #3 — fresh runtime (also exercises the g_rt reset: run_main is reusable) */
  KValue *e2 = krt2_run_main(krt2_with_scope(kclo(ws_body, NULL)));
  CHECK(kctor_is(e2, "Success"), "withScope: Exit == Success");
  CHECK(e2->as.ctor.argc == 1 && e2->as.ctor.args[0]->tag == K_INT
            && e2->as.ctor.args[0]->as.i == 42,
        "withScope: returns the body's result 42, not Unit");

  if (fails == 0) { fprintf(stderr, "PASS: scope_drain (root drain + withScope result + run_main reuse)\n"); return 0; }
  fprintf(stderr, "FAIL: scope_drain (%d checks failed)\n", fails);
  return 1;
}
