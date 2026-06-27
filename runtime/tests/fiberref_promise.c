/* fiberref_promise.c — §18.1.7 FiberRef copy-on-fork independence + §18.11
 * Promise.poll/isDone, stressed under TRUE multicore parallelism and heavy GC
 * pressure (REVIEW gate: a GC stress when the fork/promise path is touched).
 *
 * The program (built as a krt2 action tree and run on the M:N scheduler):
 *   main = do
 *     ref <- newFiberRef 0
 *     setFiberRef ref SENTINEL            -- parent's visible value
 *     spawnAll N                          -- fork N children, await each
 *     parentNow <- getFiberRef ref        -- MUST still be SENTINEL
 *     if parentNow == SENTINEL then print "ok" else print "BAD:<v>"
 *
 *   child k = do
 *     inherited <- getFiberRef ref        -- the SNAPSHOT taken at fork (SENTINEL)
 *     _ <- modifyFiberRef ref (\x -> x + (k+1))   -- mutate THIS fiber's copy
 *     p <- newPromise
 *     _ <- completePromise p (Success inherited)
 *     m <- pollPromise p                  -- Some (Success inherited), non-blocking
 *     d <- isDonePromise p                -- True
 *     -- assert in-program: inherited == SENTINEL and the peek agrees, else fail
 *     churn                               -- heap pressure for concurrent GC
 *     pure ()
 *
 * If any child saw a non-SENTINEL inherited value (i.e. a sibling's mutation
 * leaked across the copy-on-fork boundary) it fails the whole computation with a
 * typed error, so the terminal Exit is Failure — caught by the assertion.  The
 * happens-before of each await makes the output deterministic.
 *
 * Expected stdout: "ok\n"; terminal Exit: Success ().  Repeated REPS times with
 * a tight GC trigger so collections interleave the fork/promise/fiberref churn.
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define N 256
#define REPS 20
#define SENTINEL 1000

/* the FiberRef handle for the current program build (a static => a GC root). */
static KValue *g_ref;

/* pure (a -> a): add `delta` (captured in env[0]) to the inherited value. */
static KValue *add_delta(KEnv *env, KValue *x) {
  return kint(kas_int(x) + kas_int(kvar(env, 0)));
}

/* churn the heap: build a chain of boxed conses so Boehm GC has work to do. */
static KValue *churn_chain(int depth) {
  KValue *acc = kint(0);
  for (int i = 0; i < depth; i++) {
    KValue *args[2] = { kint(i), acc };
    acc = kctor(KCT_OTHER, "Box", 2, args);
  }
  return acc;
}

/* \d -> if isDone then (\m -> assert inherited, peek) else fail.  We thread the
 * inherited value (env[0]) and the poll result (env[1]) through.  The assertion
 * is: inherited == SENTINEL AND poll == Some (Success inherited). */
static KValue *child_check(KEnv *env, KValue *isDoneV) {
  KValue *inherited = kvar(env, 0);
  KValue *pollV = kvar(env, 1);
  int ok = 1;
  if (kas_int(inherited) != SENTINEL) ok = 0;             /* copy-on-fork independence */
  if (!kctor_is(pollV, "Some")) ok = 0;                   /* non-blocking peek saw it  */
  else {
    KValue *ex = kctor_arg(pollV, 0);
    if (!kctor_is(ex, "Success")) ok = 0;
    else if (kas_int(kctor_arg(ex, 0)) != SENTINEL) ok = 0;
  }
  if (!kas_bool(isDoneV)) ok = 0;                          /* isDone agrees with poll   */
  (void)churn_chain(48);
  if (!ok) return krt2_throw(kint(-1));                    /* fail the fiber (caught up top) */
  return krt2_pure(kunit());
}
/* \m -> bind isDone, then check. */
static KValue *child_after_poll(KEnv *env, KValue *pollV) {
  KValue *inherited = kvar(env, 0), *prom = kvar(env, 1);
  return krt2_bind(krt2_is_done_promise(prom),
                   kclo(child_check, kpush(inherited, kpush(pollV, NULL))));
}
/* \_completed -> bind poll, then continue. */
static KValue *child_after_complete(KEnv *env, KValue *completedV) {
  (void)completedV;
  KValue *inherited = kvar(env, 0), *prom = kvar(env, 1);
  return krt2_bind(krt2_poll_promise(prom),
                   kclo(child_after_poll, kpush(inherited, kpush(prom, NULL))));
}
/* \p -> completePromise p (Success inherited); ... */
static KValue *child_with_promise(KEnv *env, KValue *prom) {
  KValue *inherited = kvar(env, 0);
  KValue *complete = krt2_complete_promise(prom, krt2_success(inherited));
  return krt2_bind(complete, kclo(child_after_complete, kpush(inherited, kpush(prom, NULL))));
}
/* \inherited -> modify own copy; newPromise; ... (id captured in env[0]). */
static KValue *child_with_inherited(KEnv *env, KValue *inherited) {
  int id = (int)kas_int(kvar(env, 0));
  KValue *doMod = krt2_modify_fiber_ref(g_ref, kclo(add_delta, kpush(kint(id + 1), NULL)));
  return krt2_then(doMod,
                   krt2_bind(krt2_new_promise(),
                             kclo(child_with_promise, kpush(inherited, NULL))));
}
static KValue *child_body(int id) {
  return krt2_bind(krt2_get_fiber_ref(g_ref),
                   kclo(child_with_inherited, kpush(kint(id), NULL)));
}

/* spawn child k, then the rest, then await child k (fan-out before fan-in). */
static KValue *await_then(KEnv *env, KValue *f) {
  KValue *rest = kvar(env, 0);
  return krt2_then(rest, krt2_then(krt2_await(f), krt2_pure(kunit())));
}
static KValue *spawn_all(int k); /* fwd */

/* after all children awaited: read the parent's cell; print ok iff SENTINEL. */
static KValue *parent_check(KEnv *env, KValue *parentNow) {
  (void)env;
  if (kas_int(parentNow) == SENTINEL) return krt2_println_c("ok");
  return krt2_println_c("BAD");
}
static KValue *after_forks(KEnv *env, KValue *unit) {
  (void)env; (void)unit;
  return krt2_bind(krt2_get_fiber_ref(g_ref), kclo(parent_check, NULL));
}
static KValue *spawn_all(int k) {
  if (k < 0) return krt2_bind(krt2_pure(kunit()), kclo(after_forks, NULL));
  KValue *rest = spawn_all(k - 1);
  return krt2_bind(krt2_fork(child_body(k)), kclo(await_then, kpush(rest, NULL)));
}

/* \ref -> setFiberRef ref SENTINEL; spawnAll; parentCheck. */
static KValue *with_ref(KEnv *env, KValue *ref) {
  (void)env;
  g_ref = ref;
  return krt2_then(krt2_set_fiber_ref(g_ref, kint(SENTINEL)), spawn_all(N - 1));
}
static KValue *program(void) {
  return krt2_bind(krt2_new_fiber_ref(kint(0)), kclo(with_ref, NULL));
}

static KValue *capture_run(KValue *prog, char *buf, size_t n) {
  fflush(stdout);
  int saved = dup(STDOUT_FILENO);
  FILE *tmp = tmpfile();
  dup2(fileno(tmp), STDOUT_FILENO);
  KValue *exitv = krt2_run_main(prog);
  fflush(stdout);
  dup2(saved, STDOUT_FILENO);
  close(saved);
  fseek(tmp, 0, SEEK_SET);
  size_t got = fread(buf, 1, n - 1, tmp);
  buf[got] = '\0';
  fclose(tmp);
  return exitv;
}

int main(void) {
  krt2_new(0);   /* one worker per core (true parallelism) */

  for (int rep = 0; rep < REPS; rep++) {
    char out[256];
    g_ref = NULL;
    KValue *exitv = capture_run(program(), out, sizeof out);

    if (!kctor_is(exitv, "Success")) {
      fprintf(stderr, "FAIL[rep %d]: Exit not Success (%s) — a child saw a leaked "
                      "sibling value or a poll/isDone mismatch\n",
              rep, kctor_name(exitv));
      return 1;
    }
    if (strcmp(out, "ok\n") != 0) {
      fprintf(stderr, "FAIL[rep %d]: output = \"%s\" (parent cell mutated by a child?)\n",
              rep, out);
      return 1;
    }
  }

  fprintf(stderr, "PASS: fiberref_promise (%d children x %d reps: copy-on-fork "
                  "independence + poll/isDone, GC-stressed)\n", N, REPS);
  return 0;
}
