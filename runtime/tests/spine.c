/* spine.c — end-to-end test of the kappart2 v1 spine.
 *
 * Builds ONE Kappa IO program as a KValue action tree and runs it on the real
 * M:N scheduler + libuv reactor.  It exercises, in one go: bind/then/pure, fork,
 * a one-shot promise (new/await/complete), a libuv timer (sleepFor), a typed
 * failure caught by catchIO, and cross-fiber wakeup (the main fiber parks on the
 * promise; the child wakes it from the reactor after the timer fires).
 *
 * The program (sugared):
 *
 *   catchIO
 *     (do let p <- newPromise
 *         _ <- fork (do sleepFor 5ms
 *                       printlnString "child: completing"
 *                       _ <- completePromise p (Success ())
 *                       pure ())
 *         _ <- awaitPromiseExit p           -- parks until the child completes p
 *         printlnString "main: got promise"
 *         throwIO "boom")                    -- typed failure
 *     (\_ -> printlnString "caught")          -- handler recovers
 *
 * Expected stdout (deterministic with KAPPA_RT_WORKERS=1):
 *
 *   child: completing
 *   main: got promise
 *   caught
 *
 * and the terminal Exit is Success () (catchIO recovered the failure).
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* The child fiber's body, parameterized by the promise handle `p`. */
static KValue *child_body(KValue *p) {
  return krt2_then(krt2_sleep_for(kint(5000000)),         /* 5 ms in ns */
         krt2_then(krt2_println_c("child: completing"),
         krt2_then(krt2_complete_promise(p, krt2_success(kunit())),
                   krt2_pure(kunit()))));
}

/* \exit -> printlnString "main: got promise"; throwIO "boom" */
static KValue *k_after_promise(KEnv *env, KValue *exit_unused) {
  (void)env; (void)exit_unused;
  return krt2_then(krt2_println_c("main: got promise"),
                   krt2_throw(kstr0("boom")));
}

/* \p -> fork child; awaitPromiseExit p >>= k_after_promise */
static KValue *k_with_promise(KEnv *env, KValue *p) {
  (void)env;
  return krt2_then(krt2_fork(child_body(p)),
                   krt2_bind(krt2_await_promise_exit(p), kclo(k_after_promise, NULL)));
}

/* \err -> printlnString "caught" */
static KValue *handler(KEnv *env, KValue *err) {
  (void)env; (void)err;
  return krt2_println_c("caught");
}

/* Run `prog` with the kappa program's stdout redirected into a temp file, then
 * read it back so we can assert the exact output. */
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
  setenv("KAPPA_RT_WORKERS", "1", 1);   /* deterministic interleaving */
  krt2_new(1);

  KValue *body = krt2_bind(krt2_new_promise(), kclo(k_with_promise, NULL));
  KValue *prog = krt2_catch(body, kclo(handler, NULL));

  char out[1024];
  KValue *exitv = capture_run(prog, out, sizeof out);

  const char *expected =
      "child: completing\n"
      "main: got promise\n"
      "caught\n";

  int ok = 1;
  if (strcmp(out, expected) != 0) {
    fprintf(stderr, "FAIL: output mismatch\n--- expected ---\n%s--- got ---\n%s", expected, out);
    ok = 0;
  }
  if (!kctor_is(exitv, "Success")) {
    fprintf(stderr, "FAIL: terminal Exit is not Success (got %s)\n", kctor_name(exitv));
    ok = 0;
  }
  if (ok) {
    fprintf(stderr, "PASS: spine (fork/await/promise/sleep/throw-catch on the M:N scheduler)\n");
    return 0;
  }
  return 1;
}
