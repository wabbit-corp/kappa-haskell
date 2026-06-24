/* parallel.c — fan-out / fan-in under TRUE multicore parallelism.
 *
 * Unlike spine.c (which pins KAPPA_RT_WORKERS=1 for byte-exact output), this
 * runs on the DEFAULT worker pool (one per core).  It forks N child fibers
 * before awaiting any of them — so the children run concurrently across the
 * workers — then fans them back in with N awaits.  It validates that the M:N
 * scheduler, the per-object park/wake handshake, and the rt->all GC root set
 * stay correct and crash-free with many concurrent fibers and cross-worker
 * wakeups.  The program's output is deterministic by causal structure, so the
 * assertion is stable regardless of how the workers interleave.
 *
 * Program (sugared), with N = 200:
 *
 *   spawn 0 = printlnString "all 200 forked"
 *   spawn k = do f <- fork (pure k)        -- a child fiber
 *                spawn (k-1)               -- fork the rest FIRST...
 *                _ <- await f              -- ...then fan in
 *                pure ()
 *
 * Expected stdout: "all 200 forked\n"; terminal Exit: Success ().
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define N 200

/* \f -> do { rest; _ <- await f; pure () }   where `rest` is captured in env[0]. */
static KValue *cont_fork(KEnv *env, KValue *f) {
  KValue *rest = kvar(env, 0);
  return krt2_then(rest, krt2_then(krt2_await(f), krt2_pure(kunit())));
}

static KValue *spawn(int k) {
  if (k == 0) return krt2_println_c("all 200 forked");
  KValue *rest = spawn(k - 1);
  return krt2_bind(krt2_fork(krt2_pure(kint(k))),
                   kclo(cont_fork, kpush(rest, NULL)));
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
  krt2_new(0);   /* 0 => one worker per core (true parallelism) */

  char out[256];
  KValue *exitv = capture_run(spawn(N), out, sizeof out);

  int ok = 1;
  if (strcmp(out, "all 200 forked\n") != 0) {
    fprintf(stderr, "FAIL: output = \"%s\"\n", out);
    ok = 0;
  }
  if (!kctor_is(exitv, "Success")) {
    fprintf(stderr, "FAIL: Exit not Success (%s)\n", kctor_name(exitv));
    ok = 0;
  }
  if (ok) { fprintf(stderr, "PASS: parallel (%d fibers fanned out across workers)\n", N); return 0; }
  return 1;
}
