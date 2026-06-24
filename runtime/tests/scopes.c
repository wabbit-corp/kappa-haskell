/* scopes.c — structured concurrency, interruption, and monitors.
 *
 * Program (sugared):
 *
 *   do sc    <- newScope
 *      child <- forkIn sc (do sleepFor 30s; printlnString "UNREACHABLE")
 *      mon   <- monitor child
 *      shutdownScope sc            -- interrupts child (ScopeShutdown), awaits it
 *      printlnString "scope drained"
 *      exit  <- awaitMonitor mon   -- child already terminated; observe its Exit
 *      case exit of
 *        Failure (Interrupt (InterruptCause ScopeShutdown _)) -> "child interrupted: ScopeShutdown"
 *        _                                                     -> "BUG"
 *
 * The child parks on a 30-SECOND timer.  If interruption works, shutdownScope
 * cancels it and the whole program finishes in milliseconds with:
 *
 *   scope drained
 *   child interrupted: ScopeShutdown
 *
 * A regression (interruption not delivered to a parked fiber, or shutdownScope
 * not waiting) would either hang ~30s, print "UNREACHABLE", or report "BUG".
 * The test fails if it does not complete well under the sleep duration.
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

static KValue *child_body(void) {
  return krt2_then(krt2_sleep_for(kint(30000000000LL)),   /* 30 s in ns */
                   krt2_println_c("UNREACHABLE"));
}

/* \exit -> classify the child's terminal Exit */
static KValue *k_exit(KEnv *env, KValue *exitv) {
  (void)env;
  if (kctor_is(exitv, "Failure")) {
    KValue *cause = kctor_arg(exitv, 0);
    if (kctor_is(cause, "Interrupt")) {
      KValue *ic = kctor_arg(cause, 0);
      if (kctor_is(ic, "InterruptCause") &&
          kctor_is(kctor_arg(ic, 0), "ScopeShutdown"))
        return krt2_println_c("child interrupted: ScopeShutdown");
      return krt2_println_c("child interrupted: other tag");
    }
    return krt2_println_c("child failed: non-interrupt cause");
  }
  return krt2_println_c("BUG: child completed");
}

/* \mon -> shutdownScope sc; "scope drained"; awaitMonitor mon >>= k_exit
 *  (sc captured in env[0]) */
static KValue *k_mon(KEnv *env, KValue *mon) {
  KValue *sc = kvar(env, 0);
  return krt2_then(krt2_shutdown_scope(sc),
         krt2_then(krt2_println_c("scope drained"),
                   krt2_bind(krt2_await_monitor(mon), kclo(k_exit, NULL))));
}

/* \child -> monitor child >>= k_mon   (sc threaded through env[0]) */
static KValue *k_child(KEnv *env, KValue *child) {
  return krt2_bind(krt2_monitor(child), kclo(k_mon, env));  /* env still = [sc] */
}

/* \sc -> forkIn sc child >>= k_child   (capture sc in env[0] for later) */
static KValue *k_scope(KEnv *env, KValue *sc) {
  (void)env;
  return krt2_bind(krt2_fork_in(sc, child_body()), kclo(k_child, kpush(sc, NULL)));
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
  krt2_new(0);

  struct timespec t0, t1;
  clock_gettime(CLOCK_MONOTONIC, &t0);

  KValue *prog = krt2_bind(krt2_new_scope(), kclo(k_scope, NULL));
  char out[512];
  KValue *exitv = capture_run(prog, out, sizeof out);

  clock_gettime(CLOCK_MONOTONIC, &t1);
  double secs = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9;

  const char *expected =
      "scope drained\n"
      "child interrupted: ScopeShutdown\n";

  int ok = 1;
  if (strcmp(out, expected) != 0) {
    fprintf(stderr, "FAIL: output mismatch\n--- expected ---\n%s--- got ---\n%s", expected, out);
    ok = 0;
  }
  if (!kctor_is(exitv, "Success")) {
    fprintf(stderr, "FAIL: main Exit not Success (%s)\n", kctor_name(exitv));
    ok = 0;
  }
  if (secs > 5.0) {                       /* the 30 s child sleep must NOT be waited */
    fprintf(stderr, "FAIL: took %.2fs — interruption did not cancel the sleeping child\n", secs);
    ok = 0;
  }
  if (ok) {
    fprintf(stderr, "PASS: scopes (forkIn + monitor + shutdownScope interrupts & awaits child) in %.3fs\n", secs);
    return 0;
  }
  return 1;
}
