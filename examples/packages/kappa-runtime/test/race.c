/* race.c (test) — race and timeout (§18.1.6).
 *
 *   R1: race (sleep 50ms; pure 1)  (pure 2)   => RaceWonRight (Success 2)
 *       the right side wins instantly; the sleeping left side is interrupted.
 *   R2: race (pure 1)  (sleep 50ms; pure 2)   => RaceWonLeft  (Success 1)
 *   R3: timeout 10ms (sleep 1s; pure 9)       => TimeoutFired (action interrupted)
 *   R4: timeout 1s (pure 7)                   => TimeoutDone  (Success 7)
 *
 * All four complete in milliseconds: a regression that fails to interrupt the
 * loser / the timed-out action would make this wait out the 50ms and 1s sleeps,
 * so the test also asserts the whole run finishes well under 1 second.
 *
 * Expected stdout: R1:ok / R2:ok / R3:ok / R4:ok / DONE
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

static KValue *sleep_then(long ns, long v) {
  return krt2_then(krt2_sleep_for(kint(ns)), krt2_pure(kint(v)));
}
/* result is `Won<Side> (Success v)` ? */
static int won_with(KValue *r, const char *side, long v) {
  if (!kctor_is(r, side)) return 0;
  KValue *ex = kctor_arg(r, 0);
  return kctor_is(ex, "Success") && kas_int(kctor_arg(ex, 0)) == v;
}

static KValue *r4_k(KEnv *e, KValue *r4) {  /* timeout 1s (pure 7) => TimeoutDone (Success 7) */
  (void)e;
  int ok = kctor_is(r4, "TimeoutDone") && kctor_is(kctor_arg(r4, 0), "Success") &&
           kas_int(kctor_arg(kctor_arg(r4, 0), 0)) == 7;
  return krt2_then(krt2_println_c(ok ? "R4:ok" : "R4:bad"), krt2_println_c("DONE"));
}
static KValue *r3_k(KEnv *e, KValue *r3) {  /* timeout 10ms (sleep 1s) => TimeoutFired */
  (void)e;
  return krt2_then(krt2_println_c(kctor_is(r3, "TimeoutFired") ? "R3:ok" : "R3:bad"),
                   krt2_bind(krt2_timeout(kint(1000000000LL), krt2_pure(kint(7))), kclo(r4_k, NULL)));
}
static KValue *r2_k(KEnv *e, KValue *r2) {  /* race (pure 1) (slow) => RaceWonLeft 1 */
  (void)e;
  return krt2_then(krt2_println_c(won_with(r2, "RaceWonLeft", 1) ? "R2:ok" : "R2:bad"),
                   krt2_bind(krt2_timeout(kint(10000000LL), sleep_then(1000000000LL, 9)), kclo(r3_k, NULL)));
}
static KValue *r1_k(KEnv *e, KValue *r1) {  /* race (slow) (pure 2) => RaceWonRight 2 */
  (void)e;
  return krt2_then(krt2_println_c(won_with(r1, "RaceWonRight", 2) ? "R1:ok" : "R1:bad"),
                   krt2_bind(krt2_race(krt2_pure(kint(1)), sleep_then(50000000LL, 2)), kclo(r2_k, NULL)));
}
static KValue *program(void) {
  return krt2_bind(krt2_race(sleep_then(50000000LL, 1), krt2_pure(kint(2))), kclo(r1_k, NULL));
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

  char out[512];
  KValue *exitv = capture_run(program(), out, sizeof out);

  clock_gettime(CLOCK_MONOTONIC, &t1);
  double secs = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9;

  const char *expected = "R1:ok\nR2:ok\nR3:ok\nR4:ok\nDONE\n";
  int ok = 1;
  if (strcmp(out, expected) != 0) { fprintf(stderr, "FAIL: output\n--exp--\n%s--got--\n%s", expected, out); ok = 0; }
  if (!kctor_is(exitv, "Success")) { fprintf(stderr, "FAIL: Exit not Success\n"); ok = 0; }
  if (secs > 1.0) { fprintf(stderr, "FAIL: took %.2fs — loser/timed-out fiber not interrupted\n", secs); ok = 0; }
  if (ok) { fprintf(stderr, "PASS: race + timeout (first-wins, loser interrupted, tie-break) in %.3fs\n", secs); return 0; }
  return 1;
}
