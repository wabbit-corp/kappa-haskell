/* stm_retry.c (test) — STM `retry` (park-until-changed) and `orElse`.
 *
 * retry: a consumer commits `do x <- readTVar tv; check (x > 0); writeTVar tv (x-1); pure x`.
 *   With tv=0 the check fails, so the transaction RETRIES and the fiber parks on
 *   tv's watcher list.  A later `atomically (writeTVar tv 5)` commit wakes it; it
 *   re-runs, reads 5, decrements to 4, and returns 5.  (If retry busy-looped or
 *   the watcher wakeup were missing, this would spin or hang.)
 *
 * orElse: `atomically (retry orElse pure 42)` runs the right branch because the
 *   left retried, yielding 42.
 *
 * Expected stdout: retry-ok / orElse-ok / DONE
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

/* consumer txn: readTVar tv >>= \x -> check(x>0) >> writeTVar tv (x-1) >> pure x */
static KValue *c_k3(KEnv *e, KValue *ign) { (void)ign; return krt2_stm_pure(kvar(e, 0)); } /* pure x */
static KValue *c_k2(KEnv *e, KValue *ign) { (void)ign;                                     /* writeTVar tv (x-1) >> pure x */
  KValue *tv = kvar(e, 0), *x = kvar(e, 1);
  return krt2_stm_bind(krt2_write_tvar(tv, kp_subInt(x, kint(1))), kclo(c_k3, kpush(x, NULL)));
}
static KValue *c_k1(KEnv *e, KValue *x) {                                                  /* check(x>0) >> ... */
  KValue *tv = kvar(e, 0);
  return krt2_stm_bind(krt2_check(kp_ltInt(kint(0), x)), kclo(c_k2, kpush(tv, kpush(x, NULL))));
}
static KValue *consumer_txn(KValue *tv) {
  return krt2_stm_bind(krt2_read_tvar(tv), kclo(c_k1, kpush(tv, NULL)));
}

/* \exit -> check Success 5, then the orElse test, then DONE */
static KValue *orelse_k(KEnv *e, KValue *r) { (void)e;                                     /* orElse result */
  return krt2_then(krt2_println_c(kas_int(r) == 42 ? "orElse-ok" : "orElse-bad"),
                   krt2_println_c("DONE"));
}
static KValue *after_consumer(KEnv *e, KValue *exitv) {
  (void)e;
  int ok = kctor_is(exitv, "Success") && kas_int(kctor_arg(exitv, 0)) == 5;
  KValue *orelse = krt2_atomically(krt2_or_else(krt2_retry(), krt2_stm_pure(kint(42))));
  return krt2_then(krt2_println_c(ok ? "retry-ok" : "retry-bad"),
                   krt2_bind(orelse, kclo(orelse_k, NULL)));
}
/* \consumer -> sleep; writeTVar tv 5 (wakes the parked retry); await consumer */
static KValue *k_consumer(KEnv *e, KValue *consumer) {
  KValue *tv = kvar(e, 0);
  return krt2_then(krt2_sleep_for(kint(10000000LL)),               /* let it park on retry */
         krt2_then(krt2_atomically(krt2_write_tvar(tv, kint(5))),  /* wakes the consumer   */
                   krt2_bind(krt2_await(consumer), kclo(after_consumer, NULL))));
}
/* \tv -> fork consumer; k_consumer */
static KValue *k_tv(KEnv *e, KValue *tv) {
  (void)e;
  return krt2_bind(krt2_fork(krt2_atomically(consumer_txn(tv))), kclo(k_consumer, kpush(tv, NULL)));
}
static KValue *program(void) {
  return krt2_bind(krt2_atomically(krt2_new_tvar(kint(0))), kclo(k_tv, NULL));
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
  setenv("KAPPA_RT_WORKERS", "1", 1);   /* deterministic output ordering */
  krt2_new(1);
  struct timespec t0, t1;
  clock_gettime(CLOCK_MONOTONIC, &t0);

  char out[128];
  KValue *exitv = capture_run(program(), out, sizeof out);

  clock_gettime(CLOCK_MONOTONIC, &t1);
  double secs = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9;

  int ok = 1;
  if (strcmp(out, "retry-ok\norElse-ok\nDONE\n") != 0) { fprintf(stderr, "FAIL: %s", out); ok = 0; }
  if (!kctor_is(exitv, "Success")) { fprintf(stderr, "FAIL: Exit not Success\n"); ok = 0; }
  if (secs > 1.0) { fprintf(stderr, "FAIL: %.2fs (retry not parking?)\n", secs); ok = 0; }
  if (ok) { fprintf(stderr, "PASS: stm_retry (retry parks+wakes, orElse) in %.3fs\n", secs); return 0; }
  return 1;
}
