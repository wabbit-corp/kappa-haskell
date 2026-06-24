/* stm_orelse.c (test) — orElse write isolation (§32.2.9 / REVIEW.md M17).
 *
 * The STM-review BLOCKER: when orElse's left branch retries, its writes MUST be
 * discarded, including writes that OVERWROTE a value set before the orElse.
 *
 *   atomically (writeTVar tv 100 >> orElse (writeTVar tv 200 >> retry) (readTVar tv))
 *
 * The left branch writes 200 then retries, so its 200 is rolled back; the right
 * branch then reads tv and sees the pre-orElse 100 (read-after-write of the
 * surviving write).  The transaction returns 100 and commits 100.  The pre-fix
 * in-place write-set returned/committed 200 — a lost-write / isolation violation.
 *
 * Expected stdout: orelse-ok
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static KValue *const_k(KEnv *e, KValue *ign) { (void)ign; return kvar(e, 0); }  /* \_ -> env[0] */

/* \_ -> orElse (writeTVar tv 200 >> retry) (readTVar tv)   (env=[tv]) */
static KValue *orelse_after_w(KEnv *e, KValue *ign) {
  (void)ign;
  KValue *tv = kvar(e, 0);
  KValue *L = krt2_stm_bind(krt2_write_tvar(tv, kint(200)), kclo(const_k, kpush(krt2_retry(), NULL)));
  KValue *R = krt2_read_tvar(tv);
  return krt2_or_else(L, R);
}
static KValue *orelse_txn(KValue *tv) {
  return krt2_stm_bind(krt2_write_tvar(tv, kint(100)), kclo(orelse_after_w, kpush(tv, NULL)));
}

/* \final -> check r (env[0]) == 100 and final == 100 */
static KValue *check_k(KEnv *e, KValue *final_) {
  KValue *r = kvar(e, 0);
  int ok = kas_int(r) == 100 && kas_int(final_) == 100;
  if (ok) return krt2_println_c("orelse-ok");
  char buf[48]; snprintf(buf, sizeof buf, "orelse-bad: r=%lld final=%lld",
                         (long long)kas_int(r), (long long)kas_int(final_));
  return krt2_println_c(buf);
}
/* \r -> read tv again, then check */
static KValue *after_orelse(KEnv *e, KValue *r) {
  KValue *tv = kvar(e, 0);
  return krt2_bind(krt2_atomically(krt2_read_tvar(tv)), kclo(check_k, kpush(r, NULL)));
}
/* \tv -> atomically(orelse_txn tv) >>= after_orelse */
static KValue *k_tv(KEnv *e, KValue *tv) {
  (void)e;
  return krt2_bind(krt2_atomically(orelse_txn(tv)), kclo(after_orelse, kpush(tv, NULL)));
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
  krt2_new(1);
  char out[128];
  KValue *exitv = capture_run(program(), out, sizeof out);
  int ok = (strcmp(out, "orelse-ok\n") == 0) && kctor_is(exitv, "Success");
  if (!ok) fprintf(stderr, "FAIL: %s", out);
  else fprintf(stderr, "PASS: stm_orelse (left-branch writes discarded on retry)\n");
  return ok ? 0 : 1;
}
