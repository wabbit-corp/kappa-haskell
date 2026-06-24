/* stm.c (test) — STM serializability under real parallelism (§32.2.9).
 *
 * Two account TVars start at 100 each (total 200).  K=16 worker fibers, running
 * on all cores, each perform M=200 atomic transfers of 1 unit between the two
 * accounts (alternating direction).  3200 transactions contend on just 2 TVars,
 * so commits conflict constantly and re-run — exactly the path that exposes
 * lost updates and torn (value,version) reads.  If `atomically` is serializable,
 * the conserved total is STILL exactly 200 at the end.
 *
 *   transfer ai aj = atomically (do a <- readTVar ai
 *                                   b <- readTVar aj
 *                                   writeTVar ai (a-1)
 *                                   writeTVar aj (b+1))
 *
 * Expected stdout: STM:conserved
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define INIT 100
#define K 16
#define M 200

/* ── the transfer transaction ───────────────────────────────────────────── */
static KValue *t_k3(KEnv *e, KValue *ign) { (void)ign;            /* writeTVar aj (b+1) */
  return krt2_write_tvar(kvar(e, 0), kp_addInt(kvar(e, 1), kint(1)));
}
static KValue *t_k2(KEnv *e, KValue *b) {                          /* writeTVar ai (a-1) >> t_k3 */
  KValue *ai = kvar(e, 0), *aj = kvar(e, 1), *a = kvar(e, 2);
  return krt2_stm_bind(krt2_write_tvar(ai, kp_subInt(a, kint(1))),
                       kclo(t_k3, kpush(aj, kpush(b, NULL))));
}
static KValue *t_k1(KEnv *e, KValue *a) {                          /* readTVar aj >>= t_k2 */
  KValue *ai = kvar(e, 0), *aj = kvar(e, 1);
  return krt2_stm_bind(krt2_read_tvar(aj), kclo(t_k2, kpush(ai, kpush(aj, kpush(a, NULL)))));
}
static KValue *transfer_stm(KValue *ai, KValue *aj) {              /* readTVar ai >>= t_k1 */
  return krt2_stm_bind(krt2_read_tvar(ai), kclo(t_k1, kpush(ai, kpush(aj, NULL))));
}

/* ── a worker: M transfers via a while loop over a counter ref ──────────── */
static KValue *w_cond_k(KEnv *e, KValue *n) { (void)e; return krt2_pure(kp_ltInt(kint(0), n)); } /* n > 0 */
static KValue *w_dec_k(KEnv *e, KValue *n)  { return krt2_write_ref(kvar(e, 0), kp_subInt(n, kint(1))); }
static KValue *w_with_ref(KEnv *e, KValue *i) {
  KValue *from = kvar(e, 0), *to = kvar(e, 1);
  KValue *cond = krt2_bind(krt2_read_ref(i), kclo(w_cond_k, NULL));
  KValue *body = krt2_then(krt2_atomically(transfer_stm(from, to)),
                           krt2_bind(krt2_read_ref(i), kclo(w_dec_k, kpush(i, NULL))));
  return krt2_while(cond, body);
}
static KValue *worker(KValue *from, KValue *to) {
  return krt2_bind(krt2_new_ref(kint(M)), kclo(w_with_ref, kpush(from, kpush(to, NULL))));
}

/* ── fan out K workers, fan them back in ────────────────────────────────── */
static KValue *sw_await(KEnv *e, KValue *f) {    /* run `rest` (fork more) FIRST, then await f */
  return krt2_then(kvar(e, 0), krt2_then(krt2_await(f), krt2_pure(kunit())));
}
static KValue *spawn_workers(int k, KValue *a0, KValue *a1) {
  if (k == 0) return krt2_pure(kunit());
  KValue *from = (k % 2 == 0) ? a0 : a1;
  KValue *to   = (k % 2 == 0) ? a1 : a0;
  KValue *rest = spawn_workers(k - 1, a0, a1);
  return krt2_bind(krt2_fork(worker(from, to)), kclo(sw_await, kpush(rest, NULL)));
}

/* ── read the total, assert conservation ────────────────────────────────── */
static KValue *tot_k2(KEnv *e, KValue *b) { return krt2_stm_pure(kp_addInt(kvar(e, 0), b)); }
static KValue *tot_k1(KEnv *e, KValue *a) {
  return krt2_stm_bind(krt2_read_tvar(kvar(e, 0)), kclo(tot_k2, kpush(a, NULL)));
}
static KValue *total_stm(KValue *a0, KValue *a1) {
  return krt2_stm_bind(krt2_read_tvar(a0), kclo(tot_k1, kpush(a1, NULL)));
}
static KValue *after_tot(KEnv *e, KValue *tot) {
  (void)e;
  if (kas_int(tot) == K * 0 + 2 * INIT) return krt2_println_c("STM:conserved");
  char buf[32]; snprintf(buf, sizeof buf, "STM:total=%lld", (long long)kas_int(tot));
  return krt2_println_c(buf);
}
static KValue *m_k1(KEnv *e, KValue *a1) {
  KValue *a0 = kvar(e, 0);
  return krt2_then(spawn_workers(K, a0, a1),
                   krt2_bind(krt2_atomically(total_stm(a0, a1)), kclo(after_tot, NULL)));
}
static KValue *m_k0(KEnv *e, KValue *a0) {
  (void)e;
  return krt2_bind(krt2_atomically(krt2_new_tvar(kint(INIT))), kclo(m_k1, kpush(a0, NULL)));
}
static KValue *program(void) {
  return krt2_bind(krt2_atomically(krt2_new_tvar(kint(INIT))), kclo(m_k0, NULL));
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
  krt2_new(0);   /* all cores — real parallel commits */
  char out[128];
  KValue *exitv = capture_run(program(), out, sizeof out);
  int ok = 1;
  if (strcmp(out, "STM:conserved\n") != 0) { fprintf(stderr, "FAIL: %s", out); ok = 0; }
  if (!kctor_is(exitv, "Success")) { fprintf(stderr, "FAIL: Exit not Success\n"); ok = 0; }
  if (ok) { fprintf(stderr, "PASS: stm (%d fibers x %d transfers, serializable, total conserved)\n", K, M); return 0; }
  return 1;
}
