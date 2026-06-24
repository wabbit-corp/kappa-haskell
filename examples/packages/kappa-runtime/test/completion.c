/* completion.c — the do-kernel completion channel (§18.7, §18.8, REVIEW.md B2).
 *
 * One program (run on the main fiber) exercises, in order:
 *
 *   A. defer runs LIFO on NORMAL completion.
 *   B. defer runs on a typed FAILURE that unwinds through the scope (caught outside).
 *   C. a `while` loop counting down a Ref to 0.
 *   D. `break` / `continue` inside a loop.
 *   E. early `return` from a fiber runs the scope's defers and yields the value
 *      (tested in a forked child so the return terminates the child, not main).
 *
 * Expected stdout (deterministic; the main fiber prints serially):
 *
 *   A:body / A:d2 / A:d1            -- defers LIFO, after the body
 *   B:cleanup / B:caught           -- defer ran as the failure unwound, then the handler
 *   C:tick x3
 *   D:1 / D:3                      -- 2 skipped via continue, 4 breaks
 *   E:cleanup / E:returned-ok      -- return ran the defer; child Exit == Success 99
 *   DONE
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* ── A: defer LIFO on normal completion ─────────────────────────────────── */
static KValue *scenarioA(void) {
  return krt2_doscope(
      krt2_then(krt2_defer(krt2_println_c("A:d1")),
      krt2_then(krt2_defer(krt2_println_c("A:d2")),
                krt2_println_c("A:body"))));
}

/* ── B: defer on a caught failure ───────────────────────────────────────── */
static KValue *b_handler(KEnv *env, KValue *err) { (void)env; (void)err; return krt2_println_c("B:caught"); }
static KValue *scenarioB(void) {
  KValue *body = krt2_doscope(
      krt2_then(krt2_defer(krt2_println_c("B:cleanup")),
                krt2_throw(kstr0("boom"))));
  return krt2_catch(body, kclo(b_handler, NULL));
}

/* ── C: while countdown over a Ref ──────────────────────────────────────── */
static KValue *c_cond_k(KEnv *env, KValue *v) { (void)env; return krt2_pure(kp_ltInt(kint(0), v)); } /* 0 < v */
static KValue *c_dec_k(KEnv *env, KValue *v) { return krt2_write_ref(kvar(env, 0), kp_subInt(v, kint(1))); }
static KValue *c_loop(KValue *i) {
  KValue *cond = krt2_bind(krt2_read_ref(i), kclo(c_cond_k, NULL));
  KValue *body = krt2_then(krt2_println_c("C:tick"),
                           krt2_bind(krt2_read_ref(i), kclo(c_dec_k, kpush(i, NULL))));
  return krt2_while(cond, body);
}

/* ── D: break / continue ────────────────────────────────────────────────── */
static KValue *d_body_k(KEnv *env, KValue *v) {
  KValue *j = kvar(env, 0);
  KValue *w = kp_addInt(v, kint(1));
  long wi = kas_int(w);
  KValue *act;
  if (wi == 2) act = krt2_continue();        /* skip printing 2 */
  else if (wi >= 4) act = krt2_break();      /* stop at 4 */
  else { char buf[16]; snprintf(buf, sizeof buf, "D:%ld", wi); act = krt2_println_c(buf); }
  return krt2_then(krt2_write_ref(j, w), act);
}
static KValue *d_loop(KValue *j) {
  KValue *body = krt2_bind(krt2_read_ref(j), kclo(d_body_k, kpush(j, NULL)));
  return krt2_while(krt2_pure(kbool(1)), body);  /* while True, exited by break */
}

/* ── E: return-from-fiber runs defers (in a forked child) ───────────────── */
static KValue *e_child_body(void) {
  return krt2_doscope(
      krt2_then(krt2_defer(krt2_println_c("E:cleanup")),
      krt2_then(krt2_return(kint(99)),
                krt2_println_c("E:unreachable"))));
}
static KValue *e_with_exit(KEnv *env, KValue *exitv) {
  (void)env;
  int ok = kctor_is(exitv, "Success") && kas_int(kctor_arg(exitv, 0)) == 99;
  return krt2_then(krt2_println_c(ok ? "E:returned-ok" : "E:bad"),
                   krt2_println_c("DONE"));
}
static KValue *e_with_child(KEnv *env, KValue *child) {
  (void)env;
  return krt2_bind(krt2_await(child), kclo(e_with_exit, NULL));
}

/* ── sequencing: A; B; (i<-newRef 3; C); (j<-newRef 0; D); (child<-fork E; await) ── */
static KValue *after_j(KEnv *env, KValue *j) {
  (void)env;
  return krt2_then(d_loop(j),
                   krt2_bind(krt2_fork(e_child_body()), kclo(e_with_child, NULL)));
}
static KValue *after_i(KEnv *env, KValue *i) {
  (void)env;
  return krt2_then(c_loop(i),
                   krt2_bind(krt2_new_ref(kint(0)), kclo(after_j, NULL)));
}
static KValue *program(void) {
  return krt2_then(scenarioA(),
         krt2_then(scenarioB(),
                   krt2_bind(krt2_new_ref(kint(3)), kclo(after_i, NULL))));
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
  setenv("KAPPA_RT_WORKERS", "1", 1);   /* deterministic serial output */
  krt2_new(1);

  char out[1024];
  KValue *exitv = capture_run(program(), out, sizeof out);

  const char *expected =
      "A:body\nA:d2\nA:d1\n"
      "B:cleanup\nB:caught\n"
      "C:tick\nC:tick\nC:tick\n"
      "D:1\nD:3\n"
      "E:cleanup\nE:returned-ok\n"
      "DONE\n";

  int ok = 1;
  if (strcmp(out, expected) != 0) {
    fprintf(stderr, "FAIL: output mismatch\n--- expected ---\n%s--- got ---\n%s", expected, out);
    ok = 0;
  }
  if (!kctor_is(exitv, "Success")) {
    fprintf(stderr, "FAIL: main Exit not Success (%s)\n", kctor_name(exitv));
    ok = 0;
  }
  if (ok) {
    fprintf(stderr, "PASS: completion (defer LIFO / fail / return / while / break+continue)\n");
    return 0;
  }
  return 1;
}
