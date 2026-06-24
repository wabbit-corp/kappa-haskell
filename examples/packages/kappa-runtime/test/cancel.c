/* cancel.c — the cancellation surface (§18.1.12): acquireRelease (bracket) and
 * mask/restore (uninterruptibleMask), matching ZIO's semantics.
 *
 * AR (acquireRelease): the RELEASE runs even when USE is interrupted, and USE is
 * interruptible while acquire/release are not (§18.1.12, ZIO acquireReleaseWith).
 *
 *   fork (acquireRelease (print "AR:acquired")
 *                        (\_ -> print "AR:released")
 *                        (\_ -> sleep 30s))      -- use is interruptible
 *   sleep 10ms; interrupt it                      -- interrupt waits for release
 *   => AR:acquired, AR:released   (in ms, not 30s)
 *
 * MR (mask/restore): a `restore`d inner region is interruptible even though the
 * surrounding mask is not, so the interrupt is delivered inside it and the code
 * after `restore` never runs.
 *
 *   fork (mask (\restore -> print "MR:in-mask"; restore (sleep 30s); print "MR:after"))
 *   sleep 10ms; interrupt it
 *   => MR:in-mask   (MR:after NOT printed; the restored sleep was interrupted)
 *
 * Expected stdout: AR:acquired / AR:released / MR:in-mask / DONE
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define SLEEP_30S kint(30000000000LL)
#define SLEEP_10MS kint(10000000LL)

static KValue *ar_release(KEnv *e, KValue *r) { (void)e; (void)r; return krt2_println_c("AR:released"); }
static KValue *ar_use(KEnv *e, KValue *r)     { (void)e; (void)r; return krt2_sleep_for(SLEEP_30S); }

static KValue *mr_body(KEnv *e, KValue *restore) {  /* \restore -> in-mask; restore(sleep); after */
  (void)e;
  return krt2_then(krt2_println_c("MR:in-mask"),
         krt2_then(kapp(restore, krt2_sleep_for(SLEEP_30S)),
                   krt2_println_c("MR:after")));
}

static KValue *k_fMR(KEnv *e, KValue *fMR) {        /* sleep; interrupt; DONE */
  (void)e;
  return krt2_then(krt2_sleep_for(SLEEP_10MS),
         krt2_then(krt2_interrupt(fMR),
                   krt2_println_c("DONE")));
}
static KValue *k_fAR(KEnv *e, KValue *fAR) {        /* sleep; interrupt AR; then start MR */
  (void)e;
  KValue *maskAction = krt2_mask(kclo(mr_body, NULL));
  return krt2_then(krt2_sleep_for(SLEEP_10MS),
         krt2_then(krt2_interrupt(fAR),
                   krt2_bind(krt2_fork(maskAction), kclo(k_fMR, NULL))));
}
static KValue *program(void) {
  KValue *ar = krt2_acquire_release(krt2_println_c("AR:acquired"),
                                    kclo(ar_release, NULL), kclo(ar_use, NULL));
  return krt2_bind(krt2_fork(ar), kclo(k_fAR, NULL));
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
  struct timespec t0, t1;
  clock_gettime(CLOCK_MONOTONIC, &t0);

  char out[512];
  KValue *exitv = capture_run(program(), out, sizeof out);

  clock_gettime(CLOCK_MONOTONIC, &t1);
  double secs = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9;

  const char *expected = "AR:acquired\nAR:released\nMR:in-mask\nDONE\n";
  int ok = 1;
  if (strcmp(out, expected) != 0) { fprintf(stderr, "FAIL: output\n--exp--\n%s--got--\n%s", expected, out); ok = 0; }
  if (!kctor_is(exitv, "Success")) { fprintf(stderr, "FAIL: Exit not Success\n"); ok = 0; }
  if (secs > 1.0) { fprintf(stderr, "FAIL: %.2fs — release/restored-use not interrupted\n", secs); ok = 0; }
  if (ok) { fprintf(stderr, "PASS: cancel (acquireRelease release-on-interrupt + mask/restore) in %.3fs\n", secs); return 0; }
  return 1;
}
