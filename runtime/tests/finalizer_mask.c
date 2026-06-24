/* finalizer_mask.c — regression for R1: finalizers run MASKED, so an async
 * interrupt delivered while a do-scope's defers are unwinding does NOT abandon
 * the scope's remaining defers (§32.2.5, §18.7 exactly-once).
 *
 * Fiber F runs a do-scope with three defers; LIFO run order is d3, d2, d1, each
 * logging its digit.  d2 signals `atDrain` and then blocks on `release`, so the
 * finalizer drain is suspended mid-flight at a known point.  Main awaits
 * `atDrain` (F is now draining, parked inside d2), interrupts F, and completes
 * `release`.  When F wakes inside d2:
 *   - WITHOUT the mask fix: the pending interrupt fires mid-finseq, unwinds out
 *     of the KK_FINSEQ, and abandons d2's tail + d1  ->  log == "3".
 *   - WITH the fix: the drain is masked, so d2 resumes (logs "2") and d1 runs
 *     (logs "1") before the interrupt is delivered  ->  log == "321".
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <stdio.h>
#include <string.h>

static char log_buf[16];
static int  log_n = 0;
static void put(char c) { if (log_n < 15) log_buf[log_n++] = c; }

static KValue *log1(KEnv *e) { (void)e; put('1'); return kunit(); }
static KValue *log2(KEnv *e) { (void)e; put('2'); return kunit(); }
static KValue *log3(KEnv *e) { (void)e; put('3'); return kunit(); }

/* do-scope { defer d1; defer d2; defer d3; pure () }  (installed d1,d2,d3 ->
 * run LIFO d3,d2,d1).  d2 = complete atDrain; awaitExit release; log "2". */
static KValue *make_F(KValue *atDrain, KValue *release) {
  KValue *d1 = kio(log1, NULL);
  KValue *d3 = kio(log3, NULL);
  KValue *d2 = krt2_then(krt2_complete_promise(atDrain, krt2_success(kunit())),
               krt2_then(krt2_await_promise_exit(release), kio(log2, NULL)));
  KValue *body = krt2_then(krt2_defer(d1),
                 krt2_then(krt2_defer(d2),
                 krt2_then(krt2_defer(d3), krt2_pure(kunit()))));
  return krt2_doscope(body);
}

/* env: v0=atDrain, v1=release; arg=fForked. */
static KValue *k3(KEnv *env, KValue *fForked) {
  KValue *atDrain = kvar(env, 0), *release = kvar(env, 1);
  return krt2_then(krt2_await_promise_exit(atDrain),       /* F is now mid-drain at d2 */
         krt2_then(krt2_interrupt_fork(fForked),           /* request interrupt, no wait */
         krt2_then(krt2_complete_promise(release, krt2_success(kunit())), /* unblock d2 */
         krt2_then(krt2_await(fForked), krt2_pure(kunit()))))); /* let F finish */
}
static KValue *k2(KEnv *env, KValue *release) {
  KValue *atDrain = kvar(env, 0);
  return krt2_bind(krt2_fork(make_F(atDrain, release)),
                   kclo(k3, kpush(atDrain, kpush(release, NULL))));
}
static KValue *k1(KEnv *env, KValue *atDrain) {
  (void)env;
  return krt2_bind(krt2_new_promise(), kclo(k2, kpush(atDrain, NULL)));
}
static KValue *mainprog(void) {
  return krt2_bind(krt2_new_promise(), kclo(k1, NULL));
}

int main(void) {
  krt2_new(1); /* single worker — the synchronization is via promises, not timing */
  KValue *ex = krt2_run_main(mainprog());
  log_buf[log_n] = '\0';
  if (strcmp(log_buf, "321") == 0 && kctor_is(ex, "Success")) {
    fprintf(stderr, "PASS: finalizer_mask (interrupt mid-finseq ran all defers LIFO: %s)\n", log_buf);
    return 0;
  }
  fprintf(stderr, "FAIL: finalizer_mask (log=\"%s\", expected \"321\"; Exit %s)\n",
          log_buf, kctor_name(ex));
  return 1;
}
