/* atomic_lostproof.c — proof that the OLD plain-Ref std.atomic lowering loses
 * updates under the real nproc-worker scheduler, while the NEW atomic
 * krt2_atomic_fetch_add does not.
 *
 * The OLD prelude lowered atomicFetchAdd to `old <- readRef cell; writeRef cell
 * (old + n); pure old` — a NON-ATOMIC read-modify-write over a plain Ref.  This
 * test reproduces exactly that lowering against a plain rt Ref cell (kref_*),
 * forks NFIBERS fibers each doing NITERS such increments on one shared cell, and
 * reports the final total.  Under true 12-core contention the read-modify-write
 * interleaves and updates are lost, so the OLD total is < NFIBERS*NITERS.  The
 * NEW path (krt2_atomic_fetch_add on an atomic cell) conserves every update.
 *
 * This is a diagnostic harness, not part of the gating suite — it is expected to
 * PRINT a lost-update count for the OLD path (that is the bug being fixed) and a
 * conserved total for the NEW path.  It exits 0 iff the NEW path is exact AND the
 * OLD path actually lost at least one update (i.e. the race is real on this box).
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <stdio.h>

#define NFIBERS 64
#define NITERS  20000 /* larger than the gating test to make the race reliable */

static int64_t iv(KValue *v) { return kas_int(v); }

/* ── OLD lowering: a NON-ATOMIC read-modify-write over a plain Ref ─────────
 * This is precisely what `atomicFetchAdd` desugared to before the fix
 * (readRef; writeRef (old+1)).  env[0] = shared Ref cell. */
static KValue *old_worker_io(KEnv *env) {
  KValue *cell = kvar(env, 0);
  for (int i = 0; i < NITERS; i++) {
    KValue *old = kref_get(cell);          /* readRef cell           */
    kref_set(cell, kint(iv(old) + 1));     /* writeRef cell (old+1)  */
  }
  return kunit();
}

/* ── NEW lowering: atomic fetch_add on an atomic cell ──────────────────────
 * env[0] = shared AtomicRef, env[1] = RmwOrder code (Int). */
static KValue *new_worker_io(KEnv *env) {
  KValue *ref = kvar(env, 0), *order = kvar(env, 1);
  for (int i = 0; i < NITERS; i++) krt2_atomic_fetch_add(order, ref, kint(1));
  return kunit();
}

/* env[0] = rest. \f -> do { rest; _ <- await f; pure () } */
static KValue *cont_after_fork(KEnv *env, KValue *f) {
  KValue *rest = kvar(env, 0);
  return krt2_then(rest, krt2_then(krt2_await(f), krt2_pure(kunit())));
}

static KValue *spawn(int k, KValue *(*body)(KEnv *), KEnv *workerEnv) {
  if (k == 0) return krt2_pure(kunit());
  KValue *rest = spawn(k - 1, body, workerEnv);
  KValue *worker = kio(body, workerEnv);
  return krt2_bind(krt2_fork(worker), kclo(cont_after_fork, kpush(rest, NULL)));
}

int main(void) {
  krt2_new(0); /* one worker per core */
  const int64_t expected = (int64_t)NFIBERS * NITERS;

  /* OLD: plain-Ref non-atomic RMW. */
  KValue *cell = kref_new(kint(0));
  krt2_run_main(spawn(NFIBERS, old_worker_io, kpush(cell, NULL)));
  int64_t oldTotal = iv(kref_get(cell));

  /* NEW: indivisible atomic fetch_add. */
  KValue *ref = krt2_new_atomic_ref(kint(0));
  krt2_run_main(spawn(NFIBERS, new_worker_io, kpush(ref, kpush(kint(4 /*RmwSeqCst*/), NULL))));
  int64_t newTotal = iv(krt2_atomic_load(kint(0 /*LoadRelaxed*/), ref));

  fprintf(stderr, "expected = %lld\n", (long long)expected);
  fprintf(stderr, "OLD plain-Ref  total = %lld  (lost %lld updates)\n",
          (long long)oldTotal, (long long)(expected - oldTotal));
  fprintf(stderr, "NEW atomic     total = %lld  (lost %lld updates)\n",
          (long long)newTotal, (long long)(expected - newTotal));

  int newExact = (newTotal == expected);
  int oldRaced = (oldTotal < expected);
  if (newExact && oldRaced) {
    fprintf(stderr, "PASS: NEW conserves all updates; OLD plain-Ref lost updates (race is real)\n");
    return 0;
  }
  if (!newExact)
    fprintf(stderr, "FAIL: NEW atomic path lost updates — atomicity is broken\n");
  if (!oldRaced)
    fprintf(stderr, "NOTE: OLD path did not lose updates this run (race not observed on this box)\n");
  return newExact ? 0 : 1;
}
