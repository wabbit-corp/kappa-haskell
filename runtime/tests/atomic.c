/* atomic.c — §29.1 AtomicRef: single-thread semantics + multicore lock-free
 * contention.  Part A exercises every operation's return value and effect on a
 * single thread (atomic ops do not suspend, so they are called directly).  Part
 * B forks NFIBERS fibers across the worker pool, each doing NITERS atomic
 * fetch_add(1) on one shared cell; if the cell is truly lock-free the total is
 * conserved exactly (a non-atomic increment would lose updates under real
 * 12-core contention).
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <stdio.h>

#define NFIBERS 64
#define NITERS  2000 /* total fetch_adds = NFIBERS * NITERS */

/* Order constructors, built with the §29.1 canonical tag ids. */
static KValue *load_relaxed(void)     { return kctor0(0, "LoadRelaxed"); }
static KValue *store_relaxed(void)    { return kctor0(0, "StoreRelaxed"); }
static KValue *rmw_relaxed(void)      { return kctor0(0, "RmwRelaxed"); }
static KValue *rmw_seqcst(void)       { return kctor0(4, "RmwSeqCst"); }
static KValue *cas_fail_relaxed(void) { return kctor0(0, "CasFailRelaxed"); }

static int fails = 0;
#define CHECK(cond, msg) do { if (!(cond)) { fprintf(stderr, "  FAIL: %s\n", msg); fails++; } } while (0)

static int64_t iv(KValue *v) { return v->as.i; }

/* ── Part A: single-thread semantics ──────────────────────────────────── */
static void semantics(void) {
  KValue *r = krt2_new_atomic_ref(kint(10));
  CHECK(iv(krt2_atomic_load(load_relaxed(), r)) == 10, "load initial == 10");

  krt2_atomic_store(store_relaxed(), r, kint(25));
  CHECK(iv(krt2_atomic_load(load_relaxed(), r)) == 25, "after store == 25");

  KValue *old = krt2_atomic_exchange(rmw_relaxed(), r, kint(7));
  CHECK(iv(old) == 25, "exchange returns old 25");
  CHECK(iv(krt2_atomic_load(load_relaxed(), r)) == 7, "after exchange == 7");

  /* CAS success: expected 7, desired 99 -> Exchanged 7; cell becomes 99. */
  KValue *res = krt2_atomic_compare_exchange(rmw_relaxed(), cas_fail_relaxed(), r, kint(7), kint(99));
  CHECK(kctor_tagid(res) == 0, "CAS success -> Exchanged (tag 0)");
  CHECK(iv(res->as.ctor.args[0]) == 7, "CAS success old == 7");
  CHECK(iv(krt2_atomic_load(load_relaxed(), r)) == 99, "after CAS success == 99");

  /* CAS failure: expected 7 (now 99), desired 0 -> NotExchanged 99; unchanged. */
  KValue *res2 = krt2_atomic_compare_exchange(rmw_relaxed(), cas_fail_relaxed(), r, kint(7), kint(0));
  CHECK(kctor_tagid(res2) == 1, "CAS failure -> NotExchanged (tag 1)");
  CHECK(iv(res2->as.ctor.args[0]) == 99, "CAS failure current == 99");
  CHECK(iv(krt2_atomic_load(load_relaxed(), r)) == 99, "after CAS failure still 99");

  /* fetch-* return the OLD value. */
  CHECK(iv(krt2_atomic_fetch_add(rmw_relaxed(), r, kint(1))) == 99, "fetch_add old 99");
  CHECK(iv(krt2_atomic_load(load_relaxed(), r)) == 100, "after fetch_add == 100");
  CHECK(iv(krt2_atomic_fetch_sub(rmw_relaxed(), r, kint(50))) == 100, "fetch_sub old 100");
  CHECK(iv(krt2_atomic_load(load_relaxed(), r)) == 50, "after fetch_sub == 50");
  CHECK(iv(krt2_atomic_fetch_or(rmw_relaxed(), r, kint(0x0F))) == 50, "fetch_or old 50");
  CHECK(iv(krt2_atomic_load(load_relaxed(), r)) == (50 | 0x0F), "after fetch_or");
  int64_t before_and = iv(krt2_atomic_load(load_relaxed(), r));
  CHECK(iv(krt2_atomic_fetch_and(rmw_relaxed(), r, kint(0x0F))) == before_and, "fetch_and old");
  CHECK(iv(krt2_atomic_load(load_relaxed(), r)) == (before_and & 0x0F), "after fetch_and");
  int64_t before_xor = iv(krt2_atomic_load(load_relaxed(), r));
  CHECK(iv(krt2_atomic_fetch_xor(rmw_relaxed(), r, kint(0xFF))) == before_xor, "fetch_xor old");
  CHECK(iv(krt2_atomic_load(load_relaxed(), r)) == (before_xor ^ 0xFF), "after fetch_xor");

  /* Bool atomic cell (AtomicValue Bool). */
  KValue *b = krt2_new_atomic_ref(kbool(0));
  CHECK(!kctor_is(krt2_atomic_load(load_relaxed(), b), "std.prelude.True"), "bool init False");
  KValue *bold = krt2_atomic_exchange(rmw_relaxed(), b, kbool(1));
  CHECK(!kctor_is(bold, "std.prelude.True"), "bool exchange old False");
  CHECK(kctor_is(krt2_atomic_load(load_relaxed(), b), "std.prelude.True"), "bool after exchange True");
}

/* ── Part B: multicore contention ─────────────────────────────────────── */

/* env: var0 = shared AtomicRef, var1 = RmwOrder. */
static KValue *worker_io(KEnv *env) {
  KValue *ref = kvar(env, 0), *order = kvar(env, 1);
  for (int i = 0; i < NITERS; i++) krt2_atomic_fetch_add(order, ref, kint(1));
  return kunit();
}

/* \f -> do { rest; _ <- await f; pure () }   (rest captured in env[0]). */
static KValue *cont_after_fork(KEnv *env, KValue *f) {
  KValue *rest = kvar(env, 0);
  return krt2_then(rest, krt2_then(krt2_await(f), krt2_pure(kunit())));
}

static KValue *spawn_workers(int k, KValue *ref, KValue *order) {
  if (k == 0) return krt2_pure(kunit());
  KValue *rest = spawn_workers(k - 1, ref, order);
  KValue *worker = kio(worker_io, kpush(ref, kpush(order, NULL)));
  return krt2_bind(krt2_fork(worker), kclo(cont_after_fork, kpush(rest, NULL)));
}

static void contention(void) {
  KValue *ref = krt2_new_atomic_ref(kint(0));
  KValue *exitv = krt2_run_main(spawn_workers(NFIBERS, ref, rmw_seqcst()));
  CHECK(kctor_is(exitv, "Success"), "contention program Exit == Success");
  int64_t total = iv(krt2_atomic_load(load_relaxed(), ref));
  if (total != (int64_t)NFIBERS * NITERS) {
    fprintf(stderr, "  FAIL: total = %lld, expected %lld (lost updates!)\n",
            (long long)total, (long long)NFIBERS * NITERS);
    fails++;
  }
}

int main(void) {
  krt2_new(0); /* one worker per core — true parallelism */
  semantics();
  contention();
  if (fails == 0) {
    fprintf(stderr, "PASS: atomic (semantics + %d fibers x %d fetch_add conserved = %d)\n",
            NFIBERS, NITERS, NFIBERS * NITERS);
    return 0;
  }
  fprintf(stderr, "FAIL: atomic (%d checks failed)\n", fails);
  return 1;
}
