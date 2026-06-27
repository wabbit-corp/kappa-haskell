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
#define REPS    8    /* re-run each contention round so Boehm GC collects mid-flight */

/* Memory orders are passed as Integer CODES (the §29.1 canonical declaration-
 * order index of the order constructor) — NOT ctor tag ids.  This mirrors the
 * std.atomic prelude, which computes the code so the runtime never has to read a
 * codegen-assigned constructor tag (see runtime/atomic.c). */
static KValue *load_relaxed(void)     { return kint(0); }  /* LoadRelaxed    */
static KValue *store_relaxed(void)    { return kint(0); }  /* StoreRelaxed   */
static KValue *rmw_relaxed(void)      { return kint(0); }  /* RmwRelaxed     */
static KValue *rmw_seqcst(void)       { return kint(4); }  /* RmwSeqCst      */
static KValue *cas_fail_relaxed(void) { return kint(0); }  /* CasFailRelaxed */

static int fails = 0;
#define CHECK(cond, msg) do { if (!(cond)) { fprintf(stderr, "  FAIL: %s\n", msg); fails++; } } while (0)

/* UNBOXING Stage 1: an Int value may be a b001 immediate, not a heap K_INT box —
 * read it through kas_int (immediate-safe), never a raw v->as.i deref. */
static int64_t iv(KValue *v) { return kas_int(v); }

/* ── Part A: single-thread semantics ──────────────────────────────────── */
static void semantics(void) {
  KValue *r = krt2_new_atomic_ref(kint(10));
  CHECK(iv(krt2_atomic_load(load_relaxed(), r)) == 10, "load initial == 10");

  krt2_atomic_store(store_relaxed(), r, kint(25));
  CHECK(iv(krt2_atomic_load(load_relaxed(), r)) == 25, "after store == 25");

  KValue *old = krt2_atomic_exchange(rmw_relaxed(), r, kint(7));
  CHECK(iv(old) == 25, "exchange returns old 25");
  CHECK(iv(krt2_atomic_load(load_relaxed(), r)) == 7, "after exchange == 7");

  /* CAS success: expected 7, desired 99 -> witnessed old 7 (== expected, so the
   * prelude reports Exchanged); cell becomes 99.  The runtime now returns only
   * the witnessed value; the Exchanged/NotExchanged shape is reconstructed in
   * source (see std.atomic), so here we check the witnessed value + the effect. */
  KValue *res = krt2_atomic_compare_exchange(rmw_relaxed(), cas_fail_relaxed(), r, kint(7), kint(99));
  CHECK(iv(res) == 7, "CAS success witnessed old == 7 (== expected)");
  CHECK(iv(krt2_atomic_load(load_relaxed(), r)) == 99, "after CAS success == 99");

  /* CAS failure: expected 7 (now 99), desired 0 -> witnessed 99 (!= expected, so
   * the prelude reports NotExchanged); cell unchanged. */
  KValue *res2 = krt2_atomic_compare_exchange(rmw_relaxed(), cas_fail_relaxed(), r, kint(7), kint(0));
  CHECK(iv(res2) == 99, "CAS failure witnessed current == 99 (!= expected)");
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

/* ── Part B: multicore contention (GC-stressed) ───────────────────────── */

/* Build a short boxed-cons chain so Boehm GC has scannable garbage to collect
 * while the contention round runs (the REVIEW gate when a concurrent path is
 * touched: exercise the op under heavy GC pressure). */
static KValue *churn_chain(int depth) {
  KValue *acc = kint(0);
  for (int i = 0; i < depth; i++) {
    KValue *args[2] = { kint(i), acc };
    acc = kctor(KCT_OTHER, "Box", 2, args);
  }
  return acc;
}

/* env: var0 = shared AtomicRef, var1 = RmwOrder code.  Each iteration also
 * allocates a small heap chain, so collections interleave the fetch-adds. */
static KValue *worker_io(KEnv *env) {
  KValue *ref = kvar(env, 0), *order = kvar(env, 1);
  for (int i = 0; i < NITERS; i++) {
    krt2_atomic_fetch_add(order, ref, kint(1));
    (void)churn_chain(8);
  }
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
  /* Each rep starts a fresh shared cell and re-forks all workers, so the GC runs
   * repeatedly across the lifetime of contended atomic cells. */
  for (int rep = 0; rep < REPS; rep++) {
    KValue *ref = krt2_new_atomic_ref(kint(0));
    KValue *exitv = krt2_run_main(spawn_workers(NFIBERS, ref, rmw_seqcst()));
    CHECK(kctor_is(exitv, "Success"), "contention program Exit == Success");
    int64_t total = iv(krt2_atomic_load(load_relaxed(), ref));
    if (total != (int64_t)NFIBERS * NITERS) {
      fprintf(stderr, "  FAIL[rep %d]: fetch_add total = %lld, expected %lld (lost updates!)\n",
              rep, (long long)total, (long long)NFIBERS * NITERS);
      fails++;
    }
  }
}

/* ── Part C: CAS-loop contention ───────────────────────────────────────────
 * Each fiber increments the shared cell NITERS times with a retrying CAS loop
 * (load; CAS(old, old+1); retry on contention).  A CAS that is not a real
 * hardware compare-exchange would let two fibers both read `old` and both store
 * `old+1`, losing one increment; a true lock-free CAS conserves every one.  The
 * witnessed value the CAS returns == `expected` exactly when the swap won. */
static KValue *cas_worker_io(KEnv *env) {
  KValue *ref = kvar(env, 0), *order = kvar(env, 1), *fail = kvar(env, 2);
  for (int i = 0; i < NITERS; i++) {
    for (;;) {
      KValue *old = krt2_atomic_load(load_relaxed(), ref);
      KValue *witnessed =
        krt2_atomic_compare_exchange(order, fail, ref, old, kint(iv(old) + 1));
      if (iv(witnessed) == iv(old)) break; /* won the CAS (witnessed == expected) */
    }
    (void)churn_chain(8); /* GC pressure between increments */
  }
  return kunit();
}

/* env[0]=rest. \f -> do { rest; _ <- await f; pure () } */
static KValue *cas_cont_after_fork(KEnv *env, KValue *f) {
  KValue *rest = kvar(env, 0);
  return krt2_then(rest, krt2_then(krt2_await(f), krt2_pure(kunit())));
}

static KValue *spawn_cas_workers(int k, KValue *ref, KValue *order, KValue *fail) {
  if (k == 0) return krt2_pure(kunit());
  KValue *rest = spawn_cas_workers(k - 1, ref, order, fail);
  KValue *worker = kio(cas_worker_io, kpush(ref, kpush(order, kpush(fail, NULL))));
  return krt2_bind(krt2_fork(worker), kclo(cas_cont_after_fork, kpush(rest, NULL)));
}

static void cas_contention(void) {
  for (int rep = 0; rep < REPS; rep++) {
    KValue *ref = krt2_new_atomic_ref(kint(0));
    KValue *exitv = krt2_run_main(spawn_cas_workers(NFIBERS, ref, rmw_seqcst(), cas_fail_relaxed()));
    CHECK(kctor_is(exitv, "Success"), "CAS contention program Exit == Success");
    int64_t total = iv(krt2_atomic_load(load_relaxed(), ref));
    if (total != (int64_t)NFIBERS * NITERS) {
      fprintf(stderr, "  FAIL[rep %d]: CAS total = %lld, expected %lld (lost updates!)\n",
              rep, (long long)total, (long long)NFIBERS * NITERS);
      fails++;
    }
  }
}

int main(void) {
  krt2_new(0); /* one worker per core — true parallelism */
  semantics();
  contention();
  cas_contention();
  if (fails == 0) {
    fprintf(stderr,
            "PASS: atomic (semantics + %d fibers x %d fetch_add + %d fibers x %d CAS-loop"
            " conserved = %d each)\n",
            NFIBERS, NITERS, NFIBERS, NITERS, NFIBERS * NITERS);
    return 0;
  }
  fprintf(stderr, "FAIL: atomic (%d checks failed)\n", fails);
  return 1;
}
