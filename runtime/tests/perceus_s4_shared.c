#include "internal.h"

#include <gc.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sched.h>
#include <sys/wait.h>
#include <unistd.h>

static int fails = 0;

#define CHECK(cond, msg) do { if (!(cond)) { fprintf(stderr, "  FAIL: %s\n", msg); fails++; } } while (0)

static unsigned long long debug_drop_count(void) {
#ifndef NDEBUG
  return atomic_load_explicit(&k_drops_total, memory_order_relaxed);
#else
  return 0;
#endif
}

static void init_stack_fiber(Fiber *f) {
  memset(f, 0, sizeof *f);
  pthread_mutex_init(&f->lock, NULL);
}

static void destroy_stack_fiber(Fiber *f) {
  pthread_mutex_destroy(&f->lock);
}

static void check_failed_wake_drops_resume_value(void) {
  Fiber f;
  init_stack_fiber(&f);
  atomic_store(&f.status, F_RUNNABLE);

  unsigned long long before = krc_debug_reclaim_count();
  krt2i_wake(NULL, &f, krt2_pure(kstr0("s4-stale-wake")));
  CHECK(krc_debug_reclaim_count() > before,
        "failed wake must consume and drop its owned resume value");

  destroy_stack_fiber(&f);
}

static Waiter *test_waiter(Fiber *f) {
  Waiter *w = (Waiter *)GC_MALLOC(sizeof(Waiter));
  w->f = f;
  w->want_exit = 1;
  w->next = NULL;
  return w;
}

static void check_cleanup_unlinks_registered_waiters(void) {
  Fiber f;
  init_stack_fiber(&f);

  Promise p;
  memset(&p, 0, sizeof p);
  pthread_mutex_init(&p.lock, NULL);
  Waiter *pw = test_waiter(&f);
  p.waiters = pw;
  krt2i_register_park_waiter(&f, KPARK_PROMISE_WAITERS, &p, pw);
  krt2i_cleanup_parked_wait(&f);
  CHECK(p.waiters == NULL, "park cleanup must unlink promise waiters");
  CHECK(f.park_kind == KPARK_NONE && f.park_owner == NULL && f.park_waiter == NULL,
        "park cleanup must clear promise registration");
  pthread_mutex_destroy(&p.lock);

  Fiber target;
  init_stack_fiber(&target);
  Waiter *fw = test_waiter(&f);
  target.waiters = fw;
  krt2i_register_park_waiter(&f, KPARK_FIBER_WAITERS, &target, fw);
  krt2i_cleanup_parked_wait(&f);
  CHECK(target.waiters == NULL, "park cleanup must unlink fiber waiters");
  CHECK(f.park_kind == KPARK_NONE, "park cleanup must clear fiber registration");
  destroy_stack_fiber(&target);

  Scope *sc = krt2i_scope_new();
  Waiter *sw = test_waiter(&f);
  sc->drain_waiters = sw;
  krt2i_register_park_waiter(&f, KPARK_SCOPE_DRAIN, sc, sw);
  krt2i_cleanup_parked_wait(&f);
  CHECK(sc->drain_waiters == NULL, "park cleanup must unlink scope drain waiters");
  CHECK(f.park_kind == KPARK_NONE, "park cleanup must clear scope registration");

  TVar tv;
  memset(&tv, 0, sizeof tv);
  Waiter *tw = test_waiter(&f);
  tv.watchers = tw;
  f.stm_reads = (TVar **)GC_MALLOC(sizeof(TVar *));
  f.stm_reads[0] = &tv;
  f.stm_nreads = 1;
  krt2i_cleanup_parked_wait(&f);
  CHECK(tv.watchers == NULL, "park cleanup must unlink STM retry watchers");
  CHECK(f.stm_reads == NULL && f.stm_nreads == 0, "park cleanup must clear STM retry registration");

  destroy_stack_fiber(&f);
}

static void check_shared_ref_reader_survives_overwrite(void) {
  KValue *old = kstr0("s4-ref-old");
  KValue *ref = kref_new(old);
  krc_mark_shared_recursive(ref);

  KValue *reader = kref_get(ref);
  CHECK(krc_count(old) == 2, "shared Ref reader setup must count the read owner and cell owner");

  unsigned long long before = krc_debug_reclaim_count();
  kref_set(ref, kstr0("s4-ref-new"));
  CHECK(krc_count(reader) == 1, "shared Ref overwrite must drop only the cell owner");
  CHECK(krc_debug_reclaim_count() == before, "shared Ref overwrite must not free a value held by a reader");

  kdrop(reader);
  CHECK(krc_debug_reclaim_count() > before, "shared Ref reader's final drop must reclaim the old value");
}

static void check_shared_array_reader_survives_overwrite(void) {
  KValue *old = kstr0("s4-array-old");
  KValue *arr = karr_new(1, old);
  krc_mark_shared_recursive(arr);

  KValue *reader = karr_get(arr, 0);
  CHECK(krc_count(old) == 2, "shared Array reader setup must count the read owner and slot owner");

  unsigned long long before = krc_debug_reclaim_count();
  karr_set(arr, 0, kstr0("s4-array-new"));
  CHECK(krc_count(reader) == 1, "shared Array overwrite must drop only the slot owner");
  CHECK(krc_debug_reclaim_count() == before, "shared Array overwrite must not free a value held by a reader");

  kdrop(reader);
  CHECK(krc_debug_reclaim_count() > before, "shared Array reader's final drop must reclaim the old value");
}

static void check_shared_atomic_ref_reader_survives_store(void) {
  KValue *old = kbigint_str("100000000000000000000000000000000000041");
  KValue *ref = krt2_new_atomic_ref(old);

  KValue *reader = krt2_atomic_load(kint(2), ref);
  CHECK(krc_count(old) == 2, "shared AtomicRef reader setup must count the load owner and cell owner");

  krt2_atomic_store(kint(2), ref, kbigint_str("100000000000000000000000000000000000043"));
  CHECK(krc_count(reader) == 1, "shared AtomicRef store must drop only the cell owner");

  kdrop(reader);
  CHECK(krc_count(old) == 0, "shared AtomicRef reader's final drop must release the old value count");
}

typedef KValue *(*AtomicFetchOp)(KValue *order, KValue *ref, KValue *v);

static void check_atomic_fetch_transfers_old_owner(const char *name, AtomicFetchOp op, KValue *arg) {
  KValue *old = kbigint_str("1267650600228229401496703205376");
  KValue *ref = krt2_new_atomic_ref(old);
  KValue *returned = op(kint(0), ref, arg);
  CHECK(returned == old, name);
  CHECK(krc_count(old) == 1, "AtomicRef fetch-* return must be the old cell owner, not a stale duplicate");
  kdrop(returned);
  CHECK(krc_count(old) == 0, "dropping an AtomicRef fetch-* result must release the old owner");
  kdrop(arg);
}

static void check_shared_atomic_ref_returned_old_owners(void) {
  KValue *old = kbigint_str("100000000000000000000000000000000000101");
  KValue *ref = krt2_new_atomic_ref(old);
  KValue *exchanged = kbigint_str("100000000000000000000000000000000000103");
  KValue *returned = krt2_atomic_exchange(kint(0), ref, exchanged);
  CHECK(returned == old, "AtomicRef exchange must return the displaced old owner");
  CHECK(krc_count(old) == 1, "AtomicRef exchange must transfer exactly the old cell owner");
  kdrop(returned);
  CHECK(krc_count(old) == 0, "dropping AtomicRef exchange result must release the displaced owner");

  KValue *alias = kbigint_str("100000000000000000000000000000000000107");
  KValue *alias_ref = krt2_new_atomic_ref(alias);
  returned = krt2_atomic_exchange(kint(0), alias_ref, kdup(alias));
  CHECK(returned == alias, "AtomicRef self-alias exchange must return the old owner");
  CHECK(krc_count(alias) == 2, "AtomicRef self-alias exchange must keep one returned owner and one cell owner");
  kdrop(returned);
  CHECK(krc_count(alias) == 1, "dropping self-alias exchange result must leave the cell owner");

  old = kbigint_str("100000000000000000000000000000000000109");
  ref = krt2_new_atomic_ref(old);
  KValue *desired = kbigint_str("100000000000000000000000000000000000113");
  returned = krt2_atomic_compare_exchange(kint(0), kint(0), ref, old, desired);
  CHECK(returned == old, "AtomicRef successful CAS must return the displaced old owner");
  CHECK(krc_count(old) == 1, "AtomicRef successful CAS must transfer exactly the old cell owner");
  kdrop(returned);
  CHECK(krc_count(old) == 0, "dropping AtomicRef successful-CAS result must release the displaced owner");
  CHECK(krc_count(desired) == 1, "AtomicRef successful CAS must install desired as the cell owner");

  alias = kbigint_str("100000000000000000000000000000000000127");
  alias_ref = krt2_new_atomic_ref(alias);
  returned = krt2_atomic_compare_exchange(kint(0), kint(0), alias_ref, alias, kdup(alias));
  CHECK(returned == alias, "AtomicRef self-alias successful CAS must return the old owner");
  CHECK(krc_count(alias) == 2, "AtomicRef self-alias successful CAS must keep one returned owner and one cell owner");
  kdrop(returned);
  CHECK(krc_count(alias) == 1, "dropping self-alias successful-CAS result must leave the cell owner");

  check_atomic_fetch_transfers_old_owner("AtomicRef fetch_add must return the displaced old owner",
                                         krt2_atomic_fetch_add,
                                         kbigint_str("100000000000000000000000000000000000001"));
  check_atomic_fetch_transfers_old_owner("AtomicRef fetch_sub must return the displaced old owner",
                                         krt2_atomic_fetch_sub,
                                         kbigint_str("1"));
  check_atomic_fetch_transfers_old_owner("AtomicRef fetch_and must return the displaced old owner",
                                         krt2_atomic_fetch_and,
                                         kbigint_str("1267650600228229401496703205376"));
  check_atomic_fetch_transfers_old_owner("AtomicRef fetch_or must return the displaced old owner",
                                         krt2_atomic_fetch_or,
                                         kbigint_str("1"));
  check_atomic_fetch_transfers_old_owner("AtomicRef fetch_xor must return the displaced old owner",
                                         krt2_atomic_fetch_xor,
                                         kbigint_str("1"));
}

static void check_run_main_returns_owned_exit(void) {
  KValue *exit = krt2_run_main(krt2_pure(kstr0("s4-run-main-owned-exit")));
  CHECK(krt2_exit_is_success(exit), "run_main ownership test must complete successfully");
  CHECK(krc_is_shared(exit), "run_main returned Exit must be shared after fiber publication");
  CHECK(krc_count(exit) == 2, "run_main must return exactly one distinct counted Exit owner for the caller");
  if (krc_count(exit) > 0) kdrop(exit);
}

typedef struct {
  KValue *ref;
  KValue *arr;
  int rounds;
  _Atomic int start;
  _Atomic int bad;
  _Atomic int bad_tag;
  _Atomic uint32_t bad_rc;
  _Atomic int bad_from_array;
} SharedStorageRace;

static int shared_storage_observed_string(SharedStorageRace *s, KValue *v, int from_array) {
  if (kis_imm(v) || v->tag != K_STR) {
    int expected = 0;
    if (atomic_compare_exchange_strong_explicit(&s->bad, &expected, 1,
                                                memory_order_relaxed,
                                                memory_order_relaxed)) {
      atomic_store_explicit(&s->bad_tag, kis_imm(v) ? -1 : (int)v->tag, memory_order_relaxed);
      atomic_store_explicit(&s->bad_rc, kis_imm(v) ? 0u : krc_word(v), memory_order_relaxed);
      atomic_store_explicit(&s->bad_from_array, from_array, memory_order_relaxed);
    }
    return 0;
  }
  const char *text = v->as.str.p;
  if (!text || strncmp(text, "rw-", 3) != 0) {
    atomic_store_explicit(&s->bad, 1, memory_order_relaxed);
    return 0;
  }
  return 1;
}

static void *shared_storage_reader(void *arg) {
  SharedStorageRace *s = (SharedStorageRace *)arg;
  while (!atomic_load_explicit(&s->start, memory_order_acquire)) sched_yield();
  for (int i = 0; i < s->rounds; i++) {
    KValue *rv = kref_get(s->ref);
    shared_storage_observed_string(s, rv, 0);
    sched_yield();
    kdrop(rv);

    KValue *av = karr_get(s->arr, 0);
    shared_storage_observed_string(s, av, 1);
    sched_yield();
    kdrop(av);
  }
  return NULL;
}

static void *shared_storage_writer(void *arg) {
  SharedStorageRace *s = (SharedStorageRace *)arg;
  atomic_store_explicit(&s->start, 1, memory_order_release);
  for (int i = 0; i < s->rounds; i++) {
    char buf[64];
    snprintf(buf, sizeof buf, "rw-ref-%d", i);
    kref_set(s->ref, kstr0(buf));
    snprintf(buf, sizeof buf, "rw-arr-%d", i);
    karr_set(s->arr, 0, kstr0(buf));
    sched_yield();
  }
  return NULL;
}

static void check_shared_ref_array_concurrent_read_write(void) {
  SharedStorageRace s;
  memset(&s, 0, sizeof s);
  s.rounds = 4000;
  s.ref = kref_new(kstr0("rw-ref-init"));
  s.arr = karr_new(1, kstr0("rw-arr-init"));
  krc_mark_shared_recursive(s.ref);
  krc_mark_shared_recursive(s.arr);

  pthread_t readers[4];
  pthread_t writer;
  for (int i = 0; i < 4; i++) GC_pthread_create(&readers[i], NULL, shared_storage_reader, &s);
  GC_pthread_create(&writer, NULL, shared_storage_writer, &s);
  GC_pthread_join(writer, NULL);
  for (int i = 0; i < 4; i++) GC_pthread_join(readers[i], NULL);

  if (atomic_load_explicit(&s.bad, memory_order_relaxed)) {
    fprintf(stderr, "  FAIL: concurrent shared %s reader observed non-string tag=%d rc=0x%08x\n",
            atomic_load_explicit(&s.bad_from_array, memory_order_relaxed) ? "Array" : "Ref",
            atomic_load_explicit(&s.bad_tag, memory_order_relaxed),
            atomic_load_explicit(&s.bad_rc, memory_order_relaxed));
    fails++;
  }
}

typedef struct {
  KValue *thunk;
  _Atomic int start;
  _Atomic int done;
} SharedMemoThunkRace;

static KValue *slow_memo_thunk(KEnv *env) {
  (void)env;
  for (int i = 0; i < 2000; i++) sched_yield();
  return kstr0("s4-shared-memo");
}

static KValue *env_must_be_shared_memo_thunk(KEnv *env) {
  KValue *captured = kvar(env, 0);
  CHECK(krc_is_shared(captured), "shared memo thunk body must not observe private captured env");
  return kstr0("s4-shared-env");
}

static void *shared_memo_thunk_marker(void *arg) {
  SharedMemoThunkRace *r = (SharedMemoThunkRace *)arg;
  while (!atomic_load_explicit(&r->start, memory_order_acquire)) sched_yield();
  while (!atomic_load_explicit(&r->done, memory_order_acquire)) {
    krc_mark_shared_recursive(r->thunk);
    sched_yield();
  }
  return NULL;
}

static void *shared_memo_thunk_forcer(void *arg) {
  SharedMemoThunkRace *r = (SharedMemoThunkRace *)arg;
  atomic_store_explicit(&r->start, 1, memory_order_release);
  KValue *v = kforce(r->thunk);
  CHECK(!kis_imm(v) && v->tag == K_STR, "shared memo thunk force must return the cached string");
  kdrop(v);
  atomic_store_explicit(&r->done, 1, memory_order_release);
  return NULL;
}

static void check_shared_memo_thunk_mark_force_race(void) {
  SharedMemoThunkRace r;
  memset(&r, 0, sizeof r);
  r.thunk = kthunk(slow_memo_thunk, NULL, 1);

  pthread_t marker;
  pthread_t forcer;
  GC_pthread_create(&marker, NULL, shared_memo_thunk_marker, &r);
  GC_pthread_create(&forcer, NULL, shared_memo_thunk_forcer, &r);
  GC_pthread_join(forcer, NULL);
  GC_pthread_join(marker, NULL);

  CHECK(r.thunk->as.thunk.cache != NULL, "shared memo thunk race test must populate the cache");
  CHECK(krc_is_shared(r.thunk->as.thunk.cache[0]), "shared memo thunk cached value must be marked shared");
}

static void check_shared_memo_existing_private_cache_is_marked_before_return(void) {
  KValue *thunk = kthunk(slow_memo_thunk, NULL, 1);
  KValue *first = kforce(thunk);
  CHECK(thunk->as.thunk.cache != NULL, "private memo thunk precondition must populate the cache");
  KValue *cached = thunk->as.thunk.cache ? thunk->as.thunk.cache[0] : NULL;
  CHECK(cached == first, "private memo thunk force should return the cached value owner");
  CHECK(cached && !krc_is_shared(cached), "private memo cache precondition must start thread-local");
  kdrop(first);

  __atomic_fetch_or(&thunk->rc, KRC_SHARED_BIT, __ATOMIC_RELAXED);
  KValue *second = kforce(thunk);
  CHECK(krc_is_shared(cached), "forcing an already-shared memo thunk must mark its existing cache before returning it");
  CHECK(second == cached, "shared memo cached fast path should return the cached value");
  kdrop(second);
}

typedef struct {
  KValue **thunks;
  int n;
  _Atomic int start;
} SharedMemoExistingCacheRace;

static void install_memo_cache_for_test(KValue *thunk, KValue *cached);

static void *shared_memo_existing_cache_marker(void *arg) {
  SharedMemoExistingCacheRace *r = (SharedMemoExistingCacheRace *)arg;
  while (!atomic_load_explicit(&r->start, memory_order_acquire)) sched_yield();
  for (int i = 0; i < r->n; i++) {
    krc_mark_shared_recursive(r->thunks[i]);
    if ((i & 7) == 0) sched_yield();
  }
  return NULL;
}

static void *shared_memo_existing_cache_forcer(void *arg) {
  SharedMemoExistingCacheRace *r = (SharedMemoExistingCacheRace *)arg;
  atomic_store_explicit(&r->start, 1, memory_order_release);
  for (int i = 0; i < r->n; i++) {
    KValue *v = kforce(r->thunks[i]);
    CHECK(!kis_imm(v) && v->tag == K_STR, "existing shared memo cache force must return a string");
    kdrop(v);
    if ((i & 7) == 0) sched_yield();
  }
  return NULL;
}

static void check_shared_memo_existing_cache_mark_force_race(void) {
#ifdef KRT2_TSAN
  enum { N = 512 };
#else
  enum { N = 2048 };
#endif
  SharedMemoExistingCacheRace r;
  memset(&r, 0, sizeof r);
  r.n = N;
  r.thunks = (KValue **)kgc_alloc(sizeof(KValue *) * N);
  for (int i = 0; i < N; i++) {
    KValue *cached = kstr0("s4-existing-cache-race");
    r.thunks[i] = kthunk(slow_memo_thunk, NULL, 1);
    install_memo_cache_for_test(r.thunks[i], cached);
  }

  pthread_t marker;
  pthread_t forcer;
  GC_pthread_create(&marker, NULL, shared_memo_existing_cache_marker, &r);
  GC_pthread_create(&forcer, NULL, shared_memo_existing_cache_forcer, &r);
  GC_pthread_join(forcer, NULL);
  GC_pthread_join(marker, NULL);

  for (int i = 0; i < N; i++) {
    KValue *cached = r.thunks[i]->as.thunk.cache ? r.thunks[i]->as.thunk.cache[0] : NULL;
    CHECK(cached && krc_is_shared(cached), "existing memo cache race must leave cached value shared");
  }
}

static void check_shared_memo_force_marks_env_before_body(void) {
  KValue *captured = kstr0("s4-env-private");
  KValue *thunk = kthunk(env_must_be_shared_memo_thunk, kpush(captured, NULL), 1);
  __atomic_fetch_or(&thunk->rc, KRC_SHARED_BIT, __ATOMIC_RELAXED);
  KValue *forced = kforce(thunk);
  CHECK(krc_is_shared(captured), "forcing an already-shared memo thunk must mark captured env before body");
  CHECK(!kis_imm(forced) && forced->tag == K_STR, "shared env memo thunk must return a string");
  kdrop(forced);
}

static void install_memo_cache_for_test(KValue *thunk, KValue *cached) {
  KValue **cell = (KValue **)kgc_alloc(sizeof(KValue *));
  cell[0] = cached;
  thunk->as.thunk.cache = cell;
}

static void check_shared_memo_cache_cycle_marks_without_recursing_forever(void) {
  KValue *a = kthunk(slow_memo_thunk, NULL, 1);
  KValue *b = kthunk(slow_memo_thunk, NULL, 1);
  install_memo_cache_for_test(a, b);
  install_memo_cache_for_test(b, a);
  krc_mark_shared_recursive(a);
  CHECK(krc_is_shared(a), "cache-cycle root memo thunk must be marked shared");
  CHECK(krc_is_shared(b), "cache-cycle cached memo thunk must be marked shared");
}

static void check_shared_memo_deep_cache_chain_marks_iteratively(void) {
#ifdef KRT2_TSAN
  enum { N = 4096 };
#else
  enum { N = 100000 };
#endif
  KValue **nodes = (KValue **)kgc_alloc(sizeof(KValue *) * N);
  KValue *leaf = kstr0("s4-deep-memo-cache-leaf");
  for (int i = 0; i < N; i++) nodes[i] = kthunk(slow_memo_thunk, NULL, 1);
  for (int i = 0; i < N - 1; i++) install_memo_cache_for_test(nodes[i], nodes[i + 1]);
  install_memo_cache_for_test(nodes[N - 1], leaf);

  krc_mark_shared_recursive(nodes[0]);
  CHECK(krc_is_shared(nodes[0]), "deep memo cache root must be marked shared");
  CHECK(krc_is_shared(nodes[N - 1]), "deep memo cache tail thunk must be marked shared");
  CHECK(krc_is_shared(leaf), "deep memo cache leaf must be marked shared");
}

static void check_stm_same_pointer_write_consumes_journal_owner(void) {
  Fiber f;
  init_stack_fiber(&f);
  KValue *v = kstr0("s4-stm-same");
  CHECK(krt2i_op_atomically(NULL, &f, krt2_new_tvar(v)), "STM same-pointer setup must create a TVar");
  KValue *tv = kctor_arg(f.cur, 0);
  KValue *owned_write = kdup(v);
  unsigned before_count = krc_count(v);
  unsigned long long before = debug_drop_count();
  CHECK(krt2i_op_atomically(NULL, &f, krt2_write_tvar(tv, owned_write)),
        "STM same-pointer write transaction must commit");
#ifndef NDEBUG
  CHECK(debug_drop_count() == before + 1,
        "STM same-pointer commit must drop exactly the write-log owner it does not install");
#endif
  CHECK(krc_count(v) == before_count,
        "STM same-pointer commit must not retain the skipped write-log owner");
  destroy_stack_fiber(&f);
}

#ifndef KRT2_TSAN
static void trigger_promise_poll_result_drop_does_not_stale_promise(void) {
  krt_init();
  krc_poison_set_enabled(1);

  KValue *p_exit = krt2_run_main(krt2_new_promise());
  if (!krt2_exit_is_success(p_exit)) _exit(2);
  KValue *promise = kctor_arg(p_exit, 0);

  KValue *done_exit = krt2_run_main(krt2_complete_promise(promise, krt2_success(kstr0("s4-promised"))));
  if (!krt2_exit_is_success(done_exit)) _exit(3);

  KValue *poll1_exit = krt2_run_main(krt2_poll_promise(promise));
  if (!krt2_exit_is_success(poll1_exit)) _exit(4);
  KValue *poll1 = kctor_arg(poll1_exit, 0);
  kdrop(poll1);

  KValue *poll2_exit = krt2_run_main(krt2_poll_promise(promise));
  if (!krt2_exit_is_success(poll2_exit)) _exit(5);
  KValue *poll2 = kctor_arg(poll2_exit, 0);
  if (kctor_tagid(poll2) != KCT_SOME) _exit(6);
  KValue *observed_exit = kctor_arg(poll2, 0);
  if (!krt2_exit_is_success(observed_exit)) _exit(7);
  const char *s = kas_str(kctor_arg(observed_exit, 0));
  _exit(strcmp(s, "s4-promised") == 0 ? 0 : 8);
}

static KValue *child_wait_then_get_ref(KEnv *env) {
  KValue *ref = kvar(env, 0);
  KValue *promise = kvar(env, 1);
  return krt2_then(krt2_await_promise_exit(promise), krt2_get_fiber_ref(ref));
}

static KValue *after_parent_overwrite(KEnv *env, KValue *ignored) {
  (void)ignored;
  KValue *fiber = kvar(env, 0);
  KValue *promise = kvar(env, 1);
  return krt2_then(krt2_complete_promise(promise, krt2_success(kunit())),
                   krt2_await(fiber));
}

static KValue *after_child_forked(KEnv *env, KValue *fiber) {
  KValue *ref = kvar(env, 0);
  KValue *promise = kvar(env, 1);
  return krt2_bind(krt2_set_fiber_ref(ref, kstr0("s4-parent-new")),
                   kclo(after_parent_overwrite, kpush(fiber, kpush(promise, NULL))));
}

static KValue *after_ref_initialized(KEnv *env, KValue *ignored) {
  (void)ignored;
  KValue *ref = kvar(env, 0);
  KValue *promise = kvar(env, 1);
  KValue *child = child_wait_then_get_ref(kpush(ref, kpush(promise, NULL)));
  return krt2_bind(krt2_fork(child), kclo(after_child_forked, kpush(ref, kpush(promise, NULL))));
}

static KValue *after_fiber_ref_new(KEnv *env, KValue *ref) {
  KValue *promise = kvar(env, 0);
  return krt2_bind(krt2_set_fiber_ref(ref, kstr0("s4-child-copy")),
                   kclo(after_ref_initialized, kpush(ref, kpush(promise, NULL))));
}

static KValue *run_fiber_ref_snapshot_case(KEnv *env, KValue *promise) {
  (void)env;
  return krt2_bind(krt2_new_fiber_ref(kstr0("s4-init")),
                   kclo(after_fiber_ref_new, kpush(promise, NULL)));
}

static void trigger_fiber_ref_snapshot_value_survives_parent_overwrite(void) {
  krt_init();
  krc_poison_set_enabled(1);

  KValue *program = krt2_bind(krt2_new_promise(), kclo(run_fiber_ref_snapshot_case, NULL));
  KValue *exit = krt2_run_main(program);
  if (!krt2_exit_is_success(exit)) _exit(2);
  KValue *child_exit = kctor_arg(exit, 0);
  if (!krt2_exit_is_success(child_exit)) _exit(3);
  const char *s = kas_str(kctor_arg(child_exit, 0));
  _exit(strcmp(s, "s4-child-copy") == 0 ? 0 : 4);
}

static KValue *fanout_payload_from_exit(KEnv *env, KValue *exit) {
  (void)env;
  if (!krt2_exit_is_success(exit)) return krt2_pure(kstr0("bad-exit"));
  return krt2_pure(kctor_arg(exit, 0));
}

static KValue *promise_fanout_waiter(KEnv *env) {
  KValue *promise = kvar(env, 0);
  return krt2_bind(krt2_await_promise_exit(promise), kclo(fanout_payload_from_exit, NULL));
}

static KValue *pair_child_exits(KEnv *env, KValue *exit2) {
  KValue *exit1 = kvar(env, 0);
  KValue *args[2] = { exit1, exit2 };
  return krt2_pure(kctor(KCT_USER_BASE + 41, "FanoutPair", 2, args));
}

static KValue *after_promise_waiter1(KEnv *env, KValue *exit1) {
  KValue *waiter2 = kvar(env, 0);
  return krt2_bind(krt2_await(waiter2), kclo(pair_child_exits, kpush(exit1, NULL)));
}

static KValue *after_promise_complete(KEnv *env, KValue *ignored) {
  (void)ignored;
  KValue *waiter1 = kvar(env, 0);
  KValue *waiter2 = kvar(env, 1);
  return krt2_bind(krt2_await(waiter1), kclo(after_promise_waiter1, kpush(waiter2, NULL)));
}

static KValue *after_promise_waiters_parked(KEnv *env, KValue *ignored) {
  (void)ignored;
  KValue *promise = kvar(env, 0);
  KValue *waiter1 = kvar(env, 1);
  KValue *waiter2 = kvar(env, 2);
  return krt2_bind(krt2_complete_promise(promise, krt2_success(kstr0("s4-promise-fanout"))),
                   kclo(after_promise_complete, kpush(waiter1, kpush(waiter2, NULL))));
}

static KValue *after_promise_waiter2_fork(KEnv *env, KValue *waiter2) {
  KValue *promise = kvar(env, 0);
  KValue *waiter1 = kvar(env, 1);
  return krt2_then(krt2_cede(),
         krt2_bind(krt2_cede(),
                   kclo(after_promise_waiters_parked,
                        kpush(promise, kpush(waiter1, kpush(waiter2, NULL))))));
}

static KValue *after_promise_waiter1_fork(KEnv *env, KValue *waiter1) {
  KValue *promise = kvar(env, 0);
  KValue *waiter = promise_fanout_waiter(kpush(promise, NULL));
  return krt2_bind(krt2_fork(waiter), kclo(after_promise_waiter2_fork, kpush(promise, kpush(waiter1, NULL))));
}

static KValue *run_promise_fanout_case(KEnv *env, KValue *promise) {
  (void)env;
  KValue *waiter = promise_fanout_waiter(kpush(promise, NULL));
  return krt2_bind(krt2_fork(waiter), kclo(after_promise_waiter1_fork, kpush(promise, NULL)));
}

static void assert_fanout_pair_payloads(KValue *pair, const char *expected) {
  KValue *exit1 = kctor_arg(pair, 0);
  KValue *exit2 = kctor_arg(pair, 1);
  if (!krt2_exit_is_success(exit1) || !krt2_exit_is_success(exit2)) _exit(10);
  const char *s1 = kas_str(kctor_arg(exit1, 0));
  const char *s2 = kas_str(kctor_arg(exit2, 0));
  if (strcmp(s1, expected) != 0 || strcmp(s2, expected) != 0) _exit(11);
}

static void trigger_promise_fanout_waiters_share_exit(void) {
  krt_init();
  krc_poison_set_enabled(1);

  KValue *exit = krt2_run_main(krt2_bind(krt2_new_promise(), kclo(run_promise_fanout_case, NULL)));
  if (!krt2_exit_is_success(exit)) _exit(2);
  assert_fanout_pair_payloads(kctor_arg(exit, 0), "s4-promise-fanout");
  _exit(0);
}

static KValue *target_fiber_after_gate(KEnv *env, KValue *ignored) {
  (void)env;
  (void)ignored;
  return krt2_pure(kstr0("s4-fiber-fanout"));
}

static KValue *target_fiber_body(KEnv *env) {
  KValue *gate = kvar(env, 0);
  return krt2_bind(krt2_await_promise_exit(gate), kclo(target_fiber_after_gate, NULL));
}

static KValue *fiber_fanout_waiter(KEnv *env) {
  KValue *target = kvar(env, 0);
  return krt2_bind(krt2_await(target), kclo(fanout_payload_from_exit, NULL));
}

static KValue *after_fiber_waiter1(KEnv *env, KValue *exit1) {
  KValue *waiter2 = kvar(env, 0);
  return krt2_bind(krt2_await(waiter2), kclo(pair_child_exits, kpush(exit1, NULL)));
}

static KValue *after_gate_complete(KEnv *env, KValue *ignored) {
  (void)ignored;
  KValue *waiter1 = kvar(env, 0);
  KValue *waiter2 = kvar(env, 1);
  return krt2_bind(krt2_await(waiter1), kclo(after_fiber_waiter1, kpush(waiter2, NULL)));
}

static KValue *after_fiber_waiters_parked(KEnv *env, KValue *ignored) {
  (void)ignored;
  KValue *gate = kvar(env, 0);
  KValue *waiter1 = kvar(env, 1);
  KValue *waiter2 = kvar(env, 2);
  return krt2_bind(krt2_complete_promise(gate, krt2_success(kunit())),
                   kclo(after_gate_complete, kpush(waiter1, kpush(waiter2, NULL))));
}

static KValue *after_fiber_waiter2_fork(KEnv *env, KValue *waiter2) {
  KValue *gate = kvar(env, 0);
  KValue *waiter1 = kvar(env, 1);
  return krt2_then(krt2_cede(),
         krt2_bind(krt2_cede(),
                   kclo(after_fiber_waiters_parked,
                        kpush(gate, kpush(waiter1, kpush(waiter2, NULL))))));
}

static KValue *after_fiber_waiter1_fork(KEnv *env, KValue *waiter1) {
  KValue *gate = kvar(env, 0);
  KValue *target = kvar(env, 1);
  KValue *waiter = fiber_fanout_waiter(kpush(target, NULL));
  return krt2_bind(krt2_fork(waiter), kclo(after_fiber_waiter2_fork, kpush(gate, kpush(waiter1, NULL))));
}

static KValue *after_target_fork(KEnv *env, KValue *target) {
  KValue *gate = kvar(env, 0);
  KValue *waiter = fiber_fanout_waiter(kpush(target, NULL));
  return krt2_bind(krt2_fork(waiter), kclo(after_fiber_waiter1_fork, kpush(gate, kpush(target, NULL))));
}

static KValue *run_fiber_fanout_case(KEnv *env, KValue *gate) {
  (void)env;
  KValue *target = target_fiber_body(kpush(gate, NULL));
  return krt2_bind(krt2_fork(target), kclo(after_target_fork, kpush(gate, NULL)));
}

static void trigger_fiber_fanout_waiters_share_exit(void) {
  krt_init();
  krc_poison_set_enabled(1);

  KValue *exit = krt2_run_main(krt2_bind(krt2_new_promise(), kclo(run_fiber_fanout_case, NULL)));
  if (!krt2_exit_is_success(exit)) _exit(2);
  assert_fanout_pair_payloads(kctor_arg(exit, 0), "s4-fiber-fanout");
  _exit(0);
}

static void expect_no_poison_trap(const char *label, void (*fn)(void)) {
  int pipefd[2];
  CHECK(pipe(pipefd) == 0, "pipe created");
  pid_t pid = fork();
  CHECK(pid >= 0, "fork succeeded");
  if (pid == 0) {
    alarm(10);
    close(pipefd[0]);
    dup2(pipefd[1], STDERR_FILENO);
    close(pipefd[1]);
    fn();
    _exit(0);
  }

  close(pipefd[1]);
  char buf[4096];
  ssize_t n = read(pipefd[0], buf, sizeof(buf) - 1);
  close(pipefd[0]);
  if (n < 0) n = 0;
  buf[n] = '\0';

  int status = 0;
  CHECK(waitpid(pid, &status, 0) == pid, "child reaped");
  if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
    fprintf(stderr, "  FAIL: %s trapped or failed; status=%d stderr=%s\n", label, status, buf);
    fails++;
  }
}
#endif

int main(void) {
  krt_init();
  check_shared_ref_reader_survives_overwrite();
  check_shared_array_reader_survives_overwrite();
  check_shared_atomic_ref_reader_survives_store();
  check_shared_atomic_ref_returned_old_owners();
  check_failed_wake_drops_resume_value();
  check_cleanup_unlinks_registered_waiters();
  check_shared_ref_array_concurrent_read_write();
  check_shared_memo_thunk_mark_force_race();
  check_shared_memo_existing_private_cache_is_marked_before_return();
  check_shared_memo_existing_cache_mark_force_race();
  check_shared_memo_force_marks_env_before_body();
  check_shared_memo_cache_cycle_marks_without_recursing_forever();
  check_shared_memo_deep_cache_chain_marks_iteratively();
#ifndef KRT2_TSAN
  expect_no_poison_trap("promise poll result drop does not stale promise",
                        trigger_promise_poll_result_drop_does_not_stale_promise);
  expect_no_poison_trap("FiberRef fork snapshot survives parent overwrite",
                        trigger_fiber_ref_snapshot_value_survives_parent_overwrite);
  expect_no_poison_trap("promise fan-out waiters share completed Exit safely",
                        trigger_promise_fanout_waiters_share_exit);
  expect_no_poison_trap("fiber fan-out waiters share completed Exit safely",
                        trigger_fiber_fanout_waiters_share_exit);
#endif
  check_run_main_returns_owned_exit();
  check_stm_same_pointer_write_consumes_journal_owner();
  if (fails) {
    fprintf(stderr, "FAIL: perceus_s4_shared (%d)\n", fails);
    return 1;
  }
  fprintf(stderr, "OK: perceus_s4_shared\n");
  return 0;
}
