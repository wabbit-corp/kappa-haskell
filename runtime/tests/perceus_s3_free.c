#include "internal.h"

#include <stdio.h>
#include <stdlib.h>

static void check(int cond, const char *msg) {
  if (!cond) {
    fprintf(stderr, "%s\n", msg);
    exit(1);
  }
}

static unsigned long long debug_drop_count(void) {
#ifndef NDEBUG
  return atomic_load_explicit(&k_drops_total, memory_order_relaxed);
#else
  return 0;
#endif
}

static void check_unique_tree_frees_on_zero(void) {
  KValue *leaf = kstr0("leaf");
  KValue *args[1] = { leaf };
  KValue *root = kctor(KCT_USER_BASE, "Root", 1, args);
  unsigned long long before = krc_debug_reclaim_count();
  kdrop(root);
  unsigned long long after = krc_debug_reclaim_count();
  check(after > before, "S3.2 kdrop of a unique freeable tree must release at least one object");
}

static void check_shared_freeable_tags_reclaim_and_retained_tags_do_not_free(void) {
  KValue *shared = kstr0("shared");
  krc_mark_shared_recursive(shared);
  unsigned long long before_shared = krc_debug_reclaim_count();
  kdrop(shared);
  check(krc_debug_reclaim_count() > before_shared, "S4 shared freeable-tag values must reclaim on last atomic drop");

  KValue *ref = kref_new(kunit());
  krc_mark_shared_recursive(ref);
  unsigned long long before_ref = krc_debug_reclaim_count();
  kdrop(ref);
  check(krc_debug_reclaim_count() == before_ref, "mutable refs must not be freed by S4 shared kdrop");
}

static void check_deep_free_is_iterative(void) {
  enum { DEPTH = 20000 };
  KValue *spine = kstr0("end");
  for (int i = 0; i < DEPTH; i++) {
    KValue *args[1] = { spine };
    spine = kctor(KCT_USER_BASE + 1, "Cons", 1, args);
  }
  unsigned long long before = krc_debug_reclaim_count();
  kdrop(spine);
  unsigned long long after = krc_debug_reclaim_count();
  check(after > before + 1000, "deep S3.2 free must walk iteratively and release nested objects");
}

static void check_record_rest_keeps_field_alive(void) {
  const char *names[2] = { "drop", "keep" };
  KValue *drop = kstr0("drop-field");
  KValue *keep = kstr0("keep-field");
  KValue *vals[2] = { drop, keep };
  KValue *rec = krec(2, names, vals);
  const char *excluded[1] = { "drop" };
  KValue *rest = krec_without(rec, 1, excluded);
  check(krc_count(keep) == 2, "record-rest setup must duplicate kept field ownership");
  kdrop(rec);
  check(krc_count(keep) == 1, "freeing the source record must not free a field retained by record rest");
  kdrop(rest);
}

static void check_ref_set_drops_old_value(void) {
  KValue *old = kstr0("s33-ref-old");
  KValue *ref = kref_new(old);
  unsigned long long before = krc_debug_reclaim_count();
  kref_set(ref, kstr0("s33-ref-new"));
  check(krc_debug_reclaim_count() > before, "S3.3 kref_set must drop the displaced old value");
}

static void check_ref_set_self_assignment_consumes_owned_arg(void) {
  KValue *v = kstr0("s33-ref-self");
  KValue *ref = kref_new(v);
  KValue *owned = kref_get(ref);
  check(owned == v && krc_count(v) == 2, "ref self-assignment setup must pass an owned duplicate");
  kref_set(ref, owned);
  KValue *got = kref_get(ref);
  check(got == v, "S3.3 kref_set self-assignment must keep the slot value");
  kdrop(got);
  check(krc_count(v) == 1, "S3.3 kref_set self-assignment must consume the owned write arg");
}

static void check_array_set_drops_old_slot_reference(void) {
  KValue *old = kstr0("s33-array-old");
  KValue *arr = karr_new(1, old);
  unsigned long long before = krc_debug_reclaim_count();
  karr_set(arr, 0, kstr0("s33-array-new"));
  check(krc_debug_reclaim_count() > before, "S3.3 karr_set must drop the displaced slot reference");
}

static void check_array_set_self_assignment_consumes_owned_arg(void) {
  KValue *v = kstr0("s33-array-self");
  KValue *arr = karr_new(1, v);
  KValue *owned = karr_get(arr, 0);
  check(owned == v && krc_count(v) == 2, "array self-assignment setup must pass an owned duplicate");
  karr_set(arr, 0, owned);
  KValue *got = karr_get(arr, 0);
  check(got == v, "S3.3 karr_set self-assignment must keep the slot value");
  kdrop(got);
  check(krc_count(v) == 1, "S3.3 karr_set self-assignment must consume the owned write arg");
}

static void check_array_new_zero_consumes_init(void) {
  KValue *init = kstr0("s33-array-zero-init");
  unsigned long long before = krc_debug_reclaim_count();
  KValue *arr = karr_new(0, init);
  check(karr_len(arr) == 0, "zero-length array setup must produce an empty array");
  check(krc_debug_reclaim_count() > before, "S3.3 karr_new(0, init) must consume the owned init it cannot store");
}

static void check_atomic_store_self_assignment_consumes_owned_arg(void) {
  KValue *v = kbigint_str("444444444444444444444444444444444444444");
  KValue *ref = krt2_new_atomic_ref(v);
  KValue *owned = kdup(v);
  krt2_atomic_store(kint(2), ref, owned);
  KValue *loaded = krt2_atomic_load(kint(2), ref);
  check(loaded == v, "S3.3 atomic store self-assignment must keep the cell value");
  kdrop(loaded);
  check(krc_is_shared(v), "AtomicRef cells stay shared-marked for S4 counted RC");
}

static void check_atomic_cas_failure_drops_desired(void) {
  KValue *ref = krt2_new_atomic_ref(kbigint_str("100000000000000000000000000000000000001"));
  KValue *expected = kbigint_str("200000000000000000000000000000000000002");
  KValue *desired = kbigint_str("300000000000000000000000000000000000003");
  check(krc_count(desired) == 1, "CAS desired setup must be uniquely owned by the call");
  KValue *witnessed = krt2_atomic_compare_exchange(kint(4), kint(2), ref, expected, desired);
  check(krc_count(desired) == 0, "S3.3 failed CAS must drop the desired value it did not publish");
  kdrop(witnessed);
  kdrop(expected);
}

static void check_atomic_cas_failure_alias_desired_contract(void) {
  KValue *v = kbigint_str("555555555555555555555555555555555555555");
  KValue *ref = krt2_new_atomic_ref(v);
  KValue *expected = kbigint_str("666666666666666666666666666666666666666");
  KValue *desired = kdup(v);
  unsigned before = krc_count(v);
  KValue *witnessed = krt2_atomic_compare_exchange(kint(4), kint(2), ref, expected, desired);
  check(witnessed == v, "failed CAS with desired==old must return the witnessed old value");
  check(krc_count(v) == before, "failed CAS with desired==old must drop desired and return one witnessed owner");
  KValue *loaded = krt2_atomic_load(kint(2), ref);
  check(loaded == v, "failed CAS with desired==old must leave the cell unchanged");
  kdrop(loaded);
  kdrop(witnessed);
  kdrop(expected);
  check(krc_count(v) == 1, "failed CAS alias cleanup must leave exactly the AtomicRef cell owner");
  check(krc_is_shared(v), "AtomicRef alias-failure desired stays shared-marked after failed CAS");
}

static KValue *complete_promise_twice(KEnv *env, KValue *promise) {
  (void)env;
  return krt2_then(krt2_complete_promise(promise, krt2_success(kstr0("s33-promise-first"))),
                   krt2_complete_promise(promise, krt2_success(kstr0("s33-promise-second"))));
}

static void check_promise_recomplete_drops_losing_exit(void) {
  unsigned long long before = krc_debug_reclaim_count();
  KValue *exit = krt2_run_main(krt2_bind(krt2_new_promise(), kclo(complete_promise_twice, NULL)));
  check(krt2_exit_is_success(exit), "promise recomplete test program must succeed");
  check(krc_debug_reclaim_count() > before, "S3.3 promise recomplete must drop the losing Exit value");
}

static KValue *overwrite_fiber_ref(KEnv *env, KValue *ref) {
  (void)env;
  return krt2_then(krt2_set_fiber_ref(ref, kstr0("s33-fiber-old")),
                   krt2_set_fiber_ref(ref, kstr0("s33-fiber-new")));
}

static void check_fiber_ref_overwrite_drops_old_override(void) {
  unsigned long long before = krc_debug_reclaim_count();
  KValue *exit = krt2_run_main(krt2_bind(krt2_new_fiber_ref(kstr0("s33-fiber-init")),
                                         kclo(overwrite_fiber_ref, NULL)));
  check(krt2_exit_is_success(exit), "FiberRef overwrite test program must succeed");
  check(krc_debug_reclaim_count() > before, "S3.3 setFiberRef must drop the displaced override");
}

static KValue *stm_second_write(KEnv *env, KValue *ignored) {
  (void)ignored;
  return krt2_write_tvar(kvar(env, 0), kstr0("s33-stm-new"));
}

static KValue *run_stm_duplicate_write(KEnv *env, KValue *tv) {
  (void)env;
  KValue *tx = krt2_stm_bind(krt2_write_tvar(tv, kstr0("s33-stm-old")),
                             kclo(stm_second_write, kpush(tv, NULL)));
  return krt2_atomically(tx);
}

static void check_stm_duplicate_write_drops_skipped_value(void) {
  unsigned long long before = debug_drop_count();
  KValue *program = krt2_bind(krt2_atomically(krt2_new_tvar(kstr0("s33-stm-init"))),
                              kclo(run_stm_duplicate_write, NULL));
  KValue *exit = krt2_run_main(program);
  check(krt2_exit_is_success(exit), "STM duplicate-write test program must succeed");
  check(debug_drop_count() >= before + 2, "S4 STM commit must drop the skipped write-log owner and displaced old TVar value");
}

static KValue *stm_retry_after_write(KEnv *env, KValue *ignored) {
  (void)env; (void)ignored;
  return krt2_retry();
}

static KValue *run_stm_orelse_rollback(KEnv *env, KValue *tv) {
  (void)env;
  KValue *left = krt2_stm_bind(krt2_write_tvar(tv, kstr0("s33-stm-rollback")),
                               kclo(stm_retry_after_write, NULL));
  KValue *tx = krt2_or_else(left, krt2_stm_pure(kunit()));
  return krt2_atomically(tx);
}

static void check_stm_orelse_rollback_drops_truncated_write(void) {
  unsigned long long before = debug_drop_count();
  KValue *program = krt2_bind(krt2_atomically(krt2_new_tvar(kstr0("s33-stm-or-init"))),
                              kclo(run_stm_orelse_rollback, NULL));
  KValue *exit = krt2_run_main(program);
  check(krt2_exit_is_success(exit), "STM orElse rollback test program must succeed");
  check(debug_drop_count() > before, "S3.3 STM orElse rollback must drop truncated write-log references");
}

int main(void) {
  krt_init();
  check_unique_tree_frees_on_zero();
  check_shared_freeable_tags_reclaim_and_retained_tags_do_not_free();
  check_deep_free_is_iterative();
  check_record_rest_keeps_field_alive();
  check_ref_set_drops_old_value();
  check_ref_set_self_assignment_consumes_owned_arg();
  check_array_set_drops_old_slot_reference();
  check_array_set_self_assignment_consumes_owned_arg();
  check_array_new_zero_consumes_init();
  check_atomic_store_self_assignment_consumes_owned_arg();
  check_atomic_cas_failure_drops_desired();
  check_atomic_cas_failure_alias_desired_contract();
  check_promise_recomplete_drops_losing_exit();
  check_fiber_ref_overwrite_drops_old_override();
  check_stm_duplicate_write_drops_skipped_value();
  check_stm_orelse_rollback_drops_truncated_write();
  return 0;
}
