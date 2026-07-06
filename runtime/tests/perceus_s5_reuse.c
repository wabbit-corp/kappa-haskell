#include "internal.h"

#include <stdio.h>
#include <stdlib.h>
#include <sys/wait.h>
#include <unistd.h>

static void check(int cond, const char *msg) {
  if (!cond) {
    fprintf(stderr, "%s\n", msg);
    exit(1);
  }
}

static KValue *boxed_ctor1(int tag, const char *name, KValue *field) {
  KValue *args[1] = { field };
  KValue *v = kctor(tag, name, 1, args);
  check(!kis_imm(v) && v->tag == K_CTOR, "test setup must allocate a boxed one-field constructor");
  return v;
}

static KValue *boxed_ctor2(int tag, const char *name, KValue *left, KValue *right) {
  KValue *args[2] = { left, right };
  KValue *v = kctor(tag, name, 2, args);
  check(!kis_imm(v) && v->tag == K_CTOR, "test setup must allocate a boxed two-field constructor");
  return v;
}

static KValue *boxed_ctor3(int tag, const char *name, KValue *a, KValue *b, KValue *c) {
  KValue *args[3] = { a, b, c };
  KValue *v = kctor(tag, name, 3, args);
  check(!kis_imm(v) && v->tag == K_CTOR, "test setup must allocate a boxed three-field constructor");
  return v;
}

static void expect_child_failure(void (*fn)(void), const char *msg) {
  pid_t pid = fork();
  check(pid >= 0, "fork for expected-failure S5 test");
  if (pid == 0) {
    (void)freopen("/dev/null", "w", stderr);
    fn();
    _exit(0);
  }
  int status = 0;
  check(waitpid(pid, &status, 0) == pid, "child reaped for expected-failure S5 test");
  check(!WIFEXITED(status) || WEXITSTATUS(status) != 0, msg);
}

static void check_unique_ctor_reuses_cell_and_drops_old_field(void) {
  KValue *old_field = kstr0("s5-old");
  KValue *box = boxed_ctor1(KCT_USER_BASE + 10, "S5Old", old_field);
  KValue **old_args = box->as.ctor.args;
  KValue *new_field = kstr0("s5-new");
  KValue *new_args[1] = { new_field };

  KValue *token = kdrop_reuse_ctor(box, 1);
  check(token == box, "S5 drop_reuse must return a unique unshared ctor token");

  unsigned long long before = krc_debug_reclaim_count();
  unsigned long long reuse_before = krc_debug_reuse_count();
  KValue *rebuilt = kreuse_ctor(token, KCT_USER_BASE + 11, "S5New", 1, new_args);
  check(rebuilt == box, "S5 reuse_alloc must overwrite the unique token in place");
  check(rebuilt->as.ctor.args == old_args, "S5 reuse_alloc must reuse the existing ctor argument vector");
  check(kctor_tagid(rebuilt) == KCT_USER_BASE + 11, "S5 reuse_alloc must update the ctor tag");
  check(kctor_arg(rebuilt, 0) == new_field, "S5 reuse_alloc must install the new field owner");
  check(krc_debug_reclaim_count() > before, "S5 reuse_alloc must drop the overwritten old field exactly through the RC path");
  check(krc_debug_reuse_count() == reuse_before + 1, "S5 reuse_alloc must record one successful in-place reuse");
  kdrop(rebuilt);
}

static void check_aliased_ctor_falls_back_to_fresh_allocation(void) {
  KValue *box = boxed_ctor1(KCT_USER_BASE + 12, "S5AliasedOld", kstr0("s5-aliased-old"));
  KValue *alias = kdup(box);
  check(krc_count(box) == 2, "S5 alias setup must have two counted owners");

  KValue *token = kdrop_reuse_ctor(box, 1);
  check(token == NULL, "S5 drop_reuse must reject aliased ctors");
  check(krc_count(alias) == 1, "S5 drop_reuse fallback must consume exactly one aliased owner");

  KValue *new_args[1] = { kstr0("s5-aliased-new") };
  KValue *fresh = kreuse_ctor(token, KCT_USER_BASE + 13, "S5AliasedNew", 1, new_args);
  check(fresh != alias, "S5 reuse_alloc NULL-token fallback must allocate a fresh ctor");
  check(kctor_tagid(fresh) == KCT_USER_BASE + 13, "S5 NULL-token fallback must build the requested ctor");
  kdrop(alias);
  kdrop(fresh);
}

static void check_shared_ctor_falls_back_and_reclaims_normally(void) {
  KValue *box = boxed_ctor1(KCT_USER_BASE + 14, "S5SharedOld", kstr0("s5-shared-old"));
  krc_mark_shared_recursive(box);
  check(krc_is_shared(box), "S5 shared setup must mark the ctor shared");

  unsigned long long before = krc_debug_reclaim_count();
  KValue *token = kdrop_reuse_ctor(box, 1);
  check(token == NULL, "S5 drop_reuse must reject shared ctors");
  check(krc_debug_reclaim_count() > before, "S5 shared fallback must use the normal shared drop/free path");

  KValue *new_args[1] = { kstr0("s5-shared-new") };
  KValue *fresh = kreuse_ctor(token, KCT_USER_BASE + 15, "S5SharedNew", 1, new_args);
  check(!kis_imm(fresh) && kctor_tagid(fresh) == KCT_USER_BASE + 15, "S5 shared fallback must build the requested fresh ctor");
  kdrop(fresh);
}

static void check_packed_result_discards_token_for_canonical_immediate(void) {
  KValue *box = boxed_ctor1(KCT_USER_BASE + 16, "S5PackedOld", kstr0("s5-packed-old"));
  KValue *token = kdrop_reuse_ctor(box, 1);
  check(token == box, "S5 packed fallback setup must get a reusable boxed token");

  KValue *new_args[1] = { kint(7) };
  unsigned long long before = krc_debug_reclaim_count();
  KValue *packed = kreuse_ctor(token, KCT_USER_BASE + 17, "S5PackedNew", 1, new_args);
  check(packed != box, "S5 reuse_alloc must not force a boxed cell when kctor would pack");
  check(kis_imm(packed), "S5 packed fallback must return the canonical immediate representation");
  check(kctor_tagid(packed) == KCT_USER_BASE + 17, "S5 packed fallback must preserve the requested tag");
  check(krc_debug_reclaim_count() > before, "S5 packed fallback must drop the discarded token normally");
}

static void check_wrong_arity_falls_back_to_normal_drop(void) {
  KValue *box = boxed_ctor1(KCT_USER_BASE + 18, "S5ArityOld", kstr0("s5-arity-old"));
  unsigned long long before = krc_debug_reclaim_count();
  KValue *token = kdrop_reuse_ctor(box, 2);
  check(token == NULL, "S5 drop_reuse must reject arity-mismatched tokens");
  check(krc_debug_reclaim_count() > before, "S5 arity-mismatch fallback must normal-drop the old ctor");

  KValue *new_args[1] = { kstr0("s5-arity-new") };
  KValue *fresh = kreuse_ctor(token, KCT_USER_BASE + 19, "S5ArityNew", 1, new_args);
  check(!kis_imm(fresh) && kctor_tagid(fresh) == KCT_USER_BASE + 19, "S5 arity fallback must build a fresh ctor");
  kdrop(fresh);
}

static void check_moved_fields_reuse_without_intermediate_child_drops(void) {
  KValue *left = kstr0("s5-left");
  KValue *right = kstr0("s5-right");
  KValue *box = boxed_ctor2(KCT_USER_BASE + 20, "S5MoveOld", left, right);
  KValue **old_args = box->as.ctor.args;
  KValue *new_args[2] = { right, left };
  int move_slots[2] = { 1, 0 };

  unsigned long long before = krc_debug_reclaim_count();
  unsigned long long reuse_before = krc_debug_reuse_count();
  KValue *rebuilt = kdrop_reuse_ctor_alloc(box, 2, KCT_USER_BASE + 21, "S5MoveNew", 2, new_args, move_slots);
  check(rebuilt == box, "S5 fused move rebuild must reuse the unique source cell");
  check(rebuilt->as.ctor.args == old_args, "S5 fused move rebuild must reuse the existing ctor argument vector");
  check(kctor_arg(rebuilt, 0) == right, "S5 fused move rebuild must install moved right field");
  check(kctor_arg(rebuilt, 1) == left, "S5 fused move rebuild must install moved left field");
  check(krc_debug_reclaim_count() == before, "S5 fused move rebuild must not drop moved child fields before final owner drop");
  check(krc_debug_reuse_count() == reuse_before + 1, "S5 fused move rebuild must record one successful in-place reuse");
  kdrop(rebuilt);
}

static void check_moved_fields_fallback_duplicates_before_drop(void) {
  KValue *left = kstr0("s5-fallback-left");
  KValue *right = kstr0("s5-fallback-right");
  KValue *box = boxed_ctor2(KCT_USER_BASE + 22, "S5MoveAliasedOld", left, right);
  KValue *alias = kdup(box);
  KValue *new_args[2] = { right, left };
  int move_slots[2] = { 1, 0 };

  unsigned long long reuse_before = krc_debug_reuse_count();
  KValue *fresh = kdrop_reuse_ctor_alloc(box, 2, KCT_USER_BASE + 23, "S5MoveAliasedNew", 2, new_args, move_slots);
  check(fresh != alias, "S5 fused move fallback must allocate when the source is aliased");
  check(kctor_arg(fresh, 0) == right, "S5 fused move fallback must preserve moved right field");
  check(kctor_arg(fresh, 1) == left, "S5 fused move fallback must preserve moved left field");
  check(krc_count(alias) == 1, "S5 fused move fallback must consume one source owner");
  check(krc_debug_reuse_count() == reuse_before, "S5 fused move fallback must not increment the reuse counter");
  kdrop(alias);
  kdrop(fresh);
}

static void check_skip_reuse_preserves_skipped_fields_and_arg_vector(void) {
  KValue *left = kstr0("s5-skip-left");
  KValue *mid = kstr0("s5-skip-mid");
  KValue *right = kstr0("s5-skip-right");
  KValue *box = boxed_ctor3(KCT_USER_BASE + 24, "S5SkipOld", left, mid, right);
  KValue **old_args = box->as.ctor.args;
  KValue *new_mid = kstr0("s5-skip-new-mid");
  KValue *new_args[3] = { left, new_mid, right };
  int move_slots[3] = { 0, -1, 2 };
  int skip_slots[2] = { 0, 2 };

  KValue *token = ktry_reuse_ctor(box, 3);
  check(token == box, "S5 skip reuse setup must prove a unique token");
  unsigned long long before = krc_debug_reclaim_count();
  unsigned long long reuse_before = krc_debug_reuse_count();
  KValue *rebuilt = kreuse_ctor_skip(token, KCT_USER_BASE + 25, "S5SkipNew", 3, new_args, move_slots, skip_slots, 2);
  check(rebuilt == box, "S5 skip reuse must overwrite the unique token in place");
  check(rebuilt->as.ctor.args == old_args, "S5 skip reuse must reuse the existing ctor argument vector");
  check(kctor_arg(rebuilt, 0) == left, "S5 skip reuse must preserve skipped left field owner");
  check(kctor_arg(rebuilt, 1) == new_mid, "S5 skip reuse must install non-skipped replacement field");
  check(kctor_arg(rebuilt, 2) == right, "S5 skip reuse must preserve skipped right field owner");
  check(krc_debug_reclaim_count() > before, "S5 skip reuse must drop overwritten non-skipped fields through RC");
  check(krc_debug_reuse_count() == reuse_before + 1, "S5 skip reuse must record one successful in-place reuse");
  kdrop(rebuilt);
}

static void check_skip_reuse_always_protects_moved_slots(void) {
  KValue *left = kstr0("s5-skip-move-left");
  KValue *right = kstr0("s5-skip-move-right");
  KValue *box = boxed_ctor2(KCT_USER_BASE + 28, "S5SkipMoveOld", left, right);
  KValue **old_args = box->as.ctor.args;
  KValue *new_args[2] = { right, left };
  int move_slots[2] = { 1, 0 };

  KValue *token = ktry_reuse_ctor(box, 2);
  check(token == box, "S5 skip/move setup must prove a unique token");
  unsigned long long before = krc_debug_reclaim_count();
  unsigned long long reuse_before = krc_debug_reuse_count();
  KValue *rebuilt = kreuse_ctor_skip(token, KCT_USER_BASE + 29, "S5SkipMoveNew", 2, new_args, move_slots, NULL, 0);
  check(rebuilt == box, "S5 skip/move reuse must overwrite the unique token in place");
  check(rebuilt->as.ctor.args == old_args, "S5 skip/move reuse must reuse the existing ctor argument vector");
  check(kctor_arg(rebuilt, 0) == right, "S5 skip/move reuse must preserve moved right field");
  check(kctor_arg(rebuilt, 1) == left, "S5 skip/move reuse must preserve moved left field");
  check(krc_debug_reclaim_count() == before, "S5 skip/move reuse must not reclaim moved fields even when skip_slots omits them");
  check(krc_debug_reuse_count() == reuse_before + 1, "S5 skip/move reuse must record one successful in-place reuse");
  kdrop(rebuilt);
}

static void check_skip_reuse_packed_result_falls_back_to_canonical_ctor(void) {
  KValue *old_field = kstr0("s5-skip-pack-old");
  KValue *old_args[1] = { old_field };
  KValue *box = kctor(KRT2_OP_BASE, "S5SkipPackOld", 1, old_args);
  KValue *new_args[1] = { kint(7) };

  KValue *token = ktry_reuse_ctor(box, 1);
  check(token == box, "S5 skip packed fallback setup must prove a unique token");
  unsigned long long before = krc_debug_reclaim_count();
  unsigned long long reuse_before = krc_debug_reuse_count();
  KValue *rebuilt = kreuse_ctor_skip(token, KCT_USER_BASE + 27, "S5SkipPackNew", 1, new_args, NULL, NULL, 0);
  check(rebuilt != box, "S5 skip packed fallback must not reuse a cell for a canonical immediate result");
  check(kctor_tagid(rebuilt) == KCT_USER_BASE + 27, "S5 skip packed fallback must preserve the new constructor tag");
  check(kctor_arg(rebuilt, 0) == kint(7), "S5 skip packed fallback must preserve the new packed field");
  check(krc_debug_reclaim_count() > before, "S5 skip packed fallback must drop the discarded token normally");
  check(krc_debug_reuse_count() == reuse_before, "S5 skip packed fallback must not count as in-place reuse");
  kdrop(rebuilt);
}

static void check_skip_reuse_packed_result_respects_skip_slots(void) {
  KValue *old_field = kstr0("s5-skip-pack-dead-old");
  KValue *old_args[1] = { old_field };
  KValue *box = kctor(KRT2_OP_BASE, "S5SkipPackDeadOld", 1, old_args);
  KValue *new_args[1] = { kint(8) };
  int skip_slots[1] = { 0 };

  KValue *token = ktry_reuse_ctor(box, 1);
  check(token == box, "S5 skip packed/dead fallback setup must prove a unique token");
  krc_poison_set_enabled(1);
  kdrop(old_field);
  unsigned long long before = krc_debug_reclaim_count();
  unsigned long long reuse_before = krc_debug_reuse_count();
  KValue *rebuilt = kreuse_ctor_skip(token, KCT_USER_BASE + 30, "S5SkipPackDeadNew", 1, new_args, NULL, skip_slots, 1);
  check(rebuilt != box, "S5 skip packed/dead fallback must not reuse a cell for a canonical immediate result");
  check(kctor_arg(rebuilt, 0) == kint(8), "S5 skip packed/dead fallback must preserve the packed field");
  check(krc_debug_reclaim_count() == before + 1, "S5 skip packed/dead fallback must reclaim only the token, not skipped old fields");
  check(krc_debug_reuse_count() == reuse_before, "S5 skip packed/dead fallback must not count as in-place reuse");
  krc_poison_set_enabled(0);
  kdrop(rebuilt);
}

static void bad_null_token_reuse(void) {
  KValue *args[1] = { kunit() };
  int skip_slots[1] = { 0 };
  (void)kreuse_ctor_skip(NULL, KCT_USER_BASE + 26, "S5SkipBad", 1, args, NULL, skip_slots, 1);
}

static void check_skip_reuse_null_token_fails_closed(void) {
  expect_child_failure(bad_null_token_reuse, "S5 skip reuse must fail closed instead of allocating with a NULL token");
}

static void bad_move_slot_reuse(void) {
  KValue *left = kstr0("s5-bad-move-left");
  KValue *right = kstr0("s5-bad-move-right");
  KValue *box = boxed_ctor2(KCT_USER_BASE + 31, "S5BadMoveOld", left, right);
  KValue *new_args[2] = { right, left };
  int bad_move_slots[2] = { 0, 1 };
  KValue *token = ktry_reuse_ctor(box, 2);
  check(token == box, "S5 bad-move setup must prove a unique token");
  (void)kreuse_ctor_skip(token, KCT_USER_BASE + 32, "S5BadMoveNew", 2, new_args, bad_move_slots, NULL, 0);
}

static void check_skip_reuse_invalid_move_slots_fail_closed(void) {
  expect_child_failure(bad_move_slot_reuse, "S5 skip reuse must fail closed when move slots do not match the token fields");
}

static void bad_fused_move_slot_reuse(void) {
  KValue *left = kstr0("s5-bad-fused-move-left");
  KValue *right = kstr0("s5-bad-fused-move-right");
  KValue *box = boxed_ctor2(KCT_USER_BASE + 33, "S5BadFusedMoveOld", left, right);
  KValue *new_args[2] = { right, left };
  int bad_move_slots[2] = { 0, 1 };
  (void)kdrop_reuse_ctor_alloc(box, 2, KCT_USER_BASE + 34, "S5BadFusedMoveNew", 2, new_args, bad_move_slots);
}

static void check_fused_reuse_invalid_move_slots_fail_closed(void) {
  expect_child_failure(bad_fused_move_slot_reuse, "S5 fused reuse must fail closed when move slots do not match the source fields");
}

int main(void) {
  krt_init();
  check_unique_ctor_reuses_cell_and_drops_old_field();
  check_aliased_ctor_falls_back_to_fresh_allocation();
  check_shared_ctor_falls_back_and_reclaims_normally();
  check_packed_result_discards_token_for_canonical_immediate();
  check_wrong_arity_falls_back_to_normal_drop();
  check_moved_fields_reuse_without_intermediate_child_drops();
  check_moved_fields_fallback_duplicates_before_drop();
  check_skip_reuse_preserves_skipped_fields_and_arg_vector();
  check_skip_reuse_always_protects_moved_slots();
  check_skip_reuse_packed_result_falls_back_to_canonical_ctor();
  check_skip_reuse_packed_result_respects_skip_slots();
  check_skip_reuse_null_token_fails_closed();
  check_skip_reuse_invalid_move_slots_fail_closed();
  check_fused_reuse_invalid_move_slots_fail_closed();
  return 0;
}
