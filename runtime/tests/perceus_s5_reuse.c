#include "internal.h"

#include <stdio.h>
#include <stdlib.h>

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

static void check_unique_ctor_reuses_cell_and_drops_old_field(void) {
  KValue *old_field = kstr0("s5-old");
  KValue *box = boxed_ctor1(KCT_USER_BASE + 10, "S5Old", old_field);
  KValue *new_field = kstr0("s5-new");
  KValue *new_args[1] = { new_field };

  KValue *token = kdrop_reuse_ctor(box, 1);
  check(token == box, "S5 drop_reuse must return a unique unshared ctor token");

  unsigned long long before = krc_debug_reclaim_count();
  KValue *rebuilt = kreuse_ctor(token, KCT_USER_BASE + 11, "S5New", 1, new_args);
  check(rebuilt == box, "S5 reuse_alloc must overwrite the unique token in place");
  check(kctor_tagid(rebuilt) == KCT_USER_BASE + 11, "S5 reuse_alloc must update the ctor tag");
  check(kctor_arg(rebuilt, 0) == new_field, "S5 reuse_alloc must install the new field owner");
  check(krc_debug_reclaim_count() > before, "S5 reuse_alloc must drop the overwritten old field exactly through the RC path");
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
  KValue *new_args[2] = { right, left };
  int move_slots[2] = { 1, 0 };

  unsigned long long before = krc_debug_reclaim_count();
  KValue *rebuilt = kdrop_reuse_ctor_alloc(box, 2, KCT_USER_BASE + 21, "S5MoveNew", 2, new_args, move_slots);
  check(rebuilt == box, "S5 fused move rebuild must reuse the unique source cell");
  check(kctor_arg(rebuilt, 0) == right, "S5 fused move rebuild must install moved right field");
  check(kctor_arg(rebuilt, 1) == left, "S5 fused move rebuild must install moved left field");
  check(krc_debug_reclaim_count() == before, "S5 fused move rebuild must not drop moved child fields before final owner drop");
  kdrop(rebuilt);
}

static void check_moved_fields_fallback_duplicates_before_drop(void) {
  KValue *left = kstr0("s5-fallback-left");
  KValue *right = kstr0("s5-fallback-right");
  KValue *box = boxed_ctor2(KCT_USER_BASE + 22, "S5MoveAliasedOld", left, right);
  KValue *alias = kdup(box);
  KValue *new_args[2] = { right, left };
  int move_slots[2] = { 1, 0 };

  KValue *fresh = kdrop_reuse_ctor_alloc(box, 2, KCT_USER_BASE + 23, "S5MoveAliasedNew", 2, new_args, move_slots);
  check(fresh != alias, "S5 fused move fallback must allocate when the source is aliased");
  check(kctor_arg(fresh, 0) == right, "S5 fused move fallback must preserve moved right field");
  check(kctor_arg(fresh, 1) == left, "S5 fused move fallback must preserve moved left field");
  check(krc_count(alias) == 1, "S5 fused move fallback must consume one source owner");
  kdrop(alias);
  kdrop(fresh);
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
  return 0;
}
