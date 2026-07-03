#include "internal.h"

#include <stdio.h>
#include <stdlib.h>

static void check(int cond, const char *msg) {
  if (!cond) {
    fprintf(stderr, "%s\n", msg);
    exit(1);
  }
}

static void check_unique_tree_frees_on_zero(void) {
  KValue *leaf = kstr0("leaf");
  KValue *args[1] = { leaf };
  KValue *root = kctor(KCT_USER_BASE, "Root", 1, args);
  unsigned long long before = kgc_debug_free_count();
  kdrop(root);
  unsigned long long after = kgc_debug_free_count();
  check(after > before, "S3.2 kdrop of a unique freeable tree must release at least one object");
}

static void check_shared_and_retained_tags_do_not_free(void) {
  KValue *shared = kstr0("shared");
  krc_mark_shared_recursive(shared);
  unsigned long long before_shared = kgc_debug_free_count();
  kdrop(shared);
  check(kgc_debug_free_count() == before_shared, "shared freeable-tag values must remain retained until S4");

  KValue *ref = kref_new(kunit());
  unsigned long long before_ref = kgc_debug_free_count();
  kdrop(ref);
  check(kgc_debug_free_count() == before_ref, "mutable refs must not be freed by S3.2 kdrop");
}

static void check_deep_free_is_iterative(void) {
  enum { DEPTH = 20000 };
  KValue *spine = kstr0("end");
  for (int i = 0; i < DEPTH; i++) {
    KValue *args[1] = { spine };
    spine = kctor(KCT_USER_BASE + 1, "Cons", 1, args);
  }
  unsigned long long before = kgc_debug_free_count();
  kdrop(spine);
  unsigned long long after = kgc_debug_free_count();
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

int main(void) {
  krt_init();
  check_unique_tree_frees_on_zero();
  check_shared_and_retained_tags_do_not_free();
  check_deep_free_is_iterative();
  check_record_rest_keeps_field_alive();
  return 0;
}
