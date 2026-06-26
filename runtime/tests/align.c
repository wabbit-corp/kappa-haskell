/* align.c — value-unboxing GC/alignment contract (UNBOXING-DESIGN §5.4).
 *
 * Stage 0 established the contract: every *heap* KValue* the runtime hands out
 * has its low 3 bits clear (8-byte aligned), so a real pointer never collides
 * with an immediate's tag and the low 3 bits are free for the discriminator.
 *
 * Stage 1 turns that latent budget on for Int: a small Int (61-bit range) is a
 * b001 IMMEDIATE packed into the KValue* word ((value << 3) | KIMM_INT).  Stage
 * 1b extends it to EVERY nullary ctor: a 0-field constructor of any ADT (Unit /
 * Bool / Nil / None / a user enum variant) is a b010 IMMEDIATE ((tagId << 3) |
 * KIMM_CTOR) — NOT a heap pointer.  Stage 1d packs a SINGLE-field ctor whose one
 * field is itself an immediate (and whose id fits 20 bits) into a b011 IMMEDIATE
 * ([field-word | tagId | KIMM_PACKED]).  Only a multi-field ctor, a single-field
 * ctor over a HEAP field / too-big immediate, a string / ref / Double / out-of-
 * 61-bit Int stays an 8-aligned heap box.  This harness verifies all of the
 * post-Stage-1d contract:
 *   - heap boxes (multi-field ctors, boxed-field single ctors, strings, refs)
 *     are still 8-aligned (a missed alignment makes tagging unsound);
 *   - in-range Ints are b001 immediates that round-trip through kas_int exactly,
 *     and out-of-range Ints fall back to an 8-aligned heap box;
 *   - nullary ctors are b010 immediates that round-trip through kctor_tagid and
 *     report 0 args (kctor_argc);
 *   - single-field ctors over a packing immediate are b011 immediates that
 *     round-trip the tag id (kctor_tagid), report 1 arg (kctor_argc), and project
 *     the field back exactly (kctor_arg).
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

static int fails = 0;
static void aligned(KValue *v, const char *what) {
  if (((uintptr_t)v & 7u) != 0) {
    fprintf(stderr, "  FAIL: %s not 8-aligned: %p (low3 = %lu)\n",
            what, (void *)v, (unsigned long)((uintptr_t)v & 7u));
    fails++;
  }
}

/* A small Int must be a b001 immediate (NOT a heap pointer) and recover its
 * value exactly through kas_int; the runtime must agree it is not a pointer. */
static void imm_int(int64_t i) {
  KValue *v = kint(i);
  if (!kis_imm_int(v)) {
    fprintf(stderr, "  FAIL: kint(%" PRId64 ") is not an immediate Int (%p)\n", i, (void *)v);
    fails++;
  }
  if (kis_imm_int(v) && kas_int(v) != i) {
    fprintf(stderr, "  FAIL: kint(%" PRId64 ") round-trips to %" PRId64 "\n", i, kas_int(v));
    fails++;
  }
}

/* An out-of-61-bit Int must be a heap box (8-aligned, not an immediate) and
 * still recover its value through kas_int. */
static void boxed_int(int64_t i) {
  KValue *v = kint(i);
  if (kis_imm(v)) {
    fprintf(stderr, "  FAIL: kint(%" PRId64 ") tagged immediate but is out of range\n", i);
    fails++;
  }
  aligned(v, "kint heap (out of immediate range)");
  if (!kis_imm(v) && kas_int(v) != i) {
    fprintf(stderr, "  FAIL: boxed kint(%" PRId64 ") round-trips to %" PRId64 "\n", i, kas_int(v));
    fails++;
  }
}

/* A nullary ctor must be a b010 immediate (NOT a heap pointer) carrying the
 * tag id, with 0 args, recovered through kctor_tagid / kctor_argc. */
static void imm_ctor(KValue *v, int tagid, const char *what) {
  if (!kis_imm_ctor(v)) {
    fprintf(stderr, "  FAIL: %s is not a b010 nullary immediate (%p, low3=%lu)\n",
            what, (void *)v, (unsigned long)((uintptr_t)v & 7u));
    fails++;
    return;
  }
  if (kctor_tagid(v) != tagid) {
    fprintf(stderr, "  FAIL: %s tagid %d, expected %d\n", what, kctor_tagid(v), tagid);
    fails++;
  }
  if (kctor_argc(v) != 0) {
    fprintf(stderr, "  FAIL: %s argc %d, expected 0\n", what, kctor_argc(v));
    fails++;
  }
}

/* A single-field ctor over a PACKING immediate field must be a b011 packed
 * immediate (NOT a heap pointer) carrying the tag id, with 1 arg, and project the
 * field back to a value equal to the original. */
static void imm_packed(int tagid, KValue *field, const char *what) {
  KValue *a[1] = { field };
  KValue *v = kctor(tagid, what, 1, a);
  if (!kis_imm_packed(v)) {
    fprintf(stderr, "  FAIL: %s is not a b011 packed immediate (%p, low3=%lu)\n",
            what, (void *)v, (unsigned long)((uintptr_t)v & 7u));
    fails++;
    return;
  }
  if (kctor_tagid(v) != tagid) {
    fprintf(stderr, "  FAIL: %s tagid %d, expected %d\n", what, kctor_tagid(v), tagid);
    fails++;
  }
  if (kctor_argc(v) != 1) {
    fprintf(stderr, "  FAIL: %s argc %d, expected 1\n", what, kctor_argc(v));
    fails++;
  }
  /* The field is a packing immediate, which canonicalizes: word identity IS value
   * identity, so the recovered field word must equal the original word exactly. */
  if (kctor_arg(v, 0) != field) {
    fprintf(stderr, "  FAIL: %s field did not round-trip (%p != %p)\n",
            what, (void *)kctor_arg(v, 0), (void *)field);
    fails++;
  }
}

/* A single-field ctor whose field is a HEAP pointer (or a too-big immediate, or
 * whose id does not fit 20 bits) must stay an 8-aligned heap box. */
static void boxed_single(int tagid, KValue *field, const char *what) {
  KValue *a[1] = { field };
  KValue *v = kctor(tagid, what, 1, a);
  if (kis_imm(v)) {
    fprintf(stderr, "  FAIL: %s should stay boxed but is a tagged immediate (%p)\n",
            what, (void *)v);
    fails++;
    return;
  }
  aligned(v, what);
  /* The same field pointer goes in and comes back out of the boxed ctor. */
  if (kctor_argc(v) != 1 || kctor_arg(v, 0) != field) {
    fprintf(stderr, "  FAIL: boxed %s did not round-trip its field\n", what);
    fails++;
  }
}

int main(void) {
  krt2_new(1); /* initialize the runtime + threaded Boehm GC */

  /* Stage 1b: the nullary builtins are now b010 IMMEDIATES, not heap boxes —
   * one canonical representation each, alloc-free, id recovered without a deref. */
  imm_ctor(kunit(),  KCT_UNIT,  "kunit");
  imm_ctor(kbool(0), KCT_FALSE, "kbool false");
  imm_ctor(kbool(1), KCT_TRUE,  "kbool true");
  /* a user-id nullary ctor (KCT_USER_BASE+) is likewise a b010 immediate */
  imm_ctor(kctor0(KCT_USER_BASE + 3, "GameMode.Quit"), KCT_USER_BASE + 3, "kctor0 user");
  imm_ctor(kctor(KCT_USER_BASE + 7, "Enum.V", 0, NULL), KCT_USER_BASE + 7, "kctor argc=0");

  /* Stage 1d: a single-field ctor over a PACKING immediate field is a b011
   * packed immediate — alloc-free, id + field recovered without a deref. */
  imm_packed(KCT_SOME, kint(5),    "Some(5)");           /* Option<Int>, field b001 */
  imm_packed(KCT_SOME, kint(-1),   "Some(-1)");          /* a negative field word    */
  imm_packed(KCT_SOME, kint(0),    "Some(0)");
  imm_packed(KCT_SOME, kbool(1),   "Some(True)");        /* Option<Bool>, field b010 */
  imm_packed(KCT_SOME, kctor0(KCT_USER_BASE + 2, "E"), "Some(enum)"); /* field b010, user id */
  imm_packed(KCT_SOME, kint(KIMM_PACKED_FIELD_MAX >> 3), "Some(field-max)"); /* near the top edge */
  imm_packed(KCT_USER_BASE + 5, kint(9), "User(9)");     /* a user single-field id   */
  imm_packed(KCT_SOME, kmk_imm_packed(KCT_SOME, kint(5)), "Some(Some(5))"); /* nested, if it fits */

  /* a single-field ctor over a HEAP field stays an 8-aligned box (Option<List>
   * shape) — the field is a real pointer, so it cannot ride in the word. */
  boxed_single(KCT_SOME, kstr0("heap"), "Some(string)");
  boxed_single(KCT_SOME, kref_new(kunit()), "Some(ref)");
  /* a field that is a too-big immediate Int (does not fit the 41-bit payload)
   * also stays boxed. */
  boxed_single(KCT_SOME, kint(((int64_t)1 << 55)), "Some(huge)");
  /* an OP-style id above the 20-bit discriminant must NOT pack even over an
   * immediate field (the CK-machine reads its id; truncation would misdispatch). */
  boxed_single(0x40000000, kint(3), "OP-id single");

  /* small ints: now b001 immediates across the former cache range and beyond */
  for (int64_t i = -300; i <= 300; i++) imm_int(i);
  /* the immediate-range edges round-trip exactly */
  imm_int(KIMM_INT_MIN);
  imm_int(KIMM_INT_MAX);
  imm_int(0);
  imm_int(-1);

  /* one past each edge of the immediate range must fall back to a heap bignum */
  boxed_int(KIMM_INT_MAX + 1);
  boxed_int(KIMM_INT_MIN - 1);
  boxed_int(((int64_t)1 << 62));
  boxed_int(-((int64_t)1 << 62));

  /* a churn of freshly-allocated boxes of assorted shapes, forcing the
   * thread-local freelist refill + a few collections along the way.  Note kint(i)
   * and the nullary kctor0 here are immediates (no allocation); the boxes are the
   * n-ary ctor / string / ref. */
  for (int i = 0; i < 20000; i++) {
    imm_ctor(kctor0(KCT_OTHER, "Tag"), KCT_OTHER, "kctor0 churn"); /* b010, no alloc */
    /* Stage 1d: a 1-ary ctor over the small immediate kint(i) now PACKS into a
     * b011 word (no allocation) — assert that, not heap alignment. */
    imm_packed(KCT_USER_BASE + 1, kint(i), "kctor pack churn");
    /* a 1-ary ctor over a HEAP field is the boxed control that still allocates. */
    KValue *hp[1] = {kstr0("heap-field")};
    aligned(kctor(1, "Box", 1, hp), "kctor heap-field"); /* 1-ary boxed: heap field */
    aligned(kstr0("alignment"), "kstr0");
    aligned(kref_new(kunit()), "kref_new");
  }

  if (fails == 0) {
    fprintf(stderr, "PASS: align (heap boxes 8-aligned; small Ints are b001 immediates; "
                    "nullary ctors are b010 immediates; single-field ctors over a "
                    "packing immediate are b011 packed immediates — all round-trip)\n");
    return 0;
  }
  fprintf(stderr, "FAIL: align (%d contract violations)\n", fails);
  return 1;
}
