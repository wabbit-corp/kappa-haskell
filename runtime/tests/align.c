/* align.c — value-unboxing GC/alignment contract (UNBOXING-DESIGN §5.4).
 *
 * Stage 0 established the contract: every *heap* KValue* the runtime hands out
 * has its low 3 bits clear (8-byte aligned), so a real pointer never collides
 * with an immediate's tag and the low 3 bits are free for the discriminator.
 *
 * Stage 1 turns that latent budget on for Int: a small Int (61-bit range) is now
 * a b001 IMMEDIATE packed into the KValue* word ((value << 3) | KIMM_INT) — NOT
 * a heap pointer — while every other value (ctor / string / ref / Double / the
 * singletons / out-of-61-bit Int) stays an 8-aligned heap box.  This harness
 * verifies BOTH halves of the post-Stage-1 contract:
 *   - heap boxes are still 8-aligned (a missed alignment makes tagging unsound);
 *   - in-range Ints are immediates that round-trip through kas_int exactly, and
 *     out-of-range Ints fall back to an 8-aligned heap box.
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

int main(void) {
  krt2_new(1); /* initialize the runtime + threaded Boehm GC */

  /* the immutable singletons are still heap boxes (Stage 1 keeps Unit/Bool boxed;
   * the immediate-ctor phase is secondary/future work). */
  aligned(kunit(), "kunit");
  aligned(kbool(0), "kbool false");
  aligned(kbool(1), "kbool true");

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
   * here is an immediate (no allocation); the boxes are the ctors/strings/refs. */
  for (int i = 0; i < 20000; i++) {
    aligned(kctor0(0, "Tag"), "kctor0");
    KValue *a[1] = {kint(i)};
    aligned(kctor(1, "Box", 1, a), "kctor");
    aligned(kstr0("alignment"), "kstr0");
    aligned(kref_new(kunit()), "kref_new");
  }

  if (fails == 0) {
    fprintf(stderr, "PASS: align (heap boxes 8-aligned; small Ints are b001 immediates that round-trip)\n");
    return 0;
  }
  fprintf(stderr, "FAIL: align (%d contract violations)\n", fails);
  return 1;
}
