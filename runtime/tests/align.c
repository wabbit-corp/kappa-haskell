/* align.c — Stage 0 of value unboxing (UNBOXING-DESIGN §5.4): verify the
 * GC/alignment contract the future immediate-int tagging depends on.
 *
 * Immediate tagging will pack a small Int/Bool/Char/Unit INTO the KValue*-sized
 * word as e.g. (i<<1)|1, and discriminate it from a heap pointer by the low
 * bit(s).  That is only sound if EVERY KValue* the runtime hands out has its low
 * 3 bits clear (8-byte aligned), so:
 *   - a real pointer never collides with an immediate's tag, and
 *   - the low 3 bits are free for the ptr / scalar / borrow-or-thread-shared tag
 *     a future Perceus RC needs (UNBOXING-DESIGN §5.4 reserves all three).
 *
 * This harness fails closed if Boehm ever returns a pointer that is not 8-aligned
 * (it never should on a 64-bit target — GC_MALLOC aligns to >= the word size),
 * across cached + uncached ints, ctors, strings, refs, and the singletons.
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <stdio.h>
#include <stdint.h>

static int fails = 0;
static void aligned(KValue *v, const char *what) {
  if (((uintptr_t)v & 7u) != 0) {
    fprintf(stderr, "  FAIL: %s not 8-aligned: %p (low3 = %lu)\n",
            what, (void *)v, (unsigned long)((uintptr_t)v & 7u));
    fails++;
  }
}

int main(void) {
  krt2_new(1); /* initialize the runtime + threaded Boehm GC */

  /* the immutable singletons */
  aligned(kunit(), "kunit");
  aligned(kbool(0), "kbool false");
  aligned(kbool(1), "kbool true");

  /* cached small ints AND uncached ones (outside the [-16,256] cache) */
  for (int i = -300; i <= 300; i++) aligned(kint(i), "kint small");

  /* a churn of freshly-allocated boxes of assorted shapes, forcing the
   * thread-local freelist refill + a few collections along the way */
  for (int i = 0; i < 20000; i++) {
    aligned(kint(1000000 + i), "kint heap");
    aligned(kctor0(0, "Tag"), "kctor0");
    KValue *a[1] = {kint(i)};
    aligned(kctor(1, "Box", 1, a), "kctor");
    aligned(kstr0("alignment"), "kstr0");
    aligned(kref_new(kunit()), "kref_new");
  }

  if (fails == 0) {
    fprintf(stderr, "PASS: align (every KValue* is 8-aligned; low 3 bits free for the immediate/scalar tag)\n");
    return 0;
  }
  fprintf(stderr, "FAIL: align (%d unaligned values — immediate tagging would be UNSOUND here)\n", fails);
  return 1;
}
