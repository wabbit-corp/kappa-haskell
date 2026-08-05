/* mask_frame_lifetime.c -- stale restore tokens are inert, non-retaining values.
 *
 * A restore closure may outlive its dynamic mask region.  Once that region is
 * popped, its frame must no longer retain either the completed owner fiber or
 * the older mask-frame chain. */
#include "internal.h"

#include <stdio.h>
#include <string.h>

static int fails = 0;
#define CHECK(c, m) do { if (!(c)) { fprintf(stderr, "  FAIL: %s\n", m); fails++; } } while (0)

int main(void) {
  Fiber fiber;
  memset(&fiber, 0, sizeof fiber);
  fiber.mask_base = KMASK_INTERRUPTIBLE;
  fiber.mask_effective = KMASK_INTERRUPTIBLE;

  MaskFrame *outer = krt2i_mask_push(&fiber, KMASK_MASKED);
  MaskFrame *inner = krt2i_mask_push(&fiber, KMASK_UNINTERRUPTIBLE);
  krt2i_mask_pop(&fiber, inner);

  CHECK(!inner->active, "popped frame is inactive");
  CHECK(inner->owner == NULL, "popped frame releases its owner fiber");
  CHECK(inner->prev == NULL, "popped frame releases its parent chain");
  CHECK(krt2i_mask_suspend(&fiber, inner) == 0, "stale restore token is inert");

  krt2i_mask_pop(&fiber, outer);
  CHECK(outer->owner == NULL, "outer popped frame releases its owner fiber");
  CHECK(outer->prev == NULL, "outer popped frame releases its parent chain");
  CHECK(krt2i_mask_state(&fiber) == KMASK_INTERRUPTIBLE,
        "popping all frames restores the base mask state");

  if (fails == 0) {
    fprintf(stderr, "PASS: mask_frame_lifetime (stale restore frames are inert and non-retaining)\n");
    return 0;
  }
  fprintf(stderr, "FAIL: mask_frame_lifetime (%d checks failed)\n", fails);
  return 1;
}
