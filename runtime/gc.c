/* gc.c — GC/GMP boot, the public allocators, and krt_fail.
 *
 * Split out of kappart.c (see boxed.h).  Owns the Boehm collector +
 * GMP-allocator wiring (krt_init), the immediate-tag alignment contract check,
 * the two public allocators (kgc_alloc / kgc_alloc_atomic), and the fail-stop. */
#include "kappart.h"
#include "boxed.h"

#include <gc.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdatomic.h>
/* ── lifecycle / allocation ────────────────────────────────────────── */

/* Route GMP allocation through the Boehm collector so bignum limbs are
 * GC-managed (free is a no-op; the collector reclaims). */
static void *gmp_gc_alloc(size_t n) { return GC_MALLOC(n); }
static void *gmp_gc_realloc(void *p, size_t old, size_t n) {
  (void)old;
  return GC_REALLOC(p, n);
}
static void gmp_gc_free(void *p, size_t n) { (void)p; (void)n; }

/* QW4: optional allocation/GC report at exit, gated by $KAPPA_GC_STATS, for
 * the native benchmark gates (test/native/bench.sh).  Off unless the env var
 * is set, so normal runs are unaffected. */
static _Atomic unsigned long long g_kgc_frees_total = 0;

static void krt_at_exit(void) {
  if (getenv("KAPPA_GC_STATS")) {
    fprintf(stderr, "[kappa-gc] total_bytes=%zu heap_size=%zu collections=%lu frees=%llu reuses=%llu\n",
            (size_t)GC_get_total_bytes(), (size_t)GC_get_heap_size(),
            (unsigned long)GC_get_gc_no(),
            atomic_load_explicit(&g_kgc_frees_total, memory_order_relaxed),
            krc_debug_reuse_count());
  }
}

/* UNBOXING Stage 0 (§5.4): the immediate-tagging scheme requires GC_MALLOC (and
 * thus gmp_gc_alloc, the same allocator) to return >= 8-byte-aligned pointers so
 * the low 3 bits of a KValue* word are always free.  Verify at startup, failing
 * closed, rather than silently miscompiling on a hypothetical under-aligned
 * platform.  (Boehm returns >= 16-byte-aligned objects on 64-bit targets.) */
static void krt_assert_gc_alignment(void) {
  for (size_t n = 8; n < 8 + 16; n++) {
    void *p = GC_MALLOC(n);
    if (((uintptr_t)p & 0x7u) != 0)
      krt_fail("UNBOXING: GC_MALLOC returned a non-8-aligned pointer (tag-bit contract violated)");
  }
}

static int env_truthy(const char *s) {
  return s && strcmp(s, "0") != 0 && strcmp(s, "false") != 0
         && strcmp(s, "FALSE") != 0 && strcmp(s, "off") != 0
         && strcmp(s, "OFF") != 0 && strcmp(s, "no") != 0
         && strcmp(s, "NO") != 0 && s[0] != '\0';
}

void krt_init(void) {
  /* UNBOXING Stage 0 (§5.4): turn OFF interior-pointer recognition BEFORE
   * GC_INIT, so the collector roots only BASE pointers.  The (future) immediate
   * tagging packs small values into the low 3 bits of a KValue* word; a tagged
   * immediate must not be mistaken for a (possibly interior) heap pointer and
   * falsely retain an object.  The runtime only ever holds base KValue and array
   * pointers (never an interior pointer as the sole reference to an object), so
   * base-only rooting is safe — verified by the native suite + parity corpus. */
  GC_set_all_interior_pointers(0);
  GC_INIT();
#ifdef KRT2_TSAN
  /* ThreadSanitizer does not understand Boehm's custom heap reuse as malloc/free
   * lifetime boundaries, so it can report independent writes to recycled cells as
   * races. The TSan lane is for scheduler/header data races, not reclamation;
   * normal and poison lanes still exercise real GC_FREE. */
  GC_disable();
#endif
  krt_assert_gc_alignment();
  mp_set_memory_functions(gmp_gc_alloc, gmp_gc_realloc, gmp_gc_free);
  atexit(krt_at_exit);
  /* Perceus RC Stage S2.3 (PERCEUS-S2-PLAN (c) secondary): the SOFT leak-trend
   * probe.  When KAPPA_RC_REPORT is set in the environment, print the dup/drop
   * totals + net (drops - dups) at process exit — a missed drop shows as a
   * newly-positive net.  GATED so the default run prints NOTHING (byte-identical
   * output preserved); the env var is read once here, not a program input. */
  if (getenv("KAPPA_RC_REPORT")) atexit(krc_report);
  if (env_truthy(getenv("KAPPA_POISON"))) krc_poison_set_enabled(1);
}

void *kgc_alloc(size_t n) {
  void *p = GC_MALLOC(n);
  if (!p) krt_fail("out of memory (GC_MALLOC)");
  return p;
}

void *kgc_alloc_atomic(size_t n) {
  void *p = GC_MALLOC_ATOMIC(n);
  if (!p) krt_fail("out of memory (GC_MALLOC_ATOMIC)");
  return p;
}

void kgc_free(void *p) {
  if (!p) return;
  atomic_fetch_add_explicit(&g_kgc_frees_total, 1, memory_order_relaxed);
#ifdef KRT2_TSAN
  (void)p;
#else
  GC_FREE(p);
#endif
}

unsigned long long kgc_debug_free_count(void) {
  return atomic_load_explicit(&g_kgc_frees_total, memory_order_relaxed);
}

void krt_fail(const char *msg) {
  fflush(stdout);
  fprintf(stderr, "kappa: runtime failure: %s\n", msg);
  exit(1);
}
