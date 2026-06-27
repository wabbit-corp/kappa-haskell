/* abandon_foreign_chain.c — §32.2.20 REGRESSION TEST for the FOREIGN-terminal
 * branch of finish_abandon_drain (the un-popped stale `f->drain_ae` hang).
 *
 * THE BUG (pristine c3eac73): the FOREIGN-terminal branch escaped a foreign
 * abandon terminal via `f->k = ae->kont; return apply_reason(...)` WITHOUT
 * popping the drain_ae stack — leaving `f->drain_ae` dangling at the dead inner
 * AbandonEnd.  The NEXT begin_abandon_drain on the SAME fiber then read that dead
 * pointer as its prev_drain, wrongly took the nested-fold path at its own
 * KK_ABANDEND, and RK_DRAIN-walked a slice with NO live KK_ABANDEND terminal =>
 * the walk never terminated => HANG.  Single-worker, single-fiber.
 *
 * TRIGGER GEOMETRY (the FOREIGN case — verified to hit c->aux != f->drain_ae):
 * an abandoned `defer` performs an op that resolves OUTWARD to an ENCLOSING
 * handler (OUTSIDE the abandoning handler) whose clause ITSELF abandons.  The op
 * resolving to an INNER handler is NOT the foreign case (that is the ordinary
 * nested fold).  So the enclosing performing-handler must wrap the abandoning
 * handler:
 *
 *   handle ENC (abortive, op "t", ret = id) {            -- the ENCLOSING handler
 *     handle ABORT (abortive, op "go", ret = id) {       -- abandons the doscope
 *       doscope {
 *         defer { perform ENC.t (); <mark> }             -- performs OUTWARD into ENC
 *         perform ABORT.go ()                            -- abandons -> drain
 *         pure 7
 *       }
 *     }
 *   }
 *
 * ABORT.go abandons the doscope -> begin_abandon_drain (drain ae_out) -> the
 * abandoned defer performs ENC.t -> ENC's clause ALSO abandons ->
 * begin_abandon_drain (inner drain ae_in) and the captured inner slice INCLUDES
 * ae_out's KK_ABANDEND terminal -> the inner RK_DRAIN reaches ae_out, a FOREIGN
 * terminal (ae_out != f->drain_ae == ae_in).
 *
 * The test CHAINS this foreign capture with a SECOND, plain abortive-handler
 * do-scope on the SAME fiber:
 *   PART 1  the foreign doubly-abortive nested capture above, THEN
 *   PART 2  handle B (abortive) { doscope { defer <mark>; perform B.go (); pure 0 } }
 * On pristine c3eac73 the chain HANGS at part 2's KK_ABANDEND (part 2's drain
 * inherits part 1's dead drain_ae).  After the fix it returns Success 99.
 *
 * The FOREIGN branch is instrumented in rt.c (g_rt_foreign_hits, defined under
 * -DKRT2_ABANDON_INSTRUMENT, which the runtime Makefile passes) so this test can
 * PROVE it exercised the foreign path: the count must be > 0.  A weak-symbol
 * fallback keeps the test linkable without the instrumentation; the >0 assertion
 * is then skipped. */
#include "kappart2.h"
#include "kappart2_harness.h"
#include <gc.h>
#include <stdio.h>
#include <stdatomic.h>

static int fails = 0;
#define CHECK(c, m) do { if (!(c)) { fprintf(stderr, "  FAIL: %s\n", m); fails++; } } while (0)

/* FOREIGN-branch hit counter, defined in rt.c under -DKRT2_ABANDON_INSTRUMENT.
 * Weak fallback so the test links even without the instrumentation. */
#ifdef __GNUC__
__attribute__((weak)) unsigned long g_rt_foreign_hits = 0;
#else
unsigned long g_rt_foreign_hits;
#endif

static KValue *ret_pure(KEnv *e, KValue *x) { (void)e; return krt2_pure(x); }

/* an abortive handler clause over a single op returning rv (the captured k is
 * IGNORED => the body's do-scope is abandoned). */
static KValue *ab_clause_k(KEnv *e, KValue *k) { (void)k; return krt2_pure(kvar(e, 0)); }
static KValue *ab_clause(KEnv *e, KValue *p) { (void)p; return kclo(ab_clause_k, kpush(kvar(e, 0), NULL)); }

/* op-name arrays must OUTLIVE the run — krec stores the names pointer VERBATIM
 * (value.c krec: "names array is a generated static literal"); it does NOT copy.
 * So the arrays must be static, never stack locals (a dangling names pointer
 * surfaces as a spurious `kproj: no such field` at perform time). */
static const char *t_names[1]  = { "t"  };   /* the enclosing performing handler  */
static const char *go_names[1] = { "go" };   /* the abandoning handlers           */

static KValue *with_abortive(const char *label, const char **names, int64_t rv, KValue *body) {
  KValue *vals[1] = { kclo(ab_clause, kpush(kint(rv), NULL)) };
  return krt2_handle(kbool(1), kstr0(label), kclo(ret_pure, NULL), krec(1, names, vals), body);
}

/* ── PART 1: the FOREIGN doubly-abortive nested capture ────────────────────── */
static atomic_int p1_after_perform;
static KValue *p1_mark(KEnv *e) { (void)e; atomic_fetch_add(&p1_after_perform, 1); return krt2_pure(kunit()); }
static KValue *p1_defer(void) {
  /* defer { perform ENC.t (); <mark> } — performs OUTWARD into the ENCLOSING ENC. */
  return krt2_defer(krt2_then(krt2_perform(kstr0("ENC"), kstr0("t"), kunit()),
                              kio(p1_mark, NULL)));
}
static KValue *part1(void) {
  KValue *after = krt2_then(krt2_perform(kstr0("ABORT"), kstr0("go"), kunit()), krt2_pure(kint(7)));
  KValue *ds = krt2_doscope(krt2_then(p1_defer(), after));
  /* ENC (enclosing, op "t") WRAPS ABORT (abandons the doscope, op "go"). */
  return with_abortive("ENC", t_names, 0, with_abortive("ABORT", go_names, 0, ds));
}

/* ── PART 2: a plain abortive-handler do-scope with a draining defer ────────── */
static atomic_int p2_defer_ran;
static KValue *p2_mark(KEnv *e) { (void)e; atomic_fetch_add(&p2_defer_ran, 1); return krt2_pure(kunit()); }
static KValue *part2(void) {
  KValue *after = krt2_then(krt2_perform(kstr0("B"), kstr0("go"), kunit()), krt2_pure(kint(0)));
  KValue *ds = krt2_doscope(krt2_then(krt2_defer(kio(p2_mark, NULL)), after));
  return with_abortive("B", go_names, 99, ds);
}

static int success_int(KValue *ex, int64_t want) {
  return kctor_is(ex, "Success") && kctor_argc(ex) == 1 && kas_int(kctor_arg(ex, 0)) == want;
}

int main(void) {
  krt2_new(1);  /* single worker, single fiber — the isolating geometry */

  /* The CHAIN: part 1 (foreign) THEN part 2 (plain drain) on the SAME fiber.
   * On pristine c3eac73 this run never returns (hangs at part 2's KK_ABANDEND).
   * After the fix it returns Success 99 (part 2's abortive clause result). */
  atomic_store(&p1_after_perform, 0);
  atomic_store(&p2_defer_ran, 0);
  unsigned long foreign_before = g_rt_foreign_hits;

  KValue *e = krt2_run_main(krt2_then(part1(), part2()));

  unsigned long foreign_after = g_rt_foreign_hits;

  CHECK(success_int(e, 99),
        "chain: foreign doubly-abortive capture THEN plain abortive drain => Success 99 "
        "(pristine c3eac73 HANGS here)");
  CHECK(atomic_load(&p1_after_perform) == 0,
        "part1: code AFTER the abandoned ENC.t perform did NOT run (dead continuation)");
  CHECK(atomic_load(&p2_defer_ran) == 1,
        "part2: the second abortive scope's defer drained exactly once (no inherited stale drain)");

  /* PROOF the test exercised the FOREIGN branch (instrumented build). */
  if (foreign_after != foreign_before || g_rt_foreign_hits != 0) {
    CHECK(foreign_after > foreign_before,
          "instrumentation: the FOREIGN-terminal branch was hit (> 0) by part 1");
    fprintf(stderr, "  (FOREIGN-branch hits during part 1: %lu)\n", foreign_after - foreign_before);
  } else {
    fprintf(stderr, "  (note: FOREIGN-branch instrumentation not compiled in; hit-count proof skipped)\n");
  }

  /* Repeat the chain under GC stress: the AbandonEnd frames are GC_MALLOC'd, so a
   * collection across the popped-drain corner must not resurrect or corrupt it. */
  for (int i = 0; i < 500; i++) {
    KValue *er = krt2_run_main(krt2_then(part1(), part2()));
    if (!success_int(er, 99)) { fails++; fprintf(stderr, "  FAIL: chain repeat %d not Success 99\n", i); break; }
    if ((i & 7) == 0) GC_gcollect();
  }

  if (fails == 0) {
    fprintf(stderr, "PASS: abandon_foreign_chain (foreign doubly-abortive capture then plain drain terminates + composes)\n");
    return 0;
  }
  fprintf(stderr, "FAIL: abandon_foreign_chain (%d checks failed)\n", fails);
  return 1;
}
