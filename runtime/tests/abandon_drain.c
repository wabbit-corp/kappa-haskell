/* abandon_drain.c — §32.2.20/.21 handler-abandonment cleanup (RUNTIME-SPEC-
 * COVERAGE finding #1).  When a general-path handler clause completes WITHOUT
 * resuming its captured one-shot resumption (an abortive clause), the severed
 * op-site->handler slice — and every `defer`/`using` registered in its do-scopes
 * — must still run its exit actions masked-LIFO before the clause result
 * proceeds.  Before the fix the slice was dropped GC'd-unrun, so its defers never
 * fired (a resource leak); these checks would FAIL.  After the fix they PASS.
 *
 * The defers here have an OBSERVABLE side effect (they write a C-visible atomic),
 * so the test is genuinely observable — unlike a pure-Eff defer under runPure,
 * whose body the interpreter reduces to Unit (the bug was untestable-by-
 * construction at the .kp/oracle level; see the spec-coverage doc).
 *
 * Scenarios:
 *   A. ABORTIVE clause (ignores k): the body's `defer` is inside the captured
 *      slice and MUST run on abandonment.  Two stacked defers also prove LIFO.
 *   B. RESUMING clause (calls k): the SAME body must run its defer exactly once
 *      (on the resumed body's normal exit), and the post-perform code runs — the
 *      drain machinery must not double-run or skip it on the resume path.
 *   C. ABORTIVE clause where the abandoned slice's defer ITSELF fails-then-
 *      -recovers via an inner catch (defer body is real Eff that runs on the
 *      scheduler), proving the drain goes through the CK-machine, not a host
 *      finalizer.
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <gc.h>
#include <stdio.h>
#include <stdatomic.h>

static int fails = 0;
#define CHECK(c, m) do { if (!(c)) { fprintf(stderr, "  FAIL: %s\n", m); fails++; } } while (0)

/* ── A: abortive clause — abandoned slice's defers must drain (LIFO) ─────── */

static _Atomic int a_d1 = 0, a_d2 = 0;     /* set by the two body defers       */
static _Atomic long a_order = 0;           /* records LIFO order (d2 then d1)   */
static _Atomic long a_tick = 0;            /* global "Nth side effect" counter  */

static KValue *a_set_d1(KEnv *e) { (void)e; atomic_store(&a_d1, 1);
  atomic_store(&a_order, atomic_fetch_add(&a_tick, 1)); return kunit(); }
static KValue *a_set_d2(KEnv *e) { (void)e; atomic_store(&a_d2, 1);
  (void)atomic_fetch_add(&a_tick, 1); return kunit(); }

/* the abortive op clause: \payload -> \k -> pure 99  (k is IGNORED => abandon) */
static KValue *a_clause_k(KEnv *e, KValue *k) { (void)e; (void)k; return krt2_pure(kint(99)); }
static KValue *a_clause(KEnv *e, KValue *payload) { (void)e; (void)payload; return kclo(a_clause_k, NULL); }

/* the return clause: \x -> pure x */
static KValue *a_ret(KEnv *e, KValue *x) { (void)e; return krt2_pure(x); }

/* body: doscope { defer d1; defer d2; _ <- perform E.abort (); pure 0 }
 * d2 is registered LAST => runs FIRST (LIFO).  The perform's captured slice runs
 * from the op-site up to the handler and INCLUDES this doscope, so its defers are
 * exactly what abandonment must drain. */
static KValue *a_body(void) {
  KValue *after = krt2_then(krt2_perform(kstr0("E"), kstr0("abort"), kunit()),
                            krt2_pure(kint(0)));
  return krt2_doscope(
      krt2_then(krt2_defer(kio(a_set_d1, NULL)),
      krt2_then(krt2_defer(kio(a_set_d2, NULL)),
                after)));
}

static KValue *scenarioA(void) {
  const char *names[1] = { "abort" };
  KValue *vals[1]      = { kclo(a_clause, NULL) };
  KValue *ops = krec(1, names, vals);
  /* deep handler (deep=True); abortive => the tail-resumptive fast path is NOT
   * taken (the clause is not marked __tailResumptive), so this is the general
   * sever path the drain guards. */
  return krt2_handle(kbool(1), kstr0("E"), kclo(a_ret, NULL), ops, a_body());
}

/* ── B: resuming clause — defer runs once, post-perform code runs ────────── */

static _Atomic int b_defer = 0, b_after = 0;
static KValue *b_set_defer(KEnv *e) { (void)e; atomic_fetch_add(&b_defer, 1); return kunit(); }
static KValue *b_set_after(KEnv *e) { (void)e; atomic_store(&b_after, 1); return kunit(); }

/* clause: \payload -> \k -> resume k 7   (resumes the captured continuation).
 * `resume k v` is surface-elaborated to the APPLICATION `k v` (k is the
 * resumption wrapped as a 1-arg function; applying it builds the OP_RESUME) —
 * NOT a direct krt2_resume(k,..), which would pass the closure itself as the box. */
static KValue *b_clause_k(KEnv *e, KValue *k) { (void)e; return kapp(k, kint(7)); }
static KValue *b_clause(KEnv *e, KValue *payload) { (void)e; (void)payload; return kclo(b_clause_k, NULL); }
static KValue *b_ret(KEnv *e, KValue *x) { (void)e; return krt2_pure(x); }

/* body: doscope { defer; v <- perform E.go (); after-marker; pure v }
 * resume delivers 7 as `v`; the body then runs the after-marker and its defer
 * on normal exit — each exactly once. */
static KValue *b_tail(KEnv *e, KValue *v) { (void)e;
  return krt2_then(kio(b_set_after, NULL), krt2_pure(v)); }
static KValue *b_body(void) {
  KValue *seq = krt2_bind(krt2_perform(kstr0("E"), kstr0("go"), kunit()), kclo(b_tail, NULL));
  return krt2_doscope(krt2_then(krt2_defer(kio(b_set_defer, NULL)), seq));
}
static KValue *scenarioB(void) {
  const char *names[1] = { "go" };
  KValue *vals[1]      = { kclo(b_clause, NULL) };
  KValue *ops = krec(1, names, vals);
  return krt2_handle(kbool(1), kstr0("E"), kclo(b_ret, NULL), ops, b_body());
}

/* ── C: abandoned slice's defer is real Eff (fails + recovers on the CK-machine) */

static _Atomic int c_ran = 0;
static KValue *c_recover(KEnv *e, KValue *err) { (void)e; (void)err;
  atomic_store(&c_ran, 1); return krt2_pure(kunit()); }
/* defer body: catch (throw "x") (\_ -> mark)  — runs through unwind/deliver, not
 * a host finalizer, so a step-suspending defer body is honored. */
static KValue *c_defer_body(void) {
  return krt2_catch(krt2_throw(kstr0("inner")), kclo(c_recover, NULL));
}
static KValue *c_clause_k(KEnv *e, KValue *k) { (void)e; (void)k; return krt2_pure(kunit()); }
static KValue *c_clause(KEnv *e, KValue *payload) { (void)e; (void)payload; return kclo(c_clause_k, NULL); }
static KValue *c_ret(KEnv *e, KValue *x) { (void)e; return krt2_pure(x); }
static KValue *c_body(void) {
  KValue *after = krt2_then(krt2_perform(kstr0("E"), kstr0("abort"), kunit()), krt2_pure(kunit()));
  return krt2_doscope(krt2_then(krt2_defer(c_defer_body()), after));
}
static KValue *scenarioC(void) {
  const char *names[1] = { "abort" };
  KValue *vals[1]      = { kclo(c_clause, NULL) };
  KValue *ops = krec(1, names, vals);
  return krt2_handle(kbool(0), kstr0("E"), kclo(c_ret, NULL), ops, c_body()); /* shallow */
}

/* ── D: GC stress — abandon the same shape repeatedly under forced collection ── */
static _Atomic long d_count = 0;
static KValue *d_inc(KEnv *e) { (void)e; atomic_fetch_add(&d_count, 1); return kunit(); }
static KValue *scenarioD(void) {  /* abortive deep handler; body defers d_inc */
  const char *names[1] = { "abort" };
  KValue *vals[1]      = { kclo(a_clause, NULL) };   /* reuse the abortive clause */
  KValue *after = krt2_then(krt2_perform(kstr0("E"), kstr0("abort"), kunit()), krt2_pure(kint(0)));
  KValue *body  = krt2_doscope(krt2_then(krt2_defer(kio(d_inc, NULL)), after));
  return krt2_handle(kbool(1), kstr0("E"), kclo(a_ret, NULL), krec(1, names, vals), body);
}

int main(void) {
  krt2_new(1);  /* single worker: the programs are sequential on the main fiber */

  /* A — abandoned defers must drain LIFO */
  KValue *ea = krt2_run_main(scenarioA());
  CHECK(kctor_is(ea, "Success"), "A: handle Exit == Success");
  CHECK(kctor_argc(ea) == 1 && kas_int(kctor_arg(ea, 0)) == 99, "A: abortive clause result == 99");
  CHECK(atomic_load(&a_d1) == 1, "A: abandoned slice's defer d1 RAN (no leak)");
  CHECK(atomic_load(&a_d2) == 1, "A: abandoned slice's defer d2 RAN (no leak)");
  /* d2 registered last => runs first: its tick precedes d1's (a_order==1). */
  CHECK(atomic_load(&a_order) == 1, "A: defers ran LIFO (d2 before d1)");

  /* B — resume path: defer once, after-code runs, no double-drain */
  KValue *eb = krt2_run_main(scenarioB());
  CHECK(kctor_is(eb, "Success"), "B: handle Exit == Success");
  CHECK(kctor_argc(eb) == 1 && kas_int(kctor_arg(eb, 0)) == 7, "B: resumed value == 7");
  CHECK(atomic_load(&b_defer) == 1, "B: defer ran EXACTLY once on resume (no double-drain)");
  CHECK(atomic_load(&b_after) == 1, "B: post-perform code ran on resume");

  /* C — drain goes through the CK-machine (defer body fails+recovers) */
  KValue *ec = krt2_run_main(scenarioC());
  CHECK(kctor_is(ec, "Success"), "C: handle Exit == Success");
  CHECK(atomic_load(&c_ran) == 1, "C: abandoned defer body ran on the CK-machine (catch recovered)");

  /* D — GC stress: abandon the SAME shape 2000x under forced collection (the
   * severed slice + its KK_ABANDEND terminal + its defers are all GC_MALLOC'd, so
   * a collection mid-drain must not reclaim a live frame).  d_count counts how
   * many times the abandoned defer ran; it must equal the run count exactly. */
  for (int i = 0; i < 2000; i++) {
    KValue *ed = krt2_run_main(scenarioD());
    if (!kctor_is(ed, "Success")) { fails++; fprintf(stderr, "  FAIL: D run %d not Success\n", i); break; }
    if ((i & 0xf) == 0) GC_gcollect();   /* force a collection across the drain */
  }
  CHECK(atomic_load(&d_count) == 2000, "D: every abandoned defer ran under GC stress (2000/2000)");

  if (fails == 0) {
    fprintf(stderr, "PASS: abandon_drain (abandoned handler slice drains defers masked-LIFO; resume path intact)\n");
    return 0;
  }
  fprintf(stderr, "FAIL: abandon_drain (%d checks failed)\n", fails);
  return 1;
}
