/* race.c — race and timeout (§18.1.6), composed from the already-tested
 * primitives (fork / forkDaemon / await / interrupt / promise / sleep / tryExit)
 * exactly as the reference Interp.hs does, rather than as bespoke scheduler ops.
 * This reuses the verified park/wake + interruption machinery and gets the
 * mandated tie-break for free: `race` checks the LEFT fiber first, so a true
 * simultaneous tie resolves to left (§32.2.8); `timeout` checks the action first,
 * so completion beats timer expiry on a tie.
 *
 * Both are built as KValue action trees through a chain of continuation
 * closures (the de Bruijn KEnv threads the runtime values lf/rf/signal/af).
 * `interrupt` is the WAITING form, so when the winner is chosen the loser is
 * interrupted AND its finalizers run before the result is returned (§18.1.6).
 *
 * The raw results carry the winner's terminal Exit; the prelude `race`/`timeout`
 * terms unwrap them (Success -> value, Failure -> reraise, timer -> Fail Timeout).
 *   race:    RaceWonLeft Exit | RaceWonRight Exit
 *   timeout: TimeoutDone Exit | TimeoutFired
 */
#include "internal.h"

#include <gc.h>

/* result constructors (matched by name in harnesses / unwrapped by the prelude) */
static KValue *won(const char *side, KValue *exit) {
  KValue *args[1] = { exit };
  return kctor(KRT2_RESULT_ID, side, 1, args);
}
/* a daemon that signals `signal` once `child` (or `delayAction`) completes */
static KValue *signal_on(KValue *child_action_done, KValue *signal) {
  return krt2_then(child_action_done,
         krt2_then(krt2_complete_promise(signal, krt2_success(krt2i_unit())),
                   krt2_pure(krt2i_unit())));
}

/* ── race ───────────────────────────────────────────────────────────────── */

/* \mre -> if Some rex then (interrupt lf; RaceWonRight rex) else defensive  (env=[lf]) */
static KValue *race_decide_r(KEnv *env, KValue *mre) {
  KValue *lf = kvar(env, 0);
  if (kctor_is(mre, "Some"))
    return krt2_then(krt2_interrupt(lf), krt2_pure(won("RaceWonRight", kctor_arg(mre, 0))));
  return krt2_pure(won("RaceWonLeft", krt2_failure(krt2_cause_defect(kstr0("race: no winner")))));
}
/* \mle -> if Some lex then (interrupt rf; RaceWonLeft lex) else tryExit rf >>= race_decide_r
 *  (env=[lf, rf]) */
static KValue *race_decide_l(KEnv *env, KValue *mle) {
  KValue *lf = kvar(env, 0), *rf = kvar(env, 1);
  if (kctor_is(mle, "Some"))
    return krt2_then(krt2_interrupt(rf), krt2_pure(won("RaceWonLeft", kctor_arg(mle, 0))));
  return krt2_bind(krt2i_try_exit(rf), kclo(race_decide_r, kpush(lf, NULL)));
}
/* \rf -> spawn both watchers, await first signal, then decide  (env=[signal, lf]) */
static KValue *race_k_rf(KEnv *env, KValue *rf) {
  KValue *signal = kvar(env, 0), *lf = kvar(env, 1);
  /* race_decide_l reads env as [lf, rf] (kvar 0 = lf, kvar 1 = rf). */
  KValue *decide = krt2_bind(krt2i_try_exit(lf), kclo(race_decide_l, kpush(lf, kpush(rf, NULL))));
  return krt2_then(krt2_fork_daemon(signal_on(krt2_await(lf), signal)),
         krt2_then(krt2_fork_daemon(signal_on(krt2_await(rf), signal)),
         krt2_then(krt2_await_promise_exit(signal), decide)));
}
/* \lf -> fork right >>= race_k_rf  (env=[right, signal]) */
static KValue *race_k_lf(KEnv *env, KValue *lf) {
  KValue *right = kvar(env, 0), *signal = kvar(env, 1);
  return krt2_bind(krt2_fork(right), kclo(race_k_rf, kpush(signal, kpush(lf, NULL))));
}
/* \signal -> fork left >>= race_k_lf  (env=[left, right]) */
static KValue *race_k_signal(KEnv *env, KValue *signal) {
  KValue *left = kvar(env, 0), *right = kvar(env, 1);
  return krt2_bind(krt2_fork(left), kclo(race_k_lf, kpush(right, kpush(signal, NULL))));
}
KValue *krt2_race(KValue *left, KValue *right) {
  return krt2_bind(krt2_new_promise(), kclo(race_k_signal, kpush(left, kpush(right, NULL))));
}

/* ── timeout ────────────────────────────────────────────────────────────── */

/* \mae -> if Some aex then TimeoutDone aex else (interruptAs TimedOut af; TimeoutFired)
 *  (env=[af]) */
static KValue *timeout_decide(KEnv *env, KValue *mae) {
  KValue *af = kvar(env, 0);
  if (kctor_is(mae, "Some"))
    return krt2_pure(won("TimeoutDone", kctor_arg(mae, 0)));
  KValue *cause = krt2_interrupt_cause("TimedOut", krt2i_none());
  return krt2_then(krt2_interrupt_as(cause, af),
                   krt2_pure(kctor0(KRT2_RESULT_ID, "TimeoutFired")));
}
/* \af -> spawn action-watcher + timer-watcher, await first signal, then decide
 *  (env=[dur, signal]) */
static KValue *timeout_k_af(KEnv *env, KValue *af) {
  KValue *dur = kvar(env, 0), *signal = kvar(env, 1);
  KValue *decide = krt2_bind(krt2i_try_exit(af), kclo(timeout_decide, kpush(af, NULL)));
  return krt2_then(krt2_fork_daemon(signal_on(krt2_await(af), signal)),
         krt2_then(krt2_fork_daemon(signal_on(krt2_sleep_for(dur), signal)),
         krt2_then(krt2_await_promise_exit(signal), decide)));
}
/* \signal -> fork action >>= timeout_k_af  (env=[dur, action]) */
static KValue *timeout_k_signal(KEnv *env, KValue *signal) {
  KValue *dur = kvar(env, 0), *action = kvar(env, 1);
  return krt2_bind(krt2_fork(action), kclo(timeout_k_af, kpush(dur, kpush(signal, NULL))));
}
KValue *krt2_timeout(KValue *dur, KValue *action) {
  return krt2_bind(krt2_new_promise(), kclo(timeout_k_signal, kpush(dur, kpush(action, NULL))));
}
