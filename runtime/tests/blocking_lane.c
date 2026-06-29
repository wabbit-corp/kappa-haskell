/* blocking_lane.c — classified blocking native actions must not monopolize a
 * scheduler worker (§18.1.5, §18.1.11, §27.6).
 *
 * With a single runtime worker, fork a blocking K_NATIVE sleep and then a fast
 * sibling that completes a promise. If the blocking K_NATIVE runs directly on
 * the scheduler worker, the promise cannot complete until the sleep returns.
 * If rt-blocking is real, the blocking fiber parks, the native call runs on an
 * off-worker thread, and the fast sibling completes promptly.
 */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

static int fails = 0;
#define CHECK(c, m) do { if (!(c)) { fprintf(stderr, "  FAIL: %s\n", m); fails++; } } while (0)

static KValue *g_promise = NULL;
static KValue *g_block_fiber = NULL;
static KValue *g_interrupted_exit = NULL;
static KValue *g_source_interrupted_exit = NULL;
static KValue *g_preentry_native_exit = NULL;
static KValue *g_preentry_source_exit = NULL;
static KValue *g_post_suspend_promise = NULL;
static KValue *g_post_suspend_started_exit = NULL;
static KValue *g_post_suspend_exit = NULL;
static _Atomic int g_block_done = 0;
static _Atomic int g_gate_started = 0;
static _Atomic int g_gate_release = 0;
static _Atomic int g_preentry_native_started = 0;
static _Atomic int g_preentry_source_started = 0;
static _Atomic int g_post_suspend_started = 0;
static _Atomic int g_post_suspend_done = 0;
static _Atomic int g_post_suspend_probe_started = 0;
static _Atomic int g_post_suspend_probe_done = 0;
static uint64_t g_start_ns = 0;
static uint64_t g_signal_elapsed_ns = 0;
static uint64_t g_interrupt_elapsed_ns = 0;
static uint64_t g_source_interrupt_elapsed_ns = 0;
static uint64_t g_preentry_native_elapsed_ns = 0;
static uint64_t g_preentry_source_elapsed_ns = 0;
static uint64_t g_post_suspend_parent_elapsed_ns = 0;

static uint64_t now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ((uint64_t)ts.tv_sec * 1000000000ull) + (uint64_t)ts.tv_nsec;
}

static KValue *blocking_sleep_fn(KValue **args) {
  (void)args;
  usleep(600 * 1000);
  atomic_store(&g_block_done, 1);
  return kunit();
}

static KValue *blocking_action(void) {
  return knative_sat_blocking(blocking_sleep_fn, 0, NULL, /*is_io=*/1);
}

static KValue *fast_action(void) {
  return krt2_complete_promise(g_promise, krt2_success(kint(1)));
}

static KValue *after_block_exit(KEnv *e, KValue *exitv) {
  (void)e;
  (void)exitv;
  return krt2_pure(kunit());
}

static KValue *after_signal(KEnv *e, KValue *exitv) {
  (void)e;
  (void)exitv;
  g_signal_elapsed_ns = now_ns() - g_start_ns;
  return krt2_bind(krt2_await(g_block_fiber), kclo(after_block_exit, NULL));
}

static KValue *after_fork_fast(KEnv *e, KValue *fiber) {
  (void)e;
  (void)fiber;
  return krt2_bind(krt2_await_promise_exit(g_promise), kclo(after_signal, NULL));
}

static KValue *after_fork_blocking(KEnv *e, KValue *fiber) {
  (void)e;
  g_block_fiber = fiber;
  return krt2_bind(krt2_fork(fast_action()), kclo(after_fork_fast, NULL));
}

static KValue *after_new_promise(KEnv *e, KValue *promise) {
  (void)e;
  g_promise = promise;
  g_start_ns = now_ns();
  return krt2_bind(krt2_fork(blocking_action()), kclo(after_fork_blocking, NULL));
}

static KValue *program(void) {
  return krt2_bind(krt2_new_promise(), kclo(after_new_promise, NULL));
}

static KValue *after_interrupted_await(KEnv *e, KValue *exitv) {
  (void)e;
  g_interrupted_exit = exitv;
  g_interrupt_elapsed_ns = now_ns() - g_start_ns;
  return krt2_pure(kunit());
}

static KValue *after_fork_interrupt_case(KEnv *e, KValue *fiber) {
  (void)e;
  return krt2_then(krt2_sleep_for(kint(10 * 1000000LL)),
                   krt2_then(krt2_interrupt_fork(fiber),
                             krt2_bind(krt2_await(fiber), kclo(after_interrupted_await, NULL))));
}

static KValue *interrupt_program(void) {
  return krt2_bind(krt2_fork(blocking_action()), kclo(after_fork_interrupt_case, NULL));
}

static KValue *gate_fn(KValue **args) {
  (void)args;
  atomic_store(&g_gate_started, 1);
  while (!atomic_load(&g_gate_release)) {
    usleep(1000);
  }
  return kunit();
}

static KValue *wait_gate_started_fn(KValue **args) {
  (void)args;
  while (!atomic_load(&g_gate_started)) {
    usleep(1000);
  }
  return kunit();
}

static KValue *release_gate_fn(KValue **args) {
  (void)args;
  atomic_store(&g_gate_release, 1);
  return kunit();
}

static KValue *source_blocking_body(void) {
  return krt2_blocking(
      krt2_then(knative_sat(gate_fn, 0, NULL, /*is_io=*/1),
                krt2_sleep_for(kint(600 * 1000000LL))));
}

static KValue *after_source_interrupted_await(KEnv *e, KValue *exitv) {
  (void)e;
  g_source_interrupted_exit = exitv;
  g_source_interrupt_elapsed_ns = now_ns() - g_start_ns;
  return krt2_pure(kunit());
}

static KValue *after_source_gate_started(KEnv *e, KValue *ignored) {
  KValue *fiber = kvar(e, 0);
  (void)ignored;
  g_start_ns = now_ns();
  return krt2_then(krt2_interrupt_fork(fiber),
                   krt2_then(knative_sat(release_gate_fn, 0, NULL, /*is_io=*/1),
                             krt2_bind(krt2_await(fiber), kclo(after_source_interrupted_await, NULL))));
}

static KValue *after_fork_source_interrupt_case(KEnv *e, KValue *fiber) {
  (void)e;
  KEnv *env = kpush(fiber, NULL);
  return krt2_then(krt2_cede(),
                   krt2_bind(knative_sat(wait_gate_started_fn, 0, NULL, /*is_io=*/1),
                             kclo(after_source_gate_started, env)));
}

static KValue *source_interrupt_program(void) {
  return krt2_bind(krt2_fork(source_blocking_body()), kclo(after_fork_source_interrupt_case, NULL));
}

static KValue *preentry_native_fn(KValue **args) {
  (void)args;
  atomic_store(&g_preentry_native_started, 1);
  usleep(200 * 1000);
  return kunit();
}

static KValue *preentry_native_action(void) {
  return knative_sat_blocking(preentry_native_fn, 0, NULL, /*is_io=*/1);
}

static KValue *after_preentry_native_await(KEnv *e, KValue *exitv) {
  (void)e;
  g_preentry_native_exit = exitv;
  g_preentry_native_elapsed_ns = now_ns() - g_start_ns;
  return krt2_pure(kunit());
}

static KValue *after_fork_preentry_native(KEnv *e, KValue *fiber) {
  (void)e;
  g_start_ns = now_ns();
  return krt2_then(krt2_interrupt_fork(fiber),
                   krt2_bind(krt2_await(fiber), kclo(after_preentry_native_await, NULL)));
}

static KValue *preentry_native_program(void) {
  return krt2_bind(krt2_fork(preentry_native_action()), kclo(after_fork_preentry_native, NULL));
}

static KValue *preentry_source_fn(KValue **args) {
  (void)args;
  atomic_store(&g_preentry_source_started, 1);
  usleep(200 * 1000);
  return kunit();
}

static KValue *preentry_source_action(void) {
  return krt2_blocking(knative_sat(preentry_source_fn, 0, NULL, /*is_io=*/1));
}

static KValue *after_preentry_source_await(KEnv *e, KValue *exitv) {
  (void)e;
  g_preentry_source_exit = exitv;
  g_preentry_source_elapsed_ns = now_ns() - g_start_ns;
  return krt2_pure(kunit());
}

static KValue *after_fork_preentry_source(KEnv *e, KValue *fiber) {
  (void)e;
  g_start_ns = now_ns();
  return krt2_then(krt2_interrupt_fork(fiber),
                   krt2_bind(krt2_await(fiber), kclo(after_preentry_source_await, NULL)));
}

static KValue *preentry_source_program(void) {
  return krt2_bind(krt2_fork(preentry_source_action()), kclo(after_fork_preentry_source, NULL));
}

static KValue *post_suspend_block_fn(KValue **args) {
  (void)args;
  atomic_store(&g_post_suspend_started, 1);
  usleep(600 * 1000);
  atomic_store(&g_post_suspend_done, 1);
  return kunit();
}

static KValue *post_suspend_body(void) {
  return krt2_blocking(
      krt2_then(krt2_sleep_for(kint(30 * 1000000LL)),
                krt2_then(krt2_complete_promise(g_post_suspend_promise,
                                                krt2_success(kunit())),
                          knative_sat(post_suspend_block_fn, 0, NULL, /*is_io=*/1))));
}

static KValue *after_post_suspend_await(KEnv *e, KValue *exitv) {
  (void)e;
  g_post_suspend_exit = exitv;
  return krt2_pure(kunit());
}

static KValue *after_post_suspend_parent_sleep(KEnv *e, KValue *ignored) {
  KValue *fiber = kvar(e, 0);
  (void)ignored;
  g_post_suspend_parent_elapsed_ns = now_ns() - g_start_ns;
  atomic_store(&g_post_suspend_probe_started, atomic_load(&g_post_suspend_started));
  atomic_store(&g_post_suspend_probe_done, atomic_load(&g_post_suspend_done));
  return krt2_bind(krt2_await(fiber), kclo(after_post_suspend_await, NULL));
}

static KValue *after_post_suspend_started(KEnv *e, KValue *exitv) {
  KValue *fiber = kvar(e, 0);
  g_post_suspend_started_exit = exitv;
  return krt2_bind(krt2_sleep_for(kint(50 * 1000000LL)),
                   kclo(after_post_suspend_parent_sleep, kpush(fiber, NULL)));
}

static KValue *after_fork_post_suspend(KEnv *e, KValue *fiber) {
  (void)e;
  KEnv *env = kpush(fiber, NULL);
  return krt2_bind(krt2_await_promise_exit(g_post_suspend_promise),
                   kclo(after_post_suspend_started, env));
}

static KValue *after_new_post_suspend_promise(KEnv *e, KValue *promise) {
  (void)e;
  g_post_suspend_promise = promise;
  g_start_ns = now_ns();
  return krt2_bind(krt2_fork(post_suspend_body()), kclo(after_fork_post_suspend, NULL));
}

static KValue *post_suspend_program(void) {
  return krt2_bind(krt2_new_promise(), kclo(after_new_post_suspend_promise, NULL));
}

int main(void) {
  setenv("KAPPA_RT_WORKERS", "1", 1);
  krt2_new(1);

  KValue *exitv = krt2_run_main(program());
  CHECK(krt2_exit_is_success(exitv), "run_main succeeded");
  CHECK(atomic_load(&g_block_done) == 1, "blocking native action completed before shutdown");

  uint64_t elapsed_ms = g_signal_elapsed_ns / 1000000ull;
  fprintf(stderr, "  promise completed after %llums while blocking sleep was 600ms\n",
          (unsigned long long)elapsed_ms);
  CHECK(elapsed_ms < 300, "blocking native action did not monopolize the only scheduler worker");

  atomic_store(&g_block_done, 0);
  g_interrupted_exit = NULL;
  g_interrupt_elapsed_ns = 0;
  g_start_ns = now_ns();
  KValue *exitv2 = krt2_run_main(interrupt_program());
  CHECK(krt2_exit_is_success(exitv2), "interrupt run_main succeeded");
  CHECK(g_interrupted_exit && kctor_is(g_interrupted_exit, "Failure"),
        "interrupted blocking fiber exits with Failure");
  CHECK(atomic_load(&g_block_done) == 1,
        "blocking worker completed before the interrupted fiber terminated");
  uint64_t interrupt_elapsed_ms = g_interrupt_elapsed_ns / 1000000ull;
  fprintf(stderr, "  interrupted blocking fiber completed after %llums\n",
          (unsigned long long)interrupt_elapsed_ms);
  CHECK(interrupt_elapsed_ms >= 500,
        "interrupt does not detach a non-cancellable blocking call from its fiber");

  g_source_interrupted_exit = NULL;
  atomic_store(&g_gate_started, 0);
  atomic_store(&g_gate_release, 0);
  g_source_interrupt_elapsed_ns = 0;
  g_start_ns = now_ns();
  KValue *exitv3 = krt2_run_main(source_interrupt_program());
  CHECK(krt2_exit_is_success(exitv3), "source blocking interrupt run_main succeeded");
  CHECK(g_source_interrupted_exit && kctor_is(g_source_interrupted_exit, "Failure"),
        "interrupted source blocking fiber exits with Failure");
  uint64_t source_interrupt_elapsed_ms = g_source_interrupt_elapsed_ns / 1000000ull;
  fprintf(stderr, "  interrupted source blocking sleep completed after %llums\n",
          (unsigned long long)source_interrupt_elapsed_ms);
  CHECK(source_interrupt_elapsed_ms < 300,
        "source-level blocking preserves pending interruption before first suspension");

  g_preentry_native_exit = NULL;
  atomic_store(&g_preentry_native_started, 0);
  g_preentry_native_elapsed_ns = 0;
  KValue *exitv4 = krt2_run_main(preentry_native_program());
  CHECK(krt2_exit_is_success(exitv4), "pre-entry native interrupt run_main succeeded");
  CHECK(g_preentry_native_exit && kctor_is(g_preentry_native_exit, "Failure"),
        "pre-entry interrupted native blocking fiber exits with Failure");
  CHECK(atomic_load(&g_preentry_native_started) == 0,
        "pending interrupt prevents classified blocking native body from starting");
  uint64_t preentry_native_elapsed_ms = g_preentry_native_elapsed_ns / 1000000ull;
  fprintf(stderr, "  pre-entry native blocking interrupt completed after %llums\n",
          (unsigned long long)preentry_native_elapsed_ms);

  g_preentry_source_exit = NULL;
  atomic_store(&g_preentry_source_started, 0);
  g_preentry_source_elapsed_ns = 0;
  KValue *exitv5 = krt2_run_main(preentry_source_program());
  CHECK(krt2_exit_is_success(exitv5), "pre-entry source blocking interrupt run_main succeeded");
  CHECK(g_preentry_source_exit && kctor_is(g_preentry_source_exit, "Failure"),
        "pre-entry interrupted source blocking fiber exits with Failure");
  CHECK(atomic_load(&g_preentry_source_started) == 0,
        "pending interrupt prevents source-level blocking body from starting");
  uint64_t preentry_source_elapsed_ms = g_preentry_source_elapsed_ns / 1000000ull;
  fprintf(stderr, "  pre-entry source blocking interrupt completed after %llums\n",
          (unsigned long long)preentry_source_elapsed_ms);

  g_post_suspend_exit = NULL;
  g_post_suspend_started_exit = NULL;
  g_post_suspend_promise = NULL;
  atomic_store(&g_post_suspend_started, 0);
  atomic_store(&g_post_suspend_done, 0);
  atomic_store(&g_post_suspend_probe_started, 0);
  atomic_store(&g_post_suspend_probe_done, 0);
  g_post_suspend_parent_elapsed_ns = 0;
  KValue *exitv6 = krt2_run_main(post_suspend_program());
  CHECK(krt2_exit_is_success(exitv6), "post-suspension source blocking run_main succeeded");
  CHECK(g_post_suspend_started_exit && kctor_is(g_post_suspend_started_exit, "Success"),
        "post-suspension source blocking child signalled native-work entry");
  CHECK(g_post_suspend_exit && kctor_is(g_post_suspend_exit, "Success"),
        "post-suspension source blocking child exits successfully");
  CHECK(atomic_load(&g_post_suspend_started) == 1,
        "post-suspension source blocking body reached synchronous native work");
  CHECK(atomic_load(&g_post_suspend_done) == 1,
        "post-suspension source blocking body completed synchronous native work");
  uint64_t post_suspend_parent_elapsed_ms = g_post_suspend_parent_elapsed_ns / 1000000ull;
  fprintf(stderr, "  parent observed post-suspend blocking body after %llums while it slept 600ms\n",
          (unsigned long long)post_suspend_parent_elapsed_ms);
  CHECK(post_suspend_parent_elapsed_ms < 300,
        "source-level blocking remains on the blocking lane after suspension");
  CHECK(atomic_load(&g_post_suspend_probe_started) == 1,
        "parent ran after post-suspension native work had started");
  CHECK(atomic_load(&g_post_suspend_probe_done) == 0,
        "parent ran before post-suspension native work completed");

  if (fails) {
    fprintf(stderr, "FAIL: blocking_lane (%d)\n", fails);
    return 1;
  }
  fprintf(stderr, "OK: blocking_lane\n");
  return 0;
}
