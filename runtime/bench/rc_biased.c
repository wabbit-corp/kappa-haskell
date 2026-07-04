#include "kappart2.h"

#include <stdint.h>
#include <stdio.h>
#include <time.h>

static volatile uintptr_t rc_sink;

static double now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}

static double run_pair_loop(KValue *v, int iters) {
  double t0 = now_ns();
  for (int i = 0; i < iters; i++) {
    KValue *w = kdup(v);
    __asm__ __volatile__("" : : "r"(w) : "memory");
    kdrop(w);
  }
  double t1 = now_ns();
  rc_sink ^= (uintptr_t)krc_count(v);
  return (t1 - t0) / (double)iters;
}

static double best_pair_loop(KValue *v, int iters, int repeats) {
  double best = 1.0e100;
  for (int i = 0; i < repeats; i++) {
    double ns = run_pair_loop(v, iters);
    if (ns < best) best = ns;
  }
  return best;
}

static double run_ref_read_loop(KValue *r, int iters) {
  double t0 = now_ns();
  for (int i = 0; i < iters; i++) {
    KValue *w = kref_get(r);
    __asm__ __volatile__("" : : "r"(w) : "memory");
    kdrop(w);
  }
  double t1 = now_ns();
  rc_sink ^= (uintptr_t)krc_count(r);
  return (t1 - t0) / (double)iters;
}

static double best_ref_read_loop(KValue *r, int iters, int repeats) {
  double best = 1.0e100;
  for (int i = 0; i < repeats; i++) {
    double ns = run_ref_read_loop(r, iters);
    if (ns < best) best = ns;
  }
  return best;
}

static double run_arr_read_loop(KValue *a, int iters) {
  double t0 = now_ns();
  for (int i = 0; i < iters; i++) {
    KValue *w = karr_get(a, 0);
    __asm__ __volatile__("" : : "r"(w) : "memory");
    kdrop(w);
  }
  double t1 = now_ns();
  rc_sink ^= (uintptr_t)krc_count(a);
  return (t1 - t0) / (double)iters;
}

static double best_arr_read_loop(KValue *a, int iters, int repeats) {
  double best = 1.0e100;
  for (int i = 0; i < repeats; i++) {
    double ns = run_arr_read_loop(a, iters);
    if (ns < best) best = ns;
  }
  return best;
}

int main(void) {
  krt_init();
  const int iters = 5000000;
  const int repeats = 7;

  KValue *local = kref_new(kunit());
  KValue *shared = kref_new(kunit());
  krc_mark_shared_recursive(shared);
  KValue *local_payload = kstr0("local");
  KValue *shared_payload = kstr0("shared");
  KValue *local_ref = kref_new(local_payload);
  KValue *shared_ref = kref_new(shared_payload);
  krc_mark_shared_recursive(shared_ref);
  KValue *local_arr_payload = kstr0("local-array");
  KValue *shared_arr_payload = kstr0("shared-array");
  KValue *local_arr = karr_new(1, local_arr_payload);
  KValue *shared_arr = karr_new(1, shared_arr_payload);
  krc_mark_shared_recursive(shared_arr);

  (void)run_pair_loop(local, 10000);
  (void)run_pair_loop(shared, 10000);
  (void)run_ref_read_loop(local_ref, 10000);
  (void)run_ref_read_loop(shared_ref, 10000);
  (void)run_arr_read_loop(local_arr, 10000);
  (void)run_arr_read_loop(shared_arr, 10000);

  double local_ns = best_pair_loop(local, iters, repeats);
  double shared_ns = best_pair_loop(shared, iters, repeats);
  printf("S4 biased RC local %.3f ns/op, shared %.3f ns/op, ratio %.3f\n",
         local_ns, shared_ns, local_ns / shared_ns);
  double local_ref_ns = best_ref_read_loop(local_ref, iters, repeats);
  double shared_ref_ns = best_ref_read_loop(shared_ref, iters, repeats);
  printf("S4 ref read local %.3f ns/op, shared %.3f ns/op, ratio %.3f\n",
         local_ref_ns, shared_ref_ns, local_ref_ns / shared_ref_ns);
  double local_arr_ns = best_arr_read_loop(local_arr, iters, repeats);
  double shared_arr_ns = best_arr_read_loop(shared_arr, iters, repeats);
  printf("S4 array read local %.3f ns/op, shared %.3f ns/op, ratio %.3f\n",
         local_arr_ns, shared_arr_ns, local_arr_ns / shared_arr_ns);

  if (krc_count(local) != 1 || krc_count(shared) != 1 ||
      krc_count(local_payload) != 1 || krc_count(shared_payload) != 1 ||
      krc_count(local_arr_payload) != 1 || krc_count(shared_arr_payload) != 1) {
    fprintf(stderr, "FAIL: RC pair loop did not preserve owner counts\n");
    return 1;
  }
  if (!(local_ns < shared_ns * 0.85)) {
    fprintf(stderr, "FAIL: S4 biased RC fast path did not beat shared atomic slow path\n");
    return 1;
  }
  if (!(local_ns < 20.0)) {
    fprintf(stderr, "FAIL: S4 biased RC fast path exceeded the loose absolute budget\n");
    return 1;
  }
  if (!(local_ref_ns < local_ns * 2.25)) {
    fprintf(stderr, "FAIL: S4 private ref read is too far from the local RC baseline\n");
    return 1;
  }
  if (!(local_ref_ns < 25.0)) {
    fprintf(stderr, "FAIL: S4 private ref read exceeded the loose absolute budget\n");
    return 1;
  }
  if (!(local_ref_ns < shared_ref_ns * 0.85)) {
    fprintf(stderr, "FAIL: S4 private ref read did not beat shared locked read\n");
    return 1;
  }
  if (!(local_arr_ns < local_ns * 2.25)) {
    fprintf(stderr, "FAIL: S4 private array read is too far from the local RC baseline\n");
    return 1;
  }
  if (!(local_arr_ns < 25.0)) {
    fprintf(stderr, "FAIL: S4 private array read exceeded the loose absolute budget\n");
    return 1;
  }
  if (!(local_arr_ns < shared_arr_ns * 0.85)) {
    fprintf(stderr, "FAIL: S4 private array read did not beat shared locked read\n");
    return 1;
  }
  return rc_sink == 0xdeadbeef ? 1 : 0;
}
