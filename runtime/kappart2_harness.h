/* kappart2_harness.h — helpers for hand-writing test programs as KValue action
 * trees (DESIGN.md §1, REVIEW.md m3).  These let a C harness express
 * fork/await/promise/sleep programs of the exact shape the v2 codegen will emit,
 * so the runtime is testable before backend integration.
 *
 * A continuation `(a -> IO b)` is a kappart closure: a `KFn` (KValue*(KEnv*,
 * KValue*)) that, given the bound value, RETURNS the next action node.  Build
 * one with `kclo(fn, env)` (from kappart.h) and capture free variables in the
 * `KEnv` via `kpush`.  Simple continuations that use only their argument pass
 * `env = NULL`. */
#ifndef KAPPART2_HARNESS_H
#define KAPPART2_HARNESS_H

#include "kappart2.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Console action builders from raw C strings (the public ABI takes boxed
 * KValue strings; these wrap kstr0 for harness convenience). */
KValue *krt2_print_c(const char *s);    /* printString  (no newline) */
KValue *krt2_println_c(const char *s);  /* printlnString             */

#ifdef __cplusplus
}
#endif
#endif /* KAPPART2_HARNESS_H */
