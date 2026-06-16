/* kappart_ffi_stub.c — the no-FFI runtime unit.
 *
 * Links into native executables that use no foreign (libuv/sqlite)
 * primitives.  It knows no FFI primitives; the code generator never emits
 * an FFI primitive against this unit because the build's supported-prim
 * set excludes them.  The demo build links kappart_ffi.c (libuv+sqlite)
 * in place of this file.  See docs/NATIVE_BACKEND.md §6. */
#include "kappart.h"

int prim_is_io_ffi(const char *p) {
  (void)p;
  return 0;
}

int prim_arity_ffi(const char *p) {
  (void)p;
  krt_fail("internal: unknown primitive (no FFI runtime linked)");
}

KValue *krun_io_ffi(KValue *action) {
  (void)action;
  krt_fail("internal: FFI IO primitive with no FFI runtime linked");
}
