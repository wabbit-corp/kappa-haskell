/* delve_terminal_adapter.h — conservative-ABI adapter surface for delve's
 * native Linux terminal.
 *
 * This header is the SINGLE source of truth for the host.native.delve_terminal
 * raw surface: the build plan generates it by PREPROCESSING + PARSING this
 * header (generateAllFromHeader "…/delve_terminal_adapter.h" "delve_"). There
 * is no hand-authored symbolDecl. The adapter implementation
 * (delve_terminal_adapter.c) includes this header so its definitions are
 * checked against these prototypes, and delegates to the real POSIX terminal
 * shim (delve_terminal.c).
 *
 * Why an adapter (§26.1.2 / §26.1.4): the underlying shim
 * (delve_terminal.h) uses OUT-PARAMETERS — `int delve_open_terminal(handle**)`
 * returns an errno and writes the handle through a pointer, and
 * `delve_get_size` writes a by-value `delve_size` struct through a pointer.
 * Neither maps to a DIRECT conservative C-ABI call (the generator surfaces a
 * non-char pointer as `Option RawPtr` and rejects by-value struct results).
 * These adapter functions present a flat conservative surface instead:
 *
 *   - a handle is returned by value as `void *` (NULL on failure) -> the
 *     generator surfaces it as `Option RawPtr`;
 *   - errnos are returned as plain `int` (0 = ok, >0 = errno; a negative value
 *     marks "no result, see |value| as errno") -> generated as `Integer`;
 *   - sizes are returned as two separate `int` accessors (cols / rows);
 *   - the monotonic seed is a `uint64_t` (generated as std.ffi.U64);
 *   - text payload functions return or accept NUL-terminated C strings
 *     (declared in the binding's `cstrings`, so they generate as `String`,
 *     not Option RawPtr).
 *
 * Every prototype here is conservatively representable (only int / void* /
 * const char* / uint64_t), so the broad generator binds all of them.
 */
#ifndef DELVE_TERMINAL_ADAPTER_H
#define DELVE_TERMINAL_ADAPTER_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Open the terminal in raw mode. Returns an opaque handle, or NULL on failure
 * (the failing errno is then available from delve_last_errno2). */
void *delve_open_terminal2(void);

/* The errno recorded by the most recent adapter call that failed (0 if none). */
int delve_last_errno2(void);

/* Restore the terminal and release the handle. Returns 0 on success or an
 * errno on failure. A NULL handle is a no-op returning 0. */
int delve_close_terminal2(void *handle);

/* Block for the next key. Returns the (non-negative) decoded key code on
 * success, or the negated errno (a value < 0) on failure. */
int delve_read_key2(void *handle);

/* Write exactly `len` bytes of `text`. Returns 0 on success or an errno. */
int delve_write_all2(void *handle, const char *text, int len);

/* Terminal width / height in cells. Returns the (non-negative) count, or the
 * negated errno (< 0) on failure. */
int delve_get_cols2(void *handle);
int delve_get_rows2(void *handle);

/* A monotonic, process-specific seed value. */
uint64_t delve_monotonic_seed2(void);

/* Human-readable description of an errno code (NUL-terminated C string). */
const char *delve_describe_error2(int code);

/* Read an entire UTF-8 text file. Returns the text on success. On failure it
 * returns the empty string and records errno in delve_last_errno2; callers
 * check last_errno to distinguish a real empty file from a failed read. */
const char *delve_read_text_file2(const char *path);

/* Write exactly `len` bytes of `text`. Returns 0 on success or an errno. */
int delve_write_text_file2(const char *path, const char *text, int len);

/* Return 1 if the path exists, 0 if it does not, or a negative errno on an
 * actual stat failure. */
int delve_file_exists2(const char *path);

/* Ensure a directory exists. Returns 0 on success or an errno. */
int delve_ensure_directory2(const char *path);

#ifdef __cplusplus
}
#endif

#endif /* DELVE_TERMINAL_ADAPTER_H */
