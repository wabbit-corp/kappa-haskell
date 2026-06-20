/* delve_terminal_adapter.c — conservative-ABI adapter over delve_terminal.c.
 *
 * Presents the flat conservative surface declared in delve_terminal_adapter.h
 * (handle by value, errnos as int, size as two int accessors, seed as
 * uint64_t, error text as a C string) by delegating to the out-parameter POSIX
 * shim in delve_terminal.c. No state beyond a single recorded errno; the
 * handle itself is owned by the shim and threaded back through the void*.
 */
#include "delve_terminal_adapter.h"
#include "delve_terminal.h"

#include <string.h>

/* errno of the most recent failing adapter call (chiefly for the open path,
 * whose failure is signalled by a NULL return that cannot also carry errno). */
static int g_last_errno = 0;

void *delve_open_terminal2(void) {
    delve_terminal_handle *h = 0;
    int rc = delve_open_terminal(&h);
    if (rc != 0) {
        g_last_errno = rc;
        return 0;
    }
    g_last_errno = 0;
    return (void *)h;
}

int delve_last_errno2(void) {
    return g_last_errno;
}

int delve_close_terminal2(void *handle) {
    if (!handle) return 0;
    int rc = delve_close_terminal((delve_terminal_handle *)handle);
    if (rc != 0) g_last_errno = rc;
    return rc;
}

int delve_read_key2(void *handle) {
    if (!handle) return -1; /* -EPERM-ish: no handle */
    int code = 0;
    int rc = delve_read_key((delve_terminal_handle *)handle, &code);
    if (rc != 0) {
        g_last_errno = rc;
        return rc > 0 ? -rc : -1;
    }
    if (code < 0) code = 0;
    return code;
}

int delve_write_all2(void *handle, const char *text, int len) {
    if (!handle) return -1;
    int rc = delve_write_all((delve_terminal_handle *)handle, text, len);
    if (rc != 0) g_last_errno = rc;
    return rc;
}

int delve_get_cols2(void *handle) {
    if (!handle) return -1;
    delve_size sz;
    int rc = delve_get_size((delve_terminal_handle *)handle, &sz);
    if (rc != 0) {
        g_last_errno = rc;
        return rc > 0 ? -rc : -1;
    }
    return sz.cols;
}

int delve_get_rows2(void *handle) {
    if (!handle) return -1;
    delve_size sz;
    int rc = delve_get_size((delve_terminal_handle *)handle, &sz);
    if (rc != 0) {
        g_last_errno = rc;
        return rc > 0 ? -rc : -1;
    }
    return sz.rows;
}

uint64_t delve_monotonic_seed2(void) {
    return delve_monotonic_seed();
}

const char *delve_describe_error2(int code) {
    int e = code < 0 ? -code : code;
    return delve_strerror(e);
}
