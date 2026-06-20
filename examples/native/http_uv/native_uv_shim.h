/* native_uv_shim.h — the public ABI of the libuv blocking adapter.
 *
 * This header is the SINGLE source of truth for the adapter's surface: the
 * build plan generates the Kappa `host.native.uvnet` raw surface by
 * PREPROCESSING + PARSING this header (generateFromHeader), and the adapter
 * implementation (native_uv_shim.c) includes it so its definitions are checked
 * against these prototypes. There is no hand-authored symbolDecl for these
 * functions anywhere in the build manifest.
 *
 * The adapter is the justified event-loop companion (§26.1.9): libuv's API is
 * callback/async, which a conservative C-ABI host binding cannot drive
 * directly from Kappa (no function-pointer marshalling), so these six
 * functions present a small BLOCKING interface over the async raw libuv
 * surface. Handles cross the boundary as opaque void* (the generator maps a
 * non-char pointer to a conservative Option RawPtr).
 */
#ifndef NATIVE_UV_SHIM_H
#define NATIVE_UV_SHIM_H

/* bind+listen on host:port with the given backlog; returns a listener handle. */
void *http_uv_listen(const char *host, int port, int backlog);

/* block until the next connection arrives and accept it. */
void *http_uv_accept(void *listener);

/* read one request chunk (NUL-terminated HTTP text) from the connection. */
const char *http_uv_read(void *conn);

/* write the full response bytes to the connection. */
void http_uv_write(void *conn, const char *data);

/* close a connection / the listener (releases the handle). */
void http_uv_close_conn(void *conn);
void http_uv_close_listener(void *listener);

#endif /* NATIVE_UV_SHIM_H */
