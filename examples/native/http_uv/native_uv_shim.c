/* native_uv_shim.c — a thin BLOCKING adapter over libuv for the HTTP stack's
 * host.native transport (acme.http.runtime native fragment).
 *
 * This is ORDINARY C named by the package build manifest as a `shim`
 * realization input (§36.28). It does NOT hand-roll a socket primitive set:
 * all transport work is delegated to libuv (uv_tcp_*, uv_listen, uv_accept,
 * uv_read_*, uv_write, uv_run, uv_close), a pkg-config-discoverable public C
 * library. The libuv functions the shim depends on are declared in the
 * manifest's `verify` list and checked against the installed <uv.h> by the
 * native ABI verifier (fail-closed); the manifest's symbolList declares THESE
 * adapter symbols with their conservative ABI, which the backend lowers to
 * direct typed call sites.
 *
 * The adapter presents a simple blocking interface (listen / accept / read /
 * write / close) by running a single libuv event loop. The accept/read/write
 * waits use UV_RUN_ONCE (block until the awaited callback fires); handle
 * teardown pumps with UV_RUN_NOWAIT until a per-handle close flag is set by
 * close_cb, so it completes the asynchronous uv_close without blocking on the
 * still-active listening handle that shares the loop. Handles are plain void*
 * (the Kappa side treats them opaquely, as std.ffi.OpaqueHandle).
 *
 * Fatal setup failures (bind/listen on an unavailable port, allocation
 * failure) print a diagnostic and exit rather than returning a NULL handle the
 * UIO facade has no error channel to observe.
 */
#ifndef _GNU_SOURCE
#define _GNU_SOURCE 1 /* uv.h's unix backend needs pthread_rwlock_t etc. */
#endif
#include <uv.h>

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void http_uv_die(const char *what, int err) {
  if (err)
    fprintf(stderr, "http_uv: %s: %s\n", what, uv_strerror(err));
  else
    fprintf(stderr, "http_uv: %s\n", what);
  exit(1);
}

/* close_cb sets the int flag the handle's data points at, so a teardown pump
 * can detect that the asynchronous uv_close has actually completed. */
static void close_cb(uv_handle_t *h) {
  if (h->data) *(int *)h->data = 1;
}

/* Pump `loop` without blocking until `*flag` is set by close_cb. uv_close
 * completion runs in the loop's closing-handles phase, which fires under
 * UV_RUN_NOWAIT, so this never blocks on other active handles on the loop. */
static void drain_close(uv_loop_t *loop, const volatile int *flag) {
  while (!*flag) uv_run(loop, UV_RUN_NOWAIT);
}

/* ── listener state ─────────────────────────────────────────────────── */

typedef struct {
  uv_loop_t loop;
  uv_tcp_t server;
  int pending; /* a connection is waiting to be uv_accept'ed */
} HttpListener;

static void on_connection(uv_stream_t *server, int status) {
  HttpListener *l = (HttpListener *)server->data;
  if (status >= 0) l->pending = 1;
  uv_stop(&l->loop);
}

void *http_uv_listen(const char *host, int port, int backlog) {
  HttpListener *l = (HttpListener *)calloc(1, sizeof(HttpListener));
  if (!l) http_uv_die("out of memory", 0);
  int rc = uv_loop_init(&l->loop);
  if (rc) http_uv_die("uv_loop_init", rc);
  rc = uv_tcp_init(&l->loop, &l->server);
  if (rc) http_uv_die("uv_tcp_init", rc);
  l->server.data = l;
  struct sockaddr_in addr;
  rc = uv_ip4_addr(host, port, &addr);
  if (rc) http_uv_die("uv_ip4_addr", rc);
  rc = uv_tcp_bind(&l->server, (const struct sockaddr *)&addr, 0);
  if (rc) http_uv_die("uv_tcp_bind", rc);
  rc = uv_listen((uv_stream_t *)&l->server, backlog, on_connection);
  if (rc) http_uv_die("uv_listen", rc);
  return l;
}

/* ── connection state ───────────────────────────────────────────────── */

typedef struct {
  HttpListener *owner;
  uv_tcp_t client;
  /* one-shot read buffer */
  char *rbuf;
  ssize_t rlen;
  int read_done;
} HttpConn;

void *http_uv_accept(void *lp) {
  HttpListener *l = (HttpListener *)lp;
  while (!l->pending) uv_run(&l->loop, UV_RUN_ONCE);
  l->pending = 0;
  HttpConn *c = (HttpConn *)calloc(1, sizeof(HttpConn));
  if (!c) http_uv_die("out of memory", 0);
  c->owner = l;
  int rc = uv_tcp_init(&l->loop, &c->client);
  if (rc) http_uv_die("uv_tcp_init", rc);
  c->client.data = c;
  rc = uv_accept((uv_stream_t *)&l->server, (uv_stream_t *)&c->client);
  if (rc) {
    /* the client handle is already registered on the loop; close it
     * properly (never free a registered handle) before bailing out. */
    int closed = 0;
    c->client.data = &closed;
    uv_close((uv_handle_t *)&c->client, close_cb);
    drain_close(&l->loop, &closed);
    free(c);
    http_uv_die("uv_accept", rc);
  }
  return c;
}

static void alloc_cb(uv_handle_t *h, size_t suggested, uv_buf_t *buf) {
  (void)h;
  buf->base = (char *)malloc(suggested);
  buf->len = buf->base ? suggested : 0; /* NULL base must report zero len */
}

static void read_cb(uv_stream_t *s, ssize_t nread, const uv_buf_t *buf) {
  HttpConn *c = (HttpConn *)s->data;
  if (nread == 0) {
    /* libuv: 0 means "nothing right now" (EAGAIN-like), NOT EOF — keep
     * the read open and let the loop continue. */
    if (buf->base) free(buf->base);
    return;
  }
  if (nread > 0) {
    c->rbuf = (char *)malloc((size_t)nread + 1);
    if (c->rbuf) {
      memcpy(c->rbuf, buf->base, (size_t)nread);
      c->rbuf[nread] = '\0';
      c->rlen = nread;
    }
  } else {
    c->rbuf = NULL;
    c->rlen = nread; /* UV_EOF or a read error (<0) */
  }
  c->read_done = 1;
  uv_read_stop(s);
  uv_stop(&c->owner->loop);
  if (buf->base) free(buf->base);
}

/* returns a NUL-terminated request chunk (HTTP text); empty string on EOF. */
const char *http_uv_read(void *cp) {
  HttpConn *c = (HttpConn *)cp;
  free(c->rbuf); /* release any buffer from a prior read on this connection */
  c->rbuf = NULL;
  c->read_done = 0;
  int rc = uv_read_start((uv_stream_t *)&c->client, alloc_cb, read_cb);
  if (rc) http_uv_die("uv_read_start", rc);
  while (!c->read_done) uv_run(&c->owner->loop, UV_RUN_ONCE);
  return c->rbuf ? c->rbuf : "";
}

typedef struct {
  uv_write_t req;
  int done;
  HttpConn *conn;
} WriteReq;

static void write_cb(uv_write_t *req, int status) {
  /* This example serves small single-buffer responses; a short or failed
   * write is not retried (status is informational only here). */
  (void)status;
  WriteReq *w = (WriteReq *)req;
  w->done = 1;
  uv_stop(&w->conn->owner->loop);
}

void http_uv_write(void *cp, const char *data) {
  HttpConn *c = (HttpConn *)cp;
  WriteReq w;
  memset(&w, 0, sizeof(w));
  w.conn = c;
  /* responses must fit a single buffer (< 4 GiB); short writes are not split */
  uv_buf_t buf = uv_buf_init((char *)data, (unsigned)strlen(data));
  if (uv_write(&w.req, (uv_stream_t *)&c->client, &buf, 1, write_cb)) return;
  while (!w.done) uv_run(&c->owner->loop, UV_RUN_ONCE);
}

void http_uv_close_conn(void *cp) {
  HttpConn *c = (HttpConn *)cp;
  int closed = 0;
  c->client.data = &closed;
  uv_close((uv_handle_t *)&c->client, close_cb);
  drain_close(&c->owner->loop, &closed); /* await close before freeing */
  free(c->rbuf);
  free(c);
}

void http_uv_close_listener(void *lp) {
  HttpListener *l = (HttpListener *)lp;
  int closed = 0;
  l->server.data = &closed;
  uv_close((uv_handle_t *)&l->server, close_cb);
  drain_close(&l->loop, &closed); /* await close so uv_loop_close won't EBUSY */
  int rc = uv_loop_close(&l->loop);
  if (rc) fprintf(stderr, "http_uv: uv_loop_close: %s\n", uv_strerror(rc));
  free(l);
}
