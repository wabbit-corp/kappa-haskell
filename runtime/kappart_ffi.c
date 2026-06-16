/* kappart_ffi.c — the full FFI runtime unit: POSIX TCP sockets + sqlite3.
 *
 * Links into native executables that use the foreign primitives named in
 * Kappa.Backend.Ffi (kept in lock-step with this file).  The HTTP+sqlite
 * demo (examples/native/http_sqlite) drives this surface: accept a TCP
 * connection, read an HTTP request, perform >=1 sqlite read/write, write
 * an HTTP response — all from a real native process.
 *
 * Foreign handles are wrapped in K_FGN values; the Boehm collector only
 * reclaims the small wrapper, the underlying OS resource is released by
 * the explicit close primitives (see docs/NATIVE_BACKEND.md §4, §6).
 */
#include "kappart.h"

#include <arpa/inet.h>
#include <netinet/in.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

#include <sqlite3.h>

/* ── handle helpers ────────────────────────────────────────────────── */

static int fgn_fd(KValue *v) {
  if (v->tag != K_FGN) krt_fail("ffi: expected a socket handle");
  return (int)(intptr_t)v->as.fgn.p;
}

static sqlite3 *fgn_db(KValue *v) {
  if (v->tag != K_FGN) krt_fail("ffi: expected a sqlite handle");
  return (sqlite3 *)v->as.fgn.p;
}

/* ── TCP sockets ───────────────────────────────────────────────────── */

static KValue *tcp_listen(KValue *portv) {
  int port = (int)kas_int(portv);
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  if (fd < 0) krt_fail("ffi: socket() failed");
  int one = 1;
  setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
  struct sockaddr_in addr;
  memset(&addr, 0, sizeof addr);
  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = htonl(INADDR_ANY);
  addr.sin_port = htons((uint16_t)port);
  if (bind(fd, (struct sockaddr *)&addr, sizeof addr) < 0)
    krt_fail("ffi: bind() failed (port in use?)");
  if (listen(fd, 16) < 0) krt_fail("ffi: listen() failed");
  return kfgn((void *)(intptr_t)fd, "tcp-listener");
}

static KValue *tcp_accept(KValue *lv) {
  int cfd = accept(fgn_fd(lv), NULL, NULL);
  if (cfd < 0) krt_fail("ffi: accept() failed");
  return kfgn((void *)(intptr_t)cfd, "tcp-conn");
}

static KValue *conn_read(KValue *cv) {
  char buf[8192];
  ssize_t n = read(fgn_fd(cv), buf, sizeof buf);
  if (n < 0) krt_fail("ffi: read() failed");
  return kstr(buf, (size_t)n);
}

static KValue *conn_write(KValue *cv, KValue *sv) {
  if (sv->tag != K_STR) krt_fail("ffi: __connWrite expects a String");
  const char *p = sv->as.str.p;
  size_t len = sv->as.str.len, off = 0;
  while (off < len) {
    ssize_t n = write(fgn_fd(cv), p + off, len - off);
    if (n <= 0) krt_fail("ffi: write() failed");
    off += (size_t)n;
  }
  return kunit();
}

static KValue *conn_close(KValue *cv) {
  close(fgn_fd(cv));
  return kunit();
}

/* ── sqlite3 ───────────────────────────────────────────────────────── */

static KValue *sqlite_open(KValue *pathv) {
  if (pathv->tag != K_STR) krt_fail("ffi: __sqliteOpen expects a String");
  sqlite3 *db = NULL;
  /* the string is NUL-terminated by kstr() */
  if (sqlite3_open(pathv->as.str.p, &db) != SQLITE_OK)
    krt_fail("ffi: sqlite3_open failed");
  return kfgn(db, "sqlite3");
}

static KValue *sqlite_exec(KValue *dbv, KValue *sqlv) {
  if (sqlv->tag != K_STR) krt_fail("ffi: __sqliteExec expects a String");
  char *err = NULL;
  if (sqlite3_exec(fgn_db(dbv), sqlv->as.str.p, NULL, NULL, &err) != SQLITE_OK) {
    fprintf(stderr, "kappa: sqlite exec error: %s\n", err ? err : "(unknown)");
    sqlite3_free(err);
    krt_fail("ffi: sqlite3_exec failed");
  }
  return kunit();
}

static KValue *sqlite_query_int(KValue *dbv, KValue *sqlv) {
  if (sqlv->tag != K_STR) krt_fail("ffi: __sqliteQueryInt expects a String");
  sqlite3_stmt *stmt = NULL;
  if (sqlite3_prepare_v2(fgn_db(dbv), sqlv->as.str.p, -1, &stmt, NULL) != SQLITE_OK)
    krt_fail("ffi: sqlite3_prepare failed");
  int64_t result = 0;
  if (sqlite3_step(stmt) == SQLITE_ROW)
    result = (int64_t)sqlite3_column_int64(stmt, 0);
  sqlite3_finalize(stmt);
  return kint(result);
}

static KValue *sqlite_query_text(KValue *dbv, KValue *sqlv) {
  if (sqlv->tag != K_STR) krt_fail("ffi: __sqliteQueryText expects a String");
  sqlite3_stmt *stmt = NULL;
  if (sqlite3_prepare_v2(fgn_db(dbv), sqlv->as.str.p, -1, &stmt, NULL) != SQLITE_OK)
    krt_fail("ffi: sqlite3_prepare failed");
  KValue *result;
  if (sqlite3_step(stmt) == SQLITE_ROW) {
    const unsigned char *t = sqlite3_column_text(stmt, 0);
    int n = sqlite3_column_bytes(stmt, 0);
    result = kstr((const char *)(t ? t : (const unsigned char *)""), (size_t)(t ? n : 0));
  } else {
    result = kstr0("");
  }
  sqlite3_finalize(stmt);
  return result;
}

static KValue *sqlite_close(KValue *dbv) {
  sqlite3_close(fgn_db(dbv));
  return kunit();
}

/* ── dispatch tables (consumed by the core runtime) ────────────────── */

#define IS(n) (strcmp(p, n) == 0)

int prim_is_io_ffi(const char *p) {
  return IS("__tcpListen") || IS("__tcpAccept") || IS("__connRead") ||
         IS("__connWrite") || IS("__connClose") || IS("__listenClose") ||
         IS("__sqliteOpen") || IS("__sqliteExec") || IS("__sqliteQueryInt") ||
         IS("__sqliteQueryText") || IS("__sqliteClose");
}

int prim_arity_ffi(const char *p) {
  if (IS("__tcpListen") || IS("__tcpAccept") || IS("__connRead") ||
      IS("__connClose") || IS("__listenClose") || IS("__sqliteOpen") ||
      IS("__sqliteClose"))
    return 1;
  if (IS("__connWrite") || IS("__sqliteExec") || IS("__sqliteQueryInt") ||
      IS("__sqliteQueryText"))
    return 2;
  krt_fail("internal: unknown FFI primitive arity");
}

KValue *krun_io_ffi(KValue *action) {
  const char *p = action->as.prim.name;
  KValue **a = action->as.prim.args;
  if (IS("__tcpListen")) return tcp_listen(a[0]);
  if (IS("__tcpAccept")) return tcp_accept(a[0]);
  if (IS("__connRead")) return conn_read(a[0]);
  if (IS("__connWrite")) return conn_write(a[0], a[1]);
  if (IS("__connClose")) return conn_close(a[0]);
  if (IS("__listenClose")) return conn_close(a[0]); /* same close() path */
  if (IS("__sqliteOpen")) return sqlite_open(a[0]);
  if (IS("__sqliteExec")) return sqlite_exec(a[0], a[1]);
  if (IS("__sqliteQueryInt")) return sqlite_query_int(a[0], a[1]);
  if (IS("__sqliteQueryText")) return sqlite_query_text(a[0], a[1]);
  if (IS("__sqliteClose")) return sqlite_close(a[0]);
  krt_fail("internal: unknown FFI IO primitive");
}
