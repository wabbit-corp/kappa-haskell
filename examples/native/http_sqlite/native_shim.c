/* native_shim.c — the demo's C shim for its host.native bindings.
 *
 * This is ORDINARY C named by the package build manifest (kappa.build.kp)
 * as a `shim` realization input (§36.28). It exposes simple C-ABI functions
 * (scalars / opaque void* handles / NUL-terminated strings) that the
 * manifest's `symbolList` declares with their ABI signatures. The Kappa
 * native backend generates a direct `extern` prototype + a typed marshalling
 * wrapper + a direct call for each — there is no runtime FFI primitive table
 * and no string dispatch. The handles are plain pointers (a socket fd cast
 * to void*, or a sqlite3*); the Kappa side treats them opaquely (OpaqueHandle).
 */
#include <arpa/inet.h>
#include <netinet/in.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

#include <sqlite3.h>

static void shim_fail(const char *msg) {
  fprintf(stderr, "kappa native shim: %s\n", msg);
  exit(1);
}

/* ── sqlite3 (CtHandle = sqlite3*; CtString in; CtInt64/CtUnit out) ──── */

void *demo_sqlite_open(const char *path) {
  sqlite3 *db = NULL;
  if (sqlite3_open(path, &db) != SQLITE_OK) shim_fail("sqlite3_open failed");
  return (void *)db;
}

void demo_sqlite_exec(void *db, const char *sql) {
  char *err = NULL;
  if (sqlite3_exec((sqlite3 *)db, sql, NULL, NULL, &err) != SQLITE_OK) {
    fprintf(stderr, "kappa native shim: sqlite exec error: %s\n", err ? err : "(unknown)");
    sqlite3_free(err);
    shim_fail("sqlite3_exec failed");
  }
}

int64_t demo_sqlite_query_int(void *db, const char *sql) {
  sqlite3_stmt *stmt = NULL;
  if (sqlite3_prepare_v2((sqlite3 *)db, sql, -1, &stmt, NULL) != SQLITE_OK)
    shim_fail("sqlite3_prepare failed");
  int64_t result = 0;
  if (sqlite3_step(stmt) == SQLITE_ROW) result = (int64_t)sqlite3_column_int64(stmt, 0);
  sqlite3_finalize(stmt);
  return result;
}

/* Return the first column of the first row as a NUL-terminated string (a small
 * static buffer; the conservative C-string convention, declared `cstrings`). */
const char *demo_sqlite_query_text(void *db, const char *sql) {
  static char buf[1024];
  buf[0] = '\0';
  sqlite3_stmt *stmt = NULL;
  if (sqlite3_prepare_v2((sqlite3 *)db, sql, -1, &stmt, NULL) != SQLITE_OK)
    shim_fail("sqlite3_prepare failed");
  if (sqlite3_step(stmt) == SQLITE_ROW) {
    const unsigned char *t = sqlite3_column_text(stmt, 0);
    if (t) {
      size_t i = 0;
      for (; t[i] != '\0' && i + 1 < sizeof(buf); i++) buf[i] = (char)t[i];
      buf[i] = '\0';
    }
  }
  sqlite3_finalize(stmt);
  return buf;
}

void demo_sqlite_close(void *db) { sqlite3_close((sqlite3 *)db); }

/* ── POSIX TCP (CtHandle = fd cast to void*; CtInt64 port; CtString io) ─ */

void *demo_tcp_listen(int port) {
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  if (fd < 0) shim_fail("socket() failed");
  int one = 1;
  setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
  struct sockaddr_in addr;
  memset(&addr, 0, sizeof addr);
  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = htonl(INADDR_ANY);
  addr.sin_port = htons((uint16_t)port);
  if (bind(fd, (struct sockaddr *)&addr, sizeof addr) < 0) shim_fail("bind() failed (port in use?)");
  if (listen(fd, 16) < 0) shim_fail("listen() failed");
  return (void *)(intptr_t)fd;
}

void *demo_tcp_accept(void *listener) {
  int cfd = accept((int)(intptr_t)listener, NULL, NULL);
  if (cfd < 0) shim_fail("accept() failed");
  return (void *)(intptr_t)cfd;
}

/* returns a NUL-terminated copy of the request bytes (HTTP text — no NULs) */
const char *demo_conn_read(void *conn) {
  static char buf[8192];
  ssize_t n = read((int)(intptr_t)conn, buf, sizeof buf - 1);
  if (n < 0) shim_fail("read() failed");
  buf[n] = '\0';
  return buf;
}

void demo_conn_write(void *conn, const char *s) {
  size_t len = strlen(s), off = 0;
  while (off < len) {
    ssize_t n = write((int)(intptr_t)conn, s + off, len - off);
    if (n <= 0) shim_fail("write() failed");
    off += (size_t)n;
  }
}

void demo_conn_close(void *conn) { close((int)(intptr_t)conn); }

void demo_listen_close(void *listener) { close((int)(intptr_t)listener); }
