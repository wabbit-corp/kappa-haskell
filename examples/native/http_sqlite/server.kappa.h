/* generated host-binding prototypes (§27.1.1 ABI check). */
#include <stdint.h>
#include <stddef.h>
extern void demo_conn_close(void *);
extern const char * demo_conn_read(void *);
extern void demo_conn_write(void *, const char *);
extern void demo_listen_close(void *);
extern void * demo_tcp_accept(void *);
extern void * demo_tcp_listen(int);
extern void demo_sqlite_close(void *);
extern void demo_sqlite_exec(void *, const char *);
extern void * demo_sqlite_open(const char *);
extern int64_t demo_sqlite_query_int(void *, const char *);
extern const char * demo_sqlite_query_text(void *, const char *);
