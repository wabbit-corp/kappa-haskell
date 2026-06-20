/* Package-owned shim defining the host.native.sqlite3 provider symbols
 * for the codegen-lowering fixture (no real sqlite3 dependency). */
void *sqlite3_open_x(const char *p) { (void)p; return (void *)0; }
void sqlite3_close_x(void *h) { (void)h; }
