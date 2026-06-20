#ifndef DELVE_TERMINAL_H
#define DELVE_TERMINAL_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct delve_terminal_handle delve_terminal_handle;

typedef struct delve_size {
    int cols;
    int rows;
} delve_size;

int delve_open_terminal(delve_terminal_handle **out);
int delve_close_terminal(delve_terminal_handle *h);
int delve_read_key(delve_terminal_handle *h, int *out_code);
int delve_write_all(delve_terminal_handle *h, const char *text, int len);
int delve_get_size(delve_terminal_handle *h, delve_size *out_size);
uint64_t delve_monotonic_seed(void);
const char *delve_strerror(int code);

#ifdef __cplusplus
}
#endif

#endif
