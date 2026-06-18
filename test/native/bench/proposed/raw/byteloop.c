/* Like-for-like raw-C lower bound for byteloop: a flat per-byte buffer scan.
 * The Kappa bench folds a List Byte of N bytes summing each value; this is the
 * achievable cost of touching N bytes without per-byte K_BYTE/kint boxing.
 * N bytes of value 1 -> sum == N. volatile acc + runtime N defeats folding. */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  int64_t n = argc > 1 ? (int64_t)atoll(argv[1]) : 1000000;
  unsigned char *buf = (unsigned char *)malloc((size_t)n);
  for (int64_t i = 0; i < n; i++) buf[i] = 1;
  volatile int64_t acc = 0;
  for (int64_t i = 0; i < n; i++) acc += (int64_t)buf[i];
  printf("%lld\n", (long long)acc);
  return 0;
}
