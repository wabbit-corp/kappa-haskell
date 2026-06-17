/* Conservative raw-C baseline for the arithloop var-while sum (1..N). */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  int64_t lim = argc > 1 ? (int64_t)atoll(argv[1]) : 100000000;
  volatile int64_t total = 0;
  int64_t i = 1;
  while (i <= lim) { total += i; i += 1; }
  printf("%lld\n", (long long)total);
  return 0;
}
