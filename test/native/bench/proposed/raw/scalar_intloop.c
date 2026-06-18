/* Conservative raw-C lower bound for scalar_intloop (sumAcc 0 N).
 * volatile accumulator + runtime N so the compiler cannot fold the loop to a
 * closed form — a fair lower bound the LR1 unboxed Int worker is compared to. */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  int64_t n = argc > 1 ? (int64_t)atoll(argv[1]) : 10000000;
  volatile int64_t acc = 0;
  while (n > 0) { acc += n; n -= 1; }
  printf("%lld\n", (long long)acc);
  return 0;
}
