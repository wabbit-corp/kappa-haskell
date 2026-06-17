/* Conservative raw-C baseline for the LR1 tail-recursive Int sum
 * (sumAcc 0 N).  N comes from argv and the accumulator is volatile so the
 * compiler cannot fold the loop to a closed form — a fair lower bound for a
 * scalar int64 loop the LR1 worker is compared against. */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  int64_t n = argc > 1 ? (int64_t)atoll(argv[1]) : 100000000;
  volatile int64_t acc = 0;
  while (n > 0) { acc += n; n -= 1; }
  printf("%lld\n", (long long)acc);
  return 0;
}
