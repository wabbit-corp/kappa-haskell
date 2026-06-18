/* Conservative raw-C lower bound for scalar_doubleloop.
 * volatile double accumulator + runtime N so the loop cannot be folded. */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  int64_t n = argc > 1 ? (int64_t)atoll(argv[1]) : 2000000;
  volatile double acc = 0.0;
  while (n > 0) { acc += (double)n; n -= 1; }
  printf("%g\n", (double)acc);
  return 0;
}
