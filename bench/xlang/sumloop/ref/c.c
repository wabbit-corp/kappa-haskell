/* xlang/sumloop reference — C (-O2). N HARDCODED = 10000000. */
#include <stdint.h>
#include <stdio.h>

int main(void) {
    int64_t acc = 0;
    for (int64_t i = 0; i <= 10000000; i++) {
        acc += i;
    }
    printf("%lld\n", (long long)acc);
    return 0;
}
