/* xlang/fannkuch reference — C (-O2). N HARDCODED = 11.
 *
 * Fannkuch-redux (CLBG): over every permutation of 1..N, count the number of
 * prefix-reversals ("pancake flips") needed to bring the value 1 to the front;
 * report the maximum flip count and a checksum, summing (+flips) for
 * even-indexed permutations and (-flips) for odd-indexed ones.
 *
 * Methodology: idiomatic, clean -O2 C. This is the canonical single-threaded
 * fannkuch-redux algorithm (the permutation walk used by the CLBG reference
 * entries), NOT the hand-vectorised / multi-threaded fastest CLBG entry. The
 * goal is a fair like-for-like int-array port across languages.
 *
 * Reference answer for N=11: checksum 556355, Pfannkuchen(11) = 51. */
#include <stdint.h>
#include <stdio.h>

#define N 11

int main(void) {
    int perm[N];
    int perm1[N];
    int count[N];
    int i;

    for (i = 0; i < N; i++) perm1[i] = i; /* initial (identity) permutation */

    int64_t checksum = 0;
    int maxflips = 0;
    int permcount = 0;

    int r = N;
    for (;;) {
        /* finish generating the current permutation: rotate the prefixes that
         * the previous step left "open" (count[i] tracks the rotation state of
         * prefix i). */
        while (r != 1) {
            count[r - 1] = r;
            r--;
        }

        /* count flips on a working copy of perm1 */
        for (i = 0; i < N; i++) perm[i] = perm1[i];
        int flips = 0;
        int k;
        while ((k = perm[0]) != 0) {
            /* reverse perm[0..k] inclusive */
            int lo = 0, hi = k;
            while (lo < hi) {
                int t = perm[lo];
                perm[lo] = perm[hi];
                perm[hi] = t;
                lo++;
                hi--;
            }
            flips++;
        }
        if (flips > maxflips) maxflips = flips;
        checksum += (permcount % 2 == 0) ? flips : -flips;

        /* generate the next permutation: rotate prefixes left-by-one and tick
         * the factorial-radix counters until one does not saturate. */
        for (;;) {
            if (r == N) {
                printf("%lld\nPfannkuchen(%d) = %d\n",
                       (long long)checksum, N, maxflips);
                return 0;
            }
            int first = perm1[0];
            for (i = 0; i < r; i++) perm1[i] = perm1[i + 1];
            perm1[r] = first;

            count[r]--;
            if (count[r] > 0) break;
            r++;
        }

        permcount++;
    }
}
