/* xlang/mandelbrot reference — C (-O2).  N HARDCODED = 4000.
 *
 * CLBG Mandelbrot: render the NxN portable-bitmap (PBM) of the Mandelbrot set,
 * 8 pixels packed MSB-first per byte, then fold the packed bytes into a single
 * 64-bit rolling checksum so the program prints ONE line (compute, not I/O, is
 * what we time).
 *
 * Membership: for pixel (px,py),  Cr = 2*px/N - 1.5 ,  Ci = 2*py/N - 1.0 ;
 * iterate Z <- Z^2 + C for ITER=50 steps; the pixel is IN-SET (bit 1) iff
 * Zr*Zr + Zi*Zi <= 4.0 after the last step.
 *
 * Bit-identity note: the iteration is written with explicit temporaries
 * (no a*b+c expression) so no compiler fuses a multiply-add into a single
 * rounded FMA.  Every reference impl (kappa.kp / go / hs / c) performs the
 * SAME sequence of separately-rounded IEEE-754 double ops, so the membership
 * decision — and therefore the checksum — is bit-identical across languages.
 *
 * The checksum is an explicitly-MODULAR rolling hash, mod MOD = 2147483647
 * (2^31-1).  This matters because Kappa's `Int` is an arbitrary-precision
 * Integer (no machine-word wraparound), so the hash MUST be reduced the same
 * way in every language; the small modulus keeps every intermediate product
 * (< MOD*1000003 ~ 2.1e15) inside both a signed int64 and a uint64, so the
 * result is portable with no width-dependent behavior at all.
 */
#include <stdint.h>
#include <stdio.h>

#define N 4000              /* image is N x N */
#define ITER 50             /* mandelbrot iteration count */
#define MOD 2147483647      /* 2^31 - 1; rolling-hash modulus (portable) */

int main(void) {
    int64_t checksum = 0;
    for (int py = 0; py < N; py++) {
        double ci = 2.0 * (double)py / (double)N - 1.0;
        int nbits = 0;        /* how many pixels are packed into `byte`  */
        int64_t byte = 0;
        for (int px = 0; px < N; px++) {
            double cr = 2.0 * (double)px / (double)N - 1.5;
            double zr = 0.0, zi = 0.0;
            int inside = 1;
            for (int i = 0; i < ITER; i++) {
                double zr2 = zr * zr;
                double zi2 = zi * zi;
                double zrzi = zr * zi;
                zr = zr2 - zi2 + cr;
                zi = zrzi + zrzi + ci;   /* 2*zr*zi, no FMA fusion */
            }
            double mag = zr * zr + zi * zi;
            inside = (mag <= 4.0) ? 1 : 0;
            byte = byte * 2 + (int64_t)inside;   /* shift-in MSB-first */
            nbits++;
            if (nbits == 8) {
                checksum = (checksum * 1000003 + byte) % MOD;
                byte = 0;
                nbits = 0;
            }
        }
        /* N=4000 is a multiple of 8, so no partial trailing byte; the guard
         * below keeps the algorithm correct for any N. */
        if (nbits != 0) {
            while (nbits < 8) { byte = byte * 2; nbits++; }
            checksum = (checksum * 1000003 + byte) % MOD;
        }
    }
    printf("%lld\n", (long long)checksum);
    return 0;
}
