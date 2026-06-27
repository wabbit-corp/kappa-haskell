/* xlang/pidigits reference — C (GMP, -O2). N HARDCODED = 5000 digits.
 *
 * CLBG pidigits: digits of pi via Gibbons' unbounded spigot, driven as a stream
 * of linear fractional transformations over a (q,r,t,k,n,l) state in GMP
 * arbitrary-precision integers. Output is the standard CLBG layout: 10 digits
 * per line, each line tagged `\t:<count>` with the running digit count; a short
 * final line is left-padded with spaces.
 *
 * Idiomatic-but-fair: a clean direct transcription using mpz_t and a handful of
 * reused scratch temporaries (GMP idiom — avoid per-step alloc). NOT the
 * hand-unrolled CLBG entry. Links -lgmp.
 *
 * NOTE: every step is a PARALLEL assignment — each new value is computed from
 * the OLD q,r,t,k,n,l. The new `n` is therefore computed into a scratch BEFORE
 * any of q,r,t are overwritten.
 */
#include <stdio.h>
#include <gmp.h>

#define N 5000 /* HARDCODED digit count */

int main(void) {
    mpz_t q, r, t, k, n, l;
    mpz_t tmp1, tmp2, nr;
    mpz_inits(q, r, t, k, n, l, tmp1, tmp2, nr, NULL);

    mpz_set_ui(q, 1);
    mpz_set_ui(r, 0);
    mpz_set_ui(t, 1);
    mpz_set_ui(k, 1);
    mpz_set_ui(n, 3);
    mpz_set_ui(l, 3);

    int digits = 0;
    int col = 0;
    while (digits < N) {
        /* test: is digit n ready?   4q + r - t < n*t */
        mpz_mul_ui(tmp1, q, 4);   /* 4q       */
        mpz_add(tmp1, tmp1, r);   /* 4q+r     */
        mpz_sub(tmp1, tmp1, t);   /* 4q+r-t   */
        mpz_mul(tmp2, n, t);      /* n*t      */
        if (mpz_cmp(tmp1, tmp2) < 0) {
            /* emit digit n (always a single 0..9) */
            gmp_printf("%Zd", n);
            digits++;
            col++;
            if (col == 10) {
                printf("\t:%d\n", digits);
                col = 0;
            }
            /* PARALLEL: q,r,n := 10q, 10(r-n*t), (10*(3q+r))/t - 10*n
             * compute new n from OLD q,r,t,n first. */
            mpz_mul_ui(nr, q, 3);   /* 3q (old)        */
            mpz_add(nr, nr, r);     /* 3q+r (old)      */
            mpz_mul_ui(nr, nr, 10); /* 10*(3q+r)       */
            mpz_tdiv_q(nr, nr, t);  /* /t (old)        */
            mpz_mul_ui(tmp1, n, 10);/* 10*n (old)      */
            mpz_sub(nr, nr, tmp1);  /* new n           */
            /* new q = 10q ; new r = 10*(r - n*t)  (n*t still in tmp2) */
            mpz_mul_ui(q, q, 10);
            mpz_sub(r, r, tmp2);
            mpz_mul_ui(r, r, 10);
            mpz_set(n, nr);
        } else {
            /* PARALLEL: produce next term —
             *   q,r,t,k,n,l := q*k, (2q+r)*l, t*l, k+1,
             *                  (q*(7k+2)+r*l)/(t*l), l+2
             * compute new n from OLD values first. */
            mpz_mul_ui(tmp1, k, 7);   /* 7k             */
            mpz_add_ui(tmp1, tmp1, 2);/* 7k+2           */
            mpz_mul(tmp1, q, tmp1);   /* q*(7k+2)       */
            mpz_mul(tmp2, r, l);      /* r*l            */
            mpz_add(tmp1, tmp1, tmp2);/* q*(7k+2)+r*l   */
            mpz_mul(tmp2, t, l);      /* t*l            */
            mpz_tdiv_q(nr, tmp1, tmp2);/* new n         */
            /* new r = (2q+r)*l */
            mpz_mul_ui(tmp1, q, 2);
            mpz_add(tmp1, tmp1, r);
            mpz_mul(tmp1, tmp1, l);
            /* new q = q*k ; new t = t*l ; new k = k+1 ; new l = l+2 */
            mpz_mul(q, q, k);
            mpz_mul(t, t, l);
            mpz_set(r, tmp1);
            mpz_add_ui(k, k, 1);
            mpz_add_ui(l, l, 2);
            mpz_set(n, nr);
        }
    }

    /* pad a short final line (N=5000 is a multiple of 10, so no-op here). */
    if (col > 0) {
        while (col < 10) { putchar(' '); col++; }
        printf("\t:%d\n", digits);
    }

    mpz_clears(q, r, t, k, n, l, tmp1, tmp2, nr, NULL);
    return 0;
}
