/* xlang/spectralnorm reference — C (-O2).  N HARDCODED = 5500.
 *
 * Spectral norm (CLBG): largest singular value of the infinite matrix
 *   A(i,j) = 1 / ((i+j)*(i+j+1)/2 + i + 1)
 * computed by the power method: starting from u = [1,1,...], iterate
 *   v = (A^T A) u   ten times   and report  sqrt( (u . v) / (v . v) ).
 *
 * Idiomatic + clean, -O2 — NOT the hyper-tuned CLBG SIMD/pthread entry.
 * Single-threaded, plain double arrays, the textbook A/At/AtA helpers.
 * Prints the result to 9 decimals.
 */
#include <math.h>
#include <stdio.h>

/* N = 5500 */
#define N 5500

/* A(i,j) = 1 / ((i+j)(i+j+1)/2 + i + 1) */
static double A(int i, int j) {
    long ij = (long)(i + j);
    return 1.0 / (double)((ij * (ij + 1)) / 2 + i + 1);
}

/* w = A v */
static void mulAv(const double *v, double *w) {
    for (int i = 0; i < N; i++) {
        double s = 0.0;
        for (int j = 0; j < N; j++) s += A(i, j) * v[j];
        w[i] = s;
    }
}

/* w = A^T v  (A^T(i,j) = A(j,i)) */
static void mulAtv(const double *v, double *w) {
    for (int i = 0; i < N; i++) {
        double s = 0.0;
        for (int j = 0; j < N; j++) s += A(j, i) * v[j];
        w[i] = s;
    }
}

/* w = A^T A v  (via a scratch buffer) */
static void mulAtAv(const double *v, double *w, double *tmp) {
    mulAv(v, tmp);
    mulAtv(tmp, w);
}

int main(void) {
    double u[N], v[N], tmp[N];
    for (int i = 0; i < N; i++) u[i] = 1.0;

    for (int k = 0; k < 10; k++) {
        mulAtAv(u, v, tmp);
        mulAtAv(v, u, tmp);
    }

    double vBv = 0.0, vv = 0.0;
    for (int i = 0; i < N; i++) {
        vBv += u[i] * v[i];
        vv += v[i] * v[i];
    }
    printf("%.9f\n", sqrt(vBv / vv));
    return 0;
}
