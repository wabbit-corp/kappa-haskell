/* xlang/nbody reference — C (-O2).  N HARDCODED = 5000000 steps.
 *
 * The classic CLBG N-body: advance the Sun + 4 Jovian planets under Newtonian
 * gravity with a symplectic leapfrog-style integrator (dt = 0.01), and print
 * the total system energy (kinetic + potential) before and after the run, to
 * 9 decimal places.
 *
 * Methodology: this is the IDIOMATIC, readable formulation (a plain O(n^2)
 * pairwise loop with a hardware sqrt) — NOT the hand-unrolled / SIMD-intrinsic
 * CLBG "fastest" entry.  We want a fair, clean baseline across languages.
 */
#include <math.h>
#include <stdio.h>

#define N_STEPS 5000000 /* HARDCODED step count (must match every impl) */

#define PI 3.141592653589793
#define SOLAR_MASS (4.0 * PI * PI)
#define DAYS_PER_YEAR 365.24

#define NBODIES 5

typedef struct {
    double x, y, z;
    double vx, vy, vz;
    double mass;
} body;

static body bodies[NBODIES] = {
    /* Sun */
    {0.0, 0.0, 0.0, 0.0, 0.0, 0.0, SOLAR_MASS},
    /* Jupiter */
    {4.84143144246472090e+00, -1.16032004402742839e+00, -1.03622044471123109e-01,
     1.66007664274403694e-03 * DAYS_PER_YEAR, 7.69901118419740425e-03 * DAYS_PER_YEAR,
     -6.90460016972063023e-05 * DAYS_PER_YEAR, 9.54791938424326609e-04 * SOLAR_MASS},
    /* Saturn */
    {8.34336671824457987e+00, 4.12479856412430479e+00, -4.03523417114321381e-01,
     -2.76742510726862411e-03 * DAYS_PER_YEAR, 4.99852801234917238e-03 * DAYS_PER_YEAR,
     2.30417297573763929e-05 * DAYS_PER_YEAR, 2.85885980666130812e-04 * SOLAR_MASS},
    /* Uranus */
    {1.28943695621391310e+01, -1.51111514016986312e+01, -2.23307578892655734e-01,
     2.96460137564761618e-03 * DAYS_PER_YEAR, 2.37847173959480950e-03 * DAYS_PER_YEAR,
     -2.96589568540237556e-05 * DAYS_PER_YEAR, 4.36624404335156298e-05 * SOLAR_MASS},
    /* Neptune */
    {1.53796971148509165e+01, -2.59193146099879641e+01, 1.79258772950371181e-01,
     2.68067772490389322e-03 * DAYS_PER_YEAR, 1.62824170038242295e-03 * DAYS_PER_YEAR,
     -9.51592254519715870e-05 * DAYS_PER_YEAR, 5.15138902046611451e-05 * SOLAR_MASS}};

static void offset_momentum(void) {
    double px = 0.0, py = 0.0, pz = 0.0;
    for (int i = 0; i < NBODIES; i++) {
        px += bodies[i].vx * bodies[i].mass;
        py += bodies[i].vy * bodies[i].mass;
        pz += bodies[i].vz * bodies[i].mass;
    }
    bodies[0].vx = -px / SOLAR_MASS;
    bodies[0].vy = -py / SOLAR_MASS;
    bodies[0].vz = -pz / SOLAR_MASS;
}

static double energy(void) {
    double e = 0.0;
    for (int i = 0; i < NBODIES; i++) {
        e += 0.5 * bodies[i].mass *
             (bodies[i].vx * bodies[i].vx + bodies[i].vy * bodies[i].vy +
              bodies[i].vz * bodies[i].vz);
        for (int j = i + 1; j < NBODIES; j++) {
            double dx = bodies[i].x - bodies[j].x;
            double dy = bodies[i].y - bodies[j].y;
            double dz = bodies[i].z - bodies[j].z;
            double dist = sqrt(dx * dx + dy * dy + dz * dz);
            e -= (bodies[i].mass * bodies[j].mass) / dist;
        }
    }
    return e;
}

static void advance(double dt) {
    for (int i = 0; i < NBODIES; i++) {
        for (int j = i + 1; j < NBODIES; j++) {
            double dx = bodies[i].x - bodies[j].x;
            double dy = bodies[i].y - bodies[j].y;
            double dz = bodies[i].z - bodies[j].z;
            double d2 = dx * dx + dy * dy + dz * dz;
            double mag = dt / (d2 * sqrt(d2));
            bodies[i].vx -= dx * bodies[j].mass * mag;
            bodies[i].vy -= dy * bodies[j].mass * mag;
            bodies[i].vz -= dz * bodies[j].mass * mag;
            bodies[j].vx += dx * bodies[i].mass * mag;
            bodies[j].vy += dy * bodies[i].mass * mag;
            bodies[j].vz += dz * bodies[i].mass * mag;
        }
    }
    for (int i = 0; i < NBODIES; i++) {
        bodies[i].x += dt * bodies[i].vx;
        bodies[i].y += dt * bodies[i].vy;
        bodies[i].z += dt * bodies[i].vz;
    }
}

int main(void) {
    offset_momentum();
    printf("%.9f\n", energy());
    for (int s = 0; s < N_STEPS; s++) {
        advance(0.01);
    }
    printf("%.9f\n", energy());
    return 0;
}
