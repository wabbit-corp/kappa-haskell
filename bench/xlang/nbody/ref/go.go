// xlang/nbody reference — Go.  N HARDCODED = 5000000 steps.
//
// The classic CLBG N-body: Sun + 4 Jovian planets under Newtonian gravity,
// leapfrog integrator (dt = 0.01), print total system energy before and after
// to 9 decimals.  Idiomatic readable formulation (plain O(n^2) pairwise loop
// with math.Sqrt) — NOT the hand-tuned SIMD CLBG entry — for a fair baseline.
package main

import (
	"fmt"
	"math"
)

const nSteps = 5000000 // HARDCODED step count (must match every impl)

const (
	pi          = 3.141592653589793
	solarMass   = 4.0 * pi * pi
	daysPerYear = 365.24
)

type body struct {
	x, y, z    float64
	vx, vy, vz float64
	mass       float64
}

var bodies = []body{
	// Sun
	{0, 0, 0, 0, 0, 0, solarMass},
	// Jupiter
	{4.84143144246472090e+00, -1.16032004402742839e+00, -1.03622044471123109e-01,
		1.66007664274403694e-03 * daysPerYear, 7.69901118419740425e-03 * daysPerYear,
		-6.90460016972063023e-05 * daysPerYear, 9.54791938424326609e-04 * solarMass},
	// Saturn
	{8.34336671824457987e+00, 4.12479856412430479e+00, -4.03523417114321381e-01,
		-2.76742510726862411e-03 * daysPerYear, 4.99852801234917238e-03 * daysPerYear,
		2.30417297573763929e-05 * daysPerYear, 2.85885980666130812e-04 * solarMass},
	// Uranus
	{1.28943695621391310e+01, -1.51111514016986312e+01, -2.23307578892655734e-01,
		2.96460137564761618e-03 * daysPerYear, 2.37847173959480950e-03 * daysPerYear,
		-2.96589568540237556e-05 * daysPerYear, 4.36624404335156298e-05 * solarMass},
	// Neptune
	{1.53796971148509165e+01, -2.59193146099879641e+01, 1.79258772950371181e-01,
		2.68067772490389322e-03 * daysPerYear, 1.62824170038242295e-03 * daysPerYear,
		-9.51592254519715870e-05 * daysPerYear, 5.15138902046611451e-05 * solarMass},
}

func offsetMomentum() {
	var px, py, pz float64
	for i := range bodies {
		px += bodies[i].vx * bodies[i].mass
		py += bodies[i].vy * bodies[i].mass
		pz += bodies[i].vz * bodies[i].mass
	}
	bodies[0].vx = -px / solarMass
	bodies[0].vy = -py / solarMass
	bodies[0].vz = -pz / solarMass
}

func energy() float64 {
	var e float64
	for i := range bodies {
		e += 0.5 * bodies[i].mass *
			(bodies[i].vx*bodies[i].vx + bodies[i].vy*bodies[i].vy + bodies[i].vz*bodies[i].vz)
		for j := i + 1; j < len(bodies); j++ {
			dx := bodies[i].x - bodies[j].x
			dy := bodies[i].y - bodies[j].y
			dz := bodies[i].z - bodies[j].z
			dist := math.Sqrt(dx*dx + dy*dy + dz*dz)
			e -= (bodies[i].mass * bodies[j].mass) / dist
		}
	}
	return e
}

func advance(dt float64) {
	for i := range bodies {
		for j := i + 1; j < len(bodies); j++ {
			dx := bodies[i].x - bodies[j].x
			dy := bodies[i].y - bodies[j].y
			dz := bodies[i].z - bodies[j].z
			d2 := dx*dx + dy*dy + dz*dz
			mag := dt / (d2 * math.Sqrt(d2))
			bodies[i].vx -= dx * bodies[j].mass * mag
			bodies[i].vy -= dy * bodies[j].mass * mag
			bodies[i].vz -= dz * bodies[j].mass * mag
			bodies[j].vx += dx * bodies[i].mass * mag
			bodies[j].vy += dy * bodies[i].mass * mag
			bodies[j].vz += dz * bodies[i].mass * mag
		}
	}
	for i := range bodies {
		bodies[i].x += dt * bodies[i].vx
		bodies[i].y += dt * bodies[i].vy
		bodies[i].z += dt * bodies[i].vz
	}
}

func main() {
	offsetMomentum()
	fmt.Printf("%.9f\n", energy())
	for s := 0; s < nSteps; s++ {
		advance(0.01)
	}
	fmt.Printf("%.9f\n", energy())
}
