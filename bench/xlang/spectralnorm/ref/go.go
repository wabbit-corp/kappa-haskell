// xlang/spectralnorm reference — Go.  N HARDCODED = 5500.
//
// Spectral norm (CLBG): largest singular value of the infinite matrix
//   A(i,j) = 1 / ((i+j)*(i+j+1)/2 + i + 1)
// via the power method: 10 iterations of v = (A^T A) u, then
//   sqrt( (u . v) / (v . v) ).
//
// Idiomatic + clean (plain []float64 slices, textbook A/At/AtA helpers),
// single-threaded — NOT the goroutine-parallel CLBG entry.  Prints 9 decimals.
package main

import (
	"fmt"
	"math"
)

// N = 5500
const N = 5500

// A(i,j) = 1 / ((i+j)(i+j+1)/2 + i + 1)
func a(i, j int) float64 {
	ij := i + j
	return 1.0 / float64((ij*(ij+1))/2+i+1)
}

// w = A v
func mulAv(v, w []float64) {
	for i := 0; i < N; i++ {
		s := 0.0
		for j := 0; j < N; j++ {
			s += a(i, j) * v[j]
		}
		w[i] = s
	}
}

// w = A^T v
func mulAtv(v, w []float64) {
	for i := 0; i < N; i++ {
		s := 0.0
		for j := 0; j < N; j++ {
			s += a(j, i) * v[j]
		}
		w[i] = s
	}
}

// w = A^T A v
func mulAtAv(v, w, tmp []float64) {
	mulAv(v, tmp)
	mulAtv(tmp, w)
}

func main() {
	u := make([]float64, N)
	v := make([]float64, N)
	tmp := make([]float64, N)
	for i := range u {
		u[i] = 1.0
	}

	for k := 0; k < 10; k++ {
		mulAtAv(u, v, tmp)
		mulAtAv(v, u, tmp)
	}

	vBv, vv := 0.0, 0.0
	for i := 0; i < N; i++ {
		vBv += u[i] * v[i]
		vv += v[i] * v[i]
	}
	fmt.Printf("%.9f\n", math.Sqrt(vBv/vv))
}
