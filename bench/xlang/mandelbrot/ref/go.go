// xlang/mandelbrot reference — Go.  N HARDCODED = 4000.
//
// CLBG Mandelbrot: render the NxN portable-bitmap (PBM) of the Mandelbrot set,
// 8 pixels packed MSB-first per byte, then fold the packed bytes into a single
// 64-bit rolling checksum so the program prints ONE line (we time compute, not
// I/O).  See ref/c.c for the full algorithm + bit-identity note: the iteration
// uses explicit temporaries (no a*b+c) so Go's no-FMA-fusion default and the
// other languages' separately-rounded ops all agree bit-for-bit.  The checksum
// is an explicitly-MODULAR rolling hash (mod 2^31-1) so it matches Kappa, whose
// Int is an arbitrary-precision Integer with no machine-word wraparound; see
// ref/c.c for the full rationale.
package main

import "fmt"

const N = 4000           // image is N x N
const ITER = 50          // mandelbrot iteration count
const MOD = 2147483647   // 2^31 - 1; rolling-hash modulus (portable)

func main() {
	var checksum int64 = 0
	for py := 0; py < N; py++ {
		ci := 2.0*float64(py)/float64(N) - 1.0
		nbits := 0
		var byteAcc int64 = 0
		for px := 0; px < N; px++ {
			cr := 2.0*float64(px)/float64(N) - 1.5
			zr, zi := 0.0, 0.0
			for i := 0; i < ITER; i++ {
				zr2 := zr * zr
				zi2 := zi * zi
				zrzi := zr * zi
				zr = zr2 - zi2 + cr
				zi = zrzi + zrzi + ci // 2*zr*zi, no FMA fusion
			}
			mag := zr*zr + zi*zi
			inside := int64(0)
			if mag <= 4.0 {
				inside = 1
			}
			byteAcc = byteAcc*2 + inside // shift-in MSB-first
			nbits++
			if nbits == 8 {
				checksum = (checksum*1000003 + byteAcc) % MOD
				byteAcc = 0
				nbits = 0
			}
		}
		if nbits != 0 {
			for nbits < 8 {
				byteAcc = byteAcc * 2
				nbits++
			}
			checksum = (checksum*1000003 + byteAcc) % MOD
		}
	}
	fmt.Println(checksum)
}
