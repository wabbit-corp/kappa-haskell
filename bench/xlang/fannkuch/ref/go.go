// xlang/fannkuch reference — Go. N HARDCODED = 11.
//
// Fannkuch-redux (CLBG): over every permutation of 1..N, count prefix-reversals
// ("pancake flips") to bring 1 to the front; report the max flip count and a
// checksum (sum of (-1)^permindex * flips).
//
// Methodology: idiomatic clean Go, the canonical single-threaded
// fannkuch-redux walk (same shape as the C/Haskell refs here), NOT the
// multi-threaded / hand-tuned fastest CLBG entry.
//
// Reference answer for N=11: checksum 556355, Pfannkuchen(11) = 51.
package main

import "fmt"

const N = 11 // HARDCODED

func main() {
	var perm [N]int
	var perm1 [N]int
	var count [N]int

	for i := 0; i < N; i++ {
		perm1[i] = i
	}

	checksum := int64(0)
	maxflips := 0
	permcount := 0
	r := N

	for {
		for r != 1 {
			count[r-1] = r
			r--
		}

		copy(perm[:], perm1[:])
		flips := 0
		for {
			k := perm[0]
			if k == 0 {
				break
			}
			lo, hi := 0, k
			for lo < hi {
				perm[lo], perm[hi] = perm[hi], perm[lo]
				lo++
				hi--
			}
			flips++
		}
		if flips > maxflips {
			maxflips = flips
		}
		if permcount%2 == 0 {
			checksum += int64(flips)
		} else {
			checksum -= int64(flips)
		}

		for {
			if r == N {
				fmt.Printf("%d\nPfannkuchen(%d) = %d\n", checksum, N, maxflips)
				return
			}
			first := perm1[0]
			for i := 0; i < r; i++ {
				perm1[i] = perm1[i+1]
			}
			perm1[r] = first

			count[r]--
			if count[r] > 0 {
				break
			}
			r++
		}

		permcount++
	}
}
