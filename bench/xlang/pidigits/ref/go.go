// xlang/pidigits reference — Go (math/big). N HARDCODED = 5000 digits.
//
// CLBG pidigits: the digits of pi via Gibbons' unbounded spigot, driven as a
// stream of linear fractional transformations over a (q,r,t,k,n,l) state in
// arbitrary-precision integers (Go's math/big, GMP-equivalent). Output is the
// standard CLBG layout: 10 digits per line, each line tagged `\t:<count>` with
// the running digit count; a short final line is left-padded with spaces.
//
// Idiomatic-but-fair: a clean direct transcription of the algorithm, -O2-style
// (Go's default optimizer). NOT the hand-unrolled CLBG entry.
package main

import (
	"bufio"
	"fmt"
	"math/big"
	"os"
)

const N = 5000 // HARDCODED digit count

func main() {
	w := bufio.NewWriter(os.Stdout)
	defer w.Flush()

	q := big.NewInt(1)
	r := big.NewInt(0)
	t := big.NewInt(1)
	k := big.NewInt(1)
	n := big.NewInt(3)
	l := big.NewInt(3)

	// scratch
	tmp1 := new(big.Int)
	tmp2 := new(big.Int)
	nr := new(big.Int) // candidate next digit

	ten := big.NewInt(10)
	two := big.NewInt(2)
	three := big.NewInt(3)
	four := big.NewInt(4)
	seven := big.NewInt(7)

	digits := 0
	col := 0
	for digits < N {
		// test: is digit n ready?  (4q+r-t) < n*t
		tmp1.Mul(four, q)   // 4q
		tmp1.Add(tmp1, r)   // 4q+r
		tmp1.Sub(tmp1, t)   // 4q+r-t
		tmp2.Mul(n, t)      // n*t
		if tmp1.Cmp(tmp2) < 0 {
			// emit digit n
			fmt.Fprintf(w, "%d", n)
			digits++
			col++
			if col == 10 {
				fmt.Fprintf(w, "\t:%d\n", digits)
				col = 0
			}
			// PARALLEL assignment — every RHS uses the OLD q,r,t,n:
			//   q,r,t,n := 10q, 10(r-n*t), t, (10*(3q+r))/t - 10*n
			// Compute the new n FIRST, from the OLD q,r,t,n, into nr.
			nr.Mul(three, q)    // 3*q (old)
			nr.Add(nr, r)       // 3q+r (old)
			nr.Mul(ten, nr)     // 10*(3q+r)
			nr.Quo(nr, t)       // /t (old)
			tmp1.Mul(ten, n)    // 10*n (old)
			nr.Sub(nr, tmp1)    // new n
			// new q = 10q ; new r = 10*(r - n*t)  (n*t already in tmp2)
			q.Mul(ten, q)
			r.Sub(r, tmp2)
			r.Mul(ten, r)
			n.Set(nr)
		} else {
			// produce next term — a PARALLEL assignment, every RHS uses the OLD
			// q,r,t,k,n,l:
			//   q,r,t,k,n,l := q*k, (2q+r)*l, t*l, k+1,
			//                  (q*(7k+2)+r*l)/(t*l), l+2
			// Compute the new n FIRST (from the old values) into nr, then mutate.
			tmp1.Mul(seven, k)  // 7k
			tmp1.Add(tmp1, two) // 7k+2
			tmp1.Mul(q, tmp1)   // q*(7k+2)
			tmp2.Mul(r, l)      // r*l
			tmp1.Add(tmp1, tmp2) // q*(7k+2)+r*l
			tmp2.Mul(t, l)      // t*l
			nr.Quo(tmp1, tmp2)  // new n
			// new r = (2q+r)*l
			tmp1.Mul(two, q)
			tmp1.Add(tmp1, r)
			tmp1.Mul(tmp1, l)
			// new q = q*k ; new t = t*l ; new k = k+1 ; new l = l+2
			q.Mul(q, k)
			t.Mul(t, l)
			r.Set(tmp1)
			k.Add(k, big.NewInt(1))
			l.Add(l, two)
			n.Set(nr)
		}
	}

	// pad a short final line (N=5000 is a multiple of 10, so this is a no-op,
	// but kept so the impl is correct for any N).
	if col > 0 {
		for col < 10 {
			fmt.Fprint(w, " ")
			col++
		}
		fmt.Fprintf(w, "\t:%d\n", digits)
	}
}
