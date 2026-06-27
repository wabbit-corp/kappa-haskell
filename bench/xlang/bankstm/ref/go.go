// xlang/bankstm reference — Go (mutex). Savina Bank-Transaction.
//
// K = 1000 accounts, M = 1000000 concurrent random transfers across W = 4
// goroutines. Each transfer atomically debits one account and credits another
// (a critical section under a single mutex — the idiomatic Go "shared state +
// sync.Mutex" approach, the natural counterpart to GHC/Kappa STM here).
//
// The MOVED amount is conserved: the sum over all accounts is invariant to the
// (random, scheduler-dependent) choice of accounts, so the printed total is the
// deterministic invariant K*INIT regardless of interleaving — which is exactly
// the Savina conservation assertion, and keeps stdout byte-identical across
// every language impl (no PRNG agreement required for the *output*, only for the
// *contention pattern*). N is HARDCODED.
//
// Methodology: idiomatic and -O2-equivalent (go build default), NOT a hand-tuned
// lock-free CLBG entry. One global mutex models the STM commit lock; per-account
// locking would be faster but would not mirror the single-arbiter STM semantics
// the Kappa/Haskell refs use.
package main

import (
	"fmt"
	"sync"
)

const (
	K    = 1000    // accounts            (HARDCODED N: accounts)
	M    = 1000000 // total transfers     (HARDCODED N: transfers)
	W    = 4       // worker goroutines
	INIT = 1000    // starting balance per account
)

// Park-Miller MINSTD LCG; state stays in (0, 2^31-1) so it matches the Kappa
// port's bounded generator (Kappa Int auto-promotes to bignum on overflow).
func lcg(s int64) int64 { return (s * 16807) % 2147483647 }

func main() {
	bal := make([]int64, K)
	for i := range bal {
		bal[i] = INIT
	}
	var mu sync.Mutex
	var wg sync.WaitGroup

	// Per-worker seeds (distinct streams), matching the Kappa port.
	seeds := []int64{1, 1000003, 2000029, 3000071}
	perW := M / W

	for w := 0; w < W; w++ {
		wg.Add(1)
		go func(seed int64) {
			defer wg.Done()
			s := seed
			for n := 0; n < perW; n++ {
				s = lcg(s)
				i := s % K
				s = lcg(s)
				j := s % K
				mu.Lock()
				bal[i]--
				bal[j]++
				mu.Unlock()
			}
		}(seeds[w])
	}
	wg.Wait()

	var total int64 = 0
	for _, v := range bal {
		total += v
	}
	fmt.Println(total)
}
