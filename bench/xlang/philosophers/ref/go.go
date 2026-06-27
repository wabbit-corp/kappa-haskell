// xlang/philosophers reference — Go. N = 20 philosophers, M = 100000 rounds.
//
// Savina Dining-Philosophers. Go has no STM, so the idiomatic-but-fair
// deadlock-free analogue of Kappa's all-or-nothing STM pickup is ORDERED lock
// acquisition: each fork is a sync.Mutex; a philosopher always locks the
// lower-indexed of its two forks first, which makes the classic circular wait
// impossible. Each philosopher runs M rounds (lock both forks, eat = bump a
// shared atomic counter, unlock both); a WaitGroup joins them. Total meals =
// N*M = 2000000, printed on one line.
//
// Methodology: idiomatic goroutines + sync primitives, `go build` (the Go
// toolchain optimizes by default). Not hand-tuned; mirrors how one would
// actually write this in Go.
package main

import (
	"fmt"
	"sync"
	"sync/atomic"
)

const (
	N = 20     // philosophers (and forks)
	M = 100000 // rounds per philosopher
)

func main() {
	forks := make([]sync.Mutex, N)
	var meals int64
	var wg sync.WaitGroup
	wg.Add(N)
	for i := 0; i < N; i++ {
		go func(i int) {
			defer wg.Done()
			left, right := i, (i+1)%N
			lo, hi := left, right
			if lo > hi {
				lo, hi = hi, lo
			}
			for r := 0; r < M; r++ {
				// Ordered acquisition: lock the lower-indexed fork first.
				forks[lo].Lock()
				forks[hi].Lock()
				atomic.AddInt64(&meals, 1) // eat
				forks[hi].Unlock()
				forks[lo].Unlock()
			}
		}(i)
	}
	wg.Wait()
	fmt.Println(meals)
}
