// xlang/forkjoin reference — Go (idiomatic goroutines + WaitGroup).
// Savina Fork-Join: spawn N goroutines, each runs a small modular-integer CPU
// task seeded by its index, accumulates its result into a shared atomic cell;
// the parent joins all and prints the checksum.  N HARDCODED = 100000.
//
// Methodology: idiomatic-but-fair — a plain goroutine per fiber, sync/atomic
// for the lock-free accumulator, sync.WaitGroup to join.  Not hand-tuned (no
// worker-pool batching); mirrors the Kappa port's one-fiber-per-task structure.
package main

import (
	"fmt"
	"sync"
	"sync/atomic"
)

// per-fiber CPU task: modular integer mixing loop, `k` steps, seeded by acc.
// modInt keeps every step within int64 and makes the result order-independent.
func task(acc, k int64) int64 {
	for k > 0 {
		acc = (acc*1000003 + k) % 2147483647
		k--
	}
	return acc
}

func main() {
	const N = 100000 // N HARDCODED = 100000 fibers
	var total int64
	var wg sync.WaitGroup
	wg.Add(N)
	for i := int64(0); i < N; i++ {
		go func(i int64) {
			defer wg.Done()
			v := task(i+1, 200)
			atomic.AddInt64(&total, v)
		}(i)
	}
	wg.Wait()
	fmt.Println(total)
}
