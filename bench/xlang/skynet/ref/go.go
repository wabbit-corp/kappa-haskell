// xlang/skynet reference — Go (goroutines + channels). N HARDCODED = 1000000.
//
// Classic skynet: a root spawns 10 children, each spawns 10, ... down to
// 1_000_000 leaf goroutines, each returning its ordinal; the sums fold back up
// the tree. Total = sum 0..999999 = 499999500000.
//
// Methodology: idiomatic-but-fair — one goroutine per node, results collected
// over a buffered channel (the canonical Go skynet shape from the benchmark
// folklore). NOT hyper-tuned (no worker pools, no sync.WaitGroup micro-opts);
// -O is whatever `go build` gives. This is the goroutine headline to compare
// against Kappa fork/await and GHC forkIO.
package main

import "fmt"

func skynet(num, size, div int) int {
	if size == 1 {
		return num
	}
	ch := make(chan int, div)
	step := size / div
	for i := 0; i < div; i++ {
		go func(subNum int) {
			ch <- skynet(subNum, step, div)
		}(num + i*step)
	}
	sum := 0
	for i := 0; i < div; i++ {
		sum += <-ch
	}
	return sum
}

func main() {
	// N = 1000000 leaf fibers (size), branching factor 10.
	fmt.Println(skynet(0, 1000000, 10))
}
