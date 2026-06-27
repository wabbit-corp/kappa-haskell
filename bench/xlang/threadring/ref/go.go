// xlang/threadring reference — Go. Idiomatic goroutines + unbuffered channels.
// N = 503 ring nodes, HOPS = 1000000 (both HARDCODED; must match every impl).
//
// CLBG / Savina thread-ring: 503 goroutines form a ring connected by blocking
// channels; a token carrying a hop count is passed around the ring, decremented
// one per hop. The goroutine that receives the token when it reaches 0 prints
// its 1-based id. Winner = (HOPS mod N) + 1 = (1000000 mod 503) + 1 = 37.
//
// Methodology: idiomatic blocking channels, one goroutine per ring node — NOT
// the hyper-tuned CLBG entry. Built with `go build` (Go's default optimizer).
package main

import "fmt"

const (
	N    = 503     // ring size
	HOPS = 1000000 // initial token value
)

func main() {
	// chans[i] feeds ring node i (0-based internally; ids reported 1-based).
	chans := make([]chan int, N)
	for i := range chans {
		chans[i] = make(chan int)
	}
	done := make(chan int, 1)

	for i := 0; i < N; i++ {
		go func(id int, in <-chan int, out chan<- int) {
			for {
				n := <-in
				if n <= 0 {
					done <- id + 1 // report 1-based id
					return
				}
				out <- n - 1
			}
		}(i, chans[i], chans[(i+1)%N])
	}

	chans[0] <- HOPS // inject the token at ring node 1
	fmt.Println(<-done)
}
