// xlang/pingpong reference — Go. Savina Ping-Pong: two goroutines exchange N
// messages over unbuffered channels; print the count of completed round-trips.
//
// Idiomatic-but-fair: a plain pair of unbuffered channels (synchronous
// rendezvous, one goroutine per role) — the canonical Go ping-pong shape, not
// hyper-tuned. N is HARDCODED = 1000000 to match every impl + expected.txt.
package main

import "fmt"

// N = 1000000
const N = 1000000

func main() {
	ping := make(chan int) // ping -> pong
	pong := make(chan int) // pong -> ping
	done := make(chan int)

	// pong goroutine: receive a ping, send a pong, N times.
	go func() {
		count := 0
		for i := 0; i < N; i++ {
			<-ping
			pong <- 1
			count++
		}
		done <- count
	}()

	// ping role (main goroutine): send a ping, await the pong, N times.
	for i := 0; i < N; i++ {
		ping <- 1
		<-pong
	}
	count := <-done
	fmt.Println(count)
}
