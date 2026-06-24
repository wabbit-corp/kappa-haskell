// go_pingpong.go — the comparison point for fork/await: spawn a goroutine and
// wait for it, N times.  Reports ns/op and bytes/op (Go runtime TotalAlloc).
package main

import (
	"fmt"
	"runtime"
	"time"
)

func main() {
	const N = 200000
	var m0, m1 runtime.MemStats
	runtime.ReadMemStats(&m0)
	t0 := time.Now()
	for i := 0; i < N; i++ {
		done := make(chan struct{})
		go func() { close(done) }()
		<-done
	}
	d := time.Since(t0)
	runtime.ReadMemStats(&m1)
	fmt.Printf("%-34s %10.1f %12.0f\n", "go goroutine spawn+join",
		float64(d.Nanoseconds())/N, float64(m1.TotalAlloc-m0.TotalAlloc)/N)
}
