// xlang/sumloop reference — Go. N HARDCODED = 10000000.
package main

import "fmt"

func main() {
	var acc int64 = 0
	for i := int64(0); i <= 10000000; i++ {
		acc += i
	}
	fmt.Println(acc)
}
