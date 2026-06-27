// xlang/binarytrees reference — Go. N = depth = 18 HARDCODED.
//
// Binary-trees (CLBG-style): allocate + traverse many binary trees up to a
// given depth and print the check sums. The canonical allocation / GC-pressure
// microbenchmark.
//
// METHODOLOGY: idiomatic-but-fair, NOT the hyper-tuned CLBG entry. One heap
// node per tree node (the Go GC reclaims them); no arena/pool, no goroutines.
// This mirrors how an idiomatic Go program would build a recursive tree, and is
// the fair cross-language counterpart to the Kappa/Haskell/C ports.
//
// Single-line output (compute, not I/O):
//   stretch <s> trees <t> longlived <l>
package main

import "fmt"

// depth = 18 HARDCODED (N)
const minDepth = 4
const maxDepth = 18

type node struct {
	left  *node
	right *node
}

func bottomUpTree(depth int) *node {
	n := &node{}
	if depth > 0 {
		n.left = bottomUpTree(depth - 1)
		n.right = bottomUpTree(depth - 1)
	}
	return n
}

func itemCheck(n *node) int64 {
	if n.left == nil {
		return 1
	}
	return 1 + itemCheck(n.left) + itemCheck(n.right)
}

func main() {
	stretchDepth := maxDepth + 1

	stretch := bottomUpTree(stretchDepth)
	stretchCheck := itemCheck(stretch)

	longLived := bottomUpTree(maxDepth)

	var treesTotal int64 = 0
	for depth := minDepth; depth <= maxDepth; depth += 2 {
		iterations := int64(1) << uint(maxDepth-depth+minDepth)
		var check int64 = 0
		for i := int64(0); i < iterations; i++ {
			t := bottomUpTree(depth)
			check += itemCheck(t)
		}
		treesTotal += check
	}

	longLivedCheck := itemCheck(longLived)

	fmt.Printf("stretch %d trees %d longlived %d\n",
		stretchCheck, treesTotal, longLivedCheck)
}
