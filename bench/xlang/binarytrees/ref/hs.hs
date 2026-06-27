-- xlang/binarytrees reference — GHC (-O2). N = depth = 18 HARDCODED.
--
-- Binary-trees (CLBG-style): allocate + traverse many binary trees up to a
-- given depth and print the check sums. The canonical allocation / GC-pressure
-- microbenchmark.
--
-- METHODOLOGY: idiomatic-but-fair, NOT the hyper-tuned CLBG entry. A plain
-- recursive algebraic data type (Nil | Node left right); every node is a heap
-- allocation managed by the GHC GC. No unboxing tricks, no strictness pragmas
-- beyond a strict accumulator fold, no parallelism. This mirrors how an
-- idiomatic Haskell program builds a recursive tree and is the fair
-- cross-language counterpart to the Kappa/Go/C ports.
--
-- Single-line output (compute, not I/O):
--   stretch <s> trees <t> longlived <l>
module Main where

import Data.List (foldl')

-- depth = 18 HARDCODED (N)
minDepth, maxDepth :: Int
minDepth = 4
maxDepth = 18

data Tree = Nil | Node Tree Tree

bottomUpTree :: Int -> Tree
bottomUpTree 0 = Node Nil Nil
bottomUpTree d = Node (bottomUpTree (d - 1)) (bottomUpTree (d - 1))

itemCheck :: Tree -> Int
itemCheck Nil = 0
itemCheck (Node Nil _) = 1
itemCheck (Node l r) = 1 + itemCheck l + itemCheck r

main :: IO ()
main = do
  let stretchDepth = maxDepth + 1
      stretchCheck = itemCheck (bottomUpTree stretchDepth)
      longLived = bottomUpTree maxDepth
      depthCheck depth =
        let iterations = (1 `shiftLeftInt` (maxDepth - depth + minDepth)) :: Int
        in foldl' (\acc _ -> acc + itemCheck (bottomUpTree depth)) 0 [1 .. iterations]
      treesTotal = foldl' (\acc d -> acc + depthCheck d) 0 [minDepth, minDepth + 2 .. maxDepth]
      longLivedCheck = itemCheck longLived
  putStrLn $
    "stretch " ++ show stretchCheck
      ++ " trees " ++ show treesTotal
      ++ " longlived " ++ show longLivedCheck
  where
    shiftLeftInt b s = b * (2 ^ s)
