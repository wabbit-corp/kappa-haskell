-- xlang/sumloop reference — GHC (-O2). N HARDCODED = 10000000.
module Main where

import Data.List (foldl')

main :: IO ()
main = print (foldl' (+) 0 [0 .. 10000000 :: Int])
