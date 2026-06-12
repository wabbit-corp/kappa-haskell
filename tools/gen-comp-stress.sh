#!/usr/bin/env bash
# Generate a comprehension-pipeline stress file: N comprehensions, each
# running the full clause pipeline (for/let/if/order by/distinct/take/yield).
set -euo pipefail
n="${1:-200}"
out="${2:-/tmp/comp-stress.kp}"
{
  echo "-- comprehension pipeline stress: $n full-pipeline comprehensions"
  echo "xs0 : List Int"
  echo "let xs0 = [5, 3, 9, 1, 7, 3, 8, 2, 6, 4]"
  for ((i = 0; i < n; i++)); do
    echo "q$i : List Int"
    echo "let q$i ="
    echo "    ["
    echo "        for x in xs0"
    echo "        let y = x + $((i % 50))"
    echo "        if 0 < y"
    echo "        order by y"
    echo "        distinct"
    echo "        take 8"
    echo "        yield y * 2"
    echo "    ]"
  done
} >"$out"
echo "$out"
