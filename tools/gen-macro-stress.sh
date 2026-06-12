#!/usr/bin/env bash
# Generate a macro-expansion stress file: N quote/splice macro expansions.
set -euo pipefail
n="${1:-300}"
out="${2:-/tmp/macro-stress.kp}"
{
  echo "-- macro-expansion stress: $n splice sites, each grafting a quote"
  echo "mkAdd : Syntax Integer -> Syntax Integer -> Elab (Syntax Integer)"
  echo "let mkAdd a b = pure '{ addInt \${a} \${b} }"
  for ((i = 0; i < n; i++)); do
    echo "g$i : Integer"
    echo "let g$i = \$( mkAdd '{ $i } '{ $((i + 1)) } )"
  done
} >"$out"
echo "$out"
