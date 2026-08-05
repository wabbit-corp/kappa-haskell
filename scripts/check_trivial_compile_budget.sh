#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
kappa=$(cd "$root" && cabal list-bin exe:kappa)
fixture=$(mktemp "${TMPDIR:-/tmp}/kappa-trivial.XXXXXX.kp")
trap 'rm -f "$fixture"' EXIT

printf 'module bench\nlet answer = 42\n' >"$fixture"

start=$(python3 -c 'import time; print(time.monotonic_ns())')
"$kappa" check "$fixture" >/dev/null
end=$(python3 -c 'import time; print(time.monotonic_ns())')
elapsed_ms=$(((end - start) / 1000000))

if ((elapsed_ms >= 1000)); then
  printf 'trivial cold compile exceeded 1000ms: %dms\n' "$elapsed_ms" >&2
  exit 1
fi

printf 'trivial cold compile: %dms\n' "$elapsed_ms"
