#!/usr/bin/env bash
# Native backend performance benchmarks + allocation gates (QW4).
#
# Each bench is built natively and run with $KAPPA_GC_STATS=1, which makes the
# runtime print `[kappa-gc] total_bytes=… heap_size=… collections=…` at exit.
# We check:
#   * the printed RESULT matches the expected value (a correctness gate — the
#     optimized fast paths must compute the right answer), and
#   * the steady-state HEAP stays under a bound for the non-retaining benches
#     (an allocation gate: QW2 keeps a self-tail loop's parameter env out of
#     the heap, so heap_size must stay tiny even as total_bytes grows with
#     kint result boxing — a regression that reintroduced per-iteration env
#     growth would blow this bound).
#
# These benches deliberately exercise the optimized paths (QW1 direct int
# prims, QW2 in-place self-tail loops, constructor/match, record projection),
# so they are not dead code.  Deep tail-recursive benches run natively in
# constant stack; the interpreter trips its §32.1 recursion-depth guard on
# them, so an interpreter comparison is opt-in (--vs-interp) and best-effort.
#
# Usage: test/native/bench.sh [--vs-interp]
set -u

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BENCH="$ROOT/test/native/bench"
BWORK="/tmp/kappa-bench"
KAPPA="cabal run -v0 kappa --"
VS_INTERP=0
[ "${1:-}" = "--vs-interp" ] && VS_INTERP=1

cd "$ROOT"

have_driver() {
  [ -n "${KAPPA_CC:-}" ] && return 0
  for c in zig cc gcc clang; do command -v "$c" >/dev/null 2>&1 && return 0; done
  return 1
}
if ! have_driver; then echo "SKIP: no C driver (set \$KAPPA_CC or install zig/cc/gcc/clang)."; exit 0; fi

rm -rf "$BWORK"; mkdir -p "$BWORK"
echo "== building the kappa CLI =="
timeout 600 cabal build -v0 exe:kappa || { echo "FAIL: cabal build"; exit 1; }

# The allocation gate is on TOTAL_BYTES (cumulative allocation), not
# heap_size: Boehm's GC_get_heap_size() is the steady-state live footprint and
# is structurally insensitive to per-iteration churn that is collected each
# cycle — a reintroduced per-iteration KEnv rebuild moves total_bytes +65% but
# leaves heap_size byte-identical, so a heap gate would miss exactly the QW2
# regression it claims to catch.  total_bytes is deterministic across runs.
# Bounds are ~1.3-1.45x the current baseline: tight enough to catch a major
# (>=30%) per-iteration-allocation regression, loose enough not to flake.
#
# bench  expected-result  total_bytes-bound (0 = no allocation gate)
BENCHES=(
  "arithloop 2000001000000 380000000"
  "tailsum   2000001000000 260000000"
  "recproj   7000000        140000000"
  "listfold  500000500000   620000000"
)

fails=0
printf "%-10s | %-16s | %8s | %12s | %12s | %10s | %s\n" "bench" "result" "native" "total_bytes" "bound" "heap" "interp"
printf -- "-----------+------------------+----------+--------------+--------------+------------+--------\n"
for entry in "${BENCHES[@]}"; do
  set -- $entry; name="$1"; expect="$2"; totalbound="$3"
  src="$BENCH/$name.kp"; exe="$BWORK/$name"
  if ! timeout 240 $KAPPA build "$src" -o "$exe" >"$BWORK/$name.build.log" 2>&1; then
    echo "FAIL $name: native build failed"; sed 's/^/   /' "$BWORK/$name.build.log"; fails=$((fails+1)); continue
  fi
  ns=$(date +%s.%N)
  out="$(KAPPA_GC_STATS=1 timeout 120 "$exe" 2>"$BWORK/$name.gc")"; rc=$?
  ne=$(date +%s.%N)
  ntime=$(awk "BEGIN{printf \"%.2f\", $ne-$ns}")
  total=$(grep -oE 'total_bytes=[0-9]+' "$BWORK/$name.gc" | head -1 | cut -d= -f2)
  heap=$(grep -oE 'heap_size=[0-9]+' "$BWORK/$name.gc" | head -1 | cut -d= -f2)
  icol="(skipped)"
  if [ "$VS_INTERP" = 1 ]; then
    is=$(date +%s.%N); iout="$(timeout 120 $KAPPA run "$src" 2>/dev/null)"; irc=$?; ie=$(date +%s.%N)
    if [ "$irc" = 0 ]; then icol="$(awk "BEGIN{printf \"%.2fs\", $ie-$is}")"; else icol="n/a(depth/timeout)"; fi
  fi
  printf "%-10s | %-16s | %7ss | %12s | %12s | %10s | %s\n" "$name" "$out" "$ntime" "${total:-?}" "$totalbound" "${heap:-?}" "$icol"
  if [ "$rc" != 0 ]; then echo "   FAIL $name: native rc=$rc"; fails=$((fails+1)); continue; fi
  if [ "$out" != "$expect" ]; then echo "   FAIL $name: result $out != expected $expect"; fails=$((fails+1)); fi
  if [ "$totalbound" != 0 ] && [ -n "$total" ] && [ "$total" -gt "$totalbound" ]; then
    echo "   FAIL $name: total_bytes $total exceeds bound $totalbound (per-iteration allocation regression — e.g. reintroduced KEnv rebuild?)"; fails=$((fails+1))
  fi
done

echo ""
if [ "$fails" -eq 0 ]; then echo "ALL BENCHMARKS PASSED (results + allocation gates)"; else echo "$fails BENCHMARK GATE(S) FAILED"; exit 1; fi
