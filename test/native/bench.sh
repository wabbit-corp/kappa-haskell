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

# P1.1: performance builds use optimized C (-O2).  The C driver for both the
# generated native code and the raw-C baselines.
BENCHCC="${KAPPA_CC:-cc} -O2"
echo "== C driver (performance, -O2): $BENCHCC =="

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
  "arithloop 2000001000000 1000000"
  "tailsum   2000001000000 1000000"
  "recproj   7000000        140000000"
  "listfold  500000500000   620000000"
)
# arithloop's bound is now ~1MB (was 380MB): P0.2 scalarizes its non-escaping
# Int `var` loop to int64 C locals (zero per-iteration allocation); a
# regression back to the boxed kref loop (~145MB) blows this bound.
# tailsum's bound is now ~1MB (was 260MB): LR1 lowers it to a scalar int64
# worker that allocates ~zero per iteration (≈hundreds of bytes total), so a
# regression back to per-iteration kint boxing (~193MB) blows this bound.

fails=0
printf "%-10s | %-16s | %8s | %12s | %12s | %10s | %s\n" "bench" "result" "native" "total_bytes" "bound" "heap" "interp"
printf -- "-----------+------------------+----------+--------------+--------------+------------+--------\n"
for entry in "${BENCHES[@]}"; do
  set -- $entry; name="$1"; expect="$2"; totalbound="$3"
  src="$BENCH/$name.kp"; exe="$BWORK/$name"
  if ! KAPPA_CC="$BENCHCC" timeout 240 $KAPPA build "$src" -o "$exe" >"$BWORK/$name.build.log" 2>&1; then
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
echo "== raw-C ratio gates (P1.2: native -O2 elapsed vs handwritten C -O2) =="
# Large-N loops where the loop dominates startup; the raw-C baseline uses a
# volatile accumulator + runtime N so the C compiler cannot fold it away.
RATIO_N=100000000
# name  kp  raw-c-src  gate(0=report-only,else max native/C ratio)  note
ratio_bench() {
  local name="$1" kp="$2" csrc="$3" gate="$4" note="$5"
  local nexe="$BWORK/r_$name" rexe="$BWORK/c_$name"
  if ! KAPPA_CC="$BENCHCC" timeout 240 $KAPPA build "$kp" -o "$nexe" >"$BWORK/r_$name.log" 2>&1; then
    echo "   FAIL ratio $name: native build"; sed 's/^/     /' "$BWORK/r_$name.log"; fails=$((fails+1)); return; fi
  if ! $BENCHCC "$csrc" -o "$rexe" 2>"$BWORK/c_$name.log"; then
    echo "   FAIL ratio $name: raw-C build"; sed 's/^/     /' "$BWORK/c_$name.log"; fails=$((fails+1)); return; fi
  local ns ne rs re nt rt ratio
  ns=$(date +%s.%N); "$nexe" >/dev/null 2>&1; ne=$(date +%s.%N)
  rs=$(date +%s.%N); "$rexe" "$RATIO_N" >/dev/null 2>&1; re=$(date +%s.%N)
  nt=$(awk "BEGIN{printf \"%.4f\", $ne-$ns}"); rt=$(awk "BEGIN{printf \"%.4f\", $re-$rs}")
  ratio=$(awk "BEGIN{printf \"%.1f\", ($rt>0)?($nt/$rt):0}")
  printf "   %-10s native=%ss  rawC=%ss  ratio=%sx  %s\n" "$name" "$nt" "$rt" "$ratio" "$note"
  if [ "$gate" != 0 ]; then
    if awk "BEGIN{exit !($nt <= $gate*$rt)}"; then :; else
      echo "      FAIL $name: native ${nt}s exceeds ${gate}x raw-C ${rt}s"; fails=$((fails+1)); fi
  fi
}
ratio_bench tailsum   "$BENCH/ratio_tailsum.kp"   "$BENCH/raw/tailsum.c"   5  "(LR1 scalar int64 worker; GATED <=5x raw C)"
ratio_bench arithloop "$BENCH/ratio_arithloop.kp" "$BENCH/raw/arithloop.c" 5  "(P0.2 scalar int64 var loop; GATED <=5x raw C)"

echo ""
if [ "$fails" -eq 0 ]; then echo "ALL BENCHMARKS PASSED (results + allocation gates + raw-C ratio gate)"; else echo "$fails BENCHMARK GATE(S) FAILED"; exit 1; fi
