#!/usr/bin/env bash
# Runner for the proposed native-backend benchmarks (docs/KAPPA_NATIVE_BENCHMARK_DESIGN.md,
# docs/NATIVE_BACKEND_OPTIMIZATION_GUIDE.md §8 / roadmap R0.1).
#
# For each `proposed/<b>.kp` it builds the native binary at -O2, runs it R times
# with $KAPPA_GC_STATS=1, and reports the MEDIAN wall time plus the cumulative
# allocation (`total_bytes`, `collections`) and per-iteration allocation
# (`total_bytes / N`).  Where a like-for-like `proposed/raw/<b>.c` baseline
# exists, it builds+runs that at -O2 too and reports the native/raw-C time RATIO.
#
# This is REPORT-ONLY by default (the guide's gate philosophy §4: convert a
# report to a ratio/alloc gate only once the matching roadmap item lands and a
# fair baseline exists — e.g. an `adtbuild` alloc/iter gate after R1.1).  With
# `--gate` it enforces the few gates that ARE currently fair (see GATES below).
#
# Methodology realized (design §2): -O2 native + raw-C; result printed so the C
# compiler cannot fold the loop away (the raw baselines use a volatile sink);
# R invocations with the median reported; allocation counted separately from
# time; per-iteration allocation surfaced.  DEFERRED (tracked, design §2):
# confidence intervals, setup/link-order randomization, the REBUILD knob, CPU
# pinning — add when promoting a bench to a cited near-C claim.
#
# Usage: test/native/bench/proposed/run-proposed.sh [--gate] [--reps N] [bench ...]
set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../../../.." && pwd)"  # test/native/bench/proposed -> repo root
RAW="$HERE/raw"
WORK="${TMPDIR:-/tmp}/kappa-bench-proposed"
REPS=5
GATE=0
SEL=()
while [ $# -gt 0 ]; do
  case "$1" in
    --gate) GATE=1 ;;
    --reps) shift; REPS="$1" ;;
    *) SEL+=("$1") ;;
  esac
  shift
done

cd "$ROOT"

have_driver() {
  [ -n "${KAPPA_CC:-}" ] && return 0
  for c in zig cc gcc clang; do command -v "$c" >/dev/null 2>&1 && return 0; done
  return 1
}
if ! have_driver; then
  echo "SKIP: no C driver (set \$KAPPA_CC or install zig/cc/gcc/clang)."; exit 0
fi
RAWCC="${KAPPA_CC:-cc} -O2"

rm -rf "$WORK"; mkdir -p "$WORK"
echo "== building the kappa CLI =="
timeout 600 cabal build -v0 exe:kappa >/dev/null 2>&1
BIN="$(cabal list-bin kappa 2>/dev/null)"
if [ -z "$BIN" ] || [ ! -x "$BIN" ]; then
  # cabal target resolution is occasionally flaky; fall back to the conventional path.
  BIN="$(find "$ROOT/dist-newstyle" -type f -path '*/x/kappa/build/kappa/kappa' 2>/dev/null | head -1)"
fi
if [ -z "$BIN" ] || [ ! -x "$BIN" ]; then echo "FAIL: cannot locate the kappa binary"; exit 1; fi

# Per-bench iteration count N (for per-iteration allocation) and the value the
# bench must print (a correctness check — an optimized path that computes the
# wrong answer is a miscompile, not a speedup).  N matches the `.kp` source and
# the raw-C baseline's default N.  Benches absent here are run report-only with
# no N/expected check.
declare -A BN BEXP
BN[scalar_intloop]=10000000;   BEXP[scalar_intloop]=50000005000000
BN[scalar_doubleloop]=10000000
BN[adtbuild]=2000000;          BEXP[adtbuild]=2000001000000
BN[adtmatch]=500000;           BEXP[adtmatch]=500000
BN[byteloop]=1000000;          BEXP[byteloop]=1000000

# median of stdin numbers
median() { sort -n | awk '{a[NR]=$1} END{ if(NR==0){print 0} else if(NR%2){print a[(NR+1)/2]} else {print (a[NR/2]+a[NR/2+1])/2} }'; }

elapsed() { # run "$@", echo elapsed seconds
  local s e; s=$(date +%s.%N 2>/dev/null || date +%s)
  "$@" >/dev/null 2>&1
  e=$(date +%s.%N 2>/dev/null || date +%s)
  awk "BEGIN{printf \"%.4f\\n\", $e-$s}"
}

fails=0
printf "%-18s %12s %14s %12s %12s %10s  %s\n" bench "native(s)" "total_bytes" "alloc/iter" "rawC(s)" "ratio" "result"

BENCHES=()
if [ "${#SEL[@]}" -gt 0 ]; then BENCHES=("${SEL[@]}"); else
  for f in "$HERE"/*.kp; do BENCHES+=("$(basename "$f" .kp)"); done
fi

for b in "${BENCHES[@]}"; do
  src="$HERE/$b.kp"; exe="$WORK/$b"
  [ -f "$src" ] || { echo "  $b: no such bench"; continue; }
  if ! timeout 240 "$BIN" build "$src" -o "$exe" >"$WORK/$b.build.log" 2>&1; then
    printf "%-18s %12s\n" "$b" "BUILD-FAIL"; sed 's/^/    /' "$WORK/$b.build.log" | head -4; fails=$((fails+1)); continue
  fi
  # one stats run for total_bytes/result, REPS timing runs for the median
  stats="$(KAPPA_GC_STATS=1 "$exe" 2>&1)"
  result="$(printf '%s\n' "$stats" | grep -v '^\[kappa-gc\]' | head -1)"
  tb="$(printf '%s\n' "$stats" | sed -n 's/.*total_bytes=\([0-9]*\).*/\1/p')"
  for _ in $(seq 1 "$REPS"); do elapsed "$exe"; done | median > "$WORK/$b.nt"
  nt="$(cat "$WORK/$b.nt")"
  n="${BN[$b]:-}"; api="-"; [ -n "$n" ] && [ -n "$tb" ] && api="$(awk "BEGIN{printf \"%.1f\", $tb/$n}")"
  # raw-C baseline + ratio, if present
  rct="-"; ratio="-"
  if [ -f "$RAW/$b.c" ]; then
    if $RAWCC "$RAW/$b.c" -o "$WORK/${b}_c" >"$WORK/$b.cc.log" 2>&1; then
      for _ in $(seq 1 "$REPS"); do elapsed "$WORK/${b}_c" "${n:-}"; done | median > "$WORK/$b.rt"
      rct="$(cat "$WORK/$b.rt")"
      ratio="$(awk "BEGIN{ if($rct>0) printf \"%.1fx\", $nt/$rct; else printf \"n/a\" }")"
    fi
  fi
  # correctness check
  exp="${BEXP[$b]:-}"
  ok="ok"
  if [ -n "$exp" ] && [ "$result" != "$exp" ]; then ok="WRONG(exp $exp)"; fails=$((fails+1)); fi
  printf "%-18s %12s %14s %12s %12s %10s  %s\n" "$b" "$nt" "${tb:-?}" "$api" "$rct" "$ratio" "$result=$ok"
done

# ── currently-fair gates (only what is achievable today; design §4) ──────
if [ "$GATE" -eq 1 ]; then
  echo ""; echo "== gates (currently-fair only) =="
  # scalar_intloop: LR1/P0.2 must keep this an alloc-free unboxed loop.
  tb="$(KAPPA_GC_STATS=1 "$WORK/scalar_intloop" 2>&1 | sed -n 's/.*total_bytes=\([0-9]*\).*/\1/p')"
  if [ -n "$tb" ] && [ "$tb" -le 100000 ]; then
    echo "   ok scalar_intloop alloc ${tb}B <= 100KB (LR1/P0.2 unboxed loop)"
  else
    echo "   FAIL scalar_intloop alloc ${tb:-?}B > 100KB — the Int scalar loop regressed to boxing"; fails=$((fails+1))
  fi
  # adtbuild (R1.1 LANDED): saturated-ctor applications lower to a direct kctor,
  # so construction is bounded to the data representation (≈1 cons KValue + its
  # arg array + 1 kint box ≈ 240 B/iter), NOT the ~540 B/iter eta-ctor closure
  # storm.  Gate alloc/iter <= 300 B (catches a regression back to the storm).
  if [ -x "$WORK/adtbuild" ]; then
    tb="$(KAPPA_GC_STATS=1 "$WORK/adtbuild" 2>&1 | sed -n 's/.*total_bytes=\([0-9]*\).*/\1/p')"
    n="${BN[adtbuild]}"
    api="$(awk "BEGIN{ if($n>0) printf \"%.0f\", ${tb:-0}/$n; else print 0 }")"
    if [ -n "$tb" ] && [ "$api" -le 300 ]; then
      echo "   ok adtbuild alloc/iter ${api}B <= 300B (R1.1 direct ctor; no eta-ctor closure storm)"
    else
      echo "   FAIL adtbuild alloc/iter ${api:-?}B > 300B — saturated-ctor closure storm regressed (R1.1/P0-A)"; fails=$((fails+1))
    fi
  fi
  # scalar_doubleloop (R2.2 LANDED): a monomorphic Double loop lowers to an
  # unboxed `double` worker, so it allocates ~nothing per iteration (no kdbl
  # box).  Gate total alloc <= 100KB (mirrors scalar_intloop's LR1/P0.2 gate).
  if [ -x "$WORK/scalar_doubleloop" ]; then
    tb="$(KAPPA_GC_STATS=1 "$WORK/scalar_doubleloop" 2>&1 | sed -n 's/.*total_bytes=\([0-9]*\).*/\1/p')"
    if [ -n "$tb" ] && [ "$tb" -le 100000 ]; then
      echo "   ok scalar_doubleloop alloc ${tb}B <= 100KB (R2.2 unboxed double worker)"
    else
      echo "   FAIL scalar_doubleloop alloc ${tb:-?}B > 100KB — the Double scalar loop regressed to kdbl boxing"; fails=$((fails+1))
    fi
  fi
fi

echo ""
if [ "$fails" -eq 0 ]; then echo "PROPOSED BENCHES OK (report-only unless --gate)"; else echo "$fails PROPOSED BENCH ISSUE(S)"; [ "$GATE" -eq 1 ] && exit 1; fi
