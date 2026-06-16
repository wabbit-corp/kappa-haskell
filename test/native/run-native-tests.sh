#!/usr/bin/env bash
# Native-backend test suite.  For each case program it builds a native
# executable and checks its stdout against the interpreter's (`kappa run`),
# then checks the honest-unsupported path, a bounded performance smoke, and
# the HTTP+sqlite demo.  Bounded by timeouts throughout.
#
# Requires a C driver: set $KAPPA_CC (e.g. "zig cc") or have zig/cc/gcc/
# clang on PATH.  If none is found the suite SKIPS with a clear message and
# exits 0 (so it is safe to run in a minimal environment).
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
CASES="$ROOT/test/native/cases"
WORK="${TMPDIR:-/tmp}/kappa-native-test"
KAPPA="cabal run -v0 kappa --"
fails=0

cd "$ROOT"

# ── C driver detection (mirror the build driver's order) ──────────────
have_driver() {
  [ -n "${KAPPA_CC:-}" ] && return 0
  for c in zig cc gcc clang; do command -v "$c" >/dev/null 2>&1 && return 0; done
  return 1
}
if ! have_driver; then
  echo "SKIP: no C driver found (set \$KAPPA_CC or install zig/cc/gcc/clang)."
  echo "      The native backend test suite needs a C toolchain; skipping."
  exit 0
fi

rm -rf "$WORK"; mkdir -p "$WORK"
echo "== building the kappa CLI =="
timeout 600 cabal build -v0 exe:kappa || { echo "FAIL: cabal build"; exit 1; }

run_diff_case() {
  local name="$1"; local src="$CASES/$name.kp"
  echo "-- case: $name (native output must match the interpreter)"
  local interp native exe
  interp="$(timeout 120 $KAPPA run "$src" 2>/dev/null)"
  exe="$WORK/$name"
  if ! timeout 240 $KAPPA build "$src" -o "$exe" >"$WORK/$name.build.log" 2>&1; then
    echo "   FAIL: native build failed"; cat "$WORK/$name.build.log" | sed 's/^/     /'; fails=$((fails+1)); return
  fi
  native="$(timeout 120 "$exe" 2>/dev/null)"
  if [ "$interp" = "$native" ]; then
    echo "   ok ($(printf '%s' "$native" | tr '\n' '|'))"
  else
    echo "   FAIL: output mismatch"
    echo "     interpreter: $(printf '%s' "$interp" | tr '\n' '|')"
    echo "     native:      $(printf '%s' "$native" | tr '\n' '|')"
    fails=$((fails+1))
  fi
}

echo "== output-equivalence cases =="
for c in arith data control strings loops records unicode; do run_diff_case "$c"; done

echo "== honest-unsupported case =="
exe="$WORK/unsupported"
if timeout 120 $KAPPA build "$CASES/unsupported.kp" -o "$exe" >"$WORK/unsupported.log" 2>&1; then
  echo "   FAIL: build of unsupported.kp succeeded (should have been rejected)"; fails=$((fails+1))
elif grep -q "E_BACKEND_UNSUPPORTED" "$WORK/unsupported.log" && [ ! -f "$exe" ]; then
  echo "   ok (rejected with E_BACKEND_UNSUPPORTED, no executable emitted)"
else
  echo "   FAIL: did not reject with E_BACKEND_UNSUPPORTED / left an executable"
  cat "$WORK/unsupported.log" | sed 's/^/     /'; fails=$((fails+1))
fi

echo "== tail-call stress (deep tail recursion, default ~8MB C stack) =="
exe="$WORK/tailrec"
if timeout 240 $KAPPA build "$CASES/tailrec.kp" -o "$exe" >"$WORK/tailrec.build.log" 2>&1; then
  # run with the default stack: without tail-call elimination this depth
  # (millions) overflows the C stack and crashes.
  out="$( (ulimit -s 8192; timeout 60 "$exe" 2>/dev/null) | tr '\n' '|')"
  rc=$?
  if [ "$rc" -ne 0 ]; then
    echo "   FAIL: tail-recursive run crashed/timed out (rc=$rc) — stack not bounded"; fails=$((fails+1))
  elif [ "$out" = "2000001000000|7|" ]; then
    echo "   ok (2,000,000- and 3,000,000-deep tail recursion in constant stack)"
  else
    echo "   FAIL: wrong result: $out"; fails=$((fails+1))
  fi
else
  echo "   FAIL: tailrec build failed"; fails=$((fails+1))
fi

echo "== performance smoke (sum 1..1_000_000, bounded) =="
exe="$WORK/perf"
if timeout 240 $KAPPA build "$CASES/perf.kp" -o "$exe" >"$WORK/perf.build.log" 2>&1; then
  start=$(date +%s.%N 2>/dev/null || date +%s)
  out="$(timeout 30 "$exe" 2>/dev/null)"
  rc=$?
  end=$(date +%s.%N 2>/dev/null || date +%s)
  if [ "$rc" -ne 0 ]; then
    echo "   FAIL: perf run timed out or errored (rc=$rc)"; fails=$((fails+1))
  elif [ "$out" = "500000500000" ]; then
    echo "   ok (result $out in $(awk "BEGIN{printf \"%.2f\", $end-$start}")s)"
  else
    echo "   FAIL: wrong result: $out"; fails=$((fails+1))
  fi
else
  echo "   FAIL: perf build failed"; fails=$((fails+1))
fi

echo "== HTTP + sqlite demo =="
if command -v sqlite3 >/dev/null 2>&1 || ldconfig -p 2>/dev/null | grep -q sqlite3; then
  if timeout 320 bash "$ROOT/examples/native/http_sqlite/run.sh" >"$WORK/demo.log" 2>&1 && grep -q "DEMO OK" "$WORK/demo.log"; then
    echo "   ok (request -> sqlite write+read -> response; see $WORK/demo.log)"
  else
    echo "   FAIL: demo did not report DEMO OK"; tail -20 "$WORK/demo.log" | sed 's/^/     /'; fails=$((fails+1))
  fi
else
  echo "   SKIP: sqlite3 not available for the demo"
fi

echo ""
if [ "$fails" -eq 0 ]; then echo "ALL NATIVE TESTS PASSED"; else echo "$fails NATIVE TEST(S) FAILED"; exit 1; fi
