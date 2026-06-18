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
for c in arith data control strings loops records unicode traits variants-susp bignum dokernel showprims bytes ubuilders unidata uhash iorec defernest deferlazy prefixbind letqor letqelse letqmiss projection lr1 varloop recordproj tupleproj ctortags; do run_diff_case "$c"; done

# LR2: the pattern-match dispatch must be a numeric tag-id int compare
# (kctor_tagid / kvariant_tagid), NOT a kctor_is / kvariant_is strcmp.  Assert
# on a constructor/variant-heavy program's generated C.
echo "== LR2: match dispatch uses numeric tag ids, not strcmp =="
ltmp="$WORK/lr2c"; mkdir -p "$ltmp"
if timeout 120 $KAPPA build "$CASES/ctortags.kp" --emit-c -o "$ltmp/ct" >"$ltmp/build.log" 2>&1; then
  cfile="$CASES/ctortags.kappa.c"
  if grep -qE 'kctor_tagid\(' "$cfile" \
     && ! grep -qE 'kctor_is\(|kvariant_is\(' "$cfile"; then
    echo "   ok (matches dispatch on kctor_tagid/kvariant_tagid; no kctor_is/kvariant_is in generated C)"
  else
    echo "   FAIL: generated match path still uses a strcmp dispatch (or no tag id)"
    grep -nE 'kctor_is\(|kvariant_is\(' "$cfile" | sed 's/^/     /'; fails=$((fails+1))
  fi
  rm -f "$cfile"
else
  echo "   FAIL: ctortags --emit-c build failed"; cat "$ltmp/build.log" | sed 's/^/     /'; fails=$((fails+1))
fi

# Honest no-fallback property: the native backend never silently falls back
# to interpreter behaviour.  The full accepted run-mode (UIO) surface now
# compiles (there is no spec-mandated runtime construct left to reject — the
# E_BACKEND_UNSUPPORTED guards remain only for genuinely non-runtime terms,
# §31.2-erased / §30.2.4 elaboration-time, which accepted programs do not
# reach), so the no-fallback property is exercised by the namespace-hygiene
# and foreign-`expect` sections below (a hidden runtime symbol / an
# unsatisfied foreign expectation each yield a precise diagnostic and NO
# executable, never an interpreter fallback).

echo "== tail-call stress (deep tail recursion, default ~8MB C stack) =="
exe="$WORK/tailrec"
if timeout 240 $KAPPA build "$CASES/tailrec.kp" -o "$exe" >"$WORK/tailrec.build.log" 2>&1; then
  # run with the default stack: without tail-call elimination this depth
  # (millions) overflows the C stack and crashes.
  out="$( (ulimit -s 8192; timeout 60 "$exe" 2>/dev/null) | tr '\n' '|')"
  rc=$?
  if [ "$rc" -ne 0 ]; then
    echo "   FAIL: tail-recursive run crashed/timed out (rc=$rc) — stack not bounded"; fails=$((fails+1))
  elif [ "$out" = "2000001000000|7|even|0|" ]; then
    echo "   ok (self-loop + mutual + value-indirect tail recursion in constant stack)"
  else
    echo "   FAIL: wrong result: $out"; fails=$((fails+1))
  fi
else
  echo "   FAIL: tailrec build failed"; fails=$((fails+1))
fi

echo "== namespace hygiene: hidden runtime symbols are not source-visible =="
exe="$WORK/hidden"
if timeout 120 $KAPPA build --ffi-full "$CASES/hidden-symbol.kp" -o "$exe" >"$WORK/hidden.log" 2>&1; then
  echo "   FAIL: a program calling __tcpListen built (hidden symbol leaked)"; fails=$((fails+1))
elif grep -q "E_NAME_UNRESOLVED" "$WORK/hidden.log" && [ ! -f "$exe" ]; then
  echo "   ok (__tcpListen is E_NAME_UNRESOLVED, no executable; FFI prims are not prelude globals)"
else
  echo "   FAIL: __tcpListen not rejected as unresolved / left an executable"
  cat "$WORK/hidden.log" | sed 's/^/     /'; fails=$((fails+1))
fi

echo "== native build refuses an unsatisfied foreign expect without --ffi-full (no silent FFI) =="
exe="$WORK/unsupported"
if timeout 120 $KAPPA build "$CASES/unsupported.kp" -o "$exe" >"$WORK/unsupported.log" 2>&1; then
  echo "   FAIL: a foreign-expect program built without --ffi-full (FFI fabricated)"; fails=$((fails+1))
elif grep -q "E_EXPECT_UNSATISFIED" "$WORK/unsupported.log" && [ ! -f "$exe" ]; then
  echo "   ok (unsatisfied foreign expect -> E_EXPECT_UNSATISFIED, no executable, §9.4)"
else
  echo "   FAIL: foreign expect not rejected as E_EXPECT_UNSATISFIED / left an executable"
  cat "$WORK/unsupported.log" | sed 's/^/     /'; fails=$((fails+1))
fi

echo "== foreign expects fail honestly under the interpreter (no fallback) =="
if timeout 120 $KAPPA run "$ROOT/examples/native/http_sqlite/server.kp" >"$WORK/server-run.log" 2>&1; then
  echo "   FAIL: the FFI demo ran under the interpreter (expects should be unsatisfied)"; fails=$((fails+1))
elif grep -q "E_EXPECT_UNSATISFIED" "$WORK/server-run.log"; then
  echo "   ok (foreign expects unsatisfied -> E_EXPECT_UNSATISFIED, §9.4)"
else
  echo "   FAIL: interpreter did not report E_EXPECT_UNSATISFIED for the foreign demo"
  head -3 "$WORK/server-run.log" | sed 's/^/     /'; fails=$((fails+1))
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

echo "== native benchmarks + allocation gates (bench.sh) =="
# Exercises the optimized fast paths (QW1 direct int prims, QW2 in-place
# self-tail loops, constructor/match, record projection) and gates on correct
# results + a steady-state heap bound (a per-iteration env/data leak would
# blow it).  Not dead code: each bench computes a checked result.
if timeout 300 bash "$ROOT/test/native/bench.sh" >"$WORK/bench.log" 2>&1; then
  echo "   ok ($(grep -cE '^(arithloop|tailsum|recproj|listfold)' "$WORK/bench.log") benches; results + total_bytes allocation gates passed)"
  grep -E '^(arithloop|tailsum|recproj|listfold)' "$WORK/bench.log" | sed 's/^/     /'
else
  echo "   FAIL: benchmark gates failed"; tail -16 "$WORK/bench.log" | sed 's/^/     /'; fails=$((fails+1))
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
