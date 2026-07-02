#!/usr/bin/env bash
# Isolated runner for the runtime import batch. It first runs the normal
# Appendix-T harness, then checks C-native output against interpreter output for
# each imported case. This is deliberately not called by the main test suite.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
CASES="$ROOT/tests/runtime-import/cases"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/kappa-runtime-import-tests.XXXXXX")"
KAPPA="cabal run -v0 kappa --"
fails=0

cd "$ROOT"
export KAPPA_BACKEND=c

cleanup() {
  rm -rf "$WORK"
}
trap cleanup EXIT

cleanup_case_artifacts() {
  name="$1"
  rm -f \
    "$CASES/$name.kappa.c" \
    "$CASES/$name.kappa.ll" \
    "$CASES/$name.kappa.hostffi.c" \
    "$CASES/$name.native.prov"
}

if ! command -v timeout >/dev/null 2>&1; then
  timeout() {
    python3 - "$@" <<'PY'
import subprocess, sys
seconds = float(sys.argv[1].removesuffix('s'))
cmd = sys.argv[2:]
try:
    raise SystemExit(subprocess.run(cmd, timeout=seconds).returncode)
except subprocess.TimeoutExpired:
    raise SystemExit(124)
PY
  }
fi

have_driver() {
  [ -n "${KAPPA_CC:-}" ] && return 0
  for c in zig cc gcc clang; do command -v "$c" >/dev/null 2>&1 && return 0; done
  return 1
}

echo "== harness =="
for src in "$CASES"/*.kp; do
  name="$(basename "$src" .kp)"
  echo "-- case: $name"
  if ! timeout 240 $KAPPA test "$src"; then
    echo "   FAIL: harness"
    fails=$((fails+1))
  fi
done

if [ "$fails" -ne 0 ]; then
  echo "runtime import harness failures: $fails"
  exit 1
fi

if ! have_driver; then
  echo "SKIP: no C driver found (set \$KAPPA_CC or install zig/cc/gcc/clang)."
  exit 0
fi

echo "== native parity =="
for src in "$CASES"/*.kp; do
  name="$(basename "$src" .kp)"
  echo "-- case: $name"
  interp_out="$WORK/$name.interp.out"
  interp_err="$WORK/$name.interp.err"
  native_out="$WORK/$name.native.out"
  native_err="$WORK/$name.native.err"
  build_log="$WORK/$name.build.log"

  timeout 120 $KAPPA run "$src" >"$interp_out" 2>"$interp_err"
  irc=$?
  if [ "$irc" -ne 0 ]; then
    echo "   FAIL: interpreter exited with $irc"
    sed 's/^/     /' "$interp_err"
    fails=$((fails+1))
    continue
  fi
  exe="$WORK/$name"
  if ! timeout 240 $KAPPA build "$src" -o "$exe" >"$build_log" 2>&1; then
    echo "   FAIL: native build failed"
    sed 's/^/     /' "$build_log"
    cleanup_case_artifacts "$name"
    fails=$((fails+1))
    continue
  fi
  cleanup_case_artifacts "$name"
  timeout 120 "$exe" >"$native_out" 2>"$native_err"
  nrc=$?
  if [ "$nrc" -ne 0 ]; then
    echo "   FAIL: native executable exited with $nrc"
    sed 's/^/     /' "$native_err"
    fails=$((fails+1))
    continue
  fi
  if cmp -s "$interp_out" "$native_out"; then
    echo "   ok ($(tr '\n' '|' <"$native_out"))"
  else
    echo "   FAIL: output mismatch"
    echo "     interpreter: $(tr '\n' '|' <"$interp_out")"
    echo "     native:      $(tr '\n' '|' <"$native_out")"
    fails=$((fails+1))
  fi
done

if [ "$fails" -ne 0 ]; then
  echo "runtime import failures: $fails"
  exit 1
fi

echo "runtime import tests passed"
