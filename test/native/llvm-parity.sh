#!/usr/bin/env bash
# LLVM-backend parity harness.
#
# For each .kp program given (or a default M0+ corpus), build it with BOTH native
# backends — the C backend (default) and the LLVM backend (KAPPA_BACKEND=llvm) —
# run each binary, and also run the interpreter (`kappa run`), then diff stdout +
# exit code across all three. The LLVM backend must match the C backend, which is
# itself gated against the interpreter. This is the conformance gate for every
# LLVM milestone (M0 hello, M1b arithmetic, M2 CAFs, M3 ctors/match, …).
#
# Usage:
#   test/native/llvm-parity.sh                 # run the built-in corpus
#   test/native/llvm-parity.sh a.kp b.kp ...   # run specific programs
#
# Env: KAPPA=<cabal run -v0 kappa --> override the compiler invocation.
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2

KAPPA=${KAPPA:-"cabal run -v0 kappa --"}
PARITY_TIMEOUT=${KAPPA_LLVM_PARITY_TIMEOUT:-30}
BUILD_TIMEOUT=${KAPPA_LLVM_PARITY_BUILD_TIMEOUT:-240}

# The C/default leg must not inherit a caller-selected backend. The LLVM leg
# below sets KAPPA_BACKEND explicitly per command.
unset KAPPA_BACKEND

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

if ! command -v timeout >/dev/null 2>&1; then
  timeout() {
    python3 - "$@" <<'PY'
import subprocess, sys
raw = sys.argv[1]
if raw.endswith('s'):
    raw = raw[:-1]
seconds = float(raw)
cmd = sys.argv[2:]
try:
    raise SystemExit(subprocess.run(cmd, timeout=seconds).returncode)
except subprocess.TimeoutExpired:
    raise SystemExit(124)
PY
  }
fi

perceus_rc_enabled() {
  case "${KAPPA_PERCEUS_RC:-}" in
    0|[Oo][Ff][Ff]|[Ff][Aa][Ll][Ss][Ee]|[Nn][Oo]) return 1 ;;
    *) return 0 ;;
  esac
}

check_perceus_rc_log() {
  local log="$1"
  if perceus_rc_enabled; then
    if ! grep -q "perceus-rc: KBackendIR ownership metadata validation complete; 0 finding(s)" "$log"; then
      echo "[FAIL] Perceus RC C-backend build did not report zero KBackendIR ownership metadata findings"
      sed -n '/perceus-rc:/p' "$log" | sed 's/^/    /'
      return 1
    fi
  fi
  return 0
}

cleanup_generated_for_source() {
  local src="$1"
  rm -f "${src%.kp}.kappa.c" "${src%.kp}.kappa.ll"
}

# Built-in corpus grows as milestones land.  With no args, run every program in
# tests/native/llvm/ (M0 hello, M1 arithmetic/show + bigint, M2 cross-CAFs),
# plus an inline hello as a self-contained smoke (so the harness still exercises
# the M0 shape even if the corpus dir is empty/missing).
if [ "$#" -gt 0 ]; then
  CORPUS=("$@")
else
  cat > "$TMP/hello.kp" <<'KP'
module main
main : UIO Unit
let main = printlnString "hello"
KP
  CORPUS=("$TMP/hello.kp")
  for kp in tests/native/llvm/*.kp; do
    [ -e "$kp" ] && CORPUS+=("$kp")
  done
  # §32.2.6: LLVM-supported tight loops must observe safe-point interrupts.
  CORPUS+=("test/native/cases/interrupt-tight-loop.kp")
  CORPUS+=("test/native/cases/adv-boxed-loop-tail.kp")
  CORPUS+=("test/native/cases/adv-loop-tail-effect.kp")
  CORPUS+=("test/native/cases/adv-loop-tail-read.kp")
  # §18.5/§18.6 through the CK machine: suspending loops with break,
  # continue, and return must scope return to the do-block value.
  CORPUS+=("test/native/cases/suspendbreak.kp")
  CORPUS+=("test/native/cases/while-defer-scope.kp")
  # §32.2.6: scalar-worker safe-point aborts must agree with the interpreter,
  # including active release/finalizer scopes.
  CORPUS+=("test/native/cases/scalar-nested-abort.kp")
  CORPUS+=("test/native/cases/scalar-varloop-nested-abort.kp")
  CORPUS+=("test/native/cases/scalar-nested-abort-using.kp")
  CORPUS+=("test/native/cases/scalar-nested-abort-using-defer.kp")
  CORPUS+=("test/native/cases/scalar-nested-abort-defer-before-pure.kp")
  CORPUS+=("test/native/cases/scalar-nested-abort-onexit.kp")
  CORPUS+=("test/native/cases/scalar-nested-abort-cleanup-failure.kp")
  CORPUS+=("test/native/cases/defer-sleep.kp")
  CORPUS+=("test/native/cases/monadref-user-evidence.kp")
  CORPUS+=("test/native/cases/record-erased-field-proj.kp")
fi

pass=0; fail=0
for kp in "${CORPUS[@]}"; do
  name=$(basename "$kp" .kp)
  cbin="$TMP/${name}_c"; lbin="$TMP/${name}_llvm"

  interp_out=$(timeout "$PARITY_TIMEOUT" $KAPPA run "$kp" 2>/dev/null); interp_rc=$?
  if [ "$interp_rc" -eq 124 ]; then
    echo "[FAIL] $name — interpreter timed out after ${PARITY_TIMEOUT}s"
    fail=$((fail+1))
    continue
  fi

  cleanup_generated_for_source "$kp"
  timeout "$BUILD_TIMEOUT" $KAPPA build "$kp" -o "$cbin" >/dev/null 2>"$TMP/cbuild.err"; cbuild_rc=$?
  cleanup_generated_for_source "$kp"
  if [ "$cbuild_rc" -eq 124 ]; then
    echo "[FAIL] $name — C backend build timed out after ${BUILD_TIMEOUT}s"
    fail=$((fail+1))
    continue
  fi
  if [ "$cbuild_rc" -ne 0 ]; then
    echo "[FAIL] $name — C backend build error"; sed 's/^/    /' "$TMP/cbuild.err" | head -5; fail=$((fail+1)); continue
  fi
  if ! check_perceus_rc_log "$TMP/cbuild.err"; then
    fail=$((fail+1)); continue
  fi
  c_out=$(timeout "$PARITY_TIMEOUT" "$cbin" 2>/dev/null); c_rc=$?
  if [ "$c_rc" -eq 124 ]; then
    echo "[FAIL] $name — C binary timed out after ${PARITY_TIMEOUT}s"
    fail=$((fail+1))
    continue
  fi

  cleanup_generated_for_source "$kp"
  KAPPA_BACKEND=llvm timeout "$BUILD_TIMEOUT" $KAPPA build "$kp" -o "$lbin" >/dev/null 2>"$TMP/lbuild.err"; lbuild_rc=$?
  cleanup_generated_for_source "$kp"
  if [ "$lbuild_rc" -eq 124 ]; then
    echo "[FAIL] $name — LLVM backend build timed out after ${BUILD_TIMEOUT}s"
    fail=$((fail+1))
    continue
  fi
  if [ "$lbuild_rc" -ne 0 ]; then
    echo "[FAIL] $name — LLVM backend build error"; sed 's/^/    /' "$TMP/lbuild.err" | head -8; fail=$((fail+1)); continue
  fi
  if ! check_perceus_rc_log "$TMP/lbuild.err"; then
    fail=$((fail+1)); continue
  fi
  l_out=$(timeout "$PARITY_TIMEOUT" "$lbin" 2>/dev/null); l_rc=$?
  if [ "$l_rc" -eq 124 ]; then
    echo "[FAIL] $name — LLVM binary timed out after ${PARITY_TIMEOUT}s"
    fail=$((fail+1))
    continue
  fi

  if [ "$l_out" = "$c_out" ] && [ "$l_rc" = "$c_rc" ] && \
     [ "$c_out" = "$interp_out" ] && [ "$c_rc" = "$interp_rc" ]; then
    echo "[PASS] $name — interp == C == LLVM (rc=$l_rc)"
    pass=$((pass+1))
  else
    echo "[FAIL] $name"
    printf '    interp: rc=%s out=%q\n' "$interp_rc" "$interp_out"
    printf '    C     : rc=%s out=%q\n' "$c_rc" "$c_out"
    printf '    LLVM  : rc=%s out=%q\n' "$l_rc" "$l_out"
    fail=$((fail+1))
  fi
done

echo "== LLVM Perceus RC runtime gate =="
gate_src="${CORPUS[0]}"
gate_ll="${gate_src%.kp}.kappa.ll"
cleanup_generated_for_source "$gate_src"
KAPPA_BACKEND=llvm timeout "$BUILD_TIMEOUT" $KAPPA build "$gate_src" --emit-c -o "$TMP/llvm_rc_gate" >/dev/null 2>"$TMP/llvm-rc-gate.err"; gate_rc=$?
if [ "$gate_rc" -ne 0 ]; then
  echo "[FAIL] LLVM RC gate — emit build failed"
  sed 's/^/    /' "$TMP/llvm-rc-gate.err" | head -8
  fail=$((fail+1))
elif [ ! -f "$gate_ll" ]; then
  echo "[FAIL] LLVM RC gate — emitted .ll file missing"
  fail=$((fail+1))
elif grep -q 'call void @krc_set_enabled(i32 0)' "$gate_ll" \
     && grep -q 'krc_mark_shared_recursive' "$gate_ll" \
     && ! grep -qE 'call .*@kdup|call .*@kdrop' "$gate_ll"; then
  echo "[PASS] LLVM RC gate — counting/freeing disabled; publish marking retained"
else
  echo "[FAIL] LLVM RC gate — expected krc_set_enabled(0), publish marking, and no ownership kdup/kdrop"
  grep -nE 'krc_set_enabled|krc_mark_shared_recursive|kdup|kdrop' "$gate_ll" | sed 's/^/    /' || true
  fail=$((fail+1))
fi
cleanup_generated_for_source "$gate_src"

echo "---"
echo "LLVM parity: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
