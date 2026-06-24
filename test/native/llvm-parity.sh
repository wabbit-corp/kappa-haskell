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
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

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
fi

pass=0; fail=0
for kp in "${CORPUS[@]}"; do
  name=$(basename "$kp" .kp)
  cbin="$TMP/${name}_c"; lbin="$TMP/${name}_llvm"

  interp_out=$(timeout 30 $KAPPA run "$kp" 2>/dev/null); interp_rc=$?

  if ! $KAPPA build "$kp" -o "$cbin" >/dev/null 2>"$TMP/cbuild.err"; then
    echo "[FAIL] $name — C backend build error"; sed 's/^/    /' "$TMP/cbuild.err" | head -5; fail=$((fail+1)); continue
  fi
  c_out=$(timeout 30 "$cbin" 2>/dev/null); c_rc=$?

  if ! KAPPA_BACKEND=llvm $KAPPA build "$kp" -o "$lbin" >/dev/null 2>"$TMP/lbuild.err"; then
    echo "[FAIL] $name — LLVM backend build error"; sed 's/^/    /' "$TMP/lbuild.err" | head -8; fail=$((fail+1)); continue
  fi
  l_out=$(timeout 30 "$lbin" 2>/dev/null); l_rc=$?

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

echo "---"
echo "LLVM parity: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
