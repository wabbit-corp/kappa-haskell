#!/usr/bin/env bash
# Quick loop: run only the given category prefixes (default: this wave's
# targets) and print one PASS/FAIL/UNSUPPORTED/HARNESS-ERROR line each.
set -u
F=/opt/workspaces/kappa/tests/Kappa.Compiler.Tests/Fixtures
BIN="$(cabal list-bin kappa 2>/dev/null)"
PATS="${1:-expressions static_objects traits definitional_equality core_semantics stdlib deriving}"
LOG="${2:-/tmp/targets-raw.log}"
: >"$LOG"
for p in $PATS; do
  for d in "$F"/$p.*/ "$F"/${p}_*/; do
    [ -d "$d" ] || continue
    if ! timeout 30 "$BIN" test --suite "${d%/}" >>"$LOG" 2>&1; then
      tail -3 "$LOG" | grep -qF "${d%/}" || echo "HARNESS-ERROR ${d%/} (timeout or crash)" >>"$LOG"
    fi
  done
done
grep -E '^(PASS|FAIL|UNSUPPORTED|HARNESS-ERROR) /' "$LOG" | awk '{print $1}' | sort | uniq -c
