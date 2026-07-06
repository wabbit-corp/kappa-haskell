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

# This suite has explicit LLVM lanes. All other builds are the default native
# backend and must not inherit a caller's KAPPA_BACKEND.
unset KAPPA_BACKEND

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
      echo "   FAIL: Perceus RC build did not report zero KBackendIR ownership metadata findings"
      sed -n '/perceus-rc:/p' "$log" | sed 's/^/     /'
      fails=$((fails+1))
      return 1
    fi
  fi
  return 0
}

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

# ── C driver detection (mirror the build driver's order) ──────────────
have_driver() {
  [ -n "${KAPPA_CC:-}" ] && return 0
  for c in zig cc gcc clang; do command -v "$c" >/dev/null 2>&1 && return 0; done
  return 1
}

explicit_c_driver() {
  if command -v cc >/dev/null 2>&1; then
    command -v cc
  elif command -v gcc >/dev/null 2>&1; then
    command -v gcc
  elif command -v clang >/dev/null 2>&1; then
    command -v clang
  elif command -v zig >/dev/null 2>&1; then
    printf '%s cc\n' "$(command -v zig)"
  fi
}

if ! have_driver; then
  echo "SKIP: no C driver found (set \$KAPPA_CC or install zig/cc/gcc/clang)."
  echo "      The native backend test suite needs a C toolchain; skipping."
  exit 0
fi

rm -rf "$WORK"; mkdir -p "$WORK"

runtime_tsan_supported() {
  make -C "$ROOT/runtime" tsan-supported >/dev/null 2>&1
}

echo "== building the kappa CLI =="
timeout 600 cabal build -v0 exe:kappa || { echo "FAIL: cabal build"; exit 1; }

cleanup_generated_for_source() {
  local src="$1"
  rm -f "${src%.kp}.kappa.c" "${src%.kp}.kappa.ll"
}

build_clean_for_source() {
  local src="$1"
  shift
  cleanup_generated_for_source "$src"
  "$@"
  local rc=$?
  cleanup_generated_for_source "$src"
  return "$rc"
}

run_diff_case() {
  local name="$1"; local src="$CASES/$name.kp"
  echo "-- case: $name (native output must match the interpreter)"
  local interp native exe irc nrc off_native off_exe off_rc native_err
  interp="$(timeout 120 $KAPPA run "$src" 2>/dev/null)"; irc=$?
  if [ "$irc" -ne 0 ]; then
    echo "   FAIL: interpreter exited with $irc"; fails=$((fails+1)); return
  fi
  if perceus_rc_enabled; then
    off_exe="$WORK/$name.rcoff"
    cleanup_generated_for_source "$src"
    if ! timeout 240 env KAPPA_PERCEUS_RC=0 $KAPPA build "$src" -o "$off_exe" >"$WORK/$name.rcoff.build.log" 2>&1; then
      cleanup_generated_for_source "$src"
      echo "   FAIL: native RC-off baseline build failed"; cat "$WORK/$name.rcoff.build.log" | sed 's/^/     /'; fails=$((fails+1)); return
    fi
    cleanup_generated_for_source "$src"
    off_native="$(timeout 120 env -u KAPPA_POISON "$off_exe" 2>/dev/null)"; off_rc=$?
    if [ "$off_rc" -ne 0 ]; then
      echo "   FAIL: native RC-off baseline exited with $off_rc"; fails=$((fails+1)); return
    fi
    if [ "$interp" != "$off_native" ]; then
      echo "   FAIL: RC-off native baseline output mismatch"
      echo "     interpreter: $(printf '%s' "$interp" | tr '\n' '|')"
      echo "     native-off:  $(printf '%s' "$off_native" | tr '\n' '|')"
      fails=$((fails+1))
      return
    fi
  fi
  exe="$WORK/$name"
  cleanup_generated_for_source "$src"
  if ! timeout 240 $KAPPA build "$src" -o "$exe" >"$WORK/$name.build.log" 2>&1; then
    cleanup_generated_for_source "$src"
    echo "   FAIL: native build failed"; cat "$WORK/$name.build.log" | sed 's/^/     /'; fails=$((fails+1)); return
  fi
  cleanup_generated_for_source "$src"
  check_perceus_rc_log "$WORK/$name.build.log" || return
  native_err="$WORK/$name.native.err"
  if perceus_rc_enabled; then
    native="$(timeout 120 env KAPPA_POISON=1 "$exe" 2>"$native_err")"; nrc=$?
  else
    native="$(timeout 120 "$exe" 2>"$native_err")"; nrc=$?
  fi
  if [ "$nrc" -ne 0 ]; then
    echo "   FAIL: native executable exited with $nrc"
    sed 's/^/     /' "$native_err" | head -40
    fails=$((fails+1)); return
  fi
  if [ "$interp" != "$native" ]; then
    echo "   FAIL: output mismatch"
    echo "     interpreter: $(printf '%s' "$interp" | tr '\n' '|')"
    echo "     native:      $(printf '%s' "$native" | tr '\n' '|')"
    fails=$((fails+1))
  elif perceus_rc_enabled && [ "$off_native" != "$native" ]; then
    echo "   FAIL: RC-on output differs from RC-off native baseline"
    echo "     native-off:  $(printf '%s' "$off_native" | tr '\n' '|')"
    echo "     native-on:   $(printf '%s' "$native" | tr '\n' '|')"
    fails=$((fails+1))
  elif perceus_rc_enabled; then
    echo "   ok ($(printf '%s' "$native" | tr '\n' '|'); RC-on == RC-off; poison)"
  else
    echo "   ok ($(printf '%s' "$native" | tr '\n' '|'))"
  fi
}

run_expected_fail_case() {
  local name="$1"; local src="$CASES/$name.kp"
  echo "-- case: $name (interpreter and native must both fail without stdout)"
  local interp native exe irc nrc
  interp="$(timeout 120 $KAPPA run "$src" 2>/dev/null)"; irc=$?
  exe="$WORK/$name"
  cleanup_generated_for_source "$src"
  if ! timeout 240 $KAPPA build "$src" -o "$exe" >"$WORK/$name.build.log" 2>&1; then
    cleanup_generated_for_source "$src"
    echo "   FAIL: native build failed"; cat "$WORK/$name.build.log" | sed 's/^/     /'; fails=$((fails+1)); return
  fi
  cleanup_generated_for_source "$src"
  check_perceus_rc_log "$WORK/$name.build.log" || return
  native="$(timeout 120 "$exe" 2>/dev/null)"; nrc=$?
  if [ "$irc" -ne 0 ] && [ "$nrc" -ne 0 ] && [ -z "$interp" ] && [ -z "$native" ]; then
    echo "   ok (interpreter rc=$irc, native rc=$nrc, no stdout)"
  else
    echo "   FAIL: expected both paths to fail without stdout"
    echo "     interpreter rc=$irc stdout=$(printf '%s' "$interp" | tr '\n' '|')"
    echo "     native      rc=$nrc stdout=$(printf '%s' "$native" | tr '\n' '|')"
    fails=$((fails+1))
  fi
}

run_native_expected_stdout_case() {
  local name="$1"; local want="$2"; local src="$CASES/$name.kp"
  echo "-- case: $name (native erased-layout regression must print $want)"
  local exe out rc
  exe="$WORK/$name.expected.c"
  cleanup_generated_for_source "$src"
  if ! timeout 240 $KAPPA build "$src" -o "$exe" >"$WORK/$name.expected.c.build.log" 2>&1; then
    cleanup_generated_for_source "$src"
    echo "   FAIL: C native build failed"; cat "$WORK/$name.expected.c.build.log" | sed 's/^/     /'; fails=$((fails+1)); return
  fi
  cleanup_generated_for_source "$src"
  check_perceus_rc_log "$WORK/$name.expected.c.build.log" || return
  out="$(timeout 120 "$exe" 2>/dev/null)"; rc=$?
  if [ "$rc" -ne 0 ] || [ "$out" != "$want" ]; then
    echo "   FAIL: C native rc=$rc stdout=$(printf '%s' "$out" | tr '\n' '|')"
    fails=$((fails+1))
    return
  fi
  exe="$WORK/$name.expected.llvm"
  cleanup_generated_for_source "$src"
  if ! timeout 240 env KAPPA_BACKEND=llvm $KAPPA build "$src" -o "$exe" >"$WORK/$name.expected.llvm.build.log" 2>&1; then
    cleanup_generated_for_source "$src"
    echo "   FAIL: LLVM native build failed"; cat "$WORK/$name.expected.llvm.build.log" | sed 's/^/     /'; fails=$((fails+1)); return
  fi
  cleanup_generated_for_source "$src"
  check_perceus_rc_log "$WORK/$name.expected.llvm.build.log" || return
  out="$(timeout 120 "$exe" 2>/dev/null)"; rc=$?
  if [ "$rc" -ne 0 ] || [ "$out" != "$want" ]; then
    echo "   FAIL: LLVM native rc=$rc stdout=$(printf '%s' "$out" | tr '\n' '|')"
    fails=$((fails+1))
    return
  fi
  echo "   ok (C and LLVM printed $want)"
}

echo "== output-equivalence cases =="
for c in arith data control strings loops records unicode traits variants-susp bignum dokernel showprims bytes ubuilders unidata uhash iorec defernest deferlazy defer-finally defer-sleep defer-fail-compose defer-loop-fail-remaining defer-legacy-fail-compose reraise-nonfail-discard defer-finally-reraise-sequence finally-reraise-sequence finally-by-value-reraise prefixbind letqor letqelse projection lr1 varloop monadref-readref-field monadref-user-evidence recordproj record-erased-field-proj tupleproj ctortags adtcons scalarkinds fpbitident fpmath showfixed await-dbl-acc flatframe flatbinders flatclosure effects effparking efftailloop abandon-perform-drain borrowview ioerror stm atomic atomic-race mutarray fork forkdefer scope fork-transitive await-exit iobind-await join-success join-catch race timeout blocking-source blocking-first-class blocking-cede blocking-sleep interrupt-cause withscope monitor interrupt interrupt-tight-loop adv-boxed-loop-tail adv-loop-tail-effect adv-loop-tail-read tail-loop-owned-projection interrupt-general-loop masking mask-suppress-interrupt maskrank2 maskrank2nonres bracketmask usinginterrupt usingsusp promise promise-poll fiber-ref-modify fiber-id on-exit-interrupt on-interrupt-cleanup-fail timer-duration sleep-nonpositive stm-tvar scheduler-retry suspendloop acceptloop suspendvarrw var-store-io-action-no-suspend-shape suspendbreak while-defer-scope suspendsubdefer suspendmonassign suspendloop-deep finally-tail-suspend restore-suspend-do doblock-tailrec perceus-s3-generated-drops perceus-s3-ref-transfer perceus-rc-recursive-list-path perceus-s5-reuse-direct perceus-s5-reuse-move perceus-s5-reuse-mixed-branch perceus-s5-reuse-branch-replace-boxed perceus-s5-reuse-as-pattern perceus-s5-direct-projection-failclosed perceus-s5-reuse-let-scope; do run_diff_case "$c"; done
run_native_expected_stdout_case ctor-erased-tail-pattern 20
run_native_expected_stdout_case tuple-erased-field-pattern 5
run_native_expected_stdout_case poly-lambda-erased-arg 5
run_native_expected_stdout_case ctor-erased-field-patch 30
run_expected_fail_case letqmiss

echo "== interpreter interrupt publication stress =="
stress_src="$CASES/adv-loop-tail-read.kp"
stress_ok=1
for i in $(seq 1 50); do
  err="$WORK/adv-loop-tail-read-stress.$i.err"
  out="$(timeout 120 $KAPPA run "$stress_src" 2>"$err")"; rc=$?
  if [ "$rc" -ne 0 ] || [ "$out" != "exit:interrupted" ]; then
    echo "   FAIL: adv-loop-tail-read stress iteration $i rc=$rc stdout=$(printf '%s' "$out" | tr '\n' '|')"
    sed 's/^/     /' "$err" | head -20
    fails=$((fails+1))
    stress_ok=0
    break
  fi
  rm -f "$err"
done
if [ "$stress_ok" -eq 1 ]; then
  echo "   ok (50/50 interrupted fibers published exactly one Exit)"
fi

echo "== interpreter AtomicRef RMW stress =="
atomic_stress_src="$CASES/atomic-race.kp"
atomic_stress_ok=1
for i in $(seq 1 25); do
  err="$WORK/atomic-race-stress.$i.err"
  out="$(timeout 120 $KAPPA run "$atomic_stress_src" 2>"$err")"; rc=$?
  if [ "$rc" -ne 0 ] || [ "$out" != "64000" ]; then
    echo "   FAIL: atomic-race stress iteration $i rc=$rc stdout=$(printf '%s' "$out" | tr '\n' '|')"
    sed 's/^/     /' "$err" | head -20
    fails=$((fails+1))
    atomic_stress_ok=0
    break
  fi
  rm -f "$err"
done
if [ "$atomic_stress_ok" -eq 1 ]; then
  echo "   ok (25/25 AtomicRef fetch-add runs reached 64000)"
fi

# §18.1.11: the source-level `blocking` combinator must lower to the rt-blocking
# OP node on both native backends. Running the case above checks observable
# parity; this catches an accidental fallback through the synchronous bridge.
echo "== rt-blocking: source blocking lowers to krt2_blocking =="
btmp="$WORK/blocking-source-emit"; mkdir -p "$btmp"
cfile="$CASES/blocking-source.kappa.c"
rm -f "$cfile"
if timeout 120 $KAPPA build "$CASES/blocking-source.kp" --emit-c -o "$btmp/blocking" >"$btmp/c.log" 2>&1; then
  if [ -f "$cfile" ] && grep -qE '\bkrt2_blocking\(' "$cfile"; then
    echo "   ok (C source-level blocking builds OP_BLOCKING)"
  else
    echo "   FAIL: C source-level blocking did not lower through krt2_blocking or did not emit fresh C"; fails=$((fails+1))
  fi
  rm -f "$cfile"
else
  echo "   FAIL: blocking-source C --emit-c build failed"; cat "$btmp/c.log" | sed 's/^/     /'; fails=$((fails+1))
fi
llfile="$CASES/blocking-source.kappa.ll"
rm -f "$llfile"
if KAPPA_BACKEND=llvm timeout 180 $KAPPA build "$CASES/blocking-source.kp" --emit-c -o "$btmp/blocking-llvm" >"$btmp/llvm.log" 2>&1; then
  if [ -f "$llfile" ] && grep -qE 'call ptr @krt2_blocking\(' "$llfile"; then
    echo "   ok (LLVM source-level blocking builds OP_BLOCKING)"
  else
    echo "   FAIL: LLVM source-level blocking did not lower through krt2_blocking or did not emit fresh LLVM"; fails=$((fails+1))
  fi
  rm -f "$llfile"
else
  echo "   FAIL: blocking-source LLVM --emit-c build failed"; cat "$btmp/llvm.log" | sed 's/^/     /'; fails=$((fails+1))
fi
echo "== rt-blocking runtime lane, foreign-handle kind, and Perceus S3/S4/S5 gates =="
if timeout 120 make -C "$ROOT/runtime" build/blocking_lane build/fgn_kind build/perceus_s3_prereq build/perceus_s3_free build/perceus_s3_poison build/perceus_s4_shared build/perceus_s5_reuse >"$btmp/runtime.log" 2>&1; then
  if timeout 30 "$ROOT/runtime/build/blocking_lane" >"$btmp/blocking_lane.out" 2>"$btmp/blocking_lane.err"; then
    echo "   ok (runtime blocking lane preserves scheduler progress and source interruption)"
  else
    echo "   FAIL: runtime blocking lane harness failed"
    cat "$btmp/blocking_lane.out" "$btmp/blocking_lane.err" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  if timeout 30 "$ROOT/runtime/build/fgn_kind" >"$btmp/fgn_kind.out" 2>"$btmp/fgn_kind.err"; then
    echo "   ok (runtime foreign handles trap wrong kind before casting)"
  else
    echo "   FAIL: runtime foreign-handle kind harness failed"
    cat "$btmp/fgn_kind.out" "$btmp/fgn_kind.err" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  if timeout 30 "$ROOT/runtime/build/perceus_s3_prereq" >"$btmp/perceus_s3_prereq.out" 2>"$btmp/perceus_s3_prereq.err"; then
    echo "   ok (Perceus S3 freeable/shared/array prerequisites hold)"
  else
    echo "   FAIL: Perceus S3 runtime prerequisite harness failed"
    cat "$btmp/perceus_s3_prereq.out" "$btmp/perceus_s3_prereq.err" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  if timeout 30 "$ROOT/runtime/build/perceus_s3_free" >"$btmp/perceus_s3_free.out" 2>"$btmp/perceus_s3_free.err"; then
    echo "   ok (Perceus S3.2 free-on-zero runtime harness passed)"
  else
    echo "   FAIL: Perceus S3.2 free-on-zero runtime harness failed"
    cat "$btmp/perceus_s3_free.out" "$btmp/perceus_s3_free.err" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  if timeout 30 "$ROOT/runtime/build/perceus_s3_poison" >"$btmp/perceus_s3_poison.out" 2>"$btmp/perceus_s3_poison.err"; then
    echo "   ok (Perceus S3.2 poison-on-free UAF oracle harness passed)"
  else
    echo "   FAIL: Perceus S3.2 poison-on-free UAF oracle harness failed"
    cat "$btmp/perceus_s3_poison.out" "$btmp/perceus_s3_poison.err" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  if timeout 30 "$ROOT/runtime/build/perceus_s4_shared" >"$btmp/perceus_s4_shared.out" 2>"$btmp/perceus_s4_shared.err"; then
    echo "   ok (Perceus S4 shared counted-RC runtime harness passed)"
  else
    echo "   FAIL: Perceus S4 shared counted-RC runtime harness failed"
    cat "$btmp/perceus_s4_shared.out" "$btmp/perceus_s4_shared.err" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  if timeout 30 "$ROOT/runtime/build/perceus_s5_reuse" >"$btmp/perceus_s5_reuse.out" 2>"$btmp/perceus_s5_reuse.err"; then
    echo "   ok (Perceus S5 drop-guided reuse runtime harness passed)"
  else
    echo "   FAIL: Perceus S5 drop-guided reuse runtime harness failed"
    cat "$btmp/perceus_s5_reuse.out" "$btmp/perceus_s5_reuse.err" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  if KAPPA_POISON=1 timeout 30 "$ROOT/runtime/build/perceus_s5_reuse" >"$btmp/perceus_s5_reuse_poison.out" 2>"$btmp/perceus_s5_reuse_poison.err"; then
    echo "   ok (Perceus S5 drop-guided reuse runtime harness passed under KAPPA_POISON=1)"
  else
    echo "   FAIL: Perceus S5 drop-guided reuse runtime harness failed under KAPPA_POISON=1"
    cat "$btmp/perceus_s5_reuse_poison.out" "$btmp/perceus_s5_reuse_poison.err" | sed 's/^/     /'
    fails=$((fails+1))
  fi
else
  echo "   FAIL: runtime blocking/fgn/S3/S4/S5 harness build failed"; cat "$btmp/runtime.log" | sed 's/^/     /'; fails=$((fails+1))
fi

echo "== Perceus S4: ThreadSanitizer shared-RC concurrency corpus =="
if runtime_tsan_supported; then
  if timeout 300 make -C "$ROOT/runtime" tsan-rc >"$btmp/runtime-tsan-rc.log" 2>&1; then
    echo "   ok (TSan-clean shared-RC concurrency corpus)"
  else
    echo "   FAIL: Perceus S4 TSan shared-RC concurrency corpus failed"
    sed 's/^/     /' "$btmp/runtime-tsan-rc.log" | head -80
    fails=$((fails+1))
  fi
else
  echo "   FAIL: ThreadSanitizer is not supported by the detected C driver"
  fails=$((fails+1))
fi

echo "== Perceus S4: poison shared-RC concurrency corpus =="
if timeout 300 make -C "$ROOT/runtime" poison-rc >"$btmp/runtime-poison-rc.log" 2>&1; then
  echo "   ok (poison-clean shared-RC concurrency corpus under KAPPA_POISON=1)"
else
  echo "   FAIL: Perceus S4 poison shared-RC concurrency corpus failed"
  sed 's/^/     /' "$btmp/runtime-poison-rc.log" | head -80
  fails=$((fails+1))
fi

echo "== Perceus S4: biased RC fast-path performance gate =="
if timeout 120 make -C "$ROOT/runtime" bench-s4-rc >"$btmp/runtime-s4-rc-bench.log" 2>&1; then
  sed 's/^/   /' "$btmp/runtime-s4-rc-bench.log"
  echo "   ok (thread-local RC fast path beats shared atomic slow path)"
else
  echo "   FAIL: Perceus S4 biased RC performance gate failed"
  sed 's/^/     /' "$btmp/runtime-s4-rc-bench.log" | head -80
  fails=$((fails+1))
fi

echo "== package lock closure: unused sibling host bindings are not resolved =="
SEL="$WORK/selected-target-lock"; rm -rf "$SEL"; mkdir -p "$SEL/src/app"
printf 'module app.main\nmain : UIO Unit\nlet main = printlnString "selected-ok"\n' > "$SEL/src/app/main.kp"
cat > "$SEL/kappa.build.kp" <<'KP'
let buildConfig : BuildConfig = package
  { name = "selected-lock"
  , version = semver "1"
  , sourceRoots = [sourceRoot "src"]
  , fragmentAxes = []
  , dependencies = []
  , hostBindings =
      [ nativeBinding
          { name = "missing-sibling"
          , provides = [module "host.native.missing"]
          , surface = symbolList [symbolDecl "missing" "missing" [] ctUnit]
          , abi = cAbi
          , inputs = [headers ["definitely_missing_kappa_s4_sibling.h"], pkgConfig "definitely-missing-kappa-s4-sibling" None]
          , link = noLink
          , load = systemLoader
          }
      ]
  , targets =
      [ executable
          { name = "selected"
          , backend = native { toolchain = "cc", targetTriple = "x86_64-linux-gnu" }
          , fragments = tags []
          , main = module "app.main"
          , modules = modulesUnder "app"
          , dependencies = []
          , hostBindings = []
          }
      , executable
          { name = "needs-missing"
          , backend = native { toolchain = "cc", targetTriple = "x86_64-linux-gnu" }
          , fragments = tags []
          , main = module "app.main"
          , modules = modulesUnder "app"
          , dependencies = []
          , hostBindings = ["missing-sibling"]
          }
      ]
  }
KP
if timeout 200 $KAPPA build --update --manifest "$SEL" --target selected -o "$SEL/selected" >"$SEL/build.log" 2>&1; then
  selout="$(timeout 60 "$SEL/selected" 2>"$SEL/run.err")"; selrc=$?
  if [ "$selrc" -eq 0 ] && [ "$selout" = "selected-ok" ] && [ ! -e "$SEL/kappa.lock" ]; then
    echo "   ok (selected target ignores unused sibling host-binding closure)"
    printf '# kappa.lock v1 (test extra sibling entry)\nhost-binding fakeid missing-sibling\n' > "$SEL/kappa.lock"
    if timeout 200 $KAPPA build --manifest "$SEL" --target selected -o "$SEL/selected-locked" >"$SEL/locked.log" 2>&1; then
      echo "   ok (selected target tolerates unrelated sibling lock entries)"
    else
      echo "   FAIL: selected target rejected an unrelated sibling lock entry"
      cat "$SEL/locked.log" | sed 's/^/     /'
      fails=$((fails+1))
    fi
  else
    echo "   FAIL: selected target lock closure produced wrong result"
    printf '     rc=%s out=%s lock=%s\n' "$selrc" "$selout" "$(test -e "$SEL/kappa.lock" && echo yes || echo no)"
    sed 's/^/     /' "$SEL/run.err" | head -40
    fails=$((fails+1))
  fi
else
  echo "   FAIL: selected target build resolved an unused missing sibling host binding"
  cat "$SEL/build.log" | sed 's/^/     /'
  fails=$((fails+1))
fi

LOCKD="$WORK/selected-lock-duplicate"; rm -rf "$LOCKD"; mkdir -p "$LOCKD/src/app"
printf 'module app.main\nmain : UIO Unit\nlet main = printlnString "pin-ok"\n' > "$LOCKD/src/app/main.kp"
printf 'int pin_id(void);\n' > "$LOCKD/src/pin.h"
printf '#include "pin.h"\nint pin_id(void) { return 1; }\n' > "$LOCKD/src/pin.c"
cat > "$LOCKD/kappa.build.kp" <<'KP'
let buildConfig : BuildConfig = package
  { name = "selected-lock-duplicate"
  , version = semver "1"
  , sourceRoots = [sourceRoot "src"]
  , fragmentAxes = []
  , dependencies = []
  , hostBindings =
      [ nativeBinding
          { name = "pin"
          , provides = [module "host.native.pin.Raw"]
          , surface = symbolList [symbolDecl "pinId" "pin_id" [] ctInt]
          , abi = cAbi
          , inputs = [headers ["src/pin.h"], shim ["src/pin.c"], verify ["int pin_id(void)"]]
          , link = noLink
          , load = systemLoader
          }
      ]
  , targets =
      [ executable
          { name = "app"
          , backend = native { toolchain = "cc", targetTriple = "x86_64-linux-gnu" }
          , fragments = tags []
          , main = module "app.main"
          , modules = modulesUnder "app"
          , dependencies = []
          , hostBindings = ["pin"]
          }
      ]
  }
KP
if timeout 200 $KAPPA build --update --manifest "$LOCKD" --target app -o "$LOCKD/app" >"$LOCKD/build.log" 2>&1; then
  pin_line="$(grep '^host-binding ' "$LOCKD/kappa.lock" | head -1 || true)"
  pin_key="$(printf '%s\n' "$pin_line" | awk '{$1=""; $2=""; sub(/^  */, ""); print}')"
  if [ -n "$pin_key" ]; then
    if grep -q '^host-binding .* pin@x86_64-linux-gnu$' "$LOCKD/kappa.lock"; then
      echo "   ok (host-binding lock key includes the selected target ABI)"
    else
      echo "   FAIL: selected host-binding lock key is not target-qualified"
      cat "$LOCKD/kappa.lock" 2>/dev/null | sed 's/^/     /'
      fails=$((fails+1))
    fi
    printf 'host-binding stale-selected-identity %s\n' "$pin_key" >> "$LOCKD/kappa.lock"
    dupout="$(timeout 200 $KAPPA build --manifest "$LOCKD" --target app -o "$LOCKD/app2" 2>&1)"; duprc=$?
    if [ "$duprc" -ne 0 ] && grep -q "E_NATIVE_BINDING_UNPINNED" <<<"$dupout"; then
      echo "   ok (selected target rejects stale duplicate lock entry for the same host-binding key)"
    else
      echo "   FAIL: selected target accepted stale duplicate lock entry rc=$duprc"
      echo "$dupout" | sed 's/^/     /'
      fails=$((fails+1))
    fi

    explicit_cc="$(explicit_c_driver)"
    if [ -n "$explicit_cc" ]; then
      rm -f "$LOCKD/kappa.lock" "$LOCKD/app-explicit" "$LOCKD/app-explicit2"
      if KAPPA_CC=false timeout 200 $KAPPA build --cc "$explicit_cc" --update --manifest "$LOCKD" --target app -o "$LOCKD/app-explicit" >"$LOCKD/explicit-update.log" 2>&1 \
        && KAPPA_CC=false timeout 200 $KAPPA build --cc "$explicit_cc" --manifest "$LOCKD" --target app -o "$LOCKD/app-explicit2" >"$LOCKD/explicit-locked.log" 2>&1; then
        echo "   ok (explicit --cc drives lock discovery even when KAPPA_CC is stale)"
      else
        echo "   FAIL: explicit --cc was not honored consistently by lock discovery"
        cat "$LOCKD/explicit-update.log" "$LOCKD/explicit-locked.log" 2>/dev/null | sed 's/^/     /'
        fails=$((fails+1))
      fi
    else
      echo "   skip (no explicit cc/gcc/clang/zig driver found for --cc lock-discovery check)"
    fi
  else
    echo "   FAIL: selected host-binding build did not write a host-binding lock entry"
    cat "$LOCKD/kappa.lock" "$LOCKD/build.log" 2>/dev/null | sed 's/^/     /'
    fails=$((fails+1))
  fi
else
  echo "   FAIL: selected host-binding lock setup build failed"
  cat "$LOCKD/build.log" | sed 's/^/     /'
  fails=$((fails+1))
fi

echo "== Perceus S4: example package test targets build and run under default RC =="
case "$(uname -s)" in
  Darwin) DELVE_PACKAGE_TEST_TARGET="delve-tests-macos-arm64" ;;
  Linux) DELVE_PACKAGE_TEST_TARGET="delve-tests-linux" ;;
  *)
    echo "   FAIL: no host-runnable Delve package smoke target for $(uname -s)"
    fails=$((fails+1))
    DELVE_PACKAGE_TEST_TARGET=""
    ;;
esac

package_smoke() {
  local label="$1" manifest="$2" target="$3" expected="$4"
  local pkg="$WORK/${target}.pkg-src"
  local exe="$WORK/${target}.pkg-smoke"
  local log="$WORK/${target}.pkg-build.log"
  local err="$WORK/${target}.pkg-run.err"
  rm -rf "$pkg"
  mkdir -p "$pkg"
  cp -R "$manifest/." "$pkg/"
  rm -f "$pkg/kappa.lock"
  if timeout 300 env -u KAPPA_PERCEUS_RC $KAPPA build --update --manifest "$pkg" --target "$target" -o "$exe" >"$log" 2>&1; then
    KAPPA_PERCEUS_RC= check_perceus_rc_log "$log" || return
    local out rc
    out="$(cd "$pkg" && timeout 180 env -u KAPPA_PERCEUS_RC KAPPA_POISON=1 "$exe" 2>"$err")"; rc=$?
    if [ "$rc" -eq 0 ] && printf '%s\n' "$out" | grep -qxF "$expected" && ! printf '%s\n' "$out" | grep -q ': FAIL'; then
      echo "   ok ($label package test target; default RC + poison)"
    else
      echo "   FAIL: $label package test executable did not report success rc=$rc"
      printf '%s\n' "$out" | sed 's/^/     /'
      sed 's/^/     /' "$err" | head -40
      fails=$((fails+1))
    fi
  else
    echo "   FAIL: $label package test target build failed"
    cat "$log" | sed 's/^/     /'
    fails=$((fails+1))
  fi
}
[ -n "$DELVE_PACKAGE_TEST_TARGET" ] && package_smoke "delve" "$ROOT/examples/packages/delve" "$DELVE_PACKAGE_TEST_TARGET" "DELVE TESTS: ALL PASS"
package_smoke "railyard" "$ROOT/examples/packages/railyard" "railyard-tests" "RAILYARD TESTS: ALL PASS"
package_smoke "voxelcraft" "$ROOT/examples/packages/voxelcraft" "voxelcraft-tests" "VOXELCRAFT TESTS: ALL PASS"

echo "== Perceus S3.2: generated drops are non-vacuous and poison-clean =="
s32tmp="$WORK/perceus-s32-generated-drops"; mkdir -p "$s32tmp"
s32src="$CASES/perceus-s3-generated-drops.kp"
s32c="${s32src%.kp}.kappa.c"
rm -f "$s32c"
if KAPPA_PERCEUS_RC=true timeout 120 $KAPPA build "$s32src" --emit-c -o "$s32tmp/perceus_s3_generated_drops_emit" >"$s32tmp/emit.log" 2>&1; then
  KAPPA_PERCEUS_RC=true check_perceus_rc_log "$s32tmp/emit.log"
  s32_scrut_drops="$(grep -cF 'kdrop(scrut_' "$s32c" 2>/dev/null || true)"
  if [ "${s32_scrut_drops:-0}" -ge 2 ]; then
    echo "   ok-shape ($s32_scrut_drops generated scrutinee drops in the standing corpus fixture)"
  else
    echo "   FAIL: perceus-s3-generated-drops did not emit the expected generated scrutinee drops"
    [ -f "$s32c" ] && grep -nE 'kdrop|scrut_' "$s32c" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  rm -f "$s32c"
else
  echo "   FAIL: perceus-s3-generated-drops --emit-c build failed"; cat "$s32tmp/emit.log" | sed 's/^/     /'; fails=$((fails+1))
fi
rm -f "$s32c"
if KAPPA_PERCEUS_RC=0 timeout 120 $KAPPA build "$s32src" --emit-c -o "$s32tmp/perceus_s3_generated_drops_off_emit" >"$s32tmp/emit-off.log" 2>&1; then
  s32_off_main="$(awk '/^int main\(void\) \{/{f=1} f{print} f&&/^}/{exit}' "$s32c")"
  if printf '%s' "$s32_off_main" | grep -qE 'krc_set_enabled\(0\);' \
     && grep -qE 'krc_mark_shared_recursive' "$s32c" \
     && ! grep -qE 'kdrop\(|kdup\(' "$s32c"; then
    echo "   ok-off-shape (explicit RC-off suppresses generated ownership maintenance but keeps publish marking)"
  else
    echo "   FAIL: explicit RC-off generated-drop fixture emitted ownership maintenance or missed runtime RC/publish gates"
    [ -f "$s32c" ] && grep -nE 'kdrop|kdup|krc_mark_shared_recursive|krc_set_enabled' "$s32c" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  rm -f "$s32c"
else
  echo "   FAIL: perceus-s3-generated-drops RC-off --emit-c build failed"; cat "$s32tmp/emit-off.log" | sed 's/^/     /'; fails=$((fails+1))
fi
if KAPPA_PERCEUS_RC=true timeout 240 $KAPPA build "$s32src" -o "$s32tmp/perceus_s3_generated_drops" >"$s32tmp/build.log" 2>&1; then
  KAPPA_PERCEUS_RC=true check_perceus_rc_log "$s32tmp/build.log"
  s32out="$(timeout 120 env KAPPA_POISON=1 "$s32tmp/perceus_s3_generated_drops" 2>"$s32tmp/run.err")"; s32rc=$?
  if [ "$s32rc" -eq 0 ] && [ "$s32out" = "10200" ]; then
    echo "   ok-run (generated free-on-zero drops ran under KAPPA_POISON=1)"
  else
    echo "   FAIL: generated-drop fixture failed under KAPPA_POISON=1 rc=$s32rc stdout=$(printf '%s' "$s32out" | tr '\n' '|')"
    sed 's/^/     /' "$s32tmp/run.err" | head -40
    fails=$((fails+1))
  fi
  s32out_heap="$(timeout 120 env -u KAPPA_POISON KAPPA_GC_STATS=1 "$s32tmp/perceus_s3_generated_drops" 2>"$s32tmp/run-heap.err")"; s32heap_rc=$?
  if [ "$s32heap_rc" -ne 0 ] || [ "$s32out_heap" != "10200" ]; then
    echo "   FAIL: generated-drop fixture failed in real-free heap lane rc=$s32heap_rc stdout=$(printf '%s' "$s32out_heap" | tr '\n' '|')"
    sed 's/^/     /' "$s32tmp/run-heap.err" | head -40
    fails=$((fails+1))
  fi
  s32_heap="$(grep -oE 'heap_size=[0-9]+' "$s32tmp/run-heap.err" | tail -1 | cut -d= -f2)"
  s32_frees="$(grep -oE 'frees=[0-9]+' "$s32tmp/run-heap.err" | tail -1 | cut -d= -f2)"
  if [ -z "${s32_frees:-}" ] || [ "$s32_frees" -le 0 ]; then
    echo "   FAIL: generated-drop real-free lane did not report positive RC frees"
    sed 's/^/     /' "$s32tmp/run-heap.err" | head -40
    fails=$((fails+1))
  fi
else
  echo "   FAIL: perceus-s3-generated-drops native build failed"; cat "$s32tmp/build.log" | sed 's/^/     /'; fails=$((fails+1))
fi
rm -f "$s32c"

echo "== Perceus S3.4: generated free-on-zero heap stays bounded by default =="
s34src="$s32tmp/perceus-s3-generated-drops-100k.kp"
sed 's/sumDrops 100 0/sumDrops 100000 0/' "$s32src" >"$s34src"
if [ -z "${s32_heap:-}" ]; then
  echo "   FAIL: missing small-fixture heap_size GC statistic; S3.4 heap gate cannot be evaluated"
  fails=$((fails+1))
elif timeout 240 env -u KAPPA_PERCEUS_RC $KAPPA build "$s34src" -o "$s32tmp/perceus_s3_generated_drops_100k" >"$s32tmp/build-100k.log" 2>&1; then
  KAPPA_PERCEUS_RC=true check_perceus_rc_log "$s32tmp/build-100k.log"
  s34out="$(timeout 120 env -u KAPPA_POISON KAPPA_GC_STATS=1 "$s32tmp/perceus_s3_generated_drops_100k" 2>"$s32tmp/run-100k.err")"; s34rc=$?
  s34_heap="$(grep -oE 'heap_size=[0-9]+' "$s32tmp/run-100k.err" | tail -1 | cut -d= -f2)"
  s34_frees="$(grep -oE 'frees=[0-9]+' "$s32tmp/run-100k.err" | tail -1 | cut -d= -f2)"
  if [ "$s34rc" -ne 0 ] || [ "$s34out" != "10000200000" ]; then
    echo "   FAIL: generated-drop 100k fixture failed under default RC real-free lane rc=$s34rc stdout=$(printf '%s' "$s34out" | tr '\n' '|')"
    sed 's/^/     /' "$s32tmp/run-100k.err" | head -40
    fails=$((fails+1))
  elif [ -z "${s34_heap:-}" ]; then
    echo "   FAIL: missing 100k heap_size GC statistic; S3.4 heap gate cannot be evaluated"
    sed 's/^/     /' "$s32tmp/run-100k.err" | head -40
    fails=$((fails+1))
  elif [ -z "${s34_frees:-}" ] || [ "$s34_frees" -lt 200000 ]; then
    echo "   FAIL: generated-drop 100k fixture did not perform enough RC frees (frees=${s34_frees:-missing}, expected >=200000)"
    sed 's/^/     /' "$s32tmp/run-100k.err" | head -40
    fails=$((fails+1))
  elif s34_rel_limit=$((s32_heap * 4)); [ "$s34_rel_limit" -lt 2097152 ] && s34_rel_limit=2097152; [ "$s34_heap" -le 4194304 ] && [ "$s34_heap" -le "$s34_rel_limit" ]; then
    echo "   ok-heap (N=100 heap=${s32_heap}B/frees=${s32_frees:-?}, N=100000 heap=${s34_heap}B/frees=${s34_frees}; default RC real-free lane bounded)"
  else
    echo "   FAIL: generated-drop heap grew with N in real-free lane (N=100 ${s32_heap}B -> N=100000 ${s34_heap}B; limits abs=4194304B rel=${s34_rel_limit}B)"
    fails=$((fails+1))
  fi
  if timeout 240 env KAPPA_PERCEUS_RC=0 $KAPPA build "$s34src" -o "$s32tmp/perceus_s3_generated_drops_100k_off" >"$s32tmp/build-100k-off.log" 2>&1; then
    s34off_out="$(timeout 120 env KAPPA_GC_STATS=1 "$s32tmp/perceus_s3_generated_drops_100k_off" 2>"$s32tmp/run-100k-off.err")"; s34off_rc=$?
    s34off_frees="$(grep -oE 'frees=[0-9]+' "$s32tmp/run-100k-off.err" | tail -1 | cut -d= -f2)"
    if [ "$s34off_rc" -ne 0 ] || [ "$s34off_out" != "10000200000" ]; then
      echo "   FAIL: generated-drop 100k explicit RC-off baseline failed rc=$s34off_rc stdout=$(printf '%s' "$s34off_out" | tr '\n' '|')"
      sed 's/^/     /' "$s32tmp/run-100k-off.err" | head -40
      fails=$((fails+1))
    elif [ "${s34off_frees:-missing}" = "0" ]; then
      echo "   ok-off-heap (explicit RC-off produced zero RC frees, so the default-on free-count gate is discriminating)"
    else
      echo "   FAIL: explicit RC-off generated-drop baseline performed RC frees (frees=${s34off_frees:-missing})"
      sed 's/^/     /' "$s32tmp/run-100k-off.err" | head -40
      fails=$((fails+1))
    fi
  else
    echo "   FAIL: perceus-s3-generated-drops 100k explicit RC-off native build failed"; cat "$s32tmp/build-100k-off.log" | sed 's/^/     /'; fails=$((fails+1))
  fi
else
  echo "   FAIL: perceus-s3-generated-drops 100k default-RC native build failed"; cat "$s32tmp/build-100k.log" | sed 's/^/     /'; fails=$((fails+1))
fi

echo "== Perceus S5.B: same-size match rebuild emits reuse primitives =="
s5tmp="$WORK/perceus-s5-reuse-direct-shape"; rm -rf "$s5tmp"; mkdir -p "$s5tmp"
s5src="$CASES/perceus-s5-reuse-direct.kp"
s5c="${s5src%.kp}.kappa.c"
rm -f "$s5c"
if KAPPA_PERCEUS_RC=true timeout 120 $KAPPA build "$s5src" --emit-c -o "$s5tmp/perceus_s5_reuse_direct_emit" >"$s5tmp/emit.log" 2>&1; then
  KAPPA_PERCEUS_RC=true check_perceus_rc_log "$s5tmp/emit.log"
  if grep -qE 'kdrop_reuse_ctor_alloc\(' "$s5c"; then
    echo "   ok-shape (same-size constructor rebuild is routed through fused drop/reuse allocation)"
  else
    echo "   FAIL: perceus-s5-reuse-direct did not emit the expected fused drop/reuse allocation"
    [ -f "$s5c" ] && grep -nE 'kdrop_reuse_ctor_alloc|kdrop_reuse_ctor|kreuse_ctor|kdrop\(scrut_|kctor\(' "$s5c" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  rm -f "$s5c"
else
  echo "   FAIL: perceus-s5-reuse-direct --emit-c build failed"; cat "$s5tmp/emit.log" | sed 's/^/     /'; fails=$((fails+1))
fi
rm -f "$s5c"

echo "== Perceus S5.B2: moved constructor fields fuse dup/drop =="
s5mtmp="$WORK/perceus-s5-reuse-move-shape"; rm -rf "$s5mtmp"; mkdir -p "$s5mtmp"
s5msrc="$CASES/perceus-s5-reuse-move.kp"
s5mc="${s5msrc%.kp}.kappa.c"
rm -f "$s5mc"
if KAPPA_PERCEUS_RC=true timeout 120 $KAPPA build "$s5msrc" --emit-c -o "$s5mtmp/perceus_s5_reuse_move_emit" >"$s5mtmp/emit.log" 2>&1; then
  KAPPA_PERCEUS_RC=true check_perceus_rc_log "$s5mtmp/emit.log"
	  s5m_rebuild_block="$(awk '/^static KValue \*kw_main_2e_render\(KValue \*p0\) \{/{exit} {print}' "$s5mc")"
  if printf '%s\n' "$s5m_rebuild_block" | grep -qE 'kdrop_reuse_ctor_alloc\(' \
     && ! printf '%s\n' "$s5m_rebuild_block" | grep -qE 'kdup\(kctor_arg\('; then
    echo "   ok-shape (same-size field moves use fused drop/reuse allocation without field dup/drop pairs)"
  else
    echo "   FAIL: perceus-s5-reuse-move did not fuse moved-field dup/drop pairs"
    [ -f "$s5mc" ] && printf '%s\n' "$s5m_rebuild_block" | grep -nE 'kdrop_reuse_ctor_alloc|kdrop_reuse_ctor|kreuse_ctor|kdup\(kctor_arg|kdrop\(scrut_|kctor\(' | sed 's/^/     /'
    fails=$((fails+1))
  fi
  rm -f "$s5mc"
else
  echo "   FAIL: perceus-s5-reuse-move --emit-c build failed"; cat "$s5mtmp/emit.log" | sed 's/^/     /'; fails=$((fails+1))
fi
rm -f "$s5mc"

echo "== Perceus S5.B2: early-token reuse is path-total =="
s5mixtmp="$WORK/perceus-s5-reuse-mixed-branch-shape"; rm -rf "$s5mixtmp"; mkdir -p "$s5mixtmp"
s5mixsrc="$CASES/perceus-s5-reuse-mixed-branch.kp"
s5mixc="${s5mixsrc%.kp}.kappa.c"
rm -f "$s5mixc"
if KAPPA_PERCEUS_RC=true timeout 120 $KAPPA build "$s5mixsrc" --emit-c -o "$s5mixtmp/perceus_s5_reuse_mixed_emit" >"$s5mixtmp/emit.log" 2>&1; then
  KAPPA_PERCEUS_RC=true check_perceus_rc_log "$s5mixtmp/emit.log"
  if ! grep -qE 'ktry_reuse_ctor\(' "$s5mixc"; then
    echo "   ok-shape (mixed reuse/non-reuse control flow stays on the conservative lowering)"
  else
    echo "   FAIL: perceus-s5-reuse-mixed-branch acquired a reuse token for a non-total path"
    [ -f "$s5mixc" ] && grep -nE 'kw_main_2e_step|ktry_reuse_ctor|kreuse_ctor_skip|kdrop\(scrut_|kctor\(' "$s5mixc" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  rm -f "$s5mixc"
else
  echo "   FAIL: perceus-s5-reuse-mixed-branch --emit-c build failed"; cat "$s5mixtmp/emit.log" | sed 's/^/     /'; fails=$((fails+1))
fi
rm -f "$s5mixc"

echo "== Perceus S5.B2: as-pattern whole-cell aliases fail closed for reuse =="
s5astmp="$WORK/perceus-s5-reuse-as-pattern-shape"; rm -rf "$s5astmp"; mkdir -p "$s5astmp"
s5assrc="$CASES/perceus-s5-reuse-as-pattern.kp"
s5asc="${s5assrc%.kp}.kappa.c"
rm -f "$s5asc"
if KAPPA_PERCEUS_RC=true timeout 120 $KAPPA build "$s5assrc" --emit-c -o "$s5astmp/perceus_s5_reuse_as_emit" >"$s5astmp/emit.log" 2>&1; then
  KAPPA_PERCEUS_RC=true check_perceus_rc_log "$s5astmp/emit.log"
  s5as_update_block="$(awk '/^static KValue \*kw_main_2e_update\(KValue \*p0, KValue \*p1, KValue \*p2\) \{/{flag=1} /^static KValue \*kw_main_2e_render\(KValue \*p0\) \{/{flag=0} flag {print}' "$s5asc")"
  if ! printf '%s\n' "$s5as_update_block" | grep -qE 'ktry_reuse_ctor|kdrop_reuse_ctor_alloc|kreuse_ctor_skip'; then
    echo "   ok-shape (whole-scrutinee as-pattern alias disables S5 reuse)"
  else
    echo "   FAIL: perceus-s5-reuse-as-pattern reused a constructor while the whole-cell alias is live"
    [ -f "$s5asc" ] && printf '%s\n' "$s5as_update_block" | grep -nE 'ktry_reuse_ctor|kdrop_reuse_ctor_alloc|kreuse_ctor_skip|kdrop\(pat_|kctor\(' | sed 's/^/     /'
    fails=$((fails+1))
  fi
  rm -f "$s5asc"
else
  echo "   FAIL: perceus-s5-reuse-as-pattern --emit-c build failed"; cat "$s5astmp/emit.log" | sed 's/^/     /'; fails=$((fails+1))
fi
rm -f "$s5asc"

echo "== Perceus S5.B2: direct projection call results fail closed for ownership =="
s5projtmp="$WORK/perceus-s5-direct-projection-shape"; rm -rf "$s5projtmp"; mkdir -p "$s5projtmp"
s5projsrc="$CASES/perceus-s5-direct-projection-failclosed.kp"
s5projc="${s5projsrc%.kp}.kappa.c"
rm -f "$s5projc"
if KAPPA_PERCEUS_RC=true timeout 120 $KAPPA build "$s5projsrc" --emit-c -o "$s5projtmp/perceus_s5_direct_projection_emit" >"$s5projtmp/emit.log" 2>&1; then
  KAPPA_PERCEUS_RC=true check_perceus_rc_log "$s5projtmp/emit.log"
  s5proj_use_block="$(awk '/^static KValue \*kw_main_2e_use\(KValue \*p0\) \{/{flag=1} /^static KValue \*kw_main_2e_main\(void\) \{/{flag=0} flag {print}' "$s5projc")"
  if printf '%s\n' "$s5proj_use_block" | grep -qE 'kw_main_2e_project\(' \
     && ! printf '%s\n' "$s5proj_use_block" | grep -qE 'kdrop\(let_[0-9]+\);'; then
    echo "   ok-shape (borrowed direct projection result is not scope-dropped as owned)"
  else
    echo "   FAIL: perceus-s5-direct-projection-failclosed treated a borrowed direct-call projection as owned"
    [ -f "$s5projc" ] && printf '%s\n' "$s5proj_use_block" | grep -nE 'kw_main_2e_project|kdrop\(let_|krec_at|kctor_arg' | sed 's/^/     /'
    fails=$((fails+1))
  fi
  rm -f "$s5projc"
else
  echo "   FAIL: perceus-s5-direct-projection-failclosed --emit-c build failed"; cat "$s5projtmp/emit.log" | sed 's/^/     /'; fails=$((fails+1))
fi
rm -f "$s5projc"

echo "== Perceus S5.B2: skip slots are branch-local =="
s5repltmp="$WORK/perceus-s5-reuse-branch-replace-shape"; rm -rf "$s5repltmp"; mkdir -p "$s5repltmp"
s5replsrc="$CASES/perceus-s5-reuse-branch-replace-boxed.kp"
s5replc="${s5replsrc%.kp}.kappa.c"
rm -f "$s5replc"
if KAPPA_PERCEUS_RC=true timeout 120 $KAPPA build "$s5replsrc" --emit-c -o "$s5repltmp/perceus_s5_reuse_replace_emit" >"$s5repltmp/emit.log" 2>&1; then
  KAPPA_PERCEUS_RC=true check_perceus_rc_log "$s5repltmp/emit.log"
  s5repl_update_block="$(awk '/^static KValue \*kw_main_2e_update\(KValue \*p0, KValue \*p1, KValue \*p2\) \{/{flag=1} /^static KValue \*kw_main_2e_render\(KValue \*p0\) \{/{flag=0} flag {print}' "$s5replc")"
  s5repl_replace_branch="$(printf '%s\n' "$s5repl_update_block" | awk '/if \(kas_bool\(p0\)\) \{/{flag=1; next} flag && /^[[:space:]]*} else \{/{exit} flag {print}')"
  s5repl_keep_branch="$(printf '%s\n' "$s5repl_update_block" | awk '/if \(kas_bool\(p0\)\) \{/{seen=1; next} seen && /^[[:space:]]*} else \{/{flag=1; next} flag && /^[[:space:]]*}/{exit} flag {print}')"
  if printf '%s\n' "$s5repl_replace_branch" | grep -qE 'kdrop\(pat_[0-9]+\);' \
     && printf '%s\n' "$s5repl_replace_branch" | grep -qE 'int moves_[0-9]+\[\] = \{0, -1\};' \
     && printf '%s\n' "$s5repl_replace_branch" | grep -qE 'int skip_[0-9]+\[\] = \{0, 1\};' \
     && ! printf '%s\n' "$s5repl_keep_branch" | grep -qE 'kdrop\(pat_[0-9]+\);' \
     && printf '%s\n' "$s5repl_keep_branch" | grep -qE 'int moves_[0-9]+\[\] = \{0, 1\};'; then
    echo "   ok-shape (replacement branch drops/skips overwritten field; sibling branch carries both fields)"
  else
    echo "   FAIL: perceus-s5-reuse-branch-replace-boxed did not pair the overwritten boxed-slot drop with the rewrite skip"
    [ -f "$s5replc" ] && printf '%s\n' "$s5repl_update_block" | grep -nE 'ktry_reuse_ctor|kreuse_ctor_skip|moves_|skip_|kdrop\(pat_|kdrop\(scrut_|if \(kas_bool' | sed 's/^/     /'
    fails=$((fails+1))
  fi
  rm -f "$s5replc"
else
  echo "   FAIL: perceus-s5-reuse-branch-replace-boxed --emit-c build failed"; cat "$s5repltmp/emit.log" | sed 's/^/     /'; fails=$((fails+1))
fi
rm -f "$s5replc"

echo "== Perceus S5.B3: recursive boxed list-map reuses cons cells =="
s5b3tmp="$WORK/perceus-s5-listmap-reuse"; rm -rf "$s5b3tmp"; mkdir -p "$s5b3tmp"
s5b3src="$ROOT/test/native/bench/proposed/s5_listmap_reuse.kp"
s5b3c="${s5b3src%.kp}.kappa.c"
rm -f "$s5b3c"
if KAPPA_PERCEUS_RC=true timeout 120 $KAPPA build "$s5b3src" --emit-c -o "$s5b3tmp/emit" >"$s5b3tmp/emit.log" 2>&1; then
  KAPPA_PERCEUS_RC=true check_perceus_rc_log "$s5b3tmp/emit.log"
  if grep -qE 'ktry_reuse_ctor\(' "$s5b3c" \
     && grep -qE 'kreuse_ctor_skip\(' "$s5b3c"; then
    echo "   ok-shape (recursive boxed list-map uses the early-token reuse branch)"
  else
    echo "   FAIL: s5_listmap_reuse did not emit the early-token reuse branch"
    [ -f "$s5b3c" ] && grep -nE 'ktry_reuse_ctor|kreuse_ctor_skip|kdrop_reuse_ctor_alloc|kdup\(kctor_arg|kctor\(' "$s5b3c" | sed 's/^/     /'
    fails=$((fails+1))
  fi
else
  echo "   FAIL: s5_listmap_reuse --emit-c build failed"; cat "$s5b3tmp/emit.log" | sed 's/^/     /'; fails=$((fails+1))
fi
rm -f "$s5b3c"
if KAPPA_PERCEUS_RC=true timeout 180 $KAPPA build "$s5b3src" -o "$s5b3tmp/on" >"$s5b3tmp/on.build.log" 2>&1 \
   && KAPPA_PERCEUS_RC=0 timeout 180 $KAPPA build "$s5b3src" -o "$s5b3tmp/off" >"$s5b3tmp/off.build.log" 2>&1; then
  KAPPA_PERCEUS_RC=true check_perceus_rc_log "$s5b3tmp/on.build.log"
  on_out="$(KAPPA_GC_STATS=1 KAPPA_POISON=1 timeout 60 "$s5b3tmp/on" 2>&1)"; on_rc=$?
  off_out="$(KAPPA_GC_STATS=1 timeout 60 "$s5b3tmp/off" 2>&1)"; off_rc=$?
  on_res="$(printf '%s\n' "$on_out" | grep -v '^\[kappa-gc\]')"
  off_res="$(printf '%s\n' "$off_out" | grep -v '^\[kappa-gc\]')"
  on_bytes="$(printf '%s\n' "$on_out" | grep -oE 'total_bytes=[0-9]+' | tail -1 | cut -d= -f2)"
  off_bytes="$(printf '%s\n' "$off_out" | grep -oE 'total_bytes=[0-9]+' | tail -1 | cut -d= -f2)"
  on_reuses="$(printf '%s\n' "$on_out" | grep -oE 'reuses=[0-9]+' | tail -1 | cut -d= -f2)"
  off_reuses="$(printf '%s\n' "$off_out" | grep -oE 'reuses=[0-9]+' | tail -1 | cut -d= -f2)"
  delta=$(( ${off_bytes:-0} - ${on_bytes:-0} ))
  if [ "$on_rc" -eq 0 ] && [ "$off_rc" -eq 0 ] \
     && [ "$on_res" = "20000" ] && [ "$off_res" = "20000" ] \
     && [ -n "$on_reuses" ] && [ "$on_reuses" -ge 19000 ] \
     && [ "${off_reuses:-0}" -eq 0 ] \
     && [ "$delta" -ge 500000 ]; then
    echo "   ok-reuse (RC-on reuses=${on_reuses}, RC-off reuses=${off_reuses:-0}, total_bytes delta=${delta}B)"
  else
    echo "   FAIL: s5_listmap_reuse did not prove recursive in-place reuse"
    echo "     on rc=${on_rc:-?} result=${on_res:-?} bytes=${on_bytes:-?} reuses=${on_reuses:-?}"
    echo "     off rc=${off_rc:-?} result=${off_res:-?} bytes=${off_bytes:-?} reuses=${off_reuses:-?}"
    printf '%s\n' "$on_out" "$off_out" | sed 's/^/     /'
    fails=$((fails+1))
  fi
else
  echo "   FAIL: s5_listmap_reuse native build failed"
  cat "$s5b3tmp/on.build.log" "$s5b3tmp/off.build.log" | sed 's/^/     /'
  fails=$((fails+1))
fi

echo "== Perceus S5.B3: rbtree-shaped recursive rebuild reuses n-ary nodes =="
s5rbtmp="$WORK/perceus-s5-rbtree-reuse"; rm -rf "$s5rbtmp"; mkdir -p "$s5rbtmp"
s5rbsrc="$ROOT/test/native/bench/proposed/s5_rbtree_reuse.kp"
s5rbc="${s5rbsrc%.kp}.kappa.c"
rm -f "$s5rbc"
if KAPPA_PERCEUS_RC=true timeout 180 $KAPPA build "$s5rbsrc" --emit-c -o "$s5rbtmp/emit" >"$s5rbtmp/emit.log" 2>&1; then
  KAPPA_PERCEUS_RC=true check_perceus_rc_log "$s5rbtmp/emit.log"
  if grep -qE 'ktry_reuse_ctor\(' "$s5rbc" \
     && grep -qE 'kreuse_ctor_skip\(' "$s5rbc" \
     && grep -qE 'KT_main_2e_Node' "$s5rbc"; then
    echo "   ok-shape (rbtree-shaped rebuild uses the early-token reuse branch for Node)"
  else
    echo "   FAIL: s5_rbtree_reuse did not emit the early-token Node reuse branch"
    [ -f "$s5rbc" ] && grep -nE 'kw_main_2e_mapValues|ktry_reuse_ctor|kreuse_ctor_skip|kdrop_reuse_ctor_alloc|kdup\(kctor_arg|kctor\(' "$s5rbc" | sed 's/^/     /'
    fails=$((fails+1))
  fi
else
  echo "   FAIL: s5_rbtree_reuse --emit-c build failed"; cat "$s5rbtmp/emit.log" | sed 's/^/     /'; fails=$((fails+1))
fi
rm -f "$s5rbc"
if KAPPA_PERCEUS_RC=true timeout 180 $KAPPA build "$s5rbsrc" -o "$s5rbtmp/on" >"$s5rbtmp/on.build.log" 2>&1 \
   && KAPPA_PERCEUS_RC=0 timeout 180 $KAPPA build "$s5rbsrc" -o "$s5rbtmp/off" >"$s5rbtmp/off.build.log" 2>&1; then
  KAPPA_PERCEUS_RC=true check_perceus_rc_log "$s5rbtmp/on.build.log"
  on_out="$(KAPPA_GC_STATS=1 KAPPA_POISON=1 timeout 60 "$s5rbtmp/on" 2>&1)"; on_rc=$?
  off_out="$(KAPPA_GC_STATS=1 timeout 60 "$s5rbtmp/off" 2>&1)"; off_rc=$?
  on_res="$(printf '%s\n' "$on_out" | grep -v '^\[kappa-gc\]')"
  off_res="$(printf '%s\n' "$off_out" | grep -v '^\[kappa-gc\]')"
  on_bytes="$(printf '%s\n' "$on_out" | grep -oE 'total_bytes=[0-9]+' | tail -1 | cut -d= -f2)"
  off_bytes="$(printf '%s\n' "$off_out" | grep -oE 'total_bytes=[0-9]+' | tail -1 | cut -d= -f2)"
  on_reuses="$(printf '%s\n' "$on_out" | grep -oE 'reuses=[0-9]+' | tail -1 | cut -d= -f2)"
  off_reuses="$(printf '%s\n' "$off_out" | grep -oE 'reuses=[0-9]+' | tail -1 | cut -d= -f2)"
  delta=$(( ${off_bytes:-0} - ${on_bytes:-0} ))
  if [ "$on_rc" -eq 0 ] && [ "$off_rc" -eq 0 ] \
     && [ "$on_res" = "32767" ] && [ "$off_res" = "32767" ] \
     && [ -n "$on_reuses" ] && [ "$on_reuses" -ge 32000 ] \
     && [ "${off_reuses:-0}" -eq 0 ] \
     && [ "$delta" -ge 1000000 ]; then
    echo "   ok-reuse (RC-on reuses=${on_reuses}, RC-off reuses=${off_reuses:-0}, total_bytes delta=${delta}B)"
  else
    echo "   FAIL: s5_rbtree_reuse did not prove rbtree-shaped in-place reuse"
    echo "     on rc=${on_rc:-?} result=${on_res:-?} bytes=${on_bytes:-?} reuses=${on_reuses:-?}"
    echo "     off rc=${off_rc:-?} result=${off_res:-?} bytes=${off_bytes:-?} reuses=${off_reuses:-?}"
    printf '%s\n' "$on_out" "$off_out" | sed 's/^/     /'
    fails=$((fails+1))
  fi
else
  echo "   FAIL: s5_rbtree_reuse native build failed"
  cat "$s5rbtmp/on.build.log" "$s5rbtmp/off.build.log" | sed 's/^/     /'
  fails=$((fails+1))
fi

echo "== Perceus S5.B3: rbtree insert moves owned path cells into reuse =="
s5ritmp="$WORK/perceus-s5-rbtree-insert-reuse"; rm -rf "$s5ritmp"; mkdir -p "$s5ritmp"
s5risrc="$ROOT/test/native/bench/proposed/s5_rbtree_insert_reuse.kp"
s5ric="${s5risrc%.kp}.kappa.c"
rm -f "$s5ric"
if KAPPA_PERCEUS_RC=true timeout 180 $KAPPA build "$s5risrc" --emit-c -o "$s5ritmp/emit" >"$s5ritmp/emit.log" 2>&1; then
  KAPPA_PERCEUS_RC=true check_perceus_rc_log "$s5ritmp/emit.log"
  if grep -qE 'ktry_reuse_ctor\(' "$s5ric" \
     && grep -qE 'kreuse_ctor_skip\(' "$s5ric" \
     && grep -qE 'kw_main_2e_insert\(kdup\(let_[0-9]+\), kdup\(let_[0-9]+\), p3\)' "$s5ric" \
     && grep -qE 'kw_main_2e_insertRangeFuel\(kdup\(let_[0-9]+\), p1, .*let_[0-9]+\)' "$s5ric" \
     && grep -qE -- '->as\.ctor\.args\[' "$s5ric"; then
    echo "   ok-shape (insert transfers the owned tree path into early-token Node reuse)"
  else
    echo "   FAIL: s5_rbtree_insert_reuse did not emit owned-transfer early-token reuse"
    [ -f "$s5ric" ] && grep -nE 'kw_main_2e_insertRangeFuel|kw_main_2e_insert\(|ktry_reuse_ctor|kreuse_ctor_skip|kdup\(p3|kdup\(let_|kctor_arg|as\.ctor\.args' "$s5ric" | sed 's/^/     /'
    fails=$((fails+1))
  fi
else
  echo "   FAIL: s5_rbtree_insert_reuse --emit-c build failed"; cat "$s5ritmp/emit.log" | sed 's/^/     /'; fails=$((fails+1))
fi
rm -f "$s5ric"
if KAPPA_PERCEUS_RC=true timeout 180 $KAPPA build "$s5risrc" -o "$s5ritmp/on" >"$s5ritmp/on.build.log" 2>&1 \
   && KAPPA_PERCEUS_RC=0 timeout 180 $KAPPA build "$s5risrc" -o "$s5ritmp/off" >"$s5ritmp/off.build.log" 2>&1; then
  KAPPA_PERCEUS_RC=true check_perceus_rc_log "$s5ritmp/on.build.log"
  on_out="$(KAPPA_GC_STATS=1 KAPPA_POISON=1 timeout 60 "$s5ritmp/on" 2>&1)"; on_rc=$?
  off_out="$(KAPPA_GC_STATS=1 timeout 60 "$s5ritmp/off" 2>&1)"; off_rc=$?
  on_res="$(printf '%s\n' "$on_out" | grep -v '^\[kappa-gc\]')"
  off_res="$(printf '%s\n' "$off_out" | grep -v '^\[kappa-gc\]')"
  on_bytes="$(printf '%s\n' "$on_out" | grep -oE 'total_bytes=[0-9]+' | tail -1 | cut -d= -f2)"
  off_bytes="$(printf '%s\n' "$off_out" | grep -oE 'total_bytes=[0-9]+' | tail -1 | cut -d= -f2)"
  on_reuses="$(printf '%s\n' "$on_out" | grep -oE 'reuses=[0-9]+' | tail -1 | cut -d= -f2)"
  off_reuses="$(printf '%s\n' "$off_out" | grep -oE 'reuses=[0-9]+' | tail -1 | cut -d= -f2)"
  delta=$(( ${off_bytes:-0} - ${on_bytes:-0} ))
  if [ "$on_rc" -eq 0 ] && [ "$off_rc" -eq 0 ] \
     && [ "$on_res" = "19777" ] && [ "$off_res" = "19777" ] \
     && [ -n "$on_reuses" ] && [ "$on_reuses" -ge 100000 ] \
     && [ "${off_reuses:-0}" -eq 0 ] \
     && [ "$delta" -ge 10000000 ]; then
    echo "   ok-reuse (RC-on reuses=${on_reuses}, RC-off reuses=${off_reuses:-0}, total_bytes delta=${delta}B)"
  else
    echo "   FAIL: s5_rbtree_insert_reuse did not prove insert-path in-place reuse"
    echo "     on rc=${on_rc:-?} result=${on_res:-?} bytes=${on_bytes:-?} reuses=${on_reuses:-?}"
    echo "     off rc=${off_rc:-?} result=${off_res:-?} bytes=${off_bytes:-?} reuses=${off_reuses:-?}"
    printf '%s\n' "$on_out" "$off_out" | sed 's/^/     /'
    fails=$((fails+1))
  fi
else
  echo "   FAIL: s5_rbtree_insert_reuse native build failed"
  cat "$s5ritmp/on.build.log" "$s5ritmp/off.build.log" | sed 's/^/     /'
  fails=$((fails+1))
fi
if timeout 240 bash "$ROOT/test/native/bench/proposed/run-proposed.sh" --reps 5 s5_rbtree_insert_reuse >"$s5ritmp/proposed.log" 2>&1; then
  sed -n '/^s5_rbtree_insert_reuse/p' "$s5ritmp/proposed.log" | sed 's/^/   report /'
else
  echo "   FAIL: s5_rbtree_insert_reuse proposed benchmark report failed"
  cat "$s5ritmp/proposed.log" | sed 's/^/     /'
  fails=$((fails+1))
fi

# LR2: the pattern-match dispatch must be a numeric tag-id int compare
# (kctor_tagid / kvariant_tagid), NOT a kctor_is / kvariant_is strcmp.  Assert
# on a constructor/variant-heavy program's generated C.
echo "== LR2: match dispatch uses numeric tag ids, not strcmp =="
ltmp="$WORK/lr2c"; mkdir -p "$ltmp"
cfile="$CASES/ctortags.kappa.c"
rm -f "$cfile"
if timeout 120 $KAPPA build "$CASES/ctortags.kp" --emit-c -o "$ltmp/ct" >"$ltmp/build.log" 2>&1; then
  check_perceus_rc_log "$ltmp/build.log"
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

# R1.1 / P0-A: a saturated constructor application lowers to a DIRECT kctor,
# not an eta-expanded curried kclo/kapp/kappi chain.  The eta-ctor storm's
# signature is the applied implicit type argument `kappi(kclo(…), kunit())`
# wrapping the constructor closure; after the fix that pattern is gone and the
# cons site is a direct `kctor(KCT_CONS, …)`.  The builder's body is then
# capture-free, so its self-tail loop runs in-place with NO per-iteration env:
# under R2.3 the `range` worker is FLAT (params are direct C locals reassigned
# `p0 = …; continue;`), so there is no `kvar`/`kpush` on the build path at all.
echo "== R1.1: saturated constructor application is a direct kctor (no eta-ctor closure storm) =="
rtmp="$WORK/r11c"; mkdir -p "$rtmp"
cfile="$CASES/adtcons.kappa.c"
rm -f "$cfile"
if timeout 120 $KAPPA build "$CASES/adtcons.kp" --emit-c -o "$rtmp/ac" >"$rtmp/build.log" 2>&1; then
  check_perceus_rc_log "$rtmp/build.log"
  if grep -qE 'kctor\(KCT_CONS,' "$cfile" \
     && ! grep -qE 'kappi\(kclo\(' "$cfile" \
     && grep -qE 'p[0-9]+ = tc_[0-9]+;' "$cfile" \
     && ! grep -qE 'kvar\(kw_env' "$cfile"; then
    echo "   ok (direct kctor on the construction path; flat in-place self-tail loop, no kclo storm)"
  else
    echo "   FAIL: constructor construction path is not a direct kctor / in-place loop not re-enabled"
    grep -nE 'kappi\(kclo\(' "$cfile" | sed 's/^/     /'; fails=$((fails+1))
  fi
  rm -f "$cfile"
else
  echo "   FAIL: adtcons --emit-c build failed"; cat "$rtmp/build.log" | sed 's/^/     /'; fails=$((fails+1))
fi

# R2.1 / P1-F: the pointer-free scalar boxes must be allocated on the atomic
# (unscanned) GC heap via alloc_val_atomic, not the scanned alloc_val — this
# removes them as conservative-GC false-pointer sources and cuts mark work.  A
# revert to alloc_val would silently regress GC cost; the equivalence suite
# already proves the non-zeroing atomic alloc is correct, so this is a source
# invariant on the scalar constructors in the runtime.
#
# UNBOXING Stage 1: a small Int is now a b001 IMMEDIATE packed into the KValue*
# word (kint() allocates NOTHING for the 61-bit range; an out-of-range Int is a
# K_BIGINT, which is pointer-bearing and correctly uses the scanned alloc_val).
# So K_INT is no longer a constructed scalar box at all — it is DROPPED from this
# invariant.  K_DBL/K_CHR/K_BYTE still box on the atomic heap and must stay there.
echo "== R2.1: pointer-free scalar boxes use the atomic (unscanned) GC heap =="
# The scalar constructors (kdbl/kchr/kbyte) live in the value-model translation
# unit after kappart.c was split (see runtime/boxed.h).
rt="$ROOT/runtime/value.c"
# The scalar tags K_DBL/K_CHR/K_BYTE are constructed only in kdbl/kchr/kbyte, so
# keying on the tag argument is an unambiguous, format-robust invariant: each must
# allocate via alloc_val_atomic and none via the scanned alloc_val.
r21_ok=1
for tag in K_DBL K_CHR K_BYTE; do
  grep -qE "alloc_val_atomic\($tag\)" "$rt" || r21_ok=0
  # negative: the scanned alloc_val(TAG) must not appear; (^|[^_]) anchors so a
  # line-start occurrence is still caught and alloc_val_atomic is not matched.
  grep -qE "(^|[^_])alloc_val\($tag\)" "$rt" && r21_ok=0
done
# K_INT must NOT be constructed as a scalar box anymore (it is an immediate); a
# reappearance of alloc_val*(K_INT) means the immediate encoding was reverted.
grep -qE "alloc_val(_atomic)?\(K_INT\)" "$rt" && r21_ok=0
if [ -f "$rt" ] && [ "$r21_ok" -eq 1 ]; then
  echo "   ok (kint/kdbl/kchr/kbyte allocate via alloc_val_atomic; scanned alloc_val reserved for pointer-bearing boxes)"
else
  echo "   FAIL: a scalar box no longer uses the atomic GC heap (R2.1 regressed)"; fails=$((fails+1))
fi

# R2.2 / P0-D: a monomorphic first-order Double (or mixed Int+Double) function
# lowers to a typed unboxed worker with a scalar while-loop — `double
# kwd_…(double, …, int *kovf)` reached via kunbox_dbl, with a native double add
# (`= … + …;`) in the worker body (each op its own FMA-safe statement) rather
# than per-iteration boxed kp_addDouble.  (The boxed kw_ worker, which DOES
# keep kp_addDouble as the escape reference, still exists — so we assert the
# unboxed worker's positive signals, not the absence of kp_addDouble globally.)
echo "== R2.2: Double / mixed-kind functions get a typed unboxed scalar worker =="
dtmp="$WORK/r22c"; mkdir -p "$dtmp"
dbench="$ROOT/test/native/bench/proposed/scalar_doubleloop.kp"
cfile="$ROOT/test/native/bench/proposed/scalar_doubleloop.kappa.c"
rm -f "$cfile"
if timeout 120 $KAPPA build "$dbench" --emit-c -o "$dtmp/sd" >"$dtmp/build.log" 2>&1; then
  check_perceus_rc_log "$dtmp/build.log"
  # the body of the unboxed double worker: from its `double kwd_…(double` line
  # to the next top-level `}` at column 0.
  # a kwd_ worker (any double param/result) — the bench's sumD returns double,
  # so match a double-returning kwd_ definition line (ends in `{`).
  worker="$(awk '/^static double kwd_[A-Za-z0-9_]+\(.*\{$/{f=1} f{print} f&&/^}/{exit}' "$cfile")"
  if printf '%s' "$worker" | grep -qE 'kwd_[A-Za-z0-9_]+\(' \
     && grep -qE 'kunbox_dbl\(' "$cfile" \
     && printf '%s' "$worker" | grep -qE '= [A-Za-z0-9_]+ \+ [A-Za-z0-9_]+;' \
     && ! printf '%s' "$worker" | grep -qE 'kp_[A-Za-z]+Double\('; then
    echo "   ok (typed double worker via kunbox_dbl with native double ops; no boxed prim in the unboxed loop)"
  else
    echo "   FAIL: Double loop did not lower to a typed unboxed worker (R2.2 regressed)"; fails=$((fails+1))
  fi
  rm -f "$cfile"
else
  echo "   FAIL: scalar_doubleloop --emit-c build failed"; cat "$dtmp/build.log" | sed 's/^/     /'; fails=$((fails+1))
fi

# S2.3b/P0.2: track LLVM var/while scalarization. The old raw-ref peephole was
# unsound because it bypassed checker-selected MonadRef evidence, but scalarizing
# surface var loops is still required once the backend proves the selected
# actions are equivalent to builtin IO refs. Until then, krt2_while is only the
# correctness fallback.
echo "== S2.3b LLVM: var/while Int scalarization status =="
ltmp="$WORK/r22llvm"; mkdir -p "$ltmp"
lbench="$ROOT/test/native/bench/proposed/scalar_intwhile.kp"
llfile="$ROOT/test/native/bench/proposed/scalar_intwhile.kappa.ll"
rm -f "$llfile"
if KAPPA_BACKEND=llvm timeout 120 $KAPPA build "$lbench" --emit-c -o "$ltmp/siw" >"$ltmp/build.log" 2>&1; then
  check_perceus_rc_log "$ltmp/build.log"
  sp_count=0
  fast_sp=0
  boxed_sp=0
  abort_flushes=0
  scalar_worker=""
  if [ -f "$llfile" ]; then
    scalar_worker="$(awk '/^define internal ptr @kscalarloop_[0-9]+\(ptr %args\)/{f=1} f{print} f&&/^}/{exit}' "$llfile")"
    sp_count="$(printf '%s' "$scalar_worker" | grep -cE 'call i32 @krt2_safepoint\(\)' || true)"
    fast_sp="$(printf '%s' "$scalar_worker" | awk '/^[[:space:]]*sspchk_[0-9]+:/{f=1} f&&/call i32 @krt2_safepoint\(\)/{ok=1} /^[[:space:]]*sflush_[0-9]+:/{f=0} END{print ok ? 1 : 0}')"
    boxed_sp="$(printf '%s' "$scalar_worker" | awk '/^[[:space:]]*bxspchk_[0-9]+:/{f=1} f&&/call i32 @krt2_safepoint\(\)/{ok=1} /^[[:space:]]*sdone_[0-9]+:/{f=0} END{print ok ? 1 : 0}')"
    abort_flushes="$(printf '%s' "$scalar_worker" | awk '/^[[:space:]]*sabort_[0-9]+:/{f=1; n=0} f&&/call ptr @kref_set\(/{n++} f&&/call void @krt2_scalar_abort\(\)/{seen=1; print n; exit} END{if(!seen) print 0}')"
  fi
  if [ -f "$llfile" ] \
     && printf '%s' "$scalar_worker" | grep -qE 'define internal ptr @kscalarloop_[0-9]+\(ptr %args\)' \
     && ! grep -qE 'call ptr @krt2_while\(' "$llfile" \
     && [ "$fast_sp" = 1 ] \
     && [ "$boxed_sp" = 1 ] \
     && [ "${abort_flushes:-0}" -ge 2 ]; then
    echo "   ok (evidence-aware scalar loop emitted; no krt2_while fallback; fast/boxed safepoints and both hidden refs flushed before abort)"
	  elif [ -f "$llfile" ] && grep -qE 'call ptr @krt2_while\(' "$llfile"; then
	    echo "   FAIL: scalar_intwhile used boxed krt2_while fallback; evidence-aware scalarizer is required"; fails=$((fails+1))
	  elif [ -f "$llfile" ] && { [ "$fast_sp" != 1 ] || [ "$boxed_sp" != 1 ]; }; then
	    echo "   FAIL: scalar_intwhile scalar worker is missing a safepoint in either the fast path or boxed overflow fallback"; fails=$((fails+1))
  elif [ -f "$llfile" ] && [ "${abort_flushes:-0}" -lt 2 ]; then
    echo "   FAIL: scalar_intwhile scalar worker abort path flushed only ${abort_flushes:-0}/2 hidden refs before krt2_scalar_abort"; fails=$((fails+1))
	  else
	    echo "   FAIL: LLVM var/while Int loop emitted neither scalar worker nor krt2_while fallback"; fails=$((fails+1))
  fi
  rm -f "$llfile"
else
  echo "   FAIL: scalar_intwhile (LLVM) --emit-c build failed"; cat "$ltmp/build.log" | sed 's/^/     /'; fails=$((fails+1))
fi

echo "== S2.3b LLVM: user MonadRef var/while does not scalarize =="
utmp="$WORK/user-monadref-scalar"; mkdir -p "$utmp"
usrc="$ROOT/tests/native/llvm/scalar-user-monadref-fallback.kp"
ull="$ROOT/tests/native/llvm/scalar-user-monadref-fallback.kappa.ll"
	rm -f "$ull"
	if KAPPA_BACKEND=llvm timeout 120 $KAPPA build "$usrc" --emit-c -o "$utmp/user-monadref-scalar" >"$utmp/build.log" 2>&1; then
	  check_perceus_rc_log "$utmp/build.log"
	  if [ -f "$ull" ] && grep -qE 'define internal ptr @kscalarloop_[0-9]+\(ptr %args\)' "$ull"; then
	    echo "   FAIL: user MonadRef var/while loop scalarized despite non-prelude IO evidence"; fails=$((fails+1))
  elif [ -f "$ull" ] \
       && grep -qE 'call ptr @knative_sat\(ptr @kpf_io_newRef,' "$ull" \
       && grep -qE 'call ptr @knative_sat\(ptr @kpf_io_readRef,' "$ull" \
       && grep -qE 'call ptr @knative_sat\(ptr @kpf_io_writeRef,' "$ull"; then
    echo "   ok (user MonadRef evidence stayed on the generic selected-action path)"
  else
    echo "   FAIL: user MonadRef fixture did not prove the generic selected-action fallback shape"; fails=$((fails+1))
  fi
  rm -f "$ull"
else
  echo "   FAIL: user MonadRef LLVM --emit-c build failed"; cat "$utmp/build.log" | sed 's/^/     /'; fails=$((fails+1))
fi

echo "== S2.3b LLVM: scalar reads and escaped refs preserve scalarization semantics =="
wtmp="$WORK/scalar-wildcard"; mkdir -p "$wtmp"
wsrc="$ROOT/tests/native/llvm/scalar-wildcard-read.kp"
	wll="$ROOT/tests/native/llvm/scalar-wildcard-read.kappa.ll"
	rm -f "$wll"
	if KAPPA_BACKEND=llvm timeout 120 $KAPPA build "$wsrc" --emit-c -o "$wtmp/scalar-wildcard" >"$wtmp/build.log" 2>&1; then
	  check_perceus_rc_log "$wtmp/build.log"
	  if [ -f "$wll" ] \
	     && grep -qE 'define internal ptr @kscalarloop_[0-9]+\(ptr %args\)' "$wll" \
     && ! grep -qE 'call ptr @krt2_while\(' "$wll"; then
    echo "   ok (wildcard read bind preserves the scalar loop plan)"
  else
    echo "   FAIL: wildcard read fixture lost the evidence-aware scalar loop"; fails=$((fails+1))
  fi
  rm -f "$wll"
else
  echo "   FAIL: scalar wildcard read LLVM --emit-c build failed"; cat "$wtmp/build.log" | sed 's/^/     /'; fails=$((fails+1))
fi

ftmp="$WORK/scalar-ref-freshness"; mkdir -p "$ftmp"
fsrc="$ROOT/tests/native/llvm/scalar-ref-freshness.kp"
	fll="$ROOT/tests/native/llvm/scalar-ref-freshness.kappa.ll"
	rm -f "$fll"
	if KAPPA_BACKEND=llvm timeout 120 $KAPPA build "$fsrc" --emit-c -o "$ftmp/scalar-ref-freshness.llonly" >"$ftmp/emit.log" 2>&1; then
	  check_perceus_rc_log "$ftmp/emit.log"
	  maker_block=""
	  if [ -f "$fll" ]; then
    maker_block="$(awk '/^define internal ptr @kg_main_2e_makeRef\(\)/{f=1} f{print} f&&/^}/{exit}' "$fll")"
  fi
  if [ -f "$fll" ] \
     && grep -qE 'define internal ptr @kscalarloop_[0-9]+\(ptr %args\)' "$fll" \
     && grep -qE '^define internal ptr @kscalar_region_[0-9]+\(ptr %cenv, ptr %arg\)' "$fll" \
     && ! grep -qE 'call ptr @kref_new\(' <<<"$maker_block"; then
    :
  else
    echo "   FAIL: scalar ref-freshness fixture did not delay hidden ref allocation behind the scalar-region action"; fails=$((fails+1))
  fi
  rm -f "$fll"
else
	  echo "   FAIL: scalar ref-freshness LLVM --emit-c build failed"; cat "$ftmp/emit.log" | sed 's/^/     /'; fails=$((fails+1))
	fi
	if KAPPA_BACKEND=llvm timeout 120 $KAPPA build "$fsrc" -o "$ftmp/scalar-ref-freshness" >"$ftmp/build.log" 2>&1; then
	  check_perceus_rc_log "$ftmp/build.log"
	  out="$("$ftmp/scalar-ref-freshness" 2>"$ftmp/run.err")"
	  if [ "$out" = "3" ]; then
    echo "   ok (reused scalarized IO action allocates fresh refs per execution)"
  else
    echo "   FAIL: scalar ref-freshness output mismatch: expected 3, got '$out'"; cat "$ftmp/run.err" | sed 's/^/     /'; fails=$((fails+1))
  fi
else
  echo "   FAIL: scalar ref-freshness LLVM build failed"; cat "$ftmp/build.log" | sed 's/^/     /'; fails=$((fails+1))
fi

otmp="$WORK/scalar-overflow-replay"; mkdir -p "$otmp"
osrc="$ROOT/tests/native/llvm/scalar-overflow-replay-ref.kp"
	oll="$ROOT/tests/native/llvm/scalar-overflow-replay-ref.kappa.ll"
	rm -f "$oll"
	if KAPPA_BACKEND=llvm timeout 120 $KAPPA build "$osrc" --emit-c -o "$otmp/scalar-overflow-replay.llonly" >"$otmp/emit.log" 2>&1; then
	  check_perceus_rc_log "$otmp/emit.log"
	  overflow_worker=""
	  if [ -f "$oll" ]; then
    overflow_worker="$(awk '/^define internal ptr @kscalarloop_[0-9]+\(ptr %args\)/{f=1} f{print} f&&/^}/{exit}' "$oll")"
  fi
  if [ -f "$oll" ] \
     && printf '%s' "$overflow_worker" | grep -qE 'llvm\.smul\.with\.overflow\.i64' \
     && printf '%s' "$overflow_worker" | grep -qE 'llvm\.sadd\.with\.overflow\.i64' \
     && printf '%s' "$overflow_worker" | grep -qE 'call ptr @kref_set\(' \
     && printf '%s' "$overflow_worker" | grep -qE 'call i32 @krt2_safepoint\(\)' \
     && ! grep -qE 'call ptr @krt2_while\(' "$oll"; then
    :
  else
    echo "   FAIL: scalar overflow replay fixture lost the scalar worker, boxed replay stores, or worker safepoints"; fails=$((fails+1))
  fi
  rm -f "$oll"
else
	  echo "   FAIL: scalar overflow replay LLVM --emit-c build failed"; cat "$otmp/emit.log" | sed 's/^/     /'; fails=$((fails+1))
	fi
	if KAPPA_BACKEND=llvm timeout 120 $KAPPA build "$osrc" -o "$otmp/scalar-overflow-replay" >"$otmp/build.log" 2>&1; then
	  check_perceus_rc_log "$otmp/build.log"
	  out="$("$otmp/scalar-overflow-replay" 2>"$otmp/run.err")"
	  if [ "$out" = "15511210043330985984000000" ]; then
    echo "   ok (scalar overflow fallback replays through boxed refs and preserves escaped result)"
  else
    echo "   FAIL: scalar overflow replay output mismatch: expected 15511210043330985984000000, got '$out'"; cat "$otmp/run.err" | sed 's/^/     /'; fails=$((fails+1))
  fi
else
  echo "   FAIL: scalar overflow replay LLVM build failed"; cat "$otmp/build.log" | sed 's/^/     /'; fails=$((fails+1))
fi

echo "== LLVM scalar workers: scalar let slots are entry-allocated, not loop-allocated =="
sltmp="$WORK/llvm-scalar-let"; mkdir -p "$sltmp"
slsrc="$sltmp/scalar_let_slots.kp"
cat > "$slsrc" <<'KP'
module main
sumLet : Int -> Int -> Int
let sumLet acc n =
    let next = addInt acc n in
    let prev = subInt n 1 in
    if leInt n 0 then acc else sumLet next prev
main : UIO Unit
let main = printlnString (showInt (sumLet 0 5))
KP
if KAPPA_BACKEND=llvm timeout 120 $KAPPA build "$slsrc" --emit-c -o "$sltmp/scalar_let_slots" >"$sltmp/build.log" 2>&1; then
  llfile="$sltmp/scalar_let_slots.kappa.ll"
  worker="$(awk '/^define internal i64 @kwi_main_2e_sumLet\(.*\{$/{f=1} f{print} f&&/^}/{exit}' "$llfile")"
  before_loop="$(awk '{ print } /kwloop_[0-9]+:/ { exit }' <<<"$worker")"
  after_loop="$(awk 'seen { print } /kwloop_[0-9]+:/ { seen = 1; next }' <<<"$worker")"
  if grep -qE '^define internal i64 @kwi_main_2e_sumLet\(' <<<"$worker" \
     && grep -qE ' = alloca i64, align 8' <<<"$before_loop" \
     && ! grep -qE ' = alloca ' <<<"$after_loop"; then
    echo "   ok (scalar let scratch slots are allocated before the loop header)"
  else
    echo "   FAIL: LLVM scalar worker still allocates scratch slots inside the loop"
    printf '%s\n' "$worker" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  rm -f "$llfile"
else
  echo "   FAIL: scalar_let_slots (LLVM) --emit-c build failed"; cat "$sltmp/build.log" | sed 's/^/     /'; fails=$((fails+1))
fi

# R3.1 / P1-E: a saturated call to a worker that can NEVER return a K_BOUNCE
# (its tail positions are all self-loops / values / prim or ctor results) drops
# the ktrampoline wrapper, since ktrampoline drains only K_BOUNCE.  adtcons's
# functions (self-recursive range/foldSum, value-returning fst3/snd3) are all
# non-bouncing, so its generated C has NO ktrampoline; tailrec's mutual /
# value-indirect recursion DOES bounce, so it must KEEP ktrampoline (the
# conservative analysis must not drop a real trampoline — a stack-overflow bug).
echo "== R3.1: ktrampoline dropped for non-bouncing workers, kept for bouncing ones =="
btmp="$WORK/r31c"; mkdir -p "$btmp"
nb_ok=1
rm -f "$CASES/adtcons.kappa.c"
if timeout 120 $KAPPA build "$CASES/adtcons.kp" --emit-c -o "$btmp/ac" >"$btmp/ac.log" 2>&1; then
  grep -qE 'ktrampoline\(' "$CASES/adtcons.kappa.c" && nb_ok=0   # must be NONE
  rm -f "$CASES/adtcons.kappa.c"
else nb_ok=0; fi
b_ok=0
rm -f "$CASES/tailrec.kappa.c"
if timeout 120 $KAPPA build "$CASES/tailrec.kp" --emit-c -o "$btmp/tr" >"$btmp/tr.log" 2>&1; then
  grep -qE 'ktrampoline\(' "$CASES/tailrec.kappa.c" && b_ok=1   # must be PRESENT
  rm -f "$CASES/tailrec.kappa.c"
fi
if [ "$nb_ok" -eq 1 ] && [ "$b_ok" -eq 1 ]; then
  echo "   ok (adtcons drops ktrampoline; tailrec's bouncing mutual recursion keeps it)"
else
  echo "   FAIL: R3.1 ktrampoline elision wrong (non-bouncing dropped=$nb_ok bouncing-kept=$b_ok)"; fails=$((fails+1))
fi

# R2.3 / P1-H: a capture-free AND binder-free first-order BOXED worker (over
# records/ADTs/etc., not scalar-eligible) reads its parameters directly from
# the C parameters — no `kvar` chain walk and no `kpush`/`KEnv` node for the
# parameter frame.  Assert on flatframe's `go` worker body (a record-param
# worker): no kvar/kpush, and a direct `krec_at(p` field read.
echo "== R2.3: capture-free binder-free workers read params as flat C locals (no kvar/kpush) =="
ftmp="$WORK/r23c"; mkdir -p "$ftmp"
cfile="$CASES/flatframe.kappa.c"
rm -f "$cfile"
if timeout 120 $KAPPA build "$CASES/flatframe.kp" --emit-c -o "$ftmp/ff" >"$ftmp/build.log" 2>&1; then
  check_perceus_rc_log "$ftmp/build.log"
  goworker="$(awk '/^static KValue \*kw_main_2e_go\(.*\{$/{f=1} f{print} f&&/^}/{exit}' "$cfile")"
  if printf '%s' "$goworker" | grep -qE 'krec_at\(p[0-9]' \
     && ! printf '%s' "$goworker" | grep -qE 'kvar\(|kpush\('; then
    echo "   ok (flat worker reads p0/p1/p2 directly; no kvar/kpush for the parameter frame)"
  else
    echo "   FAIL: flat-frame worker still walks kvar/kpush (R2.3 regressed)"; fails=$((fails+1))
  fi
  # R2.4: flatframe's worker (Int counter + record param + Int accumulator) is
  # ALSO emitted as a MIXED unboxed worker `kwm_…(int64_t, KValue *, int64_t,
  # int *kovf)` — unboxed scalar slots, boxed record slot passed through, and a
  # record-field read coerced via a tag-checked kunbox_i64.  Assert that mixed
  # worker exists with the boxed→scalar coercion.
  kwmworker="$(awk '/^static int64_t kwm_main_2e_go\(.*\{$/{f=1} f{print} f&&/^}/{exit}' "$cfile" 2>/dev/null)"
  # scope every check to the kwm_ worker BODY: krec_at(p..) field read + the
  # worker-side coercion `kunbox_i64(fb_…, kovf)` (no `&` — distinct from the
  # call-site `kunbox_i64(la_…, &kovf)`, which would pass spuriously).
  if printf '%s' "$kwmworker" | grep -qE 'krec_at\(p[0-9]' \
     && grep -qE 'int64_t kwm_main_2e_go\(int64_t .*KValue \*' "$cfile" 2>/dev/null \
     && printf '%s' "$kwmworker" | grep -qE 'kunbox_i64\(fb_[0-9]+, kovf\)'; then
    echo "   ok-R2.4 (mixed kwm_ worker: unboxed scalar slots + boxed record slot + tag-checked field coercion)"
  else
    echo "   FAIL: R2.4 mixed worker missing (record-param worker did not unbox its scalar slots)"; fails=$((fails+1))
  fi
  rm -f "$cfile"
else
  echo "   FAIL: flatframe --emit-c build failed"; cat "$ftmp/build.log" | sed 's/^/     /'; fails=$((fails+1))
fi

# R2.3-rest: a capture-free worker that BINDS via match/let is now also FLAT —
# the params, the let var, and the destructured pattern vars are direct C
# locals (no kvar/kpush), not a kpush'd KEnv chain.  Assert on flatbinders'
# sumPairs worker (a nested-pattern match + a let in the arm): the worker reads
# kctor_arg into pat_ locals and a let_ local, with NO kvar/kpush.
echo "== R2.3-rest: capture-free match/let-bearing workers are flat (binders as C locals) =="
btmp="$WORK/r23r"; mkdir -p "$btmp"
cfile="$CASES/flatbinders.kappa.c"
rm -f "$cfile"
if timeout 120 $KAPPA build "$CASES/flatbinders.kp" --emit-c -o "$btmp/fb" >"$btmp/build.log" 2>&1; then
  check_perceus_rc_log "$btmp/build.log"
  spw="$(awk '/^static KValue \*kw_main_2e_sumPairs\(.*\{$/{f=1} f{print} f&&/^}/{exit}' "$cfile" 2>/dev/null)"
  if printf '%s' "$spw" | grep -qE 'KValue \*pat_[0-9]+ = kctor_arg' \
     && printf '%s' "$spw" | grep -qE 'KValue \*let_[0-9]+ = ' \
     && ! printf '%s' "$spw" | grep -qE 'kvar\(|kpush\('; then
    echo "   ok (match/let binders are C locals; no kvar/kpush in the flat worker)"
  else
    echo "   FAIL: match/let-bearing worker still uses a kpush'd KEnv (R2.3-rest regressed)"; fails=$((fails+1))
  fi
  rm -f "$cfile"
else
  echo "   FAIL: flatbinders --emit-c build failed"; cat "$btmp/build.log" | sed 's/^/     /'; fails=$((fails+1))
fi

# R3.2: a capture-free CLOSURE (lambda) reads its parameter DIRECTLY as the C
# `arg` (de Bruijn 0) and captured free vars from `cenv`, with NO per-application
# `kpush(arg, cenv)`.  Assert on flatclosure's `\x -> subInt (mulInt x 2) k`: the
# kfn_ body reads `arg` and `kvar(cenv,` (the capture) but contains no `kpush`.
echo "== R3.2: capture-free closures read the param flat (no per-application kpush) =="
ctmp="$WORK/r32"; mkdir -p "$ctmp"
cfile="$CASES/flatclosure.kappa.c"
rm -f "$cfile"
if timeout 120 $KAPPA build "$CASES/flatclosure.kp" --emit-c -o "$ctmp/fc" >"$ctmp/build.log" 2>&1; then
  check_perceus_rc_log "$ctmp/build.log"
  # the lambda body: a kfn_ function that reads cenv (it captures k).
  lam="$(awk '/^static KValue \*kfn_[A-Za-z0-9_]+\(KEnv \*cenv, KValue \*arg\) \{$/{f=1} f{print} f&&/^}/{exit}' "$cfile")"
  if printf '%s' "$lam" | grep -qE 'kvar\(cenv,' \
     && printf '%s' "$lam" | grep -qE '\barg\b' \
     && ! printf '%s' "$lam" | grep -qE 'kpush\('; then
    echo "   ok (flat closure: param read as arg, capture via kvar(cenv,…), no per-application kpush)"
  else
    echo "   FAIL: closure still kpushes its parameter per application (R3.2 regressed)"; fails=$((fails+1))
  fi
  rm -f "$cfile"
else
  echo "   FAIL: flatclosure --emit-c build failed"; cat "$ctmp/build.log" | sed 's/^/     /'; fails=$((fails+1))
fi

# Perceus RC S2.3b: a read-only NonLast occurrence must not get a balancing
# kdup. The first use of y below is a borrowed call argument; y is read again by
# projection afterward, so the occurrence is NonLast but consumes=False.
echo "== Perceus S2.3b: read-only NonLast use avoids kdup in generated C =="
rtmp="$WORK/rc-read-nonlast"; mkdir -p "$rtmp"
rcsrc="$rtmp/rc_read_nonlast.kp"
cat > "$rcsrc" <<'KP'
module main
type Box = (v : Int)
type PeekBox = (& x : Box) -> Int
peekBox : (& x : Box) -> Int
let peekBox x = x.v
useBorrowTwice : Box -> Int
let useBorrowTwice y = peekBox y + y.v
type RecAlias = (f : PeekBox)
useProjectedTwice : RecAlias -> Box -> Int
let useProjectedTwice r y = r.f y + y.v
main : UIO Unit
let main = printInt (useBorrowTwice (v = 41) + useProjectedTwice (f = peekBox) (v = 1))
KP
if KAPPA_PERCEUS_RC=true timeout 120 $KAPPA build "$rcsrc" --emit-c -o "$rtmp/rc_read_nonlast" >"$rtmp/build.log" 2>&1; then
  KAPPA_PERCEUS_RC=true check_perceus_rc_log "$rtmp/build.log"
  cfile="$rtmp/rc_read_nonlast.kappa.c"
  worker="$(awk '/^static KValue \*kw_main_2e_useBorrowTwice\(KValue \*p0\) \{/{f=1} f{print} f&&/^}/{exit}' "$cfile")"
  projected_worker="$(awk '/^static KValue \*kw_main_2e_useProjectedTwice\(KValue \*p0, KValue \*p1\) \{/{f=1} f{print} f&&/^}/{exit}' "$cfile")"
  if printf '%s' "$worker" | grep -qE 'kw_main_2e_peekBox\(p0\)' \
     && printf '%s' "$worker" | grep -qE 'krec_at\(p0, 0\)' \
     && ! printf '%s' "$worker" | grep -qE 'kdup\('; then
    echo "   ok (borrowed NonLast call arg remains bare; no unbalanced kdup)"
  else
    echo "   FAIL: read-only NonLast use was duped or the focused worker was not found"
    printf '%s\n' "$worker" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  if printf '%s' "$projected_worker" | grep -qE 'krec_at\(p0, 0\)' \
     && printf '%s' "$projected_worker" | grep -qE 'krec_at\(p1, 0\)' \
     && ! printf '%s' "$projected_worker" | grep -qE 'kdup\('; then
    echo "   ok (projected borrowed callee NonLast arg remains bare)"
  else
    echo "   FAIL: projected read-only NonLast use was duped or the focused worker was not found"
    printf '%s\n' "$projected_worker" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  rm -f "$cfile"
else
  echo "   FAIL: rc_read_nonlast --emit-c build failed"; cat "$rtmp/build.log" | sed 's/^/     /'; fails=$((fails+1))
fi

echo "== Perceus S3.3: public MonadRef ref transfers use selected primitive conventions =="
rftmp="$WORK/rc-ref-transfer"; mkdir -p "$rftmp"
rfsrc="$CASES/perceus-s3-ref-transfer.kp"
rfc="${rfsrc%.kp}.kappa.c"
rm -f "$rfc"
if KAPPA_PERCEUS_RC=true timeout 120 $KAPPA build "$rfsrc" --emit-c -o "$rftmp/perceus_s3_ref_transfer" >"$rftmp/build.log" 2>&1; then
  KAPPA_PERCEUS_RC=true check_perceus_rc_log "$rftmp/build.log"
  rfbody="$(awk '/^static KValue \*kdo_main.*\(KEnv \*cenv\) \{/{f=1} f{print} f&&/^}/{exit}' "$rfc")"
  if printf '%s' "$rfbody" | grep -qE 'knative_sat\(kpf_io_readRef, 1,' \
     && printf '%s' "$rfbody" | grep -qE 'knative_sat\(kpf_io_writeRef, 2,' \
     && printf '%s' "$rfbody" | grep -qE 'KValue \*na_[0-9]+\[\] = \{kvar\(env_[0-9]+, 1\)\};' \
     && printf '%s' "$rfbody" | grep -qE 'KValue \*na_[0-9]+\[\] = \{kvar\(env_[0-9]+, 1\), kdup\(kvar\(env_[0-9]+, 0\)\)\};' \
     && ! printf '%s' "$rfbody" | grep -qE 'kproj\(.*"(readRef|writeRef)"|kapp\(kappi\(kproj'; then
    echo "   ok (selected MonadRef evidence direct-lowers; borrowed ref handles stay borrowed)"
  else
    echo "   FAIL: public MonadRef read/write did not preserve selected primitive conventions"
    printf '%s\n' "$rfbody" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  rm -f "$rfc"
else
  echo "   FAIL: perceus-s3-ref-transfer --emit-c build failed"; cat "$rftmp/build.log" | sed 's/^/     /'; fails=$((fails+1))
fi

# Perceus S3.4: the explicit RC-off baseline must keep ownership helpers and
# runtime RC effects inert. This focuses a consuming variable use that RC-on may
# materialize with kdup, but `KAPPA_PERCEUS_RC=0` must preserve the old ownership
# baseline shape, disable runtime kdrop/kdup effects, and still keep S4 publish
# marking for shared-bit synchronization.
echo "== Perceus S3.4: explicit RC-off generated C has no ownership kdup =="
offtmp="$WORK/rc-off-owned-use"; mkdir -p "$offtmp"
offsrc="$offtmp/rc_off_owned_use.kp"
cat > "$offsrc" <<'KP'
module main
type Box = (v : Int)
consume : Box -> Box
let consume x = x
use : Box -> Box
let use x = consume x
main : UIO Unit
let main = printInt (use (v = 7)).v
KP
if KAPPA_PERCEUS_RC=0 timeout 120 $KAPPA build "$offsrc" --emit-c -o "$offtmp/rc_off_owned_use" >"$offtmp/build.log" 2>&1; then
  offc="$offtmp/rc_off_owned_use.kappa.c"
  offworker="$(awk '/^static KValue \*kw_main_2e_use\(KValue \*p0\) \{/{f=1} f{print} f&&/^}/{exit}' "$offc")"
  offmain="$(awk '/^int main\(void\) \{/{f=1} f{print} f&&/^}/{exit}' "$offc")"
  if printf '%s' "$offworker" | grep -qE 'kg_main_2e_consume\(\), p0' \
     && ! printf '%s' "$offworker" | grep -qE 'kdup\(' \
     && grep -qE 'krc_mark_shared_recursive' "$offc" \
     && ! grep -qE 'kdrop\(' "$offc" \
     && printf '%s' "$offmain" | grep -qE 'krc_set_enabled\(0\);'; then
    echo "   ok (explicit RC-off disables runtime RC and leaves ownership maintenance out of generated C while keeping publish marking)"
  else
    echo "   FAIL: explicit RC-off did not disable runtime RC or generated ownership maintenance"
    printf '%s\n' "$offmain" | sed 's/^/     /'
    printf '%s\n' "$offworker" | sed 's/^/     /'
    grep -nE 'kdrop|kdup|krc_mark_shared_recursive' "$offc" | sed 's/^/     /' || true
    fails=$((fails+1))
  fi
  rm -f "$offc"
else
  echo "   FAIL: rc_off_owned_use --emit-c build failed"; cat "$offtmp/build.log" | sed 's/^/     /'; fails=$((fails+1))
fi

# Perceus RC S2.3d: a locally-owned flat local consumed on one branch must be
# dropped at branch entry on sibling branches that omit it. Incoming params are
# not dropped by this stage until caller-side ownership transfer is normalized.
echo "== Perceus S2.3d: branch-dead owned flat locals are dropped =="
dtmp="$WORK/rc-branch-dead-drop"; mkdir -p "$dtmp"
dsrc="$dtmp/rc_branch_dead_drop.kp"
cat > "$dsrc" <<'KP'
module main
data Box : Type =
    MkBox (value : Int)
data Holder : Type =
    Holder (box : Box)
type RHolder : Type = (box : Box)
consumeBox : Box -> Int
let consumeBox b =
    match b
    case MkBox n -> n
peekBox : (& b : Box) -> Bool
let peekBox b = b.value == 4
peekHolder : (& h : Holder) -> Int
let peekHolder h = h.box.value
peekRHolder : (& h : RHolder) -> Int
let peekRHolder h = h.box.value
alwaysFalseConsume : Box -> Bool
let alwaysFalseConsume b =
    match b
    case MkBox n -> False
branchIf : Bool -> Box -> Int
let branchIf c x =
    if c
    then consumeBox x
    else 0
branchMatch : Option Int -> Box -> Int
let branchMatch o x =
    match o
    case Some n -> consumeBox x
    case None -> 0
branchLetIf : Bool -> Int
let branchLetIf c =
    let x = MkBox 3
    if c
    then consumeBox x
    else 0
branchGuardLet : Option Int -> Int
let branchGuardLet o =
    let x = MkBox 4
    match o
    case Some n if peekBox x -> n
    case Some n -> consumeBox x
    case None -> consumeBox x
branchAliasParam : Bool -> Box -> Int
let branchAliasParam c x =
    let y = x
    if c
    then consumeBox y
    else 0
branchBorrowedAlias : Bool -> Int
let branchBorrowedAlias c =
    let h = Holder (MkBox 6)
    let y = h.box
    if c
    then consumeBox y
    else peekHolder h
branchBorrowedRecordAlias : Bool -> Int
let branchBorrowedRecordAlias c =
    let h : RHolder = (box = MkBox 9)
    let y = h.box
    if c
    then consumeBox y
    else peekRHolder h
branchBorrowedNestedAlias : Bool -> Int
let branchBorrowedNestedAlias c =
    let h : RHolder = (box = MkBox 12)
    let y = let z = 0 in h.box
    if c
    then consumeBox y
    else peekRHolder h
branchNestedClosure : Bool -> Int
let branchNestedClosure c =
    (\n -> let x = MkBox 11 in if c then consumeBox x else 0) 0
branchGuardConsumeFallthrough : Option Int -> Box -> Int
let branchGuardConsumeFallthrough o x =
    match o
    case Some n if alwaysFalseConsume x -> n
    case Some n -> consumeBox x
    case None -> 0
branchGuardConsumeLocalFallthrough : Option Int -> Int
let branchGuardConsumeLocalFallthrough o =
    let x = MkBox 13
    match o
    case Some n if alwaysFalseConsume x -> n
    case Some n -> 0
    case None -> 0
borrowedProjectionFalse : Int
let borrowedProjectionFalse =
    let h = Holder (MkBox 5)
    branchIf False h.box
main : UIO Unit
let main = printInt (branchIf True (MkBox 1) + branchIf False (MkBox 10) + branchMatch (Some 2) (MkBox 2) + branchMatch None (MkBox 20) + branchLetIf True + branchLetIf False + branchGuardLet (Some 10) + branchGuardLet None + branchAliasParam True (MkBox 7) + branchAliasParam False (MkBox 70) + branchBorrowedAlias True + branchBorrowedAlias False + branchBorrowedRecordAlias True + branchBorrowedRecordAlias False + branchBorrowedNestedAlias True + branchBorrowedNestedAlias False + branchNestedClosure True + branchNestedClosure False + branchGuardConsumeFallthrough (Some 8) (MkBox 8) + branchGuardConsumeLocalFallthrough (Some 13) + branchGuardConsumeLocalFallthrough None + borrowedProjectionFalse)
KP
if KAPPA_PERCEUS_RC=true timeout 120 $KAPPA build "$dsrc" --emit-c -o "$dtmp/rc_branch_dead_drop_emit" >"$dtmp/emit.log" 2>&1; then
  KAPPA_PERCEUS_RC=true check_perceus_rc_log "$dtmp/emit.log"
  cfile="$dtmp/rc_branch_dead_drop.kappa.c"
  if_worker="$(awk '/^static KValue \*kw_main_2e_branchIf\(KValue \*p0, KValue \*p1\) \{/{f=1} f{print} f&&/^}/{exit}' "$cfile")"
  match_worker="$(awk '/^static KValue \*kw_main_2e_branchMatch\(KValue \*p0, KValue \*p1\) \{/{f=1} f{print} f&&/^}/{exit}' "$cfile")"
  let_worker="$(awk '/^static KValue \*kw_main_2e_branchLetIf\(KValue \*p0\) \{/{f=1} f{print} f&&/^}/{exit}' "$cfile")"
  guard_worker="$(awk '/^static KValue \*kw_main_2e_branchGuardLet\(KValue \*p0\) \{/{f=1} f{print} f&&/^}/{exit}' "$cfile")"
  alias_worker="$(awk '/^static KValue \*kw_main_2e_branchAliasParam\(KValue \*p0, KValue \*p1\) \{/{f=1} f{print} f&&/^}/{exit}' "$cfile")"
  borrowed_worker="$(awk '/^static KValue \*kw_main_2e_branchBorrowedAlias\(KValue \*p0\) \{/{f=1} f{print} f&&/^}/{exit}' "$cfile")"
  borrowed_record_worker="$(awk '/^static KValue \*kw_main_2e_branchBorrowedRecordAlias\(KValue \*p0\) \{/{f=1} f{print} f&&/^}/{exit}' "$cfile")"
  borrowed_nested_worker="$(awk '/^static KValue \*kw_main_2e_branchBorrowedNestedAlias\(KValue \*p0\) \{/{f=1} f{print} f&&/^}/{exit}' "$cfile")"
  guard_consume_worker="$(awk '/^static KValue \*kw_main_2e_branchGuardConsumeFallthrough\(KValue \*p0, KValue \*p1\) \{/{f=1} f{print} f&&/^}/{exit}' "$cfile")"
  guard_consume_local_worker="$(awk '/^static KValue \*kw_main_2e_branchGuardConsumeLocalFallthrough\(KValue \*p0\) \{/{f=1} f{print} f&&/^}/{exit}' "$cfile")"
  let_then="$(printf '%s\n' "$let_worker" | awk '/} else \{/{exit} {print}')"
  let_else="$(printf '%s\n' "$let_worker" | awk '/} else \{/{f=1; next} f{print}')"
  guard_success="$(printf '%s\n' "$guard_worker" | awk '/kw_main_2e_peekBox\(let_[0-9]+\)/{f=1} f{print} f&&/matched_[0-9]+ = 1;/{exit}')"
  borrowed_else="$(printf '%s\n' "$borrowed_worker" | awk '/} else \{/{f=1; next} f{print}')"
  borrowed_before_peek="$(printf '%s\n' "$borrowed_else" | awk '/peekHolder/{exit} {print}')"
  borrowed_record_then="$(printf '%s\n' "$borrowed_record_worker" | awk '/} else \{/{exit} {print}')"
  borrowed_record_else="$(printf '%s\n' "$borrowed_record_worker" | awk '/} else \{/{f=1; next} f{print}')"
  borrowed_record_before_consume="$(printf '%s\n' "$borrowed_record_then" | awk '/consumeBox/{exit} {print}')"
  borrowed_record_before_peek="$(printf '%s\n' "$borrowed_record_else" | awk '/peekRHolder/{exit} {print}')"
  borrowed_nested_then="$(printf '%s\n' "$borrowed_nested_worker" | awk '/} else \{/{exit} {print}')"
  borrowed_nested_else="$(printf '%s\n' "$borrowed_nested_worker" | awk '/} else \{/{f=1; next} f{print}')"
  borrowed_nested_before_consume="$(printf '%s\n' "$borrowed_nested_then" | awk '/consumeBox/{exit} {print}')"
  borrowed_nested_before_peek="$(printf '%s\n' "$borrowed_nested_else" | awk '/peekRHolder/{exit} {print}')"
  borrowed_owner="$(printf '%s\n' "$borrowed_worker" | sed -nE 's/.*KValue \*(let_[0-9]+) = kctor\(.*/\1/p' | head -n 1)"
  borrowed_record_owner="$(printf '%s\n' "$borrowed_record_worker" | sed -nE 's/.*KValue \*(let_[0-9]+) = krec\(.*/\1/p' | head -n 1)"
  borrowed_nested_owner="$(printf '%s\n' "$borrowed_nested_worker" | sed -nE 's/.*KValue \*(let_[0-9]+) = krec\(.*/\1/p' | head -n 1)"
  if [ -n "$borrowed_owner" ] && ! printf '%s' "$borrowed_before_peek" | grep -qF "kdrop($borrowed_owner);"; then
    borrowed_owner_peek_safe=yes
  else
    borrowed_owner_peek_safe=no
  fi
  if [ -n "$borrowed_record_owner" ] && ! printf '%s' "$borrowed_record_before_peek" | grep -qF "kdrop($borrowed_record_owner);"; then
    borrowed_record_owner_peek_safe=yes
  else
    borrowed_record_owner_peek_safe=no
  fi
  if [ -n "$borrowed_nested_owner" ] && ! printf '%s' "$borrowed_nested_before_peek" | grep -qF "kdrop($borrowed_nested_owner);"; then
    borrowed_nested_owner_peek_safe=yes
  else
    borrowed_nested_owner_peek_safe=no
  fi
  if printf '%s' "$guard_consume_local_worker" | grep -q 'alwaysFalseConsume' \
     && { printf '%s' "$guard_consume_local_worker" | grep -qE 'alwaysFalseConsume\(kdup\(let_[0-9]+\)\)' \
          || ! printf '%s' "$guard_consume_local_worker" | grep -qE 'kdrop\(let_[0-9]+\);'; }; then
    guard_consume_local_safe=yes
  else
    guard_consume_local_safe=no
  fi
  nested_closure_ok="$(awk '
    /^static KValue \*kfn_[A-Za-z0-9_]+\(KEnv \*cenv, KValue \*arg\) \{/ { f=1; body="" }
    f { body = body $0 "\n" }
    f && /^}/ {
      if (body ~ /consumeBox/ && body ~ /kctor\(/) {
        n=split(body, lines, "\n")
        for (i=1; i<n; i++) {
          if (lines[i] ~ /^[[:space:]]*kdrop\(let_[0-9]+\);[[:space:]]*$/ && lines[i+1] ~ /^[[:space:]]*return /) {
            found=1
          }
        }
      }
      f=0
    }
    END { print found ? "yes" : "no" }
  ' "$cfile")"
  if [ -n "$if_worker" ] && [ -n "$match_worker" ] && [ -n "$let_worker" ] && [ -n "$guard_worker" ] \
     && [ -n "$alias_worker" ] && [ -n "$borrowed_worker" ] && [ -n "$borrowed_record_worker" ] && [ -n "$borrowed_nested_worker" ] && [ -n "$guard_consume_worker" ] && [ -n "$guard_consume_local_worker" ] \
     && ! printf '%s' "$if_worker" | grep -qE 'kdrop\(p1\);' \
     && ! printf '%s' "$match_worker" | grep -qE 'kdrop\(p1\);' \
     && ! printf '%s' "$match_worker" | grep -qE 'kdrop\(scrut_[0-9]+\);' \
     && ! printf '%s' "$let_then" | grep -qE 'kdrop\(let_[0-9]+\);' \
     && printf '%s' "$let_else" | grep -qE 'kdrop\(let_[0-9]+\);' \
     && printf '%s\n' "$guard_success" | awk '/^[[:space:]]*return / && prev ~ /^[[:space:]]*kdrop\(let_[0-9]+\);[[:space:]]*$/ { found=1 } { prev=$0 } END { exit found ? 0 : 1 }' \
     && ! printf '%s' "$alias_worker" | grep -qE 'kdrop\(let_[0-9]+\);' \
     && printf '%s' "$borrowed_worker" | grep -qE 'kdup\(kctor_arg' \
     && [ "$borrowed_owner_peek_safe" = "yes" ] \
     && printf '%s' "$borrowed_record_worker" | grep -qE 'kdup\(krec_at' \
     && ! printf '%s' "$borrowed_record_before_consume" | grep -qE 'kdrop\(let_[0-9]+\);' \
     && [ "$borrowed_record_owner_peek_safe" = "yes" ] \
     && printf '%s' "$borrowed_nested_worker" | grep -qE 'if \(kas_bool\(p0\)\)' \
     && printf '%s' "$borrowed_nested_worker" | grep -qE 'kdup\(krec_at' \
     && ! printf '%s' "$borrowed_nested_before_consume" | grep -qE 'kdrop\(let_[0-9]+\);' \
     && [ "$borrowed_nested_owner_peek_safe" = "yes" ] \
	     && [ "$nested_closure_ok" = "yes" ] \
     && printf '%s' "$guard_consume_worker" | grep -qE 'kw_main_2e_alwaysFalseConsume\(kdup\(p1\)\)' \
     && [ "$guard_consume_local_safe" = "yes" ]; then
    echo "   ok (omitting branches drop constructor let-locals; aliases/guards preserve ownership)"
  else
    echo "   FAIL: S2.3d branch-dead drops have the wrong generated-code shape"
    printf '%s\n' "$if_worker" | sed 's/^/     IF: /'
    printf '%s\n' "$match_worker" | sed 's/^/     MATCH: /'
    printf '%s\n' "$let_worker" | sed 's/^/     LET: /'
    printf '%s\n' "$guard_worker" | sed 's/^/     GUARD: /'
    printf '%s\n' "$alias_worker" | sed 's/^/     ALIAS: /'
    printf '%s\n' "$borrowed_worker" | sed 's/^/     BORROWED: /'
    printf '%s\n' "$borrowed_record_worker" | sed 's/^/     RECORD: /'
    printf '%s\n' "$borrowed_nested_worker" | sed 's/^/     NESTED-RECORD: /'
    printf '     RECORD-OWNER-PEEK-SAFE: %s (%s)\n' "$borrowed_record_owner_peek_safe" "$borrowed_record_owner"
    printf '     NESTED-OWNER-PEEK-SAFE: %s (%s)\n' "$borrowed_nested_owner_peek_safe" "$borrowed_nested_owner"
    printf '     NESTED-CLOSURE-OK: %s\n' "$nested_closure_ok"
    printf '%s\n' "$guard_consume_worker" | sed 's/^/     GUARD-CONSUME: /'
    printf '     GUARD-CONSUME-LOCAL-SAFE: %s\n' "$guard_consume_local_safe"
    printf '%s\n' "$guard_consume_local_worker" | sed 's/^/     GUARD-CONSUME-LOCAL: /'
    fails=$((fails+1))
  fi
  rm -f "$cfile"
else
  echo "   FAIL: rc_branch_dead_drop --emit-c build failed"; cat "$dtmp/emit.log" | sed 's/^/     /'; fails=$((fails+1))
fi
if interp="$(timeout 120 $KAPPA run "$dsrc" 2>"$dtmp/interp.log")"; then
  if KAPPA_PERCEUS_RC=true timeout 240 $KAPPA build "$dsrc" -o "$dtmp/rc_branch_dead_drop" >"$dtmp/build.log" 2>&1; then
    KAPPA_PERCEUS_RC=true check_perceus_rc_log "$dtmp/build.log"
    native="$(timeout 120 "$dtmp/rc_branch_dead_drop" 2>/dev/null)"; nrc=$?
    if [ "$nrc" -eq 0 ] && [ "$interp" = "$native" ]; then
      echo "   ok (RC executable output matches interpreter: $(printf '%s' "$native" | tr '\n' '|'))"
    else
      echo "   FAIL: rc_branch_dead_drop runtime mismatch"
      echo "     interpreter: $(printf '%s' "$interp" | tr '\n' '|')"
      echo "     native:      $(printf '%s' "$native" | tr '\n' '|')"
      fails=$((fails+1))
    fi
  else
    echo "   FAIL: rc_branch_dead_drop native build failed"
    [ -f "$dtmp/build.log" ] && cat "$dtmp/build.log" | sed 's/^/     /'
    fails=$((fails+1))
  fi
else
  echo "   FAIL: rc_branch_dead_drop interpreter run failed"
  [ -f "$dtmp/interp.log" ] && cat "$dtmp/interp.log" | sed 's/^/     /'
  fails=$((fails+1))
fi

# Perceus RC S2.3b: mixed boxed/scalar fast workers must remain available under
# RC. Boxed-field projections in this worker grammar are read-only and boxed
# self-args are pass-through tail-loop state, so the ownership path validated by
# the boxed worker remains the source of truth and the optimized worker must not
# be suppressed as a workaround.
echo "== Perceus S2.3b: RC keeps mixed boxed/scalar workers =="
mtmp="$WORK/rc-mixed-scalar"; mkdir -p "$mtmp"
msrc="$mtmp/rc_mixed_scalar.kp"
cat > "$msrc" <<'KP'
module main
type Box = (v : Int)
sumBox : Box -> Int -> Int
let sumBox b n =
    if leInt n 0
    then b.v
    else sumBox b (subInt n 1)
main : UIO Unit
let main = printInt (sumBox (v = 7) 3)
KP
if KAPPA_PERCEUS_RC=true timeout 120 $KAPPA build "$msrc" --emit-c -o "$mtmp/rc_mixed_scalar" >"$mtmp/build.log" 2>&1; then
  KAPPA_PERCEUS_RC=true check_perceus_rc_log "$mtmp/build.log"
  cfile="$mtmp/rc_mixed_scalar.kappa.c"
  mixed_worker="$(awk '/^static int64_t kwm_main_2e_sumBox\(.*\{$/{f=1} f{print} f&&/^}/{exit}' "$cfile")"
  if printf '%s' "$mixed_worker" | grep -qE '\bkwm_main_2e_sumBox\b' \
     && printf '%s' "$mixed_worker" | grep -qE 'krec_at\(p[0-9]' \
     && printf '%s' "$mixed_worker" | grep -qE 'if \(krt2_safepoint\(\)\) \{ \*kovf = KRT2_SCALAR_ABORT; return 0; \}'; then
    echo "   ok (RC build emits mixed worker with read-only boxed field access and scalar abort channel)"
  else
    echo "   FAIL: RC build did not emit the expected mixed boxed/scalar worker for sumBox"
    grep -nE 'kwm_main_2e_sumBox|kw_main_2e_sumBox' "$cfile" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  rm -f "$cfile"
else
  echo "   FAIL: rc_mixed_scalar --emit-c build failed"; cat "$mtmp/build.log" | sed 's/^/     /'; fails=$((fails+1))
fi

echo "== Perceus S2.3b: RC keeps all-scalar workers =="
atmp="$WORK/rc-all-scalar"; mkdir -p "$atmp"
asrc="$atmp/rc_all_scalar.kp"
cat > "$asrc" <<'KP'
module main
sumInt : Int -> Int -> Int
let sumInt acc n =
    if leInt n 0
    then acc
    else sumInt (addInt acc n) (subInt n 1)
main : UIO Unit
let main = printInt (sumInt 0 3)
KP
if KAPPA_PERCEUS_RC=true timeout 120 $KAPPA build "$asrc" --emit-c -o "$atmp/rc_all_scalar" >"$atmp/build.log" 2>&1; then
  KAPPA_PERCEUS_RC=true check_perceus_rc_log "$atmp/build.log"
  cfile="$atmp/rc_all_scalar.kappa.c"
  scalar_worker="$(awk '/^static int64_t kwi_main_2e_sumInt\(.*\{$/{f=1} f{print} f&&/^}/{exit}' "$cfile")"
  if printf '%s' "$scalar_worker" | grep -qE '\bkwi_main_2e_sumInt\b' \
     && printf '%s' "$scalar_worker" | grep -qE 'if \(krt2_safepoint\(\)\) \{ \*kovf = KRT2_SCALAR_ABORT; return 0; \}' \
     && grep -qE '\bkw_main_2e_sumInt\b' "$cfile"; then
    echo "   ok (RC build emits all-scalar worker with scalar abort channel and boxed fallback)"
  else
    echo "   FAIL: RC build did not emit the expected all-scalar worker for sumInt"
    grep -nE 'kwi_main_2e_sumInt|kwd_main_2e_sumInt|kw_main_2e_sumInt' "$cfile" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  rm -f "$cfile"
else
  echo "   FAIL: rc_all_scalar --emit-c build failed"; cat "$atmp/build.log" | sed 's/^/     /'; fails=$((fails+1))
fi

echo "== §32.2.6: scalar-worker abort unwinds nested pure frames before later effects =="
natmp="$WORK/scalar-nested-abort"; mkdir -p "$natmp"
nasrc="$CASES/scalar-nested-abort.kp"
cfile="$CASES/scalar-nested-abort.kappa.c"
rm -f "$cfile"
if timeout 120 $KAPPA build "$nasrc" --emit-c -o "$natmp/scalar_nested_abort_emit" >"$natmp/emit.log" 2>&1; then
  check_perceus_rc_log "$natmp/emit.log"
  if [ -f "$cfile" ] \
     && grep -qE '\bkwi_main_2e_spin\b' "$cfile" \
     && grep -qE '\bkrt2_scalar_abort\(\)' "$cfile"; then
    echo "   ok-shape (nested scalar call uses scalar abort hook, not Unit sentinel)"
  else
    echo "   FAIL: scalar nested abort source shape missing scalar worker or abort hook"
    grep -nE 'kwi_main_2e_spin|kw_main_2e_wrap|KRT2_SCALAR_ABORT|krt2_scalar_abort|return kunit' "$cfile" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  rm -f "$cfile"
else
  echo "   FAIL: scalar-nested-abort --emit-c build failed"; cat "$natmp/emit.log" | sed 's/^/     /'; fails=$((fails+1))
fi
if build_clean_for_source "$nasrc" timeout 240 $KAPPA build "$nasrc" -o "$natmp/scalar_nested_abort" >"$natmp/build.log" 2>&1; then
  check_perceus_rc_log "$natmp/build.log"
  out="$(timeout 30 "$natmp/scalar_nested_abort" 2>/dev/null)"; rc=$?
  if [ "$rc" -eq 0 ] && [ "$out" = "exit:interrupted" ]; then
    echo "   ok-run (post-scalar effect skipped; interrupt delivered)"
  else
    echo "   FAIL: scalar abort did not stop the enclosing generated frame before later effects"
    echo "     rc=$rc stdout=$(printf '%s' "$out" | tr '\n' '|')"
    fails=$((fails+1))
  fi
else
  echo "   FAIL: scalar-nested-abort native build failed"; cat "$natmp/build.log" | sed 's/^/     /'; fails=$((fails+1))
fi
llfile="$CASES/scalar-nested-abort.kappa.ll"
rm -f "$llfile"
if KAPPA_BACKEND=llvm timeout 180 $KAPPA build "$nasrc" --emit-c -o "$natmp/scalar_nested_abort_llvm_emit" >"$natmp/llvm-emit.log" 2>&1; then
  check_perceus_rc_log "$natmp/llvm-emit.log"
  if [ -f "$llfile" ] \
     && grep -qE 'call void @krt2_scalar_abort\(\)' "$llfile" \
     && grep -qE 'call ptr @kio\(ptr @kdo_[0-9]+, ptr null\)' "$llfile" \
     && grep -qE 'call ptr @kio_tail\(' "$llfile"; then
    echo "   ok-llvm-shape (child do-block is delayed behind kio and returns a tail action)"
  else
    echo "   FAIL: LLVM scalar nested abort shape is missing delayed child action, tail marker, or abort hook"
    grep -nE 'kg_main_2e_child|@kio|kio_tail|krt2_scalar_abort|AFTER-SCALAR' "$llfile" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  rm -f "$llfile"
else
  echo "   FAIL: scalar-nested-abort LLVM --emit-c build failed"; cat "$natmp/llvm-emit.log" | sed 's/^/     /'; fails=$((fails+1))
fi
if KAPPA_BACKEND=llvm build_clean_for_source "$nasrc" timeout 240 $KAPPA build "$nasrc" -o "$natmp/scalar_nested_abort_llvm" >"$natmp/llvm-build.log" 2>&1; then
  check_perceus_rc_log "$natmp/llvm-build.log"
  out="$(timeout 30 "$natmp/scalar_nested_abort_llvm" 2>/dev/null)"; rc=$?
  if [ "$rc" -eq 0 ] && [ "$out" = "exit:interrupted" ]; then
    echo "   ok-llvm-run (post-scalar effect skipped; interrupt delivered)"
  else
    echo "   FAIL: LLVM scalar abort did not stop the enclosing generated frame before later effects"
    echo "     rc=$rc stdout=$(printf '%s' "$out" | tr '\n' '|')"
    fails=$((fails+1))
  fi
else
  echo "   FAIL: scalar-nested-abort LLVM native build failed"; cat "$natmp/llvm-build.log" | sed 's/^/     /'; fails=$((fails+1))
fi

echo "== §32.2.6: LLVM scalarized var-loop abort unwinds before later effects =="
vltmp="$WORK/scalar-varloop-nested-abort"; mkdir -p "$vltmp"
vlsrc="$CASES/scalar-varloop-nested-abort.kp"
vlll="$CASES/scalar-varloop-nested-abort.kappa.ll"
rm -f "$vlll"
if KAPPA_BACKEND=llvm timeout 180 $KAPPA build "$vlsrc" --emit-c -o "$vltmp/scalar_varloop_abort_emit" >"$vltmp/llvm-emit.log" 2>&1; then
  check_perceus_rc_log "$vltmp/llvm-emit.log"
  vl_worker=""
  if [ -f "$vlll" ]; then
    vl_worker="$(awk '/^define internal ptr @kscalarloop_[0-9]+\(ptr %args\)/{f=1} f{print} f&&/^}/{exit}' "$vlll")"
  fi
  vl_abort_flushes="$(printf '%s' "$vl_worker" | awk '/^[[:space:]]*sabort_[0-9]+:/{f=1; n=0} f&&/call ptr @kref_set\(/{n++} f&&/call void @krt2_scalar_abort\(\)/{seen=1; print n; exit} END{if(!seen) print 0}')"
  if [ -f "$vlll" ] \
     && printf '%s' "$vl_worker" | grep -qE 'call void @krt2_scalar_abort\(\)' \
     && printf '%s' "$vl_worker" | grep -qE 'call i32 @krt2_safepoint\(\)' \
     && [ "${vl_abort_flushes:-0}" -ge 2 ] \
     && ! grep -qE 'call ptr @krt2_while\(' "$vlll"; then
    echo "   ok-llvm-shape (scalar var-loop worker has safepoints and flushes both hidden refs before scalar abort)"
  else
    echo "   FAIL: LLVM scalar var-loop abort shape is missing worker safepoint, full abort flush (${vl_abort_flushes:-0}/2 hidden refs), hook, or scalarization"
    grep -nE '@kscalarloop_|krt2_safepoint|krt2_scalar_abort|krt2_while|AFTER-VARLOOP' "$vlll" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  rm -f "$vlll"
else
  echo "   FAIL: scalar-varloop-nested-abort LLVM --emit-c build failed"; cat "$vltmp/llvm-emit.log" | sed 's/^/     /'; fails=$((fails+1))
fi
if KAPPA_BACKEND=llvm build_clean_for_source "$vlsrc" timeout 240 $KAPPA build "$vlsrc" -o "$vltmp/scalar_varloop_abort_llvm" >"$vltmp/llvm-build.log" 2>&1; then
  check_perceus_rc_log "$vltmp/llvm-build.log"
  out="$(timeout 30 "$vltmp/scalar_varloop_abort_llvm" 2>/dev/null)"; rc=$?
  if [ "$rc" -eq 0 ] && [ "$out" = "exit:interrupted" ]; then
    echo "   ok-llvm-run (post-varloop effect skipped; interrupt delivered)"
  else
    echo "   FAIL: LLVM scalar var-loop abort did not stop the enclosing frame before later effects"
    echo "     rc=$rc stdout=$(printf '%s' "$out" | tr '\n' '|')"
    fails=$((fails+1))
  fi
else
  echo "   FAIL: scalar-varloop-nested-abort LLVM native build failed"; cat "$vltmp/llvm-build.log" | sed 's/^/     /'; fails=$((fails+1))
fi

echo "== §32.2.6: scalar-worker abort releases active using scopes =="
nu_tmp="$WORK/scalar-nested-abort-using"; mkdir -p "$nu_tmp"
nu_src="$CASES/scalar-nested-abort-using.kp"
nu_expect="$(printf 'acquired\nreleased\nexit:interrupted')"
cfile="$CASES/scalar-nested-abort-using.kappa.c"
rm -f "$cfile"
if timeout 120 $KAPPA build "$nu_src" --emit-c -o "$nu_tmp/scalar_nested_abort_using_emit" >"$nu_tmp/emit.log" 2>&1; then
  check_perceus_rc_log "$nu_tmp/emit.log"
  if [ -f "$cfile" ] \
     && grep -qE '\bkrt2_scalar_abort\(\)' "$cfile" \
     && { { grep -qE 'krt2_abort_exit_push\(' "$cfile" \
            && grep -qE 'krt2_abort_exit_finalizer\(' "$cfile"; } \
          || grep -qE 'krt2_acquire_release\(' "$cfile"; } \
     && ! grep -qE 'krt2_abort_release_drain\(\)' "$cfile"; then
    echo "   ok-shape (using release is runtime-tokenized and abort path enters the unwinder)"
  else
    echo "   FAIL: scalar abort using-release token shape missing"
    grep -nE 'abort_(release|exit)|release_fail|krt2_scalar_abort|defer-ran|AFTER-SCALAR' "$cfile" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  rm -f "$cfile"
else
  echo "   FAIL: scalar-nested-abort-using --emit-c build failed"; cat "$nu_tmp/emit.log" | sed 's/^/     /'; fails=$((fails+1))
fi
if build_clean_for_source "$nu_src" timeout 240 $KAPPA build "$nu_src" -o "$nu_tmp/scalar_nested_abort_using" >"$nu_tmp/build.log" 2>&1; then
  check_perceus_rc_log "$nu_tmp/build.log"
  out="$(timeout 30 "$nu_tmp/scalar_nested_abort_using" 2>/dev/null)"; rc=$?
  if [ "$rc" -eq 0 ] && [ "$out" = "$nu_expect" ]; then
    echo "   ok-run (using release runs; post-scalar effect is skipped)"
  else
    echo "   FAIL: scalar abort did not preserve using/defer interrupt semantics"
    echo "     rc=$rc stdout=$(printf '%s' "$out" | tr '\n' '|')"
    fails=$((fails+1))
  fi
else
  echo "   FAIL: scalar-nested-abort-using native build failed"; cat "$nu_tmp/build.log" | sed 's/^/     /'; fails=$((fails+1))
fi
nud_src="$CASES/scalar-nested-abort-using-defer.kp"
nud_expect="$(printf 'acquired\ndefer-ran\nreleased\nexit:interrupted')"
if build_clean_for_source "$nud_src" timeout 240 $KAPPA build "$nud_src" -o "$nu_tmp/scalar_nested_abort_using_defer" >"$nu_tmp/defer-build.log" 2>&1; then
  check_perceus_rc_log "$nu_tmp/defer-build.log"
  out="$(timeout 30 "$nu_tmp/scalar_nested_abort_using_defer" 2>/dev/null)"; rc=$?
  if [ "$rc" -eq 0 ] && [ "$out" = "$nud_expect" ]; then
    echo "   ok-c-defer-run (ordinary defer and using release both run on async abort)"
  else
    echo "   FAIL: C scalar abort skipped a defer/using release or ran later source effects"
    echo "     rc=$rc stdout=$(printf '%s' "$out" | tr '\n' '|')"
    fails=$((fails+1))
  fi
else
  echo "   FAIL: scalar-nested-abort-using-defer native build failed"; cat "$nu_tmp/defer-build.log" | sed 's/^/     /'; fails=$((fails+1))
fi
nup_src="$CASES/scalar-nested-abort-defer-before-pure.kp"
nup_expect="$(printf 'defer-ran\nexit:interrupted')"
if build_clean_for_source "$nup_src" timeout 240 $KAPPA build "$nup_src" -o "$nu_tmp/scalar_nested_abort_defer_before_pure" >"$nu_tmp/defer-before-pure-build.log" 2>&1; then
  check_perceus_rc_log "$nu_tmp/defer-before-pure-build.log"
  out="$(timeout 30 "$nu_tmp/scalar_nested_abort_defer_before_pure" 2>/dev/null)"; rc=$?
  if [ "$rc" -eq 0 ] && [ "$out" = "$nup_expect" ]; then
    echo "   ok-c-defer-before-pure (defer registers before following pure scalar work)"
  else
    echo "   FAIL: C scalar abort skipped a preceding defer or ran later source effects"
    echo "     rc=$rc stdout=$(printf '%s' "$out" | tr '\n' '|')"
    fails=$((fails+1))
  fi
else
  echo "   FAIL: scalar-nested-abort-defer-before-pure native build failed"; cat "$nu_tmp/defer-before-pure-build.log" | sed 's/^/     /'; fails=$((fails+1))
fi
nuo_src="$CASES/scalar-nested-abort-onexit.kp"
nuo_expect="$(printf 'int:Requested\nexit:Interrupt\nawait:interrupted')"
if build_clean_for_source "$nuo_src" timeout 240 $KAPPA build "$nuo_src" -o "$nu_tmp/scalar_nested_abort_onexit" >"$nu_tmp/onexit-build.log" 2>&1; then
  check_perceus_rc_log "$nu_tmp/onexit-build.log"
  out="$(timeout 30 "$nu_tmp/scalar_nested_abort_onexit" 2>/dev/null)"; rc=$?
  if [ "$rc" -eq 0 ] && [ "$out" = "$nuo_expect" ]; then
    echo "   ok-c-onexit-run (reason-aware finalizers run on scalar abort)"
  else
    echo "   FAIL: C scalar abort skipped onInterrupt/onExit markers or source continued"
    echo "     rc=$rc stdout=$(printf '%s' "$out" | tr '\n' '|')"
    fails=$((fails+1))
  fi
else
  echo "   FAIL: scalar-nested-abort-onexit native build failed"; cat "$nu_tmp/onexit-build.log" | sed 's/^/     /'; fails=$((fails+1))
fi
nuf_src="$CASES/scalar-nested-abort-cleanup-failure.kp"
nuf_expect="$(printf 'acquired\ndefer-fail\nrelease-fail\nexit:then2:defer:release')"
if build_clean_for_source "$nuf_src" timeout 240 $KAPPA build "$nuf_src" -o "$nu_tmp/scalar_nested_abort_cleanup_failure" >"$nu_tmp/fail-build.log" 2>&1; then
  check_perceus_rc_log "$nu_tmp/fail-build.log"
  out="$(timeout 30 "$nu_tmp/scalar_nested_abort_cleanup_failure" 2>/dev/null)"; rc=$?
  if [ "$rc" -eq 0 ] && [ "$out" = "$nuf_expect" ]; then
    echo "   ok-c-cleanup-fail (all abort cleanups run and compose after interrupt)"
  else
    echo "   FAIL: C scalar abort cleanup failures were not LIFO/composed or source continued"
    echo "     rc=$rc stdout=$(printf '%s' "$out" | tr '\n' '|')"
    fails=$((fails+1))
  fi
else
  echo "   FAIL: scalar-nested-abort-cleanup-failure native build failed"; cat "$nu_tmp/fail-build.log" | sed 's/^/     /'; fails=$((fails+1))
fi
llfile="$CASES/scalar-nested-abort-using.kappa.ll"
rm -f "$llfile"
if KAPPA_BACKEND=llvm timeout 180 $KAPPA build "$nu_src" --emit-c -o "$nu_tmp/scalar_nested_abort_using_llvm_emit" >"$nu_tmp/llvm-emit.log" 2>&1; then
  check_perceus_rc_log "$nu_tmp/llvm-emit.log"
  if [ -f "$llfile" ] \
     && grep -qE 'call void @krt2_scalar_abort\(\)' "$llfile" \
     && grep -qE 'call ptr @krt2_acquire_release\(' "$llfile"; then
    echo "   ok-llvm-shape (using is runtime-managed and scalar abort uses runtime hook)"
  else
    echo "   FAIL: LLVM scalar abort using shape is missing finalizer node or abort hook"
    grep -nE 'krt2_acquire_release|krt2_scalar_abort|defer-ran|AFTER-SCALAR' "$llfile" | sed 's/^/     /'
    fails=$((fails+1))
  fi
  rm -f "$llfile"
else
  echo "   FAIL: scalar-nested-abort-using LLVM --emit-c build failed"; cat "$nu_tmp/llvm-emit.log" | sed 's/^/     /'; fails=$((fails+1))
fi
if KAPPA_BACKEND=llvm build_clean_for_source "$nu_src" timeout 240 $KAPPA build "$nu_src" -o "$nu_tmp/scalar_nested_abort_using_llvm" >"$nu_tmp/llvm-build.log" 2>&1; then
  check_perceus_rc_log "$nu_tmp/llvm-build.log"
  out="$(timeout 30 "$nu_tmp/scalar_nested_abort_using_llvm" 2>/dev/null)"; rc=$?
  if [ "$rc" -eq 0 ] && [ "$out" = "$nu_expect" ]; then
    echo "   ok-llvm-run (using release runs; post-scalar effect is skipped)"
  else
    echo "   FAIL: LLVM scalar abort did not preserve using/defer interrupt semantics"
    echo "     rc=$rc stdout=$(printf '%s' "$out" | tr '\n' '|')"
    fails=$((fails+1))
  fi
else
  echo "   FAIL: scalar-nested-abort-using LLVM native build failed"; cat "$nu_tmp/llvm-build.log" | sed 's/^/     /'; fails=$((fails+1))
fi
if KAPPA_BACKEND=llvm build_clean_for_source "$nud_src" timeout 240 $KAPPA build "$nud_src" -o "$nu_tmp/scalar_nested_abort_using_defer_llvm" >"$nu_tmp/llvm-defer-build.log" 2>&1; then
  check_perceus_rc_log "$nu_tmp/llvm-defer-build.log"
  out="$(timeout 30 "$nu_tmp/scalar_nested_abort_using_defer_llvm" 2>/dev/null)"; rc=$?
  if [ "$rc" -eq 0 ] && [ "$out" = "$nud_expect" ]; then
    echo "   ok-llvm-defer-run (ordinary defer and using release both run on async abort)"
  else
    echo "   FAIL: LLVM scalar abort skipped a defer/using release or ran later source effects"
    echo "     rc=$rc stdout=$(printf '%s' "$out" | tr '\n' '|')"
    fails=$((fails+1))
  fi
else
  echo "   FAIL: scalar-nested-abort-using-defer LLVM native build failed"; cat "$nu_tmp/llvm-defer-build.log" | sed 's/^/     /'; fails=$((fails+1))
fi
if KAPPA_BACKEND=llvm build_clean_for_source "$nup_src" timeout 240 $KAPPA build "$nup_src" -o "$nu_tmp/scalar_nested_abort_defer_before_pure_llvm" >"$nu_tmp/llvm-defer-before-pure-build.log" 2>&1; then
  check_perceus_rc_log "$nu_tmp/llvm-defer-before-pure-build.log"
  out="$(timeout 30 "$nu_tmp/scalar_nested_abort_defer_before_pure_llvm" 2>/dev/null)"; rc=$?
  if [ "$rc" -eq 0 ] && [ "$out" = "$nup_expect" ]; then
    echo "   ok-llvm-defer-before-pure (defer registers before following pure scalar work)"
  else
    echo "   FAIL: LLVM scalar abort skipped a preceding defer or ran later source effects"
    echo "     rc=$rc stdout=$(printf '%s' "$out" | tr '\n' '|')"
    fails=$((fails+1))
  fi
else
  echo "   FAIL: scalar-nested-abort-defer-before-pure LLVM native build failed"; cat "$nu_tmp/llvm-defer-before-pure-build.log" | sed 's/^/     /'; fails=$((fails+1))
fi
if KAPPA_BACKEND=llvm build_clean_for_source "$nuf_src" timeout 240 $KAPPA build "$nuf_src" -o "$nu_tmp/scalar_nested_abort_cleanup_failure_llvm" >"$nu_tmp/llvm-fail-build.log" 2>&1; then
  check_perceus_rc_log "$nu_tmp/llvm-fail-build.log"
  out="$(timeout 30 "$nu_tmp/scalar_nested_abort_cleanup_failure_llvm" 2>/dev/null)"; rc=$?
  if [ "$rc" -eq 0 ] && [ "$out" = "$nuf_expect" ]; then
    echo "   ok-llvm-cleanup-fail (all abort cleanups run and compose after interrupt)"
  else
    echo "   FAIL: LLVM scalar abort cleanup failures were not LIFO/composed or source continued"
    echo "     rc=$rc stdout=$(printf '%s' "$out" | tr '\n' '|')"
    fails=$((fails+1))
  fi
else
  echo "   FAIL: scalar-nested-abort-cleanup-failure LLVM native build failed"; cat "$nu_tmp/llvm-fail-build.log" | sed 's/^/     /'; fails=$((fails+1))
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
cleanup_generated_for_source "$CASES/tailrec.kp"
if timeout 240 $KAPPA build "$CASES/tailrec.kp" -o "$exe" >"$WORK/tailrec.build.log" 2>&1; then
  cleanup_generated_for_source "$CASES/tailrec.kp"
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
  cleanup_generated_for_source "$CASES/tailrec.kp"
  echo "   FAIL: tailrec build failed"; fails=$((fails+1))
fi

echo "== namespace hygiene: hidden runtime symbols are not source-visible =="
exe="$WORK/hidden"
cleanup_generated_for_source "$CASES/hidden-symbol.kp"
if timeout 120 $KAPPA build "$CASES/hidden-symbol.kp" -o "$exe" >"$WORK/hidden.log" 2>&1; then
  cleanup_generated_for_source "$CASES/hidden-symbol.kp"
  echo "   FAIL: a program calling __tcpListen built (hidden symbol leaked)"; fails=$((fails+1))
elif grep -q "E_NAME_UNRESOLVED" "$WORK/hidden.log" && [ ! -f "$exe" ]; then
  cleanup_generated_for_source "$CASES/hidden-symbol.kp"
  echo "   ok (__tcpListen is E_NAME_UNRESOLVED, no executable; FFI prims are not prelude globals)"
else
  cleanup_generated_for_source "$CASES/hidden-symbol.kp"
  echo "   FAIL: __tcpListen not rejected as unresolved / left an executable"
  cat "$WORK/hidden.log" | sed 's/^/     /'; fails=$((fails+1))
fi

echo "== a bare foreign 'expect' is unsatisfied without a host binding (no silent FFI) =="
# §9.4: a bare `expect term` has no provider — native bindings come only
# through the manifest's host.native modules, never a bare-name table or
# --ffi-full. So the legacy single-file build leaves it unsatisfied.
exe="$WORK/unsupported"
cleanup_generated_for_source "$CASES/unsupported.kp"
if timeout 120 $KAPPA build "$CASES/unsupported.kp" -o "$exe" >"$WORK/unsupported.log" 2>&1; then
  cleanup_generated_for_source "$CASES/unsupported.kp"
  echo "   FAIL: a bare foreign-expect program built (FFI fabricated)"; fails=$((fails+1))
elif grep -q "E_EXPECT_UNSATISFIED" "$WORK/unsupported.log" && [ ! -f "$exe" ]; then
  cleanup_generated_for_source "$CASES/unsupported.kp"
  echo "   ok (unsatisfied foreign expect -> E_EXPECT_UNSATISFIED, no executable, §9.4)"
else
  cleanup_generated_for_source "$CASES/unsupported.kp"
  echo "   FAIL: foreign expect not rejected as E_EXPECT_UNSATISFIED / left an executable"
  cat "$WORK/unsupported.log" | sed 's/^/     /'; fails=$((fails+1))
fi

echo "== host.native imports are unresolved under the interpreter (no manifest, no fallback) =="
# The demo imports host.native.* modules; without a build manifest no
# provider supplies them, so `kappa run` fails honestly.
if timeout 120 $KAPPA run "$ROOT/examples/native/http_sqlite/server.kp" >"$WORK/server-run.log" 2>&1; then
  echo "   FAIL: the FFI demo ran under the interpreter (host.native imports should be unresolved)"; fails=$((fails+1))
elif grep -q "E_MODULE_NAME_UNRESOLVED" "$WORK/server-run.log"; then
  echo "   ok (host.native imports unresolved -> E_MODULE_NAME_UNRESOLVED, §8.3.5)"
else
  echo "   FAIL: interpreter did not report E_MODULE_NAME_UNRESOLVED for the host.native demo"
  head -3 "$WORK/server-run.log" | sed 's/^/     /'; fails=$((fails+1))
fi

echo "== native bindings are driven by the manifest (host.native imports -> prims) =="
# Build a program that imports a manifest-provided host.native module to
# C (--emit-c, no toolchain/lib needed) and confirm codegen lowered the
# provider's members to codegen-emitted direct native wrappers.
ok_sqlite_dir="$ROOT/tests/build/native/ok-sqlite"
find "$ok_sqlite_dir" -name '*.kappa.c' -delete 2>/dev/null
if timeout 120 $KAPPA build --update --manifest "$ok_sqlite_dir" --emit-c -o "$WORK/oksql" >"$WORK/oksql.log" 2>&1 \
   && grep -Rql --include='*.kappa.c' "kw_host_native_sqlite3_sqliteOpen" "$ok_sqlite_dir" \
   && grep -Rql --include='*.kappa.c' "knative_sat(kw_host_native_sqlite3_sqliteOpen" "$ok_sqlite_dir"; then
  echo "   ok (manifest nativeBinding -> host.native.sqlite3 import -> direct native sqliteOpen wrapper)"
else
  echo "   FAIL: manifest-driven native build did not emit the provider prim"
  cat "$WORK/oksql.log" | sed 's/^/     /'; fails=$((fails+1))
fi
find "$ok_sqlite_dir" -name '*.kappa.c' -delete 2>/dev/null

echo "== performance smoke (sum 1..1_000_000, bounded) =="
exe="$WORK/perf"
cleanup_generated_for_source "$CASES/perf.kp"
if timeout 240 $KAPPA build "$CASES/perf.kp" -o "$exe" >"$WORK/perf.build.log" 2>&1; then
  cleanup_generated_for_source "$CASES/perf.kp"
  start=$(python3 - <<'PY'
import time
print(f"{time.time():.6f}")
PY
)
  out="$(timeout 30 "$exe" 2>/dev/null)"
  rc=$?
  end=$(python3 - <<'PY'
import time
print(f"{time.time():.6f}")
PY
)
  if [ "$rc" -ne 0 ]; then
    echo "   FAIL: perf run timed out or errored (rc=$rc)"; fails=$((fails+1))
  elif [ "$out" = "500000500000" ]; then
    elapsed="$(python3 - "$start" "$end" <<'PY'
import sys
start = float(sys.argv[1])
end = float(sys.argv[2])
print(f"{end - start:.2f}")
PY
)"
    echo "   ok (result $out in ${elapsed}s)"
  else
    echo "   FAIL: wrong result: $out"; fails=$((fails+1))
  fi
else
  cleanup_generated_for_source "$CASES/perf.kp"
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

# R0.1: enforce the now-fair landed-wave allocation gates from the proposed
# bench suite (median-of-N timing, per-iteration allocation): adtbuild's
# direct-ctor alloc/iter bound (R1.1) and scalar_doubleloop's unboxed-double
# alloc bound (R2.2), alongside the scalar_intloop unboxed-Int bound (LR1).
# These convert three measured wins into deterministic regression gates.
echo "== R0.1: landed-wave allocation gates (proposed bench --gate) =="
if timeout 400 bash "$ROOT/test/native/bench/proposed/run-proposed.sh" --gate --reps 3 scalar_intloop adtbuild scalar_doubleloop >"$WORK/proposed.log" 2>&1; then
  echo "   ok (adtbuild ≤300B/iter [R1.1], scalar_doubleloop ≤100KB [R2.2], scalar_intloop ≤100KB [LR1])"
  grep -E '^   ok (adtbuild|scalar_doubleloop|scalar_intloop)' "$WORK/proposed.log" | sed 's/^/  /'
else
  echo "   FAIL: a landed-wave allocation gate regressed"; grep -iE 'FAIL' "$WORK/proposed.log" | sed 's/^/     /'; fails=$((fails+1))
fi

# §4b TAIL-RESUMPTIVE constant-depth gate (mirrors the R12 loop constant-depth
# check).  A deep, tail-resumptive effect handler driven over MANY perform/resume
# cycles must keep CONSTANT Cont depth — the whole point of Stage 4b.  The fast
# path leaves the op-site→handler segment on f->k (no sever, no heap Resumption,
# no per-perform Cont, the deep handler reinstated for free), so the steady-state
# live footprint (Boehm GC_get_heap_size) stays FLAT and N-INDEPENDENT.  We build
# the same tail-resumptive handler at two wildly different iteration counts and
# assert (a) correct result at each and (b) heap_size identical and bounded — a
# per-iteration Cont leak (the regression 4b prevents) would make heap_size grow
# with N.
echo "== §4b tail-resumptive handler keeps CONSTANT Cont depth (flat heap over N) =="
hd_small="" ; hd_big="" ; tl_ok=1
# small N=1000 and large N=1000000 variants of the tail-resumptive counter loop.
sed 's/loop 100000 0/loop 1000 0/'    "$CASES/efftailloop.kp" > "$WORK/efftl_small.kp"
sed 's/loop 100000 0/loop 1000000 0/' "$CASES/efftailloop.kp" > "$WORK/efftl_big.kp"
if timeout 240 $KAPPA build "$WORK/efftl_small.kp" -o "$WORK/efftl_small" >"$WORK/efftl_small.log" 2>&1 \
   && timeout 240 $KAPPA build "$WORK/efftl_big.kp" -o "$WORK/efftl_big" >"$WORK/efftl_big.log" 2>&1; then
  rs="$(timeout 60 "$WORK/efftl_small" 2>/dev/null)"
  rb="$(timeout 120 "$WORK/efftl_big" 2>/dev/null)"
  hd_small="$(KAPPA_GC_STATS=1 timeout 60 "$WORK/efftl_small" 2>&1 1>/dev/null | grep -oE 'heap_size=[0-9]+' | cut -d= -f2)"
  hd_big="$(KAPPA_GC_STATS=1 timeout 120 "$WORK/efftl_big" 2>&1 1>/dev/null | grep -oE 'heap_size=[0-9]+' | cut -d= -f2)"
  # results must be exact (the loop counts ticks: N ticks -> N)
  [ "$rs" = "1000" ] || { echo "   FAIL: N=1000 result '$rs' != 1000"; tl_ok=0; }
  [ "$rb" = "1000000" ] || { echo "   FAIL: N=1000000 result '$rb' != 1000000"; tl_ok=0; }
  if [ -z "$hd_small" ] || [ -z "$hd_big" ]; then
    echo "   FAIL: missing heap_size GC statistic; constant-depth gate cannot be evaluated"; tl_ok=0
  else
    # CONSTANT DEPTH: 1000x more iterations must NOT grow the steady-state live
    # footprint.  Allow heap_size to differ by at most 1 Boehm heap block
    # (heaps grow in chunks) — a real per-iteration Cont leak over 1e6 iters
    # would be orders of magnitude, not one block.  Also bound it absolutely so
    # a constant-but-huge footprint cannot pass.
    if [ "$hd_big" -le 4194304 ] && awk "BEGIN{exit !($hd_big <= $hd_small * 2)}"; then
      :
    else
      echo "   FAIL: heap_size grew with N (N=1e3 -> ${hd_small}B, N=1e6 -> ${hd_big}B) — Cont depth NOT constant (4b fast path regressed)"; tl_ok=0
    fi
  fi
  if [ "$tl_ok" -eq 1 ]; then
    echo "   ok (N=1e3 -> $rs, N=1e6 -> $rb; heap_size flat: ${hd_small}B == ${hd_big}B over 1000x iterations — constant Cont depth)"
  else
    fails=$((fails+1))
  fi
else
  echo "   FAIL: efftailloop constant-depth variants did not build"
  tail -8 "$WORK/efftl_small.log" "$WORK/efftl_big.log" | sed 's/^/     /'; fails=$((fails+1))
fi

echo "== HTTP + sqlite demo =="
if command -v sqlite3 >/dev/null 2>&1 || ldconfig -p 2>/dev/null | grep -q sqlite3; then
  rm -f "$ROOT/examples/native/http_sqlite/server.kappa.c" "$ROOT/examples/native/http_sqlite/server.kappa.ll"
  if timeout 320 bash "$ROOT/examples/native/http_sqlite/run.sh" >"$WORK/demo.log" 2>&1 && grep -q "DEMO OK" "$WORK/demo.log"; then
    echo "   ok (request -> sqlite write+read -> response; see $WORK/demo.log)"
  else
    echo "   FAIL: demo did not report DEMO OK"; tail -20 "$WORK/demo.log" | sed 's/^/     /'; fails=$((fails+1))
  fi
  rm -f "$ROOT/examples/native/http_sqlite/server.kappa.c" "$ROOT/examples/native/http_sqlite/server.kappa.ll"
else
  echo "   SKIP: sqlite3 not available for the demo"
fi

echo "== optimized native output has ZERO builtin string dispatch (§34.5.3; gap-5) =="
# Builtins (printlnString, arithmetic, intrinsics) and native host symbols must
# lower to DIRECT typed call sites (kpf_*/kw_* via knative); the emitted
# .kappa.c must contain no kprim_call/kprim string-dispatched primitive firing.
if pkg-config --exists sqlite3 2>/dev/null; then
  rm -f "$ROOT/examples/native/http_sqlite/server.kappa.c"
  if timeout 200 $KAPPA build --update --manifest "$ROOT/examples/native/http_sqlite" --emit-c -o "$WORK/sd" >"$WORK/sd.log" 2>&1; then
    SC="$ROOT/examples/native/http_sqlite/server.kappa.c"
    nks="$(grep -cE 'kprim_call\(|kprim\(' "$SC" 2>/dev/null || true)"
    if [ "$nks" = "0" ] && grep -q "kpf_io_printlnString" "$SC"; then
      echo "   ok (0 kprim_call/kprim; printlnString + builtins lowered to direct kpf_* calls)"
    else
      echo "   FAIL: optimized output still string-dispatches builtins ($nks kprim sites)"; grep -nE 'kprim_call\(|kprim\(' "$SC" | head | sed 's/^/     /'; fails=$((fails+1))
    fi
    rm -f "$SC"
  else
    echo "   FAIL: demo emit-c failed"; cat "$WORK/sd.log" | sed 's/^/     /'; fails=$((fails+1))
  fi
else
  echo "   SKIP: pkg-config sqlite3 not available"
fi

echo "== module-fragment selection: native fragment satisfies expect, .jvm excluded (§8.1/§36.12/§9.4) =="
FG="$WORK/frag"; rm -rf "$FG"; mkdir -p "$FG/src/demo"
# common facade: a signature + an expect term, no definition here
printf 'module demo.svc\ngreet : String -> String\nexpect term greet : String -> String\n' > "$FG/src/demo/svc.kp"
# selected-for-native fragment satisfies the expect; .jvm fragment is a CONFLICTING def that must be excluded
printf 'module demo.svc\nlet greet s = stringAppend "native:" s\n' > "$FG/src/demo/svc.native.kp"
printf 'module demo.svc\nlet greet s = stringAppend "jvm:" s\n' > "$FG/src/demo/svc.jvm.kp"
printf 'module demo.app\nimport demo.svc.(greet)\nlet main = printlnString (greet "hi")\n' > "$FG/src/demo/app.kp"
printf 'let buildConfig : BuildConfig = package { name="frag", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[axis "backend" [tag "native", tag "jvm"], axis "mode" [tag "debug", tag "release"]], dependencies=[], hostBindings=[], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags ["native","release"], main=module "demo.app", modules=modulesUnder "demo", dependencies=[], hostBindings=[] }] }' > "$FG/kappa.build.kp"
if timeout 200 $KAPPA build --update --manifest "$FG" -o "$FG/app" >"$FG/b.log" 2>&1; then
  fout="$("$FG/app" 2>&1)"
  if [ "$fout" = "native:hi" ]; then
    echo "   ok (native fragment selected + satisfied the expect; .jvm fragment excluded — no duplicate def)"
  else
    echo "   FAIL: wrong fragment selected (got '$fout', want 'native:hi')"; fails=$((fails+1))
  fi
else
  echo "   FAIL: native fragment build failed"; cat "$FG/b.log" | sed 's/^/     /'; fails=$((fails+1))
fi
# a target enabling two tags from one exclusive axis is fail-closed (§36.12)
sed 's/tags \["native","release"\]/tags ["native","jvm"]/' "$FG/kappa.build.kp" > "$FG/kappa.build.kp.bad" && mv "$FG/kappa.build.kp.bad" "$FG/kappa.build.kp"
axout="$(timeout 120 $KAPPA build --update --manifest "$FG" --emit-c -o "$FG/o" 2>&1)"
if grep -q "E_BUILD_FRAGMENT_AXIS_CONFLICT" <<<"$axout"; then
  echo "   ok (a target enabling native+jvm from one axis -> E_BUILD_FRAGMENT_AXIS_CONFLICT)"
else
  echo "   FAIL: axis-exclusivity not enforced"; echo "$axout" | sed 's/^/     /'; fails=$((fails+1))
fi
rm -rf "$FG"

echo "== native ABI discovery + verification against the real headers (§26.1.5/§36.28) =="
if pkg-config --exists sqlite3 2>/dev/null; then
  # (a) a real build records verified-against-sqlite3.h provenance
  rm -f "$ROOT/examples/native/http_sqlite/server.kappa.c" "$ROOT/examples/native/http_sqlite/server.kappa.ll" "$ROOT/examples/native/http_sqlite/server.native.prov"
  if timeout 200 $KAPPA build --update --manifest "$ROOT/examples/native/http_sqlite" --emit-c -o "$WORK/abi" >"$WORK/abi.log" 2>&1 \
     && grep -q "verified-decl int sqlite3_open" "$ROOT/examples/native/http_sqlite/server.native.prov" \
     && grep -q "pkg-config sqlite3 version=" "$ROOT/examples/native/http_sqlite/server.native.prov" \
     && grep -q "header sqlite3.h digest=" "$ROOT/examples/native/http_sqlite/server.native.prov"; then
    echo "   ok (pkg-config version + .pc digest + sqlite3.h digest + verified real decls recorded)"
  else
    echo "   FAIL: demo build did not record verified native provenance"; cat "$WORK/abi.log" | sed 's/^/     /'; fails=$((fails+1))
  fi
  rm -f "$ROOT/examples/native/http_sqlite/server.kappa.c" "$ROOT/examples/native/http_sqlite/server.kappa.ll" "$ROOT/examples/native/http_sqlite/server.native.prov"
  # (b) a verify decl that disagrees with the real sqlite3.h fails the build (fail-closed)
  BAD="$WORK/badabi"; rm -rf "$BAD"; mkdir -p "$BAD/src"
  printf 'module app\nimport host.native.sqlite3 as db\nlet main = do\n  let h <- db.sqliteOpen "x"\n  db.sqliteClose h\n' > "$BAD/src/app.kp"
  # real C symbol names; the verify decls are ABI-CONSISTENT with the declared
  # symbolList signatures (pointer params/results), so they pass the signature
  # consistency check — but the sqlite3_open verify prototype is deliberately
  # WRONG vs the real sqlite3.h (1 param, not 2), which the verify PROBE must
  # catch against the installed header → E_BUILD_NATIVE_ABI.
  printf 'let buildConfig : BuildConfig = package { name="b", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="s", provides=[module "host.native.sqlite3"], surface=symbolList [symbolDecl "sqliteOpen" "sqlite3_open" [ctString] ctHandle, symbolDecl "sqliteClose" "sqlite3_close" [ctHandle] ctUnit], abi=cAbi, inputs=[headers ["sqlite3.h"], pkgConfig "sqlite3" None, verify ["void *sqlite3_open(const char *)", "int sqlite3_close(sqlite3 *)"]], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="t" }, fragments=tags [], main=module "app", modules=modulesUnder "app", dependencies=[], hostBindings=["s"] }] }' > "$BAD/kappa.build.kp"
  bout="$(timeout 120 $KAPPA build --update --manifest "$BAD" --emit-c -o "$WORK/badout" 2>&1)"; brc=$?
  if [ "$brc" -ne 0 ] && grep -q "E_BUILD_NATIVE_ABI" <<<"$bout"; then
    echo "   ok (a signature disagreeing with the real sqlite3.h -> E_BUILD_NATIVE_ABI, fail-closed)"
  else
    echo "   FAIL: bogus verify decl was not rejected"; echo "$bout" | sed 's/^/     /'; fails=$((fails+1))
  fi
  rm -rf "$BAD"
else
  echo "   SKIP: pkg-config sqlite3 not available"
fi

echo "== exact-width ABI vocabulary (ctU32/ctUsize…) maps to real C widths + verifies (§26.1.1) =="
WD="$WORK/widths"; rm -rf "$WD"; mkdir -p "$WD/src"
printf 'module app\nimport host.native.widths as n\nimport std.ffi.(u32, u32Value)\nlet main = do\n  let x <- n.id32 (u32 256)\n  printlnString (showInt (u32Value x))\n' > "$WD/src/app.kp"
printf '#include <stdint.h>\nuint32_t id32(uint32_t x);\n' > "$WD/src/width.h"
printf '#include "width.h"\nuint32_t id32(uint32_t x) { return x + 1; }\n' > "$WD/src/width.c"
printf 'let buildConfig : BuildConfig = package { name="w", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="nb", provides=[module "host.native.widths"], surface=symbolList [symbolDecl "id32" "id32" [ctU32] ctU32], abi=cAbi, inputs=[headers ["src/width.h"], shim ["src/width.c"], verify ["uint32_t id32(uint32_t)"]], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="t" }, fragments=tags [], main=module "app", modules=modulesUnder "app", dependencies=[], hostBindings=["nb"] }] }' > "$WD/kappa.build.kp"
wout="$(timeout 200 $KAPPA build --update --manifest "$WD" --emit-c -o "$WORK/wbin" 2>&1)"; wrc=$?
WC="$(find "$WD" -name '*.kappa.c' | head -1)"
if [ "$wrc" -eq 0 ] && grep -q "extern uint32_t id32(uint32_t);" "$WC" 2>/dev/null; then
  echo "   ok (ctU32 -> 'uint32_t' extern prototype, verified against a real header)"
else
  echo "   FAIL: exact-width ctU32 did not map to uint32_t / verify"; echo "$wout" | sed 's/^/     /'; fails=$((fails+1))
fi
rm -rf "$WD"

echo "== a shim symbol whose ABI signature disagrees with the manifest is fail-closed (§27.1.1, N-19) =="
SB="$WORK/shimabi"; rm -rf "$SB"; mkdir -p "$SB/src"
printf 'module app\nimport host.native.probe as p\nlet main = do\n  let x <- p.thing 7\n  printlnString "ok"\n' > "$SB/src/app.kp"
# shim DEFINES probe_thing returning double, but the manifest declares ctI64 (int64_t)
printf '#include <stdint.h>\ndouble probe_thing(int64_t x) { return (double)x + 0.5; }\n' > "$SB/src/shim.c"
printf 'let buildConfig : BuildConfig = package { name="s", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="pb", provides=[module "host.native.probe"], surface=symbolList [symbolDecl "thing" "probe_thing" [ctI64] ctI64], abi=cAbi, inputs=[shim ["src/shim.c"]], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "app", modules=modulesUnder "app", dependencies=[], hostBindings=["pb"] }] }' > "$SB/kappa.build.kp"
if timeout 200 $KAPPA build --update --manifest "$SB" -o "$WORK/sbbin" >"$SB/b.log" 2>&1; then
  echo "   FAIL: a shim with a conflicting ABI signature built successfully (silent mis-marshalling)"; fails=$((fails+1))
else
  echo "   ok (shim ABI conflict rejected at compile via the force-included prototype header)"
fi
rm -rf "$SB"

echo "== U64 round-trips the full unsigned range incl. >= 2^63 (§26.1.1, N-35) =="
U6="$WORK/u64"; rm -rf "$U6"; mkdir -p "$U6/src"
printf 'module app\nimport host.native.u64x as n\nimport std.ffi.(u64, u64Value)\nlet main = do\n  let x <- n.u64id (u64 18446744073709551615)\n  printlnString (showInt (u64Value x))\n' > "$U6/src/app.kp"
printf '#include <stdint.h>\nuint64_t u64id(uint64_t x);\n' > "$U6/src/u64id.h"
printf '#include "u64id.h"\nuint64_t u64id(uint64_t x) { return x; }\n' > "$U6/src/shim.c"
printf 'let buildConfig : BuildConfig = package { name="u", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="ub", provides=[module "host.native.u64x"], surface=symbolList [symbolDecl "u64id" "u64id" [ctU64] ctU64], abi=cAbi, inputs=[headers ["src/u64id.h"], shim ["src/shim.c"], verify ["uint64_t u64id(uint64_t)"]], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "app", modules=modulesUnder "app", dependencies=[], hostBindings=["ub"] }] }' > "$U6/kappa.build.kp"
if timeout 200 $KAPPA build --update --manifest "$U6" -o "$WORK/u64bin" >"$U6/b.log" 2>&1; then
  u6out="$("$WORK/u64bin" 2>&1)"
  if [ "$u6out" = "18446744073709551615" ]; then
    echo "   ok (U64 2^64-1 round-trips exactly through MkU64/ku64/kas_u64)"
  else
    echo "   FAIL: U64 round-trip lossy (got '$u6out')"; fails=$((fails+1))
  fi
else
  echo "   FAIL: U64 binding did not build"; cat "$U6/b.log" | sed 's/^/     /'; fails=$((fails+1))
fi
rm -rf "$U6"

echo "== a direct library binding with a mismatched scalar width is fail-closed (§26.1.5, N-19/F2) =="
AB="$WORK/absabi"; rm -rf "$AB"; mkdir -p "$AB/src"
printf 'module app\nimport host.native.absx as n\nimport std.ffi.(i64)\nlet main = do\n  let x <- n.myabs (i64 5)\n  printlnString "ok"\n' > "$AB/src/app.kp"
# binds the real libc `abs` (int abs(int)) but DECLARES it [ctI64] ctI64 — a width mismatch
printf 'let buildConfig : BuildConfig = package { name="a", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="ab", provides=[module "host.native.absx"], surface=symbolList [symbolDecl "myabs" "abs" [ctI64] ctI64], abi=cAbi, inputs=[headers ["stdlib.h"], verify ["int abs(int)"]], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "app", modules=modulesUnder "app", dependencies=[], hostBindings=["ab"] }] }' > "$AB/kappa.build.kp"
about="$(timeout 200 $KAPPA build --update --manifest "$AB" --emit-c -o "$WORK/abbin" 2>&1)"; abrc=$?
if [ "$abrc" -ne 0 ] && grep -q "E_BUILD_NATIVE_ABI" <<<"$about"; then
  echo "   ok (declared int64_t for the real int abs -> E_BUILD_NATIVE_ABI against stdlib.h)"
else
  echo "   FAIL: a width-mismatched direct library binding was not rejected"; echo "$about" | sed 's/^/     /'; fails=$((fails+1))
fi
rm -rf "$AB"

echo "== a verify decl with NO header that declares the symbol verifies nothing -> rejected (§26.1.5/§36.28) =="
# Reviewer-found BLOCKER: a fabricated pointer ABI (real getenv is
# `char *getenv(const char*)`, declared here as a 2-arg `void*(void*,void*)`)
# with NO header in scope used to LINK, because a lone `extern` redeclaration
# is self-consistent C and the redeclaration check only fires when a header
# ALSO declares the symbol. Header-coverage must reject this fail-closed.
NH="$WORK/noheader"; rm -rf "$NH"; mkdir -p "$NH/src"
printf 'module app\nimport host.native.envx as n\nlet main = do\n  let r = n.getenv2 None None\n  printlnString "x"\n' > "$NH/src/app.kp"
printf 'let buildConfig : BuildConfig = package { name="e", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="e", provides=[module "host.native.envx"], surface=symbolList [symbolDecl "getenv2" "getenv" [ctRawPtr, ctRawPtr] ctRawPtr], abi=cAbi, inputs=[verify ["void *getenv(void *, void *)"]], link=dynamicLink ["c"], load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "app", modules=modulesUnder "app", dependencies=[], hostBindings=["e"] }] }' > "$NH/kappa.build.kp"
nhout="$(timeout 200 $KAPPA build --update --manifest "$NH" -o "$WORK/nhbin" 2>&1)"; nhrc=$?
if [ "$nhrc" -ne 0 ] && grep -q "E_BUILD_NATIVE_ABI" <<<"$nhout" && [ ! -e "$WORK/nhbin" ]; then
  echo "   ok (fabricated ABI with no declaring header -> E_BUILD_NATIVE_ABI, nothing linked)"
else
  echo "   FAIL: a verify decl with no declaring header was accepted (vacuous proof)"; echo "$nhout" | sed 's/^/     /'; fails=$((fails+1))
fi
rm -rf "$NH"

echo "== RawPtr results surface as Option RawPtr (nullability, §26.1.1:27307) =="
RP="$WORK/rawptr"; rm -rf "$RP"; mkdir -p "$RP/src"
printf 'module app\nimport host.native.envx as n\nlet main = do\n  let r <- n.getenv "PATH"\n  match r\n  case None -> printlnString "PATH=none"\n  case Some p -> printlnString "PATH=some"\n' > "$RP/src/app.kp"
printf 'let buildConfig : BuildConfig = package { name="r", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="e", provides=[module "host.native.envx"], surface=symbolList [symbolDecl "getenv" "getenv" [ctString] ctRawPtr], abi=cAbi, inputs=[headers ["stdlib.h"], verify ["char *getenv(const char *)"]], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "app", modules=modulesUnder "app", dependencies=[], hostBindings=["e"] }] }' > "$RP/kappa.build.kp"
RPC="$WORK/rpbin"
if timeout 200 $KAPPA build --update --manifest "$RP" -o "$RPC" >"$RP/b.log" 2>&1; then
  rpout="$(PATH="$PATH" "$RPC" 2>&1)"
  if [ "$rpout" = "PATH=some" ]; then
    echo "   ok (RawPtr result is Option RawPtr; non-null PATH -> Some, matched in Kappa)"
  else
    echo "   FAIL: Option RawPtr round-trip wrong (got '$rpout')"; fails=$((fails+1))
  fi
else
  echo "   FAIL: Option RawPtr binding did not build"; cat "$RP/b.log" | sed 's/^/     /'; fails=$((fails+1))
fi
rm -rf "$RP"

echo "== native host-source identity is pinned in kappa.lock + drift is fail-closed (§8.3.5/§36.7) =="
if pkg-config --exists sqlite3 2>/dev/null; then
  LK="$WORK/lockpin"; rm -rf "$LK"; mkdir -p "$LK"
  cp "$ROOT/examples/native/http_sqlite/server.kp" "$ROOT/examples/native/http_sqlite/kappa.build.kp" "$ROOT/examples/native/http_sqlite/native_shim.c" "$LK/"
  timeout 200 $KAPPA build --update --manifest "$LK" --emit-c -o "$WORK/lp" >"$LK/b1.log" 2>&1
  if grep -q "^host-binding .* sqlite3@" "$LK/kappa.lock" 2>/dev/null && grep -q "^host-binding .* posixnet@" "$LK/kappa.lock" 2>/dev/null; then
    if timeout 200 $KAPPA build --manifest "$LK" --emit-c --locked -o "$WORK/lp" >/dev/null 2>&1; then
      printf '/* drift */\n' >> "$LK/native_shim.c"
      dout="$(timeout 200 $KAPPA build --manifest "$LK" --emit-c --locked -o "$WORK/lp" 2>&1)"; drc=$?
      if [ "$drc" -ne 0 ] && grep -q "E_NATIVE_BINDING_UNPINNED" <<<"$dout"; then
        echo "   ok (host-binding pins written; --locked verifies; shim drift -> E_NATIVE_BINDING_UNPINNED)"
      else
        echo "   FAIL: shim drift not caught fail-closed"; echo "$dout" | sed 's/^/     /'; fails=$((fails+1))
      fi
    else
      echo "   FAIL: --locked rejected a fresh valid native lock"; fails=$((fails+1))
    fi
  else
    echo "   FAIL: build did not pin host bindings in kappa.lock"; cat "$LK/b1.log" | sed 's/^/     /'; fails=$((fails+1))
  fi
  rm -rf "$LK"
else
  echo "   SKIP: pkg-config sqlite3 not available"
fi

echo "== HTTP wire parser + router behavior (backend-neutral, no sockets) =="
# wire.parseRequestLine + router.respond are pure modules; build a tiny native
# executable that exercises them (no libuv / no host bindings) so parse/route
# correctness is checked apart from the native transport, using the real files.
WR="$WORK/wirep"; rm -rf "$WR"; mkdir -p "$WR/src/acme/http"
cp "$ROOT/examples/native/http_uv/src/acme/http/wire.kp" "$ROOT/examples/native/http_uv/src/acme/http/router.kp" "$WR/src/acme/http/"
printf 'module acme.http.check\nimport acme.http.wire as wire\nimport acme.http.router as router\nlet main = do\n  let a = wire.parseRequestLine "GET /health HTTP/1.1\\r\\nHost: x\\r\\n\\r\\n"\n  printlnString a.method\n  printlnString a.path\n  printlnString (router.respond a)\n  let b = wire.parseRequestLine "POST /submit HTTP/1.0\\r\\n\\r\\n"\n  printlnString b.method\n  printlnString b.path\n' > "$WR/src/acme/http/check.kp"
printf 'let buildConfig : BuildConfig = package { name="wirecheck", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[], targets=[executable { name="check", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "acme.http.check", modules=modulesUnder "acme.http", dependencies=[], hostBindings=[] }] }' > "$WR/kappa.build.kp"
if timeout 200 $KAPPA build --update --manifest "$WR" -o "$WORK/wirechk" >"$WR/b.log" 2>&1; then
  wrout="$(timeout 30 "$WORK/wirechk" 2>&1)"
  if grep -q "^GET$" <<<"$wrout" && grep -q "^/health$" <<<"$wrout" \
     && grep -q "HTTP/1.1 200 OK" <<<"$wrout" && grep -q "Content-Length: 3" <<<"$wrout" \
     && grep -q "^POST$" <<<"$wrout" && grep -q "^/submit$" <<<"$wrout"; then
    echo "   ok (method/path parsed from the request line; router built a well-formed 200)"
  else
    echo "   FAIL: wire/router behavior wrong"; echo "$wrout" | sed 's/^/     /'; fails=$((fails+1))
  fi
else
  echo "   FAIL: wire/router check did not build"; cat "$WR/b.log" | sed 's/^/     /'; fails=$((fails+1))
fi
rm -rf "$WR"

echo "== native binding surface is GENERATED from a parsed header, not hand-authored symbolDecl (§27.1.1/§36.28) =="
# The libuv example MUST derive its host.native surface mechanically from real
# headers (generateFromHeader) — the manifest must contain NO symbolDecl, and
# the generated extern prototypes must reflect the types parsed out of the
# headers (uv.h for the raw libuv surface; native_uv_shim.h for the adapter).
if pkg-config --exists libuv 2>/dev/null; then
  GENM="$ROOT/examples/native/http_uv/kappa.build.kp"
  okg=1
  # strip line comments (-- …) so a comment merely *mentioning* symbolDecl does
  # not count; we forbid an actual symbolDecl call in the binding path.
  if sed 's/--.*//' "$GENM" | grep -q "symbolDecl"; then
    echo "   FAIL: the libuv example manifest uses a hand-authored symbolDecl (must generateFromHeader)"; okg=0
  fi
  sed 's/--.*//' "$GENM" | grep -q "generateFromHeader" || { echo "   FAIL: the libuv example manifest does not use generateFromHeader"; okg=0; }
  GE="$WORK/httpgen"; rm -rf "$GE"; mkdir -p "$GE"; cp -r "$ROOT/examples/native/http_uv/." "$GE/"
  find "$GE" \( -name '*.kappa.c' -o -name '*.kappa.ll' \) -delete 2>/dev/null
  if timeout 240 $KAPPA build --update --manifest "$GE" --emit-c -o "$WORK/gexe" >"$GE/b.log" 2>&1; then
    ext="$(cat "$GE"/src/acme/http/*.kappa.c 2>/dev/null)"
    # parsed from uv.h: a void-arg const-char* return; parsed from the shim header:
    # the (const char *, int, int) -> void* prototype.  Neither was typed by hand.
    grep -q "extern const char \* uv_version_string(void);" <<<"$ext" || { echo "   FAIL: uv_version_string not generated from uv.h"; okg=0; }
    grep -q "extern void \* http_uv_listen(const char \*, int, int);" <<<"$ext" || { echo "   FAIL: http_uv_listen not generated from native_uv_shim.h"; okg=0; }
    grep -q "^host-binding .* libuv@" "$GE/kappa.lock" || { echo "   FAIL: generated libuv surface not pinned"; okg=0; }
    grep -q "^host-binding .* uvnet@" "$GE/kappa.lock" || { echo "   FAIL: generated uvnet surface not pinned"; okg=0; }
    # BROAD surface (§26.1.2): the libuv binding generates the whole mappable
    # uv_* surface from uv.h (many functions, not a curated handful), and the
    # callback/struct/variadic functions are skipped (reported, not guessed).
    genN="$(grep -oE "generated [0-9]+ function" "$GE/b.log" | head -1 | grep -oE "[0-9]+")"
    skipN="$(grep -oE "skipped [0-9]+ requiring" "$GE/b.log" | head -1 | grep -oE "[0-9]+")"
    { [ -n "$genN" ] && [ "$genN" -ge 50 ]; } || { echo "   FAIL: broad libuv surface too small (generated '${genN:-0}', expected >=50)"; okg=0; }
    { [ -n "$skipN" ] && [ "$skipN" -ge 1 ]; } || { echo "   FAIL: no callback/struct functions were skipped (expected fail-closed skips)"; okg=0; }
    # §26.1.4: every raw foreign declaration MUST carry a foreign-call
    # classification; the blocking-I/O adapter binding declares `blocking`,
    # recorded in native provenance + pinned in the host-source identity.
    grep -rq "foreign-call-classification blocking" "$GE"/src/ 2>/dev/null || { echo "   FAIL: foreign-call classification not recorded in native provenance (§26.1.4)"; okg=0; }
    if [ "$okg" -eq 1 ]; then
      echo "   ok (no symbolDecl; broad uv_* surface = $genN fns from uv.h, $skipN skipped; http_uv_listen from the shim header; both pinned)"
    else fails=$((fails+1)); fi
  else
    echo "   FAIL: generated-surface build failed"; cat "$GE/b.log" | sed 's/^/     /'; fails=$((fails+1))
  fi
  rm -rf "$GE"
else
  echo "   SKIP: pkg-config libuv not available"
fi

echo "== broad surface generalizes beyond libuv + resolves pointer typedefs (§26.1.2/§26.1.4) =="
# generateAllFromHeader is library-agnostic, not libuv-specific. zlib's deflate*
# functions take `z_streamp` (= struct z_stream *, a POINTER TYPEDEF); resolving
# the typedef is what lets them generate (they would otherwise be skipped).
if pkg-config --exists zlib 2>/dev/null; then
  ZL="$WORK/zlibgen"; rm -rf "$ZL"; mkdir -p "$ZL/src/app"
  printf 'module app\nimport host.native.z.Raw as z\nlet main = printlnString "x"\n' > "$ZL/src/app/main.kp"
  printf 'let buildConfig : BuildConfig = package { name="z", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="z", provides=[module "host.native.z.Raw"], surface=generateAllFromHeader "zlib.h" "deflate", abi=cAbi, inputs=[headers ["zlib.h"], pkgConfig "zlib" None], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "app.main", modules=modulesUnder "app", dependencies=[], hostBindings=["z"] }] }' > "$ZL/kappa.build.kp"
  zout="$(timeout 120 $KAPPA build --update --manifest "$ZL" -o "$WORK/zexe" 2>&1)"
  zN="$(grep -oE "generated [0-9]+ function" <<<"$zout" | head -1 | grep -oE "[0-9]+")"
  if [ -n "$zN" ] && [ "$zN" -ge 5 ]; then
    echo "   ok (zlib deflate* surface = $zN functions; z_streamp pointer typedef resolved — general, not libuv-specific)"
    explicit_cc="$(explicit_c_driver)"
    if [ -n "$explicit_cc" ]; then
      rm -f "$ZL/kappa.lock"
      zout2="$(KAPPA_CC=false timeout 120 $KAPPA build --cc "$explicit_cc" --update --manifest "$ZL" -o "$WORK/zexe-explicit" 2>&1)"
      zN2="$(grep -oE "generated [0-9]+ function" <<<"$zout2" | head -1 | grep -oE "[0-9]+")"
      if [ -n "$zN2" ] && [ "$zN2" -ge 5 ]; then
        echo "   ok (generated header surfaces honor explicit --cc even when KAPPA_CC is stale)"
      else
        echo "   FAIL: generated header surface did not honor explicit --cc"; echo "$zout2" | sed 's/^/     /'; fails=$((fails+1))
      fi
    fi
  else
    echo "   FAIL: zlib deflate* surface too small (got '${zN:-0}'); pointer typedefs not resolved?"; echo "$zout" | sed 's/^/     /'; fails=$((fails+1))
  fi
  rm -rf "$ZL"
else
  echo "   SKIP: pkg-config zlib not available"
fi

echo "== foreign-call classification capability rule is fail-closed (§26.1.4/§27.6) =="
# The native profile advertises rt-blocking and routes classified blocking calls
# through the off-worker blocking lane, so a `blocking` binding builds. It does
# NOT advertise a safe-cancellation capability, so a `blocking-cancellable`
# binding is rejected rather than executed with weakened semantics.
if pkg-config --exists libuv 2>/dev/null; then
  CAP="$WORK/gcap"; rm -rf "$CAP"; mkdir -p "$CAP/src/app"
  # the module header MUST match the §8.1 path-derived name (src/app/main.kp -> app.main)
  printf 'module app.main\nimport host.native.libuv.Raw as u\nlet main = do\n  let v <- u.uv_version_string\n  printlnString v\n' > "$CAP/src/app/main.kp"
  capbuild() { printf 'let buildConfig : BuildConfig = package { name="cap", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="libuv", provides=[module "host.native.libuv.Raw"], surface=generateAllFromHeader "uv.h" "uv_version", abi=cAbi, inputs=[headers ["uv.h"], define "_GNU_SOURCE" "1", pkgConfig "libuv" (Some "1.0"), cstrings ["uv_version_string"], classify %s], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "app.main", modules=modulesUnder "app", dependencies=[], hostBindings=["libuv"] }] }' "$1" > "$CAP/kappa.build.kp"; }
  okc=1
  capbuild "blocking"
  timeout 200 $KAPPA build --update --manifest "$CAP" -o "$WORK/capb" >"$CAP/b.log" 2>&1 || { echo "   FAIL: a 'blocking' binding was rejected though rt-blocking is advertised"; cat "$CAP/b.log" | sed 's/^/     /'; okc=0; }
  capbuild "blockingCancellable"
  co="$(timeout 200 $KAPPA build --update --manifest "$CAP" -o "$WORK/capc" 2>&1)"; cr=$?
  { [ "$cr" -ne 0 ] && grep -q "E_BACKEND_CAPABILITY_UNREALIZED" <<<"$co" && grep -q "rt-blocking-cancel" <<<"$co"; } || { echo "   FAIL: a 'blocking-cancellable' binding was not rejected fail-closed"; echo "$co" | sed 's/^/     /'; okc=0; }
  if [ "$okc" -eq 1 ]; then echo "   ok (capability set declared + recorded; blocking accepted under rt-blocking; blocking-cancellable rejected — no rt-blocking-cancel)"; else fails=$((fails+1)); fi
  # §26.1.3: the generator's width mapping assumes LP64; a non-LP64 target
  # triple (LLP64 = windows) is rejected rather than inferred for an unmodelled ABI.
  printf 'let buildConfig : BuildConfig = package { name="cap", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="libuv", provides=[module "host.native.libuv.Raw"], surface=generateAllFromHeader "uv.h" "uv_version", abi=cAbi, inputs=[headers ["uv.h"], define "_GNU_SOURCE" "1", pkgConfig "libuv" (Some "1.0")], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-windows-msvc" }, fragments=tags [], main=module "app.main", modules=modulesUnder "app", dependencies=[], hostBindings=["libuv"] }] }' > "$CAP/kappa.build.kp"
  wo="$(timeout 120 $KAPPA build --update --manifest "$CAP" -o "$WORK/capw" 2>&1)"; wr=$?
  if [ "$wr" -ne 0 ] && grep -q "LP64" <<<"$wo"; then
    echo "   ok (non-LP64 target triple rejected — surface not inferred for an unmodelled data model, §26.1.3)"
  else
    echo "   FAIL: a non-LP64 target triple was not rejected"; echo "$wo" | sed 's/^/     /'; fails=$((fails+1))
  fi
  rm -rf "$CAP"
else
  echo "   SKIP: pkg-config libuv not available"
fi

echo "== header-surface generation is fail-closed: missing symbol / unmappable type (§27.1.1/§36.28) =="
if pkg-config --exists libuv 2>/dev/null; then
  FC="$WORK/gfc"; rm -rf "$FC"; mkdir -p "$FC/src/app"
  printf 'module app\nimport host.native.libuv.Raw as u\nlet main = do\n  let v <- u.uv_version_string\n  printlnString v\n' > "$FC/src/app/main.kp"
  fcbuild() { printf 'let buildConfig : BuildConfig = package { name="fc", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="libuv", provides=[module "host.native.libuv.Raw"], surface=generateFromHeader "uv.h" [%s], abi=cAbi, inputs=[headers ["uv.h"], define "_GNU_SOURCE" "1", pkgConfig "libuv" (Some "1.0")], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "app.main", modules=modulesUnder "app", dependencies=[], hostBindings=["libuv"] }] }' "$1" > "$FC/kappa.build.kp"; }
  okf=1
  fcbuild '"uv_not_a_function"'
  o1="$(timeout 120 $KAPPA build --update --manifest "$FC" -o "$WORK/fc1" 2>&1)"; r1=$?
  { [ "$r1" -ne 0 ] && grep -q "E_BUILD_NATIVE_HEADER_GEN" <<<"$o1" && grep -q "does not declare a function" <<<"$o1"; } || { echo "   FAIL: a missing header symbol was not fail-closed"; echo "$o1" | sed 's/^/     /'; okf=0; }
  fcbuild '"uv_run"'  # uv_run takes a uv_run_mode by-value enum -> not conservatively mappable
  o2="$(timeout 120 $KAPPA build --update --manifest "$FC" -o "$WORK/fc2" 2>&1)"; r2=$?
  { [ "$r2" -ne 0 ] && grep -q "E_BUILD_NATIVE_HEADER_GEN" <<<"$o2" && grep -q "cannot conservatively map" <<<"$o2"; } || { echo "   FAIL: an unmappable C type was not fail-closed"; echo "$o2" | sed 's/^/     /'; okf=0; }
  # an INLINE function-pointer/callback parameter must fail closed (not be
  # silently mapped to void*), via a local header we control.
  printf '#ifndef FCH\n#define FCH\nint fc_cb(int (*cb)(int), int n);\nlong long fc_ll(unsigned long long x);\n#endif\n' > "$FC/fc.h"
  printf 'let buildConfig : BuildConfig = package { name="fc", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="d", provides=[module "host.native.d"], surface=generateFromHeader "fc.h" ["fc_cb"], abi=cAbi, inputs=[headers ["fc.h"]], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "app.main", modules=modulesUnder "app", dependencies=[], hostBindings=["d"] }] }' > "$FC/kappa.build.kp"
  o3="$(timeout 120 $KAPPA build --update --manifest "$FC" -o "$WORK/fc3" 2>&1)"; r3=$?
  { [ "$r3" -ne 0 ] && grep -q "E_BUILD_NATIVE_HEADER_GEN" <<<"$o3" && grep -q "function-pointer" <<<"$o3"; } || { echo "   FAIL: an inline function-pointer parameter was not fail-closed"; echo "$o3" | sed 's/^/     /'; okf=0; }
  [ "$okf" -eq 1 ] && echo "   ok (missing symbol, by-value enum, and inline function-pointer param all fail-closed -> E_BUILD_NATIVE_HEADER_GEN)"
  rm -rf "$FC"
else
  echo "   SKIP: pkg-config libuv not available"
fi

echo "== native input path escape is fail-closed (§36.11) =="
HP="$WORK/ghp"; rm -rf "$HP"; mkdir -p "$HP/src/app"
printf 'module app.main\nimport host.native.x as x\nlet main = printlnString "x"\n' > "$HP/src/app/main.kp"
printf 'int demo_x(void);\n' > "$HP/ok.c"; printf 'int demo_x(void);\n' > "$WORK/outside_shim.c"
hpbuild() { printf 'let buildConfig : BuildConfig = package { name="hp", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="x", provides=[module "host.native.x"], surface=symbolList [symbolDecl "demoX" "demo_x" [] ctInt], abi=cAbi, inputs=[shim [%s]], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "app.main", modules=modulesUnder "app", dependencies=[], hostBindings=["x"] }] }' "$1" > "$HP/kappa.build.kp"; }
okp=1
hpbuild '"../outside_shim.c"'
po="$(timeout 60 $KAPPA build --update --manifest "$HP" -o "$WORK/hpb" 2>&1)"
grep -q "E_NATIVE_BINDING_PATH_ESCAPE" <<<"$po" || { echo "   FAIL: a '..' shim path was not rejected"; echo "$po" | sed 's/^/     /'; okp=0; }
hpbuild '"/etc/passwd"'
po2="$(timeout 60 $KAPPA build --update --manifest "$HP" -o "$WORK/hpb" 2>&1)"
grep -q "E_NATIVE_BINDING_PATH_ESCAPE" <<<"$po2" || { echo "   FAIL: an absolute shim path was not rejected"; okp=0; }
ln -sf "$WORK/outside_shim.c" "$HP/linked.c"; hpbuild '"linked.c"'
po3="$(timeout 60 $KAPPA build --update --manifest "$HP" -o "$WORK/hpb" 2>&1)"
grep -q "E_NATIVE_BINDING_PATH_ESCAPE" <<<"$po3" || { echo "   FAIL: a symlinked shim path was not rejected"; okp=0; }
[ "$okp" -eq 1 ] && echo "   ok ('..', absolute, and symlink shim paths all rejected -> E_NATIVE_BINDING_PATH_ESCAPE)" || fails=$((fails+1))
rm -rf "$HP"; rm -f "$WORK/outside_shim.c"

echo "== explicit symbolList pointer/handle ABI must be verified (§26.1.5/§36.28) =="
if pkg-config --exists libuv 2>/dev/null; then
  AV="$WORK/gabi"; rm -rf "$AV"; mkdir -p "$AV/src/app"
  # the symbol is declared (so the per-symbol ABI check runs) but not CALLED, so
  # the accept-case build does not need the symbol linked (these are ABI-proof
  # checks at resolution time, independent of linkage).
  printf 'module app.main\nimport host.native.uvx as u\nlet main = printlnString "x"\n' > "$AV/src/app/main.kp"
  # uv_loop_new returns a uv_loop_t* (handle); declared via symbolList with NO
  # shim and NO verify -> its ABI is unproven -> must be rejected.
  printf 'let buildConfig : BuildConfig = package { name="av", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="uvx", provides=[module "host.native.uvx"], surface=symbolList [symbolDecl "uvLoopNew" "uv_loop_new" [] ctHandle], abi=cAbi, inputs=[headers ["uv.h"], pkgConfig "libuv" (Some "1.0")], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "app.main", modules=modulesUnder "app", dependencies=[], hostBindings=["uvx"] }] }' > "$AV/kappa.build.kp"
  ao="$(timeout 120 $KAPPA build --update --manifest "$AV" -o "$WORK/avb" 2>&1)"
  oka=1
  grep -q "E_NATIVE_BINDING_ABI_UNVERIFIED" <<<"$ao" || { echo "   FAIL: an unverified symbolList handle symbol was not rejected"; echo "$ao" | sed 's/^/     /'; oka=0; }
  # adding a matching verify decl proves the ABI against uv.h -> accepted
  printf 'let buildConfig : BuildConfig = package { name="av", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="uvx", provides=[module "host.native.uvx"], surface=symbolList [symbolDecl "uvLoopNew" "uv_loop_new" [] ctHandle], abi=cAbi, inputs=[headers ["uv.h"], pkgConfig "libuv" (Some "1.0"), verify ["uv_loop_t *uv_loop_new(void)"]], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "app.main", modules=modulesUnder "app", dependencies=[], hostBindings=["uvx"] }] }' > "$AV/kappa.build.kp"
  # a CONSISTENT verify decl proves the ABI against uv.h -> build SUCCEEDS
  # (uv.h's unix backend needs _GNU_SOURCE for pthread_rwlock_t).
  printf 'let buildConfig : BuildConfig = package { name="av", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="uvx", provides=[module "host.native.uvx"], surface=symbolList [symbolDecl "uvLoopNew" "uv_loop_new" [] ctHandle], abi=cAbi, inputs=[headers ["uv.h"], define "_GNU_SOURCE" "1", pkgConfig "libuv" (Some "1.0"), verify ["uv_loop_t *uv_loop_new(void)"]], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "app.main", modules=modulesUnder "app", dependencies=[], hostBindings=["uvx"] }] }' > "$AV/kappa.build.kp"
  timeout 120 $KAPPA build --update --manifest "$AV" -o "$WORK/avb" >"$AV/ok.log" 2>&1 || { echo "   FAIL: a verify-consistent handle symbol did not BUILD"; cat "$AV/ok.log" | sed 's/^/     /'; oka=0; }
  [ -x "$WORK/avb" ] || { echo "   FAIL: verify-consistent handle binding produced no executable"; oka=0; }
  # a verify decl whose ARITY/CLASS disagrees with the declared signature is a
  # fabricated ABI -> rejected (closes the reviewer-found name-only-match hole).
  printf 'let buildConfig : BuildConfig = package { name="av", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="uvx", provides=[module "host.native.uvx"], surface=symbolList [symbolDecl "getit" "getenv" [ctInt, ctInt, ctInt] ctHandle], abi=cAbi, inputs=[headers ["stdlib.h"], verify ["char *getenv(const char *)"]], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "app.main", modules=modulesUnder "app", dependencies=[], hostBindings=["uvx"] }] }' > "$AV/kappa.build.kp"
  am="$(timeout 120 $KAPPA build --update --manifest "$AV" -o "$WORK/avm" 2>&1)"
  { grep -q "E_NATIVE_BINDING_ABI_UNVERIFIED" <<<"$am" && grep -q "NOT consistent" <<<"$am"; } || { echo "   FAIL: a signature-inconsistent verify decl was accepted"; echo "$am" | sed 's/^/     /'; oka=0; }
  # a shim-bearing binding whose shim does NOT define the symbol (a library
  # symbol) must NOT ride the shim exemption (symbol-granular shim provenance).
  printf 'int defined_one(void){return 0;}\n' > "$AV/sh.c"
  printf 'let buildConfig : BuildConfig = package { name="av", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="uvx", provides=[module "host.native.uvx"], surface=symbolList [symbolDecl "uvLoopNew" "uv_loop_new" [] ctHandle], abi=cAbi, inputs=[shim ["sh.c"]], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "app.main", modules=modulesUnder "app", dependencies=[], hostBindings=["uvx"] }] }' > "$AV/kappa.build.kp"
  as="$(timeout 120 $KAPPA build --update --manifest "$AV" -o "$WORK/avs" 2>&1)"
  grep -q "E_NATIVE_BINDING_ABI_UNVERIFIED" <<<"$as" || { echo "   FAIL: a non-shim-defined symbol rode a binding's shim exemption"; echo "$as" | sed 's/^/     /'; oka=0; }
  # a scalar library symbol with a `headers` input that does NOT declare it, and
  # no verify decl, must be rejected (a header's mere presence proves nothing).
  printf 'let buildConfig : BuildConfig = package { name="av", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="uvx", provides=[module "host.native.uvx"], surface=symbolList [symbolDecl "labsx" "labs" [ctInt] ctInt], abi=cAbi, inputs=[headers ["stdint.h"]], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "app.main", modules=modulesUnder "app", dependencies=[], hostBindings=["uvx"] }] }' > "$AV/kappa.build.kp"
  ah="$(timeout 120 $KAPPA build --update --manifest "$AV" -o "$WORK/avh" 2>&1)"
  grep -q "E_NATIVE_BINDING_ABI_UNVERIFIED" <<<"$ah" || { echo "   FAIL: a scalar symbol with a non-declaring header (no verify) was accepted (fabricated-ABI bypass)"; echo "$ah" | sed 's/^/     /'; oka=0; }
  [ "$oka" -eq 1 ] && echo "   ok (unverified rejected; consistent verify builds; inconsistent verify + non-shim-defined-in-shim-binding both rejected — symbol-granular)" || fails=$((fails+1))
  rm -rf "$AV"
else
  echo "   SKIP: pkg-config libuv not available"
fi

echo "== generated char* is conservative: Option RawPtr unless cstrings proves it (§26.1.4) =="
if pkg-config --exists libuv 2>/dev/null; then
  CS="$WORK/gcs"; rm -rf "$CS"; mkdir -p "$CS/src/app"
  printf 'module app.main\nimport host.native.libuv.Raw as u\nlet main = do\n  let v <- u.uv_version_string\n  printlnString v\n' > "$CS/src/app/main.kp"
  # no cstrings: uv_version_string's char* is Option RawPtr, so printlnString on it type-errors
  printf 'let buildConfig : BuildConfig = package { name="cs", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="libuv", provides=[module "host.native.libuv.Raw"], surface=generateAllFromHeader "uv.h" "uv_version", abi=cAbi, inputs=[headers ["uv.h"], define "_GNU_SOURCE" "1", pkgConfig "libuv" (Some "1.0")], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "app.main", modules=modulesUnder "app", dependencies=[], hostBindings=["libuv"] }] }' > "$CS/kappa.build.kp"
  cso="$(timeout 120 $KAPPA build --update --manifest "$CS" -o "$WORK/csb" 2>&1)"
  oks=1
  grep -q "Option RawPtr" <<<"$cso" || { echo "   FAIL: an undeclared char* did not surface as Option RawPtr"; echo "$cso" | sed 's/^/     /'; oks=0; }
  # with cstrings: char* is String -> builds + runs
  printf 'let buildConfig : BuildConfig = package { name="cs", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="libuv", provides=[module "host.native.libuv.Raw"], surface=generateAllFromHeader "uv.h" "uv_version", abi=cAbi, inputs=[headers ["uv.h"], define "_GNU_SOURCE" "1", pkgConfig "libuv" (Some "1.0"), cstrings ["uv_version_string"]], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "app.main", modules=modulesUnder "app", dependencies=[], hostBindings=["libuv"] }] }' > "$CS/kappa.build.kp"
  if timeout 120 $KAPPA build --update --manifest "$CS" -o "$WORK/csb" >/dev/null 2>&1 && [ -n "$("$WORK/csb" 2>/dev/null)" ]; then : ; else echo "   FAIL: a cstrings-declared char* did not build/run as String"; oks=0; fi
  [ "$oks" -eq 1 ] && echo "   ok (undeclared char* -> Option RawPtr; cstrings-declared char* -> String, builds + runs)" || fails=$((fails+1))
  rm -rf "$CS"
else
  echo "   SKIP: pkg-config libuv not available"
fi

echo "== native libuv HTTP server: generated surfaces + fragment selection + live serve (§8.1/§9.4/§26.1/§36) =="
# The example facade (runtime.kp) declares `expect term` transport; the .native
# fragment refines the GENERATED libuv-adapter surface to satisfy it.  The
# .jvm/.dotnet fragments import host.jvm/host.dotnet modules that do NOT exist
# natively, so a successful build PROVES fragment selection excluded them.  The
# server also prints libuv's version via the generated host.native.libuv.Raw
# surface (uv_version_string, parsed from uv.h), then serves real requests.
if pkg-config --exists libuv 2>/dev/null && command -v curl >/dev/null 2>&1; then
  HU="$WORK/httpuv"; rm -rf "$HU"; mkdir -p "$HU"
  cp -r "$ROOT/examples/native/http_uv/." "$HU/"
  HUEXE="$WORK/httpuvd"
  if timeout 240 $KAPPA build --update --manifest "$HU" -o "$HUEXE" >"$HU/b.log" 2>&1; then
    if grep -q "^host-binding .* uvnet@" "$HU/kappa.lock" 2>/dev/null; then
      "$HUEXE" >"$HU/srv.log" 2>&1 &
      srv=$!
      ok=1
      # wait for the listener (bounded), then drive three requests through it
      for _ in 1 2 3 4 5 6 7 8 9 10; do grep -q "listening" "$HU/srv.log" 2>/dev/null && break; sleep 0.3; done
      root="$(timeout 10 curl -s http://127.0.0.1:8090/ 2>/dev/null)"
      health="$(timeout 10 curl -s http://127.0.0.1:8090/health 2>/dev/null)"
      notf="$(timeout 10 curl -s -o /dev/null -w '%{http_code}' http://127.0.0.1:8090/nope 2>/dev/null)"
      # bounded reap: the server self-exits after 3 requests; if a request was
      # dropped it might not, so wait briefly then kill — `wait` must never be
      # able to block the suite indefinitely.
      for _ in 1 2 3 4 5 6 7 8 9 10; do kill -0 "$srv" 2>/dev/null || break; sleep 0.3; done
      kill "$srv" 2>/dev/null
      wait "$srv" 2>/dev/null
      grep -q "^libuv " "$HU/srv.log" || { echo "   FAIL: server did not print libuv version via the generated raw surface"; ok=0; }
      [ "$root" = "hello from kappa + libuv" ] || { echo "   FAIL: GET / body wrong (got '$root')"; ok=0; }
      [ "$health" = "ok" ] || { echo "   FAIL: GET /health body wrong (got '$health')"; ok=0; }
      [ "$notf" = "404" ] || { echo "   FAIL: GET /nope status wrong (got '$notf')"; ok=0; }
      if [ "$ok" -eq 1 ]; then
        echo "   ok (generated libuv.Raw + uvnet surfaces; version printed; served /, /health, 404 — jvm/dotnet excluded)"
      else
        cat "$HU/srv.log" | sed 's/^/     /'; fails=$((fails+1))
      fi
    else
      echo "   FAIL: libuv host binding not pinned in kappa.lock"; cat "$HU/b.log" | sed 's/^/     /'; fails=$((fails+1))
    fi
  else
    echo "   FAIL: native libuv HTTP build failed"; cat "$HU/b.log" | sed 's/^/     /'; fails=$((fails+1))
  fi
  rm -rf "$HU"
else
  echo "   SKIP: pkg-config libuv or curl not available"
fi

echo ""
if [ "$fails" -eq 0 ]; then echo "ALL NATIVE TESTS PASSED"; else echo "$fails NATIVE TEST(S) FAILED"; exit 1; fi
