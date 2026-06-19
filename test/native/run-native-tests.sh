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
for c in arith data control strings loops records unicode traits variants-susp bignum dokernel showprims bytes ubuilders unidata uhash iorec defernest deferlazy prefixbind letqor letqelse letqmiss projection lr1 varloop recordproj tupleproj ctortags adtcons scalarkinds flatframe flatbinders flatclosure; do run_diff_case "$c"; done

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
if timeout 120 $KAPPA build "$CASES/adtcons.kp" --emit-c -o "$rtmp/ac" >"$rtmp/build.log" 2>&1; then
  cfile="$CASES/adtcons.kappa.c"
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

# R2.1 / P1-F: the pointer-free scalar boxes (K_INT/K_DBL/K_CHR/K_BYTE) must be
# allocated on the atomic (unscanned) GC heap via alloc_val_atomic, not the
# scanned alloc_val — this removes them as conservative-GC false-pointer sources
# and cuts mark work.  A revert to alloc_val would silently regress GC cost; the
# equivalence suite already proves the non-zeroing atomic alloc is correct, so
# this is a source invariant on the four scalar constructors in the runtime.
echo "== R2.1: pointer-free scalar boxes use the atomic (unscanned) GC heap =="
rt="$ROOT/runtime/kappart.c"
# The scalar tags K_INT/K_DBL/K_CHR/K_BYTE are constructed only in kint/kdbl/
# kchr/kbyte, so keying on the tag argument is an unambiguous, format-robust
# invariant: each must allocate via alloc_val_atomic and none via the scanned
# alloc_val.
r21_ok=1
for tag in K_INT K_DBL K_CHR K_BYTE; do
  grep -qE "alloc_val_atomic\($tag\)" "$rt" || r21_ok=0
  # negative: the scanned alloc_val(TAG) must not appear; (^|[^_]) anchors so a
  # line-start occurrence is still caught and alloc_val_atomic is not matched.
  grep -qE "(^|[^_])alloc_val\($tag\)" "$rt" && r21_ok=0
done
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
if timeout 120 $KAPPA build "$dbench" --emit-c -o "$dtmp/sd" >"$dtmp/build.log" 2>&1; then
  cfile="$ROOT/test/native/bench/proposed/scalar_doubleloop.kappa.c"
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
if timeout 120 $KAPPA build "$CASES/adtcons.kp" --emit-c -o "$btmp/ac" >"$btmp/ac.log" 2>&1; then
  grep -qE 'ktrampoline\(' "$CASES/adtcons.kappa.c" && nb_ok=0   # must be NONE
  rm -f "$CASES/adtcons.kappa.c"
else nb_ok=0; fi
b_ok=0
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
if timeout 120 $KAPPA build "$CASES/flatframe.kp" --emit-c -o "$ftmp/ff" >"$ftmp/build.log" 2>&1; then
  cfile="$CASES/flatframe.kappa.c"
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
if timeout 120 $KAPPA build "$CASES/flatbinders.kp" --emit-c -o "$btmp/fb" >"$btmp/build.log" 2>&1; then
  cfile="$CASES/flatbinders.kappa.c"
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
if timeout 120 $KAPPA build "$CASES/flatclosure.kp" --emit-c -o "$ctmp/fc" >"$ctmp/build.log" 2>&1; then
  cfile="$CASES/flatclosure.kappa.c"
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
if timeout 120 $KAPPA build "$CASES/hidden-symbol.kp" -o "$exe" >"$WORK/hidden.log" 2>&1; then
  echo "   FAIL: a program calling __tcpListen built (hidden symbol leaked)"; fails=$((fails+1))
elif grep -q "E_NAME_UNRESOLVED" "$WORK/hidden.log" && [ ! -f "$exe" ]; then
  echo "   ok (__tcpListen is E_NAME_UNRESOLVED, no executable; FFI prims are not prelude globals)"
else
  echo "   FAIL: __tcpListen not rejected as unresolved / left an executable"
  cat "$WORK/hidden.log" | sed 's/^/     /'; fails=$((fails+1))
fi

echo "== a bare foreign 'expect' is unsatisfied without a host binding (no silent FFI) =="
# §9.4: a bare `expect term` has no provider — native bindings come only
# through the manifest's host.native modules, never a bare-name table or
# --ffi-full. So the legacy single-file build leaves it unsatisfied.
exe="$WORK/unsupported"
if timeout 120 $KAPPA build "$CASES/unsupported.kp" -o "$exe" >"$WORK/unsupported.log" 2>&1; then
  echo "   FAIL: a bare foreign-expect program built (FFI fabricated)"; fails=$((fails+1))
elif grep -q "E_EXPECT_UNSATISFIED" "$WORK/unsupported.log" && [ ! -f "$exe" ]; then
  echo "   ok (unsatisfied foreign expect -> E_EXPECT_UNSATISFIED, no executable, §9.4)"
else
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
# provider's members to their runtime FFI prims.
if timeout 120 $KAPPA build --update --manifest "$ROOT/tests/build/native/ok-sqlite" --emit-c -o "$WORK/oksql" >"$WORK/oksql.log" 2>&1 \
   && find "$ROOT/tests/build/native/ok-sqlite" -name '*.kappa.c' -exec grep -ql "__sqliteOpen" {} \; ; then
  echo "   ok (manifest nativeBinding -> host.native.sqlite3 import -> __sqliteOpen prim)"
  find "$ROOT/tests/build/native/ok-sqlite" -name '*.kappa.c' -delete 2>/dev/null
else
  echo "   FAIL: manifest-driven native build did not emit the provider prim"
  cat "$WORK/oksql.log" | sed 's/^/     /'; fails=$((fails+1))
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

# R0.1: enforce the now-fair landed-wave allocation gates from the proposed
# bench suite (median-of-N timing, per-iteration allocation): adtbuild's
# direct-ctor alloc/iter bound (R1.1) and scalar_doubleloop's unboxed-double
# alloc bound (R2.2), alongside the scalar_intloop unboxed-Int bound (LR1/P0.2).
# These convert three measured wins into deterministic regression gates.
echo "== R0.1: landed-wave allocation gates (proposed bench --gate) =="
if timeout 400 bash "$ROOT/test/native/bench/proposed/run-proposed.sh" --gate --reps 3 scalar_intloop adtbuild scalar_doubleloop >"$WORK/proposed.log" 2>&1; then
  echo "   ok (adtbuild ≤300B/iter [R1.1], scalar_doubleloop ≤100KB [R2.2], scalar_intloop ≤100KB [LR1/P0.2])"
  grep -E '^   ok (adtbuild|scalar_doubleloop|scalar_intloop)' "$WORK/proposed.log" | sed 's/^/  /'
else
  echo "   FAIL: a landed-wave allocation gate regressed"; grep -iE 'FAIL' "$WORK/proposed.log" | sed 's/^/     /'; fails=$((fails+1))
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

echo "== native ABI discovery + verification against the real headers (§26.1.5/§36.28) =="
if pkg-config --exists sqlite3 2>/dev/null; then
  # (a) a real build records verified-against-sqlite3.h provenance
  rm -f "$ROOT/examples/native/http_sqlite/server.native.prov"
  if timeout 200 $KAPPA build --update --manifest "$ROOT/examples/native/http_sqlite" --emit-c -o "$WORK/abi" >"$WORK/abi.log" 2>&1 \
     && grep -q "verified-decl int sqlite3_open" "$ROOT/examples/native/http_sqlite/server.native.prov" \
     && grep -q "pkg-config sqlite3 version=" "$ROOT/examples/native/http_sqlite/server.native.prov" \
     && grep -q "header sqlite3.h digest=" "$ROOT/examples/native/http_sqlite/server.native.prov"; then
    echo "   ok (pkg-config version + .pc digest + sqlite3.h digest + verified real decls recorded)"
  else
    echo "   FAIL: demo build did not record verified native provenance"; cat "$WORK/abi.log" | sed 's/^/     /'; fails=$((fails+1))
  fi
  rm -f "$ROOT/examples/native/http_sqlite/server.native.prov"
  # (b) a verify decl that disagrees with the real sqlite3.h fails the build (fail-closed)
  BAD="$WORK/badabi"; rm -rf "$BAD"; mkdir -p "$BAD/src"
  printf 'module app\nimport host.native.sqlite3 as db\nlet main = do\n  h <- db.sqliteOpen "x"\n  db.sqliteClose h\n' > "$BAD/src/app.kp"
  printf 'let buildConfig : BuildConfig = package { name="b", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="s", provides=[module "host.native.sqlite3"], surface=symbolList [symbolDecl "sqliteOpen" "sqlite3_open_x" [ctString] ctHandle, symbolDecl "sqliteClose" "sqlite3_close_x" [ctHandle] ctUnit], abi=cAbi, inputs=[headers ["sqlite3.h"], pkgConfig "sqlite3" None, verify ["int sqlite3_open(double)"]], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="t" }, fragments=tags [], main=module "app", modules=modulesUnder "app", dependencies=[], hostBindings=["s"] }] }' > "$BAD/kappa.build.kp"
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
printf 'module app\nimport host.native.netbyte as n\nimport std.ffi.(u32, u32Value)\nlet main = do\n  x <- n.htonl (u32 256)\n  printlnString (showInt (u32Value x))\n' > "$WD/src/app.kp"
printf 'let buildConfig : BuildConfig = package { name="w", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="nb", provides=[module "host.native.netbyte"], surface=symbolList [symbolDecl "htonl" "htonl" [ctU32] ctU32], abi=cAbi, inputs=[headers ["arpa/inet.h"], verify ["uint32_t htonl(uint32_t)"]], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="t" }, fragments=tags [], main=module "app", modules=modulesUnder "app", dependencies=[], hostBindings=["nb"] }] }' > "$WD/kappa.build.kp"
wout="$(timeout 200 $KAPPA build --update --manifest "$WD" --emit-c -o "$WORK/wbin" 2>&1)"; wrc=$?
WC="$(find "$WD" -name '*.kappa.c' | head -1)"
if [ "$wrc" -eq 0 ] && grep -q "extern uint32_t htonl(uint32_t);" "$WC" 2>/dev/null; then
  echo "   ok (ctU32 -> 'uint32_t' extern prototype, verified against arpa/inet.h)"
else
  echo "   FAIL: exact-width ctU32 did not map to uint32_t / verify"; echo "$wout" | sed 's/^/     /'; fails=$((fails+1))
fi
rm -rf "$WD"

echo "== a shim symbol whose ABI signature disagrees with the manifest is fail-closed (§27.1.1, N-19) =="
SB="$WORK/shimabi"; rm -rf "$SB"; mkdir -p "$SB/src"
printf 'module app\nimport host.native.probe as p\nlet main = do\n  x <- p.thing 7\n  printlnString "ok"\n' > "$SB/src/app.kp"
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
printf 'module app\nimport host.native.u64x as n\nimport std.ffi.(u64, u64Value)\nlet main = do\n  x <- n.u64id (u64 18446744073709551615)\n  printlnString (showInt (u64Value x))\n' > "$U6/src/app.kp"
printf '#include <stdint.h>\nuint64_t u64id(uint64_t x) { return x; }\n' > "$U6/src/shim.c"
printf 'let buildConfig : BuildConfig = package { name="u", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="ub", provides=[module "host.native.u64x"], surface=symbolList [symbolDecl "u64id" "u64id" [ctU64] ctU64], abi=cAbi, inputs=[shim ["src/shim.c"]], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "app", modules=modulesUnder "app", dependencies=[], hostBindings=["ub"] }] }' > "$U6/kappa.build.kp"
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
printf 'module app\nimport host.native.absx as n\nimport std.ffi.(i64)\nlet main = do\n  x <- n.myabs (i64 5)\n  printlnString "ok"\n' > "$AB/src/app.kp"
# binds the real libc `abs` (int abs(int)) but DECLARES it [ctI64] ctI64 — a width mismatch
printf 'let buildConfig : BuildConfig = package { name="a", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[nativeBinding { name="ab", provides=[module "host.native.absx"], surface=symbolList [symbolDecl "myabs" "abs" [ctI64] ctI64], abi=cAbi, inputs=[headers ["stdlib.h"], verify ["int abs(int)"]], link=noLink, load=systemLoader }], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="x86_64-linux-gnu" }, fragments=tags [], main=module "app", modules=modulesUnder "app", dependencies=[], hostBindings=["ab"] }] }' > "$AB/kappa.build.kp"
about="$(timeout 200 $KAPPA build --update --manifest "$AB" --emit-c -o "$WORK/abbin" 2>&1)"; abrc=$?
if [ "$abrc" -ne 0 ] && grep -q "E_BUILD_NATIVE_ABI" <<<"$about"; then
  echo "   ok (declared int64_t for the real int abs -> E_BUILD_NATIVE_ABI against stdlib.h)"
else
  echo "   FAIL: a width-mismatched direct library binding was not rejected"; echo "$about" | sed 's/^/     /'; fails=$((fails+1))
fi
rm -rf "$AB"

echo "== RawPtr results surface as Option RawPtr (nullability, §26.1.1:27307) =="
RP="$WORK/rawptr"; rm -rf "$RP"; mkdir -p "$RP/src"
printf 'module app\nimport host.native.envx as n\nlet main = do\n  r <- n.getenv "PATH"\n  match r\n  case None -> printlnString "PATH=none"\n  case Some p -> printlnString "PATH=some"\n' > "$RP/src/app.kp"
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
  if grep -q "^host-binding .* sqlite3$" "$LK/kappa.lock" 2>/dev/null && grep -q "^host-binding .* posixnet$" "$LK/kappa.lock" 2>/dev/null; then
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

echo ""
if [ "$fails" -eq 0 ]; then echo "ALL NATIVE TESTS PASSED"; else echo "$fails NATIVE TEST(S) FAILED"; exit 1; fi
