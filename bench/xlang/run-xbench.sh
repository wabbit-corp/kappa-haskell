#!/usr/bin/env bash
# Cross-language benchmark runner (auto-discovering).
#
# Globs every bench/xlang/<name>/ directory, and for each one:
#   1. builds the Kappa port (kappa.kp) with the PREBUILT kappa binary, on the
#      C backend AND the LLVM backend (KAPPA_BACKEND=llvm);
#   2. builds each reference impl listed in `meta` (go / hs / c);
#   3. RUNS each binary, capturing stdout;
#   4. VERIFIES stdout == expected.txt  (a CORRECTNESS GATE — a benchmark whose
#      output is wrong is reported FAIL and NOT timed);
#   5. TIMES each correct binary over several repeated runs (best + median
#      wall-clock, no hyperfine dependency);
#   6. emits a comparison TABLE: benchmark | kappa-c | kappa-llvm | go | hs | c
#      with a ratio-vs-fastest column.
#
# Auto-discovery is REQUIRED: port agents drop a new bench/xlang/<name>/ dir and
# it is picked up with no shared-registry edit (no merge point).
#
# Usage:
#   bench/xlang/run-xbench.sh                  # every discovered benchmark
#   bench/xlang/run-xbench.sh sumloop nbody    # only the named ones
#
# Env:
#   KAPPA     override the compiler binary (default: `cabal list-bin exe:kappa`)
#   REPS      timed repetitions per binary (default 5)
#   KEEP      set to 1 to keep the build/work dir for inspection
#
# Portable to macOS' stock bash 3.2 (no associative arrays / no `mapfile`):
# per-column results are stashed in files under the work dir, not in arrays.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
XDIR="$ROOT/bench/xlang"

# ── Prebuilt kappa binary (NEVER `cabal run` — avoids rebuild contention) ──────
if [ -z "${KAPPA:-}" ]; then
  KAPPA="$(cd "$ROOT" && cabal list-bin exe:kappa 2>/dev/null)"
fi
if [ -z "${KAPPA:-}" ] || [ ! -x "$KAPPA" ]; then
  echo "FATAL: kappa binary not found. Build it (cabal build exe:kappa) or set \$KAPPA." >&2
  exit 2
fi

REPS="${REPS:-5}"
WORK="${TMPDIR:-/tmp}/kappa-xbench.$$"
mkdir -p "$WORK"
if [ "${KEEP:-0}" != "1" ]; then trap 'rm -rf "$WORK"' EXIT; fi

# Columns we report, in order.
COLS="kappa-c kappa-llvm go hs c"

# ── portable nanosecond clock (python3 is always present on macOS/Linux CI) ────
now_ns() { python3 -c 'import time;print(time.perf_counter_ns())'; }

# meta is `key = value` lines (whitespace around `=` ignored); pull one value.
meta_get() { # <metafile> <key>
  sed -n -E "s/^[[:space:]]*$2[[:space:]]*=[[:space:]]*(.*[^[:space:]])[[:space:]]*\$/\1/p" "$1" | head -1
}

# Time a command over $REPS runs (it must already be verified correct).
# Echoes "best_ms median_ms".
time_cmd() {
  local i t0 t1
  local tmp="$WORK/.times.$$"
  : >"$tmp"
  for ((i=0; i<REPS; i++)); do
    t0=$(now_ns); "$@" >/dev/null 2>&1; t1=$(now_ns)
    echo $(( (t1 - t0) / 1000000 )) >>"$tmp"
  done
  local sorted; sorted=$(sort -n "$tmp")
  local n; n=$(wc -l <"$tmp" | tr -d ' ')
  local best; best=$(echo "$sorted" | head -1)
  local mid=$(( n / 2 ))
  local median; median=$(echo "$sorted" | sed -n "$((mid+1))p")
  rm -f "$tmp"
  echo "$best $median"
}

BENCHES=""
if [ "$#" -gt 0 ]; then
  BENCHES="$*"
else
  for d in "$XDIR"/*/; do
    [ -f "$d/meta" ] && BENCHES="$BENCHES $(basename "$d")"
  done
fi

if [ -z "$(echo "$BENCHES" | tr -d ' ')" ]; then
  echo "No benchmarks found under $XDIR (need a meta file per dir)." >&2
  exit 1
fi

echo "== kappa xlang benchmarks =="
echo "kappa : $KAPPA"
echo "reps  : $REPS"
echo

overall_fail=0
RESULTS="$WORK/results"; mkdir -p "$RESULTS"

# record a column outcome:  <bench> <col> <status> [best] [median]
record() { echo "$3 ${4:-} ${5:-}" >"$RESULTS/$1.$2"; }
status_of() { local f="$RESULTS/$1.$2"; [ -f "$f" ] && awk '{print $1}' "$f" || echo "n/a"; }
median_of() { awk '{print $3}' "$RESULTS/$1.$2" 2>/dev/null; }

for bench in $BENCHES; do
  bdir="$XDIR/$bench"
  meta="$bdir/meta"
  if [ ! -f "$meta" ]; then echo "[$bench] SKIP — no meta"; continue; fi

  N="$(meta_get "$meta" N)"
  refs="$(meta_get "$meta" refs)"
  desc="$(meta_get "$meta" desc)"
  exp="$bdir/expected.txt"
  echo "── $bench  (N=$N) — $desc"

  for c in $COLS; do record "$bench" "$c" "n/a"; done

  if [ ! -f "$exp" ]; then
    echo "   FAIL — no expected.txt"; overall_fail=1; echo; continue
  fi

  bwork="$WORK/$bench"; mkdir -p "$bwork"

  # build (already done by caller), then verify + time one column.
  # args: col, binary-path
  verify_and_time() {
    local col="$1" binpath="$2"
    local outf="$bwork/$col.out"
    "$binpath" >"$outf" 2>/dev/null
    if ! diff -q "$exp" "$outf" >/dev/null 2>&1; then
      record "$bench" "$col" "FAIL"; overall_fail=1
      echo "   [$col] FAIL — output mismatch (got: $(tr '\n' ' ' <"$outf" | head -c 60))"
      return
    fi
    local bm; bm=$(time_cmd "$binpath")
    local best="${bm% *}" median="${bm#* }"
    record "$bench" "$col" "ok" "$best" "$median"
    echo "   [$col] ok — best ${best}ms median ${median}ms"
  }

  # ---- Kappa C backend ------------------------------------------------------
  # `kappa build` emits its .kappa.c / .kappa.ll intermediates NEXT TO THE
  # SOURCE (not at -o), so build a COPY in the work dir to keep the tree clean.
  kp="$bdir/kappa.kp"
  if [ -f "$kp" ]; then
    kp="$bwork/kappa.kp"; cp "$bdir/kappa.kp" "$kp"
    cbin="$bwork/kappa_c"
    if "$KAPPA" build "$kp" -o "$cbin" >"$bwork/kc.buildlog" 2>&1; then
      verify_and_time kappa-c "$cbin"
    else
      record "$bench" kappa-c builderr; overall_fail=1
      echo "   [kappa-c] BUILD ERROR ($(tail -1 "$bwork/kc.buildlog"))"
    fi

    lbin="$bwork/kappa_llvm"
    if KAPPA_BACKEND=llvm "$KAPPA" build "$kp" -o "$lbin" >"$bwork/kl.buildlog" 2>&1; then
      verify_and_time kappa-llvm "$lbin"
    else
      record "$bench" kappa-llvm builderr; overall_fail=1
      echo "   [kappa-llvm] BUILD ERROR ($(tail -1 "$bwork/kl.buildlog"))"
    fi
  else
    echo "   [kappa] no kappa.kp"
  fi

  # ---- reference languages --------------------------------------------------
  for r in $refs; do
    case "$r" in
      go)
        src="$bdir/ref/go.go"
        [ -f "$src" ] || { echo "   [go] no ref/go.go"; continue; }
        command -v go >/dev/null 2>&1 || { echo "   [go] SKIP — no toolchain"; continue; }
        gobin="$bwork/ref_go"
        if go build -o "$gobin" "$src" >"$bwork/go.buildlog" 2>&1; then
          verify_and_time go "$gobin"
        else
          record "$bench" go builderr; overall_fail=1
          echo "   [go] BUILD ERROR ($(tail -1 "$bwork/go.buildlog"))"
        fi ;;
      hs)
        src="$bdir/ref/hs.hs"
        [ -f "$src" ] || { echo "   [hs] no ref/hs.hs"; continue; }
        command -v ghc >/dev/null 2>&1 || { echo "   [hs] SKIP — no toolchain"; continue; }
        hsbin="$bwork/ref_hs"
        if ghc -O2 -outputdir "$bwork/hsobj" -o "$hsbin" "$src" >"$bwork/hs.buildlog" 2>&1; then
          verify_and_time hs "$hsbin"
        else
          record "$bench" hs builderr; overall_fail=1
          echo "   [hs] BUILD ERROR ($(tail -1 "$bwork/hs.buildlog"))"
        fi ;;
      c)
        src="$bdir/ref/c.c"
        [ -f "$src" ] || { echo "   [c] no ref/c.c"; continue; }
        CC="${CC:-cc}"
        command -v "$CC" >/dev/null 2>&1 || { echo "   [c] SKIP — no toolchain"; continue; }
        cbin2="$bwork/ref_c"
        # try with -lgmp (pidigits etc.), fall back to plain link
        if "$CC" -O2 -o "$cbin2" "$src" -lgmp >"$bwork/c.buildlog" 2>&1 \
           || "$CC" -O2 -o "$cbin2" "$src" >"$bwork/c.buildlog" 2>&1; then
          verify_and_time c "$cbin2"
        else
          record "$bench" c builderr; overall_fail=1
          echo "   [c] BUILD ERROR ($(tail -1 "$bwork/c.buildlog"))"
        fi ;;
      *) echo "   [$r] unknown ref language in meta" ;;
    esac
  done
  echo
done

# ── Comparison table (median ms; ratio = median / fastest-median in the row) ──
echo "== comparison table (median wall-clock ms; ratio vs fastest in row) =="
hdr=$(printf '%-14s' "benchmark")
for c in $COLS; do hdr="$hdr$(printf ' | %-13s' "$c")"; done
hdr="$hdr | fastest"
echo "$hdr"
echo "$hdr" | sed 's/./-/g'

for bench in $BENCHES; do
  # fastest median among ok columns
  fastest=""; fastest_col=""
  for c in $COLS; do
    if [ "$(status_of "$bench" "$c")" = "ok" ]; then
      m="$(median_of "$bench" "$c")"
      if [ -z "$fastest" ] || [ "$m" -lt "$fastest" ]; then fastest="$m"; fastest_col="$c"; fi
    fi
  done

  row=$(printf '%-14s' "$bench")
  for c in $COLS; do
    st="$(status_of "$bench" "$c")"
    case "$st" in
      ok)
        m="$(median_of "$bench" "$c")"
        if [ -n "$fastest" ] && [ "$fastest" -gt 0 ]; then
          ratio=$(python3 -c "print(f'{$m/$fastest:.2f}x')")
        elif [ -n "$fastest" ]; then
          ratio="1.00x"
        else
          ratio="-"
        fi
        cell="${m}ms ${ratio}" ;;
      FAIL)     cell="FAIL" ;;
      builderr) cell="builderr" ;;
      *)        cell="-" ;;
    esac
    row="$row$(printf ' | %-13s' "$cell")"
  done
  row="$row$(printf ' | %s' "${fastest_col:-none}")"
  echo "$row"
done

echo
if [ "$overall_fail" -ne 0 ]; then
  echo "RESULT: at least one benchmark/column FAILED the correctness gate or failed to build."
  exit 1
fi
echo "RESULT: all discovered benchmarks passed the correctness gate."
