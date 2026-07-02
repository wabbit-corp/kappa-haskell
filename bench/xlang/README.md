# Cross-language benchmark harness (`bench/xlang`)

The external apples-to-apples layer described in
[`docs/CROSS-LANGUAGE-BENCHMARKING.md`](../../docs/CROSS-LANGUAGE-BENCHMARKING.md).
Each benchmark ports a single program to Kappa and pits it against reference
impls (Go / GHC / C) on the same machine, with a **correctness gate** (stdout
must match `expected.txt`) before anything is timed.

## Run

```sh
make xbench                  # all discovered benchmarks
make xbench BENCH=sumloop    # only the named ones
make xbench REPS=11          # more timing repetitions
# or directly:
bash run-xbench.sh [name ...]
```

The runner is **auto-discovering**: it globs `bench/xlang/*/` (every dir with a
`meta` file). There is **no registry to edit** — drop a new benchmark dir and it
is picked up. Port agents never touch a shared file, so there are no merge
points.

## Adding a benchmark — exact convention

Create `bench/xlang/<name>/` with EXACTLY these files:

```
bench/xlang/<name>/
  meta            # key = value lines (see below)
  kappa.kp        # the Kappa port (module main, prints the result line)
  expected.txt    # the exact correct stdout for the hardcoded N
  ref/go.go       # Go reference     (package main)
  ref/hs.hs       # GHC reference    (module Main)
  ref/c.c         # C reference      (int main)
```

Only the ref files named in `meta`'s `refs` line are required; omit a language
by leaving it out of `refs` and not creating its file.

### `meta` format

```
name = <name>           # must equal the directory name
tier = <0|1|1.5|2|3>    # CROSS-LANGUAGE-BENCHMARKING tier (0 = sanity)
N    = <integer>        # the HARDCODED size parameter (no getArgs/stdin yet)
refs = go hs c          # space-separated subset of {go, hs, c}
desc = <one-line description>
```

### Rules

- **Hardcode N** in every impl (Kappa, Go, GHC, C) — `getArgs`/stdin do not
  exist yet. Use the SAME N everywhere and record it in `meta`. Put the value
  in a comment so it is greppable.
- **`expected.txt`** is the literal stdout (trailing newline included). Generate
  it by running any one correct impl: `./ref_c > expected.txt`.
- All impls must print **the same stdout** — that is what the gate checks. Keep
  output minimal (one result line) so the benchmark measures compute, not I/O.
- `kappa.kp` must be `module main` with `main : UIO Unit`; print with
  `printlnString (showInt x)` / `println (x : Double)` (see existing `.kp`
  examples under `tests/native/llvm/`).
- Be **honest**: if a port hits a real compiler/language gap (no arrays, missing
  prim, precision), say so in `desc` and the agent's report, and write what you
  can rather than fabricating output.

## Exact build/run commands (what the runner does per impl)

`$KAPPA` is the **prebuilt** binary: `cabal list-bin exe:kappa` (NEVER
`cabal run` — that triggers rebuild contention). The runner copies `kappa.kp`
into a temp work dir before building, because `kappa build` emits its
`.kappa.c` / `.kappa.ll` intermediates next to the *source*, not at `-o`.

| impl       | build                                                | run        |
|------------|------------------------------------------------------|------------|
| kappa-c    | `$KAPPA build kappa.kp -o BIN`                       | `BIN`      |
| kappa-llvm | `KAPPA_BACKEND=llvm $KAPPA build kappa.kp -o BIN`    | `BIN`      |
| go         | `go build -o BIN ref/go.go`                          | `BIN`      |
| hs         | `ghc -O2 -outputdir OBJDIR -o BIN ref/hs.hs`         | `BIN`      |
| c          | `cc -O2 -o BIN ref/c.c -lgmp` (falls back w/o -lgmp) | `BIN`      |

## Output

For each impl: build → run → `diff expected.txt` (FAIL here = reported, **not
timed**) → time over `REPS` runs (default 5), reporting best + median
wall-clock (a python `perf_counter_ns` repeated-run timer; no hyperfine
dependency). Then a table:

```
benchmark | kappa-c | kappa-llvm | go | hs | c | fastest
```

each cell `<median>ms <ratio>x` (ratio = median / fastest-in-row), or `FAIL`
(wrong output) / `builderr` / `-` (n/a). Exit code is non-zero if any column
failed the correctness gate or failed to build — so it doubles as a CI gate.

## Methodology notes

- `ns/op`/`ms` carry ~10–15% hardware/thermal variance — same-machine reference,
  not absolute (mirror the `runtime/bench` convention).
- The Kappa LLVM backend has had both boxed-parity and scalar-worker phases; use
  each row's recorded backend/version context before drawing a performance
  conclusion. A boxed fallback result is a **boxing lever** for the
  unboxing/Perceus/layout tracks, not the target capability.
