# Performance

Measurements of the interpreter pipeline on this machine (Linux x86-64,
GHC 9.4.7, `-O` defaults from the cabal file, binary invoked directly
via `cabal list-bin kappa`, `/usr/bin/time`, best/typical of 3 runs).
Reproduce with the commands shown.

## Workloads and results

### 1. `kappa check` on a small file (prelude bootstrap floor)

```
printf 'x : Integer\nlet x = addInt 1 2\n' > /tmp/small.kp
/usr/bin/time -f "%es %MKB" $(cabal list-bin kappa) check /tmp/small.kp
```

| metric | value |
| --- | --- |
| wall time | **0.03–0.04 s** |
| max RSS | ~15 MB |

This is the per-invocation floor: it includes process startup plus the
full prelude bootstrap — the embedded `std.prelude` source is parsed,
resolved, and elaborated by the ordinary pipeline on every run (see
"Known costs" below).

### 2. Generated 2000-declaration file, parse + check

```
tools/gen-stress.sh 1000 /tmp/stress.kp     # 2000 declarations
/usr/bin/time -f "%es %MKB" $(cabal list-bin kappa) check /tmp/stress.kp
```

`tools/gen-stress.sh N OUT` emits `N` signature+definition pairs
(`2N` declarations); every tenth definition references the previous one.

| file | wall time | max RSS |
| --- | --- | --- |
| 2,000 decls (1,000 pairs) | **0.07–0.11 s** | ~21 MB |
| 10,000 decls (5,000 pairs) | 0.35 s | ~46 MB |

Subtracting the ~0.03 s floor, checking throughput is roughly
**25k–30k simple declarations/s**, scaling near-linearly in both time
and memory over this range.

### 3. Runtime loop: summing 0..99,999

```
cat > /tmp/sum100k.kp <<'EOF'
main : UIO Unit
let main = do
    var i = 0
    var total = 0
    while ltInt i 100000 do
        total = addInt total i
        i = addInt i 1
    printlnString (showInt total)
EOF
/usr/bin/time -f "%es %MKB" $(cabal list-bin kappa) run /tmp/sum100k.kp
```

| metric | value |
| --- | --- |
| wall time | **1.6–1.7 s** (prints `4999950000`) |
| max RSS | ~16 MB |

That is ~60k loop iterations/s. Each iteration performs, through the
tree-walking interpreter and the §18.8 completion kernel: two `var`
reads (each elaborated to a `__runIO (readRef …)` splice per §18.6.1),
two `writeRef`s, two primitive arithmetic calls, and one comparison —
all as interpreted core terms, with a completion record allocated per
do-item. This is the expected cost profile for an AST interpreter; no
attempt is made at bytecode or closure compilation.

## Known costs and bounds

* **Prelude recompilation per invocation.** `std.prelude` (builtins +
  ~250 lines of embedded source: data types, traits, instances, list
  functions) is compiled from scratch on every `check`/`run`/`test`
  process — there is no serialized artifact cache. It is the bulk of
  the 0.03 s small-file floor. `kappa test` on a directory amortizes
  it poorly too: the prelude state is rebuilt per fixture compilation
  (Haskell laziness shares the parsed prelude within a process via the
  `preludeState` CAF in `Kappa.Pipeline`, so the cost per additional
  fixture in one `kappa test` run is small in practice).
* **Fuel-bounded conversion.** Definitional-equality checks in
  `Kappa.Eval` run under a fuel budget so pathological or
  non-terminating unfoldings cannot hang the checker. Soundness
  direction: exhausting fuel only ever yields "not convertible" — the
  checker may then reject a convertible program (incompleteness), but
  it never accepts an inequality. Additionally, only
  conversion-reducible (§15.1) definitions δ-unfold at all, so
  unverified recursion cannot be forced during checking.
* **External-fixture driver timeout.** `tools/run-external-fixtures.sh`
  applies a per-fixture timeout so a single pathological fixture cannot
  stall the corpus run.
* **Memory flags.** The executable is built with
  `-rtsopts "-with-rtsopts=-K64m"`: a 64 MB GHC stack limit (deep
  recursion in the elaborator/interpreter fails predictably instead of
  overflowing), and no heap cap (GHC default unbounded heap). Observed
  RSS stays under ~50 MB for all workloads above.

## Non-goals

No benchmarking of backends, codegen, or incremental checking — none
exist (SPEC_COVERAGE.md Parts VI/IX). Numbers here are for honesty
about interpreter-grade performance, not competitive claims.
