# Performance

Measurements of the interpreter pipeline on this machine (Linux x86-64,
GHC 9.4.7, `-O` defaults from the cabal file, binary invoked directly
via `cabal list-bin kappa`, `/usr/bin/time`, best/typical of 3 runs).
Re-measured after the macro/effects/projections/unicode feature phase
(the implementation roughly doubled to ~23.7k lines; constants grew
accordingly and one quadratic was found and fixed — see §2 and "Known
costs"). Reproduce with the commands shown.

## Workloads and results

### 1. `kappa check` on a small file (prelude bootstrap floor)

```
printf 'x : Integer\nlet x = addInt 1 2\n' > /tmp/small.kp
/usr/bin/time -f "%es %MKB" $(cabal list-bin kappa) check /tmp/small.kp
```

| metric | value |
| --- | --- |
| wall time | **0.08–0.09 s** |
| max RSS | ~26 MB |

This is the per-invocation floor: process startup plus the full prelude
bootstrap — the embedded `std.prelude` source *and* the embedded std
modules (`std.hash`, `std.unicode`, `std.atomic`, `std.gradual`,
`std.bridge`, `std.supervisor`, `std.ffi`, `std.deriving.shape`, …) are
parsed, resolved, and elaborated by the ordinary pipeline on every run
(see "Known costs"). The floor roughly doubled against the previous
round (0.03–0.04 s / ~15 MB) because the embedded surface roughly
doubled; it is still bootstrap-dominated, not workload-dominated.

### 2. Generated declaration files, parse + check

```
tools/gen-stress.sh 1000 /tmp/stress.kp     # 2000 declarations
/usr/bin/time -f "%es %MKB" $(cabal list-bin kappa) check /tmp/stress.kp
```

`tools/gen-stress.sh N OUT` emits `N` signature+definition pairs
(`2N` declarations); every tenth definition references the previous one.

| file | wall time | max RSS |
| --- | --- | --- |
| 2,000 decls (1,000 pairs) | **0.19 s** | ~32 MB |
| 10,000 decls (5,000 pairs) | 0.70 s | ~70 MB |

Subtracting the ~0.09 s floor, checking throughput is roughly
**16k–18k simple declarations/s**, scaling near-linearly in both time
and memory over this range (slower constants than the previous round's
25k–30k/s: every definition now also runs the §12.2 usage analysis and
the larger goal/zonk machinery).

**Fixed quadratic.** This re-measurement round found `checkModule`
quadratic in the declaration count (~4x time per size doubling above
16k declarations; 64k declarations took 24.6 s): `siglessLets` and
`sigNames` were lists, so every `let` scanned all signature names and
every signature scanned the sig-less-let list. Both are `Set`s now and
the curve is linear again (the numbers below). The in-tree suites and
the external corpus were re-run after the fix: identical outcomes,
fixture for fixture.

### 2a. Literal-heavy files (lexer scaling by literal family)

```
tools/gen-stress.sh 32000 /tmp/stress-float.kp float   # 64k float decls
tools/gen-stress.sh 32000 /tmp/stress-char.kp  char    # 64k char decls
/usr/bin/time -f "%es" $(cabal list-bin kappa) check /tmp/stress-float.kp
```

`gen-stress.sh` takes a third KIND argument (`int`/`float`/`char`)
because float and quoted-literal scanning use multi-character lexer
lookahead (an earlier `peekAt` made those files quadratic; lookahead is
`T.uncons . T.drop n` with n ≤ 2 since). Best of 3, `kappa check`:

| decls | int | float | char |
| --- | --- | --- | --- |
| 16,000 | 0.84 s (88 MB) | 0.63 s (68 MB) | 0.72 s (74 MB) |
| 32,000 | 1.84 s (160 MB) | 1.28 s (119 MB) | 1.18 s (127 MB) |
| 64,000 | 3.71 s (269 MB) | 2.53 s (201 MB) | 2.36 s (259 MB) |

Per-doubling factor is ~1.9–2.2x for every literal family, and
float/char files are no slower than int files of the same shape — the
literal-kind asymmetry remains gone. Memory is linear at roughly
4 KB/declaration.

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
| wall time | **2.1–2.2 s** (prints `4999950000`) |
| max RSS | ~27 MB |

That is ~50k loop iterations/s. Each iteration performs, through the
tree-walking interpreter and the §18.8 completion kernel: two `var`
reads (each elaborated to a `__runIO (readRef …)` splice per §18.6.1),
two `writeRef`s, two primitive arithmetic calls, and one comparison —
all as interpreted core terms, with a completion record allocated per
do-item. This is the expected cost profile for an AST interpreter; no
attempt is made at bytecode or closure compilation.

### 4. Macro-expansion stress (§21 quote/splice pipeline)

N top-level `$( … )` splice sites, each calling an `Elab` macro that
grafts a two-hole quote (`mkAdd a b = pure '{ addInt ${a} ${b} }`),
so every site runs the §21.9 Elab interpreter, §21.4 hygiene/grafting,
splice re-elaboration, and the usage-analysis expansion accounting:

```
tools/gen-macro-stress.sh 1200 /tmp/macro-stress.kp
/usr/bin/time -f "%es %MKB" $(cabal list-bin kappa) check /tmp/macro-stress.kp
```

| splice sites | wall time | max RSS |
| --- | --- | --- |
| 300 | 0.14 s | 28 MB |
| 600 | 0.21 s | 33 MB |
| 1,200 | 0.34 s | 41 MB |

Linear: ~0.22 ms per macro expansion net of the floor (~4.5k
expansions/s), ~11 KB per expansion.

### 5. Comprehension-pipeline stress (§20 query lowering)

N comprehensions, each running the full clause pipeline over a
10-element list — `for`/`let`/`if`/`order by`/`distinct`/`take`/`yield`
— so every site elaborates the §20.10.11 as-if lowering with its
orderedness/plan checks and the associated trait goals:

```
tools/gen-comp-stress.sh 800 /tmp/comp-stress.kp
/usr/bin/time -f "%es %MKB" $(cabal list-bin kappa) check /tmp/comp-stress.kp
```

| comprehensions | wall time | max RSS |
| --- | --- | --- |
| 200 | 2.84 s | 46 MB |
| 400 | 5.65 s | 62 MB |
| 800 | 11.41 s | 88 MB |

Linear: ~14 ms and ~55 KB per full-pipeline comprehension. The
per-site constant is the heaviest of any construct measured here (a
seven-clause pipeline lowers to a chain of carrier combinators, each
elaborated and instance-resolved); files mixing a few comprehensions
into ordinary code are unaffected.

## Known costs and bounds

* **Prelude recompilation per invocation.** `std.prelude` (builtins +
  embedded source: data types, traits, instances, list functions) plus
  the embedded std modules are compiled from scratch on every
  `check`/`run`/`test` process — there is no serialized artifact cache.
  This is the bulk of the 0.09 s small-file floor. Within one
  `kappa test` process the bootstrapped state is shared across fixtures
  (the `preludeState` CAF in `Kappa.Pipeline`), so the cost per
  additional fixture is small.
* **Fuel-bounded conversion.** Definitional-equality checks in
  `Kappa.Eval` run under a fuel budget so pathological or
  non-terminating unfoldings cannot hang the checker. Soundness
  direction: exhausting fuel only ever yields "not convertible" — the
  checker may then reject a convertible program (incompleteness), but
  it never accepts an inequality. Additionally, only
  conversion-reducible (§15.1) definitions δ-unfold at all, so
  unverified recursion cannot be forced during checking. Macro/Elab
  execution shares the same fuel discipline (§21.8 delta documented in
  IMPLEMENTATION_NOTES.md).
* **External-fixture driver timeout.** `tools/run-external-fixtures.sh`
  applies a per-fixture timeout so a single pathological fixture cannot
  stall the corpus run.
* **Memory flags.** The executable is built with
  `-rtsopts "-with-rtsopts=-K64m"`: a 64 MB GHC stack limit (deep
  recursion in the elaborator/interpreter fails predictably instead of
  overflowing), and no heap cap (GHC default unbounded heap). Observed
  RSS stays under ~90 MB for every workload above except the synthetic
  32k+-declaration files (linear at ~4 KB/decl, ~270 MB at 64k).

## Non-goals

No benchmarking of backends, codegen, or incremental checking — none
exist (SPEC_COVERAGE.md Parts VI/IX). Numbers here are for honesty
about interpreter-grade performance, not competitive claims.
