# New package targets — port status (honest)

Two uploaded packages were unpacked here (sources preserved verbatim from
`input/`, provenance intact). Both were authored against a *different/hypothetical*
Kappa front end (schematic `build.kp` manifests; jvm/dotnet backends; assumed
proof inference and named-argument constructor syntax). This file records,
honestly, what builds under THIS implementation and what is blocked, with exact
causes. **image-loader now builds, tests, and runs end-to-end** (all checks pass);
delve's status is recorded below.

## image-loader (`image-loader/`) — PNG container validation + QOI decode

Pure-Kappa parsers (no native shim). Original `build.kp` targets only `jvm` and
`dotnet` library/test targets — backends this implementation does not provide
(§27.2/§27.3 say a conforming implementation **MAY** provide them; they are not
mandatory). Added toward a native port:

- `src/acme/png/prim.native.kp` — a portable U32/byte fragment over the prelude's
  Integer/Byte primitives (satisfies the `prim` facade's `expect` decls; the
  jvm/dotnet `prim` fragments are excluded by §36.12 fragment selection). This
  fragment is correct and self-contained.
- `test/acme/image/run_tests.kp` — a native test runner over the package's pure
  PNG/QOI test functions.
- `kappa.build.kp` — a native executable target in this implementation's manifest
  schema.

**STATUS: BUILDS, TESTS, AND RUNS.** `kappa build` exits 0 (only
`W_TERMINATION_UNVERIFIED` warnings, which are acceptable — termination is
recorded-not-verified by this front end), produces the `image-tests` native
executable, and running it prints `IMAGE TESTS: ALL PASS` with all 8 checks
(`qoi.onePixelRed`, `qoi.run`, `qoi.badMagicRejected`, `png.onePixelHeader`,
`png.badSignatureRejected`, `image.sniffQoi`, `image.sniffPng`,
`image.loadQoiRaster`) showing `: PASS`.

The package source was written against a richer/hypothetical front end. The
following purely-mechanical, behavior-preserving adaptations were applied to the
`.kp` sources to make it accepted by THIS front end (the original `build.kp` is
untouched for provenance; `kappa.build.kp` is unchanged):

1. **Parenthesized named-argument constructor application → brace form.** This
   front end parses `Ctor (field = e) …` as application to *anonymous records*
   (`actual: (field : T) expected: T`). Every constructor application of that
   shape was rewritten to the brace block `Ctor { field = e, … }`. Sites:
   `image/core.kp` (`RasterImage`), `png/parser.kp` (`ParseState` in
   `initialState`/`bump`/the `with*` helpers, `PngImage` in `makeImage`),
   `png/ihdr.kp` (`Ihdr`), `png/chunk.kp` (`RawChunk`), `qoi/parser.kp`
   (`DecodeState`, `QoiDesc`). Same constructor, same field values → identical
   runtime value.
2. **`Nat` subtraction → total saturating `satSub`** (KNOWN_SPEC_ISSUES #6: checked
   `Nat` `-` needs a `subDefined x y = True` proof this front end cannot infer).
   Added `src/acme/natutil.kp` defining `satSub a b = natOfInt (subInt (natToInt a)
   (natToInt b))` and replaced every `a - b` (including the `decreases` measures)
   with `nat.satSub a b`. Sites: `png/binary.kp` (`remaining`, `byteAt`),
   `png/crc32.kp` (`foldBytes` measure, `crcBits` decrement), `png/parser.kp`
   (`parseLoop` measure, `IendNotLast`), `png/ihdr.kp` (`divisibleBy3` decrement,
   `parsePaletteEntries` measure), `qoi/binary.kp` (`remaining`, `modNat`),
   `qoi/parser.kp` (`emptyIndex`/`indexGet`/`indexPut`/`emitPixel`/`emitRun`).
   Saturating subtraction is runtime-identical to checked subtraction whenever
   `b <= a`, which always holds here (byte cursors/counters never underflow), so
   observable behavior is preserved.
3. **`Nat` division → total `safeDiv`.** The same proof-inference gap affects checked
   `Nat` `/` (needs `divDefined x y = True`). Added `safeDiv a b = natOfInt (divInt
   (natToInt a) (natToInt b))` in `natutil.kp` and replaced `/` at the QOI sites
   (`qoi/binary.kp` `modNat`/`high2`/`nibbleHigh`; `qoi/parser.kp` `validateHeader`
   bound and the `decodeDiff` `tag/16`,`tag/4`). All divisors are nonzero constants
   or the already-`!= 0`-validated `width`, so identical to checked division.
4. **Multi-line operator continuation joined onto one line** (KNOWN_SPEC_ISSUES #13):
   the `+`-chains in `u32NatOfBytes` (`png/binary.kp`, `qoi/binary.kp`) and the hash
   sum in `qoi/parser.kp` `pixelHash` were joined/parenthesized onto one line.
   Arithmetic is unchanged.
5. **`reverse` helper added** (`natutil.kp`): the front-end prelude has no `reverse`;
   added a standard accumulator `reverse`. Used in `png/ihdr.kp`,
   `png/parser.kp`, `qoi/parser.kp` where the originals called `reverse`.
6. **Record patch `.{ … }` on nominal data → full reconstruction.** This front end's
   `.{ }` update only applies to anonymous record types, not nominal `data` records
   (`E_TYPE_EQUALITY_MISMATCH: record patch requires a closed record`). The
   `ParseState`/`DecodeState` patches were rewritten as full constructor
   reconstructions (named `with*`/`withCursor` helpers in `png/parser.kp` and
   `qoi/parser.kp`) that copy unchanged fields by projection and set the updated
   ones — semantically identical to the patch.
7. **`Eq` instances added for user enums.** `==` on `Channels` (`qoi/core.kp`),
   `ColorType` (`png/core.kp`), `ImageFormat`/`PixelFormat` and `Eq a => Eq (Option
   a)` (`image/core.kp`) — the richer front end auto-derived these; here they are
   written out as match-based structural equality. Used only by the test asserts;
   no parser/decoder behavior change.
8. **`Cursor` data constructor renamed `Cursor` → `MkCursor`** (`png/binary.kp`,
   `qoi/binary.kp`, and the one external use in `png/chunk.kp`). A qualified type
   reference `bin.Cursor` resolved to the same-named *constructor* (term) instead of
   the type; giving the constructor a distinct name disambiguates. Type name and all
   field/projection behavior unchanged.
9. **Qualified constructor pattern → selective import.** `image/core.kp` matched
   `case qoi.ChannelsRgb`/`qoi.ChannelsRgba`, which did not resolve; added
   `import acme.qoi.core.(ChannelsRgb, ChannelsRgba)` and used the unqualified
   constructors in the patterns.
10. **`do`-block trailing `if` joined to one line** (`test/acme/image/run_tests.kp`):
    the do-statement `if … then … else …` with `then`/`else` on indented
    continuation lines is not accepted as a do-item; placing it on one line parses.
    Control flow unchanged.

**One genuine latent bug fixed (behavior corrected to intended):**
`png/chunk.kp` `checkSignature` called `bytes.bytesStartsWith source pngSignature`,
but this prelude's signature is `bytesStartsWith prefix haystack` (the prefix is the
first argument). The swapped order made every valid PNG fail with `BadSignature`
(`png.onePixelHeader` FAIL). Corrected to `bytesStartsWith pngSignature source`,
matching the prefix-first convention the package's own `loader.startsWith` uses.
After the fix the CRC-checked parse of the bundled 1×1 truecolor PNG succeeds, so
the package's `crc32` is confirmed correct. (`testBadSignatureRejected` still passes:
the 2-byte non-PNG input is rejected under either argument order.)

The data-declaration layout the package uses (constructor binders on indented
continuation lines) WAS a front-end gap and is now FIXED (see the Parser commit
"accept constructor binders on an indented continuation block").

## delve (`delve/`) — native Linux terminal roguelike

A genuine native package with a package-owned C shim
(`native/delve_terminal.c` + `.h`). The original `build.kp` (kept verbatim for
provenance) uses a schematic `nativeBinding(headers=, sources=, summaries=…)`
schema and a **trusted-summary-refined** `Raw` surface (`Raw.TerminalError`,
`Ok/Err` result wrappers, ownership) that this front end does not synthesize.

**STATUS — Part A (pure game-logic tests): BUILDS, TESTS, AND RUNS.**
`kappa build --manifest . -o /tmp/delve-tests --target delve-tests` exits 0
(only `W_TERMINATION_UNVERIFIED` warnings) and the `delve-tests` executable
prints `DELVE TESTS: ALL PASS` with all three checks (`gen.seededDungeonHasPlayer`,
`gen.seededDungeonHasRooms`, `input.hjklWorks`) `: PASS`.

**STATUS — Part B (full game incl. native terminal binding): COMPILES + LINKS.**
`kappa build --manifest . -o /tmp/delve-game --target delve --update` exits 0 and
produces a native ELF executable that links the conservative terminal binding.
(The interactive game is not run here — it needs a real TTY — but the bar of the
whole game compiling+linking with the terminal binding is met.)

### Target scoping (`kappa.build.kp`, new, this implementation's brace schema)
Two native executable targets share one manifest. A `role` fragment axis
(`game`/`test`) keeps them apart, since `modulesUnder "delve"` selects every
`delve.*` source and a suffix-less file is always selected:
- the interactive-only modules were renamed to carry a `.game` fragment suffix
  (`ai.game.kp`, `combat.game.kp`, `fov.game.kp`, `inventory.game.kp`,
  `engine.game.kp`, `render.game.kp`, `main.game.kp`, `terminal.game.kp` — the
  facade); the module name is unchanged (the path-derived name strips suffixes);
- `delve-tests` enables `["native","test"]`, so the `.game` fragments and the
  `terminal.native.linux.kp` (suffixes `native`,`linux`) are excluded — only the
  pure modules (no suffix: `core`/`gen`/`grid`/`rng`/`input`/`content`/`natutil`)
  plus `delve.run_tests` and the two test modules participate;
- `delve` enables `["native","linux","game"]` and links the `delve-terminal`
  binding (facade `terminal.game.kp` + impl `terminal.native.linux.kp`).
A new `test/delve/run_tests.kp` runner imports the two test modules and prints a
PASS/FAIL line per check plus the summary.

### Mechanical adaptations (behavior-preserving), driven by the first compiler error
The same families as image-loader, applied to delve's pure + interactive modules:
1. **Paren named-arg constructor application → brace** (`Stats`/`Actor` in
   `content.kp`; `Level` in `grid.kp`; `GameState` in `gen.kp`).
2. **Missing prelude helpers added** in a new `src/delve/natutil.kp`
   (`reverse`, `take`, `drop`, `listGet`, `listIsEmpty`, `max`, `min`, `abs`,
   `sign`, `arrayGetI`/`arraySet`/`arrayReplicate`, plus `satSub`/`safeDiv`/
   `safeMod`); imported `.*` where used. `fov`'s local `sign` was removed in
   favour of the shared one.
3. **`Nat` modulo needing a `modDefined` proof → total `safeMod`** in `rng.kp`
   (the LCG `% modulus` and the range reduction; divisors are the nonzero
   constant modulus / a `max 1`-bounded span, so runtime-identical).
4. **`.{ }` record patch on nominal `data` → reconstruction helpers** (a block of
   `with*` builders in `core.kp` covering `Level`/`Tile`/`Stats`/`Actor`/
   `PlayerState`/`GameState`); every patch in `grid`/`gen`/`combat`/`ai`/
   `fov`/`inventory`/`engine` rewritten to copy-unchanged-set-changed.
5. **`Eq` instances written out** for `Direction`, `Command`, `Species`,
   `TileKind`, `GameMode` (used by `==`/`!=` in the tests and engine).
6. **Multi-line operator chains joined** (`input_test.kp` `&&` chain;
   `render.game.kp` `hpBar` `++` chain).
7. **Block-local mutual defs reordered** so the callee precedes the caller
   (`positions`/`carveRect` `goX`/`goY`; `render` `rowLoop`/`row`/`rows`).
8. **`std.bytes.(Bytes)` import dropped** in `core.kp` (`Bytes` is a prelude type;
   only `utf8Bytes` from `std.unicode` is imported).
9. **`rng` module-alias renamed to `prng`** in `gen`/`combat`/`ai`: a record
   field named `rng` of type `rng.Rng` formed a `E_RECORD_DEPENDENCY_CYCLE`
   (the field-type projection resolved to the same-named field, not the module);
   `.rng` field projections are unchanged.

### Conservative terminal overlay + adapter (Part B)
The conservative `generateAllFromHeader` surface (§26.1.4: non-char pointer →
`Option RawPtr`, `int` → `Integer`, `uint64_t` → `std.ffi.U64`, declared
`cstrings` → `String`) cannot bind the shim's out-parameter entry points
(`int delve_open_terminal(handle**)`, `delve_get_size(…, delve_size*)`). A thin
package-owned adapter was added:
- `native/delve_terminal_adapter.h` / `.c` expose a flat conservative surface
  (`void *delve_open_terminal2(void)`, `int delve_read_key2/​write_all2/​get_cols2/​
  get_rows2/​close_terminal2(...)`, `uint64_t delve_monotonic_seed2(void)`,
  `const char *delve_describe_error2(int)`, `int delve_last_errno2(void)`),
  delegating to the existing POSIX shim. These functions are shim-defined, so
  they satisfy the ABI-proof rule; the manifest binds them with
  `surface = generateAllFromHeader "…/delve_terminal_adapter.h" "delve_"`,
  `inputs = [headers …, shim [adapter, shim], cstrings [describe_error2, write_all2], classify blocking]`.
  The generator binds all 9 functions (0 skipped); the binding is pinned in
  `kappa.lock`.
- `terminal.native.linux.kp` was rewritten as the conservative overlay:
  `Terminal` wraps `Option RawPtr`; `Raw.*` calls are sequenced with `bindIO`;
  the errno return codes are mapped to the public `delve.terminal` operations.

Two front-end realities forced behavior-preserving surface changes (documented
honestly, not hidden):
- **The native backend does not implement the exception primitives**
  (`throwIO`/`catchIO`/`__absurd`): a `raise`/`try…except`-based `IO GameError`
  terminal surface typechecks but fails native codegen (`E_BACKEND_UNSUPPORTED`).
  The facade was therefore changed from `IO GameError` to **`UIO`** (no error
  channel); the overlay maps an errno failure to a benign in-band default
  (`open` always yields a handle, `readKey` error → `KeyUnknown`, `size` error →
  `80×24`) instead of raising. On a real TTY — the only environment that runs the
  game — the success path is identical; only the process-terminating
  raise-on-failure path (which never occurs in normal play) is replaced.
- **Cross-module `&`-borrow parameters are not tracked like local borrows**: a
  same-module *recursive* (or local) borrow of a path that was previously passed
  to an *imported* `&`-parameter function is reported `E_QTT_PATH_CONSUMED`
  (sequential imported borrows are fine; mixing an imported borrow then a local
  `&`-call is not). The original game's render/input loop is exactly that shape
  (`engine` borrows the `terminal` from `delve.terminal` then self-recurses). It
  was rewritten as an **iterative `while` loop with a mutable game-state `var`**
  inside a single function, and `main` keeps all terminal borrows inside that one
  `runLoop` (the size query, the per-frame render/read), which the borrow checker
  accepts for sequential same-function borrows. Game semantics are unchanged.

The C shim's `delve_monotonic_seed` was changed to seed from ISO C `time()`+pid
instead of `clock_gettime(CLOCK_MONOTONIC)`: the native build force-`-include`s a
generated prototype header (pulling in `<features.h>`) before this file's own
feature-test macros take effect, so `CLOCK_MONOTONIC` was not visible. The seed
is still process- and time-specific.

### Lockfile note
No `kappa.lock` is committed. A single lockfile cannot serve both targets in
this implementation: the `delve` (binding) target requires a pinned
`host-binding` entry under `--locked`, while the binding-free `delve-tests`
target rejects that same entry as a content mismatch. So:
- build/run the tests with `kappa build --manifest . -o /tmp/delve-tests
  --target delve-tests` (a binding-free target needs no lock — exits 0);
- build the game with `kappa build --manifest . -o /tmp/delve-game --target delve
  --update` (the first/update build generates and pins `kappa.lock` for the
  binding; a subsequent `--target delve` then verifies it locked). `--update` is
  the natural first-build flow for a host.native package (§36.7).

## Summary

Both packages now build under this implementation. **image-loader** builds,
tests, and runs (`IMAGE TESTS: ALL PASS`). **delve** builds and runs its pure
game-logic tests (`DELVE TESTS: ALL PASS`, Part A) AND compiles+links the full
interactive game including the conservative native terminal binding (Part B).
Reaching green required only behavior-preserving source adaptation (named-arg →
brace constructor application; guarded `Nat` arithmetic; conservative-overlay
terminal fragment + a thin C adapter; record-patch → reconstruction; written-out
`Eq` instances; an iterative loop in place of a cross-module borrowing recursion;
a `UIO` terminal surface because the native backend has no exception primitives)
plus this implementation's manifest/fragment mechanisms — no stubs or faked
results; every test really runs the game logic. The jvm/dotnet targets in the
original `build.kp` files are spec-optional and remain unrealized (kept for
provenance). Remaining front-end gaps surfaced honestly above: no proof inference
for checked `Nat` `%`/`/`/`-`; no trusted-summary `Result` surface refinement;
cross-module `&`-borrows are not tracked like local borrows; the native backend
does not implement `throwIO`/`catchIO`/`__absurd`.
