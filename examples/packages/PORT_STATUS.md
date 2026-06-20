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
(`native/delve_terminal.c` + `.h`). Native binding support is exactly this
implementation's spec mechanism (§26.1.2/§27.1.1): `generateFromHeader` over the
shim header + `shim [...]` + safe paths + lock/provenance + classification — the
hardening committed this pass applies directly. Original `build.kp` uses a
schematic `nativeBinding(headers=, sources=, summaries=trustedSummary …)` schema
and a **trusted-summary-refined** `Raw` surface (`Raw.TerminalError`, `Ok/Err`
result wrappers, ownership) that this implementation does not synthesize — its
generator produces the conservative scalar/pointer surface (§26.1.4), so the
`terminal.native.linux.kp` fragment would need rewriting as a conservative overlay
(handle as `Option RawPtr`, errno `int`, error translation in Kappa) plus a thin
companion adapter presenting a Kappa-friendly conservative surface (the C shim's
`out`-param `int delve_open_terminal(handle**)` does not map to a direct
conservative call). Not yet adapted.

## Summary

Bringing either package fully green requires source adaptation (named-arg → brace
constructor application; guarded `Nat` subtraction; conservative-overlay terminal
fragment) and/or further front-end features (proof inference, trusted-summary
refinement). The jvm/dotnet targets are spec-optional. These are tracked, not
hidden.
