# New package targets — port status (honest)

Two uploaded packages were unpacked here (sources preserved verbatim from
`input/`, provenance intact). Both were authored against a *different/hypothetical*
Kappa front end (schematic `build.kp` manifests; jvm/dotnet backends; assumed
proof inference and named-argument constructor syntax). This file records,
honestly, what builds under THIS implementation and what is blocked, with exact
causes. Neither package builds end-to-end yet.

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

**Build BLOCKED** by package source written against features this front end does
not accept (these are real, separately-tracked items, NOT silent failures):
1. `Ctor (field = value) …` **parenthesized named-argument constructor
   application** (e.g. `acme/image/core.kp` `qoiAsRaster`). This front end parses
   `(x = e)` as an anonymous record; the supported named form is the brace block
   `Ctor { field = value, … }`. (Spec §16.1.7 named-argument blocks.)
2. Unguarded **`Nat` subtraction** `bytesLength src - offset` (`acme/png/binary.kp`
   `remaining`/`byteAt`). §28.2 checked subtraction requires a proof
   `offset <= bytesLength src`; this is the deliberate partial-subtraction design,
   tracked as KNOWN_SPEC_ISSUES #6 (needs a guarding `if`/flow fact or a saturating
   helper). The `CheckedSub Nat` instance exists; the proof obligation is real.
3. **Multi-line operator continuation** at constant deeper indent (`u32NatOfBytes`'s
   `+`-chain) — KNOWN_SPEC_ISSUES #13.

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
