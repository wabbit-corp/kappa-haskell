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
2. **`Nat` subtraction** — both the unguarded measure form `bytesLength src - offset`
   (`acme/png/binary.kp` `remaining`/`byteAt`; the `decreases` measures in
   `png/parser.kp:45`, `png/ihdr.kp:71`, `png/crc32.kp:15`) AND the guarded
   recursive decrements `if i == 0 then … else f (i - 1)` (`qoi/parser.kp:85,92,99`).
   §28.2 checked subtraction requires a proof `subDefined x y = True`
   (KNOWN_SPEC_ISSUES #6). PRECISE ROOT CAUSE (investigated this pass): even the
   explicitly-`<=`-guarded form `if y <= x then x - y else 0` is rejected. The flow
   machinery (`Check.propProof`/`factReduce`, `csBoolFacts`) discharges an equality
   goal only by reducing the goal term against branch-fact *condition terms*. But
   for `Nat`: the guard `y <= x` lowers through `Ord`/`compare`
   (`if ltInt (natToInt y) (natToInt x) then LT elif eqInt … then EQ else GT`,
   Prelude:1010), the guard `i == 0` lowers to `eqInt (natToInt i) 0 = False`
   (Prelude:1007), while the proof goal `subDefined x y` lowers to
   `leInt (natToInt y) (natToInt x) = True` (Prelude:1266). These are structurally
   unrelated terms over the same `natToInt`+Int-primitive substrate, so `factReduce`
   (which matches whole condition terms) cannot connect them. Discharging this needs
   a genuine §16.4.4 flow-typing **arithmetic bridge**: a sound decision step over
   Int-primitive branch facts (`eqInt`/`ltInt`/`leInt` on `natToInt _`) that proves
   the `leInt`-shaped goal — including the Nat-non-negativity lemma `natToInt n ≥ 0`
   needed for `eqInt (natToInt i) 0 = False ⟹ leInt 1 (natToInt i) = True`. This is
   a real elaborator feature (multi-step, with regression surface on the implicit
   solver), not a convertibility tweak; it is the shared prerequisite for both the
   guarded decrements and the `decreases` measures here. The `CheckedSub Nat`
   instance exists; `natOfInt (subInt (natToInt a) (natToInt b))` is the total
   saturating escape hatch (verified to compile) but changes the package's intended
   checked-arithmetic semantics, so it is a rewrite, not a transparent fix.
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
