#!/usr/bin/env python3
"""Generate src/Kappa/UnicodeData.hs from Python's unicodedata (UCD 15.0.0).

Run once and commit the generated module; the build itself never runs
this script (boot packages only, hermetic builds).

Data emitted:
  * canonical combining classes (nonzero entries only),
  * fully-expanded canonical decompositions (NFD, Hangul excluded:
    Hangul decomposition/composition is algorithmic at runtime),
  * fully-expanded compatibility decompositions where they differ from
    the canonical ones (NFKD, Hangul excluded),
  * primary composite pairs (canonical two-element decompositions minus
    the full composition exclusions, derived via the NFC round-trip),
  * Grapheme_Cluster_Break classes per UAX #29 (Unicode 15.0.0).

Grapheme_Cluster_Break derivation notes (the UCD rule data files are not
available hermetically; the classes are derived from unicodedata
categories plus the property lists below):
  * Other_Grapheme_Extend is read from a UCD 15.0.0 PropList.txt copy
    when PROPLIST points at one; otherwise a vendored snapshot of that
    property (small, stable) is used.
  * Prepend uses Prepended_Concatenation_Mark plus a hardcoded snapshot
    of Indic_Syllabic_Category=Consonant_Preceding_Repha/Consonant_Prefixed
    (IndicSyllabicCategory.txt is not available).
  * Extended_Pictographic is a hardcoded snapshot of the emoji-data
    15.0 derived ranges.
"""
import os
import sys
import unicodedata as ud

OUT = os.path.join(os.path.dirname(__file__), "..", "src", "Kappa", "UnicodeData.hs")

MAX = 0x110000

def cps():
    for cp in range(MAX):
        if 0xD800 <= cp <= 0xDFFF:
            continue
        yield cp

def is_hangul_syllable(cp):
    return 0xAC00 <= cp <= 0xD7A3

# ── property list parsing / snapshots ────────────────────────────────

def parse_proplist(path, prop):
    out = set()
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.split("#")[0].strip()
            if not line or ";" not in line:
                continue
            rng, name = [p.strip() for p in line.split(";", 1)]
            if name != prop:
                continue
            if ".." in rng:
                lo, hi = rng.split("..")
                out.update(range(int(lo, 16), int(hi, 16) + 1))
            else:
                out.add(int(rng, 16))
    return out

# UCD 15.0.0 PropList.txt Other_Grapheme_Extend (snapshot)
OTHER_GRAPHEME_EXTEND_SNAPSHOT = set(
    [0x09BE, 0x09D7, 0x0B3E, 0x0B57, 0x0BBE, 0x0BD7, 0x0CC2, 0x0CD5, 0x0CD6,
     0x0D3E, 0x0D57, 0x0DCF, 0x0DDF, 0x1715, 0x1734, 0x1B35, 0x200C, 0x302E,
     0x302F, 0x3099, 0x309A, 0xFF9E, 0xFF9F, 0x1133E, 0x11357, 0x114B0,
     0x114BD, 0x115AF, 0x11930, 0x1D165, 0x1D16E, 0x1D16F, 0x1D170, 0x1D171,
     0x1D172]
    + list(range(0xE0020, 0xE0080))
)

# UCD 15.0.0 PropList.txt Prepended_Concatenation_Mark (snapshot)
PREPENDED_CONCATENATION_MARK_SNAPSHOT = set(
    [0x0600, 0x0601, 0x0602, 0x0603, 0x0604, 0x0605, 0x06DD, 0x070F, 0x0890,
     0x0891, 0x08E2, 0x110BD, 0x110CD]
)

# IndicSyllabicCategory.txt 15.0: Consonant_Preceding_Repha + Consonant_Prefixed
INDIC_PREPEND = set(
    [0x0D4E, 0x111C2, 0x111C3, 0x1193F, 0x11941, 0x11A3A, 0x11D46, 0x11F02]
    + list(range(0x11A84, 0x11A8A))
)

# emoji-data.txt 15.0 Extended_Pictographic (consolidated ranges)
EXT_PICT_RANGES = [
    (0x00A9, 0x00A9), (0x00AE, 0x00AE), (0x203C, 0x203C), (0x2049, 0x2049),
    (0x2122, 0x2122), (0x2139, 0x2139), (0x2194, 0x2199), (0x21A9, 0x21AA),
    (0x231A, 0x231B), (0x2328, 0x2328), (0x2388, 0x2388), (0x23CF, 0x23CF),
    (0x23E9, 0x23F3), (0x23F8, 0x23FA), (0x24C2, 0x24C2), (0x25AA, 0x25AB),
    (0x25B6, 0x25B6), (0x25C0, 0x25C0), (0x25FB, 0x25FE), (0x2600, 0x2605),
    (0x2607, 0x2612), (0x2614, 0x2685), (0x2690, 0x2705), (0x2708, 0x2712),
    (0x2714, 0x2714), (0x2716, 0x2716), (0x271D, 0x271D), (0x2721, 0x2721),
    (0x2728, 0x2728), (0x2733, 0x2734), (0x2744, 0x2744), (0x2747, 0x2747),
    (0x274C, 0x274C), (0x274E, 0x274E), (0x2753, 0x2755), (0x2757, 0x2757),
    (0x2763, 0x2767), (0x2795, 0x2797), (0x27A1, 0x27A1), (0x27B0, 0x27B0),
    (0x27BF, 0x27BF), (0x2934, 0x2935), (0x2B05, 0x2B07), (0x2B1B, 0x2B1C),
    (0x2B50, 0x2B50), (0x2B55, 0x2B55), (0x3030, 0x3030), (0x303D, 0x303D),
    (0x3297, 0x3297), (0x3299, 0x3299),
    (0x1F000, 0x1F0FF), (0x1F10D, 0x1F10F), (0x1F12F, 0x1F12F),
    (0x1F16C, 0x1F171), (0x1F17E, 0x1F17F), (0x1F18E, 0x1F18E),
    (0x1F191, 0x1F19A), (0x1F1AD, 0x1F1E5), (0x1F201, 0x1F20F),
    (0x1F21A, 0x1F21A), (0x1F22F, 0x1F22F), (0x1F232, 0x1F23A),
    (0x1F23C, 0x1F23F), (0x1F249, 0x1F3FA), (0x1F400, 0x1F53D),
    (0x1F546, 0x1F64F), (0x1F680, 0x1F6FF), (0x1F774, 0x1F77F),
    (0x1F7D5, 0x1F7FF), (0x1F80C, 0x1F80F), (0x1F848, 0x1F84F),
    (0x1F85A, 0x1F85F), (0x1F888, 0x1F88F), (0x1F8AE, 0x1F8FF),
    (0x1F90C, 0x1F93A), (0x1F93C, 0x1F945), (0x1F947, 0x1FAFF),
    (0x1FC00, 0x1FFFD),
]

EMOJI_MODIFIER = set(range(0x1F3FB, 0x1F400))

# SpacingMark exceptions per UAX #29 (Unicode 15.0)
SPACING_MARK_EXCEPTIONS = set(
    [0x102B, 0x102C, 0x1038, 0x1083, 0x108F, 0x1A61, 0x1A63, 0x1A64,
     0xAA7B, 0xAA7D, 0x11720, 0x11721]
    + list(range(0x1062, 0x1065)) + list(range(0x1067, 0x106E))
    + list(range(0x1087, 0x108D)) + list(range(0x109A, 0x109D))
    + list(range(0x19B0, 0x19B5)) + [0x19B8, 0x19B9]
    + list(range(0x19BB, 0x19C1)) + [0x19C8, 0x19C9]
)


def main():
    if ud.unidata_version != "15.0.0":
        print(f"warning: unicodedata is {ud.unidata_version}, expected 15.0.0",
              file=sys.stderr)

    proplist = os.environ.get("PROPLIST")
    if proplist and os.path.exists(proplist):
        oge = parse_proplist(proplist, "Other_Grapheme_Extend")
        pcm = parse_proplist(proplist, "Prepended_Concatenation_Mark")
        src = proplist
    else:
        oge = OTHER_GRAPHEME_EXTEND_SNAPSHOT
        pcm = PREPENDED_CONCATENATION_MARK_SNAPSHOT
        src = "vendored snapshot"
    print(f"Other_Grapheme_Extend/PCM source: {src}", file=sys.stderr)

    # ── normalization tables ─────────────────────────────────────────
    cccs = []
    nfd = []
    nfkd = []
    for cp in cps():
        c = chr(cp)
        k = ud.combining(c)
        if k:
            cccs.append((cp, k))
        if is_hangul_syllable(cp):
            continue
        d = ud.normalize("NFD", c)
        if d != c:
            # exclude Hangul syllables that appear inside expansions: none do
            nfd.append((cp, [ord(x) for x in d]))
        kd = ud.normalize("NFKD", c)
        if kd != d:
            nfkd.append((cp, [ord(x) for x in kd]))

    # primary composites: canonical pair decompositions minus exclusions
    comp = []
    for cp in cps():
        if is_hangul_syllable(cp):
            continue
        dec = ud.decomposition(chr(cp))
        if not dec or dec.startswith("<"):
            continue
        parts = [int(p, 16) for p in dec.split()]
        if len(parts) != 2:
            continue
        a, b = parts
        # full composition exclusion test: NFC must recompose to cp
        if ud.normalize("NFC", chr(a) + chr(b)) == chr(cp):
            comp.append(((a, b), cp))

    # ── grapheme cluster break classes ───────────────────────────────
    # 0 Other, 1 CR, 2 LF, 3 Control, 4 Extend, 5 ZWJ, 6 RI, 7 Prepend,
    # 8 SpacingMark, 9 ExtPict  (Hangul L/V/T/LV/LVT are algorithmic)
    ext_pict = set()
    for lo, hi in EXT_PICT_RANGES:
        ext_pict.update(range(lo, hi + 1))

    def gcb(cp):
        if cp == 0x000D:
            return 1
        if cp == 0x000A:
            return 2
        c = chr(cp)
        cat = ud.category(c)
        if cat in ("Zl", "Zp", "Cc", "Cs"):
            return 3
        if cat == "Cf" and cp not in (0x200C, 0x200D) and cp not in pcm:
            return 3
        if cp == 0x200D:
            return 5
        if cat in ("Mn", "Me") or cp in oge or cp in EMOJI_MODIFIER:
            return 4
        if 0x1F1E6 <= cp <= 0x1F1FF:
            return 6
        if cp in pcm or cp in INDIC_PREPEND:
            return 7
        if (cat == "Mc" or cp in (0x0E33, 0x0EB3)) \
                and cp not in SPACING_MARK_EXCEPTIONS:
            return 8
        if cp in ext_pict:
            return 9
        return 0

    ranges = []
    prev_cls = None
    start = None
    last = None
    for cp in cps():
        cls = gcb(cp)
        if cls == 0:
            if prev_cls is not None:
                ranges.append((start, last, prev_cls))
                prev_cls = None
            continue
        if prev_cls == cls and cp == last + 1:
            last = cp
        else:
            if prev_cls is not None:
                ranges.append((start, last, prev_cls))
            prev_cls = cls
            start = cp
            last = cp
    if prev_cls is not None:
        ranges.append((start, last, prev_cls))

    # ── emit ─────────────────────────────────────────────────────────
    def pairs(xs):
        return ",".join(f"({a},{b})" for a, b in xs)

    def decomps(xs):
        return ",".join(f"({cp},{lst})" for cp, lst in xs)

    def triples(xs):
        return ",".join(f"({a},{b},{c})" for a, b, c in xs)

    def comps(xs):
        return ",".join(f"(({a},{b}),{c})" for (a, b), c in xs)

    with open(OUT, "w", encoding="utf-8") as f:
        f.write(f"""-- | Embedded Unicode Character Database tables (UCD {ud.unidata_version}).
--
-- GENERATED by tools/gen-unicode-data.py — do not edit by hand.
-- See that script for derivation notes (canonical/compatibility
-- decompositions are fully expanded; Hangul is algorithmic at runtime;
-- the Grapheme_Cluster_Break classes are derived per UAX #29).
module Kappa.UnicodeData
  ( unicodeDataVersion
  , combiningClassTable
  , canonicalDecompTable
  , compatDecompTable
  , compositionTable
  , GCB (..)
  , gcbRangeTable
  ) where

unicodeDataVersion :: (Int, Int, Int)
unicodeDataVersion = ({ud.unidata_version.replace('.', ',')})

-- | (codepoint, canonical combining class); nonzero classes only.
combiningClassTable :: [(Int, Int)]
combiningClassTable = [{pairs(cccs)}]

-- | Fully expanded canonical decompositions (NFD), Hangul excluded.
canonicalDecompTable :: [(Int, [Int])]
canonicalDecompTable = [{decomps(nfd)}]

-- | Fully expanded compatibility decompositions (NFKD) where they
-- differ from the canonical expansion, Hangul excluded.
compatDecompTable :: [(Int, [Int])]
compatDecompTable = [{decomps(nfkd)}]

-- | Primary composite pairs (composition exclusions removed).
compositionTable :: [((Int, Int), Int)]
compositionTable = [{comps(comp)}]

-- | Grapheme_Cluster_Break classes (UAX #29). Hangul L\\/V\\/T\\/LV\\/LVT
-- are recognized algorithmically by the consumer, not listed here.
data GCB
  = GcbOther
  | GcbCR
  | GcbLF
  | GcbControl
  | GcbExtend
  | GcbZWJ
  | GcbRegionalIndicator
  | GcbPrepend
  | GcbSpacingMark
  | GcbExtendedPictographic
  deriving stock (Eq, Show)

-- | Sorted, disjoint (lo, hi, class) ranges; absent code points are
-- GcbOther (or Hangul, handled algorithmically).
gcbRangeTable :: [(Int, Int, Int)]
gcbRangeTable = [{triples(ranges)}]
""")
    print(f"wrote {OUT}: ccc={len(cccs)} nfd={len(nfd)} nfkd={len(nfkd)} "
          f"comp={len(comp)} gcbRanges={len(ranges)}", file=sys.stderr)


if __name__ == "__main__":
    main()
