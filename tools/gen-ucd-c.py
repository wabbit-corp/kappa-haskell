#!/usr/bin/env python3
"""Generate runtime/kappa_ucd.h from src/Kappa/UnicodeData.hs.

The native runtime's Unicode primitives (§29.4: normalize / grapheme
segmentation) must be observationally identical to the interpreter, which
runs the table-driven algorithms in Kappa.Unicode over the committed
Kappa.UnicodeData tables.  To guarantee the C tables equal those exact
tables, this script PARSES the committed Haskell module (its table
literals are also valid Python literals) and re-emits them as C arrays.
No Unicode database is consulted for those tables, so they can never drift
from what the interpreter uses.

The case-folding table (Data.Text.toCaseFold, not held in
Kappa.UnicodeData) is derived from Python's str.casefold(); both implement
full Unicode case folding.

Run once and commit runtime/kappa_ucd.h; the build never runs this script
(boot packages / hermetic builds), mirroring tools/gen-unicode-data.py.
"""
import ast
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "..", "src", "Kappa", "UnicodeData.hs")
OUT = os.path.join(HERE, "..", "runtime", "kappa_ucd.h")


def parse_table(name):
    """Return the literal value of `name = <expr>` from UnicodeData.hs."""
    prefix = name + " = "
    with open(SRC, encoding="utf-8") as f:
        for line in f:
            if line.startswith(prefix):
                return ast.literal_eval(line[len(prefix):].strip())
    raise SystemExit(f"table {name!r} not found in {SRC}")


def emit_ccc(out, table):
    # [(cp, ccc)] sorted by cp -> two parallel arrays for binary search.
    rows = sorted(table)
    out.append(f"#define KU_CCC_N {len(rows)}")
    out.append("static const int32_t ku_ccc_cp[KU_CCC_N] = {"
               + ",".join(str(cp) for cp, _ in rows) + "};")
    out.append("static const uint8_t ku_ccc_val[KU_CCC_N] = {"
               + ",".join(str(v) for _, v in rows) + "};")


def emit_decomp(out, table, tag):
    # [(cp, [cp...])] sorted by cp -> {cp, off, len} index + flat int pool.
    rows = sorted(table)
    pool = []
    idx = []
    for cp, ds in rows:
        idx.append((cp, len(pool), len(ds)))
        pool.extend(ds)
    out.append(f"#define KU_{tag}_N {len(idx)}")
    out.append(f"static const int32_t ku_{tag.lower()}_cp[KU_{tag}_N] = {{"
               + ",".join(str(cp) for cp, _, _ in idx) + "};")
    out.append(f"static const int32_t ku_{tag.lower()}_off[KU_{tag}_N] = {{"
               + ",".join(str(o) for _, o, _ in idx) + "};")
    out.append(f"static const int32_t ku_{tag.lower()}_len[KU_{tag}_N] = {{"
               + ",".join(str(l) for _, _, l in idx) + "};")
    out.append(f"#define KU_{tag}_POOL_N {len(pool) if pool else 1}")
    out.append(f"static const int32_t ku_{tag.lower()}_pool[KU_{tag}_POOL_N] = {{"
               + (",".join(str(x) for x in pool) if pool else "0") + "};")


def emit_composition(out, table):
    # [((a,b), r)] sorted by (a,b) -> parallel arrays for binary search.
    rows = sorted(((a, b, r) for (a, b), r in table))
    out.append(f"#define KU_COMP_N {len(rows)}")
    out.append("static const int32_t ku_comp_a[KU_COMP_N] = {"
               + ",".join(str(a) for a, _, _ in rows) + "};")
    out.append("static const int32_t ku_comp_b[KU_COMP_N] = {"
               + ",".join(str(b) for _, b, _ in rows) + "};")
    out.append("static const int32_t ku_comp_r[KU_COMP_N] = {"
               + ",".join(str(r) for _, _, r in rows) + "};")


def emit_gcb(out, table):
    # [(lo, hi, cls)] sorted by lo -> arrays for lookupLE binary search.
    rows = sorted(table)
    out.append(f"#define KU_GCB_N {len(rows)}")
    out.append("static const int32_t ku_gcb_lo[KU_GCB_N] = {"
               + ",".join(str(lo) for lo, _, _ in rows) + "};")
    out.append("static const int32_t ku_gcb_hi[KU_GCB_N] = {"
               + ",".join(str(hi) for _, hi, _ in rows) + "};")
    out.append("static const uint8_t ku_gcb_cls[KU_GCB_N] = {"
               + ",".join(str(cls) for _, _, cls in rows) + "};")


def emit_casefold(out):
    # str.casefold() differences, cp -> [cp...]; same {cp,off,len}+pool shape.
    idx = []
    pool = []
    for cp in range(0x110000):
        if 0xD800 <= cp <= 0xDFFF:
            continue
        s = chr(cp).casefold()
        folded = [ord(ch) for ch in s]
        if folded != [cp]:
            idx.append((cp, len(pool), len(folded)))
            pool.extend(folded)
    out.append(f"#define KU_FOLD_N {len(idx)}")
    out.append("static const int32_t ku_fold_cp_arr[KU_FOLD_N] = {"
               + ",".join(str(cp) for cp, _, _ in idx) + "};")
    out.append("static const int32_t ku_fold_off[KU_FOLD_N] = {"
               + ",".join(str(o) for _, o, _ in idx) + "};")
    out.append("static const int32_t ku_fold_len[KU_FOLD_N] = {"
               + ",".join(str(l) for _, _, l in idx) + "};")
    out.append(f"#define KU_FOLD_POOL_N {len(pool) if pool else 1}")
    out.append("static const int32_t ku_fold_pool[KU_FOLD_POOL_N] = {"
               + (",".join(str(x) for x in pool) if pool else "0") + "};")


def main():
    ver = parse_table("unicodeDataVersion")
    out = []
    out.append("/* kappa_ucd.h — Unicode tables for the native runtime's §29.4")
    out.append(" * std.unicode primitives.  GENERATED by tools/gen-ucd-c.py from")
    out.append(" * src/Kappa/UnicodeData.hs (the same tables the interpreter uses)")
    out.append(" * plus Python str.casefold() — do not edit by hand. */")
    out.append("#ifndef KAPPA_UCD_H")
    out.append("#define KAPPA_UCD_H")
    out.append("#include <stdint.h>")
    out.append(f"#define KU_UCD_VERSION_MAJOR {ver[0]}")
    out.append(f"#define KU_UCD_VERSION_MINOR {ver[1]}")
    out.append(f"#define KU_UCD_VERSION_PATCH {ver[2]}")
    emit_ccc(out, parse_table("combiningClassTable"))
    emit_decomp(out, parse_table("canonicalDecompTable"), "CANON")
    emit_decomp(out, parse_table("compatDecompTable"), "COMPAT")
    emit_composition(out, parse_table("compositionTable"))
    emit_gcb(out, parse_table("gcbRangeTable"))
    emit_casefold(out)
    out.append("#endif /* KAPPA_UCD_H */")
    with open(OUT, "w", encoding="utf-8") as f:
        f.write("\n".join(out) + "\n")
    print(f"wrote {OUT}")


if __name__ == "__main__":
    main()
