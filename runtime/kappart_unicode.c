/* kappart_unicode.c — std.unicode: the UTF-8 codec + the UCD-table-driven
 * algorithms (UAX #15 normalization, UAX #29 grapheme/word segmentation,
 * case folding).
 *
 * Split out of kappart.c (see kappart_internal.h).  This is the ONLY
 * translation unit that includes kappa_ucd.h — the generated UCD tables are
 * ~100KB, so including the header anywhere else would duplicate them in every
 * object file.  The code-point buffer (cpbuf) and utf8_next are inline in
 * kappart_internal.h. */
#include "kappart.h"
#include "kappart_internal.h"
#include "kappa_ucd.h" /* §29.4 Unicode tables (generated; see tools/gen-ucd-c.py) */

#include <stdint.h>
#include <string.h>
/* ── §29.4 std.unicode helpers (table-free: codec, scalars, cursors) ── */

/* UTF-8 encode one scalar (assumed a valid Unicode scalar) into b. */
void utf8_encode(uint32_t cp, sbuf *b) {
  if (cp < 0x80) sb_putc(b, (char)cp);
  else if (cp < 0x800) {
    sb_putc(b, (char)(0xC0 | (cp >> 6)));
    sb_putc(b, (char)(0x80 | (cp & 0x3F)));
  } else if (cp < 0x10000) {
    sb_putc(b, (char)(0xE0 | (cp >> 12)));
    sb_putc(b, (char)(0x80 | ((cp >> 6) & 0x3F)));
    sb_putc(b, (char)(0x80 | (cp & 0x3F)));
  } else {
    sb_putc(b, (char)(0xF0 | (cp >> 18)));
    sb_putc(b, (char)(0x80 | ((cp >> 12) & 0x3F)));
    sb_putc(b, (char)(0x80 | ((cp >> 6) & 0x3F)));
    sb_putc(b, (char)(0x80 | (cp & 0x3F)));
  }
}

/* Strict decode of one scalar at p (< end), matching Data.Text's UTF-8:
 * no overlong forms, no surrogates (D800..DFFF), nothing above U+10FFFF.
 * Returns bytes consumed (1..4) for a complete well-formed scalar, 0 when
 * the bytes are a valid but INCOMPLETE final sequence (a strict prefix of
 * some valid encoding), and -1 when they begin an invalid sequence. */
int utf8_strict(const unsigned char *p, const unsigned char *end, uint32_t *cp) {
  size_t avail = (size_t)(end - p);
  unsigned c = p[0];
  if (c < 0x80) { *cp = c; return 1; }
  if (c < 0xC2) return -1;                 /* 80..BF stray cont; C0/C1 overlong */
  if (c < 0xE0) {                          /* 2-byte C2..DF */
    if (avail < 2) return 0;
    if ((p[1] & 0xC0) != 0x80) return -1;
    *cp = ((c & 0x1F) << 6) | (p[1] & 0x3F);
    return 2;
  }
  if (c < 0xF0) {                          /* 3-byte E0..EF */
    unsigned lo = (c == 0xE0) ? 0xA0 : 0x80;       /* exclude overlong */
    unsigned hi = (c == 0xED) ? 0x9F : 0xBF;       /* exclude surrogates */
    if (avail < 2) return 0;
    if (p[1] < lo || p[1] > hi) return -1;
    if (avail < 3) return 0;
    if ((p[2] & 0xC0) != 0x80) return -1;
    *cp = ((c & 0x0F) << 12) | ((p[1] & 0x3F) << 6) | (p[2] & 0x3F);
    return 3;
  }
  if (c < 0xF5) {                          /* 4-byte F0..F4 */
    unsigned lo = (c == 0xF0) ? 0x90 : 0x80;       /* exclude overlong */
    unsigned hi = (c == 0xF4) ? 0x8F : 0xBF;       /* cap at U+10FFFF */
    if (avail < 2) return 0;
    if (p[1] < lo || p[1] > hi) return -1;
    if (avail < 3) return 0;
    if ((p[2] & 0xC0) != 0x80) return -1;
    if (avail < 4) return 0;
    if ((p[3] & 0xC0) != 0x80) return -1;
    *cp = ((c & 0x07) << 18) | ((p[1] & 0x3F) << 12) | ((p[2] & 0x3F) << 6) | (p[3] & 0x3F);
    return 4;
  }
  return -1;                               /* F5..FF */
}

/* Whole-buffer strict validity (mirrors Data.Text.Encoding.decodeUtf8'). */
int utf8_valid_all(const unsigned char *p, size_t len) {
  const unsigned char *end = p + len;
  while (p < end) { uint32_t cp; int n = utf8_strict(p, end, &cp); if (n <= 0) return 0; p += n; }
  return 1;
}

/* Length of the longest wholly-valid UTF-8 prefix (= splitValidUtf8Prefix). */
size_t utf8_valid_prefix_len(const unsigned char *p, size_t len) {
  const unsigned char *q = p, *end = p + len;
  while (q < end) { uint32_t cp; int n = utf8_strict(q, end, &cp); if (n <= 0) break; q += n; }
  return (size_t)(q - p);
}

/* Is the run an incomplete trailing sequence — i.e. valid once one, two,
 * or three 0x80 continuation bytes are appended (the interpreter's exact
 * isIncompleteUtf8Tail heuristic)?  rest is short in practice. */
int utf8_is_incomplete_tail(const unsigned char *p, size_t len) {
  unsigned char *buf = (unsigned char *)kgc_alloc_atomic(len + 3);
  if (len) memcpy(buf, p, len);
  for (int k = 1; k <= 3; k++) {
    buf[len + k - 1] = 0x80;
    if (utf8_valid_all(buf, len + (size_t)k)) return 1;
  }
  return 0;
}

/* Number of Unicode scalars in a (valid) UTF-8 string. */
size_t utf8_scalar_count(const unsigned char *p, size_t len) {
  const unsigned char *end = p + len; size_t n = 0;
  while (p < end) { uint32_t cp; int k = utf8_next(p, end, &cp); p += (k > 0 ? k : 1); n++; }
  return n;
}

/* Byte offset of the start of scalar index `idx` (clamped to [0,count]). */
size_t utf8_scalar_byte_offset(const unsigned char *p, size_t len, size_t idx) {
  const unsigned char *q = p, *end = p + len; size_t n = 0;
  while (q < end && n < idx) { uint32_t cp; int k = utf8_next(q, end, &cp); q += (k > 0 ? k : 1); n++; }
  return (size_t)(q - p);
}
/* Box an unsigned 64-bit result as the corresponding non-negative integer
 * (K_INT when it fits a signed 64-bit, else a K_BIGINT). Public: the native
 * FFI marshalling boxes U64/Usize results through it (§26.1.1 exact-width). */
KValue *ku64(uint64_t u) {
  if (u <= (uint64_t)INT64_MAX) return kint((int64_t)u);
  mpz_t z; mpz_init(z); mpz_import(z, 1, -1, sizeof(uint64_t), 0, 0, &u);
  return kbig_from_mpz(z);
}

/* ── §29.4 std.unicode table-driven algorithms (UAX #15 / UAX #29) ────
 * These mirror Kappa.Unicode exactly, over the same Kappa.UnicodeData
 * tables (re-emitted into kappa_ucd.h), so the native results are
 * observationally identical to the interpreter's. */


/* Exact-match binary search over a sorted int32 key array. */
static int ku_bsearch(const int32_t *arr, int n, int32_t key) {
  int lo = 0, hi = n - 1;
  while (lo <= hi) { int mid = (lo + hi) / 2; if (arr[mid] == key) return mid; if (arr[mid] < key) lo = mid + 1; else hi = mid - 1; }
  return -1;
}

static int ku_ccc(uint32_t cp) { int i = ku_bsearch(ku_ccc_cp, KU_CCC_N, (int32_t)cp); return i < 0 ? 0 : ku_ccc_val[i]; }

/* Canonical (or, when compat, compatibility-then-canonical) decomposition
 * of cp; returns a pointer into the pool and its length, or NULL. */
static const int32_t *ku_decomp(int compat, uint32_t cp, int *outlen) {
  if (compat) { int i = ku_bsearch(ku_compat_cp, KU_COMPAT_N, (int32_t)cp); if (i >= 0) { *outlen = ku_compat_len[i]; return ku_compat_pool + ku_compat_off[i]; } }
  int i = ku_bsearch(ku_canon_cp, KU_CANON_N, (int32_t)cp); if (i >= 0) { *outlen = ku_canon_len[i]; return ku_canon_pool + ku_canon_off[i]; }
  return NULL;
}

/* Primary composite of (a,b), or -1.  Sorted by (a,b). */
static int32_t ku_compose(uint32_t a, uint32_t b) {
  int lo = 0, hi = KU_COMP_N - 1;
  while (lo <= hi) {
    int mid = (lo + hi) / 2; int32_t ca = ku_comp_a[mid], cb = ku_comp_b[mid];
    if (ca == (int32_t)a && cb == (int32_t)b) return ku_comp_r[mid];
    if (ca < (int32_t)a || (ca == (int32_t)a && cb < (int32_t)b)) lo = mid + 1; else hi = mid - 1;
  }
  return -1;
}

/* Hangul constants (UAX #15 §3.12). */
enum { KU_SBASE = 0xAC00, KU_LBASE = 0x1100, KU_VBASE = 0x1161, KU_TBASE = 0x11A7,
       KU_VCOUNT = 21, KU_TCOUNT = 28, KU_NCOUNT = 588, KU_SCOUNT = 11172 };

/* Recursive full decomposition (Hangul algorithmic; tables expanded). */
static void ku_full_decompose(int compat, uint32_t c, cpbuf *out) {
  if (c >= KU_SBASE && c < KU_SBASE + KU_SCOUNT) {
    int s = (int)c - KU_SBASE; uint32_t l = KU_LBASE + s / KU_NCOUNT;
    uint32_t v = KU_VBASE + (s % KU_NCOUNT) / KU_TCOUNT; uint32_t t = KU_TBASE + s % KU_TCOUNT;
    cp_push(out, l); cp_push(out, v); if (t != KU_TBASE) cp_push(out, t); return;
  }
  int len; const int32_t *d = ku_decomp(compat, c, &len);
  if (!d) { cp_push(out, c); return; }
  for (int i = 0; i < len; i++) ku_full_decompose(compat, (uint32_t)d[i], out);
}

/* Canonical ordering: stable insertion sort of each maximal nonzero-ccc run. */
static void ku_canonical_order(uint32_t *a, size_t n) {
  size_t i = 0;
  while (i < n) {
    if (ku_ccc(a[i]) == 0) { i++; continue; }
    size_t j = i; while (j < n && ku_ccc(a[j]) != 0) j++;
    for (size_t k = i + 1; k < j; k++) {
      uint32_t v = a[k]; int cv = ku_ccc(v); size_t m = k;
      while (m > i && ku_ccc(a[m - 1]) > cv) { a[m] = a[m - 1]; m--; }
      a[m] = v;
    }
    i = j;
  }
}

/* Primary composition (UAX #15 §3.11, D117).  Writes into out (<= n). */
static size_t ku_compose_chars(const uint32_t *a, size_t n, uint32_t *out) {
  if (n == 0) return 0;
  size_t oi = 0; uint32_t starter = a[0];
  uint32_t *pend = (uint32_t *)kgc_alloc_atomic((n ? n : 1) * sizeof(uint32_t)); size_t pn = 0;
  for (size_t i = 1; i < n; i++) {
    uint32_t c = a[i]; int cc = ku_ccc(c);
    if (cc == 0 && pn == 0) {
      int32_t comp = ku_compose(starter, c); if (comp >= 0) { starter = (uint32_t)comp; continue; }
    } else if (cc != 0) {
      int blocked = (pn > 0) && (ku_ccc(pend[pn - 1]) >= cc);
      if (!blocked) { int32_t comp = ku_compose(starter, c); if (comp >= 0) { starter = (uint32_t)comp; continue; } }
    }
    if (cc == 0) { out[oi++] = starter; for (size_t k = 0; k < pn; k++) out[oi++] = pend[k]; starter = c; pn = 0; }
    else pend[pn++] = c;
  }
  out[oi++] = starter; for (size_t k = 0; k < pn; k++) out[oi++] = pend[k];
  return oi;
}

/* Decode a (valid) UTF-8 K_STR into a code-point buffer. */
void ku_decode(const unsigned char *s, size_t slen, cpbuf *out) {
  const unsigned char *p = s, *end = s + slen;
  while (p < end) { uint32_t cp; int k = utf8_next(p, end, &cp); p += (k > 0 ? k : 1); cp_push(out, cp); }
}

/* §29.4 normalize: form 0=NFC 1=NFD 2=NFKC 3=NFKD (Kappa.Unicode order). */
KValue *ku_normalize(int form, const unsigned char *s, size_t slen) {
  int compat = (form == 2 || form == 3);
  cpbuf in; cp_init(&in); ku_decode(s, slen, &in);
  cpbuf dec; cp_init(&dec);
  for (size_t i = 0; i < in.len; i++) ku_full_decompose(compat, in.p[i], &dec);
  ku_canonical_order(dec.p, dec.len);
  uint32_t *fp = dec.p; size_t fn = dec.len;
  if (form == 0 || form == 2) {
    uint32_t *out = (uint32_t *)kgc_alloc_atomic((dec.len ? dec.len : 1) * sizeof(uint32_t));
    fn = ku_compose_chars(dec.p, dec.len, out); fp = out;
  }
  sbuf b; sb_init(&b); for (size_t i = 0; i < fn; i++) utf8_encode(fp[i], &b); return sb_to_str(&b);
}

/* UAX #29 Grapheme_Cluster_Break class of a scalar (Kappa.Unicode GcbClass). */
enum { GcOther = 0, GcCR, GcLF, GcControl, GcExtend, GcZWJ, GcRI, GcPrepend,
       GcSpacingMark, GcExtPict, GcL, GcV, GcT, GcLV, GcLVT };
static int ku_gcb_raw(uint32_t cp) {
  int lo = 0, hi = KU_GCB_N - 1, best = -1;
  while (lo <= hi) { int mid = (lo + hi) / 2; if (ku_gcb_lo[mid] <= (int32_t)cp) { best = mid; lo = mid + 1; } else hi = mid - 1; }
  if (best >= 0 && (int32_t)cp <= ku_gcb_hi[best]) return ku_gcb_cls[best];
  return 0;
}
static int ku_gcb_of(uint32_t n) {
  if ((n >= 0x1100 && n <= 0x115F) || (n >= 0xA960 && n <= 0xA97C)) return GcL;
  if ((n >= 0x1160 && n <= 0x11A7) || (n >= 0xD7B0 && n <= 0xD7C6)) return GcV;
  if ((n >= 0x11A8 && n <= 0x11FF) || (n >= 0xD7CB && n <= 0xD7FB)) return GcT;
  if (n >= KU_SBASE && n < KU_SBASE + KU_SCOUNT) return ((n - KU_SBASE) % KU_TCOUNT == 0) ? GcLV : GcLVT;
  switch (ku_gcb_raw(n)) {
    case 1: return GcCR; case 2: return GcLF; case 3: return GcControl; case 4: return GcExtend;
    case 5: return GcZWJ; case 6: return GcRI; case 7: return GcPrepend; case 8: return GcSpacingMark;
    case 9: return GcExtPict; default: return GcOther;
  }
}

/* Number of scalars in the extended grapheme cluster at cps[start..n). */
size_t ku_grapheme_len(const uint32_t *cps, size_t n, size_t start) {
  if (start >= n) return 0;
  int prev = ku_gcb_of(cps[start]);
  int pictExtend = (prev == GcExtPict), pictZWJ = 0, riRun = (prev == GcRI) ? 1 : 0;
  size_t i = start + 1;
  for (; i < n; i++) {
    int cls = ku_gcb_of(cps[i]); int brk;
    if (prev == GcCR && cls == GcLF) brk = 0;
    else if (prev == GcControl || prev == GcCR || prev == GcLF) brk = 1;
    else if (cls == GcControl || cls == GcCR || cls == GcLF) brk = 1;
    else if (prev == GcL && (cls == GcL || cls == GcV || cls == GcLV || cls == GcLVT)) brk = 0;
    else if ((prev == GcLV || prev == GcV) && (cls == GcV || cls == GcT)) brk = 0;
    else if ((prev == GcLVT || prev == GcT) && cls == GcT) brk = 0;
    else if (cls == GcExtend || cls == GcZWJ) brk = 0;
    else if (cls == GcSpacingMark) brk = 0;
    else if (prev == GcPrepend) brk = 0;
    else if (prev == GcZWJ && cls == GcExtPict && pictZWJ) brk = 0;
    else if (prev == GcRI && cls == GcRI) brk = (riRun % 2 == 0);
    else brk = 1;
    if (brk) break;
    int nPictExtend = (cls == GcExtPict) ? 1 : (cls == GcExtend ? pictExtend : 0);
    int nPictZWJ = (cls == GcZWJ && pictExtend);
    int nRiRun = (cls == GcRI) ? riRun + 1 : 0;
    pictExtend = nPictExtend; pictZWJ = nPictZWJ; riRun = nRiRun; prev = cls;
  }
  return i - start;
}

size_t ku_grapheme_count(const uint32_t *cps, size_t n) {
  size_t i = 0, count = 0;
  while (i < n) { size_t l = ku_grapheme_len(cps, n, i); i += (l ? l : 1); count++; }
  return count;
}

/* Encode cps[a..b) back to a UTF-8 K_STR. */
KValue *ku_encode_range(const uint32_t *cps, size_t a, size_t b) {
  sbuf sb; sb_init(&sb); for (size_t i = a; i < b; i++) utf8_encode(cps[i], &sb); return sb_to_str(&sb);
}

/* Full case fold of one scalar: writes folded scalars into out. */
void ku_casefold_scalar(uint32_t c, cpbuf *out) {
  int i = ku_bsearch(ku_fold_cp_arr, KU_FOLD_N, (int32_t)c);
  if (i < 0) { cp_push(out, c); return; }
  for (int k = 0; k < ku_fold_len[i]; k++) cp_push(out, (uint32_t)ku_fold_pool[ku_fold_off[i] + k]);
}

/* Haskell Data.Char.isSpace (ASCII controls + Unicode space separators). */
int ku_is_space(uint32_t c) {
  if (c == ' ' || (c >= '\t' && c <= '\r')) return 1;       /* \t \n \v \f \r */
  if (c == 0x85 || c == 0xA0 || c == 0x1680) return 1;
  if (c >= 0x2000 && c <= 0x200A) return 1;
  return c == 0x2028 || c == 0x2029 || c == 0x202F || c == 0x205F || c == 0x3000;
}
