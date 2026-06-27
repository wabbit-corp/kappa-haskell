/* boxed.h — cross-TU surface internal to the kappart runtime.
 *
 * kappart.c was split into cohesive translation units (gc.c,
 * value.c, bignum.c, show.c, unicode.c,
 * prims.c).  Functions that used to be file-static helpers but are now
 * called across that split need a shared declaration; that is what this header
 * provides.  It is PURELY internal — the public surface (the kp_ and kpf_
 * prims, and the hot immediate/deref inlines like kis_imm/kderef) stays in the
 * public kappart.h.
 *
 * Two kinds of declaration live here:
 *   (B) static-inline HOT ops whose bodies live in the header so they inline at
 *       every call site regardless of which TU they land in (after the split
 *       these calls cross TU boundaries; -flto recovers most of it, but keeping
 *       the bodies inline makes the result link-site-independent).  These come
 *       first because some of the (A) prototypes refer to their types (sbuf).
 *   (A) cross-TU PROTOTYPES for functions DEFINED in exactly one TU and CALLED
 *       from another.  These were the in-file forward declarations and statics.
 *
 * kappa_ucd.h (≈100KB of generated UCD tables) is deliberately NOT included
 * here: only unicode.c includes it, so the tables exist in exactly one
 * object file.  Including it from this header would duplicate them everywhere. */
#ifndef BOXED_H
#define BOXED_H

#include "kappart.h"
#include <gmp.h>

#include <string.h> /* memcpy, for the inline string/scalar buffers below */

/* ── (B) hot inline ops (bodies in the header so they inline cross-TU) ── */

/* Growable byte buffer for show/format output; the bytes are pointer-free, so
 * it is allocated on the atomic (unscanned) GC heap. */
typedef struct { char *p; size_t len, cap; } sbuf;
static inline void sb_init(sbuf *b) { b->cap = 32; b->p = (char *)kgc_alloc_atomic(b->cap); b->len = 0; }
static inline void sb_putc(sbuf *b, char c) {
  if (b->len + 1 > b->cap) {
    size_t nc = b->cap * 2; char *np = (char *)kgc_alloc_atomic(nc);
    memcpy(np, b->p, b->len); b->p = np; b->cap = nc;
  }
  b->p[b->len++] = c;
}
static inline void sb_puts(sbuf *b, const char *s) { while (*s) sb_putc(b, *s++); }
static inline KValue *sb_to_str(sbuf *b) { return kstr(b->p, b->len); }

/* decode the next UTF-8 scalar from p (< end); returns bytes consumed.
 * A multibyte sequence truncated by `end` decodes the lead byte alone
 * (returns 1) rather than over-reading past the buffer — every branch
 * checks that all its continuation bytes are in range. */
static inline int utf8_next(const unsigned char *p, const unsigned char *end, uint32_t *cp) {
  unsigned c = p[0];
  if (c < 0x80) { *cp = c; return 1; }
  if ((c >> 5) == 0x6 && p + 2 <= end) { *cp = ((c & 0x1f) << 6) | (p[1] & 0x3f); return 2; }
  if ((c >> 4) == 0xe && p + 3 <= end) { *cp = ((c & 0x0f) << 12) | ((p[1] & 0x3f) << 6) | (p[2] & 0x3f); return 3; }
  if ((c >> 3) == 0x1e && p + 4 <= end) { *cp = ((c & 0x07) << 18) | ((p[1] & 0x3f) << 12) | ((p[2] & 0x3f) << 6) | (p[3] & 0x3f); return 4; }
  *cp = c; return 1;
}

/* Growable scalar (code-point) buffer; pointer-free, so allocate atomic. */
typedef struct { uint32_t *p; size_t len, cap; } cpbuf;
static inline void cp_init(cpbuf *b) { b->cap = 16; b->p = (uint32_t *)kgc_alloc_atomic(b->cap * sizeof(uint32_t)); b->len = 0; }
static inline void cp_push(cpbuf *b, uint32_t c) {
  if (b->len + 1 > b->cap) {
    size_t nc = b->cap * 2; uint32_t *np = (uint32_t *)kgc_alloc_atomic(nc * sizeof(uint32_t));
    memcpy(np, b->p, b->len * sizeof(uint32_t)); b->p = np; b->cap = nc;
  }
  b->p[b->len++] = c;
}

/* std.prelude.Some / None constructors (hot in the option-returning prims). */
static inline KValue *ksome(KValue *x) { KValue *a[1]; a[0] = x; return kctor(KCT_SOME, "std.prelude.Some", 1, a); }
static inline KValue *knone(void) { return kctor0(KCT_NONE, "std.prelude.None"); }

/* ── (A) cross-TU prototypes ─────────────────────────────────────────── */

/* The raw value-box allocator (defined in value.c; bignum.c
 * calls it from kbig_from_mpz).  alloc_val_atomic stays private to
 * value.c — only its scalar constructors use it. */
KValue *alloc_val(KTag tag);

/* The inline/bignum boundary (bignum.c).  value↔bignum are mutually
 * recursive across the split: kint() (value) escapes to kmpz_set_i64/
 * kbig_from_mpz (bignum), while kfrom_mpz/kload_mpz/krat/as_rat (bignum) build
 * on the value constructors.  Declaring both sides here closes the cycle. */
void kmpz_set_i64(mpz_t out, int64_t v);
int kmpz_fits_i64_p(const mpz_t z);          /* does |z| fit signed 64-bit? */
int64_t kmpz_get_i64(const mpz_t z);         /* z -> int64 (caller checks fits) */
KValue *kbig_from_mpz(const mpz_t z);
KValue *kfrom_mpz(const mpz_t z);
void kload_mpz(KValue *v, mpz_t out);
int kint_cmp(KValue *a, KValue *b);          /* normalizing Int compare */
KValue *krat(mpz_t num, mpz_t den);
void as_rat(KValue *r, mpz_t num, mpz_t den);
KValue *rat_addsub(KValue *x, KValue *y, int sub); /* exact a/b ± c/d (backs addRat/subRat) */

/* Int membership across the inline/bignum boundary (value.c), used by
 * klit_eq (value) and kvalue_rep_eq (prims). */
int kis_int_any(KValue *v);

/* show / string-builder boundary (show.c), called by the prims. */
KValue *show_int_val(KValue *v);
KValue *str_append(KValue *a, KValue *b);
KValue *show_scalar(KValue *v);
KValue *show_string_lit(KValue *v);
KValue *show_double(double x);

/* Representation equality (prims.c), used by atomicCompareExchange. */
int kvalue_rep_eq(KValue *a, KValue *b);

/* std.unicode helpers the prims call (unicode.c).  These are the only
 * UCD-table consumers, so their definitions stay in the unicode TU; the prims
 * reach them through these declarations. */
void utf8_encode(uint32_t cp, sbuf *b);
int utf8_strict(const unsigned char *p, const unsigned char *end, uint32_t *cp);
int utf8_valid_all(const unsigned char *p, size_t len);
size_t utf8_valid_prefix_len(const unsigned char *p, size_t len);
int utf8_is_incomplete_tail(const unsigned char *p, size_t len);
size_t utf8_scalar_count(const unsigned char *p, size_t len);
size_t utf8_scalar_byte_offset(const unsigned char *p, size_t len, size_t idx);
KValue *ku_normalize(int form, const unsigned char *s, size_t slen);
void ku_decode(const unsigned char *s, size_t slen, cpbuf *out);
void ku_casefold_scalar(uint32_t c, cpbuf *out);
size_t ku_grapheme_count(const uint32_t *cps, size_t n);
size_t ku_grapheme_len(const uint32_t *cps, size_t n, size_t start);
KValue *ku_encode_range(const uint32_t *cps, size_t a, size_t b);
int ku_is_space(uint32_t c);

#endif /* BOXED_H */
