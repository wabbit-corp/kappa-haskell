/* kappart_show.c — show / format (Dragon4) + the string builder.
 *
 * Split out of kappart.c (see kappart_internal.h).  Owns show_int_val /
 * str_append, the show_* literal formatters, the Dragon4 shortest-round-trip
 * Double formatter, and the Double/String/Scalar/Byte kp_* prims + show entry
 * points.  The string builder (sbuf) and utf8_next are inline in
 * kappart_internal.h. */
#include "kappart.h"
#include "kappart_internal.h"

#include <gmp.h>
#include <inttypes.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
/* ── pure primitives (mirror Kappa.Eval.evalPurePrim for the subset) ── */

KValue *show_int_val(KValue *v) {
  if (kis_int_word(v)) {
    char buf[32];
    int n = snprintf(buf, sizeof buf, "%" PRId64, kint_word(v));
    return kstr(buf, (size_t)n);
  }
  if (kis_imm(v)) krt_fail("showInt: not an Int");
  if (v->tag == K_BIGINT) {
    char *s = mpz_get_str(NULL, 10, (const __mpz_struct *)v->as.big.mpz);
    return kstr0(s); /* s is GC-allocated by the GMP allocator */
  }
  krt_fail("showInt: not an Int");
}

KValue *str_append(KValue *a, KValue *b) {
  if (kis_imm(a) || kis_imm(b) || a->tag != K_STR || b->tag != K_STR)
    krt_fail("stringAppend: argument is not a String");
  size_t la = a->as.str.len, lb = b->as.str.len;
  char *buf = (char *)kgc_alloc_atomic(la + lb + 1);
  memcpy(buf, a->as.str.p, la);
  memcpy(buf + la, b->as.str.p, lb);
  buf[la + lb] = '\0';
  KValue *r = alloc_val(K_STR);
  r->as.str.p = buf;
  r->as.str.len = la + lb;
  return r;
}

/* ── show helpers (match the interpreter's Haskell `show`) ─────────── */

#include <math.h>


static const char *const ascii_tab[32] = {
  "NUL","SOH","STX","ETX","EOT","ENQ","ACK","a","b","t","n","v","f","r","SO","SI",
  "DLE","DC1","DC2","DC3","DC4","NAK","SYN","ETB","CAN","EM","SUB","ESC","FS","GS","RS","US"};

/* Append showLitChar cp; *numeric set when the escape is a \DDD decimal,
 * *so set when it is \SO — both may need a "\&" before the next char. */
static void show_lit_char(sbuf *b, uint32_t cp, int *numeric, int *so) {
  *numeric = 0; *so = 0;
  if (cp == '\\') sb_puts(b, "\\\\");
  else if (cp >= 0x20 && cp <= 0x7e) sb_putc(b, (char)cp);
  else if (cp == 0x7f) sb_puts(b, "\\DEL");
  else if (cp < 0x20) { sb_putc(b, '\\'); sb_puts(b, ascii_tab[cp]); if (cp == 14) *so = 1; }
  else { char tmp[16]; snprintf(tmp, sizeof tmp, "\\%u", cp); sb_puts(b, tmp); *numeric = 1; }
}

KValue *show_scalar(KValue *v) {
  if (kis_imm(v) || v->tag != K_CHR) krt_fail("showScalar: not a scalar");
  sbuf b; sb_init(&b); sb_putc(&b, '\'');
  if (v->as.chr == '\'') sb_puts(&b, "\\'");
  else { int n, s; show_lit_char(&b, v->as.chr, &n, &s); }
  sb_putc(&b, '\''); return sb_to_str(&b);
}

KValue *show_string_lit(KValue *v) {
  if (kis_imm(v) || v->tag != K_STR) krt_fail("showStringLit: not a String");
  sbuf b; sb_init(&b); sb_putc(&b, '"');
  const unsigned char *p = (const unsigned char *)v->as.str.p;
  const unsigned char *end = p + v->as.str.len;
  int pn = 0, pso = 0; /* previous char's numeric / SO escape flags */
  while (p < end) {
    uint32_t cp; p += utf8_next(p, end, &cp);
    /* §Haskell \& protection: a decimal escape then a digit, or \SO then H */
    if ((pn && cp >= '0' && cp <= '9') || (pso && cp == 'H')) sb_puts(&b, "\\&");
    if (cp == '"') { sb_puts(&b, "\\\""); pn = 0; pso = 0; }
    else show_lit_char(&b, cp, &pn, &pso);
  }
  sb_putc(&b, '"'); return sb_to_str(&b);
}

/* ── Dragon4: shortest correctly-rounded decimal digits, matching GHC ────────
 *
 * GHC's `show :: Double -> String` extracts its digits with
 * `GHC.Float.floatToDigits 10` — the Burger-Dybvig "Printing Floating-Point
 * Numbers Quickly and Accurately" scaled-bigint loop (a.k.a. Dragon4).  The
 * old `show_double` instead grew the precision of `%.*e` until `strtod`
 * round-tripped; on tie cases (e.g. bits 0x43144d1cd2252491) that last digit
 * disagrees with Dragon4.  We port `floatToDigits 10` verbatim over GMP so the
 * digits are *guaranteed* identical to the interpreter, then hand them to the
 * unchanged Haskell-style formatter below.
 *
 * `decode_double` mirrors GHC's `decodeFloat`: it returns (f0, e0) with x ==
 * f0 * 2^e0 and f0 NORMALIZED to exactly 53 significant bits (subnormals are
 * shifted up, the exponent lowered to match) — GHC does the same, then the
 * floatToDigits `(f,e)` step re-denormalizes through `n = minExp - e0`.
 */

/* Decode a finite, nonzero, positive double into (f0, e0): x == f0 * 2^e0 with
 * f0 in [2^52, 2^53). Matches GHC `decodeFloat` for IEEE-754 binary64. */
static void decode_double(double ax, uint64_t *f0, int *e0) {
  uint64_t bits; memcpy(&bits, &ax, sizeof bits);
  uint64_t mant = bits & 0xfffffffffffffULL;       /* low 52 bits */
  int      rexp = (int)((bits >> 52) & 0x7ff);     /* biased exponent */
  if (rexp == 0) {
    /* subnormal: value = mant * 2^(1-1023-52) = mant * 2^-1074.  Normalize the
     * mantissa up to 53 bits the way GHC's decodeFloat does. */
    uint64_t m = mant; int e = -1074;
    while (m < (1ULL << 52)) { m <<= 1; e--; }
    *f0 = m; *e0 = e;
  } else {
    /* normal: value = (2^52 | mant) * 2^(rexp-1023-52). */
    *f0 = (1ULL << 52) | mant;
    *e0 = rexp - 1075;                              /* (rexp-1023) - 52 */
  }
}

/* expt b n == b^n, into z (n >= 0). */
static void ftd_expt(mpz_t z, unsigned long b, unsigned long n) {
  mpz_ui_pow_ui(z, b, n);
}

/* floatToDigits 10 over GMP: write the decimal digits (one per byte, value
 * 0..9) into out[] and return the count; *kout receives the Haskell `k`
 * (value == 0.d1d2... * 10^k).  Caller guarantees ax finite, > 0.  At most 17
 * significant digits are produced, so out[] need only hold ~20. */
static int float_to_digits10(double ax, int *kout, char *out) {
  const unsigned long base = 10, b = 2; const long p = 53;
  const int minExp0 = -1021;                 /* fst (floatRange x) */
  const long minExp = (long)minExp0 - p;     /* -1074: the real minimum exponent */
  uint64_t f0u; int e0;
  decode_double(ax, &f0u, &e0);

  mpz_t f, r, s, mUp, mDn, tmp, be, bk, dn, prod;
  mpz_inits(f, r, s, mUp, mDn, tmp, be, bk, dn, prod, (mpz_ptr)0);
  mpz_set_ui(f, (unsigned long)(f0u >> 32));
  mpz_mul_2exp(f, f, 32);
  mpz_add_ui(f, f, (unsigned long)(f0u & 0xffffffffULL));   /* f = f0 (64-bit) */
  int e = e0;

  /* (f,e): re-denormalize so subnormals get an impossibly low exponent. */
  long n = minExp - (long)e0;
  if (n > 0) { ftd_expt(tmp, b, (unsigned long)n); mpz_fdiv_q(f, f, tmp); e = e0 + (int)n; }

  /* bpm1 = b^(p-1) = 2^52 — test "f is the smallest normalized mantissa". */
  mpz_t bpm1; mpz_init(bpm1); ftd_expt(bpm1, b, (unsigned long)(p - 1));

  if (e >= 0) {
    ftd_expt(be, b, (unsigned long)e);                 /* be = b^e */
    if (mpz_cmp(f, bpm1) == 0) {
      /* (f*be*b*2, 2*b, be*b, be) */
      mpz_mul(r, f, be); mpz_mul_ui(r, r, b); mpz_mul_ui(r, r, 2);
      mpz_set_ui(s, 2 * b);
      mpz_mul_ui(mUp, be, b);
      mpz_set(mDn, be);
    } else {
      /* (f*be*2, 2, be, be) */
      mpz_mul(r, f, be); mpz_mul_ui(r, r, 2);
      mpz_set_ui(s, 2);
      mpz_set(mUp, be); mpz_set(mDn, be);
    }
  } else {
    if (e > (int)minExp && mpz_cmp(f, bpm1) == 0) {
      /* (f*b*2, expt b (-e+1)*2, b, 1) */
      mpz_mul_ui(r, f, b); mpz_mul_ui(r, r, 2);
      ftd_expt(s, b, (unsigned long)(-e + 1)); mpz_mul_ui(s, s, 2);
      mpz_set_ui(mUp, b); mpz_set_ui(mDn, 1);
    } else {
      /* (f*2, expt b (-e)*2, 1, 1) */
      mpz_mul_ui(r, f, 2);
      ftd_expt(s, b, (unsigned long)(-e)); mpz_mul_ui(s, s, 2);
      mpz_set_ui(mUp, 1); mpz_set_ui(mDn, 1);
    }
  }

  /* k0: the GHC fast estimate for b==2, base==10. */
  int lx = (int)(p - 1) + e0;
  int k1 = (int)(((long)lx * 8651) / 28738);
  int k0 = (lx >= 0) ? k1 + 1 : k1;

  /* fixup: smallest k with r + mUp <= 10^k * s (for k>=0), else
   * 10^(-k) * (r + mUp) <= s. */
  mpz_t rpUp; mpz_init(rpUp); mpz_add(rpUp, r, mUp);
  int k = k0;
  for (;;) {
    if (k >= 0) {
      ftd_expt(bk, base, (unsigned long)k);
      mpz_mul(prod, bk, s);
      if (mpz_cmp(rpUp, prod) <= 0) break;       /* r+mUp <= 10^k * s */
    } else {
      ftd_expt(bk, base, (unsigned long)(-k));
      mpz_mul(prod, bk, rpUp);
      if (mpz_cmp(prod, s) <= 0) break;          /* 10^(-k)*(r+mUp) <= s */
    }
    k++;
  }
  mpz_clear(rpUp);

  /* Apply k to the scaled big integers, then run the generate loop. */
  if (k >= 0) {
    ftd_expt(bk, base, (unsigned long)k);
    mpz_mul(s, s, bk);                            /* s := s * 10^k */
  } else {
    ftd_expt(bk, base, (unsigned long)(-k));
    mpz_mul(r, r, bk); mpz_mul(mUp, mUp, bk); mpz_mul(mDn, mDn, bk);
  }

  int nd = 0;
  for (;;) {
    /* (dn, r) = (r*10) quotRem s ; mUp*=10 ; mDn*=10 */
    mpz_mul_ui(r, r, base);
    mpz_fdiv_qr(dn, r, r, s);                     /* dn = r/s, r = r mod s (>=0) */
    mpz_mul_ui(mUp, mUp, base);
    mpz_mul_ui(mDn, mDn, base);
    int digit = (int)mpz_get_ui(dn);
    int low  = mpz_cmp(r, mDn) < 0;               /* r < mDn */
    mpz_add(tmp, r, mUp);                         /* r + mUp */
    int high = mpz_cmp(tmp, s) > 0;               /* r + mUp > s */
    if (!low && !high) { out[nd++] = (char)digit; continue; }
    if (low && !high)      out[nd++] = (char)digit;
    else if (!low && high) out[nd++] = (char)(digit + 1);
    else {                                        /* (True,True): tie -> r*2 < s ? */
      mpz_mul_ui(tmp, r, 2);
      out[nd++] = (mpz_cmp(tmp, s) < 0) ? (char)digit : (char)(digit + 1);
    }
    break;
  }

  mpz_clears(f, r, s, mUp, mDn, tmp, be, bk, dn, prod, bpm1, (mpz_ptr)0);
  *kout = k;
  return nd;
}

/* show :: Double, matching Haskell's shortest round-trip + format rules. */
KValue *show_double(double x) {
  if (isnan(x)) return kstr0("NaN");
  if (isinf(x)) return kstr0(x < 0 ? "-Infinity" : "Infinity");
  if (x == 0.0) return kstr0(signbit(x) ? "-0.0" : "0.0");
  int neg = x < 0; double ax = neg ? -x : x;
  /* shortest correctly-rounded digits via floatToDigits 10 (Dragon4). */
  char dig10[24]; int e;
  int nd = float_to_digits10(ax, &e, dig10);
  /* render digits as ASCII for the formatter below ('0'..'9'). */
  char digits[32];
  for (int i = 0; i < nd; i++) digits[i] = (char)('0' + dig10[i]);
  sbuf b; sb_init(&b); if (neg) sb_putc(&b, '-');
  if (e < 0 || e > 7) { /* scientific: d1 . (rest|0) e (e-1) */
    sb_putc(&b, digits[0]); sb_putc(&b, '.');
    if (nd == 1) sb_putc(&b, '0'); else for (int i = 1; i < nd; i++) sb_putc(&b, digits[i]);
    char tmp[16]; snprintf(tmp, sizeof tmp, "e%d", e - 1); sb_puts(&b, tmp);
  } else if (e <= 0) { /* 0.00ddd */
    sb_puts(&b, "0.");
    for (int i = 0; i < -e; i++) sb_putc(&b, '0');
    for (int i = 0; i < nd; i++) sb_putc(&b, digits[i]);
  } else { /* fixed: place point after e digits */
    for (int i = 0; i < e; i++) sb_putc(&b, i < nd ? digits[i] : '0');
    sb_putc(&b, '.');
    if (e >= nd) sb_putc(&b, '0'); else for (int i = e; i < nd; i++) sb_putc(&b, digits[i]);
  }
  return sb_to_str(&b);
}

/* ── bytes / byte / grapheme helpers (§6.5, §29.5) ─────────────────── */

KValue *kp_addDouble(KValue *x, KValue *y) { return kdbl(kas_dbl(x) + kas_dbl(y)); }
KValue *kp_subDouble(KValue *x, KValue *y) { return kdbl(kas_dbl(x) - kas_dbl(y)); }
KValue *kp_mulDouble(KValue *x, KValue *y) { return kdbl(kas_dbl(x) * kas_dbl(y)); }
KValue *kp_divDouble(KValue *x, KValue *y) { return kdbl(kas_dbl(x) / kas_dbl(y)); }
KValue *kp_negDouble(KValue *x) { return kdbl(-kas_dbl(x)); }
KValue *kp_ltDouble(KValue *x, KValue *y) { return kbool(kas_dbl(x) < kas_dbl(y)); }
KValue *kp_floatEq(KValue *x, KValue *y) { return kbool(kas_dbl(x) == kas_dbl(y)); }
KValue *kp_eqDouble(KValue *x, KValue *y) { /* §6.1.3 raw-bit equality */
  uint64_t bx, by;
  double da = kas_dbl(x), db = kas_dbl(y);
  memcpy(&bx, &da, 8); memcpy(&by, &db, 8);
  return kbool(bx == by);
}
KValue *kp_stringAppend(KValue *x, KValue *y) { return str_append(x, y); }
KValue *kp_eqStr(KValue *x, KValue *y) { return kbool(klit_eq(x, y)); }
KValue *kp_ltStr(KValue *x, KValue *y) {
  if (kis_imm(x) || kis_imm(y) || x->tag != K_STR || y->tag != K_STR)
    krt_fail("ltStr: argument is not a String");
  size_t la = x->as.str.len, lb = y->as.str.len, m = la < lb ? la : lb;
  int c = memcmp(x->as.str.p, y->as.str.p, m);
  return kbool(c < 0 || (c == 0 && la < lb));
}
KValue *kp_eqScalar(KValue *x, KValue *y) {
  if (kis_imm(x) || kis_imm(y) || x->tag != K_CHR || y->tag != K_CHR)
    krt_fail("eqScalar: argument is not a scalar");
  return kbool(x->as.chr == y->as.chr);
}
KValue *kp_ltScalar(KValue *x, KValue *y) {
  if (kis_imm(x) || kis_imm(y) || x->tag != K_CHR || y->tag != K_CHR)
    krt_fail("ltScalar: argument is not a scalar");
  return kbool(x->as.chr < y->as.chr);
}
/* show* (pure, 1-arg): pervasive in numeric output. */
KValue *kp_showInt(KValue *x) { return show_int_val(x); }
KValue *kp_showDouble(KValue *x) { return show_double(kas_dbl(x)); }
KValue *kp_showScalar(KValue *x) { return show_scalar(x); }
KValue *kp_showStringLit(KValue *x) { return show_string_lit(x); }
/* §6.5 byte compares + §29.1 bitwise (hot in hashing / byte loops).  Byte values
 * are always boxed (K_BYTE) — never immediates — so the deref is sound. */
KValue *kp_eqByte(KValue *x, KValue *y) { return kbool(x->as.byte == y->as.byte); }
KValue *kp_ltByte(KValue *x, KValue *y) { return kbool(x->as.byte < y->as.byte); }
