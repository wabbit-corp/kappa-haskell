/* kappart_bignum.c — arbitrary-precision integers (GMP) + Rational.
 *
 * Split out of kappart.c (see kappart_internal.h).  Owns the GMP<->int64
 * boundary (kmpz_*, kfrom_mpz, kbig_from_mpz, kload_mpz, kbigint_str), the
 * Rational ops (krat / as_rat / rat_addsub), the normalizing Int compare
 * (kint_cmp) + kint_binop_mpz / kint_is_zero, the Int kp_* arithmetic prims,
 * and the round-to-nearest-even Integer->Double conversion.  The value
 * constructors it builds on (kint, alloc_val, kdbl, ...) come from
 * kappart_value.c via kappart_internal.h / kappart.h. */
#include "kappart.h"
#include "kappart_internal.h"

#include <gmp.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
/* ── arbitrary-precision integers (GMP, §6) ────────────────────────── */
/* Representation: small values stay inline in K_INT (int64); a value that
 * does not fit int64 is a K_BIGINT pointing at a GC-allocated mpz.  Do not use
 * GMP's signed-long conversion helpers here: Windows is LLP64, so `long` is
 * only 32 bits even in a 64-bit process.  The runtime boundary is explicitly
 * signed 64-bit on every target. */

static void kmpz_i64_bounds(mpz_t min_out, mpz_t max_out) {
  static int ready = 0;
  static mpz_t min_i64;
  static mpz_t max_i64;
  if (!ready) {
    mpz_init_set_str(min_i64, "-9223372036854775808", 10);
    mpz_init_set_str(max_i64, "9223372036854775807", 10);
    ready = 1;
  }
  mpz_set(min_out, min_i64);
  mpz_set(max_out, max_i64);
}

int kmpz_fits_i64_p(const mpz_t z) {
  mpz_t lo, hi;
  mpz_inits(lo, hi, NULL);
  kmpz_i64_bounds(lo, hi);
  int ok = mpz_cmp(z, lo) >= 0 && mpz_cmp(z, hi) <= 0;
  mpz_clears(lo, hi, NULL);
  return ok;
}

int64_t kmpz_get_i64(const mpz_t z) {
  if (!kmpz_fits_i64_p(z)) krt_fail("Integer too large for signed 64-bit");
  int neg = mpz_sgn(z) < 0;
  mpz_t mag_z;
  mpz_init(mag_z);
  mpz_abs(mag_z, z);
  uint64_t mag = 0;
  size_t count = 0;
  mpz_export(&mag, &count, -1, sizeof(uint64_t), 0, 0, mag_z);
  mpz_clear(mag_z);
  if (!neg) return (int64_t)mag;
  if (mag == ((uint64_t)1 << 63)) return INT64_MIN;
  return -(int64_t)mag;
}

void kmpz_set_i64(mpz_t out, int64_t v) {
  uint64_t mag;
  int neg = v < 0;
  if (v == INT64_MIN) mag = ((uint64_t)1 << 63);
  else if (neg) mag = (uint64_t)(-v);
  else mag = (uint64_t)v;
  mpz_import(out, 1, -1, sizeof(uint64_t), 0, 0, &mag);
  if (neg) mpz_neg(out, out);
}

KValue *kbig_from_mpz(const mpz_t z) {
  KValue *r = alloc_val(K_BIGINT);
  __mpz_struct *p = (__mpz_struct *)kgc_alloc(sizeof(__mpz_struct));
  mpz_init_set(p, z);
  r->as.big.mpz = p;
  return r;
}

/* Demote to K_INT when the result fits int64, else keep a K_BIGINT. */
KValue *kfrom_mpz(const mpz_t z) {
  if (kmpz_fits_i64_p(z)) return kint(kmpz_get_i64(z));
  return kbig_from_mpz(z);
}

/* Load an immediate Int / K_INT / K_BIGINT into an mpz for a bignum operation. */
void kload_mpz(KValue *v, mpz_t out) {
  if (kis_imm_int(v)) kmpz_set_i64(out, kimm_int_val(v));   /* Stage 1 immediate */
  else if (kis_imm(v)) krt_fail("integer operation on a non-integer immediate");
  else if (v->tag == K_INT) kmpz_set_i64(out, v->as.i);
  else if (v->tag == K_BIGINT) mpz_set(out, (const __mpz_struct *)v->as.big.mpz);
  else krt_fail("integer operation on a non-integer value");
}

KValue *kbigint_str(const char *decimal) {
  mpz_t z;
  mpz_init(z);
  if (mpz_set_str(z, decimal, 10) != 0) krt_fail("kbigint_str: invalid decimal literal");
  return kfrom_mpz(z);
}
/* ── Rational (§28.2): an exact normalized ratio, carried at runtime as a
 * 2-field "__rat" constructor of bignum-capable num/den (positive den, gcd
 * 1). Opaque to source — only the Rational prims read it. ─────────────── */

KValue *krat(mpz_t num, mpz_t den) {
  if (mpz_sgn(den) == 0) krt_fail("Rational: zero denominator");
  if (mpz_sgn(den) < 0) { mpz_neg(num, num); mpz_neg(den, den); }
  mpz_t g; mpz_init(g); mpz_gcd(g, num, den);
  if (mpz_sgn(g) != 0) { mpz_divexact(num, num, g); mpz_divexact(den, den, g); }
  KValue *args[2]; args[0] = kfrom_mpz(num); args[1] = kfrom_mpz(den);
  return kctor(KCT_RAT, "__rat", 2, args);
}

void as_rat(KValue *r, mpz_t num, mpz_t den) {
  /* A Rational is a 2-field KCT_RAT ctor.  When both parts are small immediates
   * (e.g. 1/2) it is now a b011 packed word (Stage 1e), so identify it by tag id
   * and read the parts through the rep-agnostic accessors rather than a raw deref
   * — kctor_tagid/kctor_arg handle the packed and boxed forms uniformly. */
  if (kctor_tagid(r) != KCT_RAT)
    krt_fail("Rational operation on a non-Rational value");
  kload_mpz(kctor_arg(r, 0), num);
  kload_mpz(kctor_arg(r, 1), den);
}

/* a*d (+|-) c*b over b*d, then krat normalizes. */
KValue *rat_addsub(KValue *x, KValue *y, int sub) {
  mpz_t a, b, c, d, n, t, den; mpz_inits(a, b, c, d, n, t, den, NULL);
  as_rat(x, a, b); as_rat(y, c, d);
  mpz_mul(n, a, d); mpz_mul(t, c, b);
  if (sub) mpz_sub(n, n, t); else mpz_add(n, n, t);
  mpz_mul(den, b, d);
  return krat(n, den);
}
/* Bignum fallback for a binary integer op (used when either operand is a
 * K_BIGINT or the int64 fast path overflowed). */
typedef void (*kmpz_binop)(mpz_t, const mpz_t, const mpz_t);
static KValue *kint_binop_mpz(KValue *a, KValue *b, kmpz_binop op) {
  mpz_t za, zb, zr;
  mpz_init(za); mpz_init(zb); mpz_init(zr);
  kload_mpz(a, za); kload_mpz(b, zb);
  op(zr, za, zb);
  return kfrom_mpz(zr);
}

/* Total ordering across small/big integers. */
int kint_cmp(KValue *a, KValue *b) {
  /* Fast path: both Ints fit int64 (immediate or inline K_INT box) — compare
   * the words directly.  This also NORMALIZES the §5.3 boundary: a K_BIGINT that
   * fit int64 was canonicalised back to inline by kfrom_mpz, so a surviving
   * K_BIGINT is genuinely out of int64 range and falls to the mpz path. */
  if (kis_int_word(a) && kis_int_word(b)) {
    int64_t ia = kint_word(a), ib = kint_word(b);
    return ia < ib ? -1 : (ia > ib ? 1 : 0);
  }
  mpz_t za, zb;
  mpz_init(za); mpz_init(zb);
  kload_mpz(a, za); kload_mpz(b, zb);
  int c = mpz_cmp(za, zb);
  mpz_clear(za); mpz_clear(zb);
  return c;
}

static int kint_is_zero(KValue *v) {
  if (kis_imm_int(v)) return kimm_int_val(v) == 0;
  if (v->tag == K_INT) return v->as.i == 0;
  return mpz_sgn((const __mpz_struct *)v->as.big.mpz) == 0;
}
/* ── Direct primitive helpers (QW1) ──────────────────────────────────────
 * The pure primitives are factored into named, externally-visible helpers so
 * the codegen emits a DIRECT call (`kp_addInt(x, y)`) for a statically known
 * saturated primitive, or wraps the helper pointer in a curried K_NATIVE for
 * partial application — no string dispatch, no name lookup, no per-call
 * argument array.  These helpers ARE the single source of truth for each
 * primitive's semantics; there is no reflective by-name firing path. */
/* UNBOXING Stage 1: the inline arithmetic path operates on int64 words read out
 * of either an immediate (kis_imm_int) or a boxed K_INT (kis_int_word recognises
 * both).  __builtin_*_overflow catches the int64 overflow → escape to GMP, which
 * preserves exact bignum semantics; kint() then re-tags any in-61-bit result as
 * an immediate and boxes anything larger (canonical reduction). */
KValue *kp_addInt(KValue *x, KValue *y) {
  int64_t r;
  if (kis_int_word(x) && kis_int_word(y) &&
      !__builtin_add_overflow(kint_word(x), kint_word(y), &r))
    return kint(r);
  return kint_binop_mpz(x, y, mpz_add);
}
KValue *kp_subInt(KValue *x, KValue *y) {
  int64_t r;
  if (kis_int_word(x) && kis_int_word(y) &&
      !__builtin_sub_overflow(kint_word(x), kint_word(y), &r))
    return kint(r);
  return kint_binop_mpz(x, y, mpz_sub);
}
KValue *kp_mulInt(KValue *x, KValue *y) {
  int64_t r;
  if (kis_int_word(x) && kis_int_word(y) &&
      !__builtin_mul_overflow(kint_word(x), kint_word(y), &r))
    return kint(r);
  return kint_binop_mpz(x, y, mpz_mul);
}
KValue *kp_divInt(KValue *x, KValue *y) {
  if (kint_is_zero(y)) krt_fail("divInt: division by zero");
  if (kis_int_word(x) && kis_int_word(y)) {
    int64_t ix = kint_word(x), iy = kint_word(y);
    if (!(ix == INT64_MIN && iy == -1))
      return kint(ix / iy); /* C99 trunc toward zero == quot */
  }
  return kint_binop_mpz(x, y, mpz_tdiv_q); /* truncated quotient */
}
KValue *kp_modInt(KValue *x, KValue *y) {
  if (kint_is_zero(y)) krt_fail("modInt: division by zero");
  if (kis_int_word(x) && kis_int_word(y)) {
    int64_t ix = kint_word(x), iy = kint_word(y);
    if (ix == INT64_MIN && iy == -1) return kint(0);
    return kint(ix % iy); /* C99 % == rem */
  }
  return kint_binop_mpz(x, y, mpz_tdiv_r); /* remainder, sign of dividend */
}
KValue *kp_negInt(KValue *x) {
  if (kis_int_word(x)) {
    int64_t ix = kint_word(x);
    if (ix != INT64_MIN) return kint(-ix);
  }
  mpz_t z, zr;
  mpz_init(z); mpz_init(zr);
  kload_mpz(x, z); mpz_neg(zr, z);
  KValue *res = kfrom_mpz(zr);
  mpz_clear(z); mpz_clear(zr);
  return res;
}
/* §18.1.6 Duration/Instant + their construction/arithmetic/compare are the
 * std.time prelude fragment (ordinary Kappa over Integer) — no runtime helpers. */
KValue *kp_eqInt(KValue *x, KValue *y) { return kbool(kint_cmp(x, y) == 0); }
KValue *kp_ltInt(KValue *x, KValue *y) { return kbool(kint_cmp(x, y) < 0); }
KValue *kp_leInt(KValue *x, KValue *y) { return kbool(kint_cmp(x, y) <= 0); }
/* Convert a (possibly huge) integer magnitude to a double with IEEE
 * round-to-NEAREST-EVEN, matching Haskell `fromInteger :: Integer -> Double`.
 * GMP's `mpz_get_d` rounds TOWARD ZERO, which is wrong for values whose nearest
 * double rounds up (off by up to a ULP, e.g. 2^60+129 -> 2^60+256).  We extract
 * the top 53 significant bits + a round bit + a sticky bit and round ties-to-
 * even, then scale by 2^(bitlen-53).  `z` is treated as a nonnegative magnitude;
 * the caller applies the sign. */
static double mpz_to_double_rne(mpz_srcptr z) {
  if (mpz_sgn(z) == 0) return 0.0;
  size_t bits = mpz_sizeinbase(z, 2);          /* exact bit length of |z| */
  if (bits <= 53) return mpz_get_d(z);         /* exact: no rounding needed */
  /* mantissa = top 53 bits; let shift = bits-53 be the dropped low bits. */
  unsigned long shift = (unsigned long)(bits - 53);
  mpz_t hi, lo, halfbit; mpz_inits(hi, lo, halfbit, (mpz_ptr)0);
  mpz_fdiv_q_2exp(hi, z, shift);               /* hi = z >> shift  (53 bits) */
  mpz_fdiv_r_2exp(lo, z, shift);               /* lo = z mod 2^shift (dropped) */
  uint64_t mant = mpz_get_ui(hi);              /* fits 53 bits, < 2^64 */
  /* round bit = bit (shift-1) of z; sticky = any lower bit set. */
  mpz_setbit(halfbit, shift - 1);              /* halfbit = 2^(shift-1) */
  int cmp = mpz_cmp(lo, halfbit);              /* lo vs the halfway point */
  int round_up;
  if (cmp < 0)       round_up = 0;             /* below halfway: round down */
  else if (cmp > 0)  round_up = 1;             /* above halfway: round up */
  else               round_up = (int)(mant & 1);   /* exact tie: to even */
  mant += (uint64_t)round_up;
  /* a carry out of 53 bits (mant == 2^53) renormalizes: drop one more low bit. */
  if (mant == (1ULL << 53)) { mant >>= 1; shift += 1; }
  mpz_clears(hi, lo, halfbit, (mpz_ptr)0);
  return ldexp((double)mant, (int)shift);      /* mant * 2^shift, exact */
}

KValue *kp_intToDouble(KValue *x) {
  if (kis_int_word(x)) return kdbl((double)kint_word(x));
  if (!kis_imm(x) && x->tag == K_BIGINT) {
    mpz_srcptr z = (mpz_srcptr)x->as.big.mpz;
    int neg = mpz_sgn(z) < 0;
    double mag;
    if (neg) {
      mpz_t a; mpz_init(a); mpz_neg(a, z);
      mag = mpz_to_double_rne(a); mpz_clear(a);
    } else {
      mag = mpz_to_double_rne(z);
    }
    return kdbl(neg ? -mag : mag);
  }
  krt_fail("intToDouble: not an Int");
}
KValue *kp_intAnd(KValue *x, KValue *y) {
  if (kis_int_word(x) && kis_int_word(y)) return kint(kint_word(x) & kint_word(y));
  mpz_t a, b, r; mpz_init(a); mpz_init(b); mpz_init(r); kload_mpz(x, a); kload_mpz(y, b);
  mpz_and(r, a, b); KValue *res = kfrom_mpz(r); mpz_clear(a); mpz_clear(b); mpz_clear(r); return res;
}
KValue *kp_intOr(KValue *x, KValue *y) {
  if (kis_int_word(x) && kis_int_word(y)) return kint(kint_word(x) | kint_word(y));
  mpz_t a, b, r; mpz_init(a); mpz_init(b); mpz_init(r); kload_mpz(x, a); kload_mpz(y, b);
  mpz_ior(r, a, b); KValue *res = kfrom_mpz(r); mpz_clear(a); mpz_clear(b); mpz_clear(r); return res;
}
KValue *kp_intXor(KValue *x, KValue *y) {
  if (kis_int_word(x) && kis_int_word(y)) return kint(kint_word(x) ^ kint_word(y));
  mpz_t a, b, r; mpz_init(a); mpz_init(b); mpz_init(r); kload_mpz(x, a); kload_mpz(y, b);
  mpz_xor(r, a, b); KValue *res = kfrom_mpz(r); mpz_clear(a); mpz_clear(b); mpz_clear(r); return res;
}
