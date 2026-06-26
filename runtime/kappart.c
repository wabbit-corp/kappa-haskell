/* kappart.c — Kappa native runtime implementation.  See kappart.h and
 * docs/NATIVE_BACKEND.md.  The primitive set implemented here is kept in
 * lock-step with the supported-primitive table in Kappa.Backend.C: the
 * code generator refuses (E_BACKEND_UNSUPPORTED) any primitive this file
 * does not implement, so an unimplemented primitive is a compile-time
 * error, never a silent runtime divergence. */
#include "kappart.h"
#include "kappa_ucd.h" /* §29.4 Unicode tables (generated; see tools/gen-ucd-c.py) */

#include <gc.h>
#include <gmp.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ── lifecycle / allocation ────────────────────────────────────────── */

/* Route GMP allocation through the Boehm collector so bignum limbs are
 * GC-managed (free is a no-op; the collector reclaims). */
static void *gmp_gc_alloc(size_t n) { return GC_MALLOC(n); }
static void *gmp_gc_realloc(void *p, size_t old, size_t n) {
  (void)old;
  return GC_REALLOC(p, n);
}
static void gmp_gc_free(void *p, size_t n) { (void)p; (void)n; }

/* QW4: optional allocation/GC report at exit, gated by $KAPPA_GC_STATS, for
 * the native benchmark gates (test/native/bench.sh).  Off unless the env var
 * is set, so normal runs are unaffected. */
static void krt_at_exit(void) {
  if (getenv("KAPPA_GC_STATS")) {
    fprintf(stderr, "[kappa-gc] total_bytes=%zu heap_size=%zu collections=%lu\n",
            (size_t)GC_get_total_bytes(), (size_t)GC_get_heap_size(),
            (unsigned long)GC_get_gc_no());
  }
}

/* UNBOXING Stage 0 (§5.4): the immediate-tagging scheme requires GC_MALLOC (and
 * thus gmp_gc_alloc, the same allocator) to return >= 8-byte-aligned pointers so
 * the low 3 bits of a KValue* word are always free.  Verify at startup, failing
 * closed, rather than silently miscompiling on a hypothetical under-aligned
 * platform.  (Boehm returns >= 16-byte-aligned objects on 64-bit targets.) */
static void krt_assert_gc_alignment(void) {
  for (size_t n = 8; n < 8 + 16; n++) {
    void *p = GC_MALLOC(n);
    if (((uintptr_t)p & 0x7u) != 0)
      krt_fail("UNBOXING: GC_MALLOC returned a non-8-aligned pointer (tag-bit contract violated)");
  }
}

void krt_init(void) {
  /* UNBOXING Stage 0 (§5.4): turn OFF interior-pointer recognition BEFORE
   * GC_INIT, so the collector roots only BASE pointers.  The (future) immediate
   * tagging packs small values into the low 3 bits of a KValue* word; a tagged
   * immediate must not be mistaken for a (possibly interior) heap pointer and
   * falsely retain an object.  The runtime only ever holds base KValue and array
   * pointers (never an interior pointer as the sole reference to an object), so
   * base-only rooting is safe — verified by the native suite + parity corpus. */
  GC_set_all_interior_pointers(0);
  GC_INIT();
  krt_assert_gc_alignment();
  mp_set_memory_functions(gmp_gc_alloc, gmp_gc_realloc, gmp_gc_free);
  atexit(krt_at_exit);
}

void *kgc_alloc(size_t n) {
  void *p = GC_MALLOC(n);
  if (!p) krt_fail("out of memory (GC_MALLOC)");
  return p;
}

void *kgc_alloc_atomic(size_t n) {
  void *p = GC_MALLOC_ATOMIC(n);
  if (!p) krt_fail("out of memory (GC_MALLOC_ATOMIC)");
  return p;
}

void krt_fail(const char *msg) {
  fflush(stdout);
  fprintf(stderr, "kappa: runtime failure: %s\n", msg);
  exit(1);
}

static KValue *alloc_val(KTag tag) {
  KValue *v = (KValue *)kgc_alloc(sizeof(KValue));
  v->tag = tag;
  return v;
}

/* A scalar box whose payload is pointer-free (K_INT / K_DBL / K_CHR / K_BYTE):
 * allocate it on the atomic (unscanned) heap so the collector skips it during
 * mark — its bytes hold no pointers (R2.1 / gap P1-F).  The win is reduced
 * per-collection mark work proportional to the number of such boxes live
 * across a collection, plus removing them as conservative-GC false-pointer
 * sources; it shows up as cheaper collections, not a smaller heap.  It is
 * material for Double/Char/Byte boxes and for out-of-cache integers
 * (`kdbl`/`kchr`/`kbyte` and large `kint`s); small integers in [-16,256] are
 * served from the shared `kint_cache` and allocate nothing per step, so they
 * see no win.  Only types whose active union member holds NO pointer may use
 * this: K_STR/K_BYTES carry a buffer pointer and K_BIGINT an mpz pointer, so
 * those stay on the scanned path (alloc_val).  Scalar boxes are immutable and
 * never re-tagged into a pointer-bearing value, so the unscanned
 * classification is permanent and sound.  GC_MALLOC_ATOMIC does not zero the
 * block, but every scalar constructor sets `tag` plus its one active member
 * and all readers dispatch on `tag`, so the uninitialised inactive union
 * bytes are never observed. */
static KValue *alloc_val_atomic(KTag tag) {
  KValue *v = (KValue *)kgc_alloc_atomic(sizeof(KValue));
  v->tag = tag;
  return v;
}

/* ── value constructors ────────────────────────────────────────────── */

/* Forward declarations for the bignum helpers kint() escapes to (defined just
 * below in the §6 GMP block) — kint() must precede them to be the canonical Int
 * constructor every other helper calls. */
static void kmpz_set_i64(mpz_t out, int64_t v);
static KValue *kbig_from_mpz(const mpz_t z);

/* UNBOXING Stage 1 (§5.2 / research rec 2): an in-range Int is a CANONICAL b001
 * immediate packed into the KValue* word — no heap box, no allocation, no shared
 * singleton.  This RETIRES the old kint_cache[-16..256] carrier: a small Int is
 * now ALWAYS the immediate (never a boxed K_INT), so pointer identity can never
 * see two encodings of one value.  A value outside the 61-bit immediate range
 * escapes to the boxed K_BIGINT (GMP) path — the same place a >int64 literal
 * already lived — so nothing in [2^60, 2^63) survives as an inline K_INT box,
 * keeping the §5.3 inline/bignum boundary normalized through kfrom_mpz/kint_cmp.
 * (The boxed K_INT carrier is no longer produced by the runtime at all; it
 * remains a valid representation that readers still accept, for forward
 * compatibility with any path that builds one explicitly.) */
KValue *kint(int64_t v) {
  if (kint_fits_imm(v)) return kmk_imm_int(v);     /* canonical immediate */
  /* out of the 61-bit immediate range → boxed bignum, exactly as a literal
   * beyond int64 would be (kfrom_mpz canonicalises a fits-int64 result back to
   * the immediate, but a >2^60 magnitude stays a K_BIGINT). */
  mpz_t z; mpz_init(z); kmpz_set_i64(z, v);
  KValue *r = kbig_from_mpz(z); mpz_clear(z);
  return r;
}

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

static int kmpz_fits_i64_p(const mpz_t z) {
  mpz_t lo, hi;
  mpz_inits(lo, hi, NULL);
  kmpz_i64_bounds(lo, hi);
  int ok = mpz_cmp(z, lo) >= 0 && mpz_cmp(z, hi) <= 0;
  mpz_clears(lo, hi, NULL);
  return ok;
}

static int64_t kmpz_get_i64(const mpz_t z) {
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

static void kmpz_set_i64(mpz_t out, int64_t v) {
  uint64_t mag;
  int neg = v < 0;
  if (v == INT64_MIN) mag = ((uint64_t)1 << 63);
  else if (neg) mag = (uint64_t)(-v);
  else mag = (uint64_t)v;
  mpz_import(out, 1, -1, sizeof(uint64_t), 0, 0, &mag);
  if (neg) mpz_neg(out, out);
}

static KValue *kbig_from_mpz(const mpz_t z) {
  KValue *r = alloc_val(K_BIGINT);
  __mpz_struct *p = (__mpz_struct *)kgc_alloc(sizeof(__mpz_struct));
  mpz_init_set(p, z);
  r->as.big.mpz = p;
  return r;
}

/* Demote to K_INT when the result fits int64, else keep a K_BIGINT. */
static KValue *kfrom_mpz(const mpz_t z) {
  if (kmpz_fits_i64_p(z)) return kint(kmpz_get_i64(z));
  return kbig_from_mpz(z);
}

/* Load an immediate Int / K_INT / K_BIGINT into an mpz for a bignum operation. */
static void kload_mpz(KValue *v, mpz_t out) {
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

static KValue *krat(mpz_t num, mpz_t den) {
  if (mpz_sgn(den) == 0) krt_fail("Rational: zero denominator");
  if (mpz_sgn(den) < 0) { mpz_neg(num, num); mpz_neg(den, den); }
  mpz_t g; mpz_init(g); mpz_gcd(g, num, den);
  if (mpz_sgn(g) != 0) { mpz_divexact(num, num, g); mpz_divexact(den, den, g); }
  KValue *args[2]; args[0] = kfrom_mpz(num); args[1] = kfrom_mpz(den);
  return kctor(KCT_RAT, "__rat", 2, args);
}

static void as_rat(KValue *r, mpz_t num, mpz_t den) {
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
static KValue *rat_addsub(KValue *x, KValue *y, int sub) {
  mpz_t a, b, c, d, n, t, den; mpz_inits(a, b, c, d, n, t, den, NULL);
  as_rat(x, a, b); as_rat(y, c, d);
  mpz_mul(n, a, d); mpz_mul(t, c, b);
  if (sub) mpz_sub(n, n, t); else mpz_add(n, n, t);
  mpz_mul(den, b, d);
  return krat(n, den);
}

KValue *kdbl(double v) {
  KValue *r = alloc_val_atomic(K_DBL);
  r->as.d = v;
  return r;
}

KValue *kstr(const char *bytes, size_t len) {
  KValue *r = alloc_val(K_STR);
  char *buf = (char *)kgc_alloc_atomic(len + 1);
  if (len) memcpy(buf, bytes, len);
  buf[len] = '\0'; /* convenience for FFI; length is authoritative */
  r->as.str.p = buf;
  r->as.str.len = len;
  return r;
}

KValue *kstr0(const char *cstr) { return kstr(cstr, strlen(cstr)); }

KValue *kchr(uint32_t scalar) {
  KValue *r = alloc_val_atomic(K_CHR);
  r->as.chr = scalar;
  return r;
}

/* UNBOXING Stage 1b (§5.2): Unit is a NULLARY ctor, so it is the CANONICAL b010
 * immediate (tag id KCT_UNIT) — never a boxed K_UNIT singleton.  This RETIRES the
 * old `the_unit` carrier exactly as Stage 1 retired kint_cache: with one
 * representation, pointer identity (`a == b` in kvalue_rep_eq) can never see two
 * encodings of `()`.  The boxed K_UNIT tag remains accepted by readers (kctor_is,
 * kctor_tagid) for forward compatibility, but the runtime never produces one. */
KValue *kunit(void) {
  return kmk_imm_ctor(KCT_UNIT);
}

/* LR2: the builtin tag ids are shared with codegen (which spells them KCT_*);
 * pin every id so a header edit that desyncs them from Kappa.Builtins's
 * `runtimeCtors` (the compiler-side source of truth) fails THIS build, not a
 * pattern match at runtime.  One assert per id, in enum order — keep in lockstep
 * with `runtimeCtors`. */
_Static_assert(KCT_UNIT                 ==  1, "KCT_UNIT must be 1");
_Static_assert(KCT_TRUE                 ==  2, "KCT_TRUE must be 2");
_Static_assert(KCT_FALSE                ==  3, "KCT_FALSE must be 3");
_Static_assert(KCT_CONS                 ==  4, "KCT_CONS must be 4");
_Static_assert(KCT_NIL                  ==  5, "KCT_NIL must be 5");
_Static_assert(KCT_SOME                 ==  6, "KCT_SOME must be 6");
_Static_assert(KCT_NONE                 ==  7, "KCT_NONE must be 7");
_Static_assert(KCT_RAT                  ==  8, "KCT_RAT must be 8");
_Static_assert(KCT_EFFPURE              ==  9, "KCT_EFFPURE must be 9");
_Static_assert(KCT_EFFOP                == 10, "KCT_EFFOP must be 10");
_Static_assert(KCT_SUCCESS              == 11, "KCT_SUCCESS must be 11");
_Static_assert(KCT_FAILURE              == 12, "KCT_FAILURE must be 12");
_Static_assert(KCT_FAIL                 == 13, "KCT_FAIL must be 13");
_Static_assert(KCT_INTERRUPT            == 14, "KCT_INTERRUPT must be 14");
_Static_assert(KCT_DEFECT               == 15, "KCT_DEFECT must be 15");
_Static_assert(KCT_BOTH                 == 16, "KCT_BOTH must be 16");
_Static_assert(KCT_THEN                 == 17, "KCT_THEN must be 17");
_Static_assert(KCT_RO_LEFT              == 18, "KCT_RO_LEFT must be 18");
_Static_assert(KCT_RO_RIGHT             == 19, "KCT_RO_RIGHT must be 19");
_Static_assert(KCT_TO_TIMED_OUT         == 20, "KCT_TO_TIMED_OUT must be 20");
_Static_assert(KCT_TO_EXIT              == 21, "KCT_TO_EXIT must be 21");
_Static_assert(KCT_MK_INTERRUPT_CAUSE   == 22, "KCT_MK_INTERRUPT_CAUSE must be 22");
_Static_assert(KCT_IT_REQUESTED         == 23, "KCT_IT_REQUESTED must be 23");
_Static_assert(KCT_IT_SCOPE_SHUTDOWN    == 24, "KCT_IT_SCOPE_SHUTDOWN must be 24");
_Static_assert(KCT_IT_TIMED_OUT         == 25, "KCT_IT_TIMED_OUT must be 25");
_Static_assert(KCT_IT_RACE_LOST         == 26, "KCT_IT_RACE_LOST must be 26");
_Static_assert(KCT_IT_EXTERNAL          == 27, "KCT_IT_EXTERNAL must be 27");
_Static_assert(KCT_USER_BASE            == 40, "KCT_USER_BASE must be 40");
_Static_assert(KCT_USER_BASE > KCT_IT_EXTERNAL,
               "user ctor ids must not collide with the pinned builtin ids");

KValue *kctor(int tagid, const char *name, int argc, KValue **args) {
  /* UNBOXING Stage 1b (§5.1/§5.2): EVERY nullary ctor — of ANY ADT — is the
   * CANONICAL b010 immediate carrying its tag id, alloc-free, with no surviving
   * boxed K_CTOR for a 0-field value.  An n-ary ctor (argc > 0) stays a boxed
   * K_CTOR (its fields need heap storage).  This generalizes the Stage-1 narrow
   * Bool/Unit/Nil/None plan to arbitrary enum variants. */
  if (argc == 0) return kmk_imm_ctor(tagid);
  /* UNBOXING Stage 1d (§5.1/§5.2): a SINGLE-field ctor whose one field is itself
   * an immediate that fits the 41-bit payload packs into a b011 word carrying the
   * tag id AND the field's whole word — alloc-free (Some/Ok/Err over a small
   * Int/enum).  A field that is a heap pointer or a too-big immediate falls back
   * to the boxed K_CTOR below.  The tag id must ALSO fit the 20-bit discriminant
   * (kctor_tagid_packs) — the kappart2 OP action nodes at KRT2_OP_BASE do not,
   * so ioPure(immediate) etc. stay boxed and the CK-machine still sees its id.
   * Per-value packing is canonical: the same field value always lands the same
   * way. */
  if (argc == 1 && kctor_tagid_packs(tagid) && kctor_field_packs(args[0]))
    return kmk_imm_packed(tagid, args[0]);
  /* UNBOXING Stage 1e (§5.1/§5.2): a TWO-field ctor whose BOTH fields are
   * immediates that each fit the 20-bit per-slot budget packs into a b011 word
   * (nfields=1) carrying the tag id AND both fields' whole words — alloc-free
   * (Pair(smallInt,smallInt), a 2-scalar record lowered to a ctor, a 2-enum
   * variant).  If either field is a heap pointer or a too-big immediate the ctor
   * boxes below.  Same tagId gate as the single-field path keeps the kappart2 OP
   * nodes (KRT2_OP_BASE) boxed.  Per-value packing is canonical. */
  if (argc == 2 && kctor_tagid_packs(tagid)
      && kctor_field2_packs(args[0]) && kctor_field2_packs(args[1]))
    return kmk_imm_packed2(tagid, args[0], args[1]);
  KValue *r = alloc_val(K_CTOR);
  r->as.ctor.name = name;
  r->as.ctor.tagid = tagid;   /* LR2 numeric identity for matching */
  r->as.ctor.argc = argc;
  KValue **a = (KValue **)kgc_alloc(sizeof(KValue *) * (size_t)argc);
  for (int i = 0; i < argc; i++) a[i] = args[i];
  r->as.ctor.args = a;
  return r;
}

KValue *kctor0(int tagid, const char *name) {
  /* Every nullary ctor is the canonical b010 immediate (§5.2).  `name` is unused
   * now (the immediate carries only the tag id); kept in the signature for the
   * codegen call shape and diagnostic parity with kctor. */
  (void)name;
  return kmk_imm_ctor(tagid);
}

/* The two Bool constructors are nullary, so True/False are canonical b010
 * immediates (KCT_TRUE/KCT_FALSE) — alloc-free, one representation each, never a
 * boxed singleton (§5.2).  This RETIRES the old `the_true`/`the_false` carriers. */
KValue *kbool(int b) {
  return kmk_imm_ctor(b ? KCT_TRUE : KCT_FALSE);
}

KValue *krec(int n, const char **names, KValue **vals) {
  KValue *r = alloc_val(K_REC);
  r->as.rec.n = n;
  r->as.rec.names = names; /* names array is a generated static literal */
  if (n) {
    KValue **v = (KValue **)kgc_alloc(sizeof(KValue *) * (size_t)n);
    for (int i = 0; i < n; i++) v[i] = vals[i];
    r->as.rec.vals = v;
  } else {
    r->as.rec.vals = NULL;
  }
  return r;
}

KValue *kclo(KFn fn, KEnv *env) {
  KValue *r = alloc_val(K_CLO);
  r->as.clo.fn = fn;
  r->as.clo.env = env;
  return r;
}

KValue *kio(KIOFn fn, KEnv *env) {
  KValue *r = alloc_val(K_IO);
  r->as.io.fn = fn;
  r->as.io.env = env;
  return r;
}

KValue *kfail(KValue *err) {
  KValue *r = alloc_val(K_FAIL);
  r->as.fail.err = err;
  return r;
}

int kis_fail(KValue *v) { return v && !kis_imm(v) && v->tag == K_FAIL; }

KValue *kref_new(KValue *init) {
  KValue *r = alloc_val(K_REF);
  KValue **cell = (KValue **)kgc_alloc(sizeof(KValue *));
  cell[0] = init;
  r->as.ref.cell = cell;
  return r;
}

KValue *kfgn(void *p, const char *kind) {
  KValue *r = alloc_val(K_FGN);
  r->as.fgn.p = p;
  r->as.fgn.kind = kind;
  return r;
}

/* A curried direct-call action (argc=0): the codegen-emitted function
 * pointer for a builtin primitive (§34.5.3) or a native host-binding symbol
 * (§27.1.1).  Accumulates args via kapp.  `is_io` distinguishes a pure
 * builtin (fires its fn immediately on saturation) from an effectful action
 * (a saturated value is the suspended IO action that krun_io fires). */
KValue *knative(KNativeFn fn, int arity, const char *kind, int is_io) {
  KValue *r = alloc_val(K_NATIVE);
  r->as.native.fn = fn;
  r->as.native.arity = arity;
  r->as.native.argc = 0;
  r->as.native.args = NULL;
  r->as.native.kind = kind;
  r->as.native.is_io = is_io;
  return r;
}

/* The saturated fast path: build a K_NATIVE holding all `arity` args at once
 * (copied into GC memory so it outlives the caller's argument array).  For an
 * effectful action this is the suspended IO action krun_io fires; codegen
 * emits this only for IO builtins / native symbols. */
KValue *knative_sat(KNativeFn fn, int arity, KValue **args, int is_io) {
  KValue *r = alloc_val(K_NATIVE);
  r->as.native.fn = fn;
  r->as.native.arity = arity;
  r->as.native.argc = arity;
  KValue **a = (KValue **)kgc_alloc(sizeof(KValue *) * (size_t)(arity > 0 ? arity : 1));
  for (int i = 0; i < arity; i++) a[i] = args[i];
  r->as.native.args = a;
  r->as.native.kind = "native";
  r->as.native.is_io = is_io;
  return r;
}

/* §34.5.3 IO builtin direct entry points (codegen calls these via K_NATIVE,
 * never by name).  The pure builtins are the kp_ and kpf_ helpers below; these
 * kpf_io_ entries are the effectful ones the do-kernel sequences. */
KValue *kpf_io_printString(KValue **a) {
  if (a[0]->tag != K_STR) krt_fail("printString: argument is not a String");
  fwrite(a[0]->as.str.p, 1, a[0]->as.str.len, stdout);
  return kunit();
}
KValue *kpf_io_printlnString(KValue **a) {
  if (a[0]->tag != K_STR) krt_fail("printlnString: argument is not a String");
  fwrite(a[0]->as.str.p, 1, a[0]->as.str.len, stdout);
  fputc('\n', stdout);
  return kunit();
}
KValue *kpf_io_ioPure(KValue **a) { return a[0]; }
KValue *kpf_io_ioBind(KValue **a) {
  KValue *r = krun_io(a[0]);
  if (kis_fail(r)) return r;
  return krun_io(kapp(a[1], r));
}
KValue *kpf_io_ioThen(KValue **a) {
  KValue *r = krun_io(a[0]);
  if (kis_fail(r)) return r;
  return krun_io(a[1]);
}
KValue *kpf_io_throwIO(KValue **a) { return kfail(a[0]); }
KValue *kpf_io_catchIO(KValue **a) {
  KValue *r = krun_io(a[0]);
  if (kis_fail(r)) return krun_io(kapp(a[1], r->as.fail.err));
  return r;
}
KValue *kpf_io_finallyIO(KValue **a) {
  KValue *r = krun_io(a[0]);
  KValue *fr = krun_io(a[1]);
  if (kis_fail(r)) return r;
  if (kis_fail(fr)) return fr;
  return r;
}
KValue *kpf_io_newRef(KValue **a) { return kref_new(a[0]); }
KValue *kpf_io_readRef(KValue **a) { return kref_get(a[0]); }
KValue *kpf_io_writeRef(KValue **a) { return kref_set(a[0], a[1]); }

/* §18.1.13 STM, single-agent semantics — matching the reference interpreter
 * (Kappa.Interp.stmAtomically, which runs an STM action through the very same
 * IO runner): a TVar is a mutable cell and `atomically` runs the transaction
 * directly.  A transaction that never `retry`s commits in one pass, which is
 * everything expressible without a concurrent writer.  Real multi-fiber STM —
 * journaled reads, optimistic commit, retry-parking — lives in the kappart2
 * scheduler (stm.c) and is reached once the do-kernel is CPS-lowered so a
 * transaction can suspend a fiber. */
KValue *kpf_io_newTVar(KValue **a) { return kref_new(a[0]); }
KValue *kpf_io_readTVar(KValue **a) { return kref_get(a[0]); }
KValue *kpf_io_writeTVar(KValue **a) { return kref_set(a[0], a[1]); }
KValue *kpf_io_atomically(KValue **a) { return krun_io(a[0]); }
KValue *kpf_io_retry(KValue **a) {
  (void)a;
  /* Single-agent: there is no concurrent writer to advance a read TVar, so a
   * blocked transaction can never make progress.  Fail loudly rather than
   * livelock; blocking retry needs the concurrent scheduler. */
  krt_fail("STM retry: the single-agent native runtime has no concurrent writer "
           "to wake a blocked transaction (needs the kappart2 scheduler)");
}
KValue *kpf_io_check(KValue **a) {
  /* check b = if b then pure () else retry (§18.1.13). */
  return kas_bool(a[0]) ? kunit() : kpf_io_retry(a);
}

/* ── §18.1 algebraic-effect runtime ───────────────────────────────────
 * Mirrors Kappa.Eval.evalEffPrim over the untyped OpCall tree
 * (`__EffPure v` / `__EffOp label op payload cont`).  Labels are string
 * tokens (the label global's name); the handler `ops` is a record keyed by
 * operation name.  Continuations are GC closures built with kclo/kpush. */
KValue *kpf___effBind(KValue **a);
KValue *kpf___handleEff(KValue **a);
KValue *kpf___absurd(KValue **a);

static KValue *eff_bind_k(KEnv *env, KValue *x) {
  /* env: kvar0 = f, kvar1 = cont.  \x -> __effBind (cont x) f */
  KValue *f = kvar(env, 0), *cont = kvar(env, 1);
  KValue *args[2]; args[0] = kapp(cont, x); args[1] = f;
  return kpf___effBind(args);
}

/* §12.4.3 first-class borrowed views. A borrow carries no runtime
 * witness (it IS its value), so captureBorrow reifies the view as the
 * value itself and withBorrowView eliminates it by reinstating the
 * borrowed binder (applying the continuation to the viewed value). */
KValue *kpf_captureBorrow(KValue **a) { return a[0]; }
KValue *kpf_withBorrowView(KValue **a) { return kapp(a[1], a[0]); }

/* runPure : Eff <[]> a -> a  (§18.1.14) */
KValue *kpf_runPure(KValue **a) {
  if (kctor_tagid(a[0]) == KCT_EFFPURE) return kctor_arg(a[0], 0);
  krt_fail("runPure: computation is not fully handled (an operation escaped its handlers)");
  return 0;
}

KValue *kpf___absurd(KValue **a) {
  (void)a;
  krt_fail("__absurd: attempted to eliminate a Void value");
  return 0;
}

/* __effBind m f : monadic bind over the Eff tree (§18.1.14) */
KValue *kpf___effBind(KValue **a) {
  KValue *m = a[0], *f = a[1];
  int t = kctor_tagid(m);
  if (t == KCT_EFFPURE) return kapp(f, kctor_arg(m, 0));
  if (t == KCT_EFFOP) {
    KEnv *env = kpush(f, kpush(kctor_arg(m, 3), 0)); /* kvar0=f, kvar1=cont */
    KValue *args[4];
    args[0] = kctor_arg(m, 0); args[1] = kctor_arg(m, 1); args[2] = kctor_arg(m, 2);
    args[3] = kclo(eff_bind_k, env);
    return kctor(KCT_EFFOP, "__EffOp", 4, args);
  }
  krt_fail("__effBind: not an Eff value");
  return 0;
}

/* env for the deep/propagate resumption: kvar0=cont,1=ops,2=ret,3=label,4=deep */
static KValue *eff_reinstall_k(KEnv *env, KValue *x) {
  KValue *cont = kvar(env, 0), *ops = kvar(env, 1), *ret = kvar(env, 2),
         *label = kvar(env, 3), *deepV = kvar(env, 4);
  KValue *args[5];
  args[0] = deepV; args[1] = label; args[2] = ret; args[3] = ops;
  args[4] = kapp(cont, x);
  return kpf___handleEff(args);
}
static int eff_label_eq(KValue *x, KValue *y) {
  return x->tag == K_STR && y->tag == K_STR && x->as.str.len == y->as.str.len &&
         memcmp(x->as.str.p, y->as.str.p, x->as.str.len) == 0;
}

/* __handleEff deep label ret ops comp  (§18.1.21/.22) */
KValue *kpf___handleEff(KValue **a) {
  KValue *deepV = a[0], *label = a[1], *ret = a[2], *ops = a[3], *comp = a[4];
  int t = kctor_tagid(comp);
  if (t == KCT_EFFPURE) return kapp(ret, kctor_arg(comp, 0));
  if (t == KCT_EFFOP) {
    KValue *l = kctor_arg(comp, 0), *op = kctor_arg(comp, 1),
           *pay = kctor_arg(comp, 2), *cont = kctor_arg(comp, 3);
    KEnv *renv = kpush(cont, kpush(ops, kpush(ret, kpush(label, kpush(deepV, 0)))));
    if (eff_label_eq(l, label)) {
      KValue *clause = kproj(ops, op->as.str.p); /* op is a null-terminated KString */
      KValue *k = (kctor_tagid(deepV) == KCT_TRUE) ? kclo(eff_reinstall_k, renv) : cont;
      return kapp(kapp(clause, pay), k);
    } else {
      KValue *args[4];
      args[0] = l; args[1] = op; args[2] = pay; args[3] = kclo(eff_reinstall_k, renv);
      return kctor(KCT_EFFOP, "__EffOp", 4, args);
    }
  }
  krt_fail("__handleEff: not an Eff value");
  return 0;
}

KValue *kinject(int tagid, const char *tag, KValue *payload) {
  KValue *r = alloc_val(K_VARIANT);
  r->as.var.tag = tag;          /* a generated static string literal */
  r->as.var.tagid = tagid;      /* LR2 numeric identity for matching */
  r->as.var.payload = payload;
  return r;
}

KValue *kthunk(KIOFn fn, KEnv *env, int memo) {
  KValue *r = alloc_val(K_THUNK);
  r->as.thunk.fn = fn;
  r->as.thunk.env = env;
  r->as.thunk.memo = memo;
  r->as.thunk.cache = NULL;
  return r;
}

KValue *kbyte(unsigned char w) {
  KValue *r = alloc_val_atomic(K_BYTE);
  r->as.byte = w;
  return r;
}

KValue *kbytes(const unsigned char *p, size_t len) {
  KValue *r = alloc_val(K_BYTES);
  unsigned char *buf = (unsigned char *)kgc_alloc_atomic(len ? len : 1);
  if (len) memcpy(buf, p, len);
  r->as.bytes.p = buf;
  r->as.bytes.len = len;
  return r;
}

/* lists */
KValue *knil(void) { return kctor0(KCT_NIL, "std.prelude.Nil"); }
KValue *kcons(KValue *h, KValue *t) {
  KValue *args[2] = {h, t};
  return kctor(KCT_CONS, "std.prelude.::", 2, args);
}
/* Cons (`x :: xs`) is a 2-field ctor.  When both fields are small immediates —
 * e.g. `[smallInt]` = Cons(smallInt, Nil), whose tail Nil is a b010 immediate —
 * it is now a b011 packed word (Stage 1e), so identify it by tag id rather than a
 * raw deref; kctor_tagid handles the packed (b011), nullary (b010) and boxed
 * forms.  A non-ctor immediate (an Int / Nil) reports -1 ≠ KCT_CONS, so the test
 * still rejects them. */
int kis_cons(KValue *v) { return kctor_tagid(v) == KCT_CONS; }

/* ── environment ───────────────────────────────────────────────────── */

KEnv *kpush(KValue *v, KEnv *e) {
  KEnv *n = (KEnv *)kgc_alloc(sizeof(KEnv));
  n->val = v;
  n->next = e;
  return n;
}

KValue *kvar(KEnv *e, int ix) {
  while (ix-- > 0) {
    if (!e) krt_fail("kvar: de Bruijn index out of range");
    e = e->next;
  }
  if (!e) krt_fail("kvar: de Bruijn index out of range");
  return e->val;
}

/* Backpatch a pushed env slot's value (the CLetRec fixpoint, §5): the LLVM
 * backend pushes a placeholder slot, compiles the rhs capturing that slot,
 * then writes the real rhs value back into it.  The C backend writes the
 * struct field directly; the LLVM backend uses opaque ptr and needs this. */
void kenv_set_val(KEnv *e, KValue *v) { e->val = v; }

/* ── native-action firing ─────────────────────────────────────────── */

/* §27.1.1: accumulate one argument onto a curried native action. */
static KValue *native_append_arg(KValue *f, KValue *x) {
  int n = f->as.native.argc;
  KValue *r = alloc_val(K_NATIVE);
  r->as.native.fn = f->as.native.fn;
  r->as.native.arity = f->as.native.arity;
  r->as.native.argc = n + 1;
  r->as.native.kind = f->as.native.kind;
  r->as.native.is_io = f->as.native.is_io;
  KValue **a = (KValue **)kgc_alloc(sizeof(KValue *) * (size_t)(n + 1));
  for (int i = 0; i < n; i++) a[i] = f->as.native.args[i];
  a[n] = x;
  r->as.native.args = a;
  return r;
}

/* Apply once, without draining tail-call bounces. A closure body may
 * return a K_BOUNCE describing a tail call it deferred (§27.5A.3 stack-safe
 * lowering); the caller drives it via ktrampoline. */
static KValue *kapply_once(KValue *f, KValue *x) {
  if (kis_imm(f)) krt_fail("kapp: applying a non-function value");
  switch (f->tag) {
    case K_CLO:
      return f->as.clo.fn(f->as.clo.env, x);
    case K_NATIVE: {
      /* §34.5.3/§27.1.1: a direct-call action.  On saturation a PURE builtin
       * fires its fn immediately (the value is its result); an effectful
       * action stays suspended (a UIO value that krun_io fires later). */
      KValue *r = native_append_arg(f, x);
      if (r->as.native.argc >= r->as.native.arity && !r->as.native.is_io)
        return r->as.native.fn(r->as.native.args);
      return r;
    }
    default:
      krt_fail("kapp: applying a non-function value");
  }
}

/* Drive a tail-call trampoline: repeatedly perform a deferred application
 * in a single C frame until a non-bounce value results.  This bounds the C
 * stack for mutual recursion, calls through a function value, and local
 * let-rec tail recursion (direct self-recursion already loops in-worker). */
KValue *ktrampoline(KValue *r) {
  while (!kis_imm(r) && r->tag == K_BOUNCE) {   /* an immediate value is never a bounce */
    KValue *fn = r->as.bounce.fn;
    KValue *arg = r->as.bounce.arg;
    r = kapply_once(fn, arg);
  }
  return r; /* a K_IOTAIL/K_IOEFFECT passes through untouched; only krun_io drives it */
}

KValue *kbounce(KValue *fn, KValue *arg) {
  KValue *r = alloc_val(K_BOUNCE);
  r->as.bounce.fn = fn;
  r->as.bounce.arg = arg;
  return r;
}

/* Mark `action` as a do-block's tail IO action: krun_io runs it in its own
 * loop rather than letting the do-block body re-enter krun_io, so IO tail
 * recursion (the `do { …; loop n }` idiom) runs in constant C stack. */
KValue *kio_tail(KValue *action) {
  KValue *r = alloc_val(K_IOTAIL);
  r->as.bounce.fn = action;
  return r;
}

/* Like kio_tail, but the enclosing scope discards the result (the branch of
 * a do-block statement-`if`, §18.8): krun_io runs the action in its loop and
 * then yields Unit, matching the interpreter (KIf completes CplNormal _). */
KValue *kio_effect(KValue *action) {
  KValue *r = alloc_val(K_IOEFFECT);
  r->as.bounce.fn = action;
  return r;
}

/* A do-block tail IO action that, once it completes, must run `n` §18.7
 * deferred actions (LIFO).  krun_io stacks these finalizers on the heap as
 * it descends a tail recursion, so the recursion is C-stack-bounded while
 * the finalizer obligations accumulate on the heap (as in the interpreter
 * exit list) rather than on the C stack. */
KValue *kio_finally(KValue *action, KValue **defers, int n) {
  KValue *r = alloc_val(K_IOFINALLY);
  r->as.iofin.action = action;
  r->as.iofin.defers = defers;
  r->as.iofin.n = n;
  return r;
}

KValue *kapp(KValue *f, KValue *x) { return ktrampoline(kapply_once(f, x)); }

KValue *kappi(KValue *f, KValue *x) {
  if (kis_imm(f)) return f;   /* implicit arg erased onto an immediate value */
  switch (f->tag) {
    /* implicit args are erased at runtime for constructors and primitives
     * (§31.2); an implicit lambda is a real binder and is applied. */
    case K_CTOR:
    case K_NATIVE:
      return f;
    case K_CLO:
      return ktrampoline(f->as.clo.fn(f->as.clo.env, x));
    default:
      krt_fail("kappi: applying a non-function value");
  }
}

/* ── deconstruction ────────────────────────────────────────────────── */

/* Stage 1b/1d: an IMMEDIATE builtin ctor (a b010 nullary, or a b011 packed
 * single-field whose field was an immediate) carries ONLY its tag id, not the
 * diagnostic `name` it was built with.  Resolve that name back to the KCT id so
 * kctor_is — a name-based identity test still used by the runtime (race/scope
 * outcome classification, krt2_exit_is_success) and the C harnesses — keeps
 * working on the immediate form.  These are exactly the names the runtime passes
 * to kctor0()/kctor(...) (the diagnostic short form AND the std.prelude.*
 * spelling).  Includes the single-field builtins (Some / Success / Failure /
 * Interrupt) because their field can be a packing immediate (e.g.
 * Some(smallInt), Success(smallInt)) and so reach kctor_is as a b011 word; an
 * n-ary builtin field that is a heap pointer is boxed and dispatched by id.
 * -1 means "not a known builtin name" (a user ctor: dispatch is by id). */
static int kbuiltin_ctor_id(const char *name) {
  if (strcmp(name, "std.prelude.Unit")  == 0) return KCT_UNIT;
  if (strcmp(name, "std.prelude.True")  == 0) return KCT_TRUE;
  if (strcmp(name, "std.prelude.False") == 0) return KCT_FALSE;
  if (strcmp(name, "std.prelude.Nil")   == 0) return KCT_NIL;
  if (strcmp(name, "std.prelude.None")  == 0 || strcmp(name, "None") == 0) return KCT_NONE;
  if (strcmp(name, "std.prelude.Some")  == 0 || strcmp(name, "Some") == 0) return KCT_SOME;
  /* §18.1 single-field Exit/Cause builtins that can wrap a packing immediate. */
  if (strcmp(name, "Success")   == 0) return KCT_SUCCESS;
  if (strcmp(name, "Failure")   == 0) return KCT_FAILURE;
  if (strcmp(name, "Interrupt") == 0) return KCT_INTERRUPT;
  /* §18.1 single-field race / timeout OUTCOMES that wrap an Exit.  When the Exit
   * is itself a Success(smallInt) it packs (b011), so the OUTCOME ctor's field is
   * an immediate and the outcome ALSO packs — name-matching must resolve these. */
  if (strcmp(name, "RaceWonLeft")  == 0) return KCT_RO_LEFT;
  if (strcmp(name, "RaceWonRight") == 0) return KCT_RO_RIGHT;
  if (strcmp(name, "TimeoutDone")  == 0) return KCT_TO_EXIT;
  /* §18.1 race / timeout / interrupt-tag nullary outcomes (built under their
   * diagnostic short names in rt.c/race.c/scope.c). */
  if (strcmp(name, "TimeoutFired")  == 0) return KCT_TO_TIMED_OUT;
  if (strcmp(name, "Requested")     == 0) return KCT_IT_REQUESTED;
  if (strcmp(name, "ScopeShutdown") == 0) return KCT_IT_SCOPE_SHUTDOWN;
  if (strcmp(name, "TimedOut")      == 0) return KCT_IT_TIMED_OUT;
  if (strcmp(name, "RaceLost")      == 0) return KCT_IT_RACE_LOST;
  if (strcmp(name, "External")      == 0) return KCT_IT_EXTERNAL;
  return -1;
}

int kctor_is(KValue *v, const char *name) {
  /* Stage 1b/1d: match an immediate ctor (b010 nullary or b011 packed
   * single-field) by resolving the requested name to its builtin id and
   * comparing against the id carried in the word — no deref.  kctor_tagid is the
   * hot path; this is the name-based reader. */
  if (kis_imm_ctor(v)) {
    int want = kbuiltin_ctor_id(name);
    return want >= 0 && kimm_ctor_id(v) == want;
  }
  if (kis_imm_packed(v)) {
    int want = kbuiltin_ctor_id(name);
    return want >= 0 && kimm_packed_tagid(v) == want;
  }
  if (kis_imm(v)) return 0;   /* an immediate Int is never a constructor */
  /* Unit's boxed spelling is retired as a carrier but still accepted by readers. */
  if (v->tag == K_UNIT) return strcmp(name, "std.prelude.Unit") == 0;
  return v->tag == K_CTOR && strcmp(v->as.ctor.name, name) == 0;
}
/* LR2: the numeric pattern-match dispatch primitive.  A b010 nullary-ctor
 * immediate reports its tag id straight from the word — a deref-free integer
 * compare, the whole point of Stage 1b.  Unit's (retired) boxed spelling still
 * reports KCT_UNIT.  Any non-constructor value reports -1, which equals no valid
 * tag id, so a ctor pattern test on a non-ctor scrutinee fails — preserving the
 * `v->tag == K_CTOR &&` type guard that kctor_is had. */
int kctor_tagid(KValue *v) {
  if (kis_imm_ctor(v)) return kimm_ctor_id(v);   /* Stage 1b: id from the word */
  if (kis_imm_packed(v)) return kimm_packed_tagid(v); /* Stage 1d: id from the word */
  if (kis_imm(v)) return -1;   /* an immediate Int matches no ctor id */
  if (v->tag == K_UNIT) return KCT_UNIT;
  if (v->tag == K_CTOR) return v->as.ctor.tagid;
  return -1;
}
const char *kctor_name(KValue *v) {
  /* An immediate ctor carries no name; this is diagnostic-only, so recover the
   * builtin names and label an unknown user ctor generically. */
  if (kis_imm_ctor(v)) {
    switch (kimm_ctor_id(v)) {
      case KCT_UNIT:  return "std.prelude.Unit";
      case KCT_TRUE:  return "std.prelude.True";
      case KCT_FALSE: return "std.prelude.False";
      case KCT_NIL:   return "std.prelude.Nil";
      case KCT_NONE:  return "std.prelude.None";
      default:        return "<nullary>";
    }
  }
  if (kis_imm_packed(v)) {                            /* Stage 1d: packed single-field */
    switch (kimm_packed_tagid(v)) {
      case KCT_SOME: return "std.prelude.Some";
      default:       return "<packed>";
    }
  }
  if (kis_imm(v) || v->tag != K_CTOR) krt_fail("kctor_name: not a constructor");
  return v->as.ctor.name;
}
int kctor_argc(KValue *v) {
  if (kis_imm_ctor(v)) return 0;        /* Stage 1b: a nullary immediate has 0 args */
  /* Stage 1d/1e: a packed ctor has 1 arg (nfields=0) or 2 args (nfields=1). */
  if (kis_imm_packed(v)) return kimm_packed_is2(v) ? 2 : 1;
  if (kis_imm(v) || v->tag != K_CTOR) krt_fail("kctor_argc: not a constructor");
  return v->as.ctor.argc;
}
KValue *kctor_arg(KValue *v, int i) {
  /* Stage 1d/1e: a b011 packed ctor has its field(s) inline — recovered as the
   * whole immediate word(s) (each a self-describing b001/b010 word).  A two-field
   * (nfields=1) word has fields 0 and 1 in adjacent 20-bit slots; a single-field
   * (nfields=0) word has field 0 in the top 40 bits. */
  if (kis_imm_packed(v)) {
    if (kimm_packed_is2(v)) {
      if (i != 0 && i != 1) krt_fail("kctor_arg: out of range");
      return kimm_packed2_field(v, i);
    }
    if (i != 0) krt_fail("kctor_arg: out of range");
    return kimm_packed_field(v);
  }
  /* A b010 immediate has 0 args, so any index into it is a codegen bug. */
  assert(!kis_imm_ctor(v) && "kctor_arg on a nullary immediate (0 args)");
  if (kis_imm(v) || v->tag != K_CTOR || i < 0 || i >= v->as.ctor.argc)
    krt_fail("kctor_arg: out of range");
  return v->as.ctor.args[i];
}

KValue *kproj(KValue *rec, const char *name) {
  if (kis_imm(rec) || rec->tag != K_REC) {
    char msg[128];
    snprintf(msg, sizeof msg, "kproj: field '%s' on non-record (tag %d)", name,
             kis_imm(rec) ? -1 : (int)rec->tag);
    krt_fail(msg);
  }
  for (int i = 0; i < rec->as.rec.n; i++)
    if (strcmp(rec->as.rec.names[i], name) == 0) return rec->as.rec.vals[i];
  {
    char msg[128];
    snprintf(msg, sizeof msg, "kproj: no such field '%s'", name);
    krt_fail(msg);
  }
}

int kvariant_is(KValue *v, const char *tag) {
  return !kis_imm(v) && v->tag == K_VARIANT && strcmp(v->as.var.tag, tag) == 0;
}
/* LR2: numeric §13 variant dispatch; -1 for a non-variant value (matches no
 * tag id, so a variant pattern test on a non-variant fails). */
int kvariant_tagid(KValue *v) {
  return (!kis_imm(v) && v->tag == K_VARIANT) ? v->as.var.tagid : -1;
}
int kis_variant(KValue *v) { return !kis_imm(v) && v->tag == K_VARIANT; }
KValue *kvariant_payload(KValue *v) {
  if (kis_imm(v) || v->tag != K_VARIANT) krt_fail("kvariant_payload: not a variant");
  return v->as.var.payload;
}

/* §19: force a suspended computation. Delay re-evaluates; Memo caches.
 * A non-thunk value forces to itself (matches the interpreter, which
 * forces through already-evaluated values). */
KValue *kforce(KValue *v) {
  if (kis_imm(v)) return v;   /* an immediate Int is already a value */
  if (v->tag != K_THUNK) return v;
  if (v->as.thunk.memo && v->as.thunk.cache) return v->as.thunk.cache[0];
  KValue *r = v->as.thunk.fn(v->as.thunk.env);
  if (v->as.thunk.memo) {
    KValue **cell = (KValue **)kgc_alloc(sizeof(KValue *));
    cell[0] = r;
    v->as.thunk.cache = cell;
  }
  return r;
}

int krec_size(KValue *rec) {
  if (kis_imm(rec) || rec->tag != K_REC) krt_fail("krec_size: not a record");
  return rec->as.rec.n;
}

/* §17.2.5 record rest binder: a new record of `rec`'s fields whose names
 * are NOT among excl[0..nexcl). Kept field names alias the original
 * record's (static) name pointers, so no copying of label strings. */
KValue *krec_without(KValue *rec, int nexcl, const char **excl) {
  if (kis_imm(rec) || rec->tag != K_REC) krt_fail("krec_without: not a record");
  int n = rec->as.rec.n;
  const char **names = (const char **)kgc_alloc(sizeof(char *) * (size_t)(n ? n : 1));
  KValue **vals = (KValue **)kgc_alloc(sizeof(KValue *) * (size_t)(n ? n : 1));
  int k = 0;
  for (int i = 0; i < n; i++) {
    int excluded = 0;
    for (int j = 0; j < nexcl; j++)
      if (strcmp(rec->as.rec.names[i], excl[j]) == 0) { excluded = 1; break; }
    if (!excluded) { names[k] = rec->as.rec.names[i]; vals[k] = rec->as.rec.vals[i]; k++; }
  }
  KValue *r = alloc_val(K_REC);
  r->as.rec.n = k;
  r->as.rec.names = names;
  r->as.rec.vals = vals;
  return r;
}

KValue *krec_at(KValue *rec, int i) {
  if (kis_imm(rec) || rec->tag != K_REC || i < 0 || i >= rec->as.rec.n)
    krt_fail("krec_at: out of range");
  return rec->as.rec.vals[i];
}

/* Is `v` an Integer in ANY representation — immediate, inline K_INT box, or
 * bignum?  Used to route Int literal-match / equality through a value-
 * normalizing compare across the inline/bignum boundary (§5.3 / research
 * rec 3) rather than klit_eq's tag short-circuit. */
static int kis_int_any(KValue *v) {
  if (kis_imm_int(v)) return 1;
  if (kis_imm(v)) return 0;          /* other immediate kinds: not an Int */
  return v->tag == K_INT || v->tag == K_BIGINT;
}
static int kint_cmp(KValue *a, KValue *b);   /* fwd: normalizing Int compare */

int klit_eq(KValue *a, KValue *b) {
  /* §5.3: an Int in [2^60, 2^63) is an immediate-overflowed K_BIGINT here but
   * an inline K_INT on the interpreter — different tags, same number.  Route any
   * Int/Int pair through the value-normalizing kint_cmp, NEVER the tag shortcut,
   * so equal numbers compare equal across the inline/bignum boundary. */
  if (kis_int_any(a) && kis_int_any(b)) return kint_cmp(a, b) == 0;
  /* The remaining literal kinds (String/Bytes/Char/Byte/Double) have no
   * inline/bignum duality, so the tag short-circuit is exact for them.  An
   * immediate Int reaching here is, by the test above, paired with a non-Int and
   * is unequal — guard the deref so we never read ->tag on an odd word. */
  if (kis_imm(a) || kis_imm(b)) return 0;
  if (a->tag != b->tag) return 0;
  switch (a->tag) {
    case K_INT: return a->as.i == b->as.i;
    case K_BIGINT:
      return mpz_cmp((const __mpz_struct *)a->as.big.mpz,
                     (const __mpz_struct *)b->as.big.mpz) == 0;
    case K_DBL: return a->as.d == b->as.d; /* raw bit-pattern compare in eq prims */
    case K_CHR: return a->as.chr == b->as.chr;
    case K_STR:
      return a->as.str.len == b->as.str.len &&
             memcmp(a->as.str.p, b->as.str.p, a->as.str.len) == 0;
    case K_BYTE: return a->as.byte == b->as.byte;
    case K_BYTES:
      return a->as.bytes.len == b->as.bytes.len &&
             memcmp(a->as.bytes.p, b->as.bytes.p, a->as.bytes.len) == 0;
    default: return 0;
  }
}

/* ── unboxing ──────────────────────────────────────────────────────── */

int64_t kas_int(KValue *v) {
  if (kis_imm_int(v)) return kimm_int_val(v);   /* Stage 1 immediate */
  if (kis_imm(v)) krt_fail("kas_int: not an Int");
  if (v->tag == K_INT) return v->as.i;
  if (v->tag == K_BIGINT) {
    const __mpz_struct *z = (const __mpz_struct *)v->as.big.mpz;
    if (!kmpz_fits_i64_p(z)) krt_fail("kas_int: Integer too large for a machine word");
    return kmpz_get_i64(z);
  }
  krt_fail("kas_int: not an Int");
}
double kas_dbl(KValue *v) {
  if (kis_imm(v) || v->tag != K_DBL) krt_fail("kas_dbl: not a Double");
  return v->as.d;
}
int kas_bool(KValue *v) {
  /* Stage 1b: True/False are b010 nullary immediates — read the id from the word
   * (no deref).  A retired boxed K_CTOR Bool is still accepted by id. */
  int id;
  if (kis_imm_ctor(v)) id = kimm_ctor_id(v);
  else if (!kis_imm(v) && v->tag == K_CTOR) id = v->as.ctor.tagid;
  else krt_fail("kas_bool: not a Bool");
  if (id == KCT_TRUE) return 1;
  if (id == KCT_FALSE) return 0;
  krt_fail("kas_bool: not a Bool constructor");
}

const char *kas_str(KValue *v) {
  if (kis_imm(v) || v->tag != K_STR) krt_fail("kas_str: not a String");
  return v->as.str.p; /* kstr() NUL-terminates; length stays authoritative */
}

/* Read an Integer as an unsigned 64-bit value (§26.1.1 U64/Usize), including
 * the >= 2^63 range that kas_int rejects — the low 64 bits of the magnitude. */
uint64_t kas_u64(KValue *v) {
  if (kis_imm_int(v)) return (uint64_t)kimm_int_val(v);   /* Stage 1 immediate */
  if (!kis_imm(v) && v->tag == K_INT) return (uint64_t)v->as.i;
  mpz_t z; mpz_init(z); kload_mpz(v, z);
  uint64_t u = 0; size_t cnt = 0;
  mpz_export(&u, &cnt, -1, sizeof(uint64_t), 0, 0, z);
  mpz_clear(z);
  return u;
}

void *kas_fgn(KValue *v) {
  if (kis_imm(v) || v->tag != K_FGN) krt_fail("kas_fgn: not a foreign handle");
  return v->as.fgn.p;
}

/* ── references ────────────────────────────────────────────────────── */

KValue *kref_get(KValue *r) {
  if (kis_imm(r) || r->tag != K_REF) krt_fail("kref_get: not a ref");
  return r->as.ref.cell[0];
}
KValue *kref_set(KValue *r, KValue *v) {
  if (kis_imm(r) || r->tag != K_REF) krt_fail("kref_set: not a ref");
  r->as.ref.cell[0] = v;
  return kunit();
}

/* ── pure primitives (mirror Kappa.Eval.evalPurePrim for the subset) ── */

static KValue *show_int_val(KValue *v) {
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

static KValue *str_append(KValue *a, KValue *b) {
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

typedef struct { char *p; size_t len, cap; } sbuf;
static void sb_init(sbuf *b) { b->cap = 32; b->p = (char *)kgc_alloc_atomic(b->cap); b->len = 0; }
static void sb_putc(sbuf *b, char c) {
  if (b->len + 1 > b->cap) {
    size_t nc = b->cap * 2; char *np = (char *)kgc_alloc_atomic(nc);
    memcpy(np, b->p, b->len); b->p = np; b->cap = nc;
  }
  b->p[b->len++] = c;
}
static void sb_puts(sbuf *b, const char *s) { while (*s) sb_putc(b, *s++); }
static KValue *sb_to_str(sbuf *b) { return kstr(b->p, b->len); }

/* decode the next UTF-8 scalar from p (< end); returns bytes consumed.
 * A multibyte sequence truncated by `end` decodes the lead byte alone
 * (returns 1) rather than over-reading past the buffer — every branch
 * checks that all its continuation bytes are in range. */
static int utf8_next(const unsigned char *p, const unsigned char *end, uint32_t *cp) {
  unsigned c = p[0];
  if (c < 0x80) { *cp = c; return 1; }
  if ((c >> 5) == 0x6 && p + 2 <= end) { *cp = ((c & 0x1f) << 6) | (p[1] & 0x3f); return 2; }
  if ((c >> 4) == 0xe && p + 3 <= end) { *cp = ((c & 0x0f) << 12) | ((p[1] & 0x3f) << 6) | (p[2] & 0x3f); return 3; }
  if ((c >> 3) == 0x1e && p + 4 <= end) { *cp = ((c & 0x07) << 18) | ((p[1] & 0x3f) << 12) | ((p[2] & 0x3f) << 6) | (p[3] & 0x3f); return 4; }
  *cp = c; return 1;
}

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

static KValue *show_scalar(KValue *v) {
  if (kis_imm(v) || v->tag != K_CHR) krt_fail("showScalar: not a scalar");
  sbuf b; sb_init(&b); sb_putc(&b, '\'');
  if (v->as.chr == '\'') sb_puts(&b, "\\'");
  else { int n, s; show_lit_char(&b, v->as.chr, &n, &s); }
  sb_putc(&b, '\''); return sb_to_str(&b);
}

static KValue *show_string_lit(KValue *v) {
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
static KValue *show_double(double x) {
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

static KValue *ksome(KValue *x) { KValue *a[1]; a[0] = x; return kctor(KCT_SOME, "std.prelude.Some", 1, a); }
static KValue *knone(void) { return kctor0(KCT_NONE, "std.prelude.None"); }

/* first index of needle in hay, or -1 (portable; no memmem dependency). */
static long bytes_index_of(const unsigned char *hay, size_t hl, const unsigned char *ned, size_t nl) {
  if (nl == 0) return 0;
  if (nl > hl) return -1;
  for (size_t i = 0; i + nl <= hl; i++)
    if (memcmp(hay + i, ned, nl) == 0) return (long)i;
  return -1;
}

static int bytes_cmp(KValue *a, KValue *b) { /* lexicographic by byte */
  size_t la = a->as.bytes.len, lb = b->as.bytes.len, m = la < lb ? la : lb;
  int c = memcmp(a->as.bytes.p, b->as.bytes.p, m);
  if (c != 0) return c < 0 ? -1 : 1;
  return la < lb ? -1 : (la > lb ? 1 : 0);
}

/* §29.1 representation equality (for atomicCompareExchange): structural
 * equality over the canonical first-order runtime values, matching the
 * interpreter's `convertible` on the atomic representation.  Integers
 * compare by value across the inline/bignum boundary. */
static int kvalue_rep_eq(KValue *a, KValue *b) {
  if (a == b) return 1;   /* immediates canonicalise: word identity == value equality */
  /* §5.3: any Int/Int pair normalizes across immediate / inline / bignum. */
  if (kis_int_any(a) && kis_int_any(b)) return kint_cmp(a, b) == 0;
  /* Stage 1d/1e: a b011 packed ctor (one OR two fields) compares STRUCTURALLY
   * against a ctor in any rep (another packed word, or a boxed K_CTOR) — same tag
   * id, same arity AND recursively-equal fields — through the immediate-aware
   * accessors.  Two packed words of the same value are already caught by a==b
   * (canonical), so a packed-vs-packed pair that reaches here differs; the
   * structural compare still gives the right answer and the boxed-vs-packed
   * direction satisfies Pair 1 2 == Pair 1 2 defensively even though
   * canonicalization means a boxed packing-eligible ctor should not normally
   * arise. */
  if (kis_imm_packed(a) || kis_imm_packed(b)) {
    int ta = kctor_tagid(a), tb = kctor_tagid(b);
    if (ta < 0 || ta != tb) return 0;          /* one side not a ctor, or different ctor */
    int na = kctor_argc(a);
    if (na != kctor_argc(b)) return 0;          /* differing arity → unequal */
    for (int i = 0; i < na; i++)
      if (!kvalue_rep_eq(kctor_arg(a, i), kctor_arg(b, i))) return 0;
    return 1;
  }
  /* Past the Int/packed cases, an immediate paired with a non-Int (or two
   * immediates of different value, already ruled out by a==b) is unequal — guard
   * the deref. */
  if (kis_imm(a) || kis_imm(b)) return 0;
  if (a->tag != b->tag) return 0;
  switch (a->tag) {
    case K_DBL: return a->as.d == b->as.d;
    case K_CHR: return a->as.chr == b->as.chr;
    case K_UNIT: return 1;
    case K_BYTE: return a->as.byte == b->as.byte;
    case K_STR:
      return a->as.str.len == b->as.str.len && memcmp(a->as.str.p, b->as.str.p, a->as.str.len) == 0;
    case K_BYTES:
      return a->as.bytes.len == b->as.bytes.len && memcmp(a->as.bytes.p, b->as.bytes.p, a->as.bytes.len) == 0;
    case K_CTOR: {
      if (strcmp(a->as.ctor.name, b->as.ctor.name) != 0 || a->as.ctor.argc != b->as.ctor.argc) return 0;
      for (int i = 0; i < a->as.ctor.argc; i++)
        if (!kvalue_rep_eq(a->as.ctor.args[i], b->as.ctor.args[i])) return 0;
      return 1;
    }
    case K_REC: {
      if (a->as.rec.n != b->as.rec.n) return 0;
      for (int i = 0; i < a->as.rec.n; i++)
        if (strcmp(a->as.rec.names[i], b->as.rec.names[i]) != 0 ||
            !kvalue_rep_eq(a->as.rec.vals[i], b->as.rec.vals[i])) return 0;
      return 1;
    }
    case K_VARIANT:
      return strcmp(a->as.var.tag, b->as.var.tag) == 0 && kvalue_rep_eq(a->as.var.payload, b->as.var.payload);
    default:
      return 0; /* closures/thunks/etc. are not canonical atomic values */
  }
}

/* ── §29.4 std.unicode helpers (table-free: codec, scalars, cursors) ── */

/* UTF-8 encode one scalar (assumed a valid Unicode scalar) into b. */
static void utf8_encode(uint32_t cp, sbuf *b) {
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
static int utf8_strict(const unsigned char *p, const unsigned char *end, uint32_t *cp) {
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
static int utf8_valid_all(const unsigned char *p, size_t len) {
  const unsigned char *end = p + len;
  while (p < end) { uint32_t cp; int n = utf8_strict(p, end, &cp); if (n <= 0) return 0; p += n; }
  return 1;
}

/* Length of the longest wholly-valid UTF-8 prefix (= splitValidUtf8Prefix). */
static size_t utf8_valid_prefix_len(const unsigned char *p, size_t len) {
  const unsigned char *q = p, *end = p + len;
  while (q < end) { uint32_t cp; int n = utf8_strict(q, end, &cp); if (n <= 0) break; q += n; }
  return (size_t)(q - p);
}

/* Is the run an incomplete trailing sequence — i.e. valid once one, two,
 * or three 0x80 continuation bytes are appended (the interpreter's exact
 * isIncompleteUtf8Tail heuristic)?  rest is short in practice. */
static int utf8_is_incomplete_tail(const unsigned char *p, size_t len) {
  unsigned char *buf = (unsigned char *)kgc_alloc_atomic(len + 3);
  if (len) memcpy(buf, p, len);
  for (int k = 1; k <= 3; k++) {
    buf[len + k - 1] = 0x80;
    if (utf8_valid_all(buf, len + (size_t)k)) return 1;
  }
  return 0;
}

/* Number of Unicode scalars in a (valid) UTF-8 string. */
static size_t utf8_scalar_count(const unsigned char *p, size_t len) {
  const unsigned char *end = p + len; size_t n = 0;
  while (p < end) { uint32_t cp; int k = utf8_next(p, end, &cp); p += (k > 0 ? k : 1); n++; }
  return n;
}

/* Byte offset of the start of scalar index `idx` (clamped to [0,count]). */
static size_t utf8_scalar_byte_offset(const unsigned char *p, size_t len, size_t idx) {
  const unsigned char *q = p, *end = p + len; size_t n = 0;
  while (q < end && n < idx) { uint32_t cp; int k = utf8_next(q, end, &cp); q += (k > 0 ? k : 1); n++; }
  return (size_t)(q - p);
}

/* The §29.3 FNV-1a lane: state mixed with 8 little-endian bytes of v. */
static uint64_t fnv_mix_u64(uint64_t s, uint64_t v) {
  for (int i = 0; i < 8; i++) s = (s ^ ((v >> (8 * i)) & 0xff)) * 1099511628211ULL;
  return s;
}
static uint64_t fnv_mix_bytes(uint64_t s, const unsigned char *p, size_t n) {
  for (size_t i = 0; i < n; i++) s = (s ^ p[i]) * 1099511628211ULL;
  return s;
}

/* Low 64 bits of an integer value in Haskell floor-mod sense (matches
 * `fromIntegral :: Integer -> Word64`).  K_INT casts directly (two's
 * complement); K_BIGINT reduces modulo 2^64. */
static uint64_t kint_low64(KValue *v) {
  if (kis_imm_int(v)) return (uint64_t)kimm_int_val(v);   /* Stage 1 immediate */
  if (v->tag == K_INT) return (uint64_t)v->as.i;
  if (v->tag == K_BIGINT) {
    mpz_t r; mpz_init(r);
    mpz_fdiv_r_2exp(r, (const __mpz_struct *)v->as.big.mpz, 64); /* 0 <= r < 2^64 */
    uint64_t lo = 0; size_t count = 0;
    mpz_export(&lo, &count, -1, sizeof(uint64_t), 0, 0, r);      /* little-endian limb */
    mpz_clear(r);
    return lo;
  }
  krt_fail("hash mix on a non-integer value");
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

/* Growable scalar (code-point) buffer; pointer-free, so allocate atomic. */
typedef struct { uint32_t *p; size_t len, cap; } cpbuf;
static void cp_init(cpbuf *b) { b->cap = 16; b->p = (uint32_t *)kgc_alloc_atomic(b->cap * sizeof(uint32_t)); b->len = 0; }
static void cp_push(cpbuf *b, uint32_t c) {
  if (b->len + 1 > b->cap) {
    size_t nc = b->cap * 2; uint32_t *np = (uint32_t *)kgc_alloc_atomic(nc * sizeof(uint32_t));
    memcpy(np, b->p, b->len * sizeof(uint32_t)); b->p = np; b->cap = nc;
  }
  b->p[b->len++] = c;
}

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
static void ku_decode(const unsigned char *s, size_t slen, cpbuf *out) {
  const unsigned char *p = s, *end = s + slen;
  while (p < end) { uint32_t cp; int k = utf8_next(p, end, &cp); p += (k > 0 ? k : 1); cp_push(out, cp); }
}

/* §29.4 normalize: form 0=NFC 1=NFD 2=NFKC 3=NFKD (Kappa.Unicode order). */
static KValue *ku_normalize(int form, const unsigned char *s, size_t slen) {
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
static size_t ku_grapheme_len(const uint32_t *cps, size_t n, size_t start) {
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

static size_t ku_grapheme_count(const uint32_t *cps, size_t n) {
  size_t i = 0, count = 0;
  while (i < n) { size_t l = ku_grapheme_len(cps, n, i); i += (l ? l : 1); count++; }
  return count;
}

/* Encode cps[a..b) back to a UTF-8 K_STR. */
static KValue *ku_encode_range(const uint32_t *cps, size_t a, size_t b) {
  sbuf sb; sb_init(&sb); for (size_t i = a; i < b; i++) utf8_encode(cps[i], &sb); return sb_to_str(&sb);
}

/* Full case fold of one scalar: writes folded scalars into out. */
static void ku_casefold_scalar(uint32_t c, cpbuf *out) {
  int i = ku_bsearch(ku_fold_cp_arr, KU_FOLD_N, (int32_t)c);
  if (i < 0) { cp_push(out, c); return; }
  for (int k = 0; k < ku_fold_len[i]; k++) cp_push(out, (uint32_t)ku_fold_pool[ku_fold_off[i] + k]);
}

/* Haskell Data.Char.isSpace (ASCII controls + Unicode space separators). */
static int ku_is_space(uint32_t c) {
  if (c == ' ' || (c >= '\t' && c <= '\r')) return 1;       /* \t \n \v \f \r */
  if (c == 0x85 || c == 0xA0 || c == 0x1680) return 1;
  if (c >= 0x2000 && c <= 0x200A) return 1;
  return c == 0x2028 || c == 0x2029 || c == 0x202F || c == 0x205F || c == 0x3000;
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
static int kint_cmp(KValue *a, KValue *b) {
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
/* §6.5 byte compares + §29.1 bitwise (hot in hashing / byte loops).  Byte values
 * are always boxed (K_BYTE) — never immediates — so the deref is sound. */
KValue *kp_eqByte(KValue *x, KValue *y) { return kbool(x->as.byte == y->as.byte); }
KValue *kp_ltByte(KValue *x, KValue *y) { return kbool(x->as.byte < y->as.byte); }
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

/* ── per-primitive direct entry points (codegen calls these directly;
 * the string dispatcher below is the bootstrap/interpreter path only). */
KValue *kpf_addInt(KValue **a) {
  return kp_addInt(a[0], a[1]);
}
KValue *kpf_subInt(KValue **a) {
  return kp_subInt(a[0], a[1]);
}
KValue *kpf_mulInt(KValue **a) {
  return kp_mulInt(a[0], a[1]);
}
KValue *kpf_divInt(KValue **a) {
  return kp_divInt(a[0], a[1]);
}
KValue *kpf_modInt(KValue **a) {
  return kp_modInt(a[0], a[1]);
}
KValue *kpf_negInt(KValue **a) {
  return kp_negInt(a[0]);
}
KValue *kpf_eqInt(KValue **a) {
  return kp_eqInt(a[0], a[1]);
}
KValue *kpf_ltInt(KValue **a) {
  return kp_ltInt(a[0], a[1]);
}
KValue *kpf_leInt(KValue **a) {
  return kp_leInt(a[0], a[1]);
}
KValue *kpf_addDouble(KValue **a) {
  return kp_addDouble(a[0], a[1]);
}
KValue *kpf_subDouble(KValue **a) {
  return kp_subDouble(a[0], a[1]);
}
KValue *kpf_mulDouble(KValue **a) {
  return kp_mulDouble(a[0], a[1]);
}
KValue *kpf_divDouble(KValue **a) {
  return kp_divDouble(a[0], a[1]);
}
KValue *kpf_negDouble(KValue **a) {
  return kp_negDouble(a[0]);
}
KValue *kpf_ltDouble(KValue **a) {
  return kp_ltDouble(a[0], a[1]);
}
KValue *kpf_floatEq(KValue **a) {
  return kp_floatEq(a[0], a[1]);
}
KValue *kpf_eqDouble(KValue **a) {
  return kp_eqDouble(a[0], a[1]);
}
KValue *kpf_stringAppend(KValue **a) {
  return kp_stringAppend(a[0], a[1]);
}
KValue *kpf_eqStr(KValue **a) {
  return kp_eqStr(a[0], a[1]);
}
KValue *kpf_ltStr(KValue **a) {
  return kp_ltStr(a[0], a[1]);
}
KValue *kpf_eqScalar(KValue **a) {
  return kp_eqScalar(a[0], a[1]);
}
KValue *kpf_ltScalar(KValue **a) {
  return kp_ltScalar(a[0], a[1]);
}
KValue *kpf_natToInt(KValue **a) {
  return a[0];
}
KValue *kpf_intToNat(KValue **a) {
  int neg;
  if (kis_int_word(a[0])) neg = kint_word(a[0]) < 0;       /* immediate or inline */
  else neg = mpz_sgn((const __mpz_struct *)a[0]->as.big.mpz) < 0;
  if (neg) krt_fail("intToNat: negative Int has no Nat image");
  return a[0];
}
KValue *kpf_intToDouble(KValue **a) {
  return kp_intToDouble(a[0]);
}
KValue *kpf_primitiveIntToString(KValue **a) {
  return show_int_val(a[0]);
}
KValue *kpf_showInt(KValue **a) {
  return kp_showInt(a[0]);
}
KValue *kpf_showDouble(KValue **a) {
  return kp_showDouble(a[0]);
}
KValue *kpf_showScalar(KValue **a) {
  return kp_showScalar(a[0]);
}
KValue *kpf_showStringLit(KValue **a) {
  return kp_showStringLit(a[0]);
}
KValue *kpf___ratOfInt(KValue **a) {
  mpz_t n, d; mpz_init(d); mpz_set_ui(d, 1); mpz_init(n); kload_mpz(a[0], n);
    return krat(n, d);
}
KValue *kpf___ratNum(KValue **a) {
  mpz_t n, d; mpz_init(n); mpz_init(d); as_rat(a[0], n, d); return kfrom_mpz(n);
}
KValue *kpf___ratDen(KValue **a) {
  mpz_t n, d; mpz_init(n); mpz_init(d); as_rat(a[0], n, d); return kfrom_mpz(d);
}
KValue *kpf_addRat(KValue **a) {
  return rat_addsub(a[0], a[1], 0);
}
KValue *kpf_subRat(KValue **a) {
  return rat_addsub(a[0], a[1], 1);
}
KValue *kpf_mulRat(KValue **a) {
  mpz_t a1, b1, c1, d1, n, den; mpz_inits(a1, b1, c1, d1, n, den, NULL);
    as_rat(a[0], a1, b1); as_rat(a[1], c1, d1);
    mpz_mul(n, a1, c1); mpz_mul(den, b1, d1); return krat(n, den);
}
KValue *kpf_divRat(KValue **a) {
  mpz_t a1, b1, c1, d1, n, den; mpz_inits(a1, b1, c1, d1, n, den, NULL);
    as_rat(a[0], a1, b1); as_rat(a[1], c1, d1);
    if (mpz_sgn(c1) == 0) krt_fail("divRat: division by zero");
    mpz_mul(n, a1, d1); mpz_mul(den, b1, c1); return krat(n, den);
}
KValue *kpf_negRat(KValue **a) {
  mpz_t n, d; mpz_init(n); mpz_init(d); as_rat(a[0], n, d); mpz_neg(n, n); return krat(n, d);
}
KValue *kpf_eqRat(KValue **a) {
  mpz_t a1, b1, c1, d1, l, r; mpz_inits(a1, b1, c1, d1, l, r, NULL);
    as_rat(a[0], a1, b1); as_rat(a[1], c1, d1);
    mpz_mul(l, a1, d1); mpz_mul(r, c1, b1); /* dens positive, so cross-mul preserves order */
    int c = mpz_cmp(l, r);
    return kbool(1 ? c == 0 : c < 0);
}
KValue *kpf_ltRat(KValue **a) {
  mpz_t a1, b1, c1, d1, l, r; mpz_inits(a1, b1, c1, d1, l, r, NULL);
    as_rat(a[0], a1, b1); as_rat(a[1], c1, d1);
    mpz_mul(l, a1, d1); mpz_mul(r, c1, b1); /* dens positive, so cross-mul preserves order */
    int c = mpz_cmp(l, r);
    return kbool(0 ? c == 0 : c < 0);
}
KValue *kpf_showRat(KValue **a) {
  mpz_t n, d; mpz_init(n); mpz_init(d); as_rat(a[0], n, d);
    /* A small Rational (e.g. 1/2) is a b011 packed word now, so read its parts
     * through the rep-agnostic kctor_arg rather than a raw deref. */
    KValue *ns = show_int_val(kctor_arg(a[0], 0));
    if (mpz_cmp_ui(d, 1) == 0) return ns;
    return str_append(str_append(ns, kstr0("/")), show_int_val(kctor_arg(a[0], 1)));
}
KValue *kpf_ratOfDouble(KValue **a) {
  double x = kas_dbl(a[0]);
    if (isnan(x) || isinf(x)) { mpz_t n, d; mpz_init(n); mpz_init_set_ui(d, 1); return krat(n, d); }
    int e2; double frac = frexp(x, &e2);            /* x = frac * 2^e2, 0.5<=|frac|<1 */
    long long mant = (long long)ldexp(frac, 53);    /* exact integer significand */
    int sh = e2 - 53;
    mpz_t n, d; mpz_init(n); kmpz_set_i64(n, (int64_t)mant); mpz_init_set_ui(d, 1);
    if (sh >= 0) mpz_mul_2exp(n, n, (unsigned)sh); else mpz_mul_2exp(d, d, (unsigned)(-sh));
    return krat(n, d);
}
KValue *kpf_eqByte(KValue **a) {
  return kp_eqByte(a[0], a[1]);
}
KValue *kpf_ltByte(KValue **a) {
  return kp_ltByte(a[0], a[1]);
}
KValue *kpf_showByte(KValue **a) {
  char t[8]; snprintf(t, sizeof t, "b'\\x%02x'", a[0]->as.byte); return kstr0(t);
}
KValue *kpf_eqBytes(KValue **a) {
  return kbool(bytes_cmp(a[0], a[1]) == 0);
}
KValue *kpf_ltBytes(KValue **a) {
  return kbool(bytes_cmp(a[0], a[1]) < 0);
}
KValue *kpf_showBytes(KValue **a) {
  sbuf b; sb_init(&b); sb_puts(&b, "0x");
    for (size_t i = 0; i < a[0]->as.bytes.len; i++) { char t[3]; snprintf(t, 3, "%02x", a[0]->as.bytes.p[i]); sb_puts(&b, t); }
    return sb_to_str(&b);
}
KValue *kpf_eqGrapheme(KValue **a) {
  return kbool(klit_eq(a[0], a[1]));
}
KValue *kpf_showGrapheme(KValue **a) {
  return str_append(str_append(kstr0("g'"), a[0]), kstr0("'"));
}
KValue *kpf___bytesEmpty(KValue **a) {
  return kbytes((const unsigned char *)"", 0);
}
KValue *kpf___bytesSingleton(KValue **a) {
  unsigned char w = a[0]->as.byte; return kbytes(&w, 1);
}
KValue *kpf___bytesLength(KValue **a) {
  return kint((int64_t)a[0]->as.bytes.len);
}
KValue *kpf___bytesIsEmpty(KValue **a) {
  return kbool(a[0]->as.bytes.len == 0);
}
KValue *kpf___bytesGet(KValue **a) {
  int64_t i = kas_int(a[1]);
    if (i >= 0 && i < (int64_t)a[0]->as.bytes.len) return ksome(kbyte(a[0]->as.bytes.p[i]));
    return knone();
}
KValue *kpf___bytesIndexUnsafe(KValue **a) {
  int64_t i = kas_int(a[1]);
    if (i < 0 || i >= (int64_t)a[0]->as.bytes.len) krt_fail("__bytesIndexUnsafe: out of range");
    return kbyte(a[0]->as.bytes.p[i]);
}
KValue *kpf___bytesAppend(KValue **a) {
  size_t la = a[0]->as.bytes.len, lb = a[1]->as.bytes.len;
    unsigned char *buf = (unsigned char *)kgc_alloc_atomic(la + lb ? la + lb : 1);
    memcpy(buf, a[0]->as.bytes.p, la); memcpy(buf + la, a[1]->as.bytes.p, lb);
    return kbytes(buf, la + lb);
}
KValue *kpf___bytesSlice(KValue **a) {
  int64_t st = kas_int(a[1]), ln = kas_int(a[2]); size_t len = a[0]->as.bytes.len;
    if (st < 0) st = 0;
    if (st > (int64_t)len) st = (int64_t)len;
    if (ln < 0) ln = 0;
    if (st + ln > (int64_t)len) ln = (int64_t)len - st;
    return kbytes(a[0]->as.bytes.p + st, (size_t)ln);
}
KValue *kpf___bytesTake(KValue **a) {
  int64_t n = kas_int(a[0]); size_t len = a[1]->as.bytes.len; if (n < 0) n = 0; if (n > (int64_t)len) n = (int64_t)len;
    return kbytes(a[1]->as.bytes.p, (size_t)n);
}
KValue *kpf___bytesDrop(KValue **a) {
  int64_t n = kas_int(a[0]); size_t len = a[1]->as.bytes.len; if (n < 0) n = 0; if (n > (int64_t)len) n = (int64_t)len;
    return kbytes(a[1]->as.bytes.p + n, len - (size_t)n);
}
KValue *kpf___bytesStartsWith(KValue **a) {
  size_t pl = a[0]->as.bytes.len, hl = a[1]->as.bytes.len;
    return kbool(pl <= hl && memcmp(a[1]->as.bytes.p, a[0]->as.bytes.p, pl) == 0);
}
KValue *kpf___bytesEndsWith(KValue **a) {
  size_t sl = a[0]->as.bytes.len, hl = a[1]->as.bytes.len;
    return kbool(sl <= hl && memcmp(a[1]->as.bytes.p + (hl - sl), a[0]->as.bytes.p, sl) == 0);
}
KValue *kpf___bytesContains(KValue **a) {
  return kbool(bytes_index_of(a[1]->as.bytes.p, a[1]->as.bytes.len, a[0]->as.bytes.p, a[0]->as.bytes.len) >= 0);
}
KValue *kpf___bytesFind(KValue **a) {
  unsigned char w = a[0]->as.byte;
    for (size_t i = 0; i < a[1]->as.bytes.len; i++) if (a[1]->as.bytes.p[i] == w) return ksome(kint((int64_t)i));
    return knone();
}
KValue *kpf___bytesBreakIndex(KValue **a) {
  long ix = bytes_index_of(a[1]->as.bytes.p, a[1]->as.bytes.len, a[0]->as.bytes.p, a[0]->as.bytes.len);
    return ix < 0 ? knone() : ksome(kint((int64_t)ix));
}
KValue *kpf___bytesToList(KValue **a) {
  KValue *acc = knil();
    for (size_t i = a[0]->as.bytes.len; i > 0; i--) acc = kcons(kbyte(a[0]->as.bytes.p[i - 1]), acc);
    return acc;
}
KValue *kpf___bytesFromList(KValue **a) {
  /* count then fill */
    size_t n = 0; for (KValue *v = a[0]; kis_cons(v); v = kctor_arg(v, 1)) n++;
    unsigned char *buf = (unsigned char *)kgc_alloc_atomic(n ? n : 1); size_t i = 0;
    for (KValue *v = a[0]; kis_cons(v); v = kctor_arg(v, 1)) buf[i++] = kctor_arg(v, 0)->as.byte;
    return kbytes(buf, n);
}
KValue *kpf___bytesCompact(KValue **a) {
  return a[0];
}
KValue *kpf___newBytesBuilder(KValue **a) {
  return kbytes((const unsigned char *)"", 0);
}
KValue *kpf___bytesBuilderByte(KValue **a) {
  /* (byte, builder) -> builder */
    size_t n = a[1]->as.bytes.len;
    unsigned char *buf = (unsigned char *)kgc_alloc_atomic(n + 1);
    memcpy(buf, a[1]->as.bytes.p, n); buf[n] = a[0]->as.byte;
    return kbytes(buf, n + 1);
}
KValue *kpf___bytesBuilderBytes(KValue **a) {
  /* (bytes, builder) -> builder */
    size_t na = a[1]->as.bytes.len, nb = a[0]->as.bytes.len;
    unsigned char *buf = (unsigned char *)kgc_alloc_atomic(na + nb ? na + nb : 1);
    memcpy(buf, a[1]->as.bytes.p, na); memcpy(buf + na, a[0]->as.bytes.p, nb);
    return kbytes(buf, na + nb);
}
KValue *kpf___finishBytesBuilder(KValue **a) {
  return a[0];
}
KValue *kpf___utf8Bytes(KValue **a) {
  return kbytes((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len);
}
KValue *kpf___utf8Valid(KValue **a) {
  return kbool(utf8_valid_all(a[0]->as.bytes.p, a[0]->as.bytes.len));
}
KValue *kpf___decodeUtf8Lossy(KValue **a) {
  /* Lenient decode (one U+FFFD per ill-formed maximal subpart).  The
     * std.unicode wrapper only calls this after __utf8Valid succeeds, so
     * the reachable case is the exact identity decode of valid UTF-8. */
    const unsigned char *p = a[0]->as.bytes.p, *end = p + a[0]->as.bytes.len;
    sbuf b; sb_init(&b);
    while (p < end) {
      uint32_t cp; int n = utf8_strict(p, end, &cp);
      if (n > 0) { for (int i = 0; i < n; i++) sb_putc(&b, (char)p[i]); p += n; }
      else { sb_puts(&b, "\xEF\xBF\xBD"); if (n == 0) p = end; else p += 1; }
    }
    return sb_to_str(&b);
}
KValue *kpf___byteLength(KValue **a) {
  return kint((int64_t)a[0]->as.str.len);
}
KValue *kpf___uniScalarValue(KValue **a) {
  return kint((int64_t)a[0]->as.chr);
}
KValue *kpf___scalarInRange(KValue **a) {
  int64_t n = kas_int(a[0]);
    return kbool(n >= 0 && n <= 0x10FFFF && !(n >= 0xD800 && n <= 0xDFFF));
}
KValue *kpf___scalarOfValue(KValue **a) {
  int64_t n = kas_int(a[0]);
    if (n >= 0 && n <= 0x10FFFF && !(n >= 0xD800 && n <= 0xDFFF)) return kchr((uint32_t)n);
    krt_fail("__scalarOfValue: value is not a Unicode scalar");
}
KValue *kpf___scalarToString(KValue **a) {
  sbuf b; sb_init(&b); utf8_encode(a[0]->as.chr, &b); return sb_to_str(&b);
}
KValue *kpf___scalarCount(KValue **a) {
  return kint((int64_t)utf8_scalar_count((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len));
}
KValue *kpf___stringScalars(KValue **a) {
  const unsigned char *p = (const unsigned char *)a[0]->as.str.p, *end = p + a[0]->as.str.len;
    KValue *acc = knil();
    /* collect codepoints then fold right-to-left into a cons list */
    size_t cnt = utf8_scalar_count(p, a[0]->as.str.len);
    KValue **tmp = (KValue **)kgc_alloc(sizeof(KValue *) * (cnt ? cnt : 1));
    size_t i = 0; const unsigned char *q = p;
    while (q < end) { uint32_t cp; int k = utf8_next(q, end, &cp); q += (k > 0 ? k : 1); tmp[i++] = kchr(cp); }
    for (size_t j = cnt; j > 0; j--) acc = kcons(tmp[j - 1], acc);
    return acc;
}
KValue *kpf___byteToNat(KValue **a) {
  return kint((int64_t)a[0]->as.byte);
}
KValue *kpf___natToByte(KValue **a) {
  return kbyte((unsigned char)(kint_low64(a[0]) & 0xff));
}
KValue *kpf___graphemeToString(KValue **a) {
  return a[0];
}
KValue *kpf___queryFromList(KValue **a) {
  return a[0];
}
KValue *kpf_unsafeConsume(KValue **a) {
  return kunit();
}
KValue *kpf___arrayIndexUnsafe(KValue **a) {
  KValue *v = a[0]; int64_t i = kas_int(a[1]);
    while (kis_cons(v)) { if (i <= 0) return kctor_arg(v, 0); v = kctor_arg(v, 1); i--; }
    krt_fail("__arrayIndexUnsafe: index out of range");
}
KValue *kpf___rangeEnum(KValue **a) {
  int ex = kas_bool(a[2]); KValue *acc = knil();
    if (!kis_imm(a[0]) && a[0]->tag == K_CHR) {   /* Char range; else Int (immediate) */
      int64_t lo = (int64_t)a[0]->as.chr, hi = (int64_t)a[1]->as.chr, top = ex ? hi - 1 : hi;
      for (int64_t c = top; c >= lo; c--) { if (c >= 0xD800 && c <= 0xDFFF) continue; acc = kcons(kchr((uint32_t)c), acc); }
    } else {
      int64_t lo = kas_int(a[0]), hi = kas_int(a[1]), top = ex ? hi - 1 : hi;
      for (int64_t n = top; n >= lo; n--) acc = kcons(kint(n), acc);
    }
    return acc;
}
KValue *kpf___intAnd(KValue **a) {
  return kp_intAnd(a[0], a[1]);
}
KValue *kpf___intOr(KValue **a) {
  return kp_intOr(a[0], a[1]);
}
KValue *kpf___intXor(KValue **a) {
  return kp_intXor(a[0], a[1]);
}
KValue *kpf___hashMixInt(KValue **a) {
  return ku64(fnv_mix_u64(kint_low64(a[0]), kint_low64(a[1])));
}
KValue *kpf___hashMixDouble(KValue **a) {
  uint64_t bits; double d = a[1]->as.d; memcpy(&bits, &d, sizeof bits);
    return ku64(fnv_mix_u64(kint_low64(a[0]), bits));
}
KValue *kpf___hashMixString(KValue **a) {
  return ku64(fnv_mix_bytes(kint_low64(a[0]), (const unsigned char *)a[1]->as.str.p, a[1]->as.str.len));
}
KValue *kpf___hashMixBytes(KValue **a) {
  return ku64(fnv_mix_bytes(kint_low64(a[0]), a[1]->as.bytes.p, a[1]->as.bytes.len));
}
KValue *kpf___newStringBuilder(KValue **a) {
  return kstr0("");
}
KValue *kpf___stringBuilderString(KValue **a) {
  return str_append(a[1], a[0]);
}
KValue *kpf___stringBuilderScalar(KValue **a) {
  sbuf b; sb_init(&b); utf8_encode(a[0]->as.chr, &b); return str_append(a[1], sb_to_str(&b));
}
KValue *kpf___stringBuilderGrapheme(KValue **a) {
  return str_append(a[1], a[0]);
}
KValue *kpf___finishStringBuilder(KValue **a) {
  return a[0];
}
KValue *kpf___stringStart(KValue **a) {
  return kint(0);
}
KValue *kpf___stringEnd(KValue **a) {
  return kint((int64_t)utf8_scalar_count((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len));
}
KValue *kpf___stringCursorOffset(KValue **a) {
  int64_t i = kas_int(a[1]); if (i < 0) i = 0;
    return kint((int64_t)utf8_scalar_byte_offset((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len, (size_t)i));
}
KValue *kpf___stringNextScalar(KValue **a) {
  const unsigned char *p = (const unsigned char *)a[0]->as.str.p; size_t len = a[0]->as.str.len;
    int64_t i = kas_int(a[1]); size_t cnt = utf8_scalar_count(p, len);
    if (i >= 0 && i < (int64_t)cnt) {
      size_t off = utf8_scalar_byte_offset(p, len, (size_t)i);
      uint32_t cp; utf8_next(p + off, p + len, &cp);
      static const char *nm[2] = {"next", "scalar"};
      KValue *vals[2]; vals[0] = kint(i + 1); vals[1] = kchr(cp);
      return ksome(krec(2, nm, vals));
    }
    return knone();
}
KValue *kpf___stringPrevScalar(KValue **a) {
  const unsigned char *p = (const unsigned char *)a[0]->as.str.p; size_t len = a[0]->as.str.len;
    int64_t i = kas_int(a[1]); size_t cnt = utf8_scalar_count(p, len);
    if (i > 0 && i <= (int64_t)cnt) {
      size_t off = utf8_scalar_byte_offset(p, len, (size_t)(i - 1));
      uint32_t cp; utf8_next(p + off, p + len, &cp);
      static const char *nm[2] = {"prev", "scalar"};
      KValue *vals[2]; vals[0] = kint(i - 1); vals[1] = kchr(cp);
      return ksome(krec(2, nm, vals));
    }
    return knone();
}
KValue *kpf___stringSpan(KValue **a) {
  const unsigned char *p = (const unsigned char *)a[0]->as.str.p; size_t len = a[0]->as.str.len;
    int64_t aa = kas_int(a[1]), bb = kas_int(a[2]); size_t cnt = utf8_scalar_count(p, len);
    if (aa >= 0 && bb <= (int64_t)cnt && aa <= bb) {
      size_t oa = utf8_scalar_byte_offset(p, len, (size_t)aa);
      size_t ob = utf8_scalar_byte_offset(p, len, (size_t)bb);
      return ksome(kstr((const char *)(p + oa), ob - oa));
    }
    return knone();
}
KValue *kpf___newUtf8Decoder(KValue **a) {
  return kbytes((const unsigned char *)"", 0);
}
KValue *kpf___decodeUtf8Chunk(KValue **a) {
  size_t pl = a[1]->as.bytes.len, cl = a[0]->as.bytes.len, total = pl + cl;
    unsigned char *comb = (unsigned char *)kgc_alloc_atomic(total ? total : 1);
    if (pl) memcpy(comb, a[1]->as.bytes.p, pl);
    if (cl) memcpy(comb + pl, a[0]->as.bytes.p, cl);
    size_t plen = utf8_valid_prefix_len(comb, total), rlen = total - plen;
    if (rlen > 0 && !utf8_is_incomplete_tail(comb + plen, rlen)) return knone();
    static const char *nm[2] = {"decoder", "text"};
    KValue *vals[2]; vals[0] = kbytes(comb + plen, rlen); vals[1] = kstr((const char *)comb, plen);
    return ksome(krec(2, nm, vals));
}
KValue *kpf___finishUtf8Decoder(KValue **a) {
  return a[0]->as.bytes.len == 0 ? ksome(kstr0("")) : knone();
}
KValue *kpf___atomicRepEq(KValue **a) {
  return kbool(kvalue_rep_eq(a[0], a[1]));
}
KValue *kpf___normalize(KValue **a) {
  return ku_normalize((int)kas_int(a[0]), (const unsigned char *)a[1]->as.str.p, a[1]->as.str.len);
}
KValue *kpf___caseFold(KValue **a) {
  cpbuf in; cp_init(&in); ku_decode((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len, &in);
    cpbuf out; cp_init(&out);
    for (size_t i = 0; i < in.len; i++) ku_casefold_scalar(in.p[i], &out);
    sbuf b; sb_init(&b); for (size_t i = 0; i < out.len; i++) utf8_encode(out.p[i], &b); return sb_to_str(&b);
}
KValue *kpf___graphemeCount(KValue **a) {
  cpbuf in; cp_init(&in); ku_decode((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len, &in);
    return kint((int64_t)ku_grapheme_count(in.p, in.len));
}
KValue *kpf___graphemeValid(KValue **a) {
  cpbuf in; cp_init(&in); ku_decode((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len, &in);
    return kbool(ku_grapheme_count(in.p, in.len) == 1);
}
KValue *kpf___graphemeOfString(KValue **a) {
  cpbuf in; cp_init(&in); ku_decode((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len, &in);
    if (ku_grapheme_count(in.p, in.len) == 1) return a[0];
    krt_fail("__graphemeOfString: string is not a single grapheme");
}
KValue *kpf___stringGraphemes(KValue **a) {
  cpbuf in; cp_init(&in); ku_decode((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len, &in);
    cpbuf bounds; cp_init(&bounds);
    size_t i = 0; while (i < in.len) { cp_push(&bounds, (uint32_t)i); size_t l = ku_grapheme_len(in.p, in.len, i); i += (l ? l : 1); }
    KValue *acc = knil();
    for (size_t b = bounds.len; b > 0; b--) {
      size_t st = bounds.p[b - 1], en = (b < bounds.len) ? bounds.p[b] : in.len;
      acc = kcons(ku_encode_range(in.p, st, en), acc);
    }
    return acc;
}
KValue *kpf___stringNextGrapheme(KValue **a) {
  cpbuf in; cp_init(&in); ku_decode((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len, &in);
    int64_t i = kas_int(a[1]);
    if (i >= 0 && i < (int64_t)in.len) {
      size_t l = ku_grapheme_len(in.p, in.len, (size_t)i); if (l == 0) l = 1;
      static const char *nm[2] = {"grapheme", "next"};
      KValue *vals[2]; vals[0] = ku_encode_range(in.p, (size_t)i, (size_t)i + l); vals[1] = kint(i + (int64_t)l);
      return ksome(krec(2, nm, vals));
    }
    return knone();
}
KValue *kpf___stringWords(KValue **a) {
  cpbuf in; cp_init(&in); ku_decode((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len, &in);
    cpbuf ws, we; cp_init(&ws); cp_init(&we);
    size_t i = 0;
    while (i < in.len) {
      while (i < in.len && ku_is_space(in.p[i])) i++;
      if (i >= in.len) break;
      size_t st = i; while (i < in.len && !ku_is_space(in.p[i])) i++;
      cp_push(&ws, (uint32_t)st); cp_push(&we, (uint32_t)i);
    }
    KValue *acc = knil();
    for (size_t b = ws.len; b > 0; b--) acc = kcons(ku_encode_range(in.p, ws.p[b - 1], we.p[b - 1]), acc);
    return acc;
}
KValue *kpf___stringSentences(KValue **a) {
  cpbuf in; cp_init(&in); ku_decode((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len, &in);
    cpbuf ps, pe; cp_init(&ps); cp_init(&pe);
    size_t start = 0, i = 0;
    while (i < in.len) {
      if (in.p[i] == '.' || in.p[i] == '!' || in.p[i] == '?') { cp_push(&ps, (uint32_t)start); cp_push(&pe, (uint32_t)(i + 1)); start = i + 1; }
      i++;
    }
    if (start < in.len) { cp_push(&ps, (uint32_t)start); cp_push(&pe, (uint32_t)in.len); }
    KValue *acc = knil();
    for (size_t b = ps.len; b > 0; b--) {
      size_t st = ps.p[b - 1], en = pe.p[b - 1];
      while (st < en && ku_is_space(in.p[st])) st++;
      while (en > st && ku_is_space(in.p[en - 1])) en--;
      if (en > st) acc = kcons(ku_encode_range(in.p, st, en), acc);
    }
    return acc;
}

/* ── IO execution ──────────────────────────────────────────────────── */

/* A heap stack of pending §18.7 finalizers (see kio_finally / krun_io). */
struct kdefer_frame { KValue **defers; int n; struct kdefer_frame *next; };

/* Run the accumulated finalizers LIFO (innermost scope first, last-
 * registered first within a scope) once a tail recursion reaches a value,
 * then return that value (or Unit when a K_IOEFFECT discarded it). */
static KValue *krun_finish(KValue *v, int discard, struct kdefer_frame *fr) {
  KValue *result = v;
  for (; fr; fr = fr->next) {
    for (int i = fr->n - 1; i >= 0; i--) {
      KValue *dr = krun_io(fr->defers[i]);
      if (!kis_fail(result) && kis_fail(dr)) result = dr;
    }
  }
  if (kis_fail(result)) return result;
  return discard ? kunit() : result;
}

KValue *krun_io(KValue *action) {
  /* Trampoline: a do-block's tail action (K_IOTAIL), a discarded tail
   * statement-`if` branch action (K_IOEFFECT → final result is Unit), and
   * the tail leg of ioBind/ioThen all continue this loop instead of
   * re-entering krun_io, so any sequenced IO tail-recursion runs in
   * constant C stack (§27.5A.3).  `discard` records that a K_IOEFFECT was
   * crossed, so the loop's final value is Unit (matching the interpreter,
   * whose KIf completion discards the branch value). */
  int discard = 0;
  /* heap stack of pending §18.7 finalizers, accumulated across a tail
   * recursion and run (LIFO) once the recursion reaches a value. */
  struct kdefer_frame *defers = NULL;
  while (1) {
  /* UNBOXING Stage 1: an immediate value in IO position is a `return`ed result
   * (e.g. `do { …; pure n }` yielding a small Int) — never an IO node — so it
   * finishes the loop directly, never dereferencing the odd word. */
  if (kis_imm(action)) return krun_finish(action, discard, defers);
  switch (action->tag) {
    case K_IOTAIL:
      action = action->as.bounce.fn;
      continue;
    case K_IOEFFECT:
      discard = 1;
      action = action->as.bounce.fn;
      continue;
    case K_IOFINALLY: {
      struct kdefer_frame *f = (struct kdefer_frame *)kgc_alloc(sizeof *f);
      f->defers = action->as.iofin.defers; f->n = action->as.iofin.n; f->next = defers;
      defers = f;
      action = action->as.iofin.action;
      continue;
    }
    case K_IO: {
      KValue *r = action->as.io.fn(action->as.io.env);
      if (kis_imm(r)) return krun_finish(r, discard, defers); /* immediate result */
      if (r->tag == K_IOTAIL) { action = r->as.bounce.fn; continue; }
      if (r->tag == K_IOEFFECT) { discard = 1; action = r->as.bounce.fn; continue; }
      if (r->tag == K_IOFINALLY) {
        struct kdefer_frame *f = (struct kdefer_frame *)kgc_alloc(sizeof *f);
        f->defers = r->as.iofin.defers; f->n = r->as.iofin.n; f->next = defers;
        defers = f; action = r->as.iofin.action; continue;
      }
      return krun_finish(r, discard, defers);
    }
    case K_NATIVE: {
      /* §27.1.1: fire the manifest symbol by calling the codegen-emitted
       * wrapper DIRECTLY — no name lookup, no strcmp, no dispatch table. */
      if (action->as.native.argc < action->as.native.arity)
        krt_fail("internal: native action run before saturation");
      KValue *r = action->as.native.fn(action->as.native.args);
      return krun_finish(r, discard, defers);
    }
    default:
      /* A pure value used in IO position (a `return`ed result, a data ctor) —
       * OR a CK-machine action node (krt2_bind/then/pure/catch/throw) that
       * reached the bridge because its do-bind action is an IO combinator
       * building a krt2_* tree (liftA2/<*>/traverse via the Applicative (IO e)
       * dictionary, which the §3.3 analysis cannot see through; see rt.c).
       * krt2_run_op_sync drives the non-suspending OPs to a value and returns
       * any non-OP value unchanged. */
      return krun_finish(krt2_run_op_sync(action), discard, defers);
  }
  }
}

KValue *krun_io_checked(KValue *action) {
  KValue *result = krun_io(action);
  if (kis_fail(result)) krt_fail("__runIO: uncaught typed IO failure");
  return result;
}
