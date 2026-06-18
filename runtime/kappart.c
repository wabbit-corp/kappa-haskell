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

void krt_init(void) {
  GC_INIT();
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

/* Cache boxes for small integers — the common loop counters / digits —
 * so a hot numeric loop does not allocate a fresh box per step.  K_INT is
 * immutable, so sharing is sound; the static array is a GC root. */
#define KINT_CACHE_LO (-16)
#define KINT_CACHE_HI 256
static KValue *kint_cache[KINT_CACHE_HI - KINT_CACHE_LO + 1];
KValue *kint(int64_t v) {
  if (v >= KINT_CACHE_LO && v <= KINT_CACHE_HI) {
    KValue **slot = &kint_cache[v - KINT_CACHE_LO];
    if (!*slot) { KValue *r = alloc_val_atomic(K_INT); r->as.i = v; *slot = r; }
    return *slot;
  }
  KValue *r = alloc_val_atomic(K_INT);
  r->as.i = v;
  return r;
}

/* ── arbitrary-precision integers (GMP, §6) ────────────────────────── */
/* Representation: small values stay inline in K_INT (int64); a value that
 * does not fit int64 is a K_BIGINT pointing at a GC-allocated mpz.  Assumes
 * an LP64 target (long == int64), which the zig profile pins. */

static KValue *kbig_from_mpz(const mpz_t z) {
  KValue *r = alloc_val(K_BIGINT);
  __mpz_struct *p = (__mpz_struct *)kgc_alloc(sizeof(__mpz_struct));
  mpz_init_set(p, z);
  r->as.big.mpz = p;
  return r;
}

/* Demote to K_INT when the result fits int64, else keep a K_BIGINT. */
static KValue *kfrom_mpz(const mpz_t z) {
  if (mpz_fits_slong_p(z)) return kint((int64_t)mpz_get_si(z));
  return kbig_from_mpz(z);
}

/* Load a K_INT/K_BIGINT into an mpz for a bignum operation. */
static void kload_mpz(KValue *v, mpz_t out) {
  if (v->tag == K_INT) mpz_set_si(out, (long)v->as.i);
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
  if (r->tag != K_CTOR || strcmp(r->as.ctor.name, "__rat") != 0)
    krt_fail("Rational operation on a non-Rational value");
  kload_mpz(r->as.ctor.args[0], num);
  kload_mpz(r->as.ctor.args[1], den);
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

static KValue *the_unit = NULL;
KValue *kunit(void) {
  if (!the_unit) the_unit = alloc_val(K_UNIT);
  return the_unit;
}

/* LR2: the builtin tag ids are shared with codegen (which spells them KCT_*);
 * pin the order so a header edit that desyncs them fails the build, not a
 * pattern match at runtime. */
_Static_assert(KCT_RAT == 8 && KCT_USER_BASE > KCT_RAT,
               "LR2 builtin ctor tag ids must stay pinned and below KCT_USER_BASE");

KValue *kctor(int tagid, const char *name, int argc, KValue **args) {
  KValue *r = alloc_val(K_CTOR);
  r->as.ctor.name = name;
  r->as.ctor.tagid = tagid;   /* LR2 numeric identity for matching */
  r->as.ctor.argc = argc;
  if (argc) {
    KValue **a = (KValue **)kgc_alloc(sizeof(KValue *) * (size_t)argc);
    for (int i = 0; i < argc; i++) a[i] = args[i];
    r->as.ctor.args = a;
  } else {
    r->as.ctor.args = NULL;
  }
  return r;
}

KValue *kctor0(int tagid, const char *name) {
  /* canonicalise the nullary Unit constructor to the single K_UNIT value so
   * Unit has one runtime representation.  kctor_tagid maps K_UNIT->KCT_UNIT,
   * so codegen passing KCT_UNIT here is consistent even though the K_UNIT
   * value carries no ctor.tagid field. */
  if (strcmp(name, "std.prelude.Unit") == 0) return kunit();
  return kctor(tagid, name, 0, NULL);
}

/* The two Bool constructors are immutable nullary ctors; cache them so
 * every comparison/boolean result does not allocate (static = GC root). */
static KValue *the_true = NULL, *the_false = NULL;
KValue *kbool(int b) {
  if (b) { if (!the_true) the_true = kctor0(KCT_TRUE, "std.prelude.True"); return the_true; }
  if (!the_false) the_false = kctor0(KCT_FALSE, "std.prelude.False");
  return the_false;
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

static int prim_is_io(const char *p);
static int prim_arity(const char *p);
static KValue *prim_fire_pure(const char *p, KValue **a);

KValue *kprim(const char *name) {
  /* A nullary pure primitive (e.g. __bytesEmpty) is a value, not a
   * function: fire it immediately rather than leaving a stuck K_PRIM. */
  if (prim_arity(name) == 0 && !prim_is_io(name)) return prim_fire_pure(name, NULL);
  KValue *r = alloc_val(K_PRIM);
  r->as.prim.name = name;
  r->as.prim.argc = 0;
  r->as.prim.args = NULL;
  return r;
}

KValue *kio(KIOFn fn, KEnv *env) {
  KValue *r = alloc_val(K_IO);
  r->as.io.fn = fn;
  r->as.io.env = env;
  return r;
}

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
 * never by name).  The pure builtins are kpf_* extracted from prim_fire_pure;
 * these are the effectful ones the do-kernel sequences. */
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
KValue *kpf_io_ioBind(KValue **a) { KValue *r = krun_io(a[0]); return krun_io(kapp(a[1], r)); }
KValue *kpf_io_ioThen(KValue **a) { (void)krun_io(a[0]); return krun_io(a[1]); }
KValue *kpf_io_newRef(KValue **a) { return kref_new(a[0]); }
KValue *kpf_io_readRef(KValue **a) { return kref_get(a[0]); }
KValue *kpf_io_writeRef(KValue **a) { return kref_set(a[0], a[1]); }

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
int kis_cons(KValue *v) { return v->tag == K_CTOR && v->as.ctor.tagid == KCT_CONS; }

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

/* ── primitive firing ──────────────────────────────────────────────── */

static int prim_is_io(const char *p);
static int prim_arity(const char *p);
static KValue *prim_fire_pure(const char *p, KValue **a);

static KValue *prim_append_arg(KValue *f, KValue *x) {
  int n = f->as.prim.argc;
  KValue *r = alloc_val(K_PRIM);
  r->as.prim.name = f->as.prim.name;
  r->as.prim.argc = n + 1;
  KValue **a = (KValue **)kgc_alloc(sizeof(KValue *) * (size_t)(n + 1));
  for (int i = 0; i < n; i++) a[i] = f->as.prim.args[i];
  a[n] = x;
  r->as.prim.args = a;
  return r;
}

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
  switch (f->tag) {
    case K_CLO:
      return f->as.clo.fn(f->as.clo.env, x);
    case K_PRIM: {
      KValue *r = prim_append_arg(f, x);
      int ar = prim_arity(r->as.prim.name);
      if (r->as.prim.argc >= ar) {
        if (prim_is_io(r->as.prim.name)) return r; /* suspended; runs in krun_io */
        return prim_fire_pure(r->as.prim.name, r->as.prim.args);
      }
      return r; /* still partial */
    }
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
  while (r->tag == K_BOUNCE) {
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

/* Direct application of a named primitive to a contiguous argument array.
 * The common case — a saturated pure primitive — fires in a single call
 * with no intermediate curried K_PRIM boxes or per-argument allocation
 * (the codegen emits this for any application whose spine head is a known
 * primitive).  Partial application, IO primitives (which stay suspended
 * for krun_io), and over-saturation fall back to the curried path. */
KValue *kprim_call(const char *name, int argc, KValue **args) {
  if (argc == prim_arity(name) && !prim_is_io(name))
    return prim_fire_pure(name, args);
  KValue *f = kprim(name);
  for (int i = 0; i < argc; i++) f = kapp(f, args[i]);
  return f;
}

KValue *kappi(KValue *f, KValue *x) {
  switch (f->tag) {
    /* implicit args are erased at runtime for constructors and primitives
     * (§31.2); an implicit lambda is a real binder and is applied. */
    case K_CTOR:
    case K_PRIM:
    case K_NATIVE:
      return f;
    case K_CLO:
      return ktrampoline(f->as.clo.fn(f->as.clo.env, x));
    default:
      krt_fail("kappi: applying a non-function value");
  }
}

/* ── deconstruction ────────────────────────────────────────────────── */

int kctor_is(KValue *v, const char *name) {
  /* Unit has two surface spellings — the canonical K_UNIT value (kunit(),
   * yielded by IO/erased/discarded positions) and the nullary constructor
   * `std.prelude.Unit` — so a `()` pattern must accept either. */
  if (v->tag == K_UNIT) return strcmp(name, "std.prelude.Unit") == 0;
  return v->tag == K_CTOR && strcmp(v->as.ctor.name, name) == 0;
}
/* LR2: the numeric pattern-match dispatch primitive.  Unit's canonical K_UNIT
 * value reports KCT_UNIT (its dual nullary-ctor spelling carries the same id).
 * Any non-constructor value reports -1, which equals no valid tag id, so a
 * ctor pattern test on a non-ctor scrutinee fails — preserving the
 * `v->tag == K_CTOR &&` type guard that kctor_is had. */
int kctor_tagid(KValue *v) {
  if (v->tag == K_UNIT) return KCT_UNIT;
  if (v->tag == K_CTOR) return v->as.ctor.tagid;
  return -1;
}
const char *kctor_name(KValue *v) {
  if (v->tag != K_CTOR) krt_fail("kctor_name: not a constructor");
  return v->as.ctor.name;
}
int kctor_argc(KValue *v) {
  if (v->tag != K_CTOR) krt_fail("kctor_argc: not a constructor");
  return v->as.ctor.argc;
}
KValue *kctor_arg(KValue *v, int i) {
  if (v->tag != K_CTOR || i < 0 || i >= v->as.ctor.argc)
    krt_fail("kctor_arg: out of range");
  return v->as.ctor.args[i];
}

KValue *kproj(KValue *rec, const char *name) {
  if (rec->tag != K_REC) {
    char msg[128];
    snprintf(msg, sizeof msg, "kproj: field '%s' on non-record (tag %d)", name, (int)rec->tag);
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
  return v->tag == K_VARIANT && strcmp(v->as.var.tag, tag) == 0;
}
/* LR2: numeric §13 variant dispatch; -1 for a non-variant value (matches no
 * tag id, so a variant pattern test on a non-variant fails). */
int kvariant_tagid(KValue *v) {
  return v->tag == K_VARIANT ? v->as.var.tagid : -1;
}
int kis_variant(KValue *v) { return v->tag == K_VARIANT; }
KValue *kvariant_payload(KValue *v) {
  if (v->tag != K_VARIANT) krt_fail("kvariant_payload: not a variant");
  return v->as.var.payload;
}

/* §19: force a suspended computation. Delay re-evaluates; Memo caches.
 * A non-thunk value forces to itself (matches the interpreter, which
 * forces through already-evaluated values). */
KValue *kforce(KValue *v) {
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
  if (rec->tag != K_REC) krt_fail("krec_size: not a record");
  return rec->as.rec.n;
}

/* §17.2.5 record rest binder: a new record of `rec`'s fields whose names
 * are NOT among excl[0..nexcl). Kept field names alias the original
 * record's (static) name pointers, so no copying of label strings. */
KValue *krec_without(KValue *rec, int nexcl, const char **excl) {
  if (rec->tag != K_REC) krt_fail("krec_without: not a record");
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
  if (rec->tag != K_REC || i < 0 || i >= rec->as.rec.n)
    krt_fail("krec_at: out of range");
  return rec->as.rec.vals[i];
}

int klit_eq(KValue *a, KValue *b) {
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
  if (v->tag == K_INT) return v->as.i;
  if (v->tag == K_BIGINT) {
    const __mpz_struct *z = (const __mpz_struct *)v->as.big.mpz;
    if (!mpz_fits_slong_p(z)) krt_fail("kas_int: Integer too large for a machine word");
    return (int64_t)mpz_get_si(z);
  }
  krt_fail("kas_int: not an Int");
}
double kas_dbl(KValue *v) {
  if (v->tag != K_DBL) krt_fail("kas_dbl: not a Double");
  return v->as.d;
}
int kas_bool(KValue *v) {
  if (v->tag != K_CTOR) krt_fail("kas_bool: not a Bool");
  if (v->as.ctor.tagid == KCT_TRUE) return 1;
  if (v->as.ctor.tagid == KCT_FALSE) return 0;
  krt_fail("kas_bool: not a Bool constructor");
}

const char *kas_str(KValue *v) {
  if (v->tag != K_STR) krt_fail("kas_str: not a String");
  return v->as.str.p; /* kstr() NUL-terminates; length stays authoritative */
}

void *kas_fgn(KValue *v) {
  if (v->tag != K_FGN) krt_fail("kas_fgn: not a foreign handle");
  return v->as.fgn.p;
}

/* ── references ────────────────────────────────────────────────────── */

KValue *kref_get(KValue *r) {
  if (r->tag != K_REF) krt_fail("kref_get: not a ref");
  return r->as.ref.cell[0];
}
KValue *kref_set(KValue *r, KValue *v) {
  if (r->tag != K_REF) krt_fail("kref_set: not a ref");
  r->as.ref.cell[0] = v;
  return kunit();
}

/* ── pure primitives (mirror Kappa.Eval.evalPurePrim for the subset) ── */

static KValue *show_int_val(KValue *v) {
  if (v->tag == K_INT) {
    char buf[32];
    int n = snprintf(buf, sizeof buf, "%" PRId64, v->as.i);
    return kstr(buf, (size_t)n);
  }
  if (v->tag == K_BIGINT) {
    char *s = mpz_get_str(NULL, 10, (const __mpz_struct *)v->as.big.mpz);
    return kstr0(s); /* s is GC-allocated by the GMP allocator */
  }
  krt_fail("showInt: not an Int");
}

static KValue *str_append(KValue *a, KValue *b) {
  if (a->tag != K_STR || b->tag != K_STR) krt_fail("stringAppend: argument is not a String");
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
  if (v->tag != K_CHR) krt_fail("showScalar: not a scalar");
  sbuf b; sb_init(&b); sb_putc(&b, '\'');
  if (v->as.chr == '\'') sb_puts(&b, "\\'");
  else { int n, s; show_lit_char(&b, v->as.chr, &n, &s); }
  sb_putc(&b, '\''); return sb_to_str(&b);
}

static KValue *show_string_lit(KValue *v) {
  if (v->tag != K_STR) krt_fail("showStringLit: not a String");
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

/* show :: Double, matching Haskell's shortest round-trip + format rules. */
static KValue *show_double(double x) {
  if (isnan(x)) return kstr0("NaN");
  if (isinf(x)) return kstr0(x < 0 ? "-Infinity" : "Infinity");
  if (x == 0.0) return kstr0(signbit(x) ? "-0.0" : "0.0");
  int neg = x < 0; double ax = neg ? -x : x;
  /* shortest digit string that round-trips, via %.*e */
  char ebuf[40]; int prec;
  for (prec = 0; prec <= 17; prec++) {
    snprintf(ebuf, sizeof ebuf, "%.*e", prec, ax);
    if (strtod(ebuf, NULL) == ax) break;
  }
  /* ebuf = "D.FFFe±XX" (or "De±XX" when prec==0) */
  char digits[32]; int nd = 0; int exp10 = 0;
  const char *q = ebuf;
  digits[nd++] = *q++;            /* leading digit D */
  if (*q == '.') { q++; while (*q != 'e' && *q != 'E') digits[nd++] = *q++; }
  q++;                            /* skip 'e' */
  exp10 = (int)strtol(q, NULL, 10);
  /* drop trailing zeros (keep at least one digit) */
  while (nd > 1 && digits[nd - 1] == '0') nd--;
  /* Haskell e = position of the decimal point: value = 0.d1.. * 10^e */
  int e = exp10 + 1;
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
  if (a == b) return 1;
  int ai = a->tag == K_INT || a->tag == K_BIGINT;
  int bi = b->tag == K_INT || b->tag == K_BIGINT;
  if (ai && bi) {
    if (a->tag == K_INT && b->tag == K_INT) return a->as.i == b->as.i;
    mpz_t x, y; mpz_init(x); mpz_init(y); kload_mpz(a, x); kload_mpz(b, y);
    int eq = mpz_cmp(x, y) == 0; mpz_clear(x); mpz_clear(y); return eq;
  }
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
 * (K_INT when it fits a signed 64-bit, else a K_BIGINT). */
static KValue *ku64(uint64_t u) {
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

#define PRIM(n) (strcmp(p, n) == 0)

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
  if (a->tag == K_INT && b->tag == K_INT)
    return a->as.i < b->as.i ? -1 : (a->as.i > b->as.i ? 1 : 0);
  mpz_t za, zb;
  mpz_init(za); mpz_init(zb);
  kload_mpz(a, za); kload_mpz(b, zb);
  return mpz_cmp(za, zb);
}

static int kint_is_zero(KValue *v) {
  if (v->tag == K_INT) return v->as.i == 0;
  return mpz_sgn((const __mpz_struct *)v->as.big.mpz) == 0;
}

/* ── Direct primitive helpers (QW1) ──────────────────────────────────────
 * The hot pure primitives are factored into named, externally-visible
 * helpers so the codegen can emit a DIRECT call (`kp_addInt(x, y)`) for a
 * statically known saturated primitive — no string dispatch, no `prim_arity`
 * / `prim_is_io` check, no per-call argument array.  `prim_fire_pure` (the
 * reflective string-keyed path, used for partial application / dynamic
 * firing) delegates to the same helpers, so there is one source of truth for
 * each primitive's semantics. */
KValue *kp_addInt(KValue *x, KValue *y) {
  int64_t r;
  if (x->tag == K_INT && y->tag == K_INT && !__builtin_add_overflow(x->as.i, y->as.i, &r))
    return kint(r);
  return kint_binop_mpz(x, y, mpz_add);
}
KValue *kp_subInt(KValue *x, KValue *y) {
  int64_t r;
  if (x->tag == K_INT && y->tag == K_INT && !__builtin_sub_overflow(x->as.i, y->as.i, &r))
    return kint(r);
  return kint_binop_mpz(x, y, mpz_sub);
}
KValue *kp_mulInt(KValue *x, KValue *y) {
  int64_t r;
  if (x->tag == K_INT && y->tag == K_INT && !__builtin_mul_overflow(x->as.i, y->as.i, &r))
    return kint(r);
  return kint_binop_mpz(x, y, mpz_mul);
}
KValue *kp_divInt(KValue *x, KValue *y) {
  if (kint_is_zero(y)) krt_fail("divInt: division by zero");
  if (x->tag == K_INT && y->tag == K_INT && !(x->as.i == INT64_MIN && y->as.i == -1))
    return kint(x->as.i / y->as.i); /* C99 trunc toward zero == quot */
  return kint_binop_mpz(x, y, mpz_tdiv_q); /* truncated quotient */
}
KValue *kp_modInt(KValue *x, KValue *y) {
  if (kint_is_zero(y)) krt_fail("modInt: division by zero");
  if (x->tag == K_INT && y->tag == K_INT) {
    if (x->as.i == INT64_MIN && y->as.i == -1) return kint(0);
    return kint(x->as.i % y->as.i); /* C99 % == rem */
  }
  return kint_binop_mpz(x, y, mpz_tdiv_r); /* remainder, sign of dividend */
}
KValue *kp_negInt(KValue *x) {
  if (x->tag == K_INT && x->as.i != INT64_MIN) return kint(-x->as.i);
  mpz_t z, zr;
  mpz_init(z); mpz_init(zr);
  kload_mpz(x, z); mpz_neg(zr, z);
  return kfrom_mpz(zr);
}
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
  if (x->tag != K_STR || y->tag != K_STR) krt_fail("ltStr: argument is not a String");
  size_t la = x->as.str.len, lb = y->as.str.len, m = la < lb ? la : lb;
  int c = memcmp(x->as.str.p, y->as.str.p, m);
  return kbool(c < 0 || (c == 0 && la < lb));
}
KValue *kp_eqScalar(KValue *x, KValue *y) {
  if (x->tag != K_CHR || y->tag != K_CHR) krt_fail("eqScalar: argument is not a scalar");
  return kbool(x->as.chr == y->as.chr);
}
KValue *kp_ltScalar(KValue *x, KValue *y) {
  if (x->tag != K_CHR || y->tag != K_CHR) krt_fail("ltScalar: argument is not a scalar");
  return kbool(x->as.chr < y->as.chr);
}
/* show* (pure, 1-arg): pervasive in numeric output. */
KValue *kp_showInt(KValue *x) { return show_int_val(x); }
KValue *kp_showDouble(KValue *x) { return show_double(kas_dbl(x)); }
KValue *kp_showScalar(KValue *x) { return show_scalar(x); }
KValue *kp_showStringLit(KValue *x) { return show_string_lit(x); }
KValue *kp_intToDouble(KValue *x) {
  if (x->tag == K_BIGINT) return kdbl(mpz_get_d((const __mpz_struct *)x->as.big.mpz));
  return kdbl((double)x->as.i);
}
/* §6.5 byte compares + §29.1 bitwise (hot in hashing / byte loops). */
KValue *kp_eqByte(KValue *x, KValue *y) { return kbool(x->as.byte == y->as.byte); }
KValue *kp_ltByte(KValue *x, KValue *y) { return kbool(x->as.byte < y->as.byte); }
KValue *kp_intAnd(KValue *x, KValue *y) {
  if (x->tag == K_INT && y->tag == K_INT) return kint(x->as.i & y->as.i);
  mpz_t a, b, r; mpz_init(a); mpz_init(b); mpz_init(r); kload_mpz(x, a); kload_mpz(y, b);
  mpz_and(r, a, b); KValue *res = kfrom_mpz(r); mpz_clear(a); mpz_clear(b); mpz_clear(r); return res;
}
KValue *kp_intOr(KValue *x, KValue *y) {
  if (x->tag == K_INT && y->tag == K_INT) return kint(x->as.i | y->as.i);
  mpz_t a, b, r; mpz_init(a); mpz_init(b); mpz_init(r); kload_mpz(x, a); kload_mpz(y, b);
  mpz_ior(r, a, b); KValue *res = kfrom_mpz(r); mpz_clear(a); mpz_clear(b); mpz_clear(r); return res;
}
KValue *kp_intXor(KValue *x, KValue *y) {
  if (x->tag == K_INT && y->tag == K_INT) return kint(x->as.i ^ y->as.i);
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
  if (a[0]->tag == K_INT ? a[0]->as.i < 0
                           : mpz_sgn((const __mpz_struct *)a[0]->as.big.mpz) < 0)
      krt_fail("intToNat: negative Int has no Nat image");
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
    KValue *ns = show_int_val(a[0]->as.ctor.args[0]);
    if (mpz_cmp_ui(d, 1) == 0) return ns;
    return str_append(str_append(ns, kstr0("/")), show_int_val(a[0]->as.ctor.args[1]));
}
KValue *kpf_ratOfDouble(KValue **a) {
  double x = kas_dbl(a[0]);
    if (isnan(x) || isinf(x)) { mpz_t n, d; mpz_init(n); mpz_init_set_ui(d, 1); return krat(n, d); }
    int e2; double frac = frexp(x, &e2);            /* x = frac * 2^e2, 0.5<=|frac|<1 */
    long long mant = (long long)ldexp(frac, 53);    /* exact integer significand */
    int sh = e2 - 53;
    mpz_t n, d; mpz_init_set_si(n, (long)mant); mpz_init_set_ui(d, 1);
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
    if (a[0]->tag == K_CHR) {
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

static KValue *prim_fire_pure(const char *p, KValue **a) {
  if (PRIM("addInt")) return kpf_addInt(a);
  if (PRIM("subInt")) return kpf_subInt(a);
  if (PRIM("mulInt")) return kpf_mulInt(a);
  if (PRIM("divInt")) return kpf_divInt(a);
  if (PRIM("modInt")) return kpf_modInt(a);
  if (PRIM("negInt")) return kpf_negInt(a);
  if (PRIM("eqInt")) return kpf_eqInt(a);
  if (PRIM("ltInt")) return kpf_ltInt(a);
  if (PRIM("leInt")) return kpf_leInt(a);
  if (PRIM("addDouble")) return kpf_addDouble(a);
  if (PRIM("subDouble")) return kpf_subDouble(a);
  if (PRIM("mulDouble")) return kpf_mulDouble(a);
  if (PRIM("divDouble")) return kpf_divDouble(a);
  if (PRIM("negDouble")) return kpf_negDouble(a);
  if (PRIM("ltDouble")) return kpf_ltDouble(a);
  if (PRIM("floatEq")) return kpf_floatEq(a);
  if (PRIM("eqDouble")) return kpf_eqDouble(a);
  if (PRIM("stringAppend")) return kpf_stringAppend(a);
  if (PRIM("eqStr")) return kpf_eqStr(a);
  if (PRIM("ltStr")) return kpf_ltStr(a);
  if (PRIM("eqScalar")) return kpf_eqScalar(a);
  if (PRIM("ltScalar")) return kpf_ltScalar(a);
  if (PRIM("natToInt") || PRIM("natOfInt")) return kpf_natToInt(a);
  if (PRIM("intToNat")) return kpf_intToNat(a);
  if (PRIM("intToDouble")) return kpf_intToDouble(a);
  if (PRIM("primitiveIntToString")) return kpf_primitiveIntToString(a);
  if (PRIM("showInt")) return kpf_showInt(a);
  if (PRIM("showDouble")) return kpf_showDouble(a);
  if (PRIM("showScalar")) return kpf_showScalar(a);
  if (PRIM("showStringLit")) return kpf_showStringLit(a);
  if (PRIM("__ratOfInt")) return kpf___ratOfInt(a);
  if (PRIM("__ratNum")) return kpf___ratNum(a);
  if (PRIM("__ratDen")) return kpf___ratDen(a);
  if (PRIM("addRat")) return kpf_addRat(a);
  if (PRIM("subRat")) return kpf_subRat(a);
  if (PRIM("mulRat")) return kpf_mulRat(a);
  if (PRIM("divRat")) return kpf_divRat(a);
  if (PRIM("negRat")) return kpf_negRat(a);
  if (PRIM("eqRat")) return kpf_eqRat(a); if (PRIM("ltRat")) return kpf_ltRat(a);
  if (PRIM("showRat")) return kpf_showRat(a);
  if (PRIM("ratOfDouble")) return kpf_ratOfDouble(a);
  if (PRIM("eqByte")) return kpf_eqByte(a);
  if (PRIM("ltByte")) return kpf_ltByte(a);
  if (PRIM("showByte")) return kpf_showByte(a);
  if (PRIM("eqBytes")) return kpf_eqBytes(a);
  if (PRIM("ltBytes")) return kpf_ltBytes(a);
  if (PRIM("showBytes")) return kpf_showBytes(a);
  if (PRIM("eqGrapheme")) return kpf_eqGrapheme(a);
  if (PRIM("showGrapheme")) return kpf_showGrapheme(a);
  if (PRIM("__bytesEmpty")) return kpf___bytesEmpty(a);
  if (PRIM("__bytesSingleton")) return kpf___bytesSingleton(a);
  if (PRIM("__bytesLength")) return kpf___bytesLength(a);
  if (PRIM("__bytesIsEmpty")) return kpf___bytesIsEmpty(a);
  if (PRIM("__bytesGet")) return kpf___bytesGet(a);
  if (PRIM("__bytesIndexUnsafe")) return kpf___bytesIndexUnsafe(a);
  if (PRIM("__bytesAppend")) return kpf___bytesAppend(a);
  if (PRIM("__bytesSlice")) return kpf___bytesSlice(a);
  if (PRIM("__bytesTake")) return kpf___bytesTake(a);
  if (PRIM("__bytesDrop")) return kpf___bytesDrop(a);
  if (PRIM("__bytesStartsWith")) return kpf___bytesStartsWith(a);
  if (PRIM("__bytesEndsWith")) return kpf___bytesEndsWith(a);
  if (PRIM("__bytesContains")) return kpf___bytesContains(a);
  if (PRIM("__bytesFind")) return kpf___bytesFind(a);
  if (PRIM("__bytesBreakIndex")) return kpf___bytesBreakIndex(a);
  if (PRIM("__bytesToList")) return kpf___bytesToList(a);
  if (PRIM("__bytesFromList")) return kpf___bytesFromList(a);
  if (PRIM("__bytesCompact")) return kpf___bytesCompact(a);
  if (PRIM("__newBytesBuilder")) return kpf___newBytesBuilder(a);
  if (PRIM("__bytesBuilderByte")) return kpf___bytesBuilderByte(a);
  if (PRIM("__bytesBuilderBytes")) return kpf___bytesBuilderBytes(a);
  if (PRIM("__finishBytesBuilder")) return kpf___finishBytesBuilder(a);
  if (PRIM("__utf8Bytes")) return kpf___utf8Bytes(a);
  if (PRIM("__utf8Valid")) return kpf___utf8Valid(a);
  if (PRIM("__decodeUtf8Lossy")) return kpf___decodeUtf8Lossy(a);
  if (PRIM("__byteLength")) return kpf___byteLength(a);
  if (PRIM("__uniScalarValue")) return kpf___uniScalarValue(a);
  if (PRIM("__scalarInRange")) return kpf___scalarInRange(a);
  if (PRIM("__scalarOfValue")) return kpf___scalarOfValue(a);
  if (PRIM("__scalarToString")) return kpf___scalarToString(a);
  if (PRIM("__scalarCount")) return kpf___scalarCount(a);
  if (PRIM("__stringScalars")) return kpf___stringScalars(a);
  if (PRIM("__byteToNat")) return kpf___byteToNat(a);
  if (PRIM("__natToByte")) return kpf___natToByte(a);
  if (PRIM("__graphemeToString")) return kpf___graphemeToString(a);
  if (PRIM("__queryFromList") || PRIM("__queryToList") || PRIM("__setFromList") || PRIM("__setToList") || PRIM("__arrayFromList") || PRIM("__arrayToList") || PRIM("__mapFromEntries") || PRIM("__mapToList") || PRIM("__transport") || PRIM("__stringCompact")) return kpf___queryFromList(a);
  if (PRIM("unsafeConsume")) return kpf_unsafeConsume(a);
  if (PRIM("__arrayIndexUnsafe")) return kpf___arrayIndexUnsafe(a);
  if (PRIM("__rangeEnum")) return kpf___rangeEnum(a);
  if (PRIM("__intAnd")) return kpf___intAnd(a);
  if (PRIM("__intOr")) return kpf___intOr(a);
  if (PRIM("__intXor")) return kpf___intXor(a);
  if (PRIM("__hashMixInt")) return kpf___hashMixInt(a);
  if (PRIM("__hashMixDouble")) return kpf___hashMixDouble(a);
  if (PRIM("__hashMixString")) return kpf___hashMixString(a);
  if (PRIM("__hashMixBytes")) return kpf___hashMixBytes(a);
  if (PRIM("__newStringBuilder")) return kpf___newStringBuilder(a);
  if (PRIM("__stringBuilderString")) return kpf___stringBuilderString(a);
  if (PRIM("__stringBuilderScalar")) return kpf___stringBuilderScalar(a);
  if (PRIM("__stringBuilderGrapheme")) return kpf___stringBuilderGrapheme(a);
  if (PRIM("__finishStringBuilder")) return kpf___finishStringBuilder(a);
  if (PRIM("__stringStart")) return kpf___stringStart(a);
  if (PRIM("__stringEnd")) return kpf___stringEnd(a);
  if (PRIM("__stringCursorOffset")) return kpf___stringCursorOffset(a);
  if (PRIM("__stringNextScalar")) return kpf___stringNextScalar(a);
  if (PRIM("__stringPrevScalar")) return kpf___stringPrevScalar(a);
  if (PRIM("__stringSpan")) return kpf___stringSpan(a);
  if (PRIM("__newUtf8Decoder")) return kpf___newUtf8Decoder(a);
  if (PRIM("__decodeUtf8Chunk")) return kpf___decodeUtf8Chunk(a);
  if (PRIM("__finishUtf8Decoder")) return kpf___finishUtf8Decoder(a);
  if (PRIM("__atomicRepEq")) return kpf___atomicRepEq(a);
  if (PRIM("__normalize")) return kpf___normalize(a);
  if (PRIM("__caseFold")) return kpf___caseFold(a);
  if (PRIM("__graphemeCount")) return kpf___graphemeCount(a);
  if (PRIM("__graphemeValid")) return kpf___graphemeValid(a);
  if (PRIM("__graphemeOfString")) return kpf___graphemeOfString(a);
  if (PRIM("__stringGraphemes")) return kpf___stringGraphemes(a);
  if (PRIM("__stringNextGrapheme")) return kpf___stringNextGrapheme(a);
  if (PRIM("__stringWords")) return kpf___stringWords(a);
  if (PRIM("__stringSentences")) return kpf___stringSentences(a);
  krt_fail("internal: unknown pure primitive");
}

/* ── IO execution ──────────────────────────────────────────────────── */

/* A heap stack of pending §18.7 finalizers (see kio_finally / krun_io). */
struct kdefer_frame { KValue **defers; int n; struct kdefer_frame *next; };

/* Run the accumulated finalizers LIFO (innermost scope first, last-
 * registered first within a scope) once a tail recursion reaches a value,
 * then return that value (or Unit when a K_IOEFFECT discarded it). */
static KValue *krun_finish(KValue *v, int discard, struct kdefer_frame *fr) {
  for (; fr; fr = fr->next)
    for (int i = fr->n - 1; i >= 0; i--) (void)krun_io(fr->defers[i]);
  return discard ? kunit() : v;
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
      if (r->tag == K_IOTAIL) { action = r->as.bounce.fn; continue; }
      if (r->tag == K_IOEFFECT) { discard = 1; action = r->as.bounce.fn; continue; }
      if (r->tag == K_IOFINALLY) {
        struct kdefer_frame *f = (struct kdefer_frame *)kgc_alloc(sizeof *f);
        f->defers = r->as.iofin.defers; f->n = r->as.iofin.n; f->next = defers;
        defers = f; action = r->as.iofin.action; continue;
      }
      return krun_finish(r, discard, defers);
    }
    case K_PRIM: {
      const char *p = action->as.prim.name;
      KValue **a = action->as.prim.args;
      if (PRIM("printString")) {
        if (a[0]->tag != K_STR) krt_fail("printString: argument is not a String");
        fwrite(a[0]->as.str.p, 1, a[0]->as.str.len, stdout);
        return krun_finish(kunit(), discard, defers);
      }
      if (PRIM("printlnString")) {
        if (a[0]->tag != K_STR) krt_fail("printlnString: argument is not a String");
        fwrite(a[0]->as.str.p, 1, a[0]->as.str.len, stdout);
        fputc('\n', stdout);
        return krun_finish(kunit(), discard, defers);
      }
      if (PRIM("ioPure")) return krun_finish(a[0], discard, defers);
      if (PRIM("ioBind")) {
        KValue *r = krun_io(a[0]);
        action = kapp(a[1], r);      /* tail: continue the loop */
        continue;
      }
      if (PRIM("ioThen")) {
        (void)krun_io(a[0]);
        action = a[1];               /* tail: continue the loop */
        continue;
      }
      if (PRIM("newRef")) return krun_finish(kref_new(a[0]), discard, defers);
      if (PRIM("readRef")) return krun_finish(kref_get(a[0]), discard, defers);
      if (PRIM("writeRef")) return krun_finish(kref_set(a[0], a[1]), discard, defers);
      krt_fail("internal: unknown IO primitive (native host bindings run as K_NATIVE)");
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
      /* a pure value used in IO position (e.g. a `return`ed result) */
      return krun_finish(action, discard, defers);
  }
  }
}

/* ── primitive tables ──────────────────────────────────────────────── */

static int prim_is_io(const char *p) {
  return PRIM("printString") || PRIM("printlnString") || PRIM("ioPure") ||
         PRIM("ioBind") || PRIM("ioThen") || PRIM("newRef") ||
         PRIM("readRef") || PRIM("writeRef");
}

static int prim_arity(const char *p) {
  /* hot path: the arithmetic / comparison ops that dominate numeric loops
   * are matched first so kprim_call's saturation check is a few strcmps,
   * not a full scan (they also appear in the binary block below — the
   * first match wins, so this is purely an ordering optimisation). */
  if (PRIM("addInt") || PRIM("subInt") || PRIM("mulInt") || PRIM("divInt") ||
      PRIM("modInt") || PRIM("eqInt") || PRIM("ltInt") || PRIM("leInt")) return 2;
  /* nullary (a value, fired on reference) */
  if (PRIM("__bytesEmpty") || PRIM("__newBytesBuilder") ||
      PRIM("__newStringBuilder") || PRIM("__newUtf8Decoder")) return 0;
  /* unary */
  if (PRIM("negInt") || PRIM("negDouble") || PRIM("showInt") ||
      PRIM("showDouble") || PRIM("showScalar") || PRIM("showStringLit") ||
      PRIM("__ratOfInt") || PRIM("__ratNum") || PRIM("__ratDen") ||
      PRIM("negRat") || PRIM("showRat") || PRIM("ratOfDouble") ||
      PRIM("natToInt") || PRIM("natOfInt") || PRIM("intToNat") ||
      PRIM("intToDouble") || PRIM("primitiveIntToString") ||
      PRIM("showByte") || PRIM("showBytes") || PRIM("showGrapheme") ||
      PRIM("__bytesSingleton") || PRIM("__bytesLength") || PRIM("__bytesIsEmpty") ||
      PRIM("__bytesToList") || PRIM("__bytesFromList") || PRIM("__bytesCompact") ||
      PRIM("__finishBytesBuilder") ||
      PRIM("__utf8Bytes") || PRIM("__utf8Valid") || PRIM("__decodeUtf8Lossy") ||
      PRIM("__byteLength") || PRIM("__uniScalarValue") || PRIM("__scalarInRange") ||
      PRIM("__scalarOfValue") || PRIM("__scalarToString") || PRIM("__scalarCount") ||
      PRIM("__stringScalars") || PRIM("__byteToNat") || PRIM("__natToByte") ||
      PRIM("__graphemeToString") || PRIM("__stringCompact") ||
      PRIM("__caseFold") || PRIM("__graphemeCount") || PRIM("__graphemeValid") ||
      PRIM("__graphemeOfString") || PRIM("__stringGraphemes") ||
      PRIM("__stringWords") || PRIM("__stringSentences") ||
      PRIM("__queryFromList") || PRIM("__queryToList") || PRIM("__setFromList") ||
      PRIM("__setToList") || PRIM("__arrayFromList") || PRIM("__arrayToList") ||
      PRIM("__mapFromEntries") || PRIM("__mapToList") || PRIM("__transport") ||
      PRIM("__stringStart") || PRIM("__stringEnd") || PRIM("__finishStringBuilder") ||
      PRIM("__finishUtf8Decoder") ||
      PRIM("ioPure") || PRIM("newRef") || PRIM("readRef") ||
      PRIM("printString") || PRIM("printlnString"))
    return 1;
  /* ternary */
  if (PRIM("__bytesSlice") || PRIM("__rangeEnum") || PRIM("__stringSpan")) return 3;
  /* binary (all remaining pure ops + ioBind/ioThen/writeRef) */
  if (PRIM("addInt") || PRIM("subInt") || PRIM("mulInt") || PRIM("divInt") ||
      PRIM("modInt") || PRIM("eqInt") || PRIM("ltInt") || PRIM("leInt") ||
      PRIM("addDouble") || PRIM("subDouble") || PRIM("mulDouble") ||
      PRIM("divDouble") || PRIM("eqDouble") || PRIM("ltDouble") ||
      PRIM("floatEq") || PRIM("stringAppend") || PRIM("eqStr") ||
      PRIM("ltStr") || PRIM("eqScalar") || PRIM("ltScalar") ||
      PRIM("addRat") || PRIM("subRat") || PRIM("mulRat") || PRIM("divRat") ||
      PRIM("eqRat") || PRIM("ltRat") ||
      PRIM("eqByte") || PRIM("ltByte") || PRIM("eqBytes") || PRIM("ltBytes") ||
      PRIM("eqGrapheme") || PRIM("__bytesGet") || PRIM("__bytesIndexUnsafe") ||
      PRIM("__bytesAppend") || PRIM("__bytesStartsWith") || PRIM("__bytesEndsWith") ||
      PRIM("__bytesContains") || PRIM("__bytesFind") || PRIM("__bytesBreakIndex") ||
      PRIM("__bytesTake") || PRIM("__bytesDrop") ||
      PRIM("__bytesBuilderByte") || PRIM("__bytesBuilderBytes") ||
      PRIM("__intAnd") || PRIM("__intOr") || PRIM("__intXor") ||
      PRIM("__hashMixInt") || PRIM("__hashMixDouble") || PRIM("__hashMixString") ||
      PRIM("__hashMixBytes") || PRIM("__arrayIndexUnsafe") || PRIM("unsafeConsume") ||
      PRIM("__stringBuilderString") || PRIM("__stringBuilderScalar") ||
      PRIM("__stringBuilderGrapheme") || PRIM("__stringCursorOffset") ||
      PRIM("__stringNextScalar") || PRIM("__stringPrevScalar") ||
      PRIM("__decodeUtf8Chunk") ||
      PRIM("__normalize") || PRIM("__stringNextGrapheme") ||
      PRIM("__atomicRepEq") ||
      PRIM("ioBind") || PRIM("ioThen") || PRIM("writeRef"))
    return 2;
  krt_fail("internal: unknown primitive arity");
}
