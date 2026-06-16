/* kappart.c — Kappa native runtime implementation.  See kappart.h and
 * docs/NATIVE_BACKEND.md.  The primitive set implemented here is kept in
 * lock-step with the supported-primitive table in Kappa.Backend.C: the
 * code generator refuses (E_BACKEND_UNSUPPORTED) any primitive this file
 * does not implement, so an unimplemented primitive is a compile-time
 * error, never a silent runtime divergence. */
#include "kappart.h"

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

void krt_init(void) {
  GC_INIT();
  mp_set_memory_functions(gmp_gc_alloc, gmp_gc_realloc, gmp_gc_free);
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

/* ── value constructors ────────────────────────────────────────────── */

KValue *kint(int64_t v) {
  KValue *r = alloc_val(K_INT);
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

KValue *kdbl(double v) {
  KValue *r = alloc_val(K_DBL);
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
  KValue *r = alloc_val(K_CHR);
  r->as.chr = scalar;
  return r;
}

static KValue *the_unit = NULL;
KValue *kunit(void) {
  if (!the_unit) the_unit = alloc_val(K_UNIT);
  return the_unit;
}

KValue *kctor(const char *name, int argc, KValue **args) {
  KValue *r = alloc_val(K_CTOR);
  r->as.ctor.name = name;
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

KValue *kctor0(const char *name) { return kctor(name, 0, NULL); }

KValue *kbool(int b) {
  return kctor0(b ? "std.prelude.True" : "std.prelude.False");
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

KValue *kprim(const char *name) {
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

KValue *kinject(const char *tag, KValue *payload) {
  KValue *r = alloc_val(K_VARIANT);
  r->as.var.tag = tag;          /* a generated static string literal */
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

/* lists */
KValue *knil(void) { return kctor0("std.prelude.Nil"); }
KValue *kcons(KValue *h, KValue *t) {
  KValue *args[2] = {h, t};
  return kctor("std.prelude.::", 2, args);
}
int kis_cons(KValue *v) { return v->tag == K_CTOR && strcmp(v->as.ctor.name, "std.prelude.::") == 0; }

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
  return r;
}

KValue *kbounce(KValue *fn, KValue *arg) {
  KValue *r = alloc_val(K_BOUNCE);
  r->as.bounce.fn = fn;
  r->as.bounce.arg = arg;
  return r;
}

KValue *kapp(KValue *f, KValue *x) { return ktrampoline(kapply_once(f, x)); }

KValue *kappi(KValue *f, KValue *x) {
  switch (f->tag) {
    /* implicit args are erased at runtime for constructors and primitives
     * (§31.2); an implicit lambda is a real binder and is applied. */
    case K_CTOR:
    case K_PRIM:
      return f;
    case K_CLO:
      return ktrampoline(f->as.clo.fn(f->as.clo.env, x));
    default:
      krt_fail("kappi: applying a non-function value");
  }
}

/* ── deconstruction ────────────────────────────────────────────────── */

int kctor_is(KValue *v, const char *name) {
  return v->tag == K_CTOR && strcmp(v->as.ctor.name, name) == 0;
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
  if (rec->tag != K_REC) krt_fail("kproj: not a record");
  for (int i = 0; i < rec->as.rec.n; i++)
    if (strcmp(rec->as.rec.names[i], name) == 0) return rec->as.rec.vals[i];
  krt_fail("kproj: no such field");
}

int kvariant_is(KValue *v, const char *tag) {
  return v->tag == K_VARIANT && strcmp(v->as.var.tag, tag) == 0;
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
  if (strcmp(v->as.ctor.name, "std.prelude.True") == 0) return 1;
  if (strcmp(v->as.ctor.name, "std.prelude.False") == 0) return 0;
  krt_fail("kas_bool: not a Bool constructor");
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

/* decode the next UTF-8 scalar from p (< end); returns bytes consumed. */
static int utf8_next(const unsigned char *p, const unsigned char *end, uint32_t *cp) {
  unsigned c = p[0];
  if (c < 0x80) { *cp = c; return 1; }
  if ((c >> 5) == 0x6 && p + 1 < end + 1 && p + 1 <= end) { *cp = ((c & 0x1f) << 6) | (p[1] & 0x3f); return 2; }
  if ((c >> 4) == 0xe) { *cp = ((c & 0x0f) << 12) | ((p[1] & 0x3f) << 6) | (p[2] & 0x3f); return 3; }
  if ((c >> 3) == 0x1e) { *cp = ((c & 0x07) << 18) | ((p[1] & 0x3f) << 12) | ((p[2] & 0x3f) << 6) | (p[3] & 0x3f); return 4; }
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

static KValue *prim_fire_pure(const char *p, KValue **a) {
  /* integer.  Int/Integer are unbounded (§6): the int64 inline form is a
   * fast path; on overflow or a bignum operand the operation promotes to a
   * GMP bignum, so results never wrap or trap (matching the interpreter). */
  if (PRIM("addInt")) {
    int64_t r;
    if (a[0]->tag == K_INT && a[1]->tag == K_INT
        && !__builtin_add_overflow(a[0]->as.i, a[1]->as.i, &r))
      return kint(r);
    return kint_binop_mpz(a[0], a[1], mpz_add);
  }
  if (PRIM("subInt")) {
    int64_t r;
    if (a[0]->tag == K_INT && a[1]->tag == K_INT
        && !__builtin_sub_overflow(a[0]->as.i, a[1]->as.i, &r))
      return kint(r);
    return kint_binop_mpz(a[0], a[1], mpz_sub);
  }
  if (PRIM("mulInt")) {
    int64_t r;
    if (a[0]->tag == K_INT && a[1]->tag == K_INT
        && !__builtin_mul_overflow(a[0]->as.i, a[1]->as.i, &r))
      return kint(r);
    return kint_binop_mpz(a[0], a[1], mpz_mul);
  }
  if (PRIM("divInt")) {
    if (kint_is_zero(a[1])) krt_fail("divInt: division by zero");
    if (a[0]->tag == K_INT && a[1]->tag == K_INT && !(a[0]->as.i == INT64_MIN && a[1]->as.i == -1))
      return kint(a[0]->as.i / a[1]->as.i); /* C99 trunc toward zero == quot */
    return kint_binop_mpz(a[0], a[1], mpz_tdiv_q); /* truncated quotient */
  }
  if (PRIM("modInt")) {
    if (kint_is_zero(a[1])) krt_fail("modInt: division by zero");
    if (a[0]->tag == K_INT && a[1]->tag == K_INT) {
      if (a[0]->as.i == INT64_MIN && a[1]->as.i == -1) return kint(0);
      return kint(a[0]->as.i % a[1]->as.i); /* C99 % == rem */
    }
    return kint_binop_mpz(a[0], a[1], mpz_tdiv_r); /* remainder, sign of dividend */
  }
  if (PRIM("negInt")) {
    if (a[0]->tag == K_INT && a[0]->as.i != INT64_MIN) return kint(-a[0]->as.i);
    mpz_t z, zr;
    mpz_init(z); mpz_init(zr);
    kload_mpz(a[0], z); mpz_neg(zr, z);
    return kfrom_mpz(zr);
  }
  if (PRIM("eqInt")) return kbool(kint_cmp(a[0], a[1]) == 0);
  if (PRIM("ltInt")) return kbool(kint_cmp(a[0], a[1]) < 0);
  if (PRIM("leInt")) return kbool(kint_cmp(a[0], a[1]) <= 0);
  /* double */
  if (PRIM("addDouble")) return kdbl(kas_dbl(a[0]) + kas_dbl(a[1]));
  if (PRIM("subDouble")) return kdbl(kas_dbl(a[0]) - kas_dbl(a[1]));
  if (PRIM("mulDouble")) return kdbl(kas_dbl(a[0]) * kas_dbl(a[1]));
  if (PRIM("divDouble")) return kdbl(kas_dbl(a[0]) / kas_dbl(a[1]));
  if (PRIM("negDouble")) return kdbl(-kas_dbl(a[0]));
  if (PRIM("ltDouble")) return kbool(kas_dbl(a[0]) < kas_dbl(a[1]));
  if (PRIM("floatEq")) return kbool(kas_dbl(a[0]) == kas_dbl(a[1]));
  if (PRIM("eqDouble")) { /* §6.1.3 raw-bit equality */
    uint64_t x, y;
    double da = kas_dbl(a[0]), db = kas_dbl(a[1]);
    memcpy(&x, &da, 8); memcpy(&y, &db, 8);
    return kbool(x == y);
  }
  /* string / scalar */
  if (PRIM("stringAppend")) return str_append(a[0], a[1]);
  if (PRIM("eqStr")) return kbool(klit_eq(a[0], a[1]));
  if (PRIM("ltStr")) {
    if (a[0]->tag != K_STR || a[1]->tag != K_STR) krt_fail("ltStr: argument is not a String");
    size_t la = a[0]->as.str.len, lb = a[1]->as.str.len, m = la < lb ? la : lb;
    int c = memcmp(a[0]->as.str.p, a[1]->as.str.p, m);
    return kbool(c < 0 || (c == 0 && la < lb));
  }
  if (PRIM("eqScalar")) {
    if (a[0]->tag != K_CHR || a[1]->tag != K_CHR) krt_fail("eqScalar: argument is not a scalar");
    return kbool(a[0]->as.chr == a[1]->as.chr);
  }
  if (PRIM("ltScalar")) {
    if (a[0]->tag != K_CHR || a[1]->tag != K_CHR) krt_fail("ltScalar: argument is not a scalar");
    return kbool(a[0]->as.chr < a[1]->as.chr);
  }
  /* show */
  if (PRIM("showInt")) return show_int_val(a[0]);
  if (PRIM("showDouble")) return show_double(kas_dbl(a[0]));
  if (PRIM("showScalar")) return show_scalar(a[0]);
  if (PRIM("showStringLit")) return show_string_lit(a[0]);
  krt_fail("internal: unknown pure primitive");
}

/* ── IO execution ──────────────────────────────────────────────────── */

KValue *krun_io(KValue *action) {
  switch (action->tag) {
    case K_IO:
      return action->as.io.fn(action->as.io.env);
    case K_PRIM: {
      const char *p = action->as.prim.name;
      KValue **a = action->as.prim.args;
      if (PRIM("printString")) {
        if (a[0]->tag != K_STR) krt_fail("printString: argument is not a String");
        fwrite(a[0]->as.str.p, 1, a[0]->as.str.len, stdout);
        return kunit();
      }
      if (PRIM("printlnString")) {
        if (a[0]->tag != K_STR) krt_fail("printlnString: argument is not a String");
        fwrite(a[0]->as.str.p, 1, a[0]->as.str.len, stdout);
        fputc('\n', stdout);
        return kunit();
      }
      if (PRIM("ioPure")) return a[0];
      if (PRIM("ioBind")) {
        KValue *r = krun_io(a[0]);
        return krun_io(kapp(a[1], r));
      }
      if (PRIM("ioThen")) {
        (void)krun_io(a[0]);
        return krun_io(a[1]);
      }
      if (PRIM("newRef")) return kref_new(a[0]);
      if (PRIM("readRef")) return kref_get(a[0]);
      if (PRIM("writeRef")) return kref_set(a[0], a[1]);
      /* FFI IO primitives are registered by the FFI runtime (kappart_ffi). */
      return krun_io_ffi(action);
    }
    default:
      /* a pure value used in IO position (e.g. a `return`ed result) */
      return action;
  }
}

/* ── primitive tables ──────────────────────────────────────────────── */

static int prim_is_io(const char *p) {
  return PRIM("printString") || PRIM("printlnString") || PRIM("ioPure") ||
         PRIM("ioBind") || PRIM("ioThen") || PRIM("newRef") ||
         PRIM("readRef") || PRIM("writeRef") || prim_is_io_ffi(p);
}

static int prim_arity(const char *p) {
  /* unary */
  if (PRIM("negInt") || PRIM("negDouble") || PRIM("showInt") ||
      PRIM("showDouble") || PRIM("showScalar") || PRIM("showStringLit") ||
      PRIM("ioPure") || PRIM("newRef") || PRIM("readRef") ||
      PRIM("printString") || PRIM("printlnString"))
    return 1;
  /* binary (all remaining pure ops + ioBind/ioThen/writeRef) */
  if (PRIM("addInt") || PRIM("subInt") || PRIM("mulInt") || PRIM("divInt") ||
      PRIM("modInt") || PRIM("eqInt") || PRIM("ltInt") || PRIM("leInt") ||
      PRIM("addDouble") || PRIM("subDouble") || PRIM("mulDouble") ||
      PRIM("divDouble") || PRIM("eqDouble") || PRIM("ltDouble") ||
      PRIM("floatEq") || PRIM("stringAppend") || PRIM("eqStr") ||
      PRIM("ltStr") || PRIM("eqScalar") || PRIM("ltScalar") ||
      PRIM("ioBind") || PRIM("ioThen") || PRIM("writeRef"))
    return 2;
  return prim_arity_ffi(p);
}
