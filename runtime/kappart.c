/* kappart.c — Kappa native runtime implementation.  See kappart.h and
 * docs/NATIVE_BACKEND.md.  The primitive set implemented here is kept in
 * lock-step with the supported-primitive table in Kappa.Backend.C: the
 * code generator refuses (E_BACKEND_UNSUPPORTED) any primitive this file
 * does not implement, so an unimplemented primitive is a compile-time
 * error, never a silent runtime divergence. */
#include "kappart.h"

#include <gc.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ── lifecycle / allocation ────────────────────────────────────────── */

void krt_init(void) { GC_INIT(); }

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

KValue *kapp(KValue *f, KValue *x) {
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

KValue *kappi(KValue *f, KValue *x) {
  switch (f->tag) {
    /* implicit args are erased at runtime for constructors and primitives
     * (§31.2); an implicit lambda is a real binder and is applied. */
    case K_CTOR:
    case K_PRIM:
      return f;
    case K_CLO:
      return f->as.clo.fn(f->as.clo.env, x);
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

int krec_size(KValue *rec) {
  if (rec->tag != K_REC) krt_fail("krec_size: not a record");
  return rec->as.rec.n;
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
  if (v->tag != K_INT) krt_fail("kas_int: not an Int");
  return v->as.i;
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

static KValue *show_int(int64_t v) {
  char buf[32];
  int n = snprintf(buf, sizeof buf, "%" PRId64, v);
  return kstr(buf, (size_t)n);
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

#define PRIM(n) (strcmp(p, n) == 0)

static KValue *prim_fire_pure(const char *p, KValue **a) {
  /* integer.  The native Int is 64-bit (documented in NATIVE_BACKEND.md);
   * the spec's Int/Integer are unbounded, so an operation whose exact
   * result exceeds 64 bits is a clean runtime trap here rather than a
   * silent wraparound (which would diverge from the interpreter). */
  if (PRIM("addInt")) {
    int64_t r;
    if (__builtin_add_overflow(kas_int(a[0]), kas_int(a[1]), &r))
      krt_fail("addInt: 64-bit integer overflow (native Int is 64-bit)");
    return kint(r);
  }
  if (PRIM("subInt")) {
    int64_t r;
    if (__builtin_sub_overflow(kas_int(a[0]), kas_int(a[1]), &r))
      krt_fail("subInt: 64-bit integer overflow (native Int is 64-bit)");
    return kint(r);
  }
  if (PRIM("mulInt")) {
    int64_t r;
    if (__builtin_mul_overflow(kas_int(a[0]), kas_int(a[1]), &r))
      krt_fail("mulInt: 64-bit integer overflow (native Int is 64-bit)");
    return kint(r);
  }
  if (PRIM("divInt")) {
    int64_t x = kas_int(a[0]), d = kas_int(a[1]);
    if (d == 0) krt_fail("divInt: division by zero");
    if (x == INT64_MIN && d == -1) krt_fail("divInt: 64-bit integer overflow");
    return kint(x / d); /* C99 trunc toward zero == quot */
  }
  if (PRIM("modInt")) {
    int64_t x = kas_int(a[0]), d = kas_int(a[1]);
    if (d == 0) krt_fail("modInt: division by zero");
    if (x == INT64_MIN && d == -1) return kint(0);
    return kint(x % d); /* C99 % == rem */
  }
  if (PRIM("negInt")) {
    int64_t x = kas_int(a[0]);
    if (x == INT64_MIN) krt_fail("negInt: 64-bit integer overflow");
    return kint(-x);
  }
  if (PRIM("eqInt")) return kbool(kas_int(a[0]) == kas_int(a[1]));
  if (PRIM("ltInt")) return kbool(kas_int(a[0]) < kas_int(a[1]));
  if (PRIM("leInt")) return kbool(kas_int(a[0]) <= kas_int(a[1]));
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
  if (PRIM("eqScalar")) return kbool(a[0]->as.chr == a[1]->as.chr);
  if (PRIM("ltScalar")) return kbool(a[0]->as.chr < a[1]->as.chr);
  /* show */
  if (PRIM("showInt")) return show_int(kas_int(a[0]));
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
