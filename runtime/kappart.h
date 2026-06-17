/* kappart.h — Kappa native runtime (boxed values, Boehm GC, primitives).
 *
 * This is the runtime the native backend (Kappa.Backend.C) links against.
 * Every Kappa value is a uniformly boxed, heap-allocated `KValue` reached
 * through ordinary C pointers, so the Boehm conservative collector traces
 * the whole graph precisely without per-type metadata. See
 * docs/NATIVE_BACKEND.md for the GC model, value layout, and the
 * supported-subset / honest-unsupported contract.
 *
 * Representation invariants the code generator relies on:
 *   - All functions are curried arity-1 closures (KFn).  Multi-argument
 *     application is a chain of `kapp` calls; partial application is free.
 *   - Implicit arguments are erased at runtime for constructors and
 *     primitives, matching Kappa.Eval.vapp (§31.2).  The generator emits
 *     `kappi` for implicit applications and `kapp` for explicit ones.
 *   - Pure primitives fold eagerly when saturated; IO primitives stay
 *     suspended as KValue and run only under `krun_io` (the do-kernel and
 *     the `main` driver), matching the interpreter's runIOValue.
 */
#ifndef KAPPART_H
#define KAPPART_H

#include <stdint.h>
#include <stddef.h>

typedef enum {
  K_INT,   /* Nat/Int/Integer (signed 64-bit; see docs §3) */
  K_DBL,   /* binary64 */
  K_STR,   /* UTF-8 text: bytes + length (not NUL-terminated)            */
  K_CHR,   /* Unicode scalar value                                       */
  K_UNIT,  /* the canonical Unit value                                   */
  K_CTOR,  /* data constructor: interned name + boxed args               */
  K_REC,   /* record value: lexicographically-sorted fields              */
  K_CLO,   /* closure: arity-1 function pointer + captured environment   */
  K_PRIM,  /* primitive, possibly partially applied                      */
  K_IO,    /* suspended IO action (do-block / sequencing)                */
  K_REF,   /* mutable cell (var / MonadRef, §18.6.1)                     */
  K_FGN,   /* opaque foreign/host pointer (FFI: socket fd, sqlite3*, …)   */
  K_VARIANT, /* variant injection: member-identity tag + payload (§13)   */
  K_THUNK,  /* suspended pure computation (Delay/Memo, §19)              */
  K_BIGINT, /* arbitrary-precision Integer beyond int64 (GMP mpz, §6)    */
  K_BOUNCE, /* deferred tail call (trampoline; never user-observable)    */
  K_BYTE,   /* a single octet (§6.5 b-handler)                           */
  K_BYTES,  /* a byte sequence: pointer + length (§29.5)                 */
  K_IOTAIL, /* a do-block's tail IO action, deferred to the krun_io loop  */
            /* (§27.5A.3 stack-safe IO sequencing; never user-observable) */
  K_IOEFFECT, /* like K_IOTAIL but the scope discards the result (a tail  */
             /* statement-`if` branch, §18.8): krun_io runs it then       */
             /* yields Unit.  Never user-observable.                       */
  K_IOFINALLY /* a do-block tail IO action carrying §18.7 deferred actions */
             /* to run (LIFO) once it completes; krun_io accumulates them  */
             /* on a heap stack so the recursion stays C-stack-bounded.    */
} KTag;

typedef struct KValue KValue;
typedef struct KEnv KEnv;

/* arity-1 closure body: receives the captured env and one argument */
typedef KValue *(*KFn)(KEnv *env, KValue *arg);
/* suspended IO body: receives the captured env, returns the result value */
typedef KValue *(*KIOFn)(KEnv *env);

struct KValue {
  KTag tag;
  union {
    int64_t  i;
    double   d;
    uint32_t chr;
    struct { const char *p; size_t len; } str;
    struct { const char *name; int argc; KValue **args; } ctor;
    struct { int n; const char **names; KValue **vals; } rec;
    struct { KFn fn; KEnv *env; } clo;
    struct { const char *name; int argc; KValue **args; } prim;
    struct { KIOFn fn; KEnv *env; } io;
    struct { KValue **cell; } ref;             /* cell[0] is the contents */
    struct { void *p; const char *kind; } fgn;
    struct { const char *tag; KValue *payload; } var;
    struct { KIOFn fn; KEnv *env; int memo; KValue **cache; } thunk;
    struct { void *mpz; } big;   /* points to a GC-allocated __mpz_struct */
    struct { KValue *fn; KValue *arg; } bounce;
    struct { KValue *action; KValue **defers; int n; } iofin; /* K_IOFINALLY */
    unsigned char byte;
    struct { const unsigned char *p; size_t len; } bytes;
  } as;
};

/* de Bruijn environment: head is index 0 (the innermost binder). */
struct KEnv {
  KValue *val;
  KEnv   *next;
};

/* ── lifecycle ─────────────────────────────────────────────────────── */
void krt_init(void);                 /* GC_INIT once, at the top of main */

/* ── allocation (Boehm GC) ─────────────────────────────────────────── */
void *kgc_alloc(size_t n);           /* scanned: may contain pointers    */
void *kgc_alloc_atomic(size_t n);    /* pointer-free (string/byte blobs) */

/* ── value constructors ────────────────────────────────────────────── */
KValue *kint(int64_t v);
KValue *kbigint_str(const char *decimal);       /* §6 Integer literal > int64 */
KValue *kdbl(double v);
KValue *kstr(const char *bytes, size_t len);   /* copies `len` bytes      */
KValue *kstr0(const char *cstr);               /* from a C string literal */
KValue *kchr(uint32_t scalar);
KValue *kunit(void);
KValue *kbool(int b);                           /* True/False constructors */
KValue *kctor(const char *name, int argc, KValue **args);
KValue *kctor0(const char *name);               /* nullary constructor     */
KValue *krec(int n, const char **names, KValue **vals);
KValue *kclo(KFn fn, KEnv *env);
KValue *kprim(const char *name);                /* 0-ary; saturates via kapp */
KValue *kio(KIOFn fn, KEnv *env);
KValue *kref_new(KValue *init);
KValue *kfgn(void *p, const char *kind);
KValue *kinject(const char *tag, KValue *payload);   /* §13 variant injection */
KValue *kthunk(KIOFn fn, KEnv *env, int memo);       /* §19 Delay(0)/Memo(1)  */
KValue *kbyte(unsigned char w);                      /* §6.5 byte             */
KValue *kbytes(const unsigned char *p, size_t len);  /* §29.5 byte sequence   */

/* ── environment ───────────────────────────────────────────────────── */
KEnv   *kpush(KValue *v, KEnv *e);
KValue *kvar(KEnv *e, int ix);

/* ── application ───────────────────────────────────────────────────── */
KValue *kapp(KValue *f, KValue *x);   /* explicit application (drains tail bounces) */
KValue *kappi(KValue *f, KValue *x);  /* implicit (erased for ctor/prim)  */
KValue *kprim_call(const char *name, int argc, KValue **args); /* saturated-prim fast path */
/* Direct helpers for statically known saturated primitives (QW1): the
 * codegen emits these instead of `kprim_call` — no string dispatch, no arity
 * check, no per-call argument array.  `prim_fire_pure` delegates to them. */
KValue *kp_addInt(KValue *, KValue *);   KValue *kp_subInt(KValue *, KValue *);
KValue *kp_mulInt(KValue *, KValue *);   KValue *kp_divInt(KValue *, KValue *);
KValue *kp_modInt(KValue *, KValue *);   KValue *kp_negInt(KValue *);
KValue *kp_eqInt(KValue *, KValue *);    KValue *kp_ltInt(KValue *, KValue *);
KValue *kp_leInt(KValue *, KValue *);
KValue *kp_addDouble(KValue *, KValue *); KValue *kp_subDouble(KValue *, KValue *);
KValue *kp_mulDouble(KValue *, KValue *); KValue *kp_divDouble(KValue *, KValue *);
KValue *kp_negDouble(KValue *);           KValue *kp_ltDouble(KValue *, KValue *);
KValue *kp_floatEq(KValue *, KValue *);   KValue *kp_eqDouble(KValue *, KValue *);
KValue *kp_stringAppend(KValue *, KValue *); KValue *kp_eqStr(KValue *, KValue *);
KValue *kp_ltStr(KValue *, KValue *);
KValue *kp_eqScalar(KValue *, KValue *);  KValue *kp_ltScalar(KValue *, KValue *);
KValue *kp_showInt(KValue *);   KValue *kp_showDouble(KValue *);
KValue *kp_showScalar(KValue *); KValue *kp_showStringLit(KValue *);
KValue *kp_intToDouble(KValue *);
KValue *kp_eqByte(KValue *, KValue *); KValue *kp_ltByte(KValue *, KValue *);
KValue *kp_intAnd(KValue *, KValue *); KValue *kp_intOr(KValue *, KValue *);
KValue *kp_intXor(KValue *, KValue *);
KValue *kbounce(KValue *fn, KValue *arg);  /* defer a tail-position application */
KValue *ktrampoline(KValue *r);            /* drive bounces to a value     */
KValue *kio_tail(KValue *action);          /* mark a do-block tail IO action for krun_io */
KValue *kio_effect(KValue *action);        /* like kio_tail, but krun_io yields Unit (discards the result) */
KValue *kio_finally(KValue *action, KValue **defers, int n); /* tail action + §18.7 defers to run after */

/* ── deconstruction (codegen for CMatch / CProj) ───────────────────── */
int      kctor_is(KValue *v, const char *name);  /* tag-name equality     */
const char *kctor_name(KValue *v);
int      kctor_argc(KValue *v);
KValue  *kctor_arg(KValue *v, int i);
KValue  *kproj(KValue *rec, const char *name);
int      kvariant_is(KValue *v, const char *tag);    /* §13 CPInject test     */
int      kis_variant(KValue *v);                     /* §13 CPInjectRest guard */
KValue  *kvariant_payload(KValue *v);
KValue  *kforce(KValue *v);                          /* §19 force a thunk      */
int      krec_size(KValue *rec);                 /* field count (tuple match) */
KValue  *krec_at(KValue *rec, int i);            /* positional field (tuples) */
KValue  *krec_without(KValue *rec, int nexcl, const char **excl); /* §17.2.5 rest */
int      klit_eq(KValue *a, KValue *b);          /* literal equality for CPLit */

/* ── unboxing helpers ──────────────────────────────────────────────── */
int64_t  kas_int(KValue *v);
double   kas_dbl(KValue *v);
int      kas_bool(KValue *v);

/* ── references ────────────────────────────────────────────────────── */
KValue  *kref_get(KValue *r);
KValue  *kref_set(KValue *r, KValue *v);         /* returns Unit          */

/* ── IO execution ──────────────────────────────────────────────────── */
KValue  *krun_io(KValue *action);    /* run an IO action to a result      */

/* list helpers for `for` loops and FFI glue (Cons "::" / Nil) */
KValue  *knil(void);
KValue  *kcons(KValue *h, KValue *t);
int      kis_cons(KValue *v);

/* abort with a runtime error message (mirrors a Kappa runtime defect). */
void     krt_fail(const char *msg) __attribute__((noreturn));

/* ── FFI hooks ─────────────────────────────────────────────────────── */
/* The core runtime dispatches any primitive it does not implement itself
 * to the FFI runtime (kappart_ffi.c).  The stub build provides a unit
 * that knows no FFI primitives; the demo build links the sockets+sqlite3
 * implementation instead.  The code generator only emits a primitive
 * after confirming the linked runtime implements it, so these are never
 * reached for an unknown name. */
int      prim_is_io_ffi(const char *p);   /* is `p` an FFI IO primitive?  */
int      prim_arity_ffi(const char *p);   /* arity of FFI primitive `p`   */
KValue  *krun_io_ffi(KValue *action);     /* run an FFI IO action         */

#endif /* KAPPART_H */
