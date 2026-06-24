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
  K_IOFINALLY, /* a do-block tail IO action carrying §18.7 deferred actions */
             /* to run (LIFO) once it completes; krun_io accumulates them  */
             /* on a heap stack so the recursion stays C-stack-bounded.    */
  K_FAIL,   /* internal typed IO failure: carries the thrown error value     */
            /* and propagates through krun_io until catchIO handles it.      */
  K_NATIVE  /* §26/§27.1.1 native host-binding action: a CODEGEN-EMITTED   */
            /* direct C wrapper pointer + accumulated args.  Replaces the  */
            /* former string-named FFI primitive: there is NO runtime name */
            /* table and NO strcmp dispatch — krun_io fires the action by  */
            /* CALLING the function pointer the .kappa.c emitted for the   */
            /* manifest's symbol.  Curries by accumulating args (argc<     */
            /* arity is a partial value); a saturated K_NATIVE is the      */
            /* suspended UIO action that krun_io runs.                     */
} KTag;

/* LR2 constructor tag ids (numeric pattern-match dispatch).  These FIXED ids
 * are shared between the runtime (which builds these builtins) and codegen
 * (which references them as KCT_* in generated matches/constructions), so the
 * two MUST agree — see the _Static_assert in kappart.c.  KCT_OTHER=0 is a
 * never-constructed-with sentinel distinct from every real id and from the
 * kctor_tagid() "not a constructor" return of -1.  User constructors get
 * codegen-assigned ids at KCT_USER_BASE and above (so they never collide with
 * a builtin); variant injections get a disjoint 0-based codegen id space
 * (a variant value is never tested with a ctor id, so overlap is harmless). */
enum {
  KCT_OTHER = 0,
  KCT_UNIT  = 1,
  KCT_TRUE, KCT_FALSE,
  KCT_CONS, KCT_NIL,
  KCT_SOME, KCT_NONE,
  KCT_RAT,
  KCT_EFFPURE, KCT_EFFOP,   /* §18.1 algebraic-effect tree nodes */
  KCT_USER_BASE = 16
};

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
    /* LR2: `tagid` (a numeric ctor identity: a builtin KCT_ id or a
     * codegen-assigned KCT_USER_BASE+ id) lets the match path dispatch via an
     * int compare (kctor_tagid) instead of a kctor_is strcmp.  `name` is
     * retained for diagnostics / rep-equality. */
    struct { const char *name; int argc; KValue **args; int tagid; } ctor;
    struct { int n; const char **names; KValue **vals; } rec;
    struct { KFn fn; KEnv *env; } clo;
    struct { KIOFn fn; KEnv *env; } io;
    struct { KValue **cell; } ref;             /* cell[0] is the contents */
    struct { void *p; const char *kind; } fgn;
    /* LR2: `tagid` is the variant injection's numeric identity (codegen-
     * assigned, 0-based — variants are never built by the runtime).  `tag`
     * (the §13.3 canonical member-identity string) is retained. */
    struct { const char *tag; KValue *payload; int tagid; } var;
    struct { KIOFn fn; KEnv *env; int memo; KValue **cache; } thunk;
    struct { void *mpz; } big;   /* points to a GC-allocated __mpz_struct */
    struct { KValue *fn; KValue *arg; } bounce;
    struct { KValue *action; KValue **defers; int n; } iofin; /* K_IOFINALLY */
    struct { KValue *err; } fail;
    unsigned char byte;
    struct { const unsigned char *p; size_t len; } bytes;
    /* K_NATIVE: `fn` is the codegen-emitted direct wrapper, `arity` the
     * declared param count, `argc` the args accumulated so far, `kind` a
     * label for diagnostics only (NEVER used for dispatch). */
    struct { KValue *(*fn)(KValue **args); int arity; int argc; KValue **args; const char *kind; int is_io; } native;
  } as;
};

/* §27.1.1 native action body: receives the accumulated argument array and
 * returns the (boxed) result.  Emitted per manifest symbol by the backend. */
typedef KValue *(*KNativeFn)(KValue **args);

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
KValue *kctor(int tagid, const char *name, int argc, KValue **args);
KValue *kctor0(int tagid, const char *name);    /* nullary constructor     */
KValue *krec(int n, const char **names, KValue **vals);
KValue *kclo(KFn fn, KEnv *env);
KValue *kio(KIOFn fn, KEnv *env);
KValue *kfail(KValue *err);
int     kis_fail(KValue *v);
KValue *kref_new(KValue *init);
KValue *kfgn(void *p, const char *kind);
KValue *kinject(int tagid, const char *tag, KValue *payload); /* §13 variant injection */
KValue *kthunk(KIOFn fn, KEnv *env, int memo);       /* §19 Delay(0)/Memo(1)  */
KValue *kbyte(unsigned char w);                      /* §6.5 byte             */
KValue *kbytes(const unsigned char *p, size_t len);  /* §29.5 byte sequence   */

/* ── environment ───────────────────────────────────────────────────── */
KEnv   *kpush(KValue *v, KEnv *e);
KValue *kvar(KEnv *e, int ix);

/* ── application ───────────────────────────────────────────────────── */
KValue *kapp(KValue *f, KValue *x);   /* explicit application (drains tail bounces) */
KValue *kappi(KValue *f, KValue *x);  /* implicit (erased for ctor/prim)  */
/* Direct helpers for the pure primitives: the codegen emits a direct call for
 * a statically known saturated primitive, or a curried K_NATIVE wrapping the
 * helper pointer for partial application — no string dispatch, no arity check,
 * no per-call argument array, no by-name firing path. */
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

/* LR1: unbox a K_INT to int64 for the typed unboxed Int workers (kwi_*).  A
 * non-K_INT value (a K_BIGINT that does not fit, or any non-Int box) sets the
 * overflow/escape flag so the caller re-runs the boxed worker — the unboxed
 * fast path is only taken when every argument is an inline K_INT. */
static inline int64_t kunbox_i64(KValue *v, int *ovf) {
  if (v->tag == K_INT) return v->as.i;
  *ovf = 1;
  return 0;
}
/* R2.2: unbox a K_DBL to double for the typed unboxed Double workers.  A
 * non-K_DBL value sets the escape flag so the caller re-runs the boxed worker.
 * Unlike `kas_dbl` (which aborts on a non-Double), this ESCAPES — the unboxed
 * fast path is only taken when the argument is an inline K_DBL, exactly
 * mirroring `kunbox_i64`'s tag-checked escape (never a crash on the wrong
 * tag). */
static inline double kunbox_dbl(KValue *v, int *ovf) {
  if (v->tag == K_DBL) return v->as.d;
  *ovf = 1;
  return 0.0;
}
KValue *kbounce(KValue *fn, KValue *arg);  /* defer a tail-position application */
KValue *ktrampoline(KValue *r);            /* drive bounces to a value     */
KValue *kio_tail(KValue *action);          /* mark a do-block tail IO action for krun_io */
KValue *kio_effect(KValue *action);        /* like kio_tail, but krun_io yields Unit (discards the result) */
KValue *kio_finally(KValue *action, KValue **defers, int n); /* tail action + §18.7 defers to run after */

/* ── deconstruction (codegen for CMatch / CProj) ───────────────────── */
int      kctor_is(KValue *v, const char *name);  /* tag-name equality     */
int      kctor_tagid(KValue *v);   /* LR2: numeric ctor identity for matching;
                                    * K_UNIT->KCT_UNIT; non-ctor -> -1 (matches
                                    * no test, preserving the K_CTOR type guard) */
const char *kctor_name(KValue *v);
int      kctor_argc(KValue *v);
KValue  *kctor_arg(KValue *v, int i);
KValue  *kproj(KValue *rec, const char *name);
int      kvariant_is(KValue *v, const char *tag);    /* §13 CPInject test     */
int      kvariant_tagid(KValue *v);  /* LR2: numeric variant identity; non-variant -> -1 */
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
const char *kas_str(KValue *v);   /* NUL-terminated bytes of a K_STR (§26 CtString) */
void    *kas_fgn(KValue *v);      /* opaque pointer of a K_FGN (§26 CtHandle/CtRawPtr) */
uint64_t kas_u64(KValue *v);      /* Integer as unsigned 64-bit (§26 U64/Usize) */
KValue  *ku64(uint64_t u);        /* box an unsigned 64-bit as a non-negative Integer */

/* ── references ────────────────────────────────────────────────────── */
KValue  *kref_get(KValue *r);
KValue  *kref_set(KValue *r, KValue *v);         /* returns Unit          */

/* ── IO execution ──────────────────────────────────────────────────── */
KValue  *krun_io(KValue *action);    /* run an IO action to a result      */
KValue  *krun_io_checked(KValue *action); /* run IO; abort on uncaught typed failure */

/* list helpers for `for` loops and FFI glue (Cons "::" / Nil) */
KValue  *knil(void);
KValue  *kcons(KValue *h, KValue *t);
int      kis_cons(KValue *v);

/* abort with a runtime error message (mirrors a Kappa runtime defect). */
void     krt_fail(const char *msg) __attribute__((noreturn));

/* ── native host-binding actions (§26/§27.1.1) ─────────────────────── */
/* A native action carries a DIRECT C function pointer emitted by the
 * backend for a manifest-declared symbol — there is no name table and no
 * strcmp dispatch.  `knative` builds the curried (argc=0) action value;
 * `kapp` accumulates args and a saturated action is the suspended UIO
 * action that `krun_io` runs by calling `fn`.  `knative_sat` is the
 * saturated fast path the backend emits for an exactly-applied call. */
KValue  *knative(KNativeFn fn, int arity, const char *kind, int is_io);
KValue  *knative_sat(KNativeFn fn, int arity, KValue **args, int is_io);

#endif /* KAPPART_H */
