/* value.c — the boxed-value model.
 *
 * Split out of kappart.c (see boxed.h).  Owns alloc_val /
 * alloc_val_atomic, the value constructors, the environment, application +
 * the trampoline, deconstruction / matching, literal equality, and the
 * unboxing accessors + refs.  The bignum boundary it escapes to (kmpz_set_i64,
 * kbig_from_mpz, kfrom_mpz, kload_mpz, kint_cmp, krat, as_rat) lives in
 * bignum.c and is reached through boxed.h. */
#include "kappart.h"
#include "boxed.h"

#include <gmp.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
KValue *alloc_val(KTag tag) {
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
int kis_int_any(KValue *v) {
  if (kis_imm_int(v)) return 1;
  if (kis_imm(v)) return 0;          /* other immediate kinds: not an Int */
  return v->tag == K_INT || v->tag == K_BIGINT;
}

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

