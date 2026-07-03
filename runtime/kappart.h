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
#include <assert.h>
#include <stdatomic.h>

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
  K_ARRAY, /* mutable O(1) array: length-prefixed slab; K_REF widened to  */
           /* N cells (MUTABLE-ARRAY-DESIGN §5.1).  `elemkind`/`element_  */
           /* size` pick the slab rep — boxed today (every element a      */
           /* b000 KValue*); the field exists so the unboxed INT64/DOUBLE  */
           /* scalar slabs are a later additive change, NOT a reshape.     */
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
  K_NATIVE, /* §26/§27.1.1 native host-binding action: a CODEGEN-EMITTED   */
            /* direct C wrapper pointer + accumulated args.  Replaces the  */
            /* former string-named FFI primitive: there is NO runtime name */
            /* table and NO strcmp dispatch — krun_io fires the action by  */
            /* CALLING the function pointer the .kappa.c emitted for the   */
            /* manifest's symbol.  Curries by accumulating args (argc<     */
            /* arity is a partial value); a saturated K_NATIVE is the      */
            /* suspended UIO action that krun_io runs.                     */
  K_FREED   /* DEBUG poison sentinel: only written after S3.2 RC free when */
            /* krc_poison_set_enabled(1) is active. Never user-observable. */
} KTag;

/* LR2 constructor tag ids (numeric pattern-match dispatch).  These FIXED ids
 * are shared between the runtime (which builds these builtins) and codegen
 * (which references them as KCT_* in generated matches/constructions), so the
 * two MUST agree — see the _Static_assert in value.c.  KCT_OTHER=0 is a
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
  /* §18.1 runtime-built Exit/Cause result ctors (await/join/race/timeout
   * outcomes).  FIXED ids so an Exit the RUNTIME delivers (krt2i_success/…)
   * matches a codegen id-based `case Success`/`Failure`/`Fail`/… — without
   * these, runtime-built results carry KCT_OTHER and every such match is
   * non-exhaustive.  Names are retained for diagnostics; dispatch is by id. */
  KCT_SUCCESS, KCT_FAILURE,                                /* Exit  */
  KCT_FAIL, KCT_INTERRUPT, KCT_DEFECT, KCT_BOTH, KCT_THEN, /* Cause */
  /* §18.1.6 race/timeout outcomes + §18.1.2 interruption metadata.  Runtime
   * builds these (race.c/scope.c/rt.c) under DIAGNOSTIC names (RaceWonLeft/
   * TimeoutDone/InterruptCause); dispatch is by id, so each id is pinned to the
   * PRELUDE ctor a .kp match names (ROLeft/TOExit/MkInterruptCause/...). */
  KCT_RO_LEFT, KCT_RO_RIGHT,                                 /* RaceOutcome    */
  KCT_TO_TIMED_OUT, KCT_TO_EXIT,                             /* TimeoutOutcome */
  KCT_MK_INTERRUPT_CAUSE,                                    /* InterruptCause */
  KCT_IT_REQUESTED, KCT_IT_SCOPE_SHUTDOWN, KCT_IT_TIMED_OUT, /* InterruptTag (native)        */
  KCT_IT_RACE_LOST, KCT_IT_EXTERNAL,                         /* InterruptTag (interp/future) */
  KCT_USER_BASE = 40
};

typedef struct KValue KValue;
typedef struct KEnv KEnv;

/* arity-1 closure body: receives the captured env and one argument */
typedef KValue *(*KFn)(KEnv *env, KValue *arg);
/* suspended IO body: receives the captured env, returns the result value */
typedef KValue *(*KIOFn)(KEnv *env);

struct KValue {
  KTag tag;
  /* Perceus RC Stage S0 (PERCEUS-RC-DESIGN §2/§7): a 32-bit reference count
   * occupying the previously-free 4-byte hole at offset 4 — `tag` is a 4-byte
   * KTag at offset 0 and the union is 8-aligned starting at offset 8, so this
   * field fills the padding with ZERO struct growth (sizeof stays 48; asserted
   * below).  Every heap allocation initializes it to 1 (alloc_val /
   * alloc_val_atomic in value.c).  IMMEDIATES (kis_imm: b001 Int, b010 nullary
   * ctor, b011 packed ctor) are NOT heap objects — they carry no header and so
   * no rc.  This field is RESERVED + INITIALIZED ONLY at S0: Boehm remains the
   * collector, there is no dup/drop and no RC reclamation yet.  Stage S3.0
   * rides the high bit of this word for the thread-shared flag (Koka's
   * negative-rc trick, PERCEUS-S3-PLAN §2.2); the low 31 bits remain the
   * ordinary reference count. */
  _Atomic uint32_t rc;
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
    /* K_ARRAY (MUTABLE-ARRAY-DESIGN §5.1): `elems` is ONE allocation —
     * the boxed slab is a kgc_alloc(len*sizeof(KValue*)) SCANNED block, exactly
     * like K_CTOR's args.  `len` makes arrayLen O(1) and pure; `cap` is the
     * growth seed (cap == len today).  `elemkind`/`element_size` are the slab-
     * rep discriminator and the GC-alloc selector: BOXED (==8) scanned today;
     * INT64/DOUBLE atomic slabs slot in later with NO struct change.  `elems`
     * is `void *` (not `KValue **`) precisely so the same box later holds an
     * int64_t[]/double[] without reinterpretation. */
    struct { void *elems; int64_t len; int64_t cap;
             uint8_t elemkind; uint8_t element_size; } arr;
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
     * label for diagnostics only (NEVER used for dispatch), and `blocking`
     * selects the rt-blocking lane for classified foreign work. */
    struct { KValue *(*fn)(KValue **args); int arity; int argc; KValue **args; const char *kind; int is_io; int blocking; } native;
  } as;
};

/* Perceus RC Stage S0: the `rc` word MUST fill the existing offset-4 padding —
 * no struct growth.  If this trips, the rc field changed the layout (e.g. the
 * union alignment moved) and the "zero behavior change" S0 invariant is broken. */
_Static_assert(sizeof(KValue) == 48, "Perceus S0: KValue must stay 48 bytes (rc fills the offset-4 hole)");
_Static_assert(offsetof(KValue, rc) == 4, "Perceus S0: rc must occupy the free 4-byte hole at offset 4");

/* §27.1.1 native action body: receives the accumulated argument array and
 * returns the (boxed) result.  Emitted per manifest symbol by the backend. */
typedef KValue *(*KNativeFn)(KValue **args);

/* de Bruijn environment: head is index 0 (the innermost binder). */
struct KEnv {
  KValue *val;
  KEnv   *next;
};

/* abort with a runtime error message (mirrors a Kappa runtime defect).  Kept
 * early so inline debug checks can fail through the normal runtime path. */
void     krt_fail(const char *msg) __attribute__((noreturn));

#ifndef NDEBUG
extern _Atomic int k_rc_poison_enabled;
void krc_poison_set_enabled(int enabled);
#else
static inline void krc_poison_set_enabled(int enabled) { (void)enabled; }
#endif

/* ── UNBOXING Stage 0: KValue* word tag space (UNBOXING-DESIGN §5.4) ─────────
 * The native backend will (Stage 1) carry small Int / Bool / Char / Unit /
 * nullary-ctor values as IMMEDIATES packed into the KValue*-sized word instead
 * of separate heap boxes — closing the per-`addInt` allocation.  The low 3 bits
 * of the word are the discriminator: GC_MALLOC is >= 8-byte aligned (asserted at
 * startup) and interior-pointer recognition is OFF (see krt_init), so a real
 * heap KValue* has them all 0 and a tagged immediate has at least one set, which
 * the collector then treats as a non-pointer (an odd word is not a root).
 * RESERVED budget — do NOT repurpose a code without auditing every kderef site:
 *
 *     b000   a real heap KValue* pointer (zero low bits -> kderef needs NO mask)
 *     b001   immediate Int    (Stage 1: arithmetic-shifted 61-bit value)
 *     b010   immediate ctor   (Stage 1b: EVERY nullary ctor of ANY ADT; tag id
 *                              in the payload — Unit / True / False / Nil / None
 *                              AND every user enum variant)
 *     b011   packed ctor    (Stage 1d/1e: a ONE- or TWO-field ctor whose every
 *                              field is itself an immediate that fits the payload —
 *                              a 1-bit nfields selector, the tag id AND every
 *                              field's whole immediate word in the word; e.g.
 *                              Some(smallInt) / Ok(smallEnum) / Pair(small,small),
 *                              alloc-free)
 *     b100 .. b111   RESERVED for additional immediate KINDS (e.g. immediate Char).
 *                    NOT the Perceus RC borrow / thread-shared discriminator: that
 *                    lives in the heap-object HEADER (Koka-style), since an
 *                    immediate is value-copied and never reference-counted.  See
 *                    docs/TAGGING-RESEARCH.md.
 *
 * Stage 0 installed this discriminator API + the GC/alignment contract; Stage 1
 * then ACTIVATED tagging: small Int (b001), every nullary ctor (b010), and packed
 * 1/2-field ctors (b011) are now PRODUCED as immediates (see value.c: kint, kbool,
 * kunit, the kctor builder), so kis_imm() is true for them.  Every ->tag/->as.*
 * deref routes through kderef(), whose debug assert traps any raw deref of a
 * tagged word (an odd word would segfault/misread otherwise). */
_Static_assert(_Alignof(max_align_t) >= 8,
               "UNBOXING: immediate tagging needs >= 8-byte heap alignment (low 3 bits free)");

#define KIMM_TAG_MASK ((uintptr_t)0x7)
#define KIMM_PTR      ((uintptr_t)0x0)   /* b000: a heap pointer */
#define KIMM_INT      ((uintptr_t)0x1)   /* b001: immediate Int  */
#define KIMM_CTOR     ((uintptr_t)0x2)   /* b010: immediate ctor */
#define KIMM_PACKED   ((uintptr_t)0x3)   /* b011: packed single-field ctor */

/* Is this word a tagged immediate (not a heap pointer)?  True for a small Int
 * (b001, 61-bit range), a nullary ctor (b010), and a packed 1/2-field ctor
 * (b011); n-ary ctors, out-of-range Int, Double, String, closures, refs etc.
 * stay b000 heap pointers. */
static inline int kis_imm(const KValue *v) {
  return ((uintptr_t)v & KIMM_TAG_MASK) != KIMM_PTR;
}
static inline void kassert_live(const KValue *v) {
#ifndef NDEBUG
  if (!v || kis_imm(v)) return;
  if (atomic_load_explicit(&k_rc_poison_enabled, memory_order_relaxed) && v->tag == K_FREED)
    krt_fail("use after RC free");
#else
  (void)v;
#endif
}
/* Confirm-and-return a heap pointer.  Stage 1 routes every ->tag/->as.* deref
 * through this; the debug-build assert trips if a tagged immediate is ever
 * dereferenced as a pointer (caught in CI before it segfaults on an odd word). */
static inline KValue *kderef(KValue *v) {
  assert(((uintptr_t)v & KIMM_TAG_MASK) == KIMM_PTR &&
         "kderef on a tagged immediate (UNBOXING invariant)");
  kassert_live(v);
  return v;
}
/* The payload of an immediate, sign-extended (arithmetic >> drops the 3-bit
 * tag).  Caller discriminates Int vs ctor on the low 3 bits first. */
static inline intptr_t kimm_payload(const KValue *v) {
  return (intptr_t)(uintptr_t)v >> 3;
}

/* ── Perceus RC Stage S2.0: dup / drop (PERCEUS-RC-DESIGN §2/§7, S2-PLAN (a)) ──
 *
 * The two rc-maintenance primitives the S2 codegen will emit, landed here under
 * the BOEHM DIFFERENTIAL BACKSTOP through S2: S3.2 flips `kdrop` to free unique,
 * unshared values in the conservative `kis_rc_freeable` partition when their
 * count reaches zero. Boehm still retains the deliberately excluded shapes, so
 * a missed drop remains a leak, while an extra drop trips the rc-underflow assert.
 *
 * IMMEDIATES (kis_imm: b001 Int, b010 nullary ctor, b011 packed ctor) are not
 * heap objects — they carry no header and so no `rc` — so both ops skip them via
 * the single `kis_imm` guard.
 *
 * S2.2/S2.3 begin emitting them from the C backend; S3.2 makes the zero branch
 * reclaim the proved-safe subset. */

#ifndef NDEBUG
/* DEBUG-only running totals (defined in value.c).  Behind NDEBUG so a release
 * build stays byte-identical in cost — no counter loads/stores in kdup/kdrop. */
extern _Atomic unsigned long long k_dups_total;
extern _Atomic unsigned long long k_drops_total;
#endif

/* S3.0 shared-bit encoding. The sign/high bit marks an object that has crossed
 * a fiber/concurrency boundary; S3 free-on-zero must skip such objects until
 * S4 adds counted shared-object RC.  The header word is atomic already in S3.1:
 * the shared-bit transition can race with extant aliases, and even a no-op
 * shared kdup/kdrop must read the bit without a C data race. The low count is
 * intentionally ignored while the shared bit is set. */
#define KRC_SHARED_BIT ((uint32_t)0x80000000u)
#define KRC_COUNT_MASK ((uint32_t)0x7fffffffu)

static inline uint32_t krc_word(const KValue *v) {
  kassert_live(v);
  return atomic_load_explicit((_Atomic uint32_t *)&v->rc, memory_order_relaxed);
}

static inline uint32_t krc_count(const KValue *v) {
  return kis_imm(v) ? 0u : (krc_word(v) & KRC_COUNT_MASK);
}

static inline int krc_is_shared(const KValue *v) {
  return !kis_imm(v) && ((krc_word(v) & KRC_SHARED_BIT) != 0);
}

static inline void krc_set_count(KValue *v, uint32_t count) {
  uint32_t cur = krc_word(v);
  uint32_t next;
  do {
    next = (cur & KRC_SHARED_BIT) | (count & KRC_COUNT_MASK);
  } while (!atomic_compare_exchange_weak_explicit(&v->rc, &cur, next,
                                                  memory_order_relaxed,
                                                  memory_order_relaxed));
}

static inline void krc_mark_shared_shallow(KValue *v) {
  kassert_live(v);
  if (!kis_imm(v)) atomic_fetch_or_explicit(&v->rc, KRC_SHARED_BIT, memory_order_relaxed);
}

/* S3.0/S3.2 free-on-zero partition. This is deliberately conservative and is
 * the single guard deciding whether the S3.2 free branch MAY reclaim a zero-count
 * object. Mutable/lazy/foreign/shared objects remain Boehm-retained. Closures,
 * IO/action wrappers, and native-action wrappers also stay retained until
 * KEnv/action-finalizer/native-action ownership is represented at the free site. */
static inline int kis_rc_freeable(const KValue *v) {
  if (!v || kis_imm(v) || krc_is_shared(v)) return 0;
  switch (v->tag) {
    case K_CTOR:
    case K_REC:
    case K_VARIANT:
    case K_STR:
    case K_BOUNCE:
    case K_FAIL:
      return 1;
    default:
      return 0;
  }
}

void krc_mark_shared_recursive(KValue *v);
void kfree_recursive(KValue *v);

/* Increment the reference count of a heap value and RETURN it, so a dup can be
 * spliced inside an expression: `f(kdup(x), x)` shares `x` across both args.
 * An immediate is value-copied (no rc), so it is returned unchanged. */
static inline KValue *kdup(KValue *v) {
  if (kis_imm(v)) return v;
  kassert_live(v);
  uint32_t cur = krc_word(v);
  for (;;) {
    if (cur & KRC_SHARED_BIT) return v;
    uint32_t n = cur & KRC_COUNT_MASK;
#ifndef NDEBUG
    assert(n < KRC_COUNT_MASK && "kdup: rc count overflow");
#endif
    if (n >= KRC_COUNT_MASK) return v;
    uint32_t next = (cur & KRC_SHARED_BIT) | (n + 1);
    if (atomic_compare_exchange_weak_explicit(&v->rc, &cur, next,
                                              memory_order_relaxed,
                                              memory_order_relaxed)) {
#ifndef NDEBUG
      atomic_fetch_add_explicit(&k_dups_total, 1, memory_order_relaxed);
#endif
      return v;
    }
  }
}

/* Decrement the reference count of a heap value.  Shared values are skipped until
 * S4 provides atomic shared-object RC.  When a non-shared value reaches zero,
 * S3.2 recursively frees only the `kis_rc_freeable` strict-immutable partition;
 * excluded shapes stay Boehm-retained.  Under NDEBUG the fail-closed zero guard
 * avoids wrapping the low count. */
static inline void kdrop(KValue *v) {
  if (kis_imm(v)) return;
  kassert_live(v);
  uint32_t cur = krc_word(v);
  for (;;) {
    if (cur & KRC_SHARED_BIT) return;
    uint32_t n = cur & KRC_COUNT_MASK;
#ifndef NDEBUG
    assert(n > 0 && "kdrop: rc underflow (double-drop / missed-dup)");
#endif
    if (n == 0) return;
    uint32_t next = (cur & KRC_SHARED_BIT) | (n - 1);
    if (atomic_compare_exchange_weak_explicit(&v->rc, &cur, next,
                                              memory_order_relaxed,
                                              memory_order_relaxed)) {
#ifndef NDEBUG
      atomic_fetch_add_explicit(&k_drops_total, 1, memory_order_relaxed);
#endif
      if (n == 1 && kis_rc_freeable(v)) kfree_recursive(v);
      return;
    }
  }
}

/* DEBUG leak-trend probe: print the dup/drop totals and their net (drops - dups).
 * A net that drifts negative across a corpus is a missed-drop trend (PERCEUS-S2-
 * PLAN (c) secondary check).  A no-op under NDEBUG (the counters do not exist). */
void krc_report(void);

/* ── Stage 1: immediate-Int encoding (b001) ─────────────────────────────────
 * A small Int rides INSIDE the KValue*-sized word as (value << 3) | KIMM_INT — a
 * 61-bit signed Int (research rec 1: the 3-bit tag, not OCaml's 1-bit, leaves
 * room to grow immediate KINDS).  Out-of-range values escape to the boxed
 * K_BIGINT (GMP) path, exactly as a >int64 literal does today (§5.3 / research
 * rec 3).  The encoding is CANONICAL (§5.2): an in-range Int is ALWAYS the
 * immediate and NEVER a boxed singleton, so pointer identity can never collide. */
#define KIMM_INT_BITS 61
/* [-2^60, 2^60).  An arithmetic << of a value in this range neither overflows
 * the word nor disturbs the sign once the 3 tag bits are shifted out. */
#define KIMM_INT_MAX  (((int64_t)1 << (KIMM_INT_BITS - 1)) - 1)   /* 2^60 - 1 */
#define KIMM_INT_MIN  (-((int64_t)1 << (KIMM_INT_BITS - 1)))      /* -2^60    */

/* Does a tagged word carry an immediate Int? */
static inline int kis_imm_int(const KValue *v) {
  return ((uintptr_t)v & KIMM_TAG_MASK) == KIMM_INT;
}
/* Recover the int64 value of an immediate Int (arithmetic >> 3 sign-extends). */
static inline int64_t kimm_int_val(const KValue *v) {
  return (int64_t)((intptr_t)(uintptr_t)v >> 3);
}
/* Does an int64 fit the 61-bit immediate range? */
static inline int kint_fits_imm(int64_t v) {
  return v >= KIMM_INT_MIN && v <= KIMM_INT_MAX;
}
/* Pack an in-range int64 as a b001 immediate KValue* word (caller must have
 * checked kint_fits_imm; out-of-range packing would corrupt the sign). */
static inline KValue *kmk_imm_int(int64_t v) {
  return (KValue *)(uintptr_t)(((uintptr_t)(int64_t)v << 3) | KIMM_INT);
}
/* The Int value of `v` whether it is an immediate or a boxed K_INT, WITHOUT a
 * bignum check.  Caller must already know `v` is one of those two (an immediate,
 * or a K_INT box) — the hot int prims test `kis_int_word`/tag first. */
static inline int64_t kint_word(KValue *v) {
  return kis_imm_int(v) ? kimm_int_val(v) : kderef(v)->as.i;
}
/* Is `v` an inline Int — an immediate, or a boxed K_INT — i.e. an Int that fits
 * int64 with no bignum?  (A K_BIGINT in [MIN_I64, MAX_I64] is canonicalised back
 * to inline by kfrom_mpz, so a surviving K_BIGINT never fits int64.) */
static inline int kis_int_word(KValue *v) {
  return kis_imm_int(v) || (!kis_imm(v) && kderef(v)->tag == K_INT);
}

/* ── Stage 1b: immediate nullary-ctor encoding (b010) ───────────────────────
 * EVERY nullary constructor (0 fields) — of ANY ADT — rides INSIDE the
 * KValue*-sized word as (tagId << 3) | KIMM_CTOR.  This covers Unit, True/False,
 * Nil, None AND every user enum variant / nullary case of a mixed ADT (a
 * GameMode, `Quit`, …).  Construction is alloc-free and a `match` on a nullary
 * arm is a deref-free integer compare against the tag id.  Mixed ADTs work
 * uniformly: the immediate `None` and a boxed `Some x` both answer kctor_tagid,
 * which reads the id from the word for a b010 and from the box for a b000.
 * The encoding is CANONICAL (§5.2): a given nullary ctor is ALWAYS this one
 * immediate and NEVER a surviving boxed K_CTOR/K_UNIT, so pointer-identity and
 * rep equality can never collide between the two forms. */
static inline int kis_imm_ctor(const KValue *v) {
  return ((uintptr_t)v & KIMM_TAG_MASK) == KIMM_CTOR;
}
/* The tag id of an immediate nullary ctor (logical >> 3 drops the 3-bit tag; the
 * id is small and non-negative, so an unsigned shift is correct). */
static inline int kimm_ctor_id(const KValue *v) {
  return (int)((uintptr_t)v >> 3);
}
/* Pack a ctor tag id as a b010 immediate KValue* word.  Only ever called for a
 * NULLARY ctor (argc == 0); an n-ary ctor stays a boxed K_CTOR. */
static inline KValue *kmk_imm_ctor(int tagid) {
  return (KValue *)(((uintptr_t)(unsigned)tagid << 3) | KIMM_CTOR);
}

/* ── Stage 1d/1e: packed immediate-field-ctor encoding (b011) ───────────────
 * A constructor with ONE or TWO explicit fields, where EVERY field value is
 * ITSELF an immediate (a b001 Int or a b010 nullary ctor) small enough to fit,
 * rides INSIDE the KValue*-sized word — alloc-free.  The 3-bit b011 tag is
 * followed by a 1-bit `nfields` selector (0 → one field, 1 → two fields), then
 * the 20-bit tagId, then the field payload region (the remaining 40 bits):
 *
 *   nfields=0 (single, Stage 1d):
 *     [ field0 word : 40 ][ tagId : 20 ][ nf=0 : 1 ][ b011 : 3 ]
 *   nfields=1 (double, Stage 1e):
 *     [ field1 word : 20 ][ field0 word : 20 ][ tagId : 20 ][ nf=1 : 1 ][ b011 : 3 ]
 *
 * Bit budget (every bit accounted, LSB→MSB): 3 (tag) + 1 (nfields) + 20 (tagId)
 * = 24 fixed bits, leaving 64-24 = 40 bits for the field payload region.  Single:
 * 40 bits → field0.  Double: 40 bits → field0:20 | field1:20.  Both add to 64.
 *
 * This makes the single-field arms of Option<Int>/Result<small,small>/
 * Option<enum> (Some / Ok / Err over an immediate payload) allocation-free, AND
 * the two-field ctors Pair(Int,Int) (small) / 2-scalar records lowered to a ctor
 * / 2-enum variants allocation-free.
 *
 * Why it is SOUND *and* uniform (unlike a niche): the discriminant (`tagId`) AND
 * every field live EXPLICITLY in the word, so kctor_tagid / kctor_arg decode them
 * blind — no type parameter needed, so a polymorphic `Pair a b -> …` works — and
 * a packed `Pair(None, None)` is a b011 word DISTINCT from any nullary b010 word,
 * so nesting/polymorphism have NO collision.  Per-value packing is canonical
 * (§5.2): a given value has exactly ONE rep (`Pair 1 2` always packs since both
 * fit; `Pair (2^30) 0` always boxes since field0 does not), so pointer-identity /
 * rep-equality stay consistent.
 *
 * We STORE EACH FIELD'S WHOLE IMMEDIATE WORD (not just its decoded value), so
 * kctor_arg reconstructs a valid immediate KValue with NO type information — it
 * shifts the field word back out and hands it back as a KValue*.  Each field word
 * keeps its own low 3 tag bits, so the recovered value is a self-describing
 * immediate (b001 Int or b010 ctor) exactly as it was built. */
#define KIMM_PACKED_NF_BITS    1    /* nfields selector: 0 → single, 1 → double */
#define KIMM_PACKED_TAG_BITS   20   /* tagIds 0 .. ~1M (>> KCT_USER_BASE+program) */
/* Bits below the field payload region: 3 (b011) + 1 (nfields) + 20 (tagId). */
#define KIMM_PACKED_HDR_BITS   (3 + KIMM_PACKED_NF_BITS + KIMM_PACKED_TAG_BITS)   /* 24 */
/* Single-field payload: all remaining bits hold field0's whole word. */
#define KIMM_PACKED_FIELD_BITS (64 - KIMM_PACKED_HDR_BITS)                        /* 40 */
/* Double-field payload: the 40 payload bits split evenly into two field slots. */
#define KIMM_PACKED2_FIELD_BITS (KIMM_PACKED_FIELD_BITS / 2)                      /* 20 */
#define KIMM_PACKED_TAG_MAX    ((1u << KIMM_PACKED_TAG_BITS) - 1u)              /* 2^20 - 1 */
#define KIMM_PACKED_FIELD_MAX  (((intptr_t)1 << (KIMM_PACKED_FIELD_BITS - 1)) - 1) /* 2^39 - 1 */
#define KIMM_PACKED_FIELD_MIN  (-((intptr_t)1 << (KIMM_PACKED_FIELD_BITS - 1)))    /* -2^39   */
#define KIMM_PACKED2_FIELD_MAX (((intptr_t)1 << (KIMM_PACKED2_FIELD_BITS - 1)) - 1) /* 2^19 - 1 */
#define KIMM_PACKED2_FIELD_MIN (-((intptr_t)1 << (KIMM_PACKED2_FIELD_BITS - 1)))    /* -2^19   */
/* nfields selector value (the single bit at position 3). */
#define KIMM_PACKED_NF1 ((uintptr_t)1 << 3)

/* Does this word carry a b011 packed (single- or double-field) ctor? */
static inline int kis_imm_packed(const KValue *v) {
  return ((uintptr_t)v & KIMM_TAG_MASK) == KIMM_PACKED;
}
/* Is this packed word a TWO-field ctor (nfields bit set)?  Only meaningful when
 * kis_imm_packed(v) already holds. */
static inline int kimm_packed_is2(const KValue *v) {
  return ((uintptr_t)v & KIMM_PACKED_NF1) != 0;
}
/* The tag id of a packed ctor (the 20-bit field above the 3-bit tag and the
 * 1-bit nfields selector; unsigned because the id is small and non-negative).
 * Identical position for the single- and double-field forms. */
static inline int kimm_packed_tagid(const KValue *v) {
  return (int)(((uintptr_t)v >> (3 + KIMM_PACKED_NF_BITS)) & KIMM_PACKED_TAG_MAX);
}
/* The single-field word, reconstructed.  An ARITHMETIC >> of the top 40 bits
 * sign-extends the stored field word (which itself may be a negative
 * immediate-Int word like (value<<3)|1), so the recovered KValue* has the field's
 * original low tag bits and value — a self-describing immediate. */
static inline KValue *kimm_packed_field(const KValue *v) {
  return (KValue *)(uintptr_t)((intptr_t)(uintptr_t)v >> KIMM_PACKED_HDR_BITS);
}
/* A two-field packed ctor's field `i` (i ∈ {0,1}), reconstructed.  field0 sits in
 * the low 20 bits of the payload region (bits 24..43), field1 in the high 20
 * (bits 44..63).  Each slot is sign-extended out so its whole immediate word —
 * with its own low 3 tag bits — is recovered verbatim.  field1 uses a plain
 * arithmetic >> (it is the top slot); field0 is shifted up to the sign bit first,
 * then arithmetic >> back down, so its 20-bit two's-complement is sign-extended. */
static inline KValue *kimm_packed2_field(const KValue *v, int i) {
  intptr_t w = (intptr_t)(uintptr_t)v;
  if (i == 0) {
    /* Hoist field0's MSB to bit 63: shift left by (64 - HDR - 20) = 20, then
     * arithmetic >> by (64 - 20) = 44 to land it sign-extended at bit 0. */
    intptr_t up = w << (64 - KIMM_PACKED_HDR_BITS - KIMM_PACKED2_FIELD_BITS);
    return (KValue *)(uintptr_t)(up >> (64 - KIMM_PACKED2_FIELD_BITS));
  }
  /* field1 is the top slot: a plain arithmetic >> past header + field0 sign-
   * extends it directly. */
  return (KValue *)(uintptr_t)(w >> (KIMM_PACKED_HDR_BITS + KIMM_PACKED2_FIELD_BITS));
}
/* Does the field value `f` qualify to be packed into a SINGLE-field b011 word?
 * It must be an immediate (NOT a heap pointer — those stay boxed), and its whole
 * word, viewed as a signed integer, must fit the 40-bit signed field range so the
 * arithmetic >> in kimm_packed_field recovers it without loss. */
static inline int kctor_field_packs(const KValue *f) {
  if (!kis_imm(f)) return 0;                /* a b000 heap pointer cannot pack */
  intptr_t w = (intptr_t)(uintptr_t)f;      /* the field's whole immediate word */
  return w >= KIMM_PACKED_FIELD_MIN && w <= KIMM_PACKED_FIELD_MAX;
}
/* Does the field value `f` qualify to be packed into a TWO-field b011 slot?  Same
 * immediate requirement, but the per-slot budget is only 20 bits, so the whole
 * word must fit the 20-bit signed range for kimm_packed2_field to recover it. */
static inline int kctor_field2_packs(const KValue *f) {
  if (!kis_imm(f)) return 0;
  intptr_t w = (intptr_t)(uintptr_t)f;
  return w >= KIMM_PACKED2_FIELD_MIN && w <= KIMM_PACKED2_FIELD_MAX;
}
/* Does the tag id fit the 20-bit packed-discriminant field?  Every PROGRAM ctor
 * id (KCT_USER_BASE + ctor count) is far below 2^20, but the kappart2 CK-machine
 * OP node ids live at KRT2_OP_BASE = 0x40000000 (2^30) — those action nodes (e.g.
 * ioPure) must NOT pack (their id would be truncated and the CK-machine would
 * misdispatch), so packing also gates on the id fitting.  Shared by the single-
 * and double-field paths (the tagId field is the same 20 bits in both). */
static inline int kctor_tagid_packs(int tagid) {
  return tagid >= 0 && (unsigned)tagid <= KIMM_PACKED_TAG_MAX;
}
/* Pack a single-field ctor (nfields=0).  Caller must have checked argc == 1 AND
 * kctor_field_packs(field); `tagid` must fit KIMM_PACKED_TAG_BITS.  The field's
 * whole word is shifted into the top 40 bits, the tag id into the 20 above the
 * nfields selector, and the nfields bit is left 0. */
static inline KValue *kmk_imm_packed(int tagid, const KValue *field) {
  uintptr_t fw  = (uintptr_t)field;                 /* whole field word, verbatim */
  uintptr_t tag = (uintptr_t)(unsigned)tagid & KIMM_PACKED_TAG_MAX;
  return (KValue *)((fw << KIMM_PACKED_HDR_BITS)
                    | (tag << (3 + KIMM_PACKED_NF_BITS)) | KIMM_PACKED);
}
/* Pack a two-field ctor (nfields=1).  Caller must have checked argc == 2 AND
 * kctor_field2_packs(field0) AND kctor_field2_packs(field1); `tagid` must fit
 * KIMM_PACKED_TAG_BITS.  field0's low 20 bits go directly above the header;
 * field1's low 20 bits go above field0.  The nfields bit is set. */
static inline KValue *kmk_imm_packed2(int tagid, const KValue *field0,
                                      const KValue *field1) {
  uintptr_t f0  = (uintptr_t)field0 & ((((uintptr_t)1) << KIMM_PACKED2_FIELD_BITS) - 1);
  uintptr_t f1  = (uintptr_t)field1 & ((((uintptr_t)1) << KIMM_PACKED2_FIELD_BITS) - 1);
  uintptr_t tag = (uintptr_t)(unsigned)tagid & KIMM_PACKED_TAG_MAX;
  return (KValue *)((f1 << (KIMM_PACKED_HDR_BITS + KIMM_PACKED2_FIELD_BITS))
                    | (f0 << KIMM_PACKED_HDR_BITS)
                    | (tag << (3 + KIMM_PACKED_NF_BITS))
                    | KIMM_PACKED_NF1 | KIMM_PACKED);
}

/* ── lifecycle ─────────────────────────────────────────────────────── */
void krt_init(void);                 /* GC_INIT once, at the top of main */

/* ── allocation (Boehm GC) ─────────────────────────────────────────── */
void *kgc_alloc(size_t n);           /* scanned: may contain pointers    */
void *kgc_alloc_atomic(size_t n);    /* pointer-free (string/byte blobs) */
void  kgc_free(void *p);             /* S3 free-on-zero shell/slab release */
unsigned long long kgc_debug_free_count(void);

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
/* K_ARRAY elemkind discriminator (MUTABLE-ARRAY-DESIGN §5.1/§5.3.3).  ONLY the
 * boxed kind is produced today; the scalar kinds reserve their values so the
 * later INT64/DOUBLE slabs slot in beside the boxed ops with no renumbering. */
enum { KARR_BOXED = 0, KARR_INT64 = 1, KARR_DOUBLE = 2 };
/* Boxed mutable array (MUTABLE-ARRAY-DESIGN §5.1): N-cell generalization of
 * K_REF.  `karr_new(n, init)` allocates a SCANNED n-slot KValue* slab, transfers
 * `init` into the first slot, and counts each additional boxed slot alias with
 * kdup(init); get/set/len are O(1).  Index out of range / wrong tag traps via
 * krt_fail (the runtime floor, §6 tier 3). */
KValue *karr_new(int64_t n, KValue *init);
KValue *karr_get(KValue *arr, int64_t i);
KValue *karr_set(KValue *arr, int64_t i, KValue *v);  /* returns Unit */
int64_t karr_len(KValue *arr);
KValue *kfgn(void *p, const char *kind);
KValue *kinject(int tagid, const char *tag, KValue *payload); /* §13 variant injection */
KValue *kthunk(KIOFn fn, KEnv *env, int memo);       /* §19 Delay(0)/Memo(1)  */
KValue *kbyte(unsigned char w);                      /* §6.5 byte             */
KValue *kbytes(const unsigned char *p, size_t len);  /* §29.5 byte sequence   */

/* ── environment ───────────────────────────────────────────────────── */
KEnv   *kpush(KValue *v, KEnv *e);
KValue *kvar(KEnv *e, int ix);
void    kenv_set_val(KEnv *e, KValue *v);  /* backpatch a pushed env slot (CLetRec) */

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
KValue *kp_intAnd(KValue *, KValue *);   KValue *kp_intOr(KValue *, KValue *);
KValue *kp_intXor(KValue *, KValue *);
KValue *kp_addDouble(KValue *, KValue *); KValue *kp_subDouble(KValue *, KValue *);
KValue *kp_mulDouble(KValue *, KValue *); KValue *kp_divDouble(KValue *, KValue *);
KValue *kp_negDouble(KValue *);           KValue *kp_ltDouble(KValue *, KValue *);
KValue *kp_floatEq(KValue *, KValue *);   KValue *kp_eqDouble(KValue *, KValue *);
/* §6.1.7 libm floating-point / transcendental math (show.c). */
KValue *kp_sqrt(KValue *);  KValue *kp_sin(KValue *);  KValue *kp_cos(KValue *);
KValue *kp_tan(KValue *);   KValue *kp_asin(KValue *); KValue *kp_acos(KValue *);
KValue *kp_atan(KValue *);  KValue *kp_exp(KValue *);  KValue *kp_log(KValue *);
KValue *kp_floor(KValue *); KValue *kp_ceil(KValue *); KValue *kp_fabs(KValue *);
KValue *kp_pow(KValue *, KValue *);       KValue *kp_atan2(KValue *, KValue *);
KValue *kp_showFixed(KValue *, KValue *); /* Nat -> Double -> String (%.*f) */
KValue *kp_stringAppend(KValue *, KValue *); KValue *kp_eqStr(KValue *, KValue *);
KValue *kp_ltStr(KValue *, KValue *);
KValue *kp_eqScalar(KValue *, KValue *);  KValue *kp_ltScalar(KValue *, KValue *);
KValue *kp_showInt(KValue *);   KValue *kp_showDouble(KValue *);
KValue *kp_showScalar(KValue *); KValue *kp_showStringLit(KValue *);
KValue *kp_intToDouble(KValue *);
KValue *kp_eqByte(KValue *, KValue *); KValue *kp_ltByte(KValue *, KValue *);

/* LR1: unbox a K_INT to int64 for the typed unboxed Int workers (kwi_*).  A
 * non-K_INT value (a K_BIGINT that does not fit, or any non-Int box) sets the
 * overflow/escape flag so the caller re-runs the boxed worker — the unboxed
 * fast path is only taken when every argument is an inline K_INT. */
static inline int64_t kunbox_i64(KValue *v, int *ovf) {
  if (kis_imm_int(v)) return kimm_int_val(v);   /* Stage 1: immediate Int */
  kassert_live(v);
  if (!kis_imm(v) && v->tag == K_INT) return v->as.i;
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
  kassert_live(v);
  if (!kis_imm(v) && v->tag == K_DBL) return v->as.d;  /* immediates are never K_DBL */
  *ovf = 1;
  return 0.0;
}
double kunbox_dbl_runtime(KValue *v, int *ovf); /* linkable LLVM mirror of kunbox_dbl */
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
int      kis_int_any(KValue *v);
const char *kas_str(KValue *v);   /* NUL-terminated bytes of a K_STR (§26 CtString) */
void    *kas_fgn(KValue *v);      /* opaque pointer of a K_FGN (§26 CtHandle/CtRawPtr) */
void    *kas_fgn_kind(KValue *v, const char *kind);
uint64_t kas_u64(KValue *v);      /* Integer as unsigned 64-bit (§26 U64/Usize) */
KValue  *ku64(uint64_t u);        /* box an unsigned 64-bit as a non-negative Integer */

/* ── references ────────────────────────────────────────────────────── */
KValue  *kref_get(KValue *r);
KValue  *kref_set(KValue *r, KValue *v);         /* returns Unit          */

/* ── IO execution ──────────────────────────────────────────────────── */
KValue  *krun_io(KValue *action);    /* run an IO action to a result      */
KValue  *krun_io_checked(KValue *action); /* run IO; abort on uncaught typed failure */
KValue  *krt2_run_op_sync(KValue *action); /* drive a non-suspending krt2_* OP node on the synchronous bridge (rt.c) */
KValue  *krt2_run_legacy_finalizers(KValue *primary, KValue **defers, int *count);
KValue  *krt2_finally(KValue *body, KValue *fin);
int      krt2_is_reraise_action(KValue *v); /* raw OP_RERAISE value returned through legacy bridges */

/* list helpers for `for` loops and FFI glue (Cons "::" / Nil) */
KValue  *knil(void);
KValue  *kcons(KValue *h, KValue *t);
int      kis_cons(KValue *v);

/* ── native host-binding actions (§26/§27.1.1) ─────────────────────── */
/* A native action carries a DIRECT C function pointer emitted by the
 * backend for a manifest-declared symbol — there is no name table and no
 * strcmp dispatch.  `knative` builds the curried (argc=0) action value;
 * `kapp` accumulates args and a saturated action is the suspended UIO
 * action that `krun_io` runs by calling `fn`.  The `_blocking` variants carry
 * the §26.1.4 classification through partial application so the CK-machine can
 * park the fiber and run the host call off-worker. */
KValue  *knative(KNativeFn fn, int arity, const char *kind, int is_io);
KValue  *knative_sat(KNativeFn fn, int arity, KValue **args, int is_io);
KValue  *knative_blocking(KNativeFn fn, int arity, const char *kind, int is_io);
KValue  *knative_sat_blocking(KNativeFn fn, int arity, KValue **args, int is_io);

#endif /* KAPPART_H */
