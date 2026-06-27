/* atomic.c — §29.1 std.atomic: lock-free AtomicRef cells (capability rt-atomics).
 *
 * An `AtomicRef a` is a distinct mutable cell (§29.1: "not an ordinary var, Ref,
 * TVar, or MonadRef").  The required `AtomicValue` instances — `Bool` and the
 * exact-width / pointer-width integers — all fit in a machine word, so the cell
 * is a single `_Atomic(int64_t)` operated on with C11 atomics under the caller's
 * requested memory order.  The boxed KValue is unboxed to the scalar on the way
 * in and re-boxed on the way out; a per-cell `kind` records how to re-box
 * (`Bool` -> kbool, integer -> kint).  This gives TRUE value semantics for
 * compare-exchange (a real hardware CAS on the scalar, not a boxed-pointer CAS
 * that would spuriously fail on equal-but-distinct boxes), and real lock-free
 * fetch-add/sub/and/or/xor.
 *
 * Memory orders arrive as boxed §29.1 LoadOrder/StoreOrder/RmwOrder/
 * CasFailureOrder constructors.  They are nullary data constructors, so they map
 * to C11 memory_order by their numeric tag id (LR2) in the spec's canonical
 * declaration order — a numeric switch, no string dispatch.
 */
#include "internal.h"

/* How to re-box the scalar cell on load/return. */
typedef enum { AKIND_INT = 0, AKIND_BOOL = 1 } AtomicKind;

struct AtomicRef {
  _Atomic(int64_t) cell;
  AtomicKind kind;
};

/* §29.1 CompareExchangeResult: the runtime does NOT build the Exchanged /
 * NotExchanged constructor.  Codegen assigns user-constructor tag ids GLOBALLY
 * (KCT_USER_BASE + a cross-program sort index), so a runtime-stamped tag would
 * not match the compiled `match` arms.  Instead krt2_atomic_compare_exchange
 * returns only the WITNESSED value (the old value the CAS observed); the
 * std.atomic prelude wrapper reconstructs Exchanged/NotExchanged in SOURCE (so
 * codegen tags them) by the §29.1 strong-CAS contract: the exchange succeeded
 * iff the witnessed old value equals `expected`. */

/* ── value <-> scalar ─────────────────────────────────────────────────── */

static int64_t atomic_unbox(KValue *v) {
  if (kis_imm_int(v)) return kimm_int_val(v);   /* Stage 1 immediate Int */
  /* Stage 1b: Bool is now a b010 nullary immediate, not a boxed K_CTOR. */
  if (kis_imm_ctor(v)) return kas_bool(v);
  if (kis_imm(v))
    krt_fail("atomic: value is not an AtomicValue (expected Bool or a fixed-width Int)");
  if (v->tag == K_INT) return v->as.i;
  if (v->tag == K_CTOR) return kas_bool(v); /* a retired boxed Bool carrier */
  krt_fail("atomic: value is not an AtomicValue (expected Bool or a fixed-width Int)");
}

static AtomicKind atomic_kind_of(KValue *v) {
  if (kis_imm_int(v)) return AKIND_INT;         /* Stage 1 immediate Int */
  if (kis_imm_ctor(v)) return AKIND_BOOL;       /* Stage 1b: Bool immediate */
  if (kis_imm(v))
    krt_fail("atomic: value is not an AtomicValue (expected Bool or a fixed-width Int)");
  if (v->tag == K_INT) return AKIND_INT;
  if (v->tag == K_CTOR) return AKIND_BOOL;
  krt_fail("atomic: value is not an AtomicValue (expected Bool or a fixed-width Int)");
}

static KValue *atomic_rebox(int64_t s, AtomicKind k) {
  return k == AKIND_BOOL ? kbool((int)s) : kint(s);
}

static struct AtomicRef *as_aref(KValue *r) {
  if (kis_imm(r) || r->tag != K_FGN) krt_fail("atomic: argument is not an AtomicRef");
  return (struct AtomicRef *)r->as.fgn.p;
}

/* ── memory-order mapping ──────────────────────────────────────────────
 * The order arrives as a small Integer CODE — the §29.1 canonical declaration-
 * order index of the LoadOrder/StoreOrder/RmwOrder/CasFailureOrder constructor,
 * computed by the std.atomic prelude wrappers (Kappa.Prelude) and passed in as a
 * boxed/immediate Int.  We deliberately do NOT switch on the constructor's
 * kctor_tagid: codegen assigns user-constructor tag ids GLOBALLY (KCT_USER_BASE
 * + a cross-program sort index, Repr.assignUserCtorTags), so a ctor's tag bears
 * no relation to its per-type position.  An Integer code is codegen-independent
 * and identical across the C and LLVM backends.  Each code maps onto exactly one
 * C11 memory_order — every §29.1 order is realised faithfully (no downgrade).  */

static memory_order load_order(KValue *o) {
  switch (kas_int(o)) {
    case 0: return memory_order_relaxed; /* LoadRelaxed */
    case 1: return memory_order_acquire; /* LoadAcquire */
    case 2: return memory_order_seq_cst; /* LoadSeqCst  */
    default: krt_fail("atomic: bad LoadOrder code");
  }
}
static memory_order store_order(KValue *o) {
  switch (kas_int(o)) {
    case 0: return memory_order_relaxed; /* StoreRelaxed */
    case 1: return memory_order_release; /* StoreRelease */
    case 2: return memory_order_seq_cst; /* StoreSeqCst  */
    default: krt_fail("atomic: bad StoreOrder code");
  }
}
static memory_order rmw_order(KValue *o) {
  switch (kas_int(o)) {
    case 0: return memory_order_relaxed; /* RmwRelaxed */
    case 1: return memory_order_acquire; /* RmwAcquire */
    case 2: return memory_order_release; /* RmwRelease */
    case 3: return memory_order_acq_rel; /* RmwAcqRel  */
    case 4: return memory_order_seq_cst; /* RmwSeqCst  */
    default: krt_fail("atomic: bad RmwOrder code");
  }
}
static memory_order cas_fail_order(KValue *o) {
  switch (kas_int(o)) {
    case 0: return memory_order_relaxed; /* CasFailRelaxed */
    case 1: return memory_order_acquire; /* CasFailAcquire */
    case 2: return memory_order_seq_cst; /* CasFailSeqCst  */
    default: krt_fail("atomic: bad CasFailureOrder code");
  }
}

/* ── operations (§29.1) ───────────────────────────────────────────────── */

KValue *krt2_new_atomic_ref(KValue *v) {
  struct AtomicRef *r = (struct AtomicRef *)kgc_alloc(sizeof *r);
  atomic_init(&r->cell, atomic_unbox(v));
  r->kind = atomic_kind_of(v);
  return kfgn(r, KRT2_KIND_ATOMIC);
}

KValue *krt2_atomic_load(KValue *order, KValue *ref) {
  struct AtomicRef *r = as_aref(ref);
  return atomic_rebox(atomic_load_explicit(&r->cell, load_order(order)), r->kind);
}

KValue *krt2_atomic_store(KValue *order, KValue *ref, KValue *v) {
  struct AtomicRef *r = as_aref(ref);
  atomic_store_explicit(&r->cell, atomic_unbox(v), store_order(order));
  return kunit();
}

KValue *krt2_atomic_exchange(KValue *order, KValue *ref, KValue *v) {
  struct AtomicRef *r = as_aref(ref);
  int64_t old = atomic_exchange_explicit(&r->cell, atomic_unbox(v), rmw_order(order));
  return atomic_rebox(old, r->kind);
}

/* Strong compare-exchange.  Returns the WITNESSED old value (boxed) — on success
 * the matched `expected`, on failure the actual current cell value.  The prelude
 * decides Exchanged vs NotExchanged from witnessed==expected (the §29.1 strong-
 * CAS contract), so this never builds a result constructor itself. */
KValue *krt2_atomic_compare_exchange(KValue *succ, KValue *fail,
                                     KValue *ref, KValue *expected, KValue *desired) {
  struct AtomicRef *r = as_aref(ref);
  int64_t exp = atomic_unbox(expected);
  int64_t des = atomic_unbox(desired);
  /* On success the CAS replaces the cell and leaves `exp` = the (matched) old
   * value; on failure it writes the actual current value back into `exp`. */
  (void)atomic_compare_exchange_strong_explicit(
      &r->cell, &exp, des, rmw_order(succ), cas_fail_order(fail));
  return atomic_rebox(exp, r->kind);
}

/* fetch-* return the OLD value; AtomicInteger gates these to integer cells. */
KValue *krt2_atomic_fetch_add(KValue *order, KValue *ref, KValue *v) {
  struct AtomicRef *r = as_aref(ref);
  return atomic_rebox(atomic_fetch_add_explicit(&r->cell, atomic_unbox(v), rmw_order(order)), r->kind);
}
KValue *krt2_atomic_fetch_sub(KValue *order, KValue *ref, KValue *v) {
  struct AtomicRef *r = as_aref(ref);
  return atomic_rebox(atomic_fetch_sub_explicit(&r->cell, atomic_unbox(v), rmw_order(order)), r->kind);
}
KValue *krt2_atomic_fetch_and(KValue *order, KValue *ref, KValue *v) {
  struct AtomicRef *r = as_aref(ref);
  return atomic_rebox(atomic_fetch_and_explicit(&r->cell, atomic_unbox(v), rmw_order(order)), r->kind);
}
KValue *krt2_atomic_fetch_or(KValue *order, KValue *ref, KValue *v) {
  struct AtomicRef *r = as_aref(ref);
  return atomic_rebox(atomic_fetch_or_explicit(&r->cell, atomic_unbox(v), rmw_order(order)), r->kind);
}
KValue *krt2_atomic_fetch_xor(KValue *order, KValue *ref, KValue *v) {
  struct AtomicRef *r = as_aref(ref);
  return atomic_rebox(atomic_fetch_xor_explicit(&r->cell, atomic_unbox(v), rmw_order(order)), r->kind);
}

/* ── codegen entry points (§34.5.3) ───────────────────────────────────────
 * The §29.1 std.atomic surface lowers each op to one of the @__atomic*@ prims
 * (Kappa.Prelude).  Both backends compile a SATURATED IO prim to a `knative_sat`
 * suspended action whose entry point is a `KValue **`-taking wrapper that
 * krun_io fires (C.hs:2113 / LLVM.hs:3350).  These adapters unpack that array
 * and forward to the positional `krt2_atomic_*` lock-free ops above, in the same
 * argument order the prelude wrapper passes them.  Atomic ops never park, so the
 * synchronous bridge is the correct (and complete) path — no CK-machine node.
 *
 * The argument order MATCHES the prim's prelude type exactly:
 *   __newAtomicRef          value
 *   __atomicLoad            order cell
 *   __atomicStore           order cell value
 *   __atomicExchange        order cell value
 *   __atomicCompareExchange success failure cell expected desired
 *   __atomicFetch{Add,...}  order cell operand
 */
KValue *kpf_io___newAtomicRef(KValue **a) { return krt2_new_atomic_ref(a[0]); }
KValue *kpf_io___atomicLoad(KValue **a) { return krt2_atomic_load(a[0], a[1]); }
KValue *kpf_io___atomicStore(KValue **a) { return krt2_atomic_store(a[0], a[1], a[2]); }
KValue *kpf_io___atomicExchange(KValue **a) { return krt2_atomic_exchange(a[0], a[1], a[2]); }
KValue *kpf_io___atomicCompareExchange(KValue **a) {
  return krt2_atomic_compare_exchange(a[0], a[1], a[2], a[3], a[4]);
}
KValue *kpf_io___atomicFetchAdd(KValue **a) { return krt2_atomic_fetch_add(a[0], a[1], a[2]); }
KValue *kpf_io___atomicFetchSub(KValue **a) { return krt2_atomic_fetch_sub(a[0], a[1], a[2]); }
KValue *kpf_io___atomicFetchAnd(KValue **a) { return krt2_atomic_fetch_and(a[0], a[1], a[2]); }
KValue *kpf_io___atomicFetchOr(KValue **a)  { return krt2_atomic_fetch_or(a[0], a[1], a[2]); }
KValue *kpf_io___atomicFetchXor(KValue **a) { return krt2_atomic_fetch_xor(a[0], a[1], a[2]); }
