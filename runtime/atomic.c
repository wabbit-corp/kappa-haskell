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

/* §29.1 CompareExchangeResult, canonical declaration order (Exchanged first).
 * The runtime constructs these, so the tag ids must match the .kp data decl. */
#define ATAG_EXCHANGED    0
#define ATAG_NOTEXCHANGED 1

/* ── value <-> scalar ─────────────────────────────────────────────────── */

static int64_t atomic_unbox(KValue *v) {
  if (v->tag == K_INT) return v->as.i;
  if (v->tag == K_CTOR) return kas_bool(v); /* the only ctor AtomicValue is Bool */
  krt_fail("atomic: value is not an AtomicValue (expected Bool or a fixed-width Int)");
}

static AtomicKind atomic_kind_of(KValue *v) {
  if (v->tag == K_INT) return AKIND_INT;
  if (v->tag == K_CTOR) return AKIND_BOOL;
  krt_fail("atomic: value is not an AtomicValue (expected Bool or a fixed-width Int)");
}

static KValue *atomic_rebox(int64_t s, AtomicKind k) {
  return k == AKIND_BOOL ? kbool((int)s) : kint(s);
}

static struct AtomicRef *as_aref(KValue *r) {
  if (r->tag != K_FGN) krt_fail("atomic: argument is not an AtomicRef");
  return (struct AtomicRef *)r->as.fgn.p;
}

/* ── memory-order mapping (numeric tag id, §29.1 canonical order) ──────── */

static memory_order load_order(KValue *o) {
  switch (kctor_tagid(o)) {
    case 0: return memory_order_relaxed; /* LoadRelaxed */
    case 1: return memory_order_acquire; /* LoadAcquire */
    case 2: return memory_order_seq_cst; /* LoadSeqCst  */
    default: krt_fail("atomic: bad LoadOrder");
  }
}
static memory_order store_order(KValue *o) {
  switch (kctor_tagid(o)) {
    case 0: return memory_order_relaxed; /* StoreRelaxed */
    case 1: return memory_order_release; /* StoreRelease */
    case 2: return memory_order_seq_cst; /* StoreSeqCst  */
    default: krt_fail("atomic: bad StoreOrder");
  }
}
static memory_order rmw_order(KValue *o) {
  switch (kctor_tagid(o)) {
    case 0: return memory_order_relaxed; /* RmwRelaxed */
    case 1: return memory_order_acquire; /* RmwAcquire */
    case 2: return memory_order_release; /* RmwRelease */
    case 3: return memory_order_acq_rel; /* RmwAcqRel  */
    case 4: return memory_order_seq_cst; /* RmwSeqCst  */
    default: krt_fail("atomic: bad RmwOrder");
  }
}
static memory_order cas_fail_order(KValue *o) {
  switch (kctor_tagid(o)) {
    case 0: return memory_order_relaxed; /* CasFailRelaxed */
    case 1: return memory_order_acquire; /* CasFailAcquire */
    case 2: return memory_order_seq_cst; /* CasFailSeqCst  */
    default: krt_fail("atomic: bad CasFailureOrder");
  }
}

static KValue *make_cas_result(int exchanged, KValue *val) {
  KValue *a[1]; a[0] = val;
  return exchanged ? kctor(ATAG_EXCHANGED, "Exchanged", 1, a)
                   : kctor(ATAG_NOTEXCHANGED, "NotExchanged", 1, a);
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

KValue *krt2_atomic_compare_exchange(KValue *succ, KValue *fail,
                                     KValue *ref, KValue *expected, KValue *desired) {
  struct AtomicRef *r = as_aref(ref);
  int64_t exp = atomic_unbox(expected);
  int64_t des = atomic_unbox(desired);
  /* On success the CAS replaces the cell and leaves `exp` = the (matched) old
   * value; on failure it writes the actual current value back into `exp`. */
  int ok = atomic_compare_exchange_strong_explicit(
      &r->cell, &exp, des, rmw_order(succ), cas_fail_order(fail));
  return make_cas_result(ok, atomic_rebox(exp, r->kind));
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
