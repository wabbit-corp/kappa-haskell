/* atomic.c — §29.1 std.atomic: AtomicRef cells (capability rt-atomics).
 *
 * An `AtomicRef a` is a distinct mutable cell (§29.1: "not an ordinary var, Ref,
 * TVar, or MonadRef").  Source `Integer` is arbitrary precision (§6), so the
 * native cell stores the canonical `KValue *` under a per-cell mutex instead of
 * narrowing through a fixed-width scalar atomic.  That keeps the native backend
 * semantically aligned with the interpreter for large integers while still
 * making each load/store/exchange/CAS/fetch-* one indivisible runtime operation.
 *
 * Memory orders arrive as boxed §29.1 LoadOrder/StoreOrder/RmwOrder/
 * CasFailureOrder constructor codes.  A mutex is at least acquire/release for
 * the operation, so validating the order code is still useful, but the current
 * representation intentionally does not promise lock-free hardware atomics.
 */
#include "internal.h"

#include <string.h>

/* How to re-box the scalar cell on load/return. */
typedef enum { AKIND_INT = 0, AKIND_BOOL = 1 } AtomicKind;

struct AtomicRef {
  pthread_mutex_t mu;
  KValue *cell;
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

static AtomicKind atomic_kind_of(KValue *v) {
  if (kis_int_any(v)) return AKIND_INT;
  if (kctor_tagid(v) == KCT_TRUE || kctor_tagid(v) == KCT_FALSE) return AKIND_BOOL;
  krt_fail("atomic: value is not an AtomicValue (expected Bool or Integer)");
}

static void atomic_check_kind(struct AtomicRef *r, KValue *v) {
  if (atomic_kind_of(v) != r->kind) {
    krt_fail("atomic: value type does not match AtomicRef cell type");
  }
}

static int atomic_value_eq(AtomicKind k, KValue *a, KValue *b) {
  switch (k) {
    case AKIND_INT: return kas_bool(kp_eqInt(a, b));
    case AKIND_BOOL: return kas_bool(a) == kas_bool(b);
  }
  return 0;
}

static struct AtomicRef *as_aref(KValue *r) {
  return (struct AtomicRef *)kas_fgn_kind(r, KRT2_KIND_ATOMIC);
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
  pthread_mutex_init(&r->mu, NULL);
  krc_mark_shared_recursive(v);
  r->cell = v;
  r->kind = atomic_kind_of(v);
  return kfgn(r, KRT2_KIND_ATOMIC);
}

KValue *krt2_atomic_load(KValue *order, KValue *ref) {
  (void)load_order(order);
  struct AtomicRef *r = as_aref(ref);
  pthread_mutex_lock(&r->mu);
  KValue *v = r->cell;
  pthread_mutex_unlock(&r->mu);
  return kdup(v);
}

KValue *krt2_atomic_store(KValue *order, KValue *ref, KValue *v) {
  (void)store_order(order);
  struct AtomicRef *r = as_aref(ref);
  atomic_check_kind(r, v);
  pthread_mutex_lock(&r->mu);
  KValue *old = r->cell;
  krc_mark_shared_recursive(v);
  r->cell = v;
  pthread_mutex_unlock(&r->mu);
  kdrop(old);
  return kunit();
}

KValue *krt2_atomic_exchange(KValue *order, KValue *ref, KValue *v) {
  (void)rmw_order(order);
  struct AtomicRef *r = as_aref(ref);
  atomic_check_kind(r, v);
  pthread_mutex_lock(&r->mu);
  KValue *old = r->cell;
  krc_mark_shared_recursive(v);
  r->cell = v;
  pthread_mutex_unlock(&r->mu);
  return old;
}

/* Strong compare-exchange.  Returns the WITNESSED old value (boxed) — on success
 * the matched `expected`, on failure the actual current cell value.  The prelude
 * decides Exchanged vs NotExchanged from witnessed==expected (the §29.1 strong-
 * CAS contract), so this never builds a result constructor itself. */
KValue *krt2_atomic_compare_exchange(KValue *succ, KValue *fail,
                                     KValue *ref, KValue *expected, KValue *desired) {
  (void)rmw_order(succ);
  (void)cas_fail_order(fail);
  struct AtomicRef *r = as_aref(ref);
  atomic_check_kind(r, expected);
  atomic_check_kind(r, desired);
  pthread_mutex_lock(&r->mu);
  KValue *old = r->cell;
  int exchanged = atomic_value_eq(r->kind, old, expected);
  if (exchanged) {
    krc_mark_shared_recursive(desired);
    r->cell = desired;
  }
  pthread_mutex_unlock(&r->mu);
  if (!exchanged) {
    KValue *witness = kdup(old);
    kdrop(desired);
    return witness;
  }
  return old;
}

/* fetch-* return the OLD value; AtomicInteger gates these to integer cells. */
KValue *krt2_atomic_fetch_add(KValue *order, KValue *ref, KValue *v) {
  (void)rmw_order(order);
  struct AtomicRef *r = as_aref(ref);
  atomic_check_kind(r, v);
  if (r->kind != AKIND_INT) krt_fail("atomicFetchAdd: AtomicRef is not an Integer cell");
  pthread_mutex_lock(&r->mu);
  KValue *old = r->cell;
  KValue *nv = kp_addInt(old, v);
  krc_mark_shared_recursive(nv);
  r->cell = nv;
  pthread_mutex_unlock(&r->mu);
  return old;
}
KValue *krt2_atomic_fetch_sub(KValue *order, KValue *ref, KValue *v) {
  (void)rmw_order(order);
  struct AtomicRef *r = as_aref(ref);
  atomic_check_kind(r, v);
  if (r->kind != AKIND_INT) krt_fail("atomicFetchSub: AtomicRef is not an Integer cell");
  pthread_mutex_lock(&r->mu);
  KValue *old = r->cell;
  KValue *nv = kp_subInt(old, v);
  krc_mark_shared_recursive(nv);
  r->cell = nv;
  pthread_mutex_unlock(&r->mu);
  return old;
}
KValue *krt2_atomic_fetch_and(KValue *order, KValue *ref, KValue *v) {
  (void)rmw_order(order);
  struct AtomicRef *r = as_aref(ref);
  atomic_check_kind(r, v);
  if (r->kind != AKIND_INT) krt_fail("atomicFetchAnd: AtomicRef is not an Integer cell");
  pthread_mutex_lock(&r->mu);
  KValue *old = r->cell;
  KValue *nv = kp_intAnd(old, v);
  krc_mark_shared_recursive(nv);
  r->cell = nv;
  pthread_mutex_unlock(&r->mu);
  return old;
}
KValue *krt2_atomic_fetch_or(KValue *order, KValue *ref, KValue *v) {
  (void)rmw_order(order);
  struct AtomicRef *r = as_aref(ref);
  atomic_check_kind(r, v);
  if (r->kind != AKIND_INT) krt_fail("atomicFetchOr: AtomicRef is not an Integer cell");
  pthread_mutex_lock(&r->mu);
  KValue *old = r->cell;
  KValue *nv = kp_intOr(old, v);
  krc_mark_shared_recursive(nv);
  r->cell = nv;
  pthread_mutex_unlock(&r->mu);
  return old;
}
KValue *krt2_atomic_fetch_xor(KValue *order, KValue *ref, KValue *v) {
  (void)rmw_order(order);
  struct AtomicRef *r = as_aref(ref);
  atomic_check_kind(r, v);
  if (r->kind != AKIND_INT) krt_fail("atomicFetchXor: AtomicRef is not an Integer cell");
  pthread_mutex_lock(&r->mu);
  KValue *old = r->cell;
  KValue *nv = kp_intXor(old, v);
  krc_mark_shared_recursive(nv);
  r->cell = nv;
  pthread_mutex_unlock(&r->mu);
  return old;
}

/* ── codegen entry points (§34.5.3) ───────────────────────────────────────
 * The §29.1 std.atomic surface lowers each op to one of the @__atomic*@ prims
 * (Kappa.Prelude).  Both backends compile a SATURATED IO prim to a `knative_sat`
 * suspended action whose entry point is a `KValue **`-taking wrapper that
 * krun_io fires (C.hs:2113 / LLVM.hs:3350).  These adapters unpack that array
 * and forward to the positional `krt2_atomic_*` boxed atomic-cell ops above, in the same
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
