/* value.c — the boxed-value model.
 *
 * Split out of kappart.c (see boxed.h).  Owns alloc_val /
 * alloc_val_atomic, the value constructors, the environment, application +
 * the trampoline, deconstruction / matching, literal equality, and the
 * unboxing accessors + refs.  The bignum boundary it escapes to (kmpz_set_i64,
 * kbig_from_mpz, kfrom_mpz, kload_mpz, kint_cmp, krat, as_rat) lives in
 * bignum.c and is reached through boxed.h. */
#include "kappart.h"
#include "internal.h"
#include "boxed.h"

#include <gmp.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct KRefCell {
  pthread_mutex_t mu;
  KValue *val;
};

typedef struct KArrayBox {
  pthread_mutex_t mu;
  KValue *slots[];
} KArrayBox;
KValue *alloc_val(KTag tag) {
  KValue *v = (KValue *)kgc_alloc(sizeof(KValue));
  v->tag = tag;
  v->rc = 1; /* Every heap KValue is born with one owner. S4 kdup/kdrop maintain
              * this header for strict-FREESET reclamation; Boehm remains the
              * allocation/rooting backstop for retained shapes. */
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
  v->rc = 1; /* Born with one owner (see alloc_val). GC_MALLOC_ATOMIC does not
              * zero, so set rc explicitly here. */
  return v;
}

/* ── Perceus RC Stage S2.0: dup/drop counters + report ──────────────────────
 * The DEBUG-only running totals `kdup`/`kdrop` (kappart.h) bump, plus the
 * `krc_report` leak-trend probe.  Behind NDEBUG so release builds carry no
 * counter storage and stay byte-identical in cost.  `krc_report` is always
 * defined (a no-op under NDEBUG) so the symbol resolves regardless of build. */
_Atomic int k_rc_enabled = 1;
static _Atomic unsigned long long k_rc_reclaims_total = 0;

void krc_set_enabled(int enabled) {
  atomic_store_explicit(&k_rc_enabled, enabled ? 1 : 0, memory_order_relaxed);
}

unsigned long long krc_debug_reclaim_count(void) {
  return atomic_load_explicit(&k_rc_reclaims_total, memory_order_relaxed);
}

static void krc_note_reclaim(void) {
  atomic_fetch_add_explicit(&k_rc_reclaims_total, 1, memory_order_relaxed);
}

#ifndef NDEBUG
_Atomic unsigned long long k_dups_total = 0;
_Atomic unsigned long long k_drops_total = 0;
_Atomic int k_rc_poison_enabled = 0;

void krc_poison_set_enabled(int enabled) {
  atomic_store_explicit(&k_rc_poison_enabled, enabled ? 1 : 0, memory_order_relaxed);
}
#endif

void krc_report(void) {
#ifndef NDEBUG
  unsigned long long dups = atomic_load_explicit(&k_dups_total, memory_order_relaxed);
  unsigned long long drops = atomic_load_explicit(&k_drops_total, memory_order_relaxed);
  fprintf(stderr, "krc_report: dups=%llu drops=%llu net=%lld\n",
          dups, drops, (long long)drops - (long long)dups);
#endif
}

typedef struct {
  KValue **items;
  KValue **inline_items;
  size_t len;
  size_t cap;
  size_t inline_cap;
} KWork;

static pthread_mutex_t g_thunk_cache_lock;
static pthread_once_t g_thunk_cache_lock_once = PTHREAD_ONCE_INIT;
static pthread_mutex_t g_shared_mark_lock;
static pthread_once_t g_shared_mark_lock_once = PTHREAD_ONCE_INIT;

static void kthunk_cache_lock_init(void) {
  pthread_mutex_init(&g_thunk_cache_lock, NULL);
}

static void kthunk_cache_lock(void) {
  pthread_once(&g_thunk_cache_lock_once, kthunk_cache_lock_init);
  pthread_mutex_lock(&g_thunk_cache_lock);
}

static void kthunk_cache_unlock(void) {
  pthread_mutex_unlock(&g_thunk_cache_lock);
}

static void kshared_mark_lock_init(void) {
  pthread_mutexattr_t attr;
  pthread_mutexattr_init(&attr);
  pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_RECURSIVE);
  pthread_mutex_init(&g_shared_mark_lock, &attr);
  pthread_mutexattr_destroy(&attr);
}

static void kshared_mark_lock(void) {
  pthread_once(&g_shared_mark_lock_once, kshared_mark_lock_init);
  pthread_mutex_lock(&g_shared_mark_lock);
}

static void kshared_mark_unlock(void) {
  pthread_mutex_unlock(&g_shared_mark_lock);
}

static KValue *kthunk_cached_value_snapshot(KValue *v) {
  if (!v->as.thunk.memo) return NULL;
  kthunk_cache_lock();
  KValue **cached = v->as.thunk.cache;
  KValue *r = cached ? cached[0] : NULL;
  kthunk_cache_unlock();
  return r;
}

static KValue *kdup_thunk_cached_value(KValue *thunk, KValue *cached) {
  if (!cached) return NULL;
  if (!krc_is_shared(thunk)) {
    kshared_mark_lock();
    if (!krc_is_shared(thunk)) {
      KValue *owned = kdup(cached);
      kshared_mark_unlock();
      return owned;
    }
    kshared_mark_unlock();
  }
  if (!kis_imm(cached)) krc_mark_shared_recursive(cached);
  return kdup(cached);
}

static void kwork_init(KWork *stack, KValue **inline_items, size_t inline_cap) {
  stack->items = inline_items;
  stack->inline_items = inline_items;
  stack->len = 0;
  stack->cap = inline_cap;
  stack->inline_cap = inline_cap;
  for (size_t i = 0; i < inline_cap; i++) inline_items[i] = NULL;
}

static void kwork_dispose(KWork *stack) {
  if (stack->items && stack->items != stack->inline_items) kgc_free(stack->items);
  stack->items = NULL;
  stack->inline_items = NULL;
  stack->len = 0;
  stack->cap = 0;
  stack->inline_cap = 0;
}

static void kwork_grow(KWork *stack) {
  size_t old_cap = stack->cap;
  size_t new_cap = old_cap ? old_cap * 2 : 64;
  KValue **items = (KValue **)kgc_alloc(sizeof(KValue *) * new_cap);
  for (size_t i = 0; i < stack->len; i++) items[i] = stack->items[i];
  for (size_t i = stack->len; i < new_cap; i++) items[i] = NULL;
  KValue **old_items = stack->items;
  stack->items = items;
  stack->cap = new_cap;
  if (old_items && old_items != stack->inline_items) kgc_free(old_items);
}

static void kwork_push(KWork *stack, KValue *v) {
  if (!v || kis_imm(v)) return;
  if (stack->len == stack->cap) kwork_grow(stack);
  stack->items[stack->len++] = v;
}

static KValue *kwork_pop(KWork *stack) {
  if (stack->len == 0) return NULL;
  KValue *v = stack->items[--stack->len];
  stack->items[stack->len] = NULL;
  return v;
}

static void krc_mark_child(KWork *stack, KValue *v);

static void krc_mark_env(KWork *stack, KEnv *env) {
  for (KEnv *e = env; e; e = e->next) krc_mark_child(stack, e->val);
}

static void krc_mark_shared_env_recursive(KEnv *env) {
  for (KEnv *e = env; e; e = e->next) krc_mark_shared_recursive(e->val);
}

static int krc_mark_shared_child_for_publish(KValue *v) {
  if (!v || kis_imm(v) || krc_is_shared(v)) return 0;
  krc_mark_shared_shallow(v);
  return 1;
}

static void krc_mark_child(KWork *stack, KValue *v) {
  if (!krc_mark_shared_child_for_publish(v)) return;
  kwork_push(stack, v);
}

static void krc_mark_mutable_child(KWork *stack, KWork *owned, KValue *v) {
  if (!krc_mark_shared_child_for_publish(v)) return;
  kwork_push(stack, v);
  kwork_push(owned, kdup(v));
}

static void krc_mark_children(KWork *stack, KWork *owned, KValue *v) {
  switch (v->tag) {
    case K_CTOR:
      for (int i = 0; i < v->as.ctor.argc; i++) krc_mark_child(stack, v->as.ctor.args[i]);
      break;
    case K_REC:
      for (int i = 0; i < v->as.rec.n; i++) krc_mark_child(stack, v->as.rec.vals[i]);
      break;
    case K_CLO:
      krc_mark_env(stack, v->as.clo.env);
      break;
    case K_IO:
      krc_mark_env(stack, v->as.io.env);
      break;
    case K_REF:
      if (v->as.ref.cell) {
        pthread_mutex_lock(&v->as.ref.cell->mu);
        krc_mark_mutable_child(stack, owned, v->as.ref.cell->val);
        pthread_mutex_unlock(&v->as.ref.cell->mu);
      }
      break;
    case K_ARRAY:
      if (v->as.arr.elemkind == KARR_BOXED) {
        KArrayBox *box = (KArrayBox *)v->as.arr.elems;
        pthread_mutex_lock(&box->mu);
        for (int64_t i = 0; i < v->as.arr.len; i++) krc_mark_mutable_child(stack, owned, box->slots[i]);
        pthread_mutex_unlock(&box->mu);
      }
      break;
    case K_FGN:
      krt2i_mark_fgn_payload_shared(v->as.fgn.kind, v->as.fgn.p);
      break;
    case K_VARIANT:
      krc_mark_child(stack, v->as.var.payload);
      break;
    case K_THUNK:
      krc_mark_env(stack, v->as.thunk.env);
      krc_mark_child(stack, kthunk_cached_value_snapshot(v));
      break;
    case K_BOUNCE:
    case K_IOTAIL:
    case K_IOEFFECT:
      krc_mark_child(stack, v->as.bounce.fn);
      if (v->tag == K_BOUNCE) krc_mark_child(stack, v->as.bounce.arg);
      break;
    case K_IOFINALLY:
      krc_mark_child(stack, v->as.iofin.action);
      for (int i = 0; i < v->as.iofin.n; i++) krc_mark_child(stack, v->as.iofin.defers[i]);
      break;
    case K_FAIL:
      krc_mark_child(stack, v->as.fail.err);
      break;
    case K_NATIVE:
      for (int i = 0; i < v->as.native.argc; i++) krc_mark_child(stack, v->as.native.args[i]);
      break;
    default:
      break;
  }
}

#ifndef NDEBUG
static int kwork_contains(KWork *work, KValue *v) {
  for (size_t i = 0; i < work->len; i++) {
    if (work->items[i] == v) return 1;
  }
  return 0;
}

static void krc_assert_shared_child(KWork *stack, KWork *seen, KValue *v);

static void krc_assert_shared_env(KWork *stack, KWork *seen, KEnv *env) {
  for (KEnv *e = env; e; e = e->next) krc_assert_shared_child(stack, seen, e->val);
}

static void krc_assert_shared_child(KWork *stack, KWork *seen, KValue *v) {
  if (!v || kis_imm(v)) return;
  assert(krc_is_shared(v) && "publish point reached an unshared KValue after recursive mark");
  if (kwork_contains(seen, v)) return;
  kwork_push(seen, v);
  kwork_push(stack, v);
}

static KValue *krc_assert_owned_mutable_child(KWork *owned, KValue *v) {
  if (!v || kis_imm(v)) return v;
  assert(krc_is_shared(v) && "publish point reached an unshared mutable-storage child");
  KValue *snapshot = kdup(v);
  kwork_push(owned, snapshot);
  return snapshot;
}

typedef struct {
  KWork *stack;
  KWork *seen;
} KAssertSharedCtx;

static void krc_assert_fgn_child(void *ctx_, KValue *v) {
  KAssertSharedCtx *ctx = (KAssertSharedCtx *)ctx_;
  krc_assert_shared_child(ctx->stack, ctx->seen, v);
}

static void krc_assert_shared_children(KWork *stack, KWork *seen, KWork *owned, KValue *v) {
  switch (v->tag) {
    case K_CTOR:
      for (int i = 0; i < v->as.ctor.argc; i++) krc_assert_shared_child(stack, seen, v->as.ctor.args[i]);
      break;
    case K_REC:
      for (int i = 0; i < v->as.rec.n; i++) krc_assert_shared_child(stack, seen, v->as.rec.vals[i]);
      break;
    case K_CLO:
      krc_assert_shared_env(stack, seen, v->as.clo.env);
      break;
    case K_IO:
      krc_assert_shared_env(stack, seen, v->as.io.env);
      break;
    case K_REF:
      if (v->as.ref.cell) {
        pthread_mutex_lock(&v->as.ref.cell->mu);
        KValue *child = krc_assert_owned_mutable_child(owned, v->as.ref.cell->val);
        pthread_mutex_unlock(&v->as.ref.cell->mu);
        krc_assert_shared_child(stack, seen, child);
      }
      break;
    case K_ARRAY:
      if (v->as.arr.elemkind == KARR_BOXED) {
        KArrayBox *box = (KArrayBox *)v->as.arr.elems;
        pthread_mutex_lock(&box->mu);
        for (int64_t i = 0; i < v->as.arr.len; i++) {
          KValue *child = krc_assert_owned_mutable_child(owned, box->slots[i]);
          krc_assert_shared_child(stack, seen, child);
        }
        pthread_mutex_unlock(&box->mu);
      }
      break;
    case K_FGN: {
      KAssertSharedCtx ctx = { stack, seen };
      krt2i_assert_fgn_payload_shared(v->as.fgn.kind, v->as.fgn.p, krc_assert_fgn_child, &ctx);
      break;
    }
    case K_VARIANT:
      krc_assert_shared_child(stack, seen, v->as.var.payload);
      break;
    case K_THUNK:
      krc_assert_shared_env(stack, seen, v->as.thunk.env);
      krc_assert_shared_child(stack, seen, kthunk_cached_value_snapshot(v));
      break;
    case K_BOUNCE:
    case K_IOTAIL:
    case K_IOEFFECT:
      krc_assert_shared_child(stack, seen, v->as.bounce.fn);
      if (v->tag == K_BOUNCE) krc_assert_shared_child(stack, seen, v->as.bounce.arg);
      break;
    case K_IOFINALLY:
      krc_assert_shared_child(stack, seen, v->as.iofin.action);
      for (int i = 0; i < v->as.iofin.n; i++) krc_assert_shared_child(stack, seen, v->as.iofin.defers[i]);
      break;
    case K_FAIL:
      krc_assert_shared_child(stack, seen, v->as.fail.err);
      break;
    case K_NATIVE:
      for (int i = 0; i < v->as.native.argc; i++) krc_assert_shared_child(stack, seen, v->as.native.args[i]);
      break;
    default:
      break;
  }
}

static void krc_assert_shared_recursive(KValue *root) {
  KWork stack, seen, owned;
  KValue *stack_inline[64];
  KValue *seen_inline[64];
  KValue *owned_inline[64];
  kwork_init(&stack, stack_inline, sizeof stack_inline / sizeof stack_inline[0]);
  kwork_init(&seen, seen_inline, sizeof seen_inline / sizeof seen_inline[0]);
  kwork_init(&owned, owned_inline, sizeof owned_inline / sizeof owned_inline[0]);
  krc_assert_shared_child(&stack, &seen, root);
  KValue *v;
  while ((v = kwork_pop(&stack)) != NULL) krc_assert_shared_children(&stack, &seen, &owned, v);
  while ((v = kwork_pop(&owned)) != NULL) kdrop(v);
  kwork_dispose(&owned);
  kwork_dispose(&seen);
  kwork_dispose(&stack);
}
#endif

void krc_mark_shared_recursive(KValue *root) {
  kshared_mark_lock();
  KWork stack, owned;
  KValue *inline_items[64];
  KValue *owned_inline[64];
  kwork_init(&stack, inline_items, sizeof inline_items / sizeof inline_items[0]);
  kwork_init(&owned, owned_inline, sizeof owned_inline / sizeof owned_inline[0]);
  krc_mark_child(&stack, root);
  KValue *v;
  while ((v = kwork_pop(&stack)) != NULL) krc_mark_children(&stack, &owned, v);
  while ((v = kwork_pop(&owned)) != NULL) kdrop(v);
  kwork_dispose(&owned);
  kwork_dispose(&stack);
#ifndef NDEBUG
  krc_assert_shared_recursive(root);
#endif
  kshared_mark_unlock();
}

static void kfree_drop_child(KWork *stack, KValue *child) {
  if (!child || kis_imm(child)) return;
  uint32_t cur = krc_word(child);
  if (cur & KRC_SATURATED_BIT) return;
  uint32_t n = cur & KRC_COUNT_MASK;
#ifndef NDEBUG
  assert(n > 0 && "kfree_recursive: child rc underflow");
#endif
  if (n == 0) return;
  if (cur & KRC_SHARED_BIT) {
    n = krc_shared_release_decrement(child, "kfree_recursive: shared child rc underflow");
    if (n == 0) return;
  } else {
    child->rc = n - 1u;
  }
#ifndef NDEBUG
  atomic_fetch_add_explicit(&k_drops_total, 1, memory_order_relaxed);
#endif
  if (n == 1 && kis_rc_freeable(child)) kwork_push(stack, child);
}

static void kfree_visit(KWork *stack, KValue *v) {
  switch (v->tag) {
    case K_CTOR:
      for (int i = 0; i < v->as.ctor.argc; i++) kfree_drop_child(stack, v->as.ctor.args[i]);
      kgc_free(v->as.ctor.args);
      break;
    case K_REC:
      for (int i = 0; i < v->as.rec.n; i++) kfree_drop_child(stack, v->as.rec.vals[i]);
      kgc_free(v->as.rec.vals);
      break;
    case K_VARIANT:
      kfree_drop_child(stack, v->as.var.payload);
      break;
    case K_STR:
      kgc_free((void *)v->as.str.p);
      break;
    case K_BOUNCE:
      kfree_drop_child(stack, v->as.bounce.fn);
      kfree_drop_child(stack, v->as.bounce.arg);
      break;
    case K_FAIL:
      kfree_drop_child(stack, v->as.fail.err);
      break;
    default:
#ifndef NDEBUG
      assert(!"kfree_visit: non-freeable tag reached the S3.2 free visitor");
#endif
      return;
  }
#ifndef NDEBUG
  if (atomic_load_explicit(&k_rc_poison_enabled, memory_order_relaxed)) {
    krc_note_reclaim();
    __atomic_store_n(&v->rc, 0u, __ATOMIC_RELAXED);
    v->tag = K_FREED;
    return;
  }
#endif
  krc_note_reclaim();
  kgc_free(v);
}

static void kfree_recursive_impl(KValue *root) {
  KWork stack;
  KValue *inline_items[64];
  kwork_init(&stack, inline_items, sizeof inline_items / sizeof inline_items[0]);
  kwork_push(&stack, root);
  KValue *v;
  while ((v = kwork_pop(&stack)) != NULL) {
    if (kis_rc_freeable(v) && krc_count(v) == 0) kfree_visit(&stack, v);
  }
  kwork_dispose(&stack);
}

void kfree_recursive(KValue *root) {
  if (!kis_rc_freeable(root) || krc_count(root) != 0) return;
  kfree_recursive_impl(root);
}

static int kctor_would_pack_value(int tagid, int argc, KValue **args) {
  if (argc == 0) return 1;
  if (!kctor_tagid_packs(tagid)) return 0;
  if (argc == 1) return kctor_field_packs(args[0]);
  if (argc == 2) return kctor_field2_packs(args[0]) && kctor_field2_packs(args[1]);
  return 0;
}

static void kctor_drop_old_fields(KValue *v) {
  KWork stack;
  KValue *inline_items[64];
  kwork_init(&stack, inline_items, sizeof inline_items / sizeof inline_items[0]);
  for (int i = 0; i < v->as.ctor.argc; i++) kfree_drop_child(&stack, v->as.ctor.args[i]);
  kgc_free(v->as.ctor.args);
  KValue *child;
  while ((child = kwork_pop(&stack)) != NULL) {
    if (kis_rc_freeable(child) && krc_count(child) == 0) kfree_visit(&stack, child);
  }
  kwork_dispose(&stack);
}

KValue *kdrop_reuse_ctor(KValue *v, int argc) {
  if (kis_imm(v)) return NULL;
  if (!atomic_load_explicit(&k_rc_enabled, memory_order_relaxed)) return NULL;
  kassert_live(v);
  uint32_t cur = krc_word(v);
  uint32_t n = cur & KRC_COUNT_MASK;
  if ((cur & (KRC_SHARED_BIT | KRC_SATURATED_BIT)) == 0
      && n == 1
      && v->tag == K_CTOR
      && v->as.ctor.argc == argc) {
    return v;
  }
  kdrop(v);
  return NULL;
}

KValue *kreuse_ctor(KValue *token, int tagid, const char *name, int argc, KValue **args) {
  if (token == NULL) return kctor(tagid, name, argc, args);
  if (!atomic_load_explicit(&k_rc_enabled, memory_order_relaxed)) return kctor(tagid, name, argc, args);
  kassert_live(token);
  uint32_t cur = krc_word(token);
  uint32_t n = cur & KRC_COUNT_MASK;
  if ((cur & (KRC_SHARED_BIT | KRC_SATURATED_BIT)) != 0
      || n != 1
      || token->tag != K_CTOR
      || token->as.ctor.argc != argc
      || kctor_would_pack_value(tagid, argc, args)) {
    kdrop(token);
    return kctor(tagid, name, argc, args);
  }

  KValue **new_args = (KValue **)kgc_alloc(sizeof(KValue *) * (size_t)argc);
  for (int i = 0; i < argc; i++) new_args[i] = args[i];
  kctor_drop_old_fields(token);
  __atomic_store_n(&token->rc, 1u, __ATOMIC_RELAXED);
  token->tag = K_CTOR;
  token->as.ctor.name = name;
  token->as.ctor.tagid = tagid;
  token->as.ctor.argc = argc;
  token->as.ctor.args = new_args;
  return token;
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

int kis_fail(KValue *v) {
  kassert_live(v);
  return v && !kis_imm(v) && v->tag == K_FAIL;
}

KValue *kref_new(KValue *init) {
  KValue *r = alloc_val(K_REF);
  KRefCell *cell = (KRefCell *)kgc_alloc(sizeof(KRefCell));
  pthread_mutex_init(&cell->mu, NULL);
  cell->val = init;
  r->as.ref.cell = cell;
  return r;
}

/* ── mutable arrays (MUTABLE-ARRAY-DESIGN §5.1) ─────────────────────────────
 * K_REF generalized from 1 cell to N.  The boxed storage is a synchronized,
 * scanned slot box: every slot is a base KValue* the collector must trace,
 * exactly like K_CTOR's args (§5.2 rule 1).  Private arrays read/write slots
 * directly under the S4 thread-local invariant; shared arrays take the box mutex
 * while acquiring or replacing a counted slot owner.  Allocating it atomic would let Boehm collect live
 * elements out from under the array, so the boxed kind MUST be scanned.  `len`
 * is stored, so karr_len is O(1) and pure; each slot is reached from the storage
 * base, never from an interior-only pointer (§5.2 rule 2). */
KValue *karr_new(int64_t n, KValue *init) {
  if (n < 0) krt_fail("karr_new: negative length");
  KValue *r = alloc_val(K_ARRAY);
  /* SCANNED: the box holds base KValue* pointers (boxed kind).  kgc_alloc of 0
   * slots is avoided (request at least one slot) so `elems` is a valid base. */
  KArrayBox *box = (KArrayBox *)kgc_alloc(sizeof(KArrayBox) + sizeof(KValue *) * (size_t)(n > 0 ? n : 1));
  pthread_mutex_init(&box->mu, NULL);
  for (int64_t i = 0; i < n; i++) box->slots[i] = (i == 0 ? init : kdup(init));
  if (n == 0) kdrop(init);
  r->as.arr.elems = (void *)box;
  r->as.arr.len = n;
  r->as.arr.cap = n;
  r->as.arr.elemkind = KARR_BOXED;
  r->as.arr.element_size = 8;
  return r;
}
KValue *karr_get(KValue *arr, int64_t i) {
  kassert_live(arr);
  if (kis_imm(arr) || arr->tag != K_ARRAY) krt_fail("karr_get: not an array");
  if (i < 0 || i >= arr->as.arr.len) krt_fail("karr_get: index out of range");
  KArrayBox *box = (KArrayBox *)arr->as.arr.elems;
  if (!krc_is_shared(arr)) return kdup(box->slots[i]);
  pthread_mutex_lock(&box->mu);
  KValue *v = kdup(box->slots[i]);
  pthread_mutex_unlock(&box->mu);
  return v;
}
KValue *karr_set(KValue *arr, int64_t i, KValue *v) {
  kassert_live(arr);
  if (kis_imm(arr) || arr->tag != K_ARRAY) krt_fail("karr_set: not an array");
  if (i < 0 || i >= arr->as.arr.len) krt_fail("karr_set: index out of range");
  KArrayBox *box = (KArrayBox *)arr->as.arr.elems;
  if (!krc_is_shared(arr)) {
    KValue *old = box->slots[i];
    box->slots[i] = v;
    kdrop(old);
    return kunit();
  }
  krc_mark_shared_recursive(v);
  pthread_mutex_lock(&box->mu);
  KValue *old = box->slots[i];
  box->slots[i] = v;
  pthread_mutex_unlock(&box->mu);
  kdrop(old);
  return kunit();
}
int64_t karr_len(KValue *arr) {
  kassert_live(arr);
  if (kis_imm(arr) || arr->tag != K_ARRAY) krt_fail("karr_len: not an array");
  return arr->as.arr.len;
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
static KValue *knative_make(KNativeFn fn, int arity, const char *kind, int is_io, int blocking) {
  KValue *r = alloc_val(K_NATIVE);
  r->as.native.fn = fn;
  r->as.native.arity = arity;
  r->as.native.argc = 0;
  r->as.native.args = NULL;
  r->as.native.kind = kind;
  r->as.native.is_io = is_io;
  r->as.native.blocking = blocking;
  return r;
}

KValue *knative(KNativeFn fn, int arity, const char *kind, int is_io) {
  return knative_make(fn, arity, kind, is_io, 0);
}

KValue *knative_blocking(KNativeFn fn, int arity, const char *kind, int is_io) {
  return knative_make(fn, arity, kind, is_io, 1);
}

/* The saturated fast path: build a K_NATIVE holding all `arity` args at once
 * (copied into GC memory so it outlives the caller's argument array).  For an
 * effectful action this is the suspended IO action krun_io fires; codegen
 * emits this only for IO builtins / native symbols. */
static KValue *knative_sat_make(KNativeFn fn, int arity, KValue **args, int is_io, int blocking) {
  KValue *r = alloc_val(K_NATIVE);
  r->as.native.fn = fn;
  r->as.native.arity = arity;
  r->as.native.argc = arity;
  KValue **a = (KValue **)kgc_alloc(sizeof(KValue *) * (size_t)(arity > 0 ? arity : 1));
  for (int i = 0; i < arity; i++) a[i] = args[i];
  r->as.native.args = a;
  r->as.native.kind = "native";
  r->as.native.is_io = is_io;
  r->as.native.blocking = blocking;
  return r;
}

KValue *knative_sat(KNativeFn fn, int arity, KValue **args, int is_io) {
  return knative_sat_make(fn, arity, args, is_io, 0);
}

KValue *knative_sat_blocking(KNativeFn fn, int arity, KValue **args, int is_io) {
  return knative_sat_make(fn, arity, args, is_io, 1);
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
  kassert_live(f);
  int n = f->as.native.argc;
  KValue *r = alloc_val(K_NATIVE);
  r->as.native.fn = f->as.native.fn;
  r->as.native.arity = f->as.native.arity;
  r->as.native.argc = n + 1;
  r->as.native.kind = f->as.native.kind;
  r->as.native.is_io = f->as.native.is_io;
  r->as.native.blocking = f->as.native.blocking;
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
  kassert_live(f);
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
  while (!kis_imm(r)) {   /* an immediate value is never a bounce */
    kassert_live(r);
    if (r->tag != K_BOUNCE) break;
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
  kassert_live(f);
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
  kassert_live(v);
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
  kassert_live(v);
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
  kassert_live(v);
  if (kis_imm(v) || v->tag != K_CTOR) krt_fail("kctor_name: not a constructor");
  return v->as.ctor.name;
}
int kctor_argc(KValue *v) {
  if (kis_imm_ctor(v)) return 0;        /* Stage 1b: a nullary immediate has 0 args */
  /* Stage 1d/1e: a packed ctor has 1 arg (nfields=0) or 2 args (nfields=1). */
  if (kis_imm_packed(v)) return kimm_packed_is2(v) ? 2 : 1;
  kassert_live(v);
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
  kassert_live(v);
  if (kis_imm(v) || v->tag != K_CTOR || i < 0 || i >= v->as.ctor.argc)
    krt_fail("kctor_arg: out of range");
  return v->as.ctor.args[i];
}

KValue *kproj(KValue *rec, const char *name) {
  kassert_live(rec);
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
  kassert_live(v);
  return !kis_imm(v) && v->tag == K_VARIANT && strcmp(v->as.var.tag, tag) == 0;
}
/* LR2: numeric §13 variant dispatch; -1 for a non-variant value (matches no
 * tag id, so a variant pattern test on a non-variant fails). */
int kvariant_tagid(KValue *v) {
  kassert_live(v);
  return (!kis_imm(v) && v->tag == K_VARIANT) ? v->as.var.tagid : -1;
}
int kis_variant(KValue *v) {
  kassert_live(v);
  return !kis_imm(v) && v->tag == K_VARIANT;
}
KValue *kvariant_payload(KValue *v) {
  kassert_live(v);
  if (kis_imm(v) || v->tag != K_VARIANT) krt_fail("kvariant_payload: not a variant");
  return v->as.var.payload;
}

/* §19: force a suspended computation. Delay re-evaluates; Memo caches.
 * A non-thunk value forces to itself (matches the interpreter, which
 * forces through already-evaluated values). */
KValue *kforce(KValue *v) {
  if (kis_imm(v)) return v;   /* an immediate Int is already a value */
  kassert_live(v);
  if (v->tag != K_THUNK) return v;
  if (v->as.thunk.memo) {
    kthunk_cache_lock();
    KValue **cached = v->as.thunk.cache;
    if (cached) {
      KValue *r = cached[0];
      kthunk_cache_unlock();
      return kdup_thunk_cached_value(v, r);
    }
    KEnv *env = v->as.thunk.env;
    int markEnv = krc_is_shared(v);
    kthunk_cache_unlock();
    if (markEnv) krc_mark_shared_env_recursive(env);
  }
  KValue *r = v->as.thunk.fn(v->as.thunk.env);
  if (v->as.thunk.memo) {
    int resultMarked = 0;
    if (krc_is_shared(v)) {
      krc_mark_shared_recursive(r);
      resultMarked = 1;
    }
    for (;;) {
      kthunk_cache_lock();
      if (v->as.thunk.cache) {
        KValue *lost = r;
        KValue *existing = v->as.thunk.cache[0];
        kthunk_cache_unlock();
        r = kdup_thunk_cached_value(v, existing);
        kdrop(lost);
        break;
      }
      if (!resultMarked && krc_is_shared(v)) {
        kthunk_cache_unlock();
        krc_mark_shared_recursive(r);
        resultMarked = 1;
        continue;
      }
      KValue **cell = (KValue **)kgc_alloc(sizeof(KValue *));
      cell[0] = r;
      v->as.thunk.cache = cell;
      r = kdup(r);
      kthunk_cache_unlock();
      break;
    }
  }
  return r;
}

int krec_size(KValue *rec) {
  kassert_live(rec);
  if (kis_imm(rec) || rec->tag != K_REC) krt_fail("krec_size: not a record");
  return rec->as.rec.n;
}

/* §17.2.5 record rest binder: a new record of `rec`'s fields whose names
 * are NOT among excl[0..nexcl). Kept field names alias the original
 * record's (static) name pointers, so no copying of label strings. */
KValue *krec_without(KValue *rec, int nexcl, const char **excl) {
  kassert_live(rec);
  if (kis_imm(rec) || rec->tag != K_REC) krt_fail("krec_without: not a record");
  int n = rec->as.rec.n;
  const char **names = (const char **)kgc_alloc(sizeof(char *) * (size_t)(n ? n : 1));
  KValue **vals = (KValue **)kgc_alloc(sizeof(KValue *) * (size_t)(n ? n : 1));
  int k = 0;
  for (int i = 0; i < n; i++) {
    int excluded = 0;
    for (int j = 0; j < nexcl; j++)
      if (strcmp(rec->as.rec.names[i], excl[j]) == 0) { excluded = 1; break; }
    if (!excluded) { names[k] = rec->as.rec.names[i]; vals[k] = kdup(rec->as.rec.vals[i]); k++; }
  }
  KValue *r = alloc_val(K_REC);
  r->as.rec.n = k;
  r->as.rec.names = names;
  r->as.rec.vals = vals;
  return r;
}

KValue *krec_at(KValue *rec, int i) {
  kassert_live(rec);
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
  kassert_live(v);
  return v->tag == K_INT || v->tag == K_BIGINT;
}

int klit_eq(KValue *a, KValue *b) {
  kassert_live(a);
  kassert_live(b);
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
  kassert_live(v);
  if (v->tag == K_INT) return v->as.i;
  if (v->tag == K_BIGINT) {
    const __mpz_struct *z = (const __mpz_struct *)v->as.big.mpz;
    if (!kmpz_fits_i64_p(z)) krt_fail("kas_int: Integer too large for a machine word");
    return kmpz_get_i64(z);
  }
  krt_fail("kas_int: not an Int");
}
double kas_dbl(KValue *v) {
  kassert_live(v);
  if (kis_imm(v) || v->tag != K_DBL) krt_fail("kas_dbl: not a Double");
  return v->as.d;
}

double kunbox_dbl_runtime(KValue *v, int *ovf) {
  return kunbox_dbl(v, ovf);
}
int kas_bool(KValue *v) {
  /* Stage 1b: True/False are b010 nullary immediates — read the id from the word
   * (no deref).  A retired boxed K_CTOR Bool is still accepted by id. */
  int id;
  if (kis_imm_ctor(v)) id = kimm_ctor_id(v);
  else if (!kis_imm(v)) {
    kassert_live(v);
    if (v->tag == K_CTOR) id = v->as.ctor.tagid;
    else krt_fail("kas_bool: not a Bool");
  }
  else krt_fail("kas_bool: not a Bool");
  if (id == KCT_TRUE) return 1;
  if (id == KCT_FALSE) return 0;
  krt_fail("kas_bool: not a Bool constructor");
}

const char *kas_str(KValue *v) {
  kassert_live(v);
  if (kis_imm(v) || v->tag != K_STR) krt_fail("kas_str: not a String");
  return v->as.str.p; /* kstr() NUL-terminates; length stays authoritative */
}

/* Read an Integer as an unsigned 64-bit value (§26.1.1 U64/Usize), including
 * the >= 2^63 range that kas_int rejects — the low 64 bits of the magnitude. */
uint64_t kas_u64(KValue *v) {
  if (kis_imm_int(v)) return (uint64_t)kimm_int_val(v);   /* Stage 1 immediate */
  kassert_live(v);
  if (!kis_imm(v) && v->tag == K_INT) return (uint64_t)v->as.i;
  mpz_t z; mpz_init(z); kload_mpz(v, z);
  uint64_t u = 0; size_t cnt = 0;
  mpz_export(&u, &cnt, -1, sizeof(uint64_t), 0, 0, z);
  mpz_clear(z);
  return u;
}

void *kas_fgn(KValue *v) {
  kassert_live(v);
  if (kis_imm(v) || v->tag != K_FGN) krt_fail("kas_fgn: not a foreign handle");
  return v->as.fgn.p;
}

void *kas_fgn_kind(KValue *v, const char *kind) {
  kassert_live(v);
  if (kis_imm(v) || v->tag != K_FGN) krt_fail("kas_fgn_kind: not a foreign handle");
  if (strcmp(v->as.fgn.kind, kind) != 0) {
    char msg[256];
    snprintf(msg, sizeof(msg), "wrong foreign handle kind: expected %s, got %s",
             kind, v->as.fgn.kind ? v->as.fgn.kind : "<null>");
    krt_fail(msg);
  }
  return v->as.fgn.p;
}

/* ── references ────────────────────────────────────────────────────── */

KValue *kref_get(KValue *r) {
  kassert_live(r);
  if (kis_imm(r) || r->tag != K_REF) krt_fail("kref_get: not a ref");
  if (!krc_is_shared(r)) return kdup(r->as.ref.cell->val);
  pthread_mutex_lock(&r->as.ref.cell->mu);
  KValue *v = kdup(r->as.ref.cell->val);
  pthread_mutex_unlock(&r->as.ref.cell->mu);
  return v;
}
KValue *kref_set(KValue *r, KValue *v) {
  kassert_live(r);
  if (kis_imm(r) || r->tag != K_REF) krt_fail("kref_set: not a ref");
  if (!krc_is_shared(r)) {
    KValue *old = r->as.ref.cell->val;
    r->as.ref.cell->val = v;
    kdrop(old);
    return kunit();
  }
  krc_mark_shared_recursive(v);
  pthread_mutex_lock(&r->as.ref.cell->mu);
  KValue *old = r->as.ref.cell->val;
  r->as.ref.cell->val = v;
  pthread_mutex_unlock(&r->as.ref.cell->mu);
  kdrop(old);
  return kunit();
}
