/* stm.c — software transactional memory (§18.1.13, §32.2.9, rt-shared-stm).
 *
 * GHC-style optimistic STM (RESEARCH.md §1; REVIEW.md M16–M19): a transaction is
 * a pure tree of reads/writes run against a thread-local journal, then committed
 * under a global lock with read-set validation.  Reads are LOCK-FREE (a single
 * acquire-load of an immutable {value,version} box gives a consistent snapshot),
 * so read-heavy transactions run in parallel across workers; only commit and
 * retry-park take the global mutex.
 *
 *  - serializable: commit validates that every read TVar's version is unchanged;
 *    if so it installs the writes and bumps versions atomically under the lock,
 *    else it re-runs the transaction (§32.2.9).
 *  - retry: parks the fiber on the watcher list of EVERY TVar it read, after
 *    re-validating under the lock (closes the lost-wakeup window, M16); a commit
 *    that writes one of those TVars wakes it to re-run.
 *  - orElse l r: runs r only if l retries, and KEEPS l's reads in the combined
 *    read-set (rolling back only l's writes) so a later change to a TVar l read
 *    wakes the parked orElse (M17).
 *  - newTVar in-txn: a fresh TVar reachable only through the transaction; its
 *    writes commit/drop with the transaction (M19).
 *  - commit is uninterruptible: the whole transaction+commit runs synchronously
 *    within one OP_ATOMICALLY dispatch; the only interruption point is retry-park
 *    (§32.2.9 / §32.2.5).
 *
 * KNOWN v1 DEVIATIONS (STM-review minors, to refine):
 *  - The RUN phase is uninterruptible too (not just commit): a long pure
 *    transaction with no retry defers an interrupt until it finishes, since
 *    fiber_step only checks interrupt_pending between dispatches.  ZIO makes the
 *    run phase interruptible; threading interrupt_pending into stm_run's loop is
 *    the fix.  Transactions are short in practice, so this is acceptable for v1.
 *  - A lock-free reader can observe a TORN snapshot across a multi-write commit
 *    in-flight (X's new box + Y's old box); such an attempt can NEVER commit (the
 *    read-set version check rejects it), so serializability of COMMITTED
 *    transactions holds, but a pure closure forced on the torn pair must be total
 *    (it could otherwise diverge before reaching validation — the GHC motivation
 *    for periodic revalidation; the run-interruptibility fix above bounds it).
 */
#include "internal.h"

#include <gc.h>
#include <stdlib.h>
#include <string.h>

/* One global STM domain: this mutex serializes commits and watcher-list edits. */
static pthread_mutex_t g_stm = PTHREAD_MUTEX_INITIALIZER;
static _Atomic uint64_t g_tick = 1;   /* monotonic commit tick -> new versions */

/* ── builders ───────────────────────────────────────────────────────────── */
static KValue *sop1(int op, const char *n, KValue *a) { KValue *x[1] = { a }; return kctor(op, n, 1, x); }
static KValue *sop2(int op, const char *n, KValue *a, KValue *b) { KValue *x[2] = { a, b }; return kctor(op, n, 2, x); }
KValue *krt2_stm_pure(KValue *v)                { return sop1(STM_PURE, "stm.pure", v); }
KValue *krt2_stm_bind(KValue *m, KValue *k)     { return sop2(STM_BIND, "stm.bind", m, k); }
KValue *krt2_new_tvar(KValue *init)             { return sop1(STM_NEW, "stm.newTVar", init); }
KValue *krt2_read_tvar(KValue *tv)              { return sop1(STM_READ, "stm.readTVar", tv); }
KValue *krt2_write_tvar(KValue *tv, KValue *v)  { return sop2(STM_WRITE, "stm.writeTVar", tv, v); }
KValue *krt2_retry(void)                        { return kctor0(STM_RETRY, "stm.retry"); }
KValue *krt2_or_else(KValue *l, KValue *r)      { return sop2(STM_ORELSE, "stm.orElse", l, r); }
KValue *krt2_check(KValue *b)                   { return kas_bool(b) ? krt2_stm_pure(kunit()) : krt2_retry(); }
KValue *krt2_atomically(KValue *stm)            { return sop1(OP_ATOMICALLY, "rt.atomically", stm); }

/* ── the transaction journal ────────────────────────────────────────────── */
typedef struct { TVar *tv; uint64_t ver; } REnt;
typedef struct { TVar *tv; KValue *val; } WEnt;
typedef struct { REnt *r; int nr, capr; WEnt *w; int nw, capw; } Journal;

static void j_read_record(Journal *j, TVar *tv, uint64_t ver) {
  if (j->nr == j->capr) {
    int nc = j->capr ? j->capr * 2 : 8;
    REnt *na = (REnt *)GC_MALLOC(sizeof(REnt) * nc);
    memcpy(na, j->r, sizeof(REnt) * j->nr); j->r = na; j->capr = nc;
  }
  j->r[j->nr].tv = tv; j->r[j->nr].ver = ver; j->nr++;
}
/* APPEND-ONLY write log (never update in place): a later writeTVar appends a new
 * entry, and j_read / commit scan newest-first.  This is what makes orElse's
 * length-truncation rollback (j->nw = saved_nw) correct — truncation discards the
 * left branch's overwrites, not just its appended-past-the-frame writes (STM
 * review BLOCKER; REVIEW.md M17).  Newest-first scan = last writer wins. */
static void j_write(Journal *j, TVar *tv, KValue *v) {
  if (j->nw == j->capw) {
    int nc = j->capw ? j->capw * 2 : 8;
    WEnt *na = (WEnt *)GC_MALLOC(sizeof(WEnt) * nc);
    memcpy(na, j->w, sizeof(WEnt) * j->nw); j->w = na; j->capw = nc;
  }
  j->w[j->nw].tv = tv; j->w[j->nw].val = v; j->nw++;
}
static KValue *j_read(Journal *j, TVar *tv) {
  for (int i = j->nw - 1; i >= 0; i--) if (j->w[i].tv == tv) return j->w[i].val; /* read-after-write (newest) */
  VBox *b = atomic_load_explicit(&tv->box, memory_order_acquire);
  j_read_record(j, tv, b->version);
  return b->val;
}
/* Has this TVar already been installed by a NEWER write-log entry (index > i)? */
static int j_newer_write(Journal *j, int i) {
  for (int k = j->nw - 1; k > i; k--) if (j->w[k].tv == j->w[i].tv) return 1;
  return 0;
}

/* ── the transaction interpreter (iterative; stack-safe) ────────────────── */
enum { FK_BIND, FK_ORELSE };
typedef struct { int kind; KValue *a; int saved_nw; } Frame;

/* Returns 1 = committed-locally with *out set, 0 = retry. */
static int stm_run(KValue *stm, Journal *j, KValue **out) {
  Frame *fr = NULL; int nf = 0, cap = 0;
  KValue *cur = stm;
  for (;;) {
    int op = kctor_tagid(cur);
    KValue *val = NULL; int retry = 0;
    switch (op) {
      case STM_PURE:  val = kctor_arg(cur, 0); break;
      case STM_READ:  val = j_read(j, (TVar *)kas_fgn(kctor_arg(cur, 0))); break;
      case STM_WRITE: j_write(j, (TVar *)kas_fgn(kctor_arg(cur, 0)), kctor_arg(cur, 1)); val = kunit(); break;
      case STM_NEW: {
        TVar *tv = (TVar *)GC_MALLOC(sizeof(TVar));
        VBox *b = (VBox *)GC_MALLOC(sizeof(VBox));
        b->val = kctor_arg(cur, 0); b->version = 0;
        atomic_store(&tv->box, b); tv->watchers = NULL;
        val = kfgn(tv, KRT2_KIND_TVAR);
        break;
      }
      case STM_BIND:
        if (nf == cap) { int nc = cap ? cap * 2 : 16; Frame *na = (Frame *)GC_MALLOC(sizeof(Frame) * nc);
          for (int i = 0; i < nf; i++) na[i] = fr[i]; fr = na; cap = nc; }
        fr[nf].kind = FK_BIND; fr[nf].a = kctor_arg(cur, 1); fr[nf].saved_nw = 0; nf++;
        cur = kctor_arg(cur, 0); continue;
      case STM_ORELSE:
        if (nf == cap) { int nc = cap ? cap * 2 : 16; Frame *na = (Frame *)GC_MALLOC(sizeof(Frame) * nc);
          for (int i = 0; i < nf; i++) na[i] = fr[i]; fr = na; cap = nc; }
        fr[nf].kind = FK_ORELSE; fr[nf].a = kctor_arg(cur, 1); fr[nf].saved_nw = j->nw; nf++;
        cur = kctor_arg(cur, 0); continue;
      case STM_RETRY: retry = 1; break;
      default:        val = cur; break;   /* a bare value */
    }
    if (!retry) {                          /* value: pop to the next bind */
      for (;;) {
        if (nf == 0) { *out = val; return 1; }
        Frame f = fr[--nf];
        if (f.kind == FK_BIND) { cur = kapp(f.a, val); break; }
        /* FK_ORELSE on the success path: left won; drop it, keep popping */
      }
    } else {                               /* retry: pop to the nearest orElse-right */
      for (;;) {
        if (nf == 0) return 0;             /* whole transaction retries */
        Frame f = fr[--nf];
        if (f.kind == FK_ORELSE) {
          j->nw = f.saved_nw;              /* roll back left's WRITES; keep its READS (M17) */
          cur = f.a; break;
        }
        /* FK_BIND: discarded by a retry */
      }
    }
  }
}

/* Unlink every watcher node of `f` from the TVars it was last retry-parked on.
 * Called on re-entry to atomically (and never re-runs leave stale watchers) and
 * makes a moved-on fiber leave no spurious-wakeup hazard (STM review MAJOR). */
static void stm_unpark(Fiber *f) {
  if (f->stm_nreads == 0) return;
  pthread_mutex_lock(&g_stm);
  for (int i = 0; i < f->stm_nreads; i++) {
    Waiter **pp = &f->stm_reads[i]->watchers;
    while (*pp) { if ((*pp)->f == f) *pp = (*pp)->next; else pp = &(*pp)->next; }
  }
  f->stm_nreads = 0; f->stm_reads = NULL;
  pthread_mutex_unlock(&g_stm);
}

/* ── atomically (the IO boundary) ───────────────────────────────────────── */
int krt2i_op_atomically(Rt *rt, Fiber *f, KValue *stm) {
  stm_unpark(f);   /* drop watchers from any previous retry-park of this fiber */
  for (;;) {
    Journal j; memset(&j, 0, sizeof j);
    KValue *result;
    int committed_locally = stm_run(stm, &j, &result);

    if (committed_locally) {
      pthread_mutex_lock(&g_stm);
      int valid = 1;
      for (int i = 0; i < j.nr; i++) {
        VBox *b = atomic_load_explicit(&j.r[i].tv->box, memory_order_acquire);
        if (b->version != j.r[i].ver) { valid = 0; break; }
      }
      if (!valid) { pthread_mutex_unlock(&g_stm); continue; }   /* conflict: re-run */

      uint64_t tick = atomic_fetch_add_explicit(&g_tick, 1, memory_order_relaxed) + 1;
      Waiter *wake = NULL;
      for (int i = 0; i < j.nw; i++) {
        if (j_newer_write(&j, i)) continue;                /* install each TVar once (newest) */
        TVar *tv = j.w[i].tv;
        VBox *nb = (VBox *)GC_MALLOC(sizeof(VBox));
        nb->val = j.w[i].val; nb->version = tick;
        atomic_store_explicit(&tv->box, nb, memory_order_release);
        Waiter *w = tv->watchers; tv->watchers = NULL;     /* take all watchers (de-duped by the wake CAS) */
        while (w) { Waiter *nx = w->next; w->next = wake; wake = w; w = nx; }
      }
      pthread_mutex_unlock(&g_stm);
      for (Waiter *w = wake; w; ) { Waiter *nx = w->next; krt2i_wake(rt, w->f, NULL); w = nx; }
      f->cur = krt2_pure(result);          /* deliver the transaction's value */
      return 1;
    }

    /* retry: re-validate under the lock, then park on every read TVar (M16). */
    pthread_mutex_lock(&g_stm);
    int stale = 0;
    for (int i = 0; i < j.nr; i++) {
      VBox *b = atomic_load_explicit(&j.r[i].tv->box, memory_order_acquire);
      if (b->version != j.r[i].ver) { stale = 1; break; }
    }
    if (stale) { pthread_mutex_unlock(&g_stm); continue; }      /* changed: re-run, don't park */
    TVar **rds = j.nr ? (TVar **)GC_MALLOC(sizeof(TVar *) * j.nr) : NULL;
    for (int i = 0; i < j.nr; i++) {
      Waiter *w = (Waiter *)GC_MALLOC(sizeof(Waiter));
      w->f = f; w->want_exit = 0; w->next = j.r[i].tv->watchers; j.r[i].tv->watchers = w;
      rds[i] = j.r[i].tv;
    }
    f->stm_reads = rds; f->stm_nreads = j.nr;   /* recorded for stm_unpark on re-entry */
    atomic_store(&f->status, F_PARKED);
    pthread_mutex_unlock(&g_stm);
    return 0;   /* parked; f->cur is still the OP_ATOMICALLY node -> re-runs on wake */
  }
}
