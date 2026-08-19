/* reactor.c — the single libuv reactor thread (DESIGN.md §7).
 *
 * One uv_loop owns all async I/O and timers; workers never touch libuv handles
 * directly.  A worker that needs I/O for a fiber pushes an IoReq onto the MPSC
 * request queue and fires uv_async_send (the only thread-safe libuv call); the
 * reactor's async callback drains the queue and starts the libuv operations,
 * whose completion callbacks resume the parked fibers back onto the run queue.
 *
 * v1 implements timers (sleepFor).  TCP/FS/the blocking lane plug in here the
 * same way: an IoOp, a start_* on the reactor, and a completion cb that calls
 * krt2i_resume.  ALL libuv handle ops (start AND stop/close) are reactor-
 * confined; cross-thread submission is the async queue (REVIEW.md M11). */
#include "internal.h"

#include <gc.h>
#include <stdlib.h>

/* A live sleep timer.  malloc'd (not GC) — the parked fiber it resumes is kept
 * alive by rt->all (REVIEW.md B4), so this struct need not be GC-scanned; it is
 * freed in the uv_close callback after the timer fires. */
typedef struct { uv_timer_t timer; Fiber *f; Rt *rt; uint64_t sleep_seq; } SleepTimer;

/* Live-SleepTimer accounting — a test signal: after a clean shutdown this is 0.
 * Incremented once per malloc in start_sleep, decremented once per close here;
 * every disposal path (normal fire, cancel, replace, shutdown-walk) frees the
 * timer through sleep_close_cb, so the count is the number of armed timers. */
static _Atomic int g_live_sleep_timers = 0;
int krt2_live_sleep_timers(void) {
  return atomic_load_explicit(&g_live_sleep_timers, memory_order_relaxed);
}

static void sleep_close_cb(uv_handle_t *h) {
  atomic_fetch_sub_explicit(&g_live_sleep_timers, 1, memory_order_relaxed);
  free(h);
}

static void sleep_timer_cb(uv_timer_t *t) {
  SleepTimer *st = (SleepTimer *)t->data;            /* sleepFor returns Unit */
  Fiber *f = st->f;
  /* This timer callback owns its uv handle and will close it below. If it still
   * occupies f->sleep_timer, clear that reactor-owned slot even when the generation
   * check rejects the callback as stale; otherwise a queued cancel could later read
   * the dangling pointer and close the same handle twice. For the current callback,
   * also clear the worker-visible mirror BEFORE the wake so the resumed fiber never
   * sees a stale-armed timer. */
  int owns_slot = (f->sleep_timer == st);
  int current = owns_slot
      && atomic_load_explicit(&f->sleep_armed, memory_order_acquire)
      && atomic_load_explicit(&f->sleep_seq, memory_order_acquire) == st->sleep_seq;
  if (owns_slot) f->sleep_timer = NULL;
  if (current) {
    atomic_store_explicit(&f->sleep_armed, 0, memory_order_release);
    krt2i_wake(st->rt, f, krt2_pure(krt2i_unit())); /* idempotent: an interrupt
                                                     * may have woken it first */
  }
  uv_close((uv_handle_t *)t, sleep_close_cb);
}

/* Runs on the reactor thread (from the async drain).  fix S2: if the fiber still
 * has a live timer from an earlier park (a masked re-park whose abandonment-cancel
 * has not been processed yet — or, defensively, any straggler), stop+close it
 * FIRST so it cannot fire and orphan-resume.  The fresh timer below re-arms the
 * FULL `nanos` from now, matching the interpreter's masked-re-park semantics
 * (Interp.interruptPoint re-runs the whole threadDelay). */
static void start_sleep(Rt *rt, Fiber *f, uint64_t nanos, uint64_t seq) {
  if (!atomic_load_explicit(&f->sleep_armed, memory_order_acquire)) return;
  if (atomic_load_explicit(&f->sleep_seq, memory_order_acquire) != seq) return;
  SleepTimer *old = (SleepTimer *)f->sleep_timer;
  if (old) {
    f->sleep_timer = NULL;
    uv_timer_stop(&old->timer);
    uv_close((uv_handle_t *)&old->timer, sleep_close_cb);
  }
  SleepTimer *st = (SleepTimer *)malloc(sizeof(SleepTimer));
  st->f = f; st->rt = rt; st->sleep_seq = seq;
  uv_timer_init(&rt->loop, &st->timer);
  st->timer.data = st;
  f->sleep_timer = st;
  atomic_fetch_add_explicit(&g_live_sleep_timers, 1, memory_order_relaxed);
  uint64_t ms = (nanos == 0) ? 0 : (nanos + 999999u) / 1000000u; /* round up */
  uv_timer_start(&st->timer, sleep_timer_cb, ms, 0);
}

/* Runs on the reactor thread.  fix S2: a sleep park was abandoned by an interrupt
 * (masked re-park or unmasked unwind); cancel the original timer so it cannot fire
 * later and CAS-win an unrelated park.  Idempotent: NULL if it already fired or was
 * replaced by start_sleep. */
static void cancel_sleep(Rt *rt, Fiber *f, uint64_t seq) {
  (void)rt;
  SleepTimer *st = (SleepTimer *)f->sleep_timer;
  if (!st) return;
  if (st->sleep_seq != seq) return;
  f->sleep_timer = NULL;
  uv_timer_stop(&st->timer);
  uv_close((uv_handle_t *)&st->timer, sleep_close_cb);
}

/* Shutdown handle-closer (fix S3): uv_close EVERY remaining handle so uv_run
 * drains the close callbacks and uv_loop_close sees none open.  A still-armed
 * SleepTimer is freed via sleep_close_cb; the async handle is embedded in Rt, so it
 * closes with no callback.  Reactor-thread only — no timer can fire concurrently
 * with the walk. */
static void reactor_close_walk_cb(uv_handle_t *h, void *arg) {
  (void)arg;
  if (uv_is_closing(h)) return;
  if (h->type == UV_TIMER) uv_close(h, sleep_close_cb); /* free the SleepTimer */
  else                     uv_close(h, NULL);           /* async: embedded in Rt */
}

/* The async callback: drain the MPSC request queue to empty (handles
 * uv_async_send coalescing — REVIEW.md B3) and, when asked, tear the loop down. */
static void reactor_async_cb(uv_async_t *h) {
  Rt *rt = (Rt *)h->data;
  for (;;) {
    pthread_mutex_lock(&rt->io_lock);
    IoReq *r = rt->io_head;
    if (r) { rt->io_head = r->next; if (!rt->io_head) rt->io_tail = NULL; }
    pthread_mutex_unlock(&rt->io_lock);
    if (!r) break;
    switch (r->op) {
      case IO_SLEEP:        start_sleep(rt, r->f, r->nanos, r->sleep_seq); break;
      case IO_CANCEL_SLEEP: cancel_sleep(rt, r->f, r->sleep_seq);          break;
    }
  }
  if (atomic_load_explicit(&rt->reactor_stop, memory_order_acquire)) {
    /* fix S3: close ALL remaining handles (the async + any still-armed sleep
     * timers) from the reactor thread, then let uv_run drain the close callbacks
     * and return on its own.  NO uv_stop — that stranded the timers' close cbs and
     * left them open, so uv_loop_close hit UV_EBUSY and the SleepTimers leaked.  The
     * old path uv_close'd only the async + uv_stop'd, abandoning armed timers. */
    uv_walk(&rt->loop, reactor_close_walk_cb, NULL);
  }
}

void krt2i_reactor_init(Rt *rt) {
  uv_loop_init(&rt->loop);
  uv_async_init(&rt->loop, &rt->async, reactor_async_cb);
  rt->async.data = rt;
}

static void *reactor_main(void *arg) {
  /* krt2i_spawn_thread handles collector registration around this entry. */
  krt2i_validate_gc_thread("reactor");
  Rt *rt = (Rt *)arg;
  uv_run(&rt->loop, UV_RUN_DEFAULT);
  uv_loop_close(&rt->loop);
  return NULL;
}

void krt2i_reactor_start(Rt *rt) {
  if (krt2i_spawn_thread(&rt->reactor_thr, reactor_main, rt) != 0)
    krt_fail("failed to start runtime reactor thread");
  rt->reactor_started = 1;
}

void krt2i_submit_sleep(Rt *rt, Fiber *f, uint64_t nanos) {
  krt2i_mark_fiber_shared(f);
  /* fix S2: mark the worker-visible mirror BEFORE enqueuing, so the abandonment
   * path (fiber_step) knows a timer may be live and routes a cancel.  The reactor
   * owns the actual SleepTimer* via f->sleep_timer. */
  uint64_t seq = atomic_fetch_add_explicit(&f->sleep_seq, 1, memory_order_acq_rel) + 1;
  atomic_store_explicit(&f->sleep_armed, 1, memory_order_release);
  atomic_store(&f->status, F_PARKED);     /* f stays GC-live via rt->all */
  IoReq *r = (IoReq *)GC_MALLOC(sizeof(IoReq)); /* scanned: keeps f reachable */
  r->op = IO_SLEEP; r->f = f; r->nanos = nanos; r->sleep_seq = seq; r->next = NULL;
  pthread_mutex_lock(&rt->io_lock);
  if (rt->io_tail) rt->io_tail->next = r; else rt->io_head = r;
  rt->io_tail = r;
  pthread_mutex_unlock(&rt->io_lock);
  uv_async_send(&rt->async);              /* unconditional (coalescing-safe) */
}

/* fix S2: route a cancel of f's active sleep timer to the reactor (handle ops are
 * reactor-confined).  Called when an interrupt abandons a sleep park.  Clears the
 * worker-visible mirror immediately; the reactor stops+closes the real timer. */
void krt2i_cancel_sleep(Rt *rt, Fiber *f) {
  if (!atomic_load_explicit(&f->sleep_armed, memory_order_acquire)) return;
  uint64_t seq = atomic_load_explicit(&f->sleep_seq, memory_order_acquire);
  atomic_fetch_add_explicit(&f->sleep_seq, 1, memory_order_acq_rel);
  atomic_store_explicit(&f->sleep_armed, 0, memory_order_release);
  IoReq *r = (IoReq *)GC_MALLOC(sizeof(IoReq)); /* scanned: keeps f reachable */
  r->op = IO_CANCEL_SLEEP; r->f = f; r->nanos = 0; r->sleep_seq = seq; r->next = NULL;
  pthread_mutex_lock(&rt->io_lock);
  if (rt->io_tail) rt->io_tail->next = r; else rt->io_head = r;
  rt->io_tail = r;
  pthread_mutex_unlock(&rt->io_lock);
  uv_async_send(&rt->async);
}

void krt2i_reactor_stop(Rt *rt) {
  if (!rt->reactor_started) return;
  atomic_store_explicit(&rt->reactor_stop, 1, memory_order_release);
  uv_async_send(&rt->async);
  if (pthread_join(rt->reactor_thr, NULL) != 0)
    krt2i_thread_fatal("failed to join runtime reactor thread");
}
