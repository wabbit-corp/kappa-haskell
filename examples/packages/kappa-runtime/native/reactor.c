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
typedef struct { uv_timer_t timer; Fiber *f; Rt *rt; } SleepTimer;

static void sleep_close_cb(uv_handle_t *h) { free(h); }

static void sleep_timer_cb(uv_timer_t *t) {
  SleepTimer *st = (SleepTimer *)t->data;            /* sleepFor returns Unit */
  krt2i_wake(st->rt, st->f, krt2_pure(krt2i_unit())); /* idempotent: an interrupt
                                                       * may have woken it first */
  uv_close((uv_handle_t *)t, sleep_close_cb);
}

/* Runs on the reactor thread (from the async drain). */
static void start_sleep(Rt *rt, Fiber *f, uint64_t nanos) {
  SleepTimer *st = (SleepTimer *)malloc(sizeof(SleepTimer));
  st->f = f; st->rt = rt;
  uv_timer_init(&rt->loop, &st->timer);
  st->timer.data = st;
  uint64_t ms = (nanos == 0) ? 0 : (nanos + 999999u) / 1000000u; /* round up */
  uv_timer_start(&st->timer, sleep_timer_cb, ms, 0);
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
      case IO_SLEEP: start_sleep(rt, r->f, r->nanos); break;
    }
  }
  if (atomic_load_explicit(&rt->reactor_stop, memory_order_acquire)) {
    /* Close our own async handle and stop the loop FROM the reactor thread.
     * v1 spine: any still-pending sleep timers are abandoned (structured root-
     * scope shutdown of leftover children is the scopes increment). */
    uv_close((uv_handle_t *)&rt->async, NULL);
    uv_stop(&rt->loop);
  }
}

void krt2i_reactor_init(Rt *rt) {
  uv_loop_init(&rt->loop);
  uv_async_init(&rt->loop, &rt->async, reactor_async_cb);
  rt->async.data = rt;
}

static void *reactor_main(void *arg) {
  /* Created via GC_pthread_create — already collector-registered (see the note
   * in rt.c:worker_main). */
  Rt *rt = (Rt *)arg;
  uv_run(&rt->loop, UV_RUN_DEFAULT);
  uv_loop_close(&rt->loop);
  return NULL;
}

void krt2i_reactor_start(Rt *rt) {
  GC_pthread_create(&rt->reactor_thr, NULL, reactor_main, rt);
  rt->reactor_started = 1;
}

void krt2i_submit_sleep(Rt *rt, Fiber *f, uint64_t nanos) {
  atomic_store(&f->status, F_PARKED);     /* f stays GC-live via rt->all */
  IoReq *r = (IoReq *)GC_MALLOC(sizeof(IoReq)); /* scanned: keeps f reachable */
  r->op = IO_SLEEP; r->f = f; r->nanos = nanos; r->next = NULL;
  pthread_mutex_lock(&rt->io_lock);
  if (rt->io_tail) rt->io_tail->next = r; else rt->io_head = r;
  rt->io_tail = r;
  pthread_mutex_unlock(&rt->io_lock);
  uv_async_send(&rt->async);              /* unconditional (coalescing-safe) */
}

void krt2i_reactor_stop(Rt *rt) {
  if (!rt->reactor_started) return;
  atomic_store_explicit(&rt->reactor_stop, 1, memory_order_release);
  uv_async_send(&rt->async);
  GC_pthread_join(rt->reactor_thr, NULL);
}
