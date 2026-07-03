#include "internal.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void check(int cond, const char *msg) {
  if (!cond) {
    fprintf(stderr, "%s\n", msg);
    exit(1);
  }
}

static KValue *dummy_clo(KEnv *env, KValue *arg) {
  (void)env;
  return arg;
}

static KValue *dummy_io(KEnv *env) {
  (void)env;
  return kunit();
}

static KValue *g_thunk_result = NULL;
static KValue *dummy_thunk(KEnv *env) {
  (void)env;
  return g_thunk_result;
}

static KValue *dummy_native(KValue **args) {
  (void)args;
  return kunit();
}

static KValue *g_promise_payload = NULL;
static KValue *g_promise_exit = NULL;

static KValue *complete_with_payload(KEnv *env, KValue *promise) {
  (void)env;
  g_promise_exit = krt2_success(g_promise_payload);
  return krt2_complete_promise(promise, g_promise_exit);
}

static void init_test_rt(Rt *rt) {
  memset(rt, 0, sizeof *rt);
  pthread_mutex_init(&rt->rq_lock, NULL);
  pthread_cond_init(&rt->rq_cv, NULL);
  pthread_mutex_init(&rt->all_lock, NULL);
  atomic_store(&rt->shutting_down, 0);
  atomic_store(&rt->next_id, 0);
}

static void destroy_test_rt(Rt *rt) {
  pthread_mutex_destroy(&rt->all_lock);
  pthread_cond_destroy(&rt->rq_cv);
  pthread_mutex_destroy(&rt->rq_lock);
}

static void check_freeable_partition(void) {
  const char *names[1] = { "field" };
  KValue *vals[1] = { kstr0("rec") };
  KValue *native_args[1] = { kstr0("native") };

  check(kis_rc_freeable(kctor(KCT_USER_BASE, "Box", 1, vals)), "K_CTOR must be S3-freeable before sharing");
  check(kis_rc_freeable(krec(1, names, vals)), "K_REC must be S3-freeable before sharing");
  check(kis_rc_freeable(kinject(KCT_USER_BASE + 1, "Choice", vals[0])), "K_VARIANT must be S3-freeable before sharing");
  check(kis_rc_freeable(kstr0("str")), "K_STR must be S3-freeable before sharing");
  check(kis_rc_freeable(kbounce(kunit(), kunit())), "K_BOUNCE must be S3-freeable before sharing");
  check(kis_rc_freeable(kfail(vals[0])), "K_FAIL must be S3-freeable before sharing");

  check(!kis_rc_freeable(kclo(dummy_clo, NULL)), "K_CLO must stay Boehm-retained until env ownership is represented");
  check(!kis_rc_freeable(kio(dummy_io, NULL)), "K_IO must stay Boehm-retained until env ownership is represented");
  check(!kis_rc_freeable(kio_tail(kunit())), "K_IOTAIL must stay Boehm-retained in S3.1");
  check(!kis_rc_freeable(kio_effect(kunit())), "K_IOEFFECT must stay Boehm-retained in S3.1");
  check(!kis_rc_freeable(kio_finally(kunit(), NULL, 0)), "K_IOFINALLY must stay Boehm-retained in S3.1");
  check(!kis_rc_freeable(knative_sat(dummy_native, 1, native_args, 0)), "K_NATIVE must stay Boehm-retained in S3.1");
  check(!kis_rc_freeable(kbigint_str("123456789012345678901234567890")), "K_BIGINT must stay Boehm-retained");
  check(!kis_rc_freeable(kbyte(7)), "boxed K_BYTE must stay Boehm-retained");
  check(!kis_rc_freeable(kbytes((const unsigned char *)"abc", 3)), "K_BYTES must stay Boehm-retained");
}

static void check_kdrop_free_on_zero_and_shared_noop(void) {
  KValue *unique = kstr0("unique");
  check(krc_count(unique) == 1, "fresh unique value must start with rc count 1");
  unsigned long long before_unique = kgc_debug_free_count();
  kdrop(unique);
  check(kgc_debug_free_count() > before_unique, "S3.2 kdrop must free unique freeable values at zero");

  KValue *shared = kstr0("shared");
  krc_mark_shared_recursive(shared);
  unsigned before = krc_count(shared);
  kdup(shared);
  check(krc_count(shared) == before, "shared kdup must be a no-op until S4 atomic shared RC");
  kdrop(shared);
  check(krc_count(shared) == before, "shared kdrop must be a no-op until S4 atomic shared RC");
  check(krc_is_shared(shared), "shared kdrop must preserve the shared bit");
}

typedef struct {
  KValue *v;
  int rounds;
} RcRaceArgs;

static void *mark_shared_thread(void *arg) {
  RcRaceArgs *a = (RcRaceArgs *)arg;
  for (int i = 0; i < a->rounds; i++) krc_mark_shared_recursive(a->v);
  return NULL;
}

static void *dup_drop_thread(void *arg) {
  RcRaceArgs *a = (RcRaceArgs *)arg;
  for (int i = 0; i < a->rounds; i++) kdrop(kdup(a->v));
  return NULL;
}

static void check_shared_header_ops_are_atomic(void) {
  KValue *v = kstr0("shared-header-atomic");
  check(atomic_is_lock_free(&v->rc), "rc header must be an atomic lock-free word");

  RcRaceArgs args = { v, 20000 };
  pthread_t threads[6];
  for (int i = 0; i < 3; i++) pthread_create(&threads[i], NULL, mark_shared_thread, &args);
  for (int i = 3; i < 6; i++) pthread_create(&threads[i], NULL, dup_drop_thread, &args);
  for (int i = 0; i < 6; i++) pthread_join(threads[i], NULL);

  check(krc_is_shared(v), "concurrent shared marking must preserve the shared bit");
  unsigned before = krc_count(v);
  kdrop(kdup(v));
  check(krc_count(v) == before, "shared kdup/kdrop must remain no-op after concurrent marking");
}

static void check_public_kfree_reclaims_zero_root(void) {
  KValue *child = kstr0("child");
  KValue *args[1] = { child };
  KValue *parent = kctor(KCT_USER_BASE, "Parent", 1, args);
  krc_set_count(parent, 0);
  unsigned long long before = kgc_debug_free_count();
  kfree_recursive(parent);
  check(kgc_debug_free_count() > before, "S3.2 public kfree_recursive must reclaim zero-count freeable roots");
}

static void check_record_rest_counts_kept_fields(void) {
  const char *names[2] = { "drop", "keep" };
  KValue *drop = kstr0("record-drop-field");
  KValue *keep = kstr0("record-keep-field");
  KValue *vals[2] = { drop, keep };
  KValue *rec = krec(2, names, vals);
  const char *excluded[1] = { "drop" };
  check(krc_count(keep) == 1, "test record field starts with the record-owned reference");
  KValue *rest = krec_without(rec, 1, excluded);
  (void)rest;
  check(krc_count(keep) == 2, "record rest binder must count kept field aliases");
  check(krc_count(drop) == 1, "record rest binder must not count excluded fields");
}

static void check_interrupt_publication_marks_shared(void) {
  Fiber target;
  memset(&target, 0, sizeof target);
  pthread_mutex_init(&target.lock, NULL);
  atomic_store(&target.interrupt_pending, 0);
  target.blocking_armed = 1; /* avoid wake; this test only checks the side-channel store */

  KValue *by = kstr0("interrupt-by");
  KValue *cause = krt2i_interrupt_cause("External", krt2i_some(by));
  check(!kis_imm(cause), "interrupt test cause must be boxed so it can be shared-marked");
  check(!krc_is_shared(cause), "fresh interrupt cause should start thread-local");

  krt2i_interrupt_request(NULL, &target, cause);
  check(target.interrupt_cause == cause, "interrupt request must store the provided cause");
  check(krc_is_shared(cause), "interrupt cause publication must mark the cause shared");
  check(krc_is_shared(kctor_arg(cause, 1)), "interrupt cause publication must mark nested Option payload");
  check(krc_is_shared(by), "interrupt cause publication must mark nested boxed payloads");
  pthread_mutex_destroy(&target.lock);
}

static void check_atomic_publication_marks_shared(void) {
  KValue *init = kbigint_str("100000000000000000000000000000000000000001");
  KValue *aref = krt2_new_atomic_ref(init);
  check(krc_is_shared(init), "AtomicRef creation must mark the initial value shared");

  KValue *stored = kbigint_str("100000000000000000000000000000000000000003");
  krt2_atomic_store(kint(0), aref, stored);
  check(krc_is_shared(stored), "AtomicRef store must mark the stored value shared");

  KValue *exchanged = kbigint_str("100000000000000000000000000000000000000005");
  krt2_atomic_exchange(kint(0), aref, exchanged);
  check(krc_is_shared(exchanged), "AtomicRef exchange must mark the new value shared");

  KValue *desired = kbigint_str("100000000000000000000000000000000000000007");
  krt2_atomic_compare_exchange(kint(0), kint(0), aref, exchanged, desired);
  check(krc_is_shared(desired), "AtomicRef successful CAS must mark desired shared");

  KValue *rmwBase = kbigint_str("1267650600228229401496703205376"); /* 2^100, definitely boxed. */
  KValue *delta = kbigint_str("100000000000000000000000000000000000000011");
  krt2_atomic_store(kint(0), aref, rmwBase);
  krt2_atomic_fetch_add(kint(0), aref, delta);
  check(krc_is_shared(krt2_atomic_load(kint(0), aref)), "AtomicRef fetch_add result must be stored shared");

  KValue *sub = kbigint_str("100000000000000000000000000000000000000013");
  krt2_atomic_store(kint(0), aref, rmwBase);
  krt2_atomic_fetch_sub(kint(0), aref, sub);
  check(krc_is_shared(krt2_atomic_load(kint(0), aref)), "AtomicRef fetch_sub result must be stored shared");

  KValue *andv = kbigint_str("1267650600228229401496703205376");
  krt2_atomic_store(kint(0), aref, rmwBase);
  krt2_atomic_fetch_and(kint(0), aref, andv);
  check(krc_is_shared(krt2_atomic_load(kint(0), aref)), "AtomicRef fetch_and result must be stored shared");

  KValue *orv = kbigint_str("1");
  krt2_atomic_store(kint(0), aref, rmwBase);
  krt2_atomic_fetch_or(kint(0), aref, orv);
  check(krc_is_shared(krt2_atomic_load(kint(0), aref)), "AtomicRef fetch_or result must be stored shared");

  KValue *xorv = kbigint_str("1");
  krt2_atomic_store(kint(0), aref, rmwBase);
  krt2_atomic_fetch_xor(kint(0), aref, xorv);
  check(krc_is_shared(krt2_atomic_load(kint(0), aref)), "AtomicRef fetch_xor result must be stored shared");
}

static void check_stm_publication_marks_shared(void) {
  Fiber f;
  memset(&f, 0, sizeof f);

  KValue *init = kstr0("stm-init");
  check(krt2i_op_atomically(NULL, &f, krt2_new_tvar(init)), "newTVar transaction should commit");
  check(krc_is_shared(init), "STM newTVar must mark the initial value shared");
  KValue *tvar = kctor_arg(f.cur, 0); /* f.cur is krt2_pure(result). */

  KValue *written = kstr0("stm-written");
  check(krt2i_op_atomically(NULL, &f, krt2_write_tvar(tvar, written)), "writeTVar transaction should commit");
  check(krc_is_shared(written), "STM commit must mark written TVar values shared");
}

static void check_shared_mutation_marks_new_values(void) {
  KValue *ref = kref_new(kunit());
  krc_mark_shared_recursive(ref);
  KValue *rv = kstr0("shared-ref-value");
  kref_set(ref, rv);
  check(krc_is_shared(rv), "write into an already-shared Ref must mark the new value shared");

  KValue *arr = karr_new(1, kunit());
  krc_mark_shared_recursive(arr);
  KValue *av = kstr0("shared-array-value");
  karr_set(arr, 0, av);
  check(krc_is_shared(av), "write into an already-shared Array must mark the new value shared");

  KValue *th = kthunk(dummy_thunk, NULL, 1);
  krc_mark_shared_recursive(th);
  g_thunk_result = kstr0("shared-thunk-cache");
  kforce(th);
  check(th->as.thunk.cache && th->as.thunk.cache[0] == g_thunk_result, "memoized shared thunk must publish exactly one cache cell");
  check(krc_is_shared(g_thunk_result), "memoizing an already-shared thunk must mark the cached value shared");
}

static KValue *boxed_publication_payload(const char *label) {
  KValue *inner = kstr0(label);
  KValue *args[1] = { inner };
  return kctor(KCT_USER_BASE, "PublishBox", 1, args);
}

static void check_resume_publication_marks_current_action(void) {
  Rt rt;
  init_test_rt(&rt);
  Fiber f;
  memset(&f, 0, sizeof f);
  KValue *action = boxed_publication_payload("resume-current-action");
  f.cur = action;

  krt2i_resume(&rt, &f);
  check(krc_is_shared(action), "run-queue resume must mark the current fiber action shared");
  check(krc_is_shared(kctor_arg(action, 0)), "run-queue resume must mark nested current-action payloads shared");
  destroy_test_rt(&rt);
}

static void check_resume_publication_marks_fiber_graph(void) {
  Rt rt;
  init_test_rt(&rt);
  Fiber f;
  memset(&f, 0, sizeof f);

  KValue *action = boxed_publication_payload("resume-graph-current");
  KValue *contAction = boxed_publication_payload("resume-graph-cont");
  KValue *exitAction = boxed_publication_payload("resume-graph-exit");
  KValue *localValue = boxed_publication_payload("resume-graph-local");
  KValue *abortAction = boxed_publication_payload("resume-graph-abort");
  KValue *interruptCause = boxed_publication_payload("resume-graph-interrupt");
  KValue *terminalExit = boxed_publication_payload("resume-graph-terminal-exit");

  ExitStack exits;
  KValue *exitItems[1] = { exitAction };
  exits.items = exitItems;
  exits.n = 1;
  exits.cap = 1;

  FiberLocals locals;
  KValue *localItems[2] = { NULL, localValue };
  locals.vals = localItems;
  locals.n = 2;

  AbortExit abortExit;
  abortExit.action = abortAction;
  abortExit.active = 1;
  abortExit.next = NULL;

  Cont cont;
  cont.kind = KK_BIND;
  cont.a = contAction;
  cont.aux = NULL;
  cont.aux2 = NULL;
  cont.next = NULL;

  f.cur = action;
  f.k = &cont;
  f.cur_exits = &exits;
  f.locals = &locals;
  f.abort_exits = &abortExit;
  f.interrupt_cause = interruptCause;
  f.exit = terminalExit;

  krt2i_resume(&rt, &f);
  check(krc_is_shared(action), "resume must mark current action shared");
  check(krc_is_shared(contAction), "resume must mark continuation actions shared");
  check(krc_is_shared(exitAction), "resume must mark do-scope exit actions shared");
  check(krc_is_shared(localValue), "resume must mark FiberRef local snapshots shared");
  check(krc_is_shared(abortAction), "resume must mark abort-exit actions shared");
  check(krc_is_shared(interruptCause), "resume must mark pending interrupt causes shared");
  check(krc_is_shared(terminalExit), "resume must mark terminal exit side channel shared if present");
  destroy_test_rt(&rt);
}

static void check_wake_publication_marks_existing_current_action(void) {
  Rt rt;
  init_test_rt(&rt);
  Fiber f;
  memset(&f, 0, sizeof f);
  KValue *action = boxed_publication_payload("wake-existing-current-action");
  KValue *contAction = boxed_publication_payload("wake-existing-cont-action");
  Cont cont;
  cont.kind = KK_THEN;
  cont.a = contAction;
  cont.aux = NULL;
  cont.aux2 = NULL;
  cont.next = NULL;
  f.cur = action;
  f.k = &cont;
  atomic_store(&f.status, F_PARKED);
  atomic_store(&f.blocking_depth, 0);

  krt2i_wake(&rt, &f, NULL);
  check(krc_is_shared(action), "wake without resume value must mark the existing current action shared");
  check(krc_is_shared(kctor_arg(action, 0)), "wake without resume value must mark nested current-action payloads shared");
  check(krc_is_shared(contAction), "wake without resume value must mark the continuation stack shared");
  destroy_test_rt(&rt);
}

static void check_fiber_shared_marks_continuation_aux_variants(void) {
  Fiber f;
  memset(&f, 0, sizeof f);

  KValue *doscopeAction = boxed_publication_payload("aux-doscope-action");
  KValue *doscopeSaved = boxed_publication_payload("aux-doscope-saved");
  KValue *finseqAction = boxed_publication_payload("aux-finseq-action");
  KValue *finseqRval = boxed_publication_payload("aux-finseq-rval");
  KValue *finseqRlabel = boxed_publication_payload("aux-finseq-rlabel");
  KValue *finseqOrigin = boxed_publication_payload("aux-finseq-origin");
  KValue *handlerRet = boxed_publication_payload("aux-handler-ret");
  KValue *handlerOps = boxed_publication_payload("aux-handler-ops");
  KValue *handlerExit = boxed_publication_payload("aux-handler-exit");
  KValue *resHeadAction = boxed_publication_payload("aux-res-head");
  KValue *resExit = boxed_publication_payload("aux-res-exit");
  KValue *resLabel = boxed_publication_payload("aux-res-label");
  KValue *resHandlerRet = boxed_publication_payload("aux-res-handler-ret");
  KValue *resHandlerOps = boxed_publication_payload("aux-res-handler-ops");
  KValue *resHandlerExit = boxed_publication_payload("aux-res-handler-exit");
  KValue *abandKontAction = boxed_publication_payload("aux-aband-kont");
  KValue *abandExit = boxed_publication_payload("aux-aband-exit");
  KValue *abandRval = boxed_publication_payload("aux-aband-rval");
  KValue *abandRlabel = boxed_publication_payload("aux-aband-rlabel");

  KValue *doscopeItems[1] = { doscopeAction };
  ExitStack doscopeXs = { doscopeItems, 1, 1 };
  KValue *doscopeSavedItems[1] = { doscopeSaved };
  ExitStack doscopeSavedXs = { doscopeSavedItems, 1, 1 };

  KValue *finseqItems[1] = { finseqAction };
  ExitStack finseqXs = { finseqItems, 1, 1 };

  KValue *handlerExitItems[1] = { handlerExit };
  ExitStack handlerXs = { handlerExitItems, 1, 1 };
  Handler handler = { handlerRet, handlerOps, 1 };

  KValue *resExitItems[1] = { resExit };
  ExitStack resXs = { resExitItems, 1, 1 };
  KValue *resHandlerExitItems[1] = { resHandlerExit };
  ExitStack resHandlerXs = { resHandlerExitItems, 1, 1 };
  Handler resHandler = { resHandlerRet, resHandlerOps, 1 };
  Cont resHead = { KK_THEN, resHeadAction, NULL, NULL, NULL };
  Resumption res = { &resHead, NULL, &resXs, resLabel, &resHandler, &resHandlerXs, 0, 0 };

  KValue *abandExitItems[1] = { abandExit };
  ExitStack abandXs = { abandExitItems, 1, 1 };
  Cont abandKont = { KK_THEN, abandKontAction, NULL, NULL, NULL };
  AbandonEnd aband = { &abandKont, &abandXs, RK_RETURN, abandRval, abandRlabel, NULL };
  FinSeq finseq = { &finseqXs, 0, RK_RETURN, finseqRval, finseqRlabel, RK_NORMAL, finseqOrigin, &aband };

  Cont cAbandEnd = { KK_ABANDEND, NULL, &aband, NULL, NULL };
  Cont cAbandon = { KK_ABANDON, NULL, &res, NULL, &cAbandEnd };
  Cont cHandler = { KK_HANDLER, boxed_publication_payload("aux-handler-label"), &handler, &handlerXs, &cAbandon };
  Cont cFinseq = { KK_FINSEQ, NULL, &finseq, NULL, &cHandler };
  Cont cDoscope = { KK_DOSCOPE, boxed_publication_payload("aux-doscope-frame"), &doscopeXs, &doscopeSavedXs, &cFinseq };
  f.k = &cDoscope;
  f.drain_ae = &aband;

  krt2i_mark_fiber_shared(&f);

  check(krc_is_shared(doscopeAction), "KK_DOSCOPE aux ExitStack actions must be shared-marked");
  check(krc_is_shared(doscopeSaved), "KK_DOSCOPE saved ExitStack actions must be shared-marked");
  check(krc_is_shared(finseqAction), "KK_FINSEQ exit actions must be shared-marked");
  check(krc_is_shared(finseqRval), "KK_FINSEQ saved value must be shared-marked");
  check(krc_is_shared(finseqRlabel), "KK_FINSEQ saved label must be shared-marked");
  check(krc_is_shared(finseqOrigin), "KK_FINSEQ origin value must be shared-marked");
  check(krc_is_shared(handlerRet), "KK_HANDLER return clause must be shared-marked");
  check(krc_is_shared(handlerOps), "KK_HANDLER op record must be shared-marked");
  check(krc_is_shared(handlerExit), "KK_HANDLER saved exits must be shared-marked");
  check(krc_is_shared(resHeadAction), "KK_ABANDON resumption head must be shared-marked");
  check(krc_is_shared(resExit), "KK_ABANDON resumption exits must be shared-marked");
  check(krc_is_shared(resLabel), "KK_ABANDON resumption label must be shared-marked");
  check(krc_is_shared(resHandlerRet), "KK_ABANDON handler return clause must be shared-marked");
  check(krc_is_shared(resHandlerOps), "KK_ABANDON handler op record must be shared-marked");
  check(krc_is_shared(resHandlerExit), "KK_ABANDON handler exits must be shared-marked");
  check(krc_is_shared(abandKontAction), "KK_ABANDEND continuation must be shared-marked");
  check(krc_is_shared(abandExit), "KK_ABANDEND saved exits must be shared-marked");
  check(krc_is_shared(abandRval), "KK_ABANDEND saved value must be shared-marked");
  check(krc_is_shared(abandRlabel), "KK_ABANDEND saved label must be shared-marked");
}

static void check_foreign_resumption_marks_private_payload(void) {
  KValue *tailAction = boxed_publication_payload("fgn-res-tail");
  KValue *resExit = boxed_publication_payload("fgn-res-exit");
  KValue *resLabel = boxed_publication_payload("fgn-res-label");
  KValue *handlerRet = boxed_publication_payload("fgn-res-handler-ret");
  KValue *handlerOps = boxed_publication_payload("fgn-res-handler-ops");
  KValue *handlerExit = boxed_publication_payload("fgn-res-handler-exit");

  KValue *resExitItems[1] = { resExit };
  ExitStack resXs = { resExitItems, 1, 1 };
  KValue *handlerExitItems[1] = { handlerExit };
  ExitStack handlerXs = { handlerExitItems, 1, 1 };
  Handler handler = { handlerRet, handlerOps, 1 };
  Cont tail = { KK_THEN, tailAction, NULL, NULL, NULL };
  Resumption res = { NULL, &tail, &resXs, resLabel, &handler, &handlerXs, 0, 0 };

  KValue *token = kfgn(&res, KRT2_KIND_RESUMPTION);
  krc_mark_shared_recursive(token);

  check(krc_is_shared(token), "K_FGN resumption token must be shared-marked");
  check(krc_is_shared(tailAction), "K_FGN resumption tail continuation must be shared-marked");
  check(krc_is_shared(resExit), "K_FGN resumption exits must be shared-marked");
  check(krc_is_shared(resLabel), "K_FGN resumption label must be shared-marked");
  check(krc_is_shared(handlerRet), "K_FGN resumption handler return clause must be shared-marked");
  check(krc_is_shared(handlerOps), "K_FGN resumption handler ops must be shared-marked");
  check(krc_is_shared(handlerExit), "K_FGN resumption handler exits must be shared-marked");
}

static void check_scheduler_publication_paths_mark_shared(void) {
  krt2_new(1);

  KValue *fiberRefInit = boxed_publication_payload("fiberref-init");
  KValue *fiberRefExit = krt2_run_main(krt2_new_fiber_ref(fiberRefInit));
  check(krt2_exit_is_success(fiberRefExit), "newFiberRef publication test must complete");
  check(krc_is_shared(fiberRefInit), "newFiberRef must mark the shared init registry value");
  check(krc_is_shared(kctor_arg(fiberRefInit, 0)), "newFiberRef must mark nested init payloads");

  g_promise_payload = boxed_publication_payload("promise-complete-exit");
  KValue *promiseProgram = krt2_bind(krt2_new_promise(), kclo(complete_with_payload, NULL));
  KValue *promiseRunExit = krt2_run_main(promiseProgram);
  check(krt2_exit_is_success(promiseRunExit), "completePromise publication test must complete");
  check(g_promise_exit != NULL, "completePromise test must construct the promised Exit");
  check(krc_is_shared(g_promise_exit), "completePromise must mark the published Exit shared");
  check(krc_is_shared(g_promise_payload), "completePromise must mark nested Exit payloads shared");
  check(krc_is_shared(kctor_arg(g_promise_payload, 0)), "completePromise must mark deeper Exit payloads shared");

  KValue *blockingPayload = boxed_publication_payload("blocking-body-payload");
  KValue *blockingBody = krt2_pure(blockingPayload);
  KValue *blockingExit = krt2_run_main(krt2_blocking(blockingBody));
  check(krt2_exit_is_success(blockingExit), "rt-blocking publication test must complete");
  check(krc_is_shared(blockingBody), "rt-blocking submission must mark the handed-off body action shared");
  check(krc_is_shared(blockingPayload), "rt-blocking submission must mark nested body payloads shared");
  check(krc_is_shared(kctor_arg(blockingPayload, 0)), "rt-blocking submission must mark deeper body payloads shared");
}

int main(void) {
  krt_init();
  check_freeable_partition();
  check_kdrop_free_on_zero_and_shared_noop();
  check_shared_header_ops_are_atomic();
  check_public_kfree_reclaims_zero_root();
  check_record_rest_counts_kept_fields();
  check_interrupt_publication_marks_shared();
  check_atomic_publication_marks_shared();
  check_stm_publication_marks_shared();
  check_shared_mutation_marks_new_values();
  check_resume_publication_marks_current_action();
  check_resume_publication_marks_fiber_graph();
  check_wake_publication_marks_existing_current_action();
  check_fiber_shared_marks_continuation_aux_variants();
  check_foreign_resumption_marks_private_payload();
  check_scheduler_publication_paths_mark_shared();

  KValue *field = kstr0("payload");
  KValue *args[1] = { field };
  KValue *box = kctor(KCT_USER_BASE, "Box", 1, args);

  check(krc_count(box) == 1, "fresh boxed ctor must start with rc count 1");
  check(kis_rc_freeable(box), "boxed ctor must be in the S3 freeable partition before sharing");
  check(kis_rc_freeable(field), "String payload must be in the S3 freeable partition before sharing");

  KValue *arr = karr_new(3, box);
  check(krc_count(box) == 3, "karr_new must count each boxed slot alias of init");
  check(!kis_rc_freeable(arr), "mutable array cell must stay Boehm-retained");

  krc_mark_shared_recursive(arr);
  check(krc_is_shared(arr), "shared mark must mark the array shell");
  check(krc_is_shared(box), "shared mark must traverse boxed array elements");
  check(krc_is_shared(field), "shared mark must traverse constructor payloads");
  check(!kis_rc_freeable(box), "shared boxed ctor must be skipped by S3 free-on-zero");
  check(!kis_rc_freeable(field), "shared String must be skipped by S3 free-on-zero");

  unsigned before = krc_count(box);
  kdrop(box);
  check(krc_is_shared(box), "kdrop must preserve the shared bit");
  check(krc_count(box) == before, "shared kdrop must not mutate the rc count bits until S4");

  KValue *fg = kfgn(NULL, "test.handle");
  KValue *ref = kref_new(kunit());
  KValue *th = kthunk(NULL, NULL, 0);
  check(!kis_rc_freeable(fg), "foreign handles must never be RC-freed");
  check(!kis_rc_freeable(ref), "mutable refs must stay Boehm-retained");
  check(!kis_rc_freeable(th), "thunks must stay Boehm-retained");

  kfree_recursive(kunit());
  kfree_recursive(fg);
  kfree_recursive(ref);

  return 0;
}
