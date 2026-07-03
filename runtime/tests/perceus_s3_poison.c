#include "internal.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

static int fails = 0;

#define CHECK(cond, msg) do { if (!(cond)) { fprintf(stderr, "  FAIL: %s\n", msg); fails++; } } while (0)

extern KValue *kpf___hashMixString(KValue **a);

static void trigger_stale_ctor_access_api(void) {
  krt_init();
  krc_poison_set_enabled(1);

  KValue *payload = kstr0("stale-payload");
  KValue *args[1] = { payload };
  KValue *box = kctor(KCT_USER_BASE, "PoisonBox", 1, args);
  KValue *stale = box;

  kdrop(box);
  (void)kctor_tagid(stale);
  _exit(0);
}

static void trigger_stale_ctor_access_env(void) {
  krt_init();

  KValue *payload = kstr0("stale-env-payload");
  KValue *args[1] = { payload };
  KValue *box = kctor(KCT_USER_BASE, "PoisonEnvBox", 1, args);
  KValue *stale = box;

  kdrop(box);
  (void)kctor_tagid(stale);
  _exit(0);
}

static void trigger_stale_hash_mix_string(void) {
  krt_init();
  krc_poison_set_enabled(1);

  KValue *stale = kstr0("hash-me");
  kdrop(stale);

  KValue *args[2] = { kint(0), stale };
  (void)kpf___hashMixString(args);
  _exit(0);
}

static void trigger_stale_lt_string(void) {
  krt_init();
  krc_poison_set_enabled(1);

  KValue *stale = kstr0("alpha");
  kdrop(stale);

  (void)kp_ltStr(stale, kstr0("omega"));
  _exit(0);
}

static KValue *make_stale_perform(KEnv *env, KValue *ignored) {
  (void)env; (void)ignored;
  KValue *label = kstr0("PoisonEffect");
  KValue *op = kstr0("stale-op");
  /* krt2_perform correctly owns its op child; this deliberately injects a stale
   * child to prove the scheduler's raw K_STR reader is covered by the poison oracle. */
  KValue *action = krt2_perform(label, op, kunit());
  krc_set_count(op, 1);
  kdrop(op);
  return action;
}

static void trigger_stale_effect_op_read(void) {
  krt_init();
  krc_poison_set_enabled(1);

  KValue *exit = krt2_run_main(krt2_bind(krt2_pure(kunit()), kclo(make_stale_perform, NULL)));
  _exit(krt2_exit_is_success(exit) ? 0 : 2);
}

static KValue *make_modified_value(KEnv *env, KValue *old) {
  (void)env; (void)old;
  return kstr0("s33-modified");
}

static KValue *after_modify_overwrite(KEnv *env, KValue *result) {
  KValue *ref = kvar(env, 0);
  return krt2_then(krt2_set_fiber_ref(ref, kstr0("s33-after-modify")),
                   krt2_pure(result));
}

static KValue *run_modify_then_overwrite(KEnv *env, KValue *ref) {
  (void)env;
  return krt2_bind(krt2_modify_fiber_ref(ref, kclo(make_modified_value, NULL)),
                   kclo(after_modify_overwrite, kpush(ref, NULL)));
}

static KValue *identity_modified_value(KEnv *env, KValue *old) {
  (void)env;
  return old;
}

static KValue *after_identity_modify_overwrite(KEnv *env, KValue *result) {
  KValue *ref = kvar(env, 0);
  return krt2_then(krt2_set_fiber_ref(ref, kstr0("s33-identity-after-modify")),
                   krt2_pure(result));
}

static KValue *run_identity_modify_then_overwrite(KEnv *env, KValue *ref) {
  (void)env;
  return krt2_then(krt2_set_fiber_ref(ref, kstr0("s33-identity-old")),
         krt2_bind(krt2_modify_fiber_ref(ref, kclo(identity_modified_value, NULL)),
                   kclo(after_identity_modify_overwrite, kpush(ref, NULL))));
}

static void trigger_modify_fiber_ref_result_survives_overwrite(void) {
  krt_init();
  krc_poison_set_enabled(1);

  KValue *exit = krt2_run_main(krt2_bind(krt2_new_fiber_ref(kstr0("s33-mod-init")),
                                         kclo(run_modify_then_overwrite, NULL)));
  if (!krt2_exit_is_success(exit)) _exit(2);
  KValue *result = kctor_arg(exit, 0);
  const char *s = kas_str(result);
  _exit(strcmp(s, "s33-modified") == 0 ? 0 : 3);
}

static void trigger_identity_modify_fiber_ref_result_survives_overwrite(void) {
  krt_init();
  krc_poison_set_enabled(1);

  KValue *exit = krt2_run_main(krt2_bind(krt2_new_fiber_ref(kstr0("s33-identity-init")),
                                         kclo(run_identity_modify_then_overwrite, NULL)));
  if (!krt2_exit_is_success(exit)) _exit(2);
  KValue *result = kctor_arg(exit, 0);
  const char *s = kas_str(result);
  _exit(strcmp(s, "s33-identity-old") == 0 ? 0 : 3);
}

static KValue *run_locally_restore_override(KEnv *env, KValue *ref) {
  (void)env;
  return krt2_then(krt2_set_fiber_ref(ref, kstr0("s33-local-old")),
         krt2_then(krt2_locally_fiber_ref(ref, kstr0("s33-local-temp"), krt2_pure(kunit())),
                   krt2_get_fiber_ref(ref)));
}

static void trigger_locally_fiber_ref_restores_live_override(void) {
  krt_init();
  krc_poison_set_enabled(1);

  KValue *exit = krt2_run_main(krt2_bind(krt2_new_fiber_ref(kstr0("s33-local-init")),
                                         kclo(run_locally_restore_override, NULL)));
  if (!krt2_exit_is_success(exit)) _exit(2);
  KValue *result = kctor_arg(exit, 0);
  const char *s = kas_str(result);
  _exit(strcmp(s, "s33-local-old") == 0 ? 0 : 3);
}

static KValue *restore_local_temp(KEnv *env, KValue *ref) {
  (void)env;
  return krt2_then(krt2_set_fiber_ref(ref, kstr0("s33-local-result-temp")),
         krt2_locally_fiber_ref(ref, kstr0("s33-local-result-temp"),
                                krt2_get_fiber_ref(ref)));
}

static void trigger_locally_fiber_ref_result_survives_restore(void) {
  krt_init();
  krc_poison_set_enabled(1);

  KValue *exit = krt2_run_main(krt2_bind(krt2_new_fiber_ref(kstr0("s33-local-result-init")),
                                         kclo(restore_local_temp, NULL)));
  if (!krt2_exit_is_success(exit)) _exit(2);
  KValue *result = kctor_arg(exit, 0);
  const char *s = kas_str(result);
  _exit(strcmp(s, "s33-local-result-temp") == 0 ? 0 : 3);
}

static KValue *overwrite_ref_finalizer(KEnv *env, KValue *ignored) {
  (void)ignored;
  KValue *ref = kvar(env, 0);
  return krt2_write_ref(ref, kstr0("s33-finalizer-new"));
}

static KValue *read_ref_with_overwriting_finalizer(KEnv *env, KValue *ref) {
  (void)env;
  return krt2_finally(krt2_read_ref(ref), kclo(overwrite_ref_finalizer, kpush(ref, NULL)));
}

static void trigger_finally_result_survives_ref_overwrite(void) {
  krt_init();
  krc_poison_set_enabled(1);

  KValue *exit = krt2_run_main(krt2_bind(krt2_new_ref(kstr0("s33-finalizer-old")),
                                         kclo(read_ref_with_overwriting_finalizer, NULL)));
  if (!krt2_exit_is_success(exit)) _exit(2);
  KValue *result = kctor_arg(exit, 0);
  const char *s = kas_str(result);
  _exit(strcmp(s, "s33-finalizer-old") == 0 ? 0 : 3);
}

static void trigger_sync_finally_result_survives_ref_overwrite(void) {
  krt_init();
  krc_poison_set_enabled(1);

  KValue *ref = kref_new(kstr0("s33-sync-finalizer-old"));
  KValue *result = krt2_run_op_sync(
      krt2_finally(krt2_read_ref(ref),
                   kclo(overwrite_ref_finalizer, kpush(ref, NULL))));
  const char *s = kas_str(result);
  _exit(strcmp(s, "s33-sync-finalizer-old") == 0 ? 0 : 3);
}

static KValue *sync_read_then_overwrite_cont(KEnv *env, KValue *result) {
  KValue *ref = kvar(env, 0);
  return krt2_then(krt2_write_ref(ref, kstr0("s33-sync-bind-new")),
                   krt2_pure(result));
}

static void trigger_sync_bind_read_result_survives_ref_overwrite(void) {
  krt_init();
  krc_poison_set_enabled(1);

  KValue *ref = kref_new(kstr0("s33-sync-bind-old"));
  KValue *result = krt2_run_op_sync(
      krt2_bind(krt2_read_ref(ref),
                kclo(sync_read_then_overwrite_cont, kpush(ref, NULL))));
  const char *s = kas_str(result);
  _exit(strcmp(s, "s33-sync-bind-old") == 0 ? 0 : 3);
}

static void expect_poison_trap(const char *label, int env_poison, void (*fn)(void)) {
  int pipefd[2];
  CHECK(pipe(pipefd) == 0, "pipe created");
  if (env_poison) CHECK(setenv("KAPPA_POISON", "1", 1) == 0, "KAPPA_POISON set");
  else unsetenv("KAPPA_POISON");
  pid_t pid = fork();
  CHECK(pid >= 0, "fork succeeded");
  if (pid == 0) {
    close(pipefd[0]);
    dup2(pipefd[1], STDERR_FILENO);
    close(pipefd[1]);
    fn();
    _exit(0);
  }

  close(pipefd[1]);
  char buf[4096];
  ssize_t n = read(pipefd[0], buf, sizeof(buf) - 1);
  close(pipefd[0]);
  if (n < 0) n = 0;
  buf[n] = '\0';

  int status = 0;
  CHECK(waitpid(pid, &status, 0) == pid, "child reaped");
  CHECK(!WIFEXITED(status) || WEXITSTATUS(status) != 0,
        "poisoned stale access failed instead of succeeding");
  if (strstr(buf, "use after RC free") == NULL) {
    fprintf(stderr, "  FAIL: %s did not name the RC UAF contract; stderr=%s\n", label, buf);
    fails++;
  }
  unsetenv("KAPPA_POISON");
}

static void expect_no_poison_trap(const char *label, void (*fn)(void)) {
  int pipefd[2];
  CHECK(pipe(pipefd) == 0, "pipe created");
  unsetenv("KAPPA_POISON");
  pid_t pid = fork();
  CHECK(pid >= 0, "fork succeeded");
  if (pid == 0) {
    close(pipefd[0]);
    dup2(pipefd[1], STDERR_FILENO);
    close(pipefd[1]);
    fn();
    _exit(0);
  }

  close(pipefd[1]);
  char buf[4096];
  ssize_t n = read(pipefd[0], buf, sizeof(buf) - 1);
  close(pipefd[0]);
  if (n < 0) n = 0;
  buf[n] = '\0';

  int status = 0;
  CHECK(waitpid(pid, &status, 0) == pid, "child reaped");
  if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
    fprintf(stderr, "  FAIL: %s triggered poison or failed; status=%d stderr=%s\n", label, status, buf);
    fails++;
  }
}

int main(void) {
  expect_poison_trap("direct poison API", 0, trigger_stale_ctor_access_api);
  expect_poison_trap("KAPPA_POISON env trigger", 1, trigger_stale_ctor_access_env);
  expect_poison_trap("prims.c raw string reader", 0, trigger_stale_hash_mix_string);
  expect_poison_trap("show.c raw string reader", 0, trigger_stale_lt_string);
  expect_poison_trap("effect scheduler raw op reader", 0, trigger_stale_effect_op_read);
  expect_no_poison_trap("modifyFiberRef result survives later overwrite",
                        trigger_modify_fiber_ref_result_survives_overwrite);
  expect_no_poison_trap("identity modifyFiberRef result survives later overwrite",
                        trigger_identity_modify_fiber_ref_result_survives_overwrite);
  expect_no_poison_trap("locallyFiberRef restores a live prior override",
                        trigger_locally_fiber_ref_restores_live_override);
  expect_no_poison_trap("locallyFiberRef body result survives restore finalizer",
                        trigger_locally_fiber_ref_result_survives_restore);
  expect_no_poison_trap("finally result survives ref-overwrite finalizer",
                        trigger_finally_result_survives_ref_overwrite);
  expect_no_poison_trap("sync finally result survives ref-overwrite finalizer",
                        trigger_sync_finally_result_survives_ref_overwrite);
  expect_no_poison_trap("sync bind read result survives ref overwrite",
                        trigger_sync_bind_read_result_survives_ref_overwrite);
  if (fails) {
    fprintf(stderr, "FAIL: perceus_s3_poison (%d)\n", fails);
    return 1;
  }
  fprintf(stderr, "OK: perceus_s3_poison\n");
  return 0;
}
