#include "kappart.h"

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

int main(void) {
  expect_poison_trap("direct poison API", 0, trigger_stale_ctor_access_api);
  expect_poison_trap("KAPPA_POISON env trigger", 1, trigger_stale_ctor_access_env);
  expect_poison_trap("prims.c raw string reader", 0, trigger_stale_hash_mix_string);
  expect_poison_trap("show.c raw string reader", 0, trigger_stale_lt_string);
  if (fails) {
    fprintf(stderr, "FAIL: perceus_s3_poison (%d)\n", fails);
    return 1;
  }
  fprintf(stderr, "OK: perceus_s3_poison\n");
  return 0;
}
