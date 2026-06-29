/* fgn_kind.c — runtime-owned K_FGN handles must fail closed on kind mismatch. */
#include "kappart2.h"
#include "kappart2_harness.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

static int fails = 0;
#define CHECK(c, m) do { if (!(c)) { fprintf(stderr, "  FAIL: %s\n", m); fails++; } } while (0)

static KValue *await_promise_as_fiber(KEnv *e, KValue *promise) {
  (void)e;
  return krt2_await(promise);
}

static KValue *bad_program(void) {
  return krt2_bind(krt2_new_promise(), kclo(await_promise_as_fiber, NULL));
}

static void run_bad_program(void) {
  krt2_new(1);
  (void)krt2_run_main(bad_program());
}

static void expect_wrong_kind_trap(void (*fn)(void), const char *expected_kind) {
  int pipefd[2];
  CHECK(pipe(pipefd) == 0, "pipe created");
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
        "wrong-kind program failed instead of succeeding");
  CHECK(strstr(buf, "wrong foreign handle kind") != NULL,
        "wrong-kind failure names the handle-kind contract");
  CHECK(strstr(buf, expected_kind) != NULL,
        "wrong-kind failure names the expected kind");
}

int main(void) {
  expect_wrong_kind_trap(run_bad_program, KRT2_KIND_FIBER);
  if (fails) {
    fprintf(stderr, "FAIL: fgn_kind (%d)\n", fails);
    return 1;
  }
  fprintf(stderr, "OK: fgn_kind\n");
  return 0;
}
