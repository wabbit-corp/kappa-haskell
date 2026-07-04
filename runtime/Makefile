# Standalone build of the Kappa runtime (`kappart2`) + its C test harnesses.
#
# This does NOT need the Kappa compiler: the harnesses construct KValue IO
# actions directly (via the kappart constructors + the krt2_* builders) and run
# them on the real scheduler, so the runtime is testable in isolation
# (docs/DESIGN.md §17).  The Kappa backend (Kappa.Backend.Driver) links the same
# sources for a real program.
#
#   make            build build/libkappart2.a and the test harnesses
#   make test       build + run the harnesses
#   make tsan-supported
#                   probe the same compiler/flag/link setup used by TSan lanes
#   make tsan       build all harnesses with ThreadSanitizer
#   make tsan-rc    build the S4 shared-RC concurrency corpus with ThreadSanitizer
#   make poison-rc  run the S4 shared-RC concurrency corpus under KAPPA_POISON=1
#   make bench-s4-rc run the S4 biased-RC fast/slow-path performance gate
#   make clean

CC      ?= cc
AR      ?= ar
BUILD   ?= build
# -fno-strict-aliasing: the KValue union is type-punned, like kappart itself.
CFLAGS  ?= -std=c11 -O2 -g -Wall -Wextra -fno-strict-aliasing -pthread
# -flto: recover cross-TU inlining of the hot boxed-value ops now that kappart.c
# is split into smaller translation units (so the split costs nothing at runtime).
# Validated safe against the conservative Boehm collector by the GC-stress
# harnesses (run_main_persist / abandon_drain / fiberref_promise / stm).
CFLAGS  += -flto
LDFLAGS += -flto
# All sources + headers live flat in this directory.
CPPFLAGS += -I .

# Homebrew prefix (Apple Silicon /opt/homebrew, Intel /usr/local) for gc/gmp/uv.
# Override BREW=... on non-homebrew systems; on Linux the system paths are used.
BREW ?= $(shell brew --prefix 2>/dev/null)
ifneq ($(BREW),)
  CPPFLAGS += -I$(BREW)/include
  LDFLAGS  += -L$(BREW)/lib
  export PKG_CONFIG_PATH := $(BREW)/lib/pkgconfig:$(PKG_CONFIG_PATH)
endif

# libuv via pkg-config (the reactor + blocking lane); Boehm GC; GMP (bignum).
UV_CFLAGS := $(shell pkg-config --cflags libuv 2>/dev/null)
UV_LIBS   := $(shell pkg-config --libs   libuv 2>/dev/null || echo -luv)
CPPFLAGS  += $(UV_CFLAGS)
# libuv's Unix headers need glibc feature macros when compiled under -std=c11
# (notably pthread_rwlock_t from <pthread.h>).
CPPFLAGS  += -D_GNU_SOURCE
# Boehm needs GC_THREADS for the multicore scheduler (parallel mark + thread regs).
CPPFLAGS  += -DGC_THREADS
# §32.2.20 test-only: compile in the abandonment-drain branch hit-counters so
# tests/abandon_foreign_chain.c can PROVE it exercises the FOREIGN-terminal path.
# Pure instrumentation (a few unconditional increments); harmless in this
# standalone test build.  Not defined by the production C/LLVM backend builds.
CPPFLAGS  += -DKRT2_ABANDON_INSTRUMENT
# -pthread (CFLAGS) + libuv's pkg-config -lpthread already cover threads.
LIBS      := $(UV_LIBS) -lgc -lgmp

# The runtime: the kappart boxed-value model + Boehm GC + primitives — split
# into six cohesive translation units (gc / value / bignum / show / unicode /
# prims; see boxed.h) — plus the kappart2 scheduler/reactor/
# structured-concurrency/race/STM translation units.
RT_SRC  := gc.c value.c bignum.c show.c \
           unicode.c prims.c \
           rt.c reactor.c scope.c race.c stm.c atomic.c
RT_OBJ  := $(RT_SRC:%.c=$(BUILD)/%.o)
RT_HDRS := kappart.h boxed.h kappart2.h internal.h kappa_ucd.h kappart2_harness.h

LIB := $(BUILD)/libkappart2.a

TEST_SRC := $(wildcard tests/*.c)
TEST_BIN := $(TEST_SRC:tests/%.c=$(BUILD)/%)
TSAN_TEST_BIN := $(filter-out $(BUILD)/atomic_lostproof,$(TEST_BIN))
S4_RC_CORPUS := $(BUILD)/atomic $(BUILD)/fiberref_promise $(BUILD)/parallel $(BUILD)/race \
                $(BUILD)/stm $(BUILD)/stm_retry $(BUILD)/stm_orelse \
                $(BUILD)/blocking_lane $(BUILD)/perceus_s3_prereq $(BUILD)/perceus_s4_shared

.PHONY: all test clean tsan-supported tsan _tsan tsan-rc _tsan-rc poison-rc _poison-rc bench bench-s4-rc _bench-s4-rc
all: $(LIB) $(TEST_BIN)

$(LIB): $(RT_OBJ)
	$(AR) rcs $@ $^

$(BUILD)/%.o: %.c $(RT_HDRS) | $(BUILD)
	$(CC) $(CFLAGS) $(CPPFLAGS) -c $< -o $@

$(BUILD)/%: tests/%.c $(LIB) | $(BUILD)
	$(CC) $(CFLAGS) $(CPPFLAGS) $(LDFLAGS) $< $(LIB) $(LIBS) -o $@

$(BUILD):
	mkdir -p $(BUILD)

test: all
	@set -e; for t in $(TEST_BIN); do echo "=== $$t ==="; $$t; done

# Microbenchmark: isolate the runtime cost sources (suspension, CPS node, value
# boxing) vs raw C and a Go goroutine baseline.  See bench/README.md.
bench: $(LIB) | $(BUILD)
	$(CC) $(CFLAGS) $(CPPFLAGS) $(LDFLAGS) bench/rt_bench.c $(LIB) $(LIBS) -o $(BUILD)/rt_bench
	@./$(BUILD)/rt_bench
	@command -v go >/dev/null 2>&1 && (cd bench && go run go_pingpong.go) || echo "(go not found — skipping the goroutine comparison)"

$(BUILD)/rc_biased_bench: bench/rc_biased.c $(LIB) | $(BUILD)
	$(CC) $(CFLAGS) $(CPPFLAGS) $(LDFLAGS) $< $(LIB) $(LIBS) -o $@

bench-s4-rc:
	@$(MAKE) BUILD=build-bench-s4-rc CFLAGS='$(CFLAGS) -DNDEBUG -O3' _bench-s4-rc

_bench-s4-rc: $(BUILD)/rc_biased_bench
	@./$(BUILD)/rc_biased_bench

# ThreadSanitizer build — the scheduler/STM/reactor are concurrent; run the
# harnesses under tsan in CI to catch data races the design must avoid. The
# atomic_lostproof is a scheduler-level diagnostic for the old plain-Ref
# read/write RMW lowering: under S4 the individual Ref operations are
# ownership-synchronized, but the two-operation sequence is still logically
# non-atomic and is intentionally not part of the TSan corpus.
tsan-supported:
	@tmp="$${TMPDIR:-/tmp}/kappa-runtime-tsan-probe-$$$$"; \
	  mkdir -p "$$tmp"; \
	  printf 'int main(void) { return 0; }\n' > "$$tmp/probe.c"; \
	  $(CC) $(CFLAGS) -fsanitize=thread -DKRT2_TSAN $(CPPFLAGS) $(LDFLAGS) "$$tmp/probe.c" $(LIBS) -o "$$tmp/probe" >/dev/null 2>&1; \
	  rc=$$?; rm -rf "$$tmp"; exit $$rc

tsan:
	@$(MAKE) BUILD=build-tsan CFLAGS='$(CFLAGS) -fsanitize=thread -DKRT2_TSAN' _tsan

_tsan: all
	@rc=0; for t in $(TSAN_TEST_BIN); do echo "=== tsan $$t ==="; $$t || { rc=$$?; break; }; done; \
	  exit $$rc

tsan-rc:
	@$(MAKE) BUILD=build-tsan-rc CFLAGS='$(CFLAGS) -fsanitize=thread -DKRT2_TSAN' _tsan-rc

_tsan-rc: $(S4_RC_CORPUS)
	@rc=0; for t in $(S4_RC_CORPUS); do echo "=== tsan-rc $$t ==="; $$t || { rc=$$?; break; }; done; \
	  exit $$rc

poison-rc:
	@$(MAKE) BUILD=build-poison-rc _poison-rc

_poison-rc: $(S4_RC_CORPUS)
	@rc=0; for t in $(S4_RC_CORPUS); do echo "=== poison-rc $$t ==="; \
	  KAPPA_POISON=1 KAPPA_RT_WORKERS=8 $$t || { rc=$$?; break; }; done; \
	  exit $$rc

clean:
	rm -rf build build-tsan build-tsan-rc build-poison-rc build-bench-s4-rc
