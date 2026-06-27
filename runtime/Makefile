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
#   make tsan       build with ThreadSanitizer (catch the parallel races early)
#   make clean

CC      ?= cc
AR      ?= ar
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
# -pthread (CFLAGS) + libuv's pkg-config -lpthread already cover threads.
LIBS      := $(UV_LIBS) -lgc -lgmp

# The runtime: the kappart boxed-value model + Boehm GC + primitives — split
# into six cohesive translation units (gc / value / bignum / show / unicode /
# prims; see boxed.h) — plus the kappart2 scheduler/reactor/
# structured-concurrency/race/STM translation units.
RT_SRC  := gc.c value.c bignum.c show.c \
           unicode.c prims.c \
           rt.c reactor.c scope.c race.c stm.c atomic.c
RT_OBJ  := $(RT_SRC:%.c=build/%.o)
RT_HDRS := kappart.h boxed.h kappart2.h internal.h kappa_ucd.h kappart2_harness.h

LIB := build/libkappart2.a

TEST_SRC := $(wildcard tests/*.c)
TEST_BIN := $(TEST_SRC:tests/%.c=build/%)

.PHONY: all test clean tsan bench
all: $(LIB) $(TEST_BIN)

$(LIB): $(RT_OBJ)
	$(AR) rcs $@ $^

build/%.o: %.c $(RT_HDRS) | build
	$(CC) $(CFLAGS) $(CPPFLAGS) -c $< -o $@

build/%: tests/%.c $(LIB) | build
	$(CC) $(CFLAGS) $(CPPFLAGS) $(LDFLAGS) $< $(LIB) $(LIBS) -o $@

build:
	mkdir -p build

test: all
	@set -e; for t in $(TEST_BIN); do echo "=== $$t ==="; $$t; done

# Microbenchmark: isolate the runtime cost sources (suspension, CPS node, value
# boxing) vs raw C and a Go goroutine baseline.  See bench/README.md.
bench: $(LIB) | build
	$(CC) $(CFLAGS) $(CPPFLAGS) $(LDFLAGS) bench/rt_bench.c $(LIB) $(LIBS) -o build/rt_bench
	@./build/rt_bench
	@command -v go >/dev/null 2>&1 && (cd bench && go run go_pingpong.go) || echo "(go not found — skipping the goroutine comparison)"

# ThreadSanitizer build — the scheduler/STM/reactor are concurrent; run the
# harnesses under tsan in CI to catch data races the design must avoid.
tsan: CFLAGS += -fsanitize=thread -DKRT2_TSAN
tsan: clean all
	@set -e; for t in $(TEST_BIN); do echo "=== tsan $$t ==="; $$t; done

clean:
	rm -rf build
