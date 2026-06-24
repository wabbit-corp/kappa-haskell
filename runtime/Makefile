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
# Boehm needs GC_THREADS for the multicore scheduler (parallel mark + thread regs).
CPPFLAGS  += -DGC_THREADS
# -pthread (CFLAGS) + libuv's pkg-config -lpthread already cover threads.
LIBS      := $(UV_LIBS) -lgc -lgmp

# The runtime: kappart.c (the boxed-value model + Boehm GC + primitives) plus
# the kappart2 scheduler/reactor/structured-concurrency/race/STM translation units.
RT_SRC  := kappart.c rt.c reactor.c scope.c race.c stm.c atomic.c
RT_OBJ  := $(RT_SRC:%.c=build/%.o)
RT_HDRS := kappart.h kappart2.h internal.h kappa_ucd.h kappart2_harness.h

LIB := build/libkappart2.a

TEST_SRC := $(wildcard tests/*.c)
TEST_BIN := $(TEST_SRC:tests/%.c=build/%)

.PHONY: all test clean tsan
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

# ThreadSanitizer build — the scheduler/STM/reactor are concurrent; run the
# harnesses under tsan in CI to catch data races the design must avoid.
tsan: CFLAGS += -fsanitize=thread -DKRT2_TSAN
tsan: clean all
	@set -e; for t in $(TEST_BIN); do echo "=== tsan $$t ==="; $$t; done

clean:
	rm -rf build
