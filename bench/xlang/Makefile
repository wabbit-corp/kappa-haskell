# Cross-language benchmark harness.  `make xbench` runs the auto-discovering
# runner over every bench/xlang/<name>/ directory.  No registry to edit — drop a
# new benchmark dir and it is picked up.
#
#   make xbench                 # all discovered benchmarks
#   make xbench BENCH="sumloop" # only the named ones
#   make xbench REPS=11         # more timing repetitions
.PHONY: xbench
xbench:
	@REPS=$(REPS) bash run-xbench.sh $(BENCH)
