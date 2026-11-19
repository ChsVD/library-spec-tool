CC = cc
AR = ar
# Fixed all-optimization solver; profiling instrumentation is excluded.
SAN ?= 0
CONFIG = all-optimized-san$(SAN)
BUILD = build/$(CONFIG)
CPPFLAGS = -Iinclude -Isrc -Ivendor
CFLAGS = -std=c11 -O2 -g
ifeq ($(SAN),1)
CFLAGS = -std=c11 -O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer -fno-pie -no-pie
endif
WARN = -Wall -Wextra -Werror -Wpedantic
BACKEND = $(wildcard vendor/gmp/minigmp/*.c)
OBJECTS = $(BUILD)/solver.o $(BUILD)/backend_alloc.o $(patsubst vendor/gmp/minigmp/%.c,$(BUILD)/vendor/%.o,$(BACKEND))
all: $(BUILD)/libsx.a
$(BUILD)/%.o: src/%.c
	@mkdir -p $(@D)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(WARN) -MMD -MP -c $< -o $@
$(BUILD)/vendor/%.o: vendor/gmp/minigmp/%.c vendor/gmp/minigmp/gmp_def.h
	@mkdir -p $(@D)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@
$(BUILD)/libsx.a: $(OBJECTS)
	$(AR) rcs $@ $^
$(BUILD)/driver: tests/driver.c $(BUILD)/libsx.a
	$(CC) $(CPPFLAGS) $(CFLAGS) $(WARN) $< $(BUILD)/libsx.a -o $@
$(BUILD)/pivot: tests/pivot.c src/solver.c src/backend.h include/sx_solver.h $(BUILD)/libsx.a
	$(CC) $(CPPFLAGS) $(CFLAGS) $(WARN) $< $(BUILD)/libsx.a -o $@
$(BUILD)/normalize: tests/normalize.c src/solver.c src/backend.h include/sx_solver.h $(BUILD)/libsx.a
	$(CC) $(CPPFLAGS) $(CFLAGS) $(WARN) $< $(BUILD)/libsx.a -o $@
$(BUILD)/bench_driver: tests/bench_driver.c $(BUILD)/libsx.a
	$(CC) $(CPPFLAGS) $(CFLAGS) $(WARN) $< $(BUILD)/libsx.a -o $@
test: $(BUILD)/driver $(BUILD)/pivot $(BUILD)/normalize
	python3 tests/check.py ./$(BUILD)/driver
	./$(BUILD)/pivot
	./$(BUILD)/normalize
bench: $(BUILD)/bench_driver
sanitize:
	$(MAKE) SAN=1 test
normal:
	$(MAKE) SAN=0 test
clean:
	rm -rf $(BUILD)
-include $(OBJECTS:.o=.d)
.PHONY: all clean test bench sanitize normal
