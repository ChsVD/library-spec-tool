CC = cc
AR = ar
CPPFLAGS = -Iinclude -Isrc -Ivendor
CFLAGS = -std=c11 -O2 -g
WARN = -Wall -Wextra -Werror -Wpedantic
BACKEND = $(wildcard vendor/gmp/minigmp/*.c)
OBJECTS = build/solver.o build/backend_alloc.o $(patsubst vendor/gmp/minigmp/%.c,build/vendor/%.o,$(BACKEND))
all: build/libsx.a
build/%.o: src/%.c
	@mkdir -p $(@D)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(WARN) -MMD -MP -c $< -o $@
build/vendor/%.o: vendor/gmp/minigmp/%.c vendor/gmp/minigmp/gmp_def.h
	@mkdir -p $(@D)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@
build/libsx.a: $(OBJECTS)
	$(AR) rcs $@ $^
clean:
	rm -rf build
-include $(OBJECTS:.o=.d)
.PHONY: all clean
build/driver: tests/driver.c build/libsx.a
	$(CC) $(CPPFLAGS) $(CFLAGS) $(WARN) $< build/libsx.a -o $@
test: build/driver build/pivot
	python3 tests/check.py
	./build/pivot
sanitize:
	$(MAKE) clean
	$(MAKE) CFLAGS="-std=c11 -O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer -fno-pie -no-pie" test
normal:
	$(MAKE) clean
	$(MAKE) test
.PHONY: test sanitize normal
build/pivot: tests/pivot.c src/solver.c src/backend.h include/sx_solver.h build/libsx.a
	$(CC) $(CPPFLAGS) $(CFLAGS) $(WARN) $< build/libsx.a -o $@