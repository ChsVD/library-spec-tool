CC = cc
AR = ar
CPPFLAGS = -Iinclude -Ivendor
CFLAGS = -std=c11 -O2 -g
OWNFLAGS = -Wall -Wextra -Werror -Wpedantic -Wconversion -Wshadow
BACKEND = $(wildcard vendor/gmp/minigmp/*.c)
OBJECTS = $(patsubst vendor/gmp/minigmp/%.c,build/vendor/%.o,$(BACKEND))
all: build/libsx_arith.a build/libsx_table.a build/libsx_solver.a build/arith_cli build/solver_cli build/test_arith build/test_table build/test_solver build/test_preprocess build/qcp_example
build/vendor:
	mkdir -p build/vendor
build/vendor/%.o: vendor/gmp/minigmp/%.c vendor/gmp/minigmp/gmp_def.h | build/vendor
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@
build/arith.o: src/arith.c src/backend.h src/runtime_scope.h include/sx_arith.h | build/vendor
	$(CC) $(CPPFLAGS) $(CFLAGS) $(OWNFLAGS) -c $< -o $@
build/solver.o: src/solver.c src/integer_ops.h src/runtime_scope.h include/sx_solver_contract.h include/sx_table.h | build/vendor
	$(CC) $(CPPFLAGS) $(CFLAGS) $(OWNFLAGS) -c $< -o $@
build/libsx_solver.a: build/solver.o build/table.o build/arith.o $(OBJECTS)
	$(AR) rcs $@ $^
build/solver_cli: tests/solver_cli.c build/libsx_solver.a
	$(CC) $(CPPFLAGS) $(CFLAGS) $(OWNFLAGS) $< build/libsx_solver.a -o $@
build/qcp_example: examples/qcp_check.c build/libsx_solver.a
	$(CC) $(CPPFLAGS) $(CFLAGS) $(OWNFLAGS) $< build/libsx_solver.a -o $@
examples: build/qcp_example
	./build/qcp_example integer
	./build/qcp_example fraction
	./build/qcp_example conflict
	./build/qcp_example budget
build/bench_preprocess: tests/bench_preprocess.c build/libsx_solver.a
	$(CC) $(CPPFLAGS) $(CFLAGS) $(OWNFLAGS) $< build/libsx_solver.a -o $@
benchmark: build/bench_preprocess
	python3 tests/benchmark_preprocess.py
build/test_preprocess: tests/test_preprocess.c build/libsx_solver.a
	$(CC) $(CPPFLAGS) $(CFLAGS) $(OWNFLAGS) $< build/libsx_solver.a -o $@
build/test_solver: tests/test_solver.c build/libsx_solver.a
	$(CC) $(CPPFLAGS) $(CFLAGS) $(OWNFLAGS) $< build/libsx_solver.a -o $@
build/table.o: src/table.c src/runtime_scope.h include/sx_table.h include/sx_solver_contract.h include/sx_arith.h | build/vendor
	$(CC) $(CPPFLAGS) $(CFLAGS) $(OWNFLAGS) -c $< -o $@
build/libsx_table.a: build/table.o build/arith.o $(OBJECTS)
	$(AR) rcs $@ $^
build/test_table: tests/test_table.c build/libsx_table.a
	$(CC) $(CPPFLAGS) $(CFLAGS) $(OWNFLAGS) $< build/libsx_table.a -o $@
build/libsx_arith.a: build/arith.o $(OBJECTS)
	$(AR) rcs $@ $^
build/arith_cli: tests/arith_cli.c build/libsx_arith.a
	$(CC) $(CPPFLAGS) $(CFLAGS) $(OWNFLAGS) $< build/libsx_arith.a -o $@
build/test_arith: tests/test_arith.c build/libsx_arith.a
	$(CC) $(CPPFLAGS) $(CFLAGS) $(OWNFLAGS) $< build/libsx_arith.a -o $@
test: all
	./build/test_arith
	./build/test_table
	./build/test_solver
	SX_TEST_DISABLE_OPTS=15 ./build/test_solver
	./build/test_preprocess
	python3 tests/check_public_api.py
	python3 tests/check_fraction.py
	python3 tests/check_solver.py
	python3 tests/check_preprocess.py
	$(MAKE) examples
	python3 tools/test_release_verifier.py
normal:
	$(MAKE) clean
	$(MAKE) CFLAGS="-std=c11 -O2 -g" all examples
sanitize:
	$(MAKE) clean
	$(MAKE) CFLAGS="-std=c11 -O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer" test
clean:
	rm -f build/arith_cli build/test_arith build/arith.o build/table.o build/libsx_arith.a build/libsx_table.a build/test_table build/vendor/*.o build/solver.o build/libsx_solver.a build/solver_cli build/test_solver build/test_preprocess build/bench_preprocess build/qcp_example
.PHONY: all test sanitize clean benchmark normal examples
