"""Reproduce the P2 review on WSL. Leave a normal build available on success."""
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / 'build'
STRICT = ['-std=c11', '-Wall', '-Wextra', '-Werror', '-Wpedantic', '-Wconversion', '-Wshadow']
SAN = ['-g', '-O1', '-fsanitize=address,undefined', '-fno-omit-frame-pointer']
ENV = {**os.environ, 'ASAN_OPTIONS':'detect_leaks=1:halt_on_error=1', 'UBSAN_OPTIONS':'halt_on_error=1:print_stacktrace=1'}


def run(log, command):
    log.write(' '.join(command) + '\n')
    log.flush()
    subprocess.run(command, cwd=ROOT, env=ENV, stdout=log, stderr=subprocess.STDOUT, check=True)


def inspect(log, flags):
    for name in ['reviewer_p2_driver', 'reviewer_p2_budget']:
        run(log, ['cc', *STRICT, *flags, '-Iinclude', '-Ivendor', f'tests/{name}.c',
                  'build/libsx_table.a', '-o', f'build/{name}'])
    run(log, ['./build/reviewer_p2_budget'])
    run(log, [sys.executable, '-B', 'tests/reviewer_p2.py'])


def main():
    BUILD.mkdir(exist_ok=True)
    with (BUILD/'reviewer_p2_acceptance.log').open('w') as log:
        run(log, [sys.executable, '-B', 'tests/check_baseline.py'])
        run(log, ['make', 'sanitize'])
        inspect(log, SAN)
        run(log, ['make', 'clean'])
        run(log, ['make', 'test'])
        inspect(log, ['-O2'])
        run(log, [sys.executable, '-B', 'tests/reviewer_fraction.py'])
    print('P2 acceptance passed. Details in build/reviewer_p2_acceptance.log')


if __name__ == '__main__':
    main()
