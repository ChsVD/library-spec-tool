"""Final acceptance runner; starts with the author's sanitizer build."""
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[1]
commands = [
    ['python3', 'tests/check_baseline.py'],
    ['./build/test_arith'],
    ['python3', 'tests/reviewer_fraction.py'],
    ['make', 'clean'],
    ['make', 'test'],
    ['python3', 'tests/reviewer_fraction.py'],
]
with (root / 'build/reviewer_acceptance.log').open('w') as log:
    for command in commands:
        print(command, flush=True)
        log.write(str(command) + '\n')
        log.flush()
        result = subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT)
        log.flush()
        print('exit', result.returncode, flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)
