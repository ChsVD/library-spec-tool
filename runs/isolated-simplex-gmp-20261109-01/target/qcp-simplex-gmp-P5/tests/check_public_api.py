"""The solver exposes one list entry; arrays belong only to the P2 table layer."""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]

def compiles(body):
    result = subprocess.run(['cc', '-std=c11', '-Wall', '-Werror', '-Iinclude', '-Ivendor',
                             '-x', 'c', '-fsyntax-only', '-'], cwd=ROOT,
                            input=body, text=True, capture_output=True)
    return result.returncode == 0

header = '#include "sx_solver_contract.h"\n'
assert compiles(header + 'void probe(void) { (void)&sx_check_qcp; }\n')
assert not compiles(header + 'void probe(void) { (void)&sx_check; }\n')
assert not compiles(header + 'SxProblem problem;\n')
assert compiles('#include "sx_table.h"\nSxProblem problem;\n')
symbols = subprocess.check_output(['nm', '-g', '--defined-only', 'build/libsx_solver.a'],
                                  cwd=ROOT, text=True)
exported = {line.split()[-1] for line in symbols.splitlines() if len(line.split()) >= 3}
assert 'sx_check_qcp' in exported and 'sx_check' not in exported
print('Public API boundary passed: list-only solver header and exported entry; P2 arrays retained')
