"""Main-agent acceptance cases, independent of the implementation author's suite."""
from fractions import Fraction
from pathlib import Path
import json
import random
import subprocess

ROOT = Path(__file__).resolve().parents[1]
CLI = ROOT / 'build/arith_cli'
rng = random.Random(61012026)
count = 0

def check(op, an, ad, bn, bd):
    global count
    a, b = Fraction(an, ad), Fraction(bn, bd)
    expected = {'+': lambda: a+b, '-': lambda: a-b,
                '*': lambda: a*b, '/': lambda: a/b,
                'c': lambda: (a>b)-(a<b)}[op]()
    expected = str(expected) if op == 'c' else f'{expected.numerator}/{expected.denominator}'
    p = subprocess.run([str(CLI), op, str(an), str(ad), str(bn), str(bd)],
                       capture_output=True, text=True, timeout=30)
    assert p.returncode == 0 and p.stdout.strip() == expected, (op, an, ad, bn, bd, expected, p.stdout, p.stderr)
    count += 1

for k in [1, 31, 32, 33, 63, 64, 65, 96, 127, 128, 257, 513, 1024, 2048]:
    for delta in [-1, 0, 1]:
        n = 2**k + delta
        for op in '+-*/c':
            check(op, -n, 2**k, 2**(k+1)+1, -(2**k+3))
    for op in '+-*/c':
        check(op, 0, -(2**k), -2**k, 2**k+1)
        check(op, 7*2**k, -13*2**k, -11*2**k, 17*2**k)

for _ in range(100):
    bits = rng.choice([32, 64, 192, 512, 1024, 2048])
    n = rng.getrandbits(bits) or 1
    # Almost equal fractions stress comparisons and cancellation.
    for op in '+-*/c':
        check(op, n, n+1, n+1, n+2)
        check(op, -n, n+1, -n, n+1)

for args in [('1', '0', '1', '1'), ('', '1', '1', '1'),
             ('--1', '1', '1', '1'), ('1x', '1', '1', '1')]:
    p = subprocess.run([str(CLI), '+', *args], capture_output=True, text=True)
    assert p.returncode == 1 and not p.stdout, (args, p)
p = subprocess.run([str(CLI), '/', '1', '1', '0', '1'], capture_output=True, text=True)
assert p.returncode == 1 and not p.stdout
print(json.dumps({'exact_comparisons': count, 'invalid_cases': 5, 'status': 'passed'}))
