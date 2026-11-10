"""Independently reconstruct each P2 basis from the original input over Q."""
from fractions import Fraction as Q
from pathlib import Path
import random
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def reconstruct(rows, n, basis, nonbasic_values):
    """Gauss-Jordan on M_B [beta | -M_N], no use of the implementation's pivot update."""
    m = len(rows)
    total = m + n
    other = sorted(set(range(total)) - set(basis))
    augmented = []
    for i, (constant, *coefficients) in enumerate(rows):
        eq = [-Q(c) for c in coefficients] + [Q(k == i) for k in range(m)]
        augmented.append([eq[v] for v in basis] + [Q(constant)] + [-eq[v] for v in other])
    for i in range(m):
        pivot = next(k for k in range(i, m) if augmented[k][i])
        augmented[pivot], augmented[i] = augmented[i], augmented[pivot]
        row = [v / augmented[i][i] for v in augmented[i]]
        for j in range(m):
            if j != i:
                a = augmented[j][i]
                augmented[j] = [v - a*w for v, w in zip(augmented[j], row)]
        augmented[i] = row
    values = [nonbasic_values.get(v, Q(0)) for v in range(total)]
    canonical = []
    for i, b in enumerate(basis):
        rhs = augmented[i][m]
        coefficients = [Q(0)] * total
        for col, v in enumerate(other):
            coefficients[v] = augmented[i][m + 1 + col]
        values[b] = rhs + sum(coefficients[v] * values[v] for v in other)
        canonical.append([rhs, *coefficients])
    return values, canonical


def cases():
    # Lower and upper limits for original variables. Expression variables keep upper 0.
    yield 0, [], []
    yield 4, [], [(None, None)]*4
    yield 0, [[-1], [0], [1]], []
    yield 2, [[1,-1,-1], [2,3,-1]], [(None,None)]*2
    yield 1, [[(1 << 96) + 1, -(1 << 65)]], [(None,None)]
    yield 1, [[-1,0], [3,2]], [(-1, 0)]
    rng = random.Random(20261109)
    for i in range(64):
        n, m = rng.randint(1,5), rng.randint(1,6)
        bounds = [(rng.choice([None,-2,-1,0]), rng.choice([None,0,1,2])) for _ in range(n)]
        rows = [[rng.randint(-5,6)] + [rng.randint(-3,3) for _ in range(n)] for _ in range(m)]
        yield n, rows, bounds
    n = 12
    yield n, [[1] + [int(j == i)*(-2 if i % 2 else 3) for j in range(n)] for i in range(n)] + [[0]*(n+1)]*8, [(None,None)]*n


def scenario(n, rows, bounds):
    m = len(rows)
    basis = list(range(n, n+m))
    bounds = bounds + [(None,0)]*m
    nonbasic = {i: Q(0) for i in range(n)}
    steps, states = [], []
    for _ in range(17):
        values, equations = reconstruct(rows, n, basis, nonbasic)
        state = [*basis, *values, *(q for row in equations for q in row)]
        states.append(state)
        if len(steps) == 16:
            break
        choice = None
        for i, b in enumerate(basis):
            lo, hi = bounds[b]
            if lo is not None and values[b] < lo:
                side, target = 'L', lo
            elif hi is not None and values[b] > hi:
                side, target = 'U', hi
            else:
                continue
            for v in nonbasic:
                a = equations[i][1+v]
                if not a:
                    continue
                delta = (target-values[b])/a
                lo_v, hi_v = bounds[v]
                if (delta>0 and (hi_v is None or values[v]<hi_v)) or (delta<0 and (lo_v is None or values[v]>lo_v)):
                    choice = i,b,v,side,target
                    break
            if choice:
                break
        if not choice:
            break
        i,b,v,side,target = choice
        steps.append((i,v,side))
        basis[i] = v
        del nonbasic[v]
        nonbasic[b] = Q(target)
    return steps, states


def main():
    counts = [0, 0, 0]
    directions = set()
    for n, rows, bounds in cases():
        steps, states = scenario(n, rows, bounds)
        words = [str(len(rows)), str(n)] + [str(x) for row in rows for x in row]
        words.extend('*' if x is None else str(x) for pair in bounds for x in pair)
        words.append(str(len(steps)))
        for i,v,side in steps:
            words.extend([str(i),str(v),side]); directions.add(side)
        p = subprocess.run([str(ROOT/'build/reviewer_p2_driver')], input=' '.join(words)+'\n', text=True, capture_output=True, timeout=60)
        assert p.returncode == 0, (p.stderr, words)
        actual = p.stdout.splitlines()
        assert len(actual) == len(states), (actual, states)
        for idx, (line, expected) in enumerate(zip(actual, states)):
            got = [Q(x) for x in line.split()]
            assert got == expected, (rows, steps, idx, expected, got)
        counts[0] += 1; counts[1] += len(states); counts[2] += len(steps)
    assert directions == {'L', 'U'}
    print(f'Independent P2 reconstruction: {counts[0]} inputs, {counts[1]} tableaux, {counts[2]} pivots; lower and upper repairs passed.')


if __name__ == '__main__':
    main()
