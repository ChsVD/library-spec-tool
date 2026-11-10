"""Independent feasibility, witness, and status checks through the public C ABI."""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import random
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / 'build/reviewer_p3_driver'
counts = {'feasible': 0, 'unsat': 0, 'limited': 0}


def satisfies(rows, x):
    return all(row[0] + sum(a*v for a, v in zip(row[1:], x)) <= 0 for row in rows)


def vertex(rows, n):
    mat = [[*map(Q, row[1:]), -Q(row[0])] for row in rows]
    for j in range(n):
        k = next((k for k in range(j, n) if mat[k][j]), None)
        if k is None:
            return None
        mat[j], mat[k] = mat[k], mat[j]
        mat[j] = [v/mat[j][j] for v in mat[j]]
        for i in range(n):
            if i != j:
                a = mat[i][j]
                mat[i] = [v - a*w for v,w in zip(mat[i],mat[j])]
    return [row[-1] for row in mat]


def bounded_feasible(rows, n):
    # Only called for boxes. A nonempty bounded polyhedron has a vertex,
    # including lower-dimensional feasible sets. Enumerate independent tight rows.
    for tight in combinations(rows, n):
        x = vertex(tight, n)
        if x is not None and satisfies(rows, x):
            return True
    return False


def verify_conflict(lines, rows, n):
    # A source expression s_i is exactly c_i0 + sum c_ij*x_j. Substitute
    # these definitions into the returned tableau row, coefficient by coefficient.
    tag, basic, source, lower, count, constant, required, attainable = lines[0].split()
    source = int(source)
    assert tag == 'conflict' and int(basic)==n+source and 0<=source<len(rows)
    assert int(lower)==0 and Q(required)==0 and int(count)==len(lines)-1
    symbolic = [Q(constant)] + [Q(0)]*n
    extreme = Q(constant)
    ids = set()
    for line in lines[1:]:
        tag, variable, index, is_lower, coefficient, bound = line.split()
        index = int(index)
        assert tag=='blocker' and 0<=index<len(rows) and int(variable)==n+index
        assert index not in ids and index!=source
        ids.add(index)
        assert int(is_lower)==0 and Q(bound)==0 and Q(coefficient)<0
        extreme += Q(coefficient)*Q(bound)
        symbolic = [v+Q(coefficient)*a for v,a in zip(symbolic,rows[index])]
    assert symbolic == rows[source] and extreme == Q(attainable) > Q(required), (lines,rows)


def probe(n, rows, pivots=0, byte_cap=0, limbs=0):
    data = [len(rows), n, pivots, byte_cap, limbs, *(v for row in rows for v in row)]
    def invoke(options):
        p = subprocess.run([str(BIN),*options], input=' '.join(map(str,data))+'\n', text=True,
                           capture_output=True, timeout=90)
        assert p.returncode == 0, (rows,p.stdout,p.stderr)
        return p.stdout.splitlines()
    lines = invoke([])
    header = tuple(map(int,lines[0].split()))
    witness = tuple(map(Q,lines[1:1+header[-1]]))
    assert len(witness) == header[-1], (header,witness)
    tail = lines[1+header[-1]:]
    if header[1] == 2:
        verify_conflict(tail,rows,n)
    else:
        assert not tail
    return header, witness


def verify(n, rows, feasible, expected_witness=None, pivots=0):
    if any(len(row)!=n+1 for row in rows):
        raise ValueError(rows)
    (e,q,z,reason,k,peak,_), x = probe(n,rows,pivots=pivots)
    assert e == 0, (rows,e,reason)
    if feasible:
        assert q == 1 and len(x) == n and satisfies(rows,x), (rows,q,x)
        assert z == (1 if all(v.denominator==1 for v in x) else 3), (rows,z,x)
        assert reason == (0 if z==1 else 1), (rows,reason,x)
        if expected_witness is not None:
            assert x == tuple(expected_witness), (x,expected_witness)
        counts['feasible'] += 1
    else:
        assert (q,z,reason) == (2,2,6) and not x, (rows,q,z,x)
        counts['unsat'] += 1
    return k, peak


def main():
    for n in [0,4]:
        verify(n, [], True, [0]*n)
    verify(0, [[0],[-17]], True, [])
    verify(0, [[5]], False)
    verify(1, [[1,-2],[-1,2]], True, [Q(1,2)])
    verify(1, [[1,-2],[-4,2]], True, [Q(1,2)])  # an integer solution also exists
    verify(1, [[1,-1],[0,1]], False)
    verify(2, [[-3,1,1],[3,-1,-1],[-1,1,-1],[1,-1,1]], True,[2,1])
    huge = 2**163+9
    verify(1,[[-1,huge],[1,-huge]], True, [Q(1,huge)])
    verify(1,[[1,-huge],[0,huge]], False)
    n = 10
    rows = []
    for i in range(n):
        row = [-i-1] + [int(j==i) for j in range(n)]
        rows.extend([row, [-v for v in row]])
    verify(n, rows, True, range(1,n+1))
    rng = random.Random(3112026)
    for i in range(125):
        n = 1 + i%3
        rows = []
        for j in range(n):
            axis = [int(k==j) for k in range(n)]
            rows += [[-2,*axis], [-2,*[-v for v in axis]]]
        rows += [[rng.randint(-5,5),*[rng.randint(-3,3) for _ in range(n)]] for _ in range(rng.randint(1,6))]
        wanted = bounded_feasible(rows,n)
        verify(n,rows,wanted)
        if i%6==0:
            altered = [row[:] for row in rows] + [[v*7 for v in rows[-1]]]
            rng.shuffle(altered)
            verify(n,altered,wanted)
    for i in range(22):
        # Positive weighted sum of all rows is 1 <= 0. Some coordinates are free.
        n = 4
        base = [[rng.randint(-4,4), rng.randint(-5,5), rng.randint(-5,5), 0, 0] for _ in range(4)]
        weights = [rng.randint(1,4) for _ in base]
        last = [-sum(w*row[j] for w,row in zip(weights,base)) for j in range(n+1)]
        last[0] += 1
        verify(n,[*base,last],False)
    row2 = [[1,-1,0],[1,0,-1]]
    k, peak = verify(2,row2,True,[1,1],pivots=2)
    assert k == 2
    header, x = probe(2,row2,pivots=1)
    assert header[:4] == (0,3,3,4) and header[4] == 1 and not x, header
    counts['limited'] += 1
    header, x = probe(2,row2,byte_cap=peak)
    assert header[1:3] == (1,1) and satisfies(row2,x), header
    header, x = probe(2,row2,byte_cap=peak-1)
    assert header[:4] == (0,3,3,2) and not x, header
    counts['limited'] += 1
    header, x = probe(1,[[-1,huge],[1,-huge]],limbs=4)
    assert header[:4] == (0,3,3,3) and not x, header
    counts['limited'] += 1
    print('Independent public-API checks:',counts)


if __name__ == '__main__':
    main()
