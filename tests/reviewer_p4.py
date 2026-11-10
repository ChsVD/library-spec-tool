"""Compare reference and optimized P4 paths against the unmodified input rows."""
import json
import random
import subprocess
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CLI = ROOT / 'build/solver_cli'


def run(rows, n, options):
    payload = f'{len(rows)} {n}\n' + '\n'.join(' '.join(map(str,row)) for row in rows) + '\n'
    proc = subprocess.run([str(CLI),*options],input=payload,text=True,capture_output=True,timeout=60)
    assert proc.returncode == 0, (rows,proc.stderr)
    return json.loads(proc.stdout)


def validate(r,rows,n,expected):
    assert r['error']=='OK' and r['q']==expected,(rows,r,expected)
    if expected=='FEASIBLE':
        w=list(map(Q,r['witness']))
        assert len(w)==n and r['stats']['verified_rows']==len(rows) and r['conflict'] is None
        for row in rows:
            assert row[0]+sum(a*v for a,v in zip(row[1:],w))<=0,(row,w)
        assert r['z']==('SAT' if all(v.denominator==1 for v in w) else 'UNKNOWN')
        for j in range(n):
            if all(row[j+1]==0 for row in rows):
                assert w[j]==0
    else:
        c=r['conflict']; src=c['bound_source_row']
        assert not r['witness'] and r['z']=='UNSAT' and not c['to_lower']
        assert 0<=src<len(rows) and c['basic_variable']==n+src and 0<=c['row']<len(rows)
        # On the ORIGINAL scale, the blocker relation must be an identity
        # for all x, not just for the last trial assignment.
        symbolic=[Q(c['constant'])]+[Q(0)]*n
        ext=Q(c['constant']); seen={src}
        for b in c['blockers']:
            j=b['source_row']; a=Q(b['coefficient']); bound=Q(b['bound'])
            assert j not in seen and 0<=j<len(rows) and b['variable']==n+j
            assert not b['is_lower'] and a<0 and bound==0
            symbolic=[u+a*v for u,v in zip(symbolic,rows[j])]
            ext+=a*bound; seen.add(j)
        assert symbolic==rows[src],(symbolic,rows[src],c)
        assert ext==Q(c['attainable'])>Q(c['required'])==0


def corpus():
    rng=random.Random(41092026)
    yield 0,[], 'FEASIBLE'
    yield 12,[[0]*13,[-8]+[0]*12], 'FEASIBLE'
    yield 5,[[-91]+[0]*5,[31]+[0]*5,[0]*6],'UNSAT'
    for trial in range(28):
        n=rng.randint(5,12); pos=rng.sample(range(n),2)
        def expanded(c,a,b,d):
            row=[0]*(n+1);row[0]=d*c;row[1+pos[0]]=d*a;row[1+pos[1]]=d*b
            return row
        d=[(2**rng.randint(32,75)+1)*(j+2) for j in range(5)]
        # Unique rational solution x=1/2,y=-3/4. Column and row order vary.
        ok=[expanded(1,-2,0,d[0]),expanded(-1,2,0,d[1]),expanded(3,0,4,d[2]),expanded(-3,0,-4,d[3])]
        # x+y>=1, x<=0, y<=0. Different positive row factors force rescaling
        # of conflict coefficients and can change the final physical pivot row.
        bad=[expanded(1,-1,-1,d[0]),expanded(0,1,0,d[1]),expanded(0,0,1,d[2])]
        for rows,expected in [(ok,'FEASIBLE'),(bad,'UNSAT')]:
            rows += [expanded(-1,0,0,d[4]),expanded(0,0,0,1),rows[-1][:]]
            rng.shuffle(rows)
            yield n,rows,expected


def main():
    import sys
    # The acceptance runner supplies one JSON array of CLI options per mode.
    modes=[json.loads(options) for options in sys.argv[1:]]
    assert len(modes)>=2
    cases=0
    for n,rows,expected in corpus():
        for options in modes:
            validate(run(rows,n,options),rows,n,expected)
        cases+=1
    # A single nonzero variable coefficient in a 3x3 input; constants are
    # part of row normalization but excluded from coefficient-density counts.
    rows=[[-7,0,0,0],[12,0,-6,0],[0,0,0,0]]
    for mask in range(16):
        opts=['--disable-opts',str(mask)]
        result=run(rows,3,opts)
        validate(result,rows,3,'FEASIBLE')
        b=result['optimization']
        assert b['input_nonzeros']==b['active_nonzeros']==1 and b['input_cells']==9
        assert b['active_rows']==(3 if mask&1 else 1) and b['active_variables']==(3 if mask&4 else 1)
        assert b['active_cells']==b['active_rows']*b['active_variables']
    print(f'Independent P4 original-row checks passed: {cases} cases x {len(modes)} modes.')


if __name__=='__main__':
    main()
