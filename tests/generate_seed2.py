"""Deterministic, independently certified stress inputs; no solver used to label."""
from pathlib import Path
from fractions import Fraction
import random,json,hashlib,math
root=Path(__file__).resolve().parents[1]
out=root/'evidence/seed2_inputs';out.mkdir(exist_ok=True);(out/'inputs').mkdir(exist_ok=True)
cases=[]
def save(name,family,rows,witness,weights,seed,permutation_of=None):
 n=len(rows[0])-1;m=len(rows)
 if witness is not None:
  assert all(sum(Fraction(a)*x for a,x in zip(row,[Fraction(1)]+witness))<=0 for row in rows)
  proof={'kind':'witness','values':[str(x) for x in witness]};expected='FEASIBLE'
 else:
  assert len(weights)==m and all(w>=0 for w in weights)
  sums=[sum(w*row[j] for w,row in zip(weights,rows)) for j in range(n+1)]
  assert sums[0]>0 and all(x==0 for x in sums[1:])
  proof={'kind':'nonnegative_combination','weights':weights};expected='UNSAT'
 data=(f'{m} {n}\n'+'\n'.join(' '.join(map(str,row)) for row in rows)+'\n').encode()
 assert max(len(str(x)) for row in rows for x in row)<1024
 f=out/'inputs'/(name+'.txt');f.write_bytes(data)
 cases.append(dict(id=name,family=family,rows=m,variables=n,seed=seed,expected_q=expected,proof=proof,input_path='inputs/'+f.name,sha256=hashlib.sha256(data).hexdigest(),permutation_of=permutation_of,max_coefficient_bits=max(abs(x).bit_length() for row in rows for x in row),density=sum(x!=0 for row in rows for x in row[1:])/(n*m)))
def system(family,n,m,bits,density,seed,unsat,thin=False,redundant=False):
 rng=random.Random(seed);nums=[rng.randrange(-7,8) or 1 for _ in range(n)];q=101 if thin else 1
 x=[Fraction(v,q) for v in nums]
 def vector():
  a=[(rng.getrandbits(bits)|1)*rng.choice([-1,1]) if rng.random()<density else 0 for _ in range(n)]
  if not any(a):a[rng.randrange(n)]=1
  return a
 # A and -A seed both signs for every variable; row order is shuffled later.
 pool=[vector() for _ in range(max(n,16))]
 for j in range(n):
  if not any(a[j] for a in pool):pool[j][j]=1
 vectors=pool+ [[-v for v in a] for a in pool]
 while len(vectors)<m:
  if redundant:
   a=rng.choice(pool);b=rng.choice(pool);vectors.append([u+v for u,v in zip(a,b)])
  else:vectors.append(vector())
 vectors=vectors[:m]
 rows=[]
 for i,a in enumerate(vectors):
  slack=rng.randrange(1,9) if family.startswith('interior') else (0 if thin or i<2*n else rng.randrange(0,8))
  rows.append([-sum(u*v for u,v in zip(a,nums))-slack]+[q*v for v in a])
 weights=None
 if unsat:
  # An n+1-row positive combination gives constant 1 and zero variable sum.
  count=n;ww=[rng.randrange(1,8) for _ in range(count)]
  closing=[-sum(ww[i]*rows[i][j] for i in range(count)) for j in range(n+1)];closing[0]+=1
  rows[-1]=closing;weights=ww+[0]*(m-count-1)+[1]
 order=list(range(m));rng.shuffle(order);rows=[rows[i] for i in order]
 if weights is not None:weights=[weights[i] for i in order]
 name=f'{family}-s{seed}-'+('unsat' if unsat else 'feas')
 save(name,family,rows,None if unsat else x,weights,seed)
 return name,rows,x,weights
specs=[('dense24',24,96,8,1.0),('mixed128',12,48,128,.65),('interior32',32,128,8,.12)]
for seed in range(31001,31009):
 for family,n,m,bits,density in specs:
  for unsat in [False,True]:system(family,n,m,bits,density,seed,unsat)
(out/'cases.json').write_text(json.dumps({'schema':1,'generator':'tests/generate_seed2.py','cases':cases},indent=2))
print('Generated and certified',len(cases),'cases at',out)
