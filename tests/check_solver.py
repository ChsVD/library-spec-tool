"""Self-authored solver cases and exact substitution. No SMT or FME reference."""
from fractions import Fraction
import json,random,subprocess
rng=random.Random(20261109)
count=0

def run(rows,n,expected,args=()):
 global count
 data=f'{len(rows)} {n}\n'+'\n'.join(' '.join(map(str,r)) for r in rows)+'\n'
 p=subprocess.run(['./build/solver_cli',*args],input=data,text=True,capture_output=True,timeout=20)
 assert p.returncode==0,(p.returncode,p.stderr,data)
 r=json.loads(p.stdout)
 assert r['error']=='OK' and r['q']==expected,(data,r)
 if expected=='FEASIBLE':
  w=list(map(Fraction,r['witness']))
  assert len(w)==n
  assert all(Fraction(row[0])+sum(a*x for a,x in zip(row[1:],w))<=0 for row in rows)
  assert r['stats']['verified_rows']==len(rows)
  integer=all(x.denominator==1 for x in w)
  assert r['z']==('SAT' if integer else 'UNKNOWN')
  assert r['reason']==('NONE' if integer else 'FRACTIONAL')
  assert r['conflict'] is None
 elif expected=='UNSAT':
  assert r['z']=='UNSAT' and not r['witness']
  c=r['conflict'];assert c is not None
  total=Fraction(c['constant'])
  for term in c['blockers']:
   a,b=Fraction(term['coefficient']),Fraction(term['bound'])
   assert term['is_lower']==(a<0 if c['to_lower'] else a>0)
   assert term['variable']==n+term['source_row']
   assert 0<=term['source_row']<len(rows) and b==0
   total+=a*b
  assert total==Fraction(c['attainable'])
  assert total<Fraction(c['required']) if c['to_lower'] else total>Fraction(c['required'])
 else:
  assert not r['witness'] and r['conflict'] is None
 count+=1
 return r

run([],0,'FEASIBLE');run([],15,'FEASIBLE');run([[-1]],0,'FEASIBLE');run([[1]],0,'UNSAT')
for a in [1,2,2**32,2**64+1,10**30]:run([[1,-a],[-1,a]],1,'FEASIBLE')
base=[[-3,1,1],[3,-1,-1],[-1,1,-1],[1,-1,1]]
run(base,2,'UNKNOWN',['--pivots','1']);run(base,2,'FEASIBLE',['--pivots','2'])
run([[1,-1],[0,1]],1,'UNSAT',['--pivots','1'])
for _ in range(45):
 n=rng.randrange(1,5);point=[rng.randrange(-9,10) for _ in range(n)];rows=[]
 for i in range(rng.randrange(1,8)):
  coeff=[rng.randrange(-8,9) for _ in range(n)];slack=rng.randrange(0,7);rows.append([-sum(a*x for a,x in zip(coeff,point))-slack,*coeff])
 # Row reordering, positive scaling, duplicated row and an unused variable.
 rng.shuffle(rows)
 rows=[[v*scale for v in row] for row in rows for scale in [2**rng.randrange(0,80)+1]]
 run(rows,n,'FEASIBLE')
 if rows:run(rows+[rows[0]],n,'FEASIBLE')
 run([r+[0] for r in rows],n+1,'FEASIBLE')
for _ in range(35):
 n=rng.randrange(1,5);k=rng.randrange(n);lo=rng.randrange(-20,20);hi=lo-rng.randrange(1,10)
 lower=[lo]+[0]*n;lower[k+1]=-1;upper=[-hi]+[0]*n;upper[k+1]=1
 rows=[]
 for row in [lower,upper]:
  scale=2**rng.randrange(1,70)+1;rows.append([scale*v for v in row])
 rng.shuffle(rows);run(rows,n,'UNSAT')
# Beyond former 8/16 limits, exact integer fixed values.
rows=[]
for i in range(9):
 a=[0]*10;a[0]=-(2**64+i);a[i+1]=1;rows.extend([a,[-v for v in a]])
run(rows,9,'FEASIBLE')
run([],0,'FEASIBLE',['--ms',str(2**64-1)])
for bad in [b'1 0 0\x00junk',b'1 0 0\x00',b'0 0\x00',b'0 0 extra',b'1 0',b'1 0 wat']:
 p=subprocess.run(['./build/solver_cli'],input=bad,capture_output=True)
 assert p.returncode!=0 and not p.stdout,(bad,p.returncode,p.stdout)
# Simulated read failure: stdin is a directory on POSIX, not a normal EOF.
import os
fd=os.open('.',os.O_RDONLY)
try:
 p=subprocess.run(['./build/solver_cli'],stdin=fd,capture_output=True)
 assert p.returncode!=0 and not p.stdout
finally:os.close(fd)
print(f'P3 CLI tests passed: {count} exact-case/transform checks, 6 malformed byte streams and I/O error rejection')
