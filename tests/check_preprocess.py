from fractions import Fraction
import json,subprocess
cases=[
 (5,[[-12,0,0,0,0,0],[6,-6,0,0,0,0],[-4,4,0,0,0,0],[0,0,0,0,0,0],[-10,0,0,0,0,0],[10,0,-5,0,0,0],[-8,0,4,0,0,0]]),
 (4,[[-9,0,0,0,0],[6,-6,0,0,0],[0,0,0,0,0],[14,0,0,-7,0],[-8,4,0,4,0],[12,-12,0,0,0]]),
 (2,[[7,0,0],[-3,0,0]]),
 (3,[[-5,0,0,0],[2**512,-2**513,0,0],[-3*2**512,3*2**513,0,0]]),
 (0,[[0],[-3]]), (8,[])
]
count=0
for n,rows in cases:
 data=f'{len(rows)} {n}\n'+'\n'.join(' '.join(map(str,row)) for row in rows)+'\n'
 reference=None
 for mask in [15,*range(15)]:
  p=subprocess.run(['./build/solver_cli','--disable-opts',str(mask),'--matrix-stats','1'],input=data,text=True,capture_output=True,check=True)
  r=json.loads(p.stdout);assert r['error']=='OK' and r['q'] in ['FEASIBLE','UNSAT'],r
  if reference is None:reference=r
  assert r['q']==reference['q'] and r['z']==reference['z']
  if r['q']=='FEASIBLE':
   witness=list(map(Fraction,r['witness']));assert len(witness)==n
   assert all(Fraction(row[0])+sum(a*x for a,x in zip(row[1:],witness))<=0 for row in rows)
   assert r['witness']==reference['witness']
  else:
   c=r['conflict'];assert c['basic_variable']==n+c['bound_source_row']
   rhs=[Fraction(c['constant']),*([Fraction(0)]*n)]
   for b in c['blockers']:
    assert b['variable']==n+b['source_row'] and not b['is_lower'] and Fraction(b['bound'])==0
    for j in range(n+1):rhs[j]+=Fraction(b['coefficient'])*rows[b['source_row']][j]
   assert rhs==list(map(Fraction,rows[c['bound_source_row']]))
   assert Fraction(c['attainable'])>Fraction(c['required'])
  if r['optimization']['matrix_snapshots']:
   assert r['optimization']['matrix_cells_scanned']>=r['optimization']['table_cells']
  count+=1
p=subprocess.run(['./build/solver_cli','--disable-opts','16'],input='0 0',text=True,capture_output=True)
assert p.returncode==2 and not p.stdout
print(f'P4 CLI masks passed: {count} exact cases, witness/affine-conflict and invalid-mask checks')
