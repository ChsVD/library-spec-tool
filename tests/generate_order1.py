"""Input-only ordering ablation; exact permutation and certificate checks."""
from pathlib import Path
from fractions import Fraction
import json,hashlib,random,time
root=Path(__file__).resolve().parents[1];out=root/'evidence/order1_inputs';out.mkdir(exist_ok=False);(out/'inputs').mkdir()
orders=['identity','rows_nnz','cols_nnz','both_nnz','rows_bits','cols_bits','both_bits','random_control']
cases=[]
for group,folder in [('seed','seed2_inputs'),('qcp','qcp1_inputs'),('hard','stress1_inputs')]:
 manifest=root/'evidence'/folder/'cases.json';source=json.loads(manifest.read_text())['cases']
 if group=='hard':source=[c for c in source if c['id'].startswith('sparse128-')]
 for c in source:
  data=(manifest.parent/c['input_path']).read_bytes();assert hashlib.sha256(data).hexdigest()==c['sha256']
  z=list(map(int,data.split()));m,n=z[:2];assert len(z)==2+m*(n+1);a=[z[2+i*(n+1):2+(i+1)*(n+1)] for i in range(m)]
  split=('train' if c['seed']<=31004 else 'holdout') if group=='seed' else group
  for order in orders:
   start=time.perf_counter();rp=list(range(m));cp=list(range(n))
   if order.endswith('nnz'):
    if order.startswith(('rows','both')):rp.sort(key=lambda i:sum(v!=0 for v in a[i][1:]))
    if order.startswith(('cols','both')):cp.sort(key=lambda j:sum(a[i][j+1]!=0 for i in range(m)))
   if order.endswith('bits'):
    if order.startswith(('rows','both')):rp.sort(key=lambda i:max(abs(v).bit_length() for v in a[i]))
    if order.startswith(('cols','both')):cp.sort(key=lambda j:max((abs(a[i][j+1]).bit_length() for i in range(m)),default=0))
   if order=='random_control':
    rng=random.Random(int(hashlib.sha256(('order1:'+c['id']).encode()).hexdigest(),16));rng.shuffle(rp);rng.shuffle(cp)
   elapsed=time.perf_counter()-start
   b=[[a[i][0]]+[a[i][j+1] for j in cp] for i in rp]
   assert sorted(rp)==list(range(m)) and sorted(cp)==list(range(n))
   proof=c['proof']
   if proof['kind']=='witness':
    x=[Fraction(proof['values'][j]) for j in cp];assert all(Fraction(row[0])+sum(v*y for v,y in zip(row[1:],x))<=0 for row in b)
    proof={'kind':'witness','values':[str(v) for v in x]}
   else:
    assert proof['kind']=='nonnegative_combination';w=[proof['weights'][i] for i in rp]
    sums=[sum(v*row[j] for v,row in zip(w,b)) for j in range(n+1)];assert all(v>=0 for v in w) and sums[0]>0 and not any(sums[1:])
    proof={'kind':'nonnegative_combination','weights':w}
   ident=c['id']+'--'+order;payload=(f'{m} {n}\n'+'\n'.join(' '.join(map(str,row)) for row in b)+'\n').encode();sha=hashlib.sha256(payload).hexdigest();f=out/'inputs'/(ident+'.txt');f.write_bytes(payload)
   cases.append(dict(id=ident,base_id=c['id'],family=c['family'],group=group,split=split,order=order,rows=m,variables=n,expected_q=c['expected_q'],proof=proof,input_path='inputs/'+f.name,sha256=sha,row_map=rp,column_map=cp,source_manifest=str(manifest),source_sha256=c['sha256'],ordering_python_seconds=elapsed))
(out/'cases.json').write_text(json.dumps({'schema':1,'orders':orders,'selection':'min geometric mean PAR2 cost ratio to identity on seed train cases only; candidates exclude random_control; ties retain earlier order','definitions':{'nnz':'ascending variable-coefficient nonzero count, constant excluded','bits':'ascending maximum abs coefficient bit length; row includes constant, column variable only','ties':'stable original index','random_control':'fixed per-case SHA256-derived seed; not eligible for selection'},'cases':cases},indent=2))
print('Certified',len(cases),'ordered inputs;',len({c['base_id'] for c in cases}),'base cases; unique per-base payloads',len({(c['base_id'],c['sha256']) for c in cases}))
