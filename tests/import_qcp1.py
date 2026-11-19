"""Convert captured QCP-branch LIA calls, independently certify rational relaxation."""
from pathlib import Path
from fractions import Fraction as F
from math import gcd,lcm
from functools import reduce
import json,hashlib
root=Path(__file__).resolve().parents[1];source=root/'evidence/qcp_capture1';out=root/'evidence/qcp1_inputs';out.mkdir(exist_ok=True);(out/'inputs').mkdir(exist_ok=True)
def certify(original,n):
 m=len(original);rows=[(list(r),[F(int(i==j)) for j in range(m)]) for i,r in enumerate(original)];layers=[];active=set(range(1,n+1))
 def compact(rows):
  unique={}
  for a,w in rows:
   g=reduce(gcd,(abs(z) for z in a),0)
   if g>1:a=[z//g for z in a];w=[z/g for z in w]
   if not any(a[1:]):
    if a[0]>0:return None,w
    continue
   unique.setdefault(tuple(a),(a,w))
  return list(unique.values()),None
 while True:
  rows,conflict=compact(rows)
  if conflict is not None:
   den=lcm(*(w.denominator for w in conflict));weights=[int(w*den) for w in conflict]
   sums=[sum(w*r[j] for w,r in zip(weights,original)) for j in range(n+1)]
   assert all(w>=0 for w in weights) and sums[0]>0 and not any(sums[1:])
   return 'UNSAT',{'kind':'nonnegative_combination','weights':weights}
  if not active:break
  j=min(active,key=lambda v:sum(a[v]>0 for a,w in rows)*sum(a[v]<0 for a,w in rows));active.remove(j)
  layers.append((j,[a for a,w in rows]));pos=[(a,w) for a,w in rows if a[j]>0];neg=[(a,w) for a,w in rows if a[j]<0]
  if len(pos)*len(neg)>20000:raise ValueError('independent verifier growth cap')
  new=[(a,w) for a,w in rows if not a[j]]
  for a,wa in pos:
   for b,wb in neg:
    u=-b[j];v=a[j];new.append(([u*x+v*y for x,y in zip(a,b)],[u*x+v*y for x,y in zip(wa,wb)]))
  rows=new
 x=[F(0)]*(n+1);x[0]=F(1)
 for j,rr in reversed(layers):
  lower=[];upper=[]
  for a in rr:
   if a[j]:
    bound=-sum(F(a[k])*x[k] for k in range(n+1) if k!=j)/a[j]
    (upper if a[j]>0 else lower).append(bound)
  lo=max(lower) if lower else None;hi=min(upper) if upper else None
  assert lo is None or hi is None or lo<=hi
  x[j]=max(F(0),lo) if lo is not None else min(F(0),hi) if hi is not None else F(0)
  if hi is not None:x[j]=min(x[j],hi)
 assert all(sum(F(a)*v for a,v in zip(row,x))<=0 for row in original)
 return 'FEASIBLE',{'kind':'witness','values':[str(v) for v in x[1:]]}
cases=[];by_hash={};errors=[]
for raw in sorted((source/'raw').glob('*/call-*.txt')):
 lines=raw.read_text().splitlines();m,n,*reserved=map(int,lines[0].split());rows=[];strict_count=0
 try:
  assert len(lines)==m+1
  for line in lines[1:]:
   strict,*a=map(int,line.split());assert len(a)==n+1
   for j,value in zip(reserved,[127,32767,2147483647,9223372036854775807]):
    if j!=-1:a[0]+=a[j]*value;a[j]=0
   if strict==0:rows.extend([a,[-v for v in a]])
   elif strict==-1:rows.append(a)
   elif strict==1:a[0]+=1;strict_count+=1;rows.append(a)
   else:raise ValueError(f'unsupported relation {strict}')
  columns=[j for j in range(1,n+1) if any(a[j] for a in rows)];matrix=[[a[0]]+[a[j] for j in columns] for a in rows];nn=len(columns)
  data=(f'{len(matrix)} {nn}\n'+'\n'.join(' '.join(map(str,a)) for a in matrix)+'\n').encode();sha=hashlib.sha256(data).hexdigest()
  origin={'raw':str(raw.relative_to(root)),'sha256':hashlib.sha256(raw.read_bytes()).hexdigest(),'original_variables':n,'column_map':columns,'reserved':reserved,'strict_integer_rows_shifted':strict_count}
  if sha in by_hash:by_hash[sha]['origins'].append(origin);continue
  answer,proof=certify(matrix,nn);name=f'qcp-call-{len(cases):03d}';f=out/'inputs'/(name+'.txt');f.write_bytes(data)
  c={'id':name,'family':'qcp-theory-call','rows':len(matrix),'variables':nn,'expected_q':answer,'proof':proof,'input_path':'inputs/'+f.name,'sha256':sha,'origins':[origin],'max_coefficient_bits':max((abs(z).bit_length() for a in matrix for z in a),default=0),'density':sum(z!=0 for a in matrix for z in a[1:])/(len(matrix)*nn) if matrix and nn else 0};cases.append(c);by_hash[sha]=c
 except Exception as e:errors.append({'raw':str(raw),'error':str(e)})
(out/'cases.json').write_text(json.dumps({'schema':1,'source_commit':'3098d53575ad2a99f9f561ec4e10233c98f44fd3','semantics':'rational relaxation of normalized integer LIA branch; equality split, strict integer row c<0 becomes c+1<=0, reserved constants substituted, unused columns removed','cases':cases,'excluded':errors},indent=2))
print('unique',len(cases),'captured',sum(len(c['origins']) for c in cases),'excluded',errors)
print('max variables',max(c['variables'] for c in cases),'max rows',max(c['rows'] for c in cases));print('answers',{q:sum(c['expected_q']==q for c in cases) for q in ['FEASIBLE','UNSAT']})
