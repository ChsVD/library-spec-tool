from pathlib import Path
import json,math,hashlib,subprocess,os,statistics,csv,shutil
root=Path(__file__).resolve().parents[1];out=root/'evidence/profile2_20261112_164317';records=json.loads((out/'results.json').read_text());assert len(records)==7
samples={};total=0
for record in records:
 a=record['profile'];assert sum(x[0] for x in a['phase_calls'])==a['calls'][0] and sum(x[1] for x in a['phase_calls'])==a['calls'][2]
 assert math.isclose(sum(x[0] for x in a['phase_seconds']),a['seconds'][0],abs_tol=1e-6) and math.isclose(sum(x[1] for x in a['phase_seconds']),a['seconds'][2],abs_tol=1e-6)
 if record['status']=='PASS':assert a['phase_calls'][1][1]==2*a['phase_calls'][1][0]
 for line in record['stderr'].splitlines():
  if not line.startswith('sx_operand='):continue
  x=json.loads(line[11:]);aa=int(x['a'],0);bb=int(x['b'],0);rr=int(x['result'],0);total+=1
  if x['operation']==0:assert aa>0 and rr==math.gcd(aa,bb);kind='kept' if rr==aa else 'one' if rr==1 else 'other'
  else:assert bb!=0 and aa%bb==0 and rr==aa//bb;kind='den_one' if abs(bb)==1 else 'quotient_one' if abs(rr)==1 else 'other'
  x.update(source_case=record['id'],kind=kind);key=(x['phase'],x['operation'],aa,bb);samples.setdefault(key,x)
groups={}
for key,x in samples.items():groups.setdefault((x['phase'],x['operation'],x['bucket'],x['kind']),[]).append(x)
chosen=[]
for group,xs in sorted(groups.items()):
 xs.sort(key=lambda x:hashlib.sha256((x['a']+':'+x['b']).encode()).hexdigest());chosen.extend(xs[:4])
for op,aa,bb in [(0,9,-18),(0,12,-18),(1,0,17),(1,4097,1),(1,-4097,1),(1,17,-17),(1,-17,17)]:
 chosen.append(dict(phase=-1,operation=op,bucket=-1,a=hex(aa),b=hex(bb),result=hex(math.gcd(aa,bb) if op==0 else aa//bb),kind='control',source_case='synthetic-boundary-control'))
for i,x in enumerate(chosen):x['sample_id']=i
(out/'micro_samples.json').write_text(json.dumps({'captured':total,'unique':len(samples),'chosen':chosen,'selection':'up to4 SHA-ordered unique actual operand pairs per phase/op/bit-bucket/outcome, plus7 correctness controls; not frequency weighted'},indent=2))
data=(str(len(chosen))+'\n'+'\n'.join(f"{x['sample_id']} {x['operation']} {x['a']} {x['b']} {x['result']}" for x in chosen)+'\n').encode();(out/'micro_input.txt').write_bytes(data)
shutil.copy2(root/'build/arith_micro2',out/'bin/arith_micro2');cpu=min(os.sched_getaffinity(0));p=subprocess.run(['taskset','-c',str(cpu),str(out/'bin/arith_micro2')],input=data,capture_output=True,timeout=400);(out/'micro_stdout.txt').write_bytes(p.stdout);(out/'micro_stderr.txt').write_bytes(p.stderr);assert p.returncode==0
raw=[]
for line in p.stdout.decode().splitlines():
 sid,mode,rep,loops,seconds=line.split();raw.append(dict(sample_id=int(sid),mode=int(mode),repeat=int(rep),loops=int(loops),seconds=float(seconds),per_call=float(seconds)/int(loops)))
assert len(raw)==len(chosen)*10
results=[]
for sample in chosen:
 med={mode:statistics.median(x['per_call'] for x in raw if x['sample_id']==sample['sample_id'] and x['mode']==mode) for mode in [0,1]}
 results.append({**sample,'native_seconds':med[0],'candidate_seconds':med[1],'speedup':med[0]/med[1]})
(out/'micro_results.json').write_text(json.dumps(results,indent=2));(out/'micro_raw.json').write_text(json.dumps(raw,indent=2));(out/'micro_config.json').write_text(json.dumps({'cpu':cpu,'repeats':5,'loops':'adaptive using native batch >=3ms, then same iterations for both modes; mode order alternates','binary_sha256':hashlib.sha256((out/'bin/arith_micro2').read_bytes()).hexdigest(),'input_sha256':hashlib.sha256(data).hexdigest(),'timeout_seconds':400},indent=2))
print('Captured',total,'unique',len(samples),'selected',len(chosen),'all exact results and immutable operands verified')
for phase in [0,1]:
 for op in [0,1]:
  for kind in sorted({x['kind'] for x in results if x['phase']==phase and x['operation']==op}):
   ss=[x['speedup'] for x in results if x['phase']==phase and x['operation']==op and x['kind']==kind];print('phase',phase,'op',op,kind,'n',len(ss),'median speedup',round(statistics.median(ss),3),'min',round(min(ss),3),'max',round(max(ss),3))
