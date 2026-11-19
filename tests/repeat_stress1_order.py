from pathlib import Path
import json,subprocess,re,os,statistics,hashlib
root=Path(__file__).resolve().parents[1];out=root/'evidence/stress1_20261112_152410';mp=root/'evidence/stress1_inputs/cases.json';cs={c['id']:c for c in json.loads(mp.read_text())['cases']}
names=['dense32-s20261112-unsat','dense32-s20261112-unsat-permuted'];jobs=[(name,v) for name in names for v in ['baseline','combined']];cpu=min(os.sched_getaffinity(0));records=[]
for rep in range(3):
 for name,v in jobs[rep:]+jobs[:rep]:
  c=cs[name];data=(mp.parent/c['input_path']).read_bytes();assert hashlib.sha256(data).hexdigest()==c['sha256']
  p=subprocess.run(['taskset','-c',str(cpu),str(out/'bin'/v)],input=data,capture_output=True,timeout=400)
  assert p.returncode==0 and p.stdout.strip()==b'1'
  sec=float(re.search(rb'kernel_seconds=([0-9.]+)',p.stderr)[1]);records.append(dict(id=name,variant=v,repeat=rep,cpu=cpu,kernel_seconds=sec))
  (out/'order_serial_records.json').write_text(json.dumps(records,indent=2))
 print('repeat',rep,'complete',flush=True)
for name,v in jobs:print(name,v,statistics.median(x['kernel_seconds'] for x in records if x['id']==name and x['variant']==v),flush=True)
