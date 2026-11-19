import json,subprocess,re,os,time,statistics
from pathlib import Path
root=Path('/home/maxu/Projects/qcp-simplex-gmp-minimal');out=root/'evidence/combined2_20261112_142737';manifest=Path('/home/maxu/qcp-gmp-bench-20261109/cases.json')
cs={c['id']:c for c in json.loads(manifest.read_text())['cases']}
ids=['sparse-feas-n32-m128','sparse-unsat-n32-m128','dense-feas-n24-m96','dense-unsat-n16-m64','one-sided-n32-m128','one-sided-n16-m64-reversed','constant-unused-n32-m320','redundant-n16-m320','fraction-n64-m128','bounded-pairs-n48-m128']
vs=['baseline','one_sided','skip_zero','combined'];cpu=min(os.sched_getaffinity(0));records=[]
for name in ids:
 for rep in range(3):
  for v in vs[rep%len(vs):]+vs[:rep%len(vs)]:
   c=cs[name];p=subprocess.run(['taskset','-c',str(cpu),str(out/'bin'/v)],input=(manifest.parent/c['input_path']).read_bytes(),capture_output=True,timeout=600)
   assert p.returncode==0 and p.stdout.strip()==(b'0' if c['expected_q']=='FEASIBLE' else b'1')
   t=float(re.search(rb'kernel_seconds=([0-9.]+)',p.stderr)[1]);records.append(dict(id=name,variant=v,repeat=rep,cpu=cpu,kernel_seconds=t))
 (out/'serial_records.json').write_text(json.dumps(records,indent=2));print(name,{v:statistics.median(x['kernel_seconds'] for x in records if x['id']==name and x['variant']==v) for v in vs},flush=True)