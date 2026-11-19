import json,subprocess,time,os,signal,re,statistics
from pathlib import Path
root=Path(__file__).resolve().parents[1];base=root/'evidence/remainder1_20261112_170832';manifest=root/'evidence/remainder1_inputs/cases.json'
ids=['original52--sparse-feas-n32-m128','stress20--dense32-s20261112-unsat','seed48--mixed128-s31001-feas','seed48--interior32-s31003-feas','stress20--redundant32-s20261115-feas']
cases={c['id']:c for c in json.loads(manifest.read_text())['cases']};assert all(i in cases for i in ids)
out=base/'serial';out.mkdir(exist_ok=False);records=[];cpu=min(os.sched_getaffinity(0))
for i in ids:
 c=cases[i];data=(manifest.parent/c['input_path']).read_bytes()
 for repeat in range(3):
  for v in (['baseline','remainder'] if repeat%2==0 else ['remainder','baseline']):
   p=subprocess.Popen(['taskset','-c',str(cpu),str(base/'bin'/v)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
   try:
    stdout,stderr=p.communicate(data,timeout=400)
    assert p.returncode==0 and stdout.strip()==(b'0' if c['expected_q']=='FEASIBLE' else b'1')
    seconds=float(re.search(rb'kernel_seconds=([0-9.]+)',stderr)[1]);status='PASS'
   except subprocess.TimeoutExpired:
    os.killpg(p.pid,signal.SIGKILL);p.communicate();seconds=None;status='TIMEOUT'
   records.append(dict(id=i,variant=v,repeat=repeat,cpu=cpu,status=status,kernel_seconds=seconds))
   (out/'results.json').write_text(json.dumps(records,indent=2));print(i,v,repeat,seconds,flush=True)
