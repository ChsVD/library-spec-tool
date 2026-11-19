from pathlib import Path
import json,subprocess,re,os,statistics,hashlib,signal
root=Path(__file__).resolve().parents[1];out=root/'evidence/order1_20261112_161356';manifest=root/'evidence/order1_inputs/cases.json';cases={(c['base_id'],c['order']):c for c in json.loads(manifest.read_text())['cases']}
r=json.loads((out/'screen_normal/results.json').read_text());by={(x['base_id'],x['order']):x for x in r};selected=json.loads((out/'selection.json').read_text())['selected_order'];ids=sorted({x['base_id'] for x in r if x['split']=='holdout'},key=lambda n:by[n,selected]['kernel_seconds']/by[n,'identity']['kernel_seconds']);ids=[ids[0],ids[-1]]
(out/'serial_design.json').write_text(json.dumps({'cases':ids,'selected_order':selected,'selection':'post-hoc best and worst heldout cases, explanatory only; not a new performance-selection sample','repeats':3,'cpu':min(os.sched_getaffinity(0)),'limit_seconds':400},indent=2))
records=[];cpu=min(os.sched_getaffinity(0))
for name in ids:
 for rep in range(3):
  orders=['identity',selected];orders=orders[rep%2:]+orders[:rep%2]
  for order in orders:
   c=cases[name,order];data=(manifest.parent/c['input_path']).read_bytes();assert hashlib.sha256(data).hexdigest()==c['sha256']
   proc=subprocess.Popen(['taskset','-c',str(cpu),str(out/'bin/normal')],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
   try:stdout,stderr=proc.communicate(data,timeout=400)
   except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.communicate();raise
   assert proc.returncode==0 and stdout.strip()==(b'0' if c['expected_q']=='FEASIBLE' else b'1')
   sec=float(re.search(rb'kernel_seconds=([0-9.]+)',stderr)[1]);records.append({'base_id':name,'order':order,'repeat':rep,'cpu':cpu,'kernel_seconds':sec})
   (out/'serial_results.json').write_text(json.dumps(records,indent=2))
 print(name,{order:statistics.median(x['kernel_seconds'] for x in records if x['base_id']==name and x['order']==order) for order in ['identity',selected]},flush=True)
