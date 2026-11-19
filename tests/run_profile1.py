import concurrent.futures as cf
import hashlib,json,subprocess,time,os,queue,re,signal,shutil
from fractions import Fraction
from pathlib import Path
root=Path(__file__).resolve().parents[1];manifest=root/'evidence/stress1_inputs/cases.json'
cases=json.loads(manifest.read_text())['cases']
selected=['sparse128-s20261114-feas','sparse128-s20261114-unsat','mixed256-s20261113-feas','circuit48-s20261117-feas','redundant32-s20261115-feas','dense32-s20261112-unsat','dense32-s20261112-unsat-permuted']
cases=sorted((c for c in cases if c['id'] in selected),key=lambda c:selected.index(c['id']))
# Independently parse saved bytes and verify certificates before any solver runs.
for c in cases:
 data=(manifest.parent/c['input_path']).read_bytes();assert hashlib.sha256(data).hexdigest()==c['sha256']
 tokens=list(map(int,data.split()));m,n=tokens[:2];assert (m,n)==(c['rows'],c['variables']) and len(tokens)==2+m*(n+1)
 rows=[tokens[2+i*(n+1):2+(i+1)*(n+1)] for i in range(m)];proof=c['proof']
 if proof['kind']=='witness':
  x=[Fraction(v) for v in proof['values']];assert len(x)==n
  assert all(Fraction(row[0])+sum(a*v for a,v in zip(row[1:],x))<=0 for row in rows)
 else:
  w=proof['weights'];assert len(w)==m and all(isinstance(v,int) and v>=0 for v in w)
  sums=[sum(v*row[j] for v,row in zip(w,rows)) for j in range(n+1)]
  assert sums[0]>0 and all(v==0 for v in sums[1:])
variants={'baseline':'build/one1-skip1-nb0-simple0-san0-profile1/bench_driver','combined':'build/one1-skip1-nb1-simple1-san0-profile1/bench_driver'}
out=root/'evidence'/('profile1_'+time.strftime('%Y%m%d_%H%M%S'));out.mkdir();(out/'bin').mkdir()
for v,path in variants.items():shutil.copy2(root/path,out/'bin'/v)
cpus=sorted(os.sched_getaffinity(0))[::2][:4];slots=queue.Queue()
for cpu in cpus:slots.put(cpu)
config={'cases':len(cases),'variants':variants,'limit_seconds':400,'cpus':cpus,'workers':len(cpus),'manifest':str(manifest),'manifest_sha256':hashlib.sha256(manifest.read_bytes()).hexdigest(),'binary_sha256':{v:hashlib.sha256((out/'bin'/v).read_bytes()).hexdigest() for v in variants},'certificate_verification':'all saved inputs independently parsed and verified before execution','measurement':'kernel monotonic time, process-tree wall timeout, GNU time peak RSS includes parsing and input preservation'}
(out/'config.json').write_text(json.dumps(config,indent=2))
(out/'source_hashes.json').write_text(json.dumps({str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for d in ['src','include','tests'] for p in (root/d).iterdir() if p.is_file()},indent=2))
print('OUTPUT',out,flush=True)
def run(c,v):
 cpu=slots.get();data=(manifest.parent/c['input_path']).read_bytes();start=time.monotonic()
 try:
  proc=subprocess.Popen(['/usr/bin/time','-f','peak_rss_kb=%M user_seconds=%U system_seconds=%S','taskset','-c',str(cpu),str(out/'bin'/v)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
  try:
   stdout,stderr=proc.communicate(data,timeout=400);code=proc.returncode
   status='PASS' if code==0 and stdout.strip()==(b'0' if c['expected_q']=='FEASIBLE' else b'1') else ('MISMATCH' if code==0 and stdout.strip() in [b'0',b'1'] else 'ERROR')
  except subprocess.TimeoutExpired:
   os.killpg(proc.pid,signal.SIGKILL);stdout,stderr=proc.communicate();code=proc.returncode;status='TIMEOUT'
 finally:slots.put(cpu)
 stderr=stderr.decode();k=re.search(r'kernel_seconds=([0-9.]+)',stderr);rss=re.search(r'peak_rss_kb=(\d+)',stderr)
 rec={**{k:c[k] for k in ['id','family','rows','variables','expected_q','sha256','max_coefficient_bits','density']},'variant':v,'cpu':cpu,'status':status,'returncode':code,'stdout':stdout.decode(),'stderr':stderr,'wall_seconds':time.monotonic()-start,'kernel_seconds':float(k[1]) if k else None,'peak_rss_kb':int(rss[1]) if rss else None}
 profiles=[json.loads(line[len('sx_profile='):]) for line in stderr.splitlines() if line.startswith('sx_profile=')]
 rec['profile']=profiles[-1] if profiles else None
 rec['profile_records']=len(profiles)
 (out/(c['id']+'--'+v+'.json')).write_text(json.dumps(rec,indent=2));return rec
jobs=[]
for i,c in enumerate(cases):
 vs=list(variants);vs=vs[i%2:]+vs[:i%2];jobs.extend((c,v) for v in vs)
records=[]
with cf.ThreadPoolExecutor(max_workers=len(cpus)) as pool:
 for f in cf.as_completed([pool.submit(run,c,v) for c,v in jobs]):
  x=f.result();records.append(x);(out/'results.json').write_text(json.dumps(records,indent=2));print(len(records),x['variant'],x['id'],x['status'],round(x['wall_seconds'],3),flush=True)
summary={v:{s:sum(x['variant']==v and x['status']==s for x in records) for s in ['PASS','TIMEOUT','MISMATCH','ERROR']} for v in variants}
(out/'summary.json').write_text(json.dumps(summary,indent=2));print(summary,flush=True)
