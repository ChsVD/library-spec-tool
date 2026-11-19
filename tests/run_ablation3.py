import concurrent.futures as cf
import hashlib,json,subprocess,time,os,queue,re
from pathlib import Path
root=Path(__file__).resolve().parents[1]
manifest=Path('/home/maxu/qcp-gmp-bench-20261109/cases.json')
cases=json.loads(manifest.read_text())['cases']
variants={'baseline':'build/one1-skip1-nb0-simple0-san0/bench_driver','nonbasic':'build/one1-skip1-nb1-simple0-san0/bench_driver','simple_arith':'build/one1-skip1-nb0-simple1-san0/bench_driver'}
out=root/'evidence'/('ablation3_'+time.strftime('%Y%m%d_%H%M%S'))
out.mkdir();(out/'bin').mkdir()
import shutil
for v,path in variants.items(): shutil.copy2(root/path,out/'bin'/v)
cpus=sorted(os.sched_getaffinity(0))[::2][:3]
slots=queue.Queue()
for c in cpus: slots.put(c)
config={'case_count':len(cases),'variants':variants,'limit_seconds':400,'workers':len(cpus),'cpus':cpus,'cases_sha256':hashlib.sha256(manifest.read_bytes()).hexdigest(),'binary_hashes':{v:hashlib.sha256((out/'bin'/v).read_bytes()).hexdigest() for v in variants},'ordering':'descending rows*variables, rotate variant order by case','timing':'kernel monotonic duration, independent process wall deadline; one sample per variant/case'}
(out/'config.json').write_text(json.dumps(config,indent=2))
(out/'source_hashes.json').write_text(json.dumps({str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for d in ['src','include','tests'] for p in (root/d).glob('*') if p.is_file()},indent=2))
print('OUTPUT',out,flush=True)
def run(c,v):
 cpu=slots.get(); data=(manifest.parent/c['input_path']).read_bytes()
 assert hashlib.sha256(data).hexdigest()==c['sha256']
 start=time.monotonic()
 try:
  p=subprocess.run(['taskset','-c',str(cpu),str(out/'bin'/v)],input=data,capture_output=True,timeout=400)
  stdout,stderr=p.stdout.decode(),p.stderr.decode();code=p.returncode
  status='ERROR'
  if code==0 and stdout.strip() in ('0','1'):
   status='PASS' if stdout.strip()==('0' if c['expected_q']=='FEASIBLE' else '1') else 'MISMATCH'
 except subprocess.TimeoutExpired as e:
  stdout=(e.stdout or b'').decode();stderr=(e.stderr or b'').decode();code=None;status='TIMEOUT'
 finally: slots.put(cpu)
 k=re.search(r'kernel_seconds=([0-9.]+)',stderr)
 rec={**{key:c[key] for key in ['id','rows','variables','expected_q','sha256']},'variant':v,'cpu':cpu,'status':status,'returncode':code,'stdout':stdout,'stderr':stderr,'wall_seconds':time.monotonic()-start,'kernel_seconds':float(k[1]) if k else None}
 (out/(c['id']+'--'+v+'.json')).write_text(json.dumps(rec,indent=2));return rec
jobs=[]
for i,c in enumerate(sorted(cases,key=lambda c:-c['rows']*c['variables'])):
 vs=list(variants);vs=vs[i%3:]+vs[:i%3]
 jobs.extend((c,v) for v in vs)
records=[]
with cf.ThreadPoolExecutor(max_workers=len(cpus)) as pool:
 for f in cf.as_completed([pool.submit(run,c,v) for c,v in jobs]):
  x=f.result();records.append(x);(out/'results.json').write_text(json.dumps(records,indent=2));print(len(records),x['variant'],x['id'],x['status'],round(x['wall_seconds'],3),flush=True)
summary={v:{s:sum(x['variant']==v and x['status']==s for x in records) for s in ['PASS','TIMEOUT','MISMATCH','ERROR']} for v in variants}
(out/'summary.json').write_text(json.dumps(summary,indent=2));print(summary,flush=True)