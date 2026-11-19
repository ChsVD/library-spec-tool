from pathlib import Path
from fractions import Fraction
import argparse,concurrent.futures as cf,hashlib,json,os,queue,re,signal,shutil,subprocess,time
ap=argparse.ArgumentParser();ap.add_argument('--phase',choices=['normal','profile'],required=True);ap.add_argument('--stage',choices=['screen','hard'],default='screen');ap.add_argument('--out');args=ap.parse_args()
root=Path(__file__).resolve().parents[1];manifest=root/'evidence/order1_inputs/cases.json';doc=json.loads(manifest.read_text());cases=doc['cases']
out=Path(args.out) if args.out else root/'evidence'/('order1_'+time.strftime('%Y%m%d_%H%M%S'));out.mkdir(exist_ok=True);(out/'bin').mkdir(exist_ok=True)
if args.stage=='screen':cases=[c for c in cases if c['group']!='hard']
else:
 selected=json.loads((out/'selection.json').read_text())['selected_order'];cases=[c for c in cases if c['group']=='hard' and c['order'] in ['identity',selected]]
run=out/(args.stage+'_'+args.phase);run.mkdir(exist_ok=False)
if not (out/'config.json').exists():
 bins={'normal':'build/one1-skip1-nb1-simple1-san0/bench_driver','profile':'build/one1-skip1-nb1-simple1-san0-profile1/bench_driver'}
 for name,path in bins.items():shutil.copy2(root/path,out/'bin'/name)
 (out/'config.json').write_text(json.dumps({'manifest':str(manifest),'manifest_sha256':hashlib.sha256(manifest.read_bytes()).hexdigest(),'timeout_seconds':400,'binaries':bins,'binary_sha256':{name:hashlib.sha256((out/'bin'/name).read_bytes()).hexdigest() for name in bins},'production_sha256':{str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for folder in ['src','include'] for p in (root/folder).iterdir() if p.is_file()},'selection_rule':doc['selection'],'ordering_time':'excluded from kernel timings; offline Python permutations, not a production implementation','deduplication':'identical payload within one base case measured once per phase and aliased; never counted as independent measurements'},indent=2))
# Reparse every saved input and check permutation provenance and proof before executing.
source_cache={}
for c in cases:
 data=(manifest.parent/c['input_path']).read_bytes();assert hashlib.sha256(data).hexdigest()==c['sha256']
 tokens=list(map(int,data.split()));m,n=tokens[:2];assert len(tokens)==2+m*(n+1)
 a=[tokens[2+i*(n+1):2+(i+1)*(n+1)] for i in range(m)];proof=c['proof']
 if c['base_id'] not in source_cache:
  sm=Path(c['source_manifest']);sc=next(x for x in json.loads(sm.read_text())['cases'] if x['id']==c['base_id']);raw=(sm.parent/sc['input_path']).read_bytes();assert hashlib.sha256(raw).hexdigest()==c['source_sha256'];z=list(map(int,raw.split()));source_cache[c['base_id']]=[z[2+i*(n+1):2+(i+1)*(n+1)] for i in range(m)]
 original=source_cache[c['base_id']];rp=c['row_map'];cp=c['column_map'];assert sorted(rp)==list(range(m)) and sorted(cp)==list(range(n));assert a==[[original[i][0]]+[original[i][j+1] for j in cp] for i in rp]
 if proof['kind']=='witness':
  x=[Fraction(v) for v in proof['values']];assert len(x)==n and all(Fraction(r[0])+sum(v*y for v,y in zip(r[1:],x))<=0 for r in a)
 else:
  w=proof['weights'];assert len(w)==m and all(v>=0 for v in w);s=[sum(v*r[j] for v,r in zip(w,a)) for j in range(n+1)];assert s[0]>0 and not any(s[1:])
cpus=sorted(os.sched_getaffinity(0))[::2][:4];slots=queue.Queue()
for cpu in cpus:slots.put(cpu)
# Rotate order per base input. Exact duplicates share one execution.
base_ids=list(dict.fromkeys(c['base_id'] for c in cases));groups={};jobs=[]
for i,base in enumerate(base_ids):
 cc=[c for c in cases if c['base_id']==base];rot=i%len(cc);cc=cc[rot:]+cc[:rot]
 for c in cc:
  key=(base,c['sha256'])
  if key not in groups:groups[key]=[];jobs.append(c)
  groups[key].append(c)
(run/'config.json').write_text(json.dumps({'phase':args.phase,'stage':args.stage,'logical_records':len(cases),'unique_executions':len(jobs),'cpus':cpus,'workers':len(cpus)},indent=2));print('OUTPUT',out,'RUN',run.name,'UNIQUE',len(jobs),flush=True)
def work(c):
 cpu=slots.get();start=time.monotonic();data=(manifest.parent/c['input_path']).read_bytes()
 try:
  proc=subprocess.Popen(['/usr/bin/time','-f','peak_rss_kb=%M','taskset','-c',str(cpu),str(out/'bin'/args.phase)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
  try:
   stdout,stderr=proc.communicate(data,timeout=400);code=proc.returncode
   status='PASS' if code==0 and stdout.strip()==(b'0' if c['expected_q']=='FEASIBLE' else b'1') else ('MISMATCH' if code==0 and stdout.strip() in [b'0',b'1'] else 'ERROR')
  except subprocess.TimeoutExpired:
   os.killpg(proc.pid,signal.SIGKILL);stdout,stderr=proc.communicate();code=proc.returncode;status='TIMEOUT'
 finally:slots.put(cpu)
 stderr=stderr.decode();match=re.search(r'kernel_seconds=([0-9.]+)',stderr);rss=re.search(r'peak_rss_kb=(\d+)',stderr)
 trace=[json.loads(line[11:]) for line in stderr.splitlines() if line.startswith('sx_profile=')]
 result={k:c[k] for k in ['id','base_id','family','group','split','order','rows','variables','expected_q','sha256']};result.update(status=status,returncode=code,cpu=cpu,wall_seconds=time.monotonic()-start,kernel_seconds=float(match[1]) if match else None,peak_rss_kb=int(rss[1]) if rss else None,profile=trace[-1] if trace else None,stdout=stdout.decode(),stderr=stderr,measured_id=c['id'])
 (run/(c['id']+'.json')).write_text(json.dumps(result,indent=2));return result
records=[]
with cf.ThreadPoolExecutor(max_workers=len(cpus)) as pool:
 for future in cf.as_completed([pool.submit(work,c) for c in jobs]):
  x=future.result()
  for c in groups[x['base_id'],x['sha256']]:
   alias=dict(x,id=c['id'],order=c['order']);records.append(alias)
  (run/'results.json').write_text(json.dumps(records,indent=2))
  print(len(records),'/',len(cases),x['id'],x['status'],round(x['wall_seconds'],3),flush=True)
summary={order:{s:sum(x['order']==order and x['status']==s for x in records) for s in ['PASS','TIMEOUT','MISMATCH','ERROR']} for order in dict.fromkeys(c['order'] for c in cases)}
(run/'summary.json').write_text(json.dumps(summary,indent=2));print('SUMMARY',summary,flush=True)
