import concurrent.futures as cf
import hashlib,json,subprocess,time,os
from pathlib import Path
root=Path(__file__).resolve().parents[1]
manifest=Path('/home/maxu/qcp-gmp-bench-20261109/cases.json')
cases=json.loads(manifest.read_text())['cases']
assert len(cases)==52
out=root/'evidence'/('p5_600s_'+time.strftime('%Y%m%d_%H%M%S'))
out.mkdir()
config={'cases_sha256':hashlib.sha256(manifest.read_bytes()).hexdigest(),'timeout_seconds_per_case':600,'parallel_workers':4,'driver_sha256':hashlib.sha256((root/'build/bench_driver').read_bytes()).hexdigest(),'timing':'wall includes loading and test input preservation; kernel_seconds covers sx_check_qcp only','no_solver_budget':True}
(out/'config.json').write_text(json.dumps(config,indent=2))
print('OUTPUT',out,flush=True)
def run(c):
    data=(manifest.parent/c['input_path']).read_bytes()
    assert hashlib.sha256(data).hexdigest()==c['sha256']
    started=time.monotonic()
    try:
        p=subprocess.run([str(root/'build/bench_driver')],input=data,capture_output=True,timeout=600)
        stdout,stderr=p.stdout.decode(),p.stderr.decode()
        status='ERROR'
        if p.returncode==0 and stdout.strip() in ('0','1'):
            want='0' if c['expected_q']=='FEASIBLE' else '1'
            status='PASS' if stdout.strip()==want else 'MISMATCH'
        code=p.returncode
    except subprocess.TimeoutExpired as e:
        status='TIMEOUT';code=None
        stdout=(e.stdout or b'').decode();stderr=(e.stderr or b'').decode()
    rec={**{k:c[k] for k in ('id','family','rows','variables','expected_q','sha256')},'status':status,'returncode':code,'stdout':stdout,'stderr':stderr,'wall_seconds':time.monotonic()-started}
    (out/(c['id']+'.json')).write_text(json.dumps(rec,indent=2))
    return rec
records=[]
with cf.ThreadPoolExecutor(max_workers=4) as pool:
    for f in cf.as_completed([pool.submit(run,c) for c in sorted(cases,key=lambda c:c['rows']*c['variables'])]):
        rec=f.result();records.append(rec)
        (out/'results.json').write_text(json.dumps(records,indent=2))
        print(len(records),rec['id'],rec['status'],round(rec['wall_seconds'],3),flush=True)
counts={s:sum(r['status']==s for r in records) for s in ('PASS','TIMEOUT','MISMATCH','ERROR')}
(out/'summary.json').write_text(json.dumps(counts,indent=2));print('SUMMARY',counts,flush=True)