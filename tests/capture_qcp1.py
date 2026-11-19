from pathlib import Path
import subprocess,json,os,hashlib
root=Path(__file__).resolve().parents[1];out=root/'evidence/qcp_capture1';build=out/'build'
listing=json.loads(subprocess.check_output(['ctest','--show-only=json-v1'],cwd=build))
records=[]
for t in listing['tests']:
 if not t['name'].startswith('smt.solve.'):continue
 d=out/'raw'/t['name'];d.mkdir(parents=True,exist_ok=True)
 env=dict(os.environ,SX_CAPTURE_DIR=str(d));cmd=t['command'];proc=subprocess.run(cmd,env=env,capture_output=True,timeout=60)
 (d/'stdout.log').write_bytes(proc.stdout);(d/'stderr.log').write_bytes(proc.stderr)
 record={'test':t['name'],'command':cmd,'returncode':proc.returncode,'input_sha256':hashlib.sha256(Path(cmd[1]).read_bytes()).hexdigest(),'calls':len(list(d.glob('call-*.txt')))};records.append(record)
 print(t['name'],record['calls'],proc.returncode,flush=True)
(out/'capture_results.json').write_text(json.dumps(records,indent=2));print('TOTAL',len(records),'calls',sum(x['calls'] for x in records))
