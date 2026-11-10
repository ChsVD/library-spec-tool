"""Run after clean ordinary build. Compare current P4 preprocess on/off, not P3."""
import argparse,subprocess,json,hashlib,platform
from pathlib import Path
parser=argparse.ArgumentParser();parser.add_argument('--repeats',type=int,default=30);parser.add_argument('--output',type=Path,default=Path('build/p4_benchmark_latest.json'));args=parser.parse_args()
assert args.repeats>0
rows=[]
for case in ['dense','sparse']:
 for flags in ['15','0']:
  p=subprocess.run(['./build/bench_preprocess',case,flags,str(args.repeats)],text=True,capture_output=True,check=True)
  rows.append(json.loads(p.stdout))
result={'comparison':'Current P4 preprocessing flags 0 versus 15; common counters and zero verification skip in both paths',
 'clock':'CLOCK_MONOTONIC, nanoseconds; one untimed warmup; no CPU affinity pinning',
 'timing_scope':'Only sx_check_qcp call, including input validation/preprocessing, table build/check/pivots, original witness verification, internal cleanup and output construction; excludes input creation, result init/clear, JSON/process setup',
 'matrix_statistics':'Additional untimed call with collect_matrix_stats=1; timed calls use 0. All other limits/settings identical',
 'compiler':subprocess.check_output(['cc','--version'],text=True).splitlines()[0],
 'flags':'-std=c11 -O2 -g (Makefile ordinary default; clean build required)',
 'platform':platform.platform(),
 'binary_sha256':hashlib.sha256(Path('build/bench_preprocess').read_bytes()).hexdigest(),
 'library_sha256':hashlib.sha256(Path('build/libsx_solver.a').read_bytes()).hexdigest(),
 'results':rows}
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(json.dumps(result,indent=2)+'\n')
print('measurement output:',args.output)
for r in rows:print(r['case'],r['entry'],'mask',r['disable_opts'],'median_ns',r['median_ns'],'peak',r['peak_bytes'],'allocations',r['allocations'])
