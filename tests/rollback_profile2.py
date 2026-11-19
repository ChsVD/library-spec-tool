from pathlib import Path
import argparse,json,hashlib
ap=argparse.ArgumentParser();ap.add_argument('--apply',action='store_true');ap.add_argument('--all',action='store_true');args=ap.parse_args()
root=Path(__file__).resolve().parents[1];archive=root/'evidence/profile2_baseline';before=json.loads((archive/'sha256.json').read_text());after=json.loads((archive/'instrumented_sha256.json').read_text());restore={}
for name,h in after.items():
 assert hashlib.sha256((root/name).read_bytes()).hexdigest()==h,'Refuse later change: '+name
 assert hashlib.sha256((archive/name).read_bytes()).hexdigest()==before[name],'Bad snapshot: '+name
 restore[name]=(archive/name).read_bytes()
if args.all:
 original=root/'evidence/profile1_baseline';hashes=json.loads((original/'sha256.json').read_text())
 for name in ['src/solver.c','Makefile']:
  data=(original/name).read_bytes();assert hashlib.sha256(data).hexdigest()==hashes[name];restore[name]=data
if args.apply:
 for name,data in restore.items():(root/name).write_bytes(data)
 print('Restored original production files' if args.all else 'Restored profile1 instrumentation state')
else:print('Rollback checks passed; no changes. --apply restores profile1; --apply --all restores original production source/Makefile.')
