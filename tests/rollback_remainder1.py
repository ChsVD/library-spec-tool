from pathlib import Path
import argparse,json,hashlib
ap=argparse.ArgumentParser();ap.add_argument('--apply',action='store_true');args=ap.parse_args()
root=Path(__file__).resolve().parents[1];archive=root/'evidence/remainder1_baseline'
before=json.loads((archive/'sha256.json').read_text());after=json.loads((archive/'current_sha256.json').read_text());restore={}
for name,h in after.items():
 if hashlib.sha256((root/name).read_bytes()).hexdigest()!=h: raise SystemExit('Refuse later change: '+name)
 data=(archive/name).read_bytes()
 if hashlib.sha256(data).hexdigest()!=before[name]: raise SystemExit('Bad snapshot: '+name)
 restore[name]=data
if args.apply:
 for name,data in restore.items():(root/name).write_bytes(data)
 print('Restored pre-remainder profile2 state; experiment artifacts retained.')
else: print('Rollback checks passed; no changes. --apply restores pre-remainder profile2 state.')
