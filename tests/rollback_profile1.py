"""Default: verify safe rollback. --apply: restore only two unchanged instrumented files."""
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parents[1];archive=root/'evidence/profile1_baseline'
before=json.loads((archive/'sha256.json').read_text());after=json.loads((archive/'instrumented_sha256.json').read_text())
for name,expected in after.items():
 assert hashlib.sha256((root/name).read_bytes()).hexdigest()==expected, 'Refuse rollback: later changes in '+name
 assert hashlib.sha256((archive/name).read_bytes()).hexdigest()==before[name], 'Baseline snapshot mismatch: '+name
if sys.argv[1:]==['--apply']:
 for name in after:(root/name).write_bytes((archive/name).read_bytes())
 print('Restored exact original solver.c and Makefile. Test artifacts and evidence retained.')
elif not sys.argv[1:]:print('Rollback checks passed; use --apply to restore. No files changed.')
else:raise SystemExit('usage: python3 tests/rollback_profile1.py [--apply]')
