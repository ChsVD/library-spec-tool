from pathlib import Path
import hashlib,json,subprocess
root=Path(__file__).resolve().parents[1]
m=json.loads((root/'BASELINE_MANIFEST.json').read_text())
for name,info in m['files'].items():
 p=Path(name)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==info['sha256'],name
 v=root/'vendor/gmp/minigmp'/p.name
 if p.name=='mpz_make_odd.c':v=root/'docs/mpz_make_odd.c.original'
 assert hashlib.sha256(v.read_bytes()).hexdigest()==info['sha256'],str(v)
assert subprocess.check_output(['git','-C',m['repository'],'rev-parse','HEAD'],text=True).strip()==m['commit']
assert subprocess.check_output(['git','-C',m['repository'],'status','--porcelain=v1','--untracked-files=all'],text=True)==m['status']
print(f"Baseline unchanged: {len(m['files'])} files; frozen commit and complete local git status match")
