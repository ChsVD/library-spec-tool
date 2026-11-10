"""Self-contained verifier regression, including optimized Python modes."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parents[1]
def require(condition,message):
    if not condition:raise RuntimeError(message)
def main():
    (ROOT/'build').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='p5-verifier-',dir=ROOT/'build') as temp:
        root=Path(temp);(root/'tools').mkdir();shutil.copyfile(ROOT/'tools/verify_release.py',root/'tools/verify_release.py')
        sample=b'original\n';(root/'README.md').write_bytes(sample)
        (root/'RELEASE_MANIFEST.json').write_text(json.dumps({'schema':1,'files':{'README.md':{'bytes':len(sample),'sha256':hashlib.sha256(sample).hexdigest()}}}))
        for bad in [False,True]:
            if bad:(root/'README.md').write_text('tampered\n')
            for options,optimized in [([],False),(['-O'],False),([],True)]:
                env=os.environ.copy()
                if optimized:env['PYTHONOPTIMIZE']='1'
                p=subprocess.run([sys.executable,*options,str(root/'tools/verify_release.py')],capture_output=True,text=True,env=env)
                require((p.returncode!=0)==bad,f'wrong verifier status: {options}, env-opt={optimized}, tampered={bad}')
                require(('Verified' in p.stdout)!=bad,'misleading success output')
    print('Release verifier: normal/-O/PYTHONOPTIMIZE accept original and reject tampering')
if __name__=='__main__':main()
