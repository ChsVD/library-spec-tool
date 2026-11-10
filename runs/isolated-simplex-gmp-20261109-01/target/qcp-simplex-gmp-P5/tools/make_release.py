"""Build a deterministic source-only archive; never include build or releases."""
from pathlib import Path
import argparse,gzip,hashlib,io,json,tarfile
ROOT=Path(__file__).resolve().parents[1]
DIRS=('include','src','vendor','tests','docs','examples','tools')
ROOT_FILES=('README.md','Makefile','DEVELOPMENT_PLAN.md','INT_YICES_COMPARISON.md','REVIEW_CHECKLIST.md','.clang-format')
PREFIX='qcp-simplex-gmp-P5'

def sources():
    found={ROOT/n for n in ROOT_FILES if (ROOT/n).is_file()}
    found.update(p for p in ROOT.glob('*.json') if p.name!='RELEASE_MANIFEST.json')
    for name in DIRS:
        for p in (ROOT/name).rglob('*'):
            if '__pycache__' in p.parts or p.suffix=='.pyc':continue
            if p.is_symlink():raise ValueError(f'source symlink rejected: {p}')
            if p.is_file():found.add(p)
    return sorted(found,key=lambda p:p.relative_to(ROOT).as_posix())

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=ROOT/'release/qcp-simplex-gmp-P5-candidate.tar.gz');parser.add_argument('--stage',default='P5-candidate');args=parser.parse_args()
    output=args.output.resolve();output.parent.mkdir(parents=True,exist_ok=True)
    data={p.relative_to(ROOT).as_posix():p.read_bytes() for p in sources()}
    manifest={'schema':1,'stage':args.stage,'root':PREFIX,'files':{n:{'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)} for n,b in data.items()},'excludes':['build/','release/','__pycache__/','*.pyc'],'self_hash':'RELEASE_MANIFEST.json intentionally excludes itself; archive digest is an external sidecar'}
    encoded=(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n').encode()
    manifest_path=output.with_name(output.name.removesuffix('.tar.gz')+'.manifest.json')
    manifest_path.write_bytes(encoded)
    with output.open('wb') as raw,gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0) as gz,tarfile.open(fileobj=gz,mode='w',format=tarfile.PAX_FORMAT) as tar:
        for name,body in sorted({**data,'RELEASE_MANIFEST.json':encoded}.items()):
            member=tarfile.TarInfo(f'{PREFIX}/{name}');member.size=len(body);member.mode=0o644;member.mtime=0;member.uid=member.gid=0;member.uname=member.gname='';tar.addfile(member,io.BytesIO(body))
    digest=hashlib.sha256(output.read_bytes()).hexdigest()
    output.with_name(output.name+'.sha256').write_text(f'{digest}  {output.name}\n')
    print(output);print(f'{len(data)} source members plus RELEASE_MANIFEST.json');print(digest)
if __name__=='__main__':main()
