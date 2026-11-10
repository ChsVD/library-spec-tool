"""Verify an extracted source tree; checks remain active under python -O."""
from pathlib import Path
import argparse,hashlib,json,sys
ROOT=Path(__file__).resolve().parents[1]

def verify(manifest):
    if not isinstance(manifest,dict) or manifest.get('schema')!=1:raise ValueError('unsupported manifest schema')
    files=manifest.get('files')
    if not isinstance(files,dict) or not files:raise ValueError('manifest has no file inventory')
    for name,info in files.items():
        if not isinstance(name,str) or not name or Path(name).is_absolute() or '..' in Path(name).parts or name=='RELEASE_MANIFEST.json':raise ValueError(f'invalid member path: {name!r}')
        p=(ROOT/name).resolve()
        if not p.is_relative_to(ROOT) or not p.is_file():raise ValueError(f'missing/outside member: {name}')
        if not isinstance(info,dict) or type(info.get('bytes')) is not int or info['bytes']<0:raise ValueError(f'invalid size metadata: {name}')
        digest=info.get('sha256')
        if not isinstance(digest,str) or len(digest)!=64 or any(c not in '0123456789abcdef' for c in digest):raise ValueError(f'invalid digest metadata: {name}')
        body=p.read_bytes()
        if len(body)!=info['bytes'] or hashlib.sha256(body).hexdigest()!=digest:raise ValueError(f'checksum/size mismatch: {name}')
    return len(files)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--manifest',type=Path,default=ROOT/'RELEASE_MANIFEST.json');args=parser.parse_args()
    try:
        count=verify(json.loads(args.manifest.read_text()))
    except (OSError,ValueError,TypeError) as error:
        print(f'release verification failed: {error}',file=sys.stderr);return 1
    print(f'Verified {count} source members; manifest self-hash intentionally excluded');return 0
if __name__=='__main__':sys.exit(main())
