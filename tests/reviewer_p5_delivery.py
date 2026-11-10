"""Verify a delivered archive, extract afresh, build, and exercise public interfaces."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_members(root, manifest):
    expected = manifest['files']
    files = {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
    assert files == set(expected)|{'RELEASE_MANIFEST.json'}, files ^ (set(expected)|{'RELEASE_MANIFEST.json'})
    for name, information in expected.items():
        p = root/name
        assert p.stat().st_size == information['bytes'] and digest(p) == information['sha256'], name


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('archive',type=Path)
    ap.add_argument('--sidecar-manifest',type=Path,required=True)
    ap.add_argument('--sidecar-sha',type=Path,required=True)
    ap.add_argument('--original-headers',type=Path)
    ap.add_argument('--smoke',action='store_true')
    ap.add_argument('--log-dir',type=Path,required=True)
    args=ap.parse_args()
    args.log_dir.mkdir(exist_ok=True,parents=True)
    checksum=digest(args.archive)
    assert checksum==args.sidecar_sha.read_text().split()[0], 'archive checksum'
    expected=json.loads(args.sidecar_manifest.read_text())
    with tempfile.TemporaryDirectory(prefix='qcp-p5-review-') as work:
        with tarfile.open(args.archive,'r:gz') as tar:
            entries=tar.getmembers(); seen=set()
            for item in entries:
                name=Path(item.name)
                assert item.isfile() or item.isdir(), item.name
                assert name.parts and name.parts[0]=='qcp-simplex-gmp-P5' and '..' not in name.parts, name
                assert name not in seen, name
                seen.add(name)
            tar.extractall(work,filter='data')
        root=Path(work)/'qcp-simplex-gmp-P5'
        manifest=json.loads((root/'RELEASE_MANIFEST.json').read_text())
        assert manifest==expected
        check_members(root,manifest)
        assert not (root/'build').exists(), 'release must build from source'
        env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','ASAN_OPTIONS':'detect_leaks=1:halt_on_error=1','UBSAN_OPTIONS':'halt_on_error=1:print_stacktrace=1'}
        for key in ['CPATH','C_INCLUDE_PATH','LIBRARY_PATH','LD_LIBRARY_PATH','PYTHONPATH']:
            env.pop(key,None)
        opts=['--smoke'] if args.smoke else []
        if args.original_headers:
            opts+=['--original-headers',str(args.original_headers.resolve())]
        try:
            subprocess.run([sys.executable,'-B','tools/verify_release.py'],cwd=root,env=env,check=True)
            readme = root/'README.md'
            original = readme.read_bytes()
            try:
                readme.write_bytes(original+b'\nchanged during package integrity test\n')
                for flags in [[], ['-O']]:
                    test = subprocess.run([sys.executable,'-B',*flags,'tools/verify_release.py'],
                                          cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
                    if test.returncode == 0:
                        raise RuntimeError(f'Production verifier accepted tampered README with {flags}')
            finally:
                readme.write_bytes(original)
            subprocess.run([sys.executable,'-B','tests/reviewer_p5_suite.py',*opts],cwd=root,env=env,check=True)
        finally:
            log=root/'build/reviewer_p5_suite.log'
            if log.is_file(): shutil.copyfile(log,args.log_dir/'suite.log')
        for n,v in manifest['files'].items():
            assert digest(root/n)==v['sha256'], 'source modified by build: '+n
        rebuilt=Path(work)/'repacked.tar.gz'
        subprocess.run([sys.executable,'-B','tools/make_release.py','--output',str(rebuilt),
                        '--stage',manifest['stage']],cwd=root,env=env,check=True)
        if digest(rebuilt)!=checksum:
            raise RuntimeError('Repacked archive differs from delivered bytes')
        (args.log_dir/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
        summary={'archive':args.archive.name,'sha256':checksum,'source_files':len(manifest['files']),'smoke':args.smoke,'result':'passed'}
        (args.log_dir/'result.json').write_text(json.dumps(summary,indent=2)+'\n')
        print(json.dumps(summary))


if __name__=='__main__':
    main()
