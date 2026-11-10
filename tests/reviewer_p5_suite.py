"""Run inside an unpacked source release. Original QCP is an optional extra check."""
import argparse
import os
from pathlib import Path
import subprocess
import sys
from reviewer_p3_acceptance import STRICT, SAN, verify
from reviewer_p4_acceptance import exercise_p4

ROOT = Path(__file__).resolve().parents[1]


def run(log, args):
    args = list(map(str, args))
    log.write(' '.join(args)+'\n'); log.flush()
    subprocess.run(args, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)


def consumer(log, original=None):
    origin = ROOT/'tests/reviewer_p5_origin.c'
    obj = 'build/reviewer_p5_origin.o'
    flags = ['-DREVIEW_ORIGINAL_QCP','-I',original] if original else ['-Ivendor']
    run(log,['cc',*STRICT,*flags,'-c',origin,'-o',obj])
    run(log,['cc',*STRICT,'-Iinclude','-Ivendor','tests/reviewer_p5_consumer.c',obj,
             'build/libsx_solver.a','-o','build/reviewer_p5_consumer'])
    run(log,['./build/reviewer_p5_consumer'])
    deps = subprocess.check_output(['readelf','-d','build/reviewer_p5_consumer'],cwd=ROOT,text=True)
    log.write(deps)
    assert not any(name in deps for name in ['libgmp','libasan','libubsan']), deps


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--original-headers',type=Path,help='Optional upstream Applications_human include root')
    ap.add_argument('--smoke',action='store_true',help='Normal build and external consumers only')
    args = ap.parse_args()
    (ROOT/'build').mkdir(exist_ok=True)
    with (ROOT/'build/reviewer_p5_suite.log').open('w') as log:
        if not args.smoke:
            run(log,['make','sanitize'])
            verify(log,SAN)
            exercise_p4(log,SAN)
        run(log,['make','normal'])
        consumer(log)
        if args.original_headers:
            consumer(log,args.original_headers)
        for which in ['integer','fraction','conflict','budget']:
            run(log,['./build/qcp_example',which])
        if not args.smoke:
            run(log,['make','test'])
            verify(log,['-O2'])
            exercise_p4(log,['-O2'])
            run(log,[sys.executable,'-B','tests/reviewer_fraction.py'])
    print('Unpacked P5 source checks passed. See build/reviewer_p5_suite.log')


if __name__=='__main__':
    for v in ['CPATH','C_INCLUDE_PATH','LIBRARY_PATH','LD_LIBRARY_PATH','PYTHONPATH']:
        os.environ.pop(v,None)
    main()
