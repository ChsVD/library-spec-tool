"""P3 acceptance including P1/P2 regression, on instrumented and normal builds."""
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
STRICT = ['-std=c11','-Wall','-Wextra','-Werror','-Wpedantic','-Wconversion','-Wshadow']
SAN = ['-O1','-g','-fsanitize=address,undefined','-fno-omit-frame-pointer']
ENV = dict(os.environ, ASAN_OPTIONS='detect_leaks=1:halt_on_error=1', UBSAN_OPTIONS='halt_on_error=1:print_stacktrace=1')


def run(log, cmd):
    log.write(' '.join(cmd)+'\n'); log.flush()
    subprocess.run(cmd,cwd=ROOT,env=ENV,stdout=log,stderr=subprocess.STDOUT,check=True)


def cli(log):
    for data in [b'1 0 0\x00junk',b'1 0 0 extra',b'1 1 42',b'1 0 0 \x00more']:
        p = subprocess.run(['./build/solver_cli'],input=data,cwd=ROOT,env=ENV,capture_output=True)
        assert p.returncode==2 and not p.stdout,(data,p)
    p = subprocess.run(['./build/solver_cli','--ms',str(2**64-1)],input=b'0 0',cwd=ROOT,env=ENV,capture_output=True,check=True)
    result=json.loads(p.stdout)
    assert (result['error'],result['q'],result['z'])==('OK','FEASIBLE','SAT'),result
    log.write('CLI rejected 4 malformed inputs and accepted maximum unsigned time budget.\n')


def verify(log, flags):
    for name in ['reviewer_p3_driver','reviewer_p3_exit','reviewer_p2_driver','reviewer_p2_budget']:
        extra = ['-Wl,--wrap=clock_gettime'] if name.endswith('exit') else []
        run(log, ['cc',*STRICT,*flags,'-Iinclude','-Ivendor',f'tests/{name}.c',
                  'build/libsx_solver.a',*extra,'-o',f'build/{name}'])
    run(log,['./build/reviewer_p3_exit'])
    run(log,[sys.executable,'-B','tests/reviewer_p3.py'])
    run(log,['./build/reviewer_p2_budget'])
    run(log,[sys.executable,'-B','tests/reviewer_p2.py'])
    cli(log)


def main():
    (ROOT/'build').mkdir(exist_ok=True)
    with (ROOT/'build/reviewer_p3_acceptance.log').open('w') as log:
        run(log,[sys.executable,'-B','tests/check_baseline.py'])
        run(log,['make','sanitize'])
        verify(log,SAN)
        run(log,['make','clean'])
        run(log,['make','test'])
        verify(log,['-O2'])
        run(log,[sys.executable,'-B','tests/reviewer_fraction.py'])
    print('P3 acceptance passed. Details in build/reviewer_p3_acceptance.log')


if __name__=='__main__':
    main()
