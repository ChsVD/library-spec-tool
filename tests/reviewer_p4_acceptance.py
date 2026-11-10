"""Reproduce P4 review using P3 public tests and independent P4 cases."""
import json
import sys
from reviewer_p3_acceptance import ROOT, STRICT, SAN, run, verify


def exercise_p4(log, flags):
    run(log, ['cc', *STRICT, *flags, '-Iinclude', '-Ivendor', 'tests/reviewer_p4_modes.c',
              'build/libsx_solver.a','-o','build/reviewer_p4_modes'])
    run(log, ['./build/reviewer_p4_modes'])
    modes = [json.dumps(['--disable-opts',str(i)]) for i in range(16)]
    run(log, [sys.executable,'-B','tests/reviewer_p4.py',*modes])


def main():
    (ROOT/'build').mkdir(exist_ok=True)
    with (ROOT/'build/reviewer_p4_acceptance.log').open('w') as log:
        run(log,[sys.executable,'-B','tests/check_baseline.py'])
        run(log,['make','sanitize'])
        verify(log,SAN)
        exercise_p4(log,SAN)
        run(log,['make','clean'])
        run(log,['make','test'])
        verify(log,['-O2'])
        exercise_p4(log,['-O2'])
        run(log,[sys.executable,'-B','tests/reviewer_fraction.py'])
    print('P4 acceptance passed. Details in build/reviewer_p4_acceptance.log')


if __name__=='__main__':
    main()
