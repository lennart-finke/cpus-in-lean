#!/usr/bin/env python3
"""Run every independent Python reference against the model and print one line per check.

  refs.py [--full]          (from anywhere; needs `lake build x86test x86sys` and, for the transcript
                             checks, a system-test run: test/sys/out/model.txt and systest.elf)

* tables: each reference regenerates the table of expected results that the test kernel compiles in
  (xsave_cases.h, vme_cases.h, svm_cases.h, crypto_cases.h, x87t_cases.h); it must be byte-identical
  to the committed header (the model-only section then checks the model against these values);
* transcripts: sse_ref, avx_ref and avx2_ref recompute their lines of the model's system-test
  transcript (test/sys/out/model.txt);
* gpr_ref check: random register-operand cases of the GPR extensions run on the model (x86test --dump);
* topo_ref check N: x86sys --smp N --cmdline smpn=N (every CPU reports its CPUID topology) for N = 2, 3,
  4, 16 (and 64, 128 with --full);
* the references' self-tests (vmeref, svmref, xsaveref, cryptoref).
Exit status 1 if any check fails.
"""
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
VAL = os.path.dirname(HERE)
SYS = os.path.join(HERE, 'sys')
OUT = os.path.join(SYS, 'out')
PY = sys.executable
failed = []


def check(name, cmd, cwd=VAL, ok=lambda r: r.returncode == 0, show=None):
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    good = ok(r)
    text = (r.stdout + r.stderr).strip().splitlines()
    line = show(r) if show else (text[-1] if text else '')
    print(f'  {"ok  " if good else "FAIL"} {name}: {line}', flush=True)
    if not good:
        failed.append(name)
        print('\n'.join('       ' + t for t in text[-15:]))


def table(name, cmd, header, to_stdout):
    with tempfile.TemporaryDirectory() as d:
        out = os.path.join(d, 'cases.h')
        if to_stdout:
            with open(out, 'w') as f:
                r = subprocess.run(cmd, cwd=SYS, stdout=f, stderr=subprocess.PIPE, text=True)
        else:
            r = subprocess.run(cmd + [out], cwd=SYS, capture_output=True, text=True)
        same = r.returncode == 0 and open(out).read() == open(os.path.join(SYS, header)).read()
        n = open(os.path.join(SYS, header)).read().count('\n')
        print(f'  {"ok  " if same else "FAIL"} {name}: regenerated {header} is {"identical" if same else "DIFFERENT"} ({n} lines)', flush=True)
        if not same:
            failed.append(name)


def main():
    full = '--full' in sys.argv
    print('== reference tables (regenerated, compared with the committed headers)')
    table('xsaveref', [PY, 'xsaveref.py', 'table', '600', '1'], 'xsave_cases.h', True)
    table('vmeref', [PY, 'vmeref.py', 'table', '800', '1'], 'vme_cases.h', True)
    table('svmref', [PY, 'svmref.py', 'table', '400', '400', '1'], 'svm_cases.h', True)
    table('cryptoref', [PY, os.path.join(HERE, 'cryptoref.py'), 'table'], 'crypto_cases.h', False)
    table('x87ref', [PY, 'x87ref.py', 'table'], 'x87t_cases.h', False)
    print('== reference self-tests')
    check('cryptoref selftest', [PY, 'test/cryptoref.py', 'selftest'])
    check('vmeref selftest', [PY, 'test/sys/vmeref.py', 'selftest'])
    check('svmref selftest', [PY, 'test/sys/svmref.py', 'selftest'])
    check('xsaveref selftest', [PY, 'test/sys/xsaveref.py', 'selftest'])
    print('== the model\'s system-test transcript against the references')
    model = os.path.join(OUT, 'model.txt')
    if os.path.exists(model):
        check('sse_ref', [PY, 'test/sse_ref.py', 'check', model])
        check('avx_ref', [PY, 'test/avx_ref.py', 'check', model])
        check('avx2_ref', [PY, 'test/avx2_ref.py', 'check', model])
    else:
        print('  FAIL transcripts: test/sys/out/model.txt missing (run test/sys/run.sh first)')
        failed.append('transcripts')
    print('== GPR extensions on the model (x86test --dump) against gpr_ref')
    check('gpr_ref', [PY, 'test/gpr_ref.py', 'check'] + (['2000', '7'] if full else []))
    print('== CPUID topology of N CPUs (x86sys --smp N --cmdline smpn=N) against topo_ref')
    elf = os.path.join(OUT, 'systest.elf')
    for n in (2, 3, 4, 16) + ((64, 128) if full else ()):
        if not os.path.exists(elf):
            print('  FAIL topo_ref: test/sys/out/systest.elf missing (run test/sys/run.sh first)')
            failed.append('topo_ref')
            break
        with tempfile.NamedTemporaryFile('w+', suffix='.txt') as t:
            subprocess.run([os.path.join(VAL, '.lake', 'build', 'bin', 'x86sys'), '--smp', str(n), '--cmdline',
                            f'smpn={n}', elf], stdout=t, check=False, timeout=3600)
            check(f'topo_ref {n} CPUs', [PY, 'test/topo_ref.py', 'check', str(n), t.name])
    print(f'refs: {"all checks passed" if not failed else "FAILED: " + ", ".join(failed)}')
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
