#!/usr/bin/env python3
"""Model-side check of the native hardware campaign (no hardware, no QEMU): generate the cases of every
family of fp_cases.FAMILIES, run them on the model with `x86fp --compat` (compatibility mode under
long mode, as the native oracle runs them) and with `x86fp` (legacy protected mode), check that both
outputs are complete and well formed, and that the two configurations agree for every case outside the
`longmode` family (whose instructions are defined to differ there; native_longmode.py) and the cases of
the extended families marked `compat_only` (their selection found the two modes to differ:
native_ext.select; counted). It also checks that the oracle could observe every model result
(native_fp.model_problems: an exception vector with a Linux signal the oracle handles, the instruction
pointer inside its code page, for format 3 a #PF inside the low 256 KiB).

  fp_model_check.py [--smoke] [--seed S] [--count N]

--smoke keeps two cases per (family, instruction), as `native_fp.py prepare --smoke` does (the default
gate); without it the whole campaign of `prepare` with that seed and count is run (verify.sh --full).
"""
import argparse
import collections
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from fp_cases import cases  # noqa: E402
from native_fp import rows, KINDS, KIND, SIZE, FORMAT3, model_problems  # noqa: E402

X86FP = HERE.parent / '.lake' / 'build' / 'bin' / 'x86fp'
BATCH = 5000


def run(binary, compat, count, v3=False):
    args = [str(X86FP)] + (['--compat'] if compat else []) + [str(binary)]
    with tempfile.NamedTemporaryFile('w+', suffix='.model') as out:
        subprocess.run(args, stdout=out, check=True, timeout=3600)
        return list(rows(Path(out.name), count, FORMAT3['model'] if v3 else KINDS[KIND]['model']))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--smoke', action='store_true')
    p.add_argument('--seed', type=int, default=20261111)
    p.add_argument('--count', type=int, default=10000)
    a = p.parse_args()
    started = time.monotonic()
    seen = collections.Counter()
    families = collections.Counter()
    differ = collections.Counter()
    problems = []
    batch, meta = [], []
    total = 0
    compat_only = collections.Counter()

    def flush():
        nonlocal total
        if not batch:
            return
        v3 = len(batch[0]) == FORMAT3['size']
        with tempfile.NamedTemporaryFile(suffix='.bin') as f:
            f.write((len(batch) | 1 << 63 | (1 << 62 if v3 else 0)).to_bytes(8, 'little') + b''.join(batch))
            f.flush()
            compat = run(f.name, True, len(batch), v3)
            legacy = run(f.name, False, len(batch), v3)
        problems.extend(model_problems(meta, compat))
        for m, c, l in zip(meta, compat, legacy):
            families[m['family']] += 1
            if c != l and m.get('compat_only'):
                compat_only[m['family']] += 1
            elif c != l and m['family'] != 'longmode':
                differ[m['family']] += 1
        total += len(batch)
        batch.clear()
        meta.clear()

    for raw, m in cases(a.seed, a.count):
        if a.smoke:
            key = (m['family'], m['instruction'])
            seen[key] += 1
            if seen[key] > 2:
                continue
        assert len(raw) in (SIZE, FORMAT3['size'])
        if batch and len(raw) != len(batch[0]):
            flush()
        batch.append(raw)
        meta.append(m)
        if len(batch) == BATCH:
            flush()
    flush()
    bad = sum(differ.values())
    print(f'fp_model_check: {total} cases in {len(families)} families run by x86fp --compat and x86fp, '
          f'complete; {bad} compat/legacy differences outside the longmode family '
          f'({families["longmode"]} longmode cases, {sum(compat_only.values())} cases of the extended families '
          f'selected as compatibility-mode specific); {time.monotonic() - started:.0f} s')
    for f, n in sorted(differ.items()):
        print(f'  {f}: {n} differ')
    for p in problems:
        print(f'  not observable natively: {p["family"]} {p["instruction"]} {p["code"]}: {p["problem"]}')
    if problems:
        return 1
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
