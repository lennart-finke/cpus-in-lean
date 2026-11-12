#!/usr/bin/env python3
"""Model-side check of the native hardware campaign (no hardware, no QEMU): generate the cases of every
family of fp_cases.FAMILIES, run them on the model with `x86fp --compat` (compatibility mode under
long mode, as the native oracle runs them) and with `x86fp` (legacy protected mode), check that both
outputs are complete and well formed, and that the two configurations agree for every case outside the
`longmode` family (whose instructions are defined to differ there; native_longmode.py).

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
from native_fp import rows, KINDS, KIND, SIZE  # noqa: E402

X86FP = HERE.parent / '.lake' / 'build' / 'bin' / 'x86fp'
BATCH = 5000


def run(binary, compat, count):
    args = [str(X86FP)] + (['--compat'] if compat else []) + [str(binary)]
    with tempfile.NamedTemporaryFile('w+', suffix='.model') as out:
        subprocess.run(args, stdout=out, check=True, timeout=3600)
        return list(rows(Path(out.name), count, KINDS[KIND]['model']))


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
    batch, meta = [], []
    total = 0

    def flush():
        nonlocal total
        if not batch:
            return
        with tempfile.NamedTemporaryFile(suffix='.bin') as f:
            f.write((len(batch) | 1 << 63).to_bytes(8, 'little') + b''.join(batch))
            f.flush()
            compat = run(f.name, True, len(batch))
            legacy = run(f.name, False, len(batch))
        for m, c, l in zip(meta, compat, legacy):
            families[m['family']] += 1
            if c != l and m['family'] != 'longmode':
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
        assert len(raw) == SIZE
        batch.append(raw)
        meta.append(m)
        if len(batch) == BATCH:
            flush()
    flush()
    bad = sum(differ.values())
    print(f'fp_model_check: {total} cases in {len(families)} families run by x86fp --compat and x86fp, '
          f'complete; {bad} compat/legacy differences outside the longmode family '
          f'({families["longmode"]} longmode cases); {time.monotonic() - started:.0f} s')
    for f, n in sorted(differ.items()):
        print(f'  {f}: {n} differ')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
