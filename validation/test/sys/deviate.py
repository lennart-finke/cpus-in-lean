#!/usr/bin/env python3
"""Apply the known-QEMU-deviation rules (qemu-deviations.txt, then any further rule files such as the
generated x87t-deviations.txt) to a QEMU transcript on stdin.
The cr3.rsvd rule also eats the trailing fields of the model line, so rules may match a prefix."""
import re
import sys

rules = []
for path in sys.argv[1:]:
    for line in open(path):
        if line.startswith('#') or not line.strip():
            continue
        pat, rep = line.rstrip('\n').split('\t')[:2]
        rules.append((re.compile(pat), rep))
used = 0
for line in sys.stdin:
    line = line.rstrip('\n')
    for pat, rep in rules:
        new = pat.sub(rep, line)
        if new != line:
            line, used = new, used + 1
            break
    print(line)
print(f'deviate: {used} known QEMU deviations applied', file=sys.stderr)
