#!/usr/bin/env python3
"""Show mismatch records with the initial vector state: show.py diff.txt vectors.bin N [N...]"""
import re, struct, sys
txt = open(sys.argv[1]).read(); d = open(sys.argv[2], 'rb').read()
want = set(sys.argv[3:])
for b in re.split(r'(?=MISMATCH #)', txt):
    m = re.match(r'MISMATCH #(\d+)', b)
    if m and m.group(1) in want:
        n = int(m.group(1)); f = struct.unpack('<B15s8III4H2H2I3I', d[n*88:(n+1)*88])
        print(' '.join(b.replace('X86.', '').split()))
        print('   init regs', [hex(x) for x in f[2:10]], 'efl', hex(f[10]), 'sel', f[12:16],
              'patch', f[16:18], [hex(x) for x in f[18:20]], 'mode', f[20], 'pte', hex(f[21]), hex(f[22]))
        print()
