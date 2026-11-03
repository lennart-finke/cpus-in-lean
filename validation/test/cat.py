#!/usr/bin/env python3
"""Group mismatches in a diff file by opcode (prefixes stripped)."""
import sys, re, collections
c = collections.Counter(); ex = {}
for l in open(sys.argv[1]):
    if not l.startswith('MISMATCH'): continue
    h = l.split()[3]
    b = bytes.fromhex(h); i = 0
    while i < len(b) and b[i] in (0xf0, 0xf2, 0xf3, 0x66, 0x67, 0x26, 0x2e, 0x36, 0x3e, 0x64, 0x65): i += 1
    k = b[i:i+2].hex() if b[i] == 0x0f else b[i:i+1].hex()
    if k in ('f6', 'f7', 'fe', 'ff', '80', '81', '83', 'c0', 'c1', 'd0', 'd1', 'd2', 'd3', '0fba', '0f00', '0f01', '0fc7'):
        j = i + len(k)//2
        if j < len(b): k += '/%d' % ((b[j] >> 3) & 7)
    c[k] += 1; ex.setdefault(k, l.split()[1])
for k, n in c.most_common(): print(n, k, ex[k])
