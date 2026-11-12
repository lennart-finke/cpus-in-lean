#!/usr/bin/env python3
"""Independent reference for the general-purpose Zen 2 extensions (x86_32/X86/Ext/Gpr.lean).

Written from the AMD64 APM vol. 3 (rev. 3.33) instruction pages and, where the APM gives no
algorithm, the Intel SDM pseudo-code -- not from the Lean code:
  POPCNT, LZCNT, TZCNT (bit scans), ANDN, BEXTR, BLSI, BLSMSK, BLSR (the APM's pseudo-operations),
  BZHI (SDM pseudo-code), PDEP/PEXT (APM diagrams: bit-by-bit scatter/gather), MULX, RORX, SARX,
  SHLX, SHRX, ADCX, ADOX, MOVBE, CRC32 (polynomial division by 11EDC6F41h of the bit-reflected
  operands, SDM CRC32 pseudo-code) and the model's documented RDRAND/RDSEED entropy source
  (SplitMix64, Steele/Lea/Flood 2014, from state 0).

  python3 gpr_ref.py check [N] [SEED]   N random register-operand cases per instruction, run on the
                                        model (x86test --dump, v1 vectors in ring 3) and compared
                                        with this reference (all GPRs and the defined flags)
"""
import os
import random
import struct
import subprocess
import sys
import tempfile

M32 = 0xFFFFFFFF
CF, PF, AF, ZF, SF, OF = 1, 4, 0x10, 0x40, 0x80, 0x800
ARITH = CF | PF | AF | ZF | SF | OF
X86TEST = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '.lake', 'build', 'bin', 'x86test')

# ---------------------------------------------------------------------------------------------
# Reference operations (values are Python ints; `w` is the operand width in bits)


def bits(x, w):
    return [(x >> i) & 1 for i in range(w)]


def popcnt(x, w):
    return sum(bits(x, w))


def lzcnt(x, w):
    n = 0
    for i in reversed(range(w)):
        if (x >> i) & 1:
            break
        n += 1
    return n


def tzcnt(x, w):
    n = 0
    for i in range(w):
        if (x >> i) & 1:
            break
        n += 1
    return n


def andn(a, b):
    return ~a & b & M32


def bextr(src, ctl):
    start, length = ctl & 0xFF, (ctl >> 8) & 0xFF
    out = 0
    for k in range(length):           # bit k of the result is source bit start + k (0 beyond 31)
        p = start + k
        if p < 32 and (src >> p) & 1:
            out |= 1 << k
        if k >= 31:
            break
    return out


def blsi(s):
    return (-s & M32) & s


def blsmsk(s):
    return ((s - 1) & M32) ^ s


def blsr(s):
    return ((s - 1) & M32) & s


def bzhi(src, idx):
    n = idx & 0xFF
    return src if n >= 32 else src & ((1 << n) - 1)


def pdep(src, mask):
    out, k = 0, 0
    for i in range(32):
        if (mask >> i) & 1:
            out |= ((src >> k) & 1) << i
            k += 1
    return out


def pext(src, mask):
    out, k = 0, 0
    for i in range(32):
        if (mask >> i) & 1:
            out |= ((src >> i) & 1) << k
            k += 1
    return out


def reflect(x, w):
    return int(format(x, '0%db' % w)[::-1], 2)


def crc32(dest, src, w):
    """SDM CRC32: TEMP1 = BIT_REFLECT(SRC), TEMP2 = BIT_REFLECT32(DEST), TEMP5 = (TEMP1 << 32) XOR
    (TEMP2 << w), TEMP6 = TEMP5 MOD2 11EDC6F41h, DEST = BIT_REFLECT32(TEMP6)."""
    t5 = (reflect(src, w) << 32) ^ (reflect(dest, 32) << w)
    poly = 0x11EDC6F41
    for i in reversed(range(32, 32 + w)):
        if (t5 >> i) & 1:
            t5 ^= poly << (i - 32)
    return reflect(t5, 32)


def splitmix64(state):
    state = (state + 0x9E3779B97F4A7C15) & (2**64 - 1)
    z = state
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & (2**64 - 1)
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & (2**64 - 1)
    return state, z ^ (z >> 31)


def parity(x):
    return bin(x & 0xFF).count('1') % 2 == 0


def szp(r, w=32):
    return (ZF if r == 0 else 0) | (SF if (r >> (w - 1)) & 1 else 0) | (PF if parity(r) else 0)

# ---------------------------------------------------------------------------------------------
# Cases: (name, instruction bytes, registers in, function(regs, eflags) -> (regs out, flags out),
# mask of the defined flags)

REGS = ['eax', 'ecx', 'edx', 'ebx', 'esp', 'ebp', 'esi', 'edi']


def vex3(map_, pp, vvvv, L=0, W=0):
    return bytes([0xC4, 0xE0 | map_, (W << 7) | ((~vvvv & 15) << 3) | (L << 2) | pp])


def rand_val(rng):
    return rng.choice([0, 1, 0xFFFFFFFF, 0x80000000, 0x7FFFFFFF, 1 << rng.randrange(32),
                       (1 << rng.randrange(33)) - 1, rng.getrandbits(32), rng.getrandbits(32),
                       rng.getrandbits(32) & rng.getrandbits(32)])


def case(rng, name):
    """One case: (bytes, regs, eflags, expected regs, expected flags, flag mask)."""
    regs = [rand_val(rng) for _ in range(8)]
    regs[4] = 0x8800
    fl = 0x202 | (rng.getrandbits(12) & ARITH)
    pick = lambda: rng.choice([0, 1, 2, 3, 5, 6, 7])
    d, s, v = pick(), pick(), pick()
    out = list(regs)
    flags, mask = fl, ARITH

    def setf(val, m):
        nonlocal flags
        flags = (flags & ~m) | (val & m)
    if name in ('popcnt', 'lzcnt', 'tzcnt', 'popcnt16', 'lzcnt16', 'tzcnt16'):
        w = 16 if name.endswith('16') else 32
        if rng.random() < 0.2:
            regs[s] = out[s] = rng.choice([0, 1 << rng.randrange(32)])
        x = regs[s] & ((1 << w) - 1)
        op = {'popcnt': 0xB8, 'lzcnt': 0xBD, 'tzcnt': 0xBC}[name.rstrip('16')]
        code = (b'\x66' if w == 16 else b'') + bytes([0xF3, 0x0F, op, 0xC0 | (d << 3) | s])
        r = {'popcnt': popcnt, 'lzcnt': lzcnt, 'tzcnt': tzcnt}[name.rstrip('16')](x, w)
        out[d] = (regs[d] & ~((1 << w) - 1) | r) if w == 16 else r
        if name.startswith('popcnt'):
            setf(ZF if x == 0 else 0, ARITH)
        else:
            setf((CF if x == 0 else 0) | (ZF if r == 0 else 0), CF | ZF)
            mask = CF | ZF
        return code, regs, fl, out, flags, mask
    if name in ('andn', 'bextr', 'bzhi', 'pdep', 'pext', 'shlx', 'sarx', 'shrx'):
        if name in ('bextr', 'bzhi') and rng.random() < 0.7:
            regs[v] = rng.randrange(48) | (rng.randrange(48) << 8) | (rng.getrandbits(16) << 16 if rng.random() < 0.2 else 0)
        if name in ('shlx', 'sarx', 'shrx') and rng.random() < 0.5:
            regs[v] = rng.randrange(70)
        out = list(regs)
        a, b = regs[v], regs[s]
        enc = {'andn': (0xF2, 0), 'bextr': (0xF7, 0), 'bzhi': (0xF5, 0), 'pdep': (0xF5, 3),
               'pext': (0xF5, 2), 'shlx': (0xF7, 1), 'sarx': (0xF7, 2), 'shrx': (0xF7, 3)}[name]
        code = vex3(2, enc[1], v, W=rng.getrandbits(1)) + bytes([enc[0], 0xC0 | (d << 3) | s])
        if name == 'andn':
            r = andn(a, b); setf(szp(r), SF | ZF | CF | OF); mask = SF | ZF | CF | OF
        elif name == 'bextr':
            r = bextr(b, a); setf(ZF if r == 0 else 0, ZF | CF | OF); mask = ZF | CF | OF
        elif name == 'bzhi':
            r = bzhi(b, a); setf(szp(r) | (CF if a & 0xFF > 31 else 0), SF | ZF | CF | OF); mask = SF | ZF | CF | OF
        elif name == 'pdep':
            r = pdep(a, b)
        elif name == 'pext':
            r = pext(a, b)
        elif name == 'shlx':
            r = (b << (a & 31)) & M32
        elif name == 'shrx':
            r = b >> (a & 31)
        else:
            sb = b - (1 << 32) if b >> 31 else b
            r = (sb >> (a & 31)) & M32
        out[d] = r
        return code, regs, fl, out, flags, mask
    if name in ('blsi', 'blsmsk', 'blsr'):
        reg = {'blsr': 1, 'blsmsk': 2, 'blsi': 3}[name]
        code = vex3(2, 0, d) + bytes([0xF3, 0xC0 | (reg << 3) | s])
        x = regs[s]
        r = {'blsi': blsi, 'blsmsk': blsmsk, 'blsr': blsr}[name](x)
        cf = (x != 0) if name == 'blsi' else (x == 0)
        out[d] = r
        setf(szp(r) | (CF if cf else 0), SF | ZF | CF | OF)
        return code, regs, fl, out, flags, SF | ZF | CF | OF
    if name == 'mulx':
        hi, lo = d, v
        code = vex3(2, 3, lo) + bytes([0xF6, 0xC0 | (hi << 3) | s])
        p = regs[2] * regs[s]
        out[lo] = p & M32
        out[hi] = p >> 32                 # hi written last: equal registers get the high half
        return code, regs, fl, out, flags, ARITH
    if name == 'rorx':
        n = rng.choice([0, 1, 31, 32, 33, rng.randrange(256)])
        vv = rng.choice([0, v])
        code = vex3(3, 3, vv) + bytes([0xF0, 0xC0 | (d << 3) | s, n])   # vvvv != 1111b too
        if vv != 0:
            # VEX.vvvv != 1111b: #UD (SDM RORX; the APM lists no #UD, the EPYC 7742 raises it)
            return code, regs, fl, None, flags, ARITH
        x, c = regs[s], n & 31
        out[d] = ((x >> c) | (x << (32 - c))) & M32
        return code, regs, fl, out, flags, ARITH
    if name in ('adcx', 'adox'):
        f = CF if name == 'adcx' else OF
        code = bytes([0x66 if name == 'adcx' else 0xF3, 0x0F, 0x38, 0xF6, 0xC0 | (d << 3) | s])
        t = regs[d] + regs[s] + (1 if fl & f else 0)
        out[d] = t & M32
        setf(f if t >> 32 else 0, f)
        return code, regs, fl, out, flags, ARITH
    if name in ('crc32b', 'crc32w', 'crc32d'):
        w = {'crc32b': 8, 'crc32w': 16, 'crc32d': 32}[name]
        s = rng.choice([0, 1, 2, 3]) if w == 8 else s     # AL, CL, DL, BL
        code = (b'\x66' if w == 16 else b'') + bytes([0xF2, 0x0F, 0x38, 0xF0 if w == 8 else 0xF1, 0xC0 | (d << 3) | s])
        out[d] = crc32(regs[d], regs[s] & ((1 << w) - 1), w)
        return code, regs, fl, out, flags, ARITH
    if name in ('rdrand', 'rdseed', 'rdrand16'):
        w = 16 if name == 'rdrand16' else 32
        code = (b'\x66' if w == 16 else b'') + bytes([0x0F, 0xC7, 0xC0 | ((7 if name == 'rdseed' else 6) << 3) | d])
        z = splitmix64(0)[1]
        out[d] = (regs[d] & 0xFFFF0000 | z & 0xFFFF) if w == 16 else z & M32
        setf(CF, ARITH)
        return code, regs, fl, out, flags, ARITH
    raise ValueError(name)


NAMES = ['popcnt', 'lzcnt', 'tzcnt', 'popcnt16', 'lzcnt16', 'tzcnt16', 'andn', 'bextr', 'bzhi', 'pdep',
         'pext', 'shlx', 'sarx', 'shrx', 'blsi', 'blsmsk', 'blsr', 'mulx', 'rorx', 'adcx', 'adox',
         'crc32b', 'crc32w', 'crc32d', 'rdrand', 'rdseed', 'rdrand16']


def record(code, regs, eflags):
    return struct.pack('<B15s8III4H2H2I3I', len(code), code.ljust(15, b'\0'), *regs, eflags, 1,
                       0x23, 0x23, 0x23, 0x23, 0xFFFF, 0xFFFF, 0, 0, 1, 0x67, 0x67)


def check(n=200, seed=1, exe=X86TEST):
    """Run every case on the model; returns the list of mismatch descriptions."""
    rng = random.Random(seed)
    cases = [(name, *case(rng, name)) for name in NAMES for _ in range(n)]
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, 'v.bin')
        with open(path, 'wb') as f:
            for c in cases:
                f.write(record(c[1], c[2], c[3]))
        res = subprocess.run([exe, '--dump', path], capture_output=True, text=True, check=True)
    rows = [l.split() for l in res.stdout.splitlines()[1:-1]]
    bad = []
    for (name, code, regs, fl, out, flags, mask), row in zip(cases, rows):
        v = [int(x, 16) for x in row]
        if out is None:   # #UD expected, nothing changed
            if v[1] != 6 or v[4:12] != regs:
                bad.append('%s %s: model vec=%x, reference #UD' % (name, code.hex(), v[1]))
            continue
        if v[1] != 3 or v[4:12] != out or (v[12] & mask) != (flags & mask):
            bad.append('%s %s in=%s: model vec=%x regs=%s flags=%x, reference regs=%s flags=%x (mask %x)' % (
                name, code.hex(), [hex(r) for r in regs], v[1], [hex(r) for r in v[4:12]], v[12],
                [hex(r) for r in out], flags, mask))
    if len(rows) != len(cases):
        bad.append('model returned %d rows for %d cases' % (len(rows), len(cases)))
    return bad, len(cases)


def main():
    args = sys.argv[1:]
    if not args or args[0] != 'check':
        print(__doc__)
        return 2
    n = int(args[1]) if len(args) > 1 else 200
    seed = int(args[2]) if len(args) > 2 else 1
    bad, total = check(n, seed)
    for b in bad[:20]:
        print(b)
    print('%d cases, %d differ from the reference' % (total, len(bad)))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
