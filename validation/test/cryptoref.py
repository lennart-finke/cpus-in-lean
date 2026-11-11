#!/usr/bin/env python3
"""Independent reference for the AES-NI, PCLMULQDQ and SHA instructions (x86_32/X86/Ext/Crypto.lean).

Written from the specifications, not from the Lean code: FIPS-197 (AES: the S-box is computed from
its definition, the multiplicative inverse in GF(2^8) followed by the affine map; the cipher and the
key expansion follow the standard's pseudocode), FIPS 180-4 (SHA-1, SHA-256), the GCM specification
(McGrew and Viega; GHASH by its bitwise algorithm), and the operation sections of the Intel SDM
instruction pages AESENC .. SHA256MSG2 (the AMD APM vol. 4 describes the same operations).

A 128-bit XMM value is a Python int; byte k is bits 8k+7..8k (memory byte k), dword k bits 32k+31..32k.

  cryptoref.py selftest                     the self-checks (also run by test_cryptoref.py)
  cryptoref.py table OUT.h [N] [SEED]       random cases with expected results for the system test
                                            kernel (t_crypto.c, MODEL-ONLY section)
  cryptoref.py vectors V.bin V.meta Q.out   check QEMU's results of the 'crypto-' vectors of a
                                            test/run.sh run (gen_crypto.py) against this reference
"""
import hashlib
import random
import struct
import sys

M32 = 0xFFFFFFFF
M128 = (1 << 128) - 1

# ---------------------------------------------------------------------------------------------
# GF(2^8) and the S-box (FIPS-197 4.2, 5.1.1)

def gmul(a, b):
    """Multiplication in GF(2^8) modulo x^8 + x^4 + x^3 + x + 1, shift-and-add."""
    p = 0
    while b:
        if b & 1:
            p ^= a
        a <<= 1
        if a & 0x100:
            a ^= 0x11B
        b >>= 1
    return p


def ginv(a):
    """Multiplicative inverse (0 maps to 0), by search."""
    if a == 0:
        return 0
    return next(x for x in range(1, 256) if gmul(a, x) == 1)


def _affine(b):
    c = 0x63
    out = 0
    for i in range(8):
        bit = (b >> i) ^ (b >> ((i + 4) % 8)) ^ (b >> ((i + 5) % 8)) ^ (b >> ((i + 6) % 8)) ^ \
            (b >> ((i + 7) % 8)) ^ (c >> i)
        out |= (bit & 1) << i
    return out


SBOX = [_affine(ginv(x)) for x in range(256)]
INV_SBOX = [0] * 256
for _x in range(256):
    INV_SBOX[SBOX[_x]] = _x

# ---------------------------------------------------------------------------------------------
# AES state: a list of 16 bytes, byte r + 4c = row r of column c (FIPS-197 3.4)

def to_bytes(x):
    return [(x >> (8 * k)) & 0xFF for k in range(16)]


def from_bytes(b):
    return sum(v << (8 * k) for k, v in enumerate(b))


def sub_bytes(s, box=SBOX):
    return [box[v] for v in s]


def shift_rows(s):
    # s'[r][c] = s[r][(c + r) mod 4]
    return [s[r + 4 * ((c + r) % 4)] for c in range(4) for r in range(4)]


def inv_shift_rows(s):
    # s'[r][(c + r) mod 4] = s[r][c]
    out = [0] * 16
    for c in range(4):
        for r in range(4):
            out[r + 4 * ((c + r) % 4)] = s[r + 4 * c]
    return out


def mix_columns(s, m=(2, 3, 1, 1)):
    out = [0] * 16
    for c in range(4):
        col = s[4 * c:4 * c + 4]
        for r in range(4):
            v = 0
            for k in range(4):
                v ^= gmul(m[(k - r) % 4], col[k])
            out[4 * c + r] = v
    return out


def inv_mix_columns(s):
    return mix_columns(s, (0x0E, 0x0B, 0x0D, 0x09))


def xor(a, b):
    return [x ^ y for x, y in zip(a, b)]

# The instructions (SDM AESENC/AESENCLAST/AESDEC/AESDECLAST/AESIMC/AESKEYGENASSIST, "Operation")

def aesenc(a, b):
    return from_bytes(xor(mix_columns(sub_bytes(shift_rows(to_bytes(a)))), to_bytes(b)))


def aesenclast(a, b):
    return from_bytes(xor(sub_bytes(shift_rows(to_bytes(a))), to_bytes(b)))


def aesdec(a, b):
    return from_bytes(xor(inv_mix_columns(sub_bytes(inv_shift_rows(to_bytes(a)), INV_SBOX)), to_bytes(b)))


def aesdeclast(a, b):
    return from_bytes(xor(sub_bytes(inv_shift_rows(to_bytes(a)), INV_SBOX), to_bytes(b)))


def aesimc(b):
    return from_bytes(inv_mix_columns(to_bytes(b)))


def sub_word(w):
    return sum(SBOX[(w >> (8 * k)) & 0xFF] << (8 * k) for k in range(4))


def rot_word(w):
    # [a0, a1, a2, a3] -> [a1, a2, a3, a0] with a0 the low byte
    return ((w >> 8) | (w << 24)) & M32


def dword(x, k):
    return (x >> (32 * k)) & M32


def dwords(d0, d1, d2, d3):
    return d0 | d1 << 32 | d2 << 64 | d3 << 96


def aeskeygenassist(b, imm):
    x1, x3 = dword(b, 1), dword(b, 3)
    return dwords(sub_word(x1), rot_word(sub_word(x1)) ^ imm, sub_word(x3), rot_word(sub_word(x3)) ^ imm)

# The standard cipher (FIPS-197 5.1, 5.2, 5.3), independent of the instruction forms

def key_expansion(key):
    nk = len(key) // 4
    nr = nk + 6
    w = [list(key[4 * i:4 * i + 4]) for i in range(nk)]
    rcon = 1
    for i in range(nk, 4 * (nr + 1)):
        t = list(w[i - 1])
        if i % nk == 0:
            t = [SBOX[v] for v in t[1:] + t[:1]]
            t[0] ^= rcon
            rcon = gmul(rcon, 2)
        elif nk > 6 and i % nk == 4:
            t = [SBOX[v] for v in t]
        w.append([x ^ y for x, y in zip(w[i - nk], t)])
    return [sum(w[4 * r:4 * r + 4], []) for r in range(nr + 1)]


def aes_encrypt_block(key, block):
    rk = key_expansion(key)
    s = xor(list(block), rk[0])
    for r in range(1, len(rk)):
        s = shift_rows(sub_bytes(s))
        if r != len(rk) - 1:
            s = mix_columns(s)
        s = xor(s, rk[r])
    return bytes(s)


def aes_decrypt_block(key, block):
    """The inverse cipher (FIPS-197 5.3, figure 12)."""
    rk = key_expansion(key)
    s = xor(list(block), rk[-1])
    for r in range(len(rk) - 2, -1, -1):
        s = sub_bytes(inv_shift_rows(s), INV_SBOX)
        s = xor(s, rk[r])
        if r != 0:
            s = inv_mix_columns(s)
    return bytes(s)

# The cipher composed from the instructions (key expansion with AESKEYGENASSIST)

def round_keys_insn(key):
    nk = len(key) // 4
    nr = nk + 6
    w = [int.from_bytes(key[4 * i:4 * i + 4], 'little') for i in range(nk)]
    rcon = 1
    for i in range(nk, 4 * (nr + 1)):
        t = w[i - 1]
        if i % nk == 0:
            t = dword(aeskeygenassist(t << 96, rcon), 3)
            rcon = gmul(rcon, 2)
        elif nk > 6 and i % nk == 4:
            t = dword(aeskeygenassist(t << 96, 0), 2)
        w.append(w[i - nk] ^ t)
    return [dwords(*w[4 * r:4 * r + 4]) for r in range(nr + 1)]


def aes_encrypt_insn(key, block):
    rk = round_keys_insn(key)
    s = int.from_bytes(block, 'little') ^ rk[0]
    for k in rk[1:-1]:
        s = aesenc(s, k)
    return aesenclast(s, rk[-1]).to_bytes(16, 'little')


def aes_decrypt_insn(key, block):
    rk = round_keys_insn(key)
    s = int.from_bytes(block, 'little') ^ rk[-1]
    for k in reversed(rk[1:-1]):
        s = aesdec(s, aesimc(k))
    return aesdeclast(s, rk[0]).to_bytes(16, 'little')

# ---------------------------------------------------------------------------------------------
# Carry-less multiplication (SDM PCLMULQDQ) and GHASH (GCM spec, algorithm 1)

def clmul(a, b):
    r = 0
    for i in range(64):
        if (b >> i) & 1:
            r ^= a << i
    return r


def pclmulqdq(a, b, imm):
    x = (a >> 64) if imm & 0x01 else a & ((1 << 64) - 1)
    y = (b >> 64) if imm & 0x10 else b & ((1 << 64) - 1)
    return clmul(x, y)


def gcm_mul(x, y):
    """X·Y in GF(2^128), blocks as 128-bit big-endian integers (bit 0 of the GCM block is the
    most significant bit)."""
    R = 0xE1 << 120
    z, v = 0, y
    for i in range(128):
        if (x >> (127 - i)) & 1:
            z ^= v
        v = (v >> 1) ^ R if v & 1 else v >> 1
    return z


def ghash(h, blocks):
    y = 0
    for b in blocks:
        y = gcm_mul(y ^ b, h)
    return y


def gfmul_insn(x, h):
    """GCM multiplication composed from PCLMULQDQ: reflect the bits of each byte (GCM numbers bits
    from the MSB), multiply with four PCLMULQDQ, reduce modulo x^128 + x^7 + x^2 + x + 1."""
    def reflect(v):
        return sum(int('{:08b}'.format((v >> (8 * k)) & 0xFF)[::-1], 2) << (8 * k) for k in range(16))
    a, b = reflect(x), reflect(h)
    p = pclmulqdq(a, b, 0x00) ^ ((pclmulqdq(a, b, 0x01) ^ pclmulqdq(a, b, 0x10)) << 64) ^ \
        (pclmulqdq(a, b, 0x11) << 128)
    hi, lo = p >> 128, p & M128
    t = pclmulqdq(hi, 0x87, 0x00) ^ (pclmulqdq(hi, 0x87, 0x01) << 64)
    lo ^= t & M128
    lo ^= pclmulqdq(t >> 128, 0x87, 0x00)
    return reflect(lo)

# ---------------------------------------------------------------------------------------------
# SHA (FIPS 180-4) and the SHA instructions (SDM)

def rol(x, n):
    return ((x << n) | (x >> (32 - n))) & M32


def ror(x, n):
    return ((x >> n) | (x << (32 - n))) & M32


def sha1_f(sel, b, c, d):
    if sel == 0:
        return (b & c) ^ (~b & d & M32)
    if sel == 2:
        return (b & c) ^ (b & d) ^ (c & d)
    return b ^ c ^ d


SHA1_K = [0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xCA62C1D6]


def sha1rnds4(a, b, imm):
    sel = imm & 3
    A, B, C, D = dword(a, 3), dword(a, 2), dword(a, 1), dword(a, 0)
    W = [dword(b, 3), dword(b, 2), dword(b, 1), dword(b, 0)]
    E = 0                     # round 0: W0E already holds W0 + E
    for i in range(4):
        A, B, C, D, E = (sha1_f(sel, B, C, D) + rol(A, 5) + W[i] + E + SHA1_K[sel]) & M32, A, rol(B, 30), C, D
    return dwords(D, C, B, A)


def sha1nexte(a, b):
    return dwords(dword(b, 0), dword(b, 1), dword(b, 2), (dword(b, 3) + rol(dword(a, 3), 30)) & M32)


def sha1msg1(a, b):
    w0, w1, w2, w3 = dword(a, 3), dword(a, 2), dword(a, 1), dword(a, 0)
    w4, w5 = dword(b, 3), dword(b, 2)
    return dwords(w5 ^ w3, w4 ^ w2, w3 ^ w1, w2 ^ w0)


def sha1msg2(a, b):
    w13, w14, w15 = dword(b, 2), dword(b, 1), dword(b, 0)
    w16 = rol(dword(a, 3) ^ w13, 1)
    w17 = rol(dword(a, 2) ^ w14, 1)
    w18 = rol(dword(a, 1) ^ w15, 1)
    w19 = rol(dword(a, 0) ^ w16, 1)
    return dwords(w19, w18, w17, w16)


def S0(x): return ror(x, 2) ^ ror(x, 13) ^ ror(x, 22)
def S1(x): return ror(x, 6) ^ ror(x, 11) ^ ror(x, 25)
def s0(x): return ror(x, 7) ^ ror(x, 18) ^ (x >> 3)
def s1(x): return ror(x, 17) ^ ror(x, 19) ^ (x >> 10)
def Ch(e, f, g): return (e & f) ^ (~e & g & M32)
def Maj(a, b, c): return (a & b) ^ (a & c) ^ (b & c)


def sha256rnds2(a, b, x0):
    A, B, C, D = dword(b, 3), dword(b, 2), dword(a, 3), dword(a, 2)
    E, F, G, H = dword(b, 1), dword(b, 0), dword(a, 1), dword(a, 0)
    for wk in (dword(x0, 0), dword(x0, 1)):
        t = (Ch(E, F, G) + S1(E) + wk + H) & M32
        A, B, C, D, E, F, G, H = (t + Maj(A, B, C) + S0(A)) & M32, A, B, C, (t + D) & M32, E, F, G
    return dwords(F, E, B, A)


def sha256msg1(a, b):
    w = [dword(a, 0), dword(a, 1), dword(a, 2), dword(a, 3), dword(b, 0)]
    return dwords(*[(w[k] + s0(w[k + 1])) & M32 for k in range(4)])


def sha256msg2(a, b):
    w14, w15 = dword(b, 2), dword(b, 3)
    w16 = (dword(a, 0) + s1(w14)) & M32
    w17 = (dword(a, 1) + s1(w15)) & M32
    w18 = (dword(a, 2) + s1(w16)) & M32
    w19 = (dword(a, 3) + s1(w17)) & M32
    return dwords(w16, w17, w18, w19)


def _pad(msg):
    m = msg + b'\x80' + b'\0' * ((55 - len(msg)) % 64) + (8 * len(msg)).to_bytes(8, 'big')
    return [list(struct.unpack('>16I', m[k:k + 64])) for k in range(0, len(m), 64)]


def add32(a, b):
    return dwords(*[(dword(a, k) + dword(b, k)) & M32 for k in range(4)])


def sha1_insn(msg):
    """SHA-1 composed from SHA1RNDS4, SHA1NEXTE, SHA1MSG1, SHA1MSG2 (and PXOR/PADDD)."""
    abcd = dwords(0x10325476, 0x98BADCFE, 0xEFCDAB89, 0x67452301)
    e = 0xC3D2E1F0
    for w in _pad(msg):
        g = [dwords(w[4 * j + 3], w[4 * j + 2], w[4 * j + 1], w[4 * j]) for j in range(4)]
        for j in range(4, 20):
            g.append(sha1msg2(sha1msg1(g[j - 4], g[j - 3]) ^ g[j - 2], g[j - 1]))
        prev, cur = abcd, sha1rnds4(abcd, add32(g[0], e << 96), 0)
        for j in range(1, 20):
            prev, cur = cur, sha1rnds4(cur, sha1nexte(prev, g[j]), j // 5)
        e = dword(sha1nexte(prev, e << 96), 3)
        abcd = add32(cur, abcd)
    return b''.join(struct.pack('>I', v) for v in (dword(abcd, 3), dword(abcd, 2), dword(abcd, 1), dword(abcd, 0), e))


def _sha256_k():
    def icbrt(n):
        x = int(round(n ** (1 / 3)))
        while x ** 3 > n:
            x -= 1
        while (x + 1) ** 3 <= n:
            x += 1
        return x
    primes = [p for p in range(2, 312) if all(p % q for q in range(2, p))][:64]
    return [icbrt(p << 96) & M32 for p in primes]   # first 32 bits of the fractional cube roots


SHA256_K = _sha256_k()


def sha256_insn(msg):
    """SHA-256 composed from SHA256RNDS2, SHA256MSG1, SHA256MSG2 (and PADDD/PALIGNR/PSHUFD)."""
    h = [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]
    st0 = dwords(h[5], h[4], h[1], h[0])     # A B E F in dwords 3 2 1 0
    st1 = dwords(h[7], h[6], h[3], h[2])     # C D G H
    for w in _pad(msg):
        g = [dwords(*w[4 * j:4 * j + 4]) for j in range(4)]
        for j in range(4, 16):
            alignr = (g[j - 2] >> 32) | (dword(g[j - 1], 0) << 96)
            g.append(sha256msg2(add32(sha256msg1(g[j - 4], g[j - 3]), alignr), g[j - 1]))
        a, b = st0, st1
        for j in range(16):
            wk = add32(g[j], dwords(*SHA256_K[4 * j:4 * j + 4]))
            b = sha256rnds2(b, a, wk)
            a = sha256rnds2(a, b, wk >> 64)
        st0, st1 = add32(a, st0), add32(b, st1)
    out = [dword(st0, 3), dword(st0, 2), dword(st1, 3), dword(st1, 2), dword(st0, 1), dword(st0, 0),
           dword(st1, 1), dword(st1, 0)]
    return b''.join(struct.pack('>I', v) for v in out)

# ---------------------------------------------------------------------------------------------
# Instruction table: (map, mandatory prefix, opcode) -> name, and evaluation

FORMS = {
    (2, 0x66, 0xDB): 'aesimc', (2, 0x66, 0xDC): 'aesenc', (2, 0x66, 0xDD): 'aesenclast',
    (2, 0x66, 0xDE): 'aesdec', (2, 0x66, 0xDF): 'aesdeclast', (3, 0x66, 0xDF): 'aeskeygenassist',
    (3, 0x66, 0x44): 'pclmulqdq',
    (2, 0, 0xC8): 'sha1nexte', (2, 0, 0xC9): 'sha1msg1', (2, 0, 0xCA): 'sha1msg2',
    (2, 0, 0xCB): 'sha256rnds2', (2, 0, 0xCC): 'sha256msg1', (2, 0, 0xCD): 'sha256msg2',
    (3, 0, 0xCC): 'sha1rnds4',
}


def execute(name, a, b, x0=0, imm=0):
    """The destination after the instruction: a = destination (ModRM.reg), b = source (r/m),
    x0 = XMM0 (SHA256RNDS2), imm = imm8."""
    return {
        'aesimc': lambda: aesimc(b), 'aesenc': lambda: aesenc(a, b), 'aesenclast': lambda: aesenclast(a, b),
        'aesdec': lambda: aesdec(a, b), 'aesdeclast': lambda: aesdeclast(a, b),
        'aeskeygenassist': lambda: aeskeygenassist(b, imm), 'pclmulqdq': lambda: pclmulqdq(a, b, imm),
        'sha1nexte': lambda: sha1nexte(a, b), 'sha1msg1': lambda: sha1msg1(a, b),
        'sha1msg2': lambda: sha1msg2(a, b), 'sha256rnds2': lambda: sha256rnds2(a, b, x0),
        'sha256msg1': lambda: sha256msg1(a, b), 'sha256msg2': lambda: sha256msg2(a, b),
        'sha1rnds4': lambda: sha1rnds4(a, b, imm),
    }[name]()

# ---------------------------------------------------------------------------------------------
# Self-checks against the published vectors and hashlib

def selftest():
    """Returns a list of failure descriptions (empty: all passed)."""
    bad = []
    def check(what, got, want):
        if got != want:
            bad.append('%s: got %s want %s' % (what, got.hex() if isinstance(got, bytes) else hex(got),
                                               want.hex() if isinstance(want, bytes) else hex(want)))
    if SBOX[0x00] != 0x63 or SBOX[0x53] != 0xED or INV_SBOX[0x63] != 0x00:
        bad.append('sbox')
    pt = bytes.fromhex('00112233445566778899aabbccddeeff')
    for key, ct in [('000102030405060708090a0b0c0d0e0f', '69c4e0d86a7b0430d8cdb78070b4c55a'),
                    ('000102030405060708090a0b0c0d0e0f1011121314151617', 'dda97ca4864cdfe06eaf70a0ec0d7191'),
                    ('000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f',
                     '8ea2b7ca516745bfeafc49904b496089')]:
        k, c = bytes.fromhex(key), bytes.fromhex(ct)
        check('fips197 enc %d' % (8 * len(k)), aes_encrypt_block(k, pt), c)
        check('fips197 dec %d' % (8 * len(k)), aes_decrypt_block(k, c), pt)
        check('insn enc %d' % (8 * len(k)), aes_encrypt_insn(k, pt), c)
        check('insn dec %d' % (8 * len(k)), aes_decrypt_insn(k, c), pt)
    k = bytes.fromhex('2b7e151628aed2a6abf7158809cf4f3c')
    check('fips197 appendix B', aes_encrypt_insn(k, bytes.fromhex('3243f6a8885a308d313198a2e0370734')),
          bytes.fromhex('3925841d02dc09fbdc118597196a0b32'))
    rng = random.Random(1)
    for n in range(20):
        key = bytes(rng.getrandbits(8) for _ in range(rng.choice((16, 24, 32))))
        blk = bytes(rng.getrandbits(8) for _ in range(16))
        check('random enc', aes_encrypt_insn(key, blk), aes_encrypt_block(key, blk))
        check('random dec', aes_decrypt_insn(key, blk), aes_decrypt_block(key, blk))
    for msg in (b'', b'abc', b'abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq', b'a' * 1000,
                bytes(range(256)) * 3):
        check('sha1 %d' % len(msg), sha1_insn(msg), hashlib.sha1(msg).digest())
        check('sha256 %d' % len(msg), sha256_insn(msg), hashlib.sha256(msg).digest())
    # GCM test case 2 (zero key, IV, plaintext), with the AES and GHASH of this module
    zero = bytes(16)
    h = int.from_bytes(aes_encrypt_block(zero, zero), 'big')
    check('gcm H', h, 0x66e94bd4ef8a2c3b884cfa59ca342b2e)
    c = int.from_bytes(aes_encrypt_block(zero, bytes(15) + b'\x02'), 'big')
    check('gcm C', c, 0x0388dace60b6a392f328c2b971b2fe78)
    g = ghash(h, [c, 128])
    check('gcm GHASH', g, 0xf38cbb1ad69223dcc3457ae5b6b0f885)
    tag = int.from_bytes(aes_encrypt_block(zero, bytes(15) + b'\x01'), 'big') ^ g
    check('gcm tag', tag, 0xab6e47d42cec13bdf53a67b21257bddf)
    # PCLMULQDQ-composed GHASH multiplication equals the bitwise algorithm (blocks as XMM loads)
    for n in range(50):
        x, y = rng.getrandbits(128), rng.getrandbits(128)
        le = lambda v: int.from_bytes(v.to_bytes(16, 'big'), 'little')
        check('gfmul', gfmul_insn(le(x), le(y)), le(gcm_mul(x, y)))
        a, b = rng.getrandbits(64), rng.getrandbits(64)
        check('clmul comm', clmul(a, b), clmul(b, a))
    return bad

# ---------------------------------------------------------------------------------------------
# Table of random cases for t_crypto.c

def _interesting128(rng):
    k = rng.randrange(8)
    if k == 0:
        return 0
    if k == 1:
        return M128
    if k == 2:
        return 1 << rng.randrange(128)
    return rng.getrandbits(128)


def table(out, n=640, seed=20261111):
    rng = random.Random(seed)
    forms = sorted(FORMS.items())
    rows = []
    for k in range(n):
        (map_, pfx, op), name = forms[k % len(forms)]
        a, b, x0 = _interesting128(rng), _interesting128(rng), _interesting128(rng)
        imm = rng.getrandbits(8)
        r = execute(name, a, b, x0, imm)
        rows.append((map_, pfx, op, imm, a, b, x0, r, name))
    w = lambda v: ', '.join('0x%08x' % dword(v, j) for j in range(4))
    with open(out, 'w') as f:
        f.write('/* Generated by test/cryptoref.py table (seed %d): AES-NI, PCLMULQDQ and SHA cases with the\n'
                '   expected destination from the independent Python reference. Do not edit. */\n' % seed)
        f.write('static const struct ccase { u8 map, pfx, op, imm; u32 a[4], b[4], x0[4], r[4]; } ccases[] = {\n')
        for map_, pfx, op, imm, a, b, x0, r, name in rows:
            f.write('\t{ %d, 0x%02x, 0x%02x, 0x%02x, { %s }, { %s }, { %s }, { %s } }, /* %s */\n'
                    % (map_, pfx, op, imm, w(a), w(b), w(x0), w(r), name))
        f.write('};\n')

# ---------------------------------------------------------------------------------------------
# Checking QEMU's results of the gen_crypto.py vectors (test/run.sh)

DATA, DATA_SIZE, V2_HDR, V2_SIZE = 0x8000, 8192, 16, 96


def _xorshift(x):
    x ^= (x << 13) & M32
    x ^= x >> 17
    x ^= (x << 5) & M32
    return x


def vectors(vbin, vmeta, qout):
    """Each 'crypto-<name>:<reg>:<x<rm>|m<address>>:<hex>:<imm>' vector whose instruction completed under QEMU:
    QEMU's destination register must equal this reference applied to the initial state."""
    data = open(vbin, 'rb').read()
    metas = [l.rstrip('\n').split(' ', 1) for l in open(vmeta)]
    qlines = {}
    for line in open(qout, errors='replace'):
        f = line.split()
        if len(f) >= 87 and all(len(x) == 8 for x in f[:87]):
            qlines[int(f[0], 16)] = [int(x, 16) for x in f[:87]]
    checked = faulted = 0
    bad = []
    for idx, (_, desc) in enumerate(metas):
        if not desc.startswith('crypto-'):
            continue
        q = qlines.get(idx)
        if q is None:
            bad.append('#%d %s: no QEMU result' % (idx, desc))
            continue
        if q[1] not in (1, 3):          # a fault: the destination is not written
            faulted += 1
            continue
        name, reg, src, _, imm = desc[len('crypto-'):].split(':')[:5]
        reg, imm = int(reg), int(imm)
        o = V2_HDR + idx * V2_SIZE
        seed = struct.unpack_from('<I', data, o + 52)[0]
        s = seed ^ 0xA5A5A5A5
        pat = []
        for _ in range(64):
            s = _xorshift(s)
            pat.append(s)
        xmm = [sum(pat[4 * k + j] << (32 * j) for j in range(4)) for k in range(8)]
        if src.startswith('m'):
            ea = int(src[1:], 16)
            s, mem = seed, bytearray()
            for _ in range(DATA_SIZE // 4):
                s = _xorshift(s)
                mem += struct.pack('<I', s)
            poff = struct.unpack_from('<2H', data, o + 64)
            pval = struct.unpack_from('<2I', data, o + 68)
            for p, v in zip(poff, pval):
                if p != 0xFFFF:
                    mem[p:p + 4] = struct.pack('<I', v)
            b = int.from_bytes(mem[ea - DATA:ea - DATA + 16], 'little')
        else:
            b = xmm[int(src[1:])]
        want = execute(name, xmm[reg], b, xmm[0], imm)
        got = sum(q[23 + 4 * reg + j] << (32 * j) for j in range(4))
        checked += 1
        if got != want:
            bad.append('#%d %s: QEMU %032x reference %032x' % (idx, desc, got, want))
    for line in bad[:20]:
        print('cryptoref: ' + line)
    print('cryptoref: %d crypto vectors checked against the reference, %d faulted, %d differ'
          % (checked, faulted, len(bad)))
    return 1 if bad else 0


def main(argv):
    if len(argv) >= 1 and argv[0] == 'selftest':
        bad = selftest()
        for b in bad:
            print('FAIL ' + b)
        print('cryptoref selftest: %s' % ('ok' if not bad else '%d failures' % len(bad)))
        return 1 if bad else 0
    if len(argv) >= 2 and argv[0] == 'table':
        table(argv[1], *(int(x) for x in argv[2:4]))
        return 0
    if len(argv) == 4 and argv[0] == 'vectors':
        return vectors(*argv[1:])
    print(__doc__)
    return 2


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
