"""Known answers for avx_ref.py (SDM/APM examples and identities), and, if a system-test transcript
exists (test/sys/out/model.txt), the reference check of its avxk lines."""
import os
import struct
import unittest

import avx_ref as R

HERE = os.path.dirname(os.path.abspath(__file__))


def f32(x):
    return struct.unpack('<I', struct.pack('<f', x))[0]


def v(*dwords):
    """A 256-bit value from dwords (dword 0 first)."""
    return R.pack(list(dwords), 32)


QNAN, SNAN = 0x7FC00000, 0x7FA00000
ONE, TWO = f32(1.0), f32(2.0)


class Compare(unittest.TestCase):
    """SDM vol. 2 CMPPS table 3-1: the result and the signaling behaviour of every predicate."""

    def test_ordered_values(self):
        # 1 < 2: EQ false, LT true, LE true, UNORD false, NEQ true, NLT false, NLE false, ORD true, ...
        expect = [0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1]
        for p in range(32):
            r, fl = R.compare(32, p, ONE, TWO, False)
            self.assertEqual(r != 0, bool(expect[p & 15]), p)
            self.assertEqual(fl, 0, p)

    def test_qnan(self):
        # unordered: true for UNORD, NEQ, NLT, NLE, EQ_UQ, NGE, NGT, TRUE; IE for the _S predicates
        true_unord = {3, 4, 5, 6, 8, 9, 10, 15}
        signaling = {1, 2, 5, 6, 9, 10, 13, 14, 16, 19, 20, 23, 24, 27, 28, 31}
        for p in range(32):
            r, fl = R.compare(32, p, QNAN, ONE, False)
            self.assertEqual(r != 0, (p & 15) in true_unord, p)
            self.assertEqual(fl, R.IE if p in signaling else 0, p)

    def test_snan_always_invalid(self):
        for p in range(32):
            self.assertEqual(R.compare(32, p, ONE, SNAN, False)[1], R.IE)

    def test_denormal(self):
        self.assertEqual(R.compare(32, 0, 1, ONE, False), (0, R.DE))
        self.assertEqual(R.compare(32, 0, 1, 0x80000000, True), (0xFFFFFFFF, 0))   # DAZ: +den == -0
        self.assertEqual(R.compare(64, 13, 0x7FF0000000000000, 0, False)[0], (1 << 64) - 1)   # inf >= 0

    def test_imm_high_bits_ignored(self):
        self.assertEqual(R.cmp_packed(1, 32, 0xE1, v(*[ONE] * 8), v(*[TWO] * 8), False),
                         R.cmp_packed(1, 32, 0x01, v(*[ONE] * 8), v(*[TWO] * 8), False))


class Permutes(unittest.TestCase):
    def test_permilps_reverse(self):
        s = v(0, 1, 2, 3, 4, 5, 6, 7)
        self.assertEqual(R.permilps_i(1, 0x1B, s), v(3, 2, 1, 0, 7, 6, 5, 4))
        self.assertEqual(R.permilps_i(0, 0x1B, s), v(3, 2, 1, 0))

    def test_permilps_variable_stays_in_lane(self):
        a = v(10, 11, 12, 13, 14, 15, 16, 17)
        self.assertEqual(R.permilps_v(1, a, v(7, 6, 5, 4, 3, 2, 1, 0)), v(13, 12, 11, 10, 17, 16, 15, 14))

    def test_permilpd(self):
        a = R.pack([1, 2, 3, 4], 64)
        self.assertEqual(R.permilpd_i(1, 0b0101, a), R.pack([2, 1, 4, 3], 64))
        self.assertEqual(R.permilpd_v(1, a, R.pack([2, 0, 0, 2], 64)), R.pack([2, 1, 3, 4], 64))

    def test_perm2f128(self):
        a, b = R.halves(1, 2), R.halves(3, 4)
        self.assertEqual(R.perm2f128(0x31, a, b), R.halves(2, 4))
        self.assertEqual(R.perm2f128(0x08, a, b), R.halves(0, 1))

    def test_shuf_unpck(self):
        a, b = v(0, 1, 2, 3, 4, 5, 6, 7), v(10, 11, 12, 13, 14, 15, 16, 17)
        self.assertEqual(R.shufps(1, 0x4E, a, b), v(2, 3, 10, 11, 6, 7, 14, 15))
        self.assertEqual(R.unpcklps(1, a, b), v(0, 10, 1, 11, 4, 14, 5, 15))


class Moves(unittest.TestCase):
    def test_maskmov(self):
        mask = v(0x80000000, 0, 0x80000000, 0, 0, 0, 0, 0x80000000)
        m = v(1, 2, 3, 4, 5, 6, 7, 8)
        self.assertEqual(R.maskload(1, 32, mask, m), v(1, 0, 3, 0, 0, 0, 0, 8))
        self.assertEqual(R.maskload(0, 32, mask, m), v(1, 0, 3, 0))
        self.assertEqual(R.maskstore(0, 32, mask, v(*[9] * 8), m), v(9, 2, 9, 4, 5, 6, 7, 8))

    def test_tests(self):
        self.assertEqual(R.test_flags(1, 32, v(0x80000000), v(0x80000000)), (False, True))
        self.assertEqual(R.test_flags(0, 1, 0, R.halves(0, 1)), (True, True))   # VEX.128 ignores bits 255:128

    def test_mutation_detected(self):
        line = ('avxk 0 movsldup l=1 d=%064x b=%064x -> vec=0000ffff r=%064x fl=00000000 mx=00001f80' %
                (0, v(0, 1, 2, 3, 4, 5, 6, 7), v(0, 0, 2, 2, 4, 4, 6, 6)))
        self.assertEqual(R.check_line(line), [])
        self.assertTrue(R.check_line(line.replace('r=0', 'r=1', 1)))


class Transcript(unittest.TestCase):
    def test_model_transcript(self):
        path = os.path.join(HERE, 'sys', 'out', 'model.txt')
        if not os.path.exists(path):
            self.skipTest('no system-test transcript (run test/sys/run.sh)')
        with open(path, errors='replace') as fh:
            if not any(l.startswith('avxk') for l in fh):
                self.skipTest('no avxk lines')
        self.assertTrue(R.check(path))


if __name__ == '__main__':
    unittest.main()
