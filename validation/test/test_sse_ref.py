"""Known answers for sse_ref.py (examples of the AMD64 APM vol. 4 and simple identities), and, if a
system-test transcript exists (test/sys/out/model.txt), the reference check of its lines."""
import os
import struct
import unittest

import sse_ref as R

HERE = os.path.dirname(os.path.abspath(__file__))


def s128(text):
    b = text.encode().ljust(16, b'\0')
    return int.from_bytes(b, 'little')


def summ(bits):
    """APM notation: CmprSumm with the least significant bit on the left."""
    return sum(1 << k for k, c in enumerate(bits) if c == '1')


def f32(x):
    return struct.unpack('<I', struct.pack('<f', x))[0]


def f64(x):
    return struct.unpack('<Q', struct.pack('<d', x))[0]


class StringCompare(unittest.TestCase):
    """APM vol. 4, 1.5.3: the four CmprSumm examples (implicit lengths, unsigned bytes)."""

    def cmp(self, agg, proto, sut):
        a, b = s128(proto), s128(sut)
        return R.pcmpstr(agg << 2, a, b, len(proto), len(sut))

    def test_subset(self):
        self.assertEqual(self.cmp(0, 'ZCx', 'aCx%xbZreCx'), summ('0110101001100000'))

    def test_ranges(self):
        self.assertEqual(self.cmp(1, 'ACax', 'aCx%xbZreCx'), summ('1110110111100000'))

    def test_match(self):
        self.assertEqual(self.cmp(2, 'ZCx', 'aCx%xbZreCx'), summ('0110000000011111'))

    def test_substring(self):
        self.assertEqual(self.cmp(3, 'ZCx', 'aZCx%xCZreZCxCZ'), summ('0100000000100000'))

    def test_outputs(self):
        a, b = s128('ZCx'), s128('aCx%xbZreCx')
        ecx, _, fl = R.pcmpstr_full(0x63, 0x00, a, b, 0, 0)          # PCMPISTRI, least significant
        self.assertEqual(ecx, 1)
        self.assertEqual(fl, 0x1 | 0x40 | 0x80)                       # CF, ZF, SF; OF = bit 0 = 0
        ecx, _, _ = R.pcmpstr_full(0x63, 0x40, a, b, 0, 0)            # most significant
        self.assertEqual(ecx, 10)
        _, x0, _ = R.pcmpstr_full(0x62, 0x40, a, b, 0, 0)             # byte mask
        self.assertEqual(x0 & 0xFFFF, 0xFF00)
        ecx, _, fl = R.pcmpstr_full(0x61, 0x00, a, b, 0xFFFFFFFD, 0)  # |EAX| = 3, empty SUT
        self.assertEqual((ecx, fl), (16, 0x40 | 0x80))

    def test_explicit_length_saturates(self):
        self.assertEqual(R.explicit_len(0x80000000, 16), 16)
        self.assertEqual(R.explicit_len(0xFFFFFFF9, 8), 7)


class FloatingPoint(unittest.TestCase):
    def test_dpps(self):
        a = R.join([f32(x) for x in (1, 2, 3, 4)], 32)
        b = R.join([f32(x) for x in (5, 6, 7, 8)], 32)
        r, fl = R.dp(32, a, b, 0xF1, 0x1F80)
        self.assertEqual((r, fl), (f32(70), 0))
        r, fl = R.dp(32, a, b, 0x3C, 0x1F80)                          # products 0, 1 into lanes 2, 3
        self.assertEqual(r, R.join([0, 0, f32(17), f32(17)], 32))

    def test_dppd(self):
        a = R.join([f64(1.5), f64(-2)], 64)
        b = R.join([f64(2), f64(0.25)], 64)
        self.assertEqual(R.dp(64, a, b, 0x33, 0x1F80), (R.join([f64(2.5), f64(2.5)], 64), 0))

    def test_round(self):
        f = R.Fmt(32)
        cases = [(2.5, 0, 2.0, R.PE), (2.5, 1, 2.0, R.PE), (2.5, 2, 3.0, R.PE), (-2.5, 3, -2.0, R.PE),
                 (-0.3, 0, -0.0, R.PE), (7.0, 0, 7.0, 0), (1e30, 2, 1e30, 0)]
        for x, mode, want, fl in cases:
            self.assertEqual(R.round_lane(f, f32(x), mode, 0x1F80), (f32(want), fl), (x, mode))
        self.assertEqual(R.round_lane(f, f32(2.5), 8, 0x1F80), (f32(2.0), 0))      # PE suppressed
        self.assertEqual(R.round_lane(f, f32(2.5), 4, 0x5F80), (f32(3.0), R.PE))   # MXCSR.RC = up
        self.assertEqual(R.round_lane(f, 0x7F800001, 0, 0x1F80), (0x7FC00001, R.IE))
        self.assertEqual(R.round_lane(f, 0x00000001, 2, 0x1FC0), (0, 0))           # DAZ

    def test_hop(self):
        a = R.join([f32(1), f32(2), f32(3), f32(4)], 32)
        b = R.join([f32(5), f32(6), f32(7), f32(8)], 32)
        self.assertEqual(R.hop(32, False, a, b, 0x1F80), (R.join([f32(x) for x in (3, 7, 11, 15)], 32), 0))
        self.assertEqual(R.hop(32, True, a, b, 0x1F80), (R.join([f32(-1)] * 4, 32), 0))
        # two NaNs: HADD returns the higher element's (the first operand in both manuals), HSUB the lower's
        n = R.join([0x7FC00001, 0x7FC00002, 0x7F800003, 0x7FC00004], 32)
        self.assertEqual(R.lanes(R.hop(32, False, n, 0, 0x1F80)[0], 32)[:2], [0x7FC00002, 0x7FC00004])
        self.assertEqual(R.hop(32, False, n, 0, 0x1F80)[1], R.IE)
        self.assertEqual(R.lanes(R.hop(32, True, n, 0, 0x1F80)[0], 32)[:2], [0x7FC00001, 0x7FC00003])
        d = R.join([0x7FF8000000000001, 0x7FF8000000000002], 64)
        self.assertEqual(R.lanes(R.hop(64, False, d, 0, 0x1F80)[0], 64)[0], 0x7FF8000000000002)
        self.assertEqual(R.lanes(R.hop(64, True, d, 0, 0x1F80)[0], 64)[0], 0x7FF8000000000001)

    def test_arith(self):
        f = R.Fmt(32)
        self.assertEqual(R.arith(f, 'add', f32(1), f32(2 ** -24), 0x1F80), (f32(1), R.PE))
        self.assertEqual(R.arith(f, 'mul', 0x7F800000, 0, 0x1F80), (0xFFC00000, R.IE))
        self.assertEqual(R.arith(f, 'mul', f32(2 ** -100), f32(2 ** -40), 0x9F80), (0, R.UE | R.PE))  # FZ
        self.assertEqual(R.arith(f, 'add', f32(1), f32(-1), 0x3F80), (0x80000000, 0))  # RC down: -0


class Others(unittest.TestCase):
    def test_mpsadbw(self):
        a = int.from_bytes(bytes(range(16)), 'little')
        b = int.from_bytes(bytes([0] * 4 + [1, 1, 1, 1] + [0] * 8), 'little')
        self.assertEqual(R.lanes(R.mpsadbw(a, b, 1), 16)[0], 4)      # |0-1|+|1-1|+|2-1|+|3-1|
        self.assertEqual(R.lanes(R.mpsadbw(a, b, 0), 16), [k * 4 + 6 for k in range(8)])

    def test_sse4a(self):
        v = 0x0123456789ABCDEF
        self.assertEqual(R.extrq(v, 16, 32), 0x4567)                  # APM vol. 4 EXTRQ example
        self.assertEqual(R.extrq(v, 0, 0), v)                         # length 0 = 64
        self.assertEqual(R.insertq(0, 0xFFFF, 16, 32), 0x0000FFFF00000000)

    def test_fisttp(self):
        self.assertEqual(R.fisttp(0xBFFF, 0xC000000000000000, 4), (0xFFFFFFFF, R.PE))   # -1.5 -> -1
        self.assertEqual(R.fisttp(0x401E, 0x8000000000000000, 4), (0x80000000, R.IE))   # 2^31
        self.assertEqual(R.fisttp(0xC01E, 0x8000000000000000, 4), (0x80000000, 0))      # -2^31
        self.assertEqual(R.fisttp(0x7FFF, 0xC000000000000000, 2), (0x8000, R.IE))       # NaN


class Transcript(unittest.TestCase):
    def test_model_transcript(self):
        path = os.path.join(HERE, 'sys', 'out', 'model.txt')
        if not os.path.exists(path):
            self.skipTest('no system-test transcript (run test/sys/run.sh)')
        self.assertTrue(R.check(path))


if __name__ == '__main__':
    unittest.main()
