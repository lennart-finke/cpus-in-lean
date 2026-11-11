"""Known answers for avx2_ref.py (IEEE 754 binary16 values, the SDM's FMA table, Python's own
math.fma and struct 'e' conversions as independent oracles), and, if a system-test transcript exists
(test/sys/out/model.txt), the reference check of its avx2k/avx2g lines and of the avx2m lines of
model-only.expected."""
import math
import os
import random
import struct
import unittest

import avx2_ref as R

HERE = os.path.dirname(os.path.abspath(__file__))


def f64(x):
    return struct.unpack('<Q', struct.pack('<d', x))[0]


def d64(b):
    return struct.unpack('<d', struct.pack('<Q', b))[0]


def f32(x):
    return struct.unpack('<I', struct.pack('<f', x))[0]


class Half(unittest.TestCase):
    def test_known_values(self):
        for h, x in ((0x3C00, 1.0), (0x7BFF, 65504.0), (0x0001, 2.0 ** -24), (0x0400, 2.0 ** -14),
                     (0xC000, -2.0), (0x3555, 0.333251953125)):
            self.assertEqual(R.half_to_single(h), (f32(x), 0))
            self.assertEqual(R.single_to_half(f32(x), 0, 0x1F80), (h, 0))

    def test_nan_and_inf(self):
        self.assertEqual(R.half_to_single(0x7C00), (0x7F800000, 0))
        self.assertEqual(R.half_to_single(0x7D01), (0x7FE02000, R.IE))       # SNaN quieted, payload << 13
        self.assertEqual(R.single_to_half(0xFFA00001, 0, 0x1F80), (0xFF00, R.IE))
        self.assertEqual(R.single_to_half(f32(65520.0), 0, 0x1F80), (0x7C00, R.OE | R.PE))   # ties away from max
        self.assertEqual(R.single_to_half(f32(65520.0), 3, 0x1F80), (0x7BFF, R.PE))     # truncated: no overflow
        self.assertEqual(R.single_to_half(f32(2.0 ** -25), 0, 0x9F80), (0x0000, R.UE | R.PE))   # FTZ ignored, tie to even
        self.assertEqual(R.single_to_half(f32(2.0 ** -25), 2, 0x9F80), (0x0001, R.UE | R.PE))
        self.assertEqual(R.single_to_half(0x00000001, 2, 0x1F80), (0x0001, R.DE | R.UE | R.PE))
        self.assertEqual(R.single_to_half(0x00000001, 2, 0x1FC0), (0x0000, 0))                 # DAZ

    def test_round_trip_all(self):
        """ph -> ps -> ph is the identity for every non-SNaN binary16 value (an SNaN comes back quiet)."""
        for h in range(65536):
            s, _ = R.half_to_single(h)
            back, fl = R.single_to_half(s, 0, 0x1F80)
            want = h | 0x200 if R.F16.issnan(h) else h
            self.assertEqual((back, fl), (want, 0), hex(h))

    def test_struct_e(self):
        """Round to nearest-even against Python's binary16 packing (struct 'e')."""
        rnd = random.Random(7)
        for _ in range(20000):
            x = rnd.getrandbits(32)
            if R.F32.isnan(x) or (x >> 23) & 0xFF == 0:
                continue
            v = struct.unpack('<f', struct.pack('<I', x))[0]
            try:
                want = struct.unpack('<H', struct.pack('<e', v))[0]
            except OverflowError:
                continue
            self.assertEqual(R.single_to_half(x, 0, 0x1F80)[0], want, hex(x))


class Fma(unittest.TestCase):
    def test_math_fma(self):
        """binary64 FMA in round to nearest against math.fma (Python 3.13+), finite operands."""
        if not hasattr(math, 'fma'):
            self.skipTest('no math.fma')
        rnd = random.Random(11)
        for _ in range(20000):
            ops = []
            for _ in range(3):
                e = rnd.choice([rnd.randint(1, 2046), rnd.randint(1000, 1046), rnd.randint(1, 40), 0])
                ops.append(rnd.getrandbits(1) << 63 | e << 52 | rnd.getrandbits(52))
            x, y, z = ops
            if rnd.random() < 0.2:
                z = f64(-d64(x) * d64(y)) if not math.isinf(d64(x) * d64(y)) else z   # near cancellation
            try:
                want = math.fma(d64(x), d64(y), d64(z))
            except (OverflowError, ValueError):
                continue
            if math.isnan(want):
                continue
            got, _ = R.fma(R.F64, x, y, z, 0, 0, 0x1F80)
            self.assertEqual(got, f64(want), (hex(x), hex(y), hex(z)))

    def test_sdm_table(self):
        """SDM vol. 1 table 14-17: 0 * inf is invalid unless z is a NaN (then Q(z), IE only for SNaN);
        the first NaN of x, y, z is returned."""
        f, one, inf, q, s = R.F32, f32(1.0), 0x7F800000, 0x7FC00001, 0x7F800002
        self.assertEqual(R.fma(f, 0, inf, one, 0, 0, 0x1F80), (f.indefinite(), R.IE))
        self.assertEqual(R.fma(f, inf, 0, q, 0, 0, 0x1F80), (q, 0))
        self.assertEqual(R.fma(f, inf, 0, s, 0, 0, 0x1F80), (s | f.quiet, R.IE))
        self.assertEqual(R.fma(f, one, 0x7FC00005, q, 0, 0, 0x1F80), (0x7FC00005, 0))
        self.assertEqual(R.fma(f, 0x7FC00007, s, q, 0, 0, 0x1F80), (0x7FC00007, R.IE))
        self.assertEqual(R.fma(f, inf, one, 0xFF800000, 0, 0, 0x1F80), (f.indefinite(), R.IE))
        self.assertEqual(R.fma(f, inf, one, 0xFF800000, 1, 0, 0x1F80), (0xFF800000, 0))     # -(inf) + -inf
        self.assertEqual(R.fma(f, q, one, one, 1, 1, 0x1F80), (q, 0))                       # no sign flip of NaNs

    def test_signed_zero(self):
        f, one = R.F32, f32(1.0)
        self.assertEqual(R.fma(f, one, one, 0xBF800000, 0, 0, 0x1F80), (0, 0))              # +0
        self.assertEqual(R.fma(f, one, one, 0xBF800000, 0, 0, 0x3F80), (0x80000000, 0))     # round down: -0
        self.assertEqual(R.fma(f, 0x80000000, one, 0x80000000, 0, 0, 0x1F80), (0x80000000, 0))
        self.assertEqual(R.fma(f, 0x80000000, one, 0, 0, 0, 0x1F80), (0, 0))

    def test_single_rounding(self):
        """(1 + 2^-23)(1 - 2^-23) - 1 = -2^-46 exactly: a separate multiply would round to 0."""
        f = R.F32
        self.assertEqual(R.fma(f, f32(1 + 2 ** -23), f32(1 - 2 ** -23), 0xBF800000, 0, 0, 0x1F80),
                         (f32(-2.0 ** -46), 0))

    def test_ftz_daz(self):
        f, tiny = R.F32, 0x00800000                        # smallest normal
        half = f32(0.5)
        self.assertEqual(R.fma(f, tiny, half, 0, 0, 0, 0x1F80), (0x00400000, 0))            # exact denormal
        self.assertEqual(R.fma(f, tiny, half, 0, 0, 0, 0x9F80), (0, R.UE | R.PE))            # FTZ
        self.assertEqual(R.fma(f, 0x00400000, f32(2.0), 0, 0, 0, 0x1F80), (tiny, R.DE))
        self.assertEqual(R.fma(f, 0x00400000, f32(2.0), 0, 0, 0, 0x1FC0), (0, 0))            # DAZ


class Mutation(unittest.TestCase):
    def test_detected(self):
        line = ('avx2k 0 vpermq l=1 w=1 mx=00001f80 imm=1b d=%064x b=%064x -> vec=0000ffff r=%064x mx=00001f80' %
                (0, R.pack([1, 2, 3, 4], 64), R.pack([4, 3, 2, 1], 64)))
        self.assertIsNone(R.check_line(line))
        self.assertTrue(R.check_line(line.replace('r=0', 'r=1', 1)))


class Transcript(unittest.TestCase):
    def test_model_transcript(self):
        paths = [p for p in (os.path.join(HERE, 'sys', 'out', 'model.txt'),) if os.path.exists(p)]
        if not paths:
            self.skipTest('no system-test transcript (run test/sys/run.sh)')
        self.assertTrue(R.check(paths))

    def test_model_only_expected(self):
        self.assertTrue(R.check([os.path.join(HERE, 'sys', 'model-only.expected')]))


if __name__ == '__main__':
    unittest.main()
