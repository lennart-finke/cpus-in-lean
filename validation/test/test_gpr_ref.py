"""Tests of the independent GPR-extension reference (gpr_ref.py) and, when the runner is built,
of the model against it."""
import os
import unittest

import gpr_ref as R


class Reference(unittest.TestCase):
    def test_crc32c_check_value(self):
        # CRC-32C ("Castagnoli") check value of "123456789": E3069283h (RFC 3720 appendix B.4 uses
        # the same polynomial); the instruction does not invert, so start with ~0 and invert at the end
        crc = 0xFFFFFFFF
        for b in b'123456789':
            crc = R.crc32(crc, b, 8)
        self.assertEqual(crc ^ 0xFFFFFFFF, 0xE3069283)

    def test_crc32_widths_agree(self):
        # one 32-bit step equals four byte steps, least significant byte first
        for v, c in ((0x12345678, 0), (0xFFFFFFFF, 0xDEADBEEF), (0x80000001, 0x1)):
            b = c
            for k in range(4):
                b = R.crc32(b, (v >> 8 * k) & 0xFF, 8)
            self.assertEqual(R.crc32(c, v, 32), b)

    def test_rfc3720_zeros(self):
        # RFC 3720 B.4: 32 bytes of zeros -> CRC 8A9136AA
        crc = 0xFFFFFFFF
        for _ in range(32):
            crc = R.crc32(crc, 0, 8)
        self.assertEqual(crc ^ 0xFFFFFFFF, 0x8A9136AA)

    def test_pdep_pext(self):
        # SDM PDEP/PEXT examples (vol. 2B, figures "PDEP Example" / "PEXT Example")
        self.assertEqual(R.pdep(0b1011, 0b11110000), 0b10110000)
        self.assertEqual(R.pext(0b10110000, 0b11110000), 0b1011)
        for m in (0, 0xFFFFFFFF, 0x0F0F0F0F, 0x80000001):
            for x in (0, 0x12345678, 0xFFFFFFFF):
                self.assertEqual(R.pext(R.pdep(x, m), m), x & ((1 << bin(m).count('1')) - 1))
        self.assertEqual(R.pdep(0x12345678, 0xFFFFFFFF), 0x12345678)

    def test_counts(self):
        self.assertEqual(R.lzcnt(0, 32), 32)
        self.assertEqual(R.tzcnt(0, 16), 16)
        self.assertEqual(R.lzcnt(1, 16), 15)
        self.assertEqual(R.tzcnt(0x80000000, 32), 31)
        self.assertEqual(R.popcnt(0xFFFF, 16), 16)

    def test_bextr_bzhi(self):
        self.assertEqual(R.bextr(0xFFF << 7, 7 | (5 << 8)), 0x1F)   # APM: bits 11:7 to 4:0
        self.assertEqual(R.bextr(0xFFFFFFFF, 30 | (8 << 8)), 3)      # zeros beyond bit 31
        self.assertEqual(R.bextr(0x12345678, 4 | (0 << 8)), 0)       # length 0
        self.assertEqual(R.bzhi(0xFFFFFFFF, 40), 0xFFFFFFFF)
        self.assertEqual(R.bzhi(0xFFFFFFFF, 0x104), 0xF)             # only bits 7:0 count

    def test_splitmix64(self):
        # first outputs of SplitMix64 from state 0 (published test value E220A8397B1DCDAF)
        self.assertEqual(R.splitmix64(0)[1], 0xE220A8397B1DCDAF)


@unittest.skipUnless(os.path.exists(R.X86TEST), 'x86test not built (lake build x86test)')
class Model(unittest.TestCase):
    def test_model_matches_reference(self):
        bad, total = R.check(60, 7)
        self.assertEqual(bad, [], '%d of %d cases differ' % (len(bad), total))


if __name__ == '__main__':
    unittest.main()
