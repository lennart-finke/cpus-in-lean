"""vmeref.py (CR4.VME/PVI reference, test/sys): its known-answer self-test, a few hand-checked cases
from the AMD APM, and that the committed case table is what the reference generates."""
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'sys'))
import vmeref as V  # noqa: E402

IF, IOPL, VM, VIF, VIP, TF, RF = V.IF, V.IOPL, V.VM, V.VIF, V.VIP, V.TF, V.RF


def case(mode, op, efl, cr4=1, n=0, irb=0, win=None):
    return V.Case(mode, V.OPN.index(op), n, cr4, irb, efl | 2, win or bytes(V.WIN))


class Vme(unittest.TestCase):
    def test_selftest(self):
        V.selftest()

    def test_popf_vip_if(self):
        # POPF (VME, IOPL < 3) popping IF = 1 while VIP = 1: #GP(0), nothing changes
        w = bytearray(V.WIN)
        w[8], w[9] = 0x02, 0x02          # FLAGS image with IF
        r = V.run(case(0, 'popf', VM | VIP, win=w))
        self.assertEqual(r[:3], (13, 0, 0))
        self.assertEqual(r[5], V.SP0)

    def test_popf_tf(self):
        w = bytearray(V.WIN)
        w[8], w[9] = 0x02, 0x01          # TF
        self.assertEqual(V.run(case(0, 'popf', VM, win=w))[:3], (13, 0, 0))

    def test_popf_vif(self):
        # the popped IF goes to VIF; IF and IOPL are unchanged
        w = bytearray(V.WIN)
        w[8], w[9] = 0x02, 0x32          # IF | IOPL = 3 in the image
        r = V.run(case(0, 'popf', VM | IF, win=w))
        self.assertEqual(r[4] & (IF | IOPL | VIF), IF | VIF)

    def test_pushfd_gp(self):
        self.assertEqual(V.run(case(0, 'pushfd', VM | VIF))[:3], (13, 0, 0))

    def test_int_irb_set(self):
        # VME, IOPL < 3, redirection bit set: #GP(0)
        self.assertEqual(V.run(case(0, 'int', VM, n=0x21, irb=1))[:3], (13, 0, 0))

    def test_int_iopl3_redirect(self):
        # IOPL = 3, bit clear: redirected; IF cleared, the image has the real IF
        r = V.run(case(0, 'int', VM | IF | IOPL, n=0x10, irb=0))
        self.assertEqual((r[3], r[2]), (V.LAND_CS, 0x10))
        self.assertEqual(r[4] & IF, 0)
        self.assertEqual(r[6][2 + 4] | r[6][3 + 4] << 8, (IF | IOPL | 2))

    def test_pvi_sti_vip(self):
        self.assertEqual(V.run(case(1, 'sti', VIP, cr4=2))[:3], (13, 0, 0))

    def test_pvi_popf_no_if(self):
        # POPF at CPL 3 with IOPL < 3 ignores IF, also with PVI
        w = bytearray(V.WIN)
        w[8], w[9] = 0x02, 0x02
        r = V.run(case(1, 'popfd', 0, cr4=2, win=w))
        self.assertEqual(r[4] & (IF | VIF), 0)

    def test_table_current(self):
        with open(os.path.join(HERE, 'sys', 'vme_cases.h')) as f:
            self.assertEqual(f.read(), V.table(800, 1))


if __name__ == '__main__':
    unittest.main()
