"""The SVM reference (test/sys/svmref.py): its self-test, and that sys/svm_cases.h is its output."""
import io
import os
import sys
import unittest
from contextlib import redirect_stdout

sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'sys'))
import svmref  # noqa: E402


class SvmRef(unittest.TestCase):
    def test_selftest(self):
        out = io.StringIO()
        with redirect_stdout(out):
            svmref.selftest()
        self.assertIn('ok', out.getvalue())

    def test_table_is_current(self):
        path = os.path.join(os.path.dirname(__file__), 'sys', 'svm_cases.h')
        with open(path) as f:
            self.assertEqual(f.read(), svmref.table(400, 400, 1))

    def test_npf_spot(self):
        # a nested reserved bit (PAE nested tables, bit 52) in the final page: RSV and P set
        c = dict(hmode=2, gmode=0, wp=0, nxe=0, cpl=0, acc=0, pg=2, ntab=7, npde=7, gpde=7,
                 npte=[7, 7, 0x47, 7, 7, 7, 7, 7], gpte=[7] * 8)
        self.assertEqual(svmref.expect_npf(c)[:4], (0x400, 0xD, 1, svmref.GPA0 + 0x2000))


if __name__ == '__main__':
    unittest.main()
