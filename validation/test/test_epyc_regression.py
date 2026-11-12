"""The saved EPYC 7742 hardware observations (fixtures/native_epyc_fixes.json) agree with the model."""
import contextlib
import io
import unittest

import epyc_regression


class EpycRegression(unittest.TestCase):
    def test_hardware_cases(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            status = epyc_regression.main()
        self.assertEqual(status, 0, out.getvalue()[-3000:])


if __name__ == '__main__':
    unittest.main()
