"""CPUID of the model against the dump of a real EPYC 7742 (cpuid_table.py check): no invented bit,
every dump bit reported or masked with a reason, x86_32/CPUID.md up to date."""
import os
import subprocess
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cpuid_table  # noqa: E402


class CpuidTable(unittest.TestCase):
    def test_dump_parses(self):
        d = cpuid_table.parse_dump()
        self.assertEqual(d[(0, None)], (0x10, 0x68747541, 0x444D4163, 0x69746E65))
        self.assertEqual(d[(0xD, 9)][0], 0x40)

    def test_model_against_dump(self):
        if not os.path.exists(cpuid_table.X86RUN):
            self.skipTest('validation/.lake/build/bin/x86run not built (lake build x86run)')
        r = subprocess.run([sys.executable, os.path.join(HERE, 'cpuid_table.py'), 'check'],
                           capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)


if __name__ == '__main__':
    unittest.main()
