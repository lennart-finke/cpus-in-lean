"""The topology reference (topo_ref.py) reproduces the CPUID dump of a real EPYC 7742 (InstLatx64
AuthenticAMD0830F10_K17_Rome, socket 0) for its 128 threads."""
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import topo_ref  # noqa: E402


class TopoRef(unittest.TestCase):
    def test_dump_cpu0(self):
        e = topo_ref.expected(128, 0)
        self.assertEqual(e['l1ebx'], 0x00800800)
        self.assertEqual(e['b0'], (1, 2, 0x100, 0))
        self.assertEqual(e['b1'], (7, 0x80, 0x201, 0))
        self.assertEqual(e['c88'], 0x707F)
        self.assertEqual(e['e1e'], (0, 0x100, 0))

    def test_dump_last_thread(self):
        # APIC ID 7Fh: core 63, thread 1
        e = topo_ref.expected(128, 127)
        self.assertEqual(e['l1ebx'] >> 24, 0x7F)
        self.assertEqual(e['e1e'], (0x7F, 0x13F, 0))

    def test_linux(self):
        self.assertEqual(topo_ref.linux_expected(4, 3),
                         {'processor': 3, 'physical id': 0, 'siblings': 4, 'core id': 1, 'cpu cores': 2,
                          'apicid': 3, 'initial apicid': 3})


if __name__ == '__main__':
    unittest.main()
