"""Coverage and input-integrity gates for the next physical-CPU campaign."""
import collections
import hashlib
import struct
import unittest

from native import register_only
from native_cases import focused_sse, saved_nan_case


class FocusedCoverage(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cases = list(focused_sse())

    def test_complete_control_matrix_and_record_layout(self):
        matrix = collections.defaultdict(set)
        for record, meta in self.cases:
            self.assertEqual(len(record), 440)
            self.assertEqual(record[1:1+record[0]].hex(), meta['code'])
            self.assertTrue(register_only(bytes.fromhex(meta['code']), 'x86_64', meta['family']))
            mxcsr = struct.unpack_from('<I', record, 432)[0]
            self.assertEqual(mxcsr, meta['mxcsr'])
            self.assertEqual((mxcsr >> 7) & 63, meta['exception_masks'])
            self.assertEqual(mxcsr & 63, meta['sticky'])
            if meta['family'] == 'hardware_sse_matrix':
                matrix[meta['format'], meta['scenario']].add(
                    (meta['exception_masks'], meta['rounding'], meta['daz'], meta['ftz']))
        expected = {(m,r,d,f) for m in range(64) for r in range(4)
                    for d in (False,True) for f in (False,True)}
        self.assertEqual(len(matrix), 4*12)
        self.assertTrue(all(settings == expected for settings in matrix.values()))

    def test_directed_groups_and_mixed_lane_inputs(self):
        counts = collections.Counter(m['family'] for _,m in self.cases)
        self.assertEqual(counts, {'hardware_sse_matrix':49152, 'hardware_sse_sticky':7680,
                                 'hardware_sse_boundary':5120, 'hardware_sse_lane_priority':1152,
                                 'hardware_sse_nan_payload':1536})
        mixed = [(r,m) for r,m in self.cases if m['family']=='hardware_sse_matrix'
                 and m['scenario']=='mixed_denormal_overflow' and m['format']=='pd']
        for record, meta in mixed:
            code = bytes.fromhex(meta['code'])
            dst = 14 if 0x45 in code else 0
            left = struct.unpack_from('<2Q', record, 176+16*dst)
            right = struct.unpack_from('<2Q', record, 176+16*(dst+1))
            self.assertEqual(left, (1,0x7fefffffffffffff))
            self.assertEqual(right, (0x3ff0000000000000,0x7fefffffffffffff))

    def test_saved_nan_case_is_exact_reproducer(self):
        record, meta = saved_nan_case()
        self.assertEqual(len(record), 440)
        self.assertEqual(hashlib.sha256(record).hexdigest(), meta['original_record_sha256'])
        self.assertEqual(record[1:1+record[0]], bytes.fromhex('450f5ef7'))
        self.assertEqual(struct.unpack_from('<I', record, 176+16*14)[0], 0x7fc00123)
        self.assertEqual(struct.unpack_from('<I', record, 176+16*15)[0], 0x7fd85edf)
        self.assertEqual(struct.unpack_from('<I', record, 432)[0], 0x7fc0)


if __name__ == '__main__':
    unittest.main()
