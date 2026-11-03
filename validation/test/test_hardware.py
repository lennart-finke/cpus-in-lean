"""The hardware gate must reject partial, duplicated, and altered evidence."""
import json
import contextlib
import io
import struct
import tempfile
import unittest
from unittest.mock import patch
from pathlib import Path

from hardware import directed_sse, digest, main, validate_output, verify_inputs


class HardwareGate(unittest.TestCase):
    def test_kvm_permission_failure_is_saved(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'manifest.json').write_text(json.dumps({'sha256': {}}))
            with patch('sys.argv', ['hardware.py', 'run', tmp]), \
                 patch('hardware.platform.system', return_value='Linux'), \
                 patch('hardware.platform.machine', return_value='x86_64'), \
                 patch('hardware.os.open', side_effect=PermissionError('KVM access denied')), \
                 contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(main(), 1)
            self.assertIn('KVM access denied', (root / 'run-error.txt').read_text())
            self.assertFalse((root / 'hardware.json').exists())

    def test_records_fail_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'reference'
            for arch, width, columns in [('i386', 8, 22), ('x86_64', 16, 58)]:
                rows = [' '.join(f'{x:0{width}x}' for x in [i] + [0] * (columns - 1)) for i in range(2)]
                good = [f'BEGIN {2:0{width}x}', *rows, 'END']
                path.write_text('\n'.join(good) + '\n')
                validate_output(path, 2, arch)
                for bad in [good[:-1], good[:2] + ['END'], [good[0], rows[0], rows[0], 'END'],
                            [good[0], rows[1], rows[0], 'END'], [good[0], rows[0] + ' 0', rows[1], 'END'],
                            [good[0], rows[0].replace('0', 'g'), rows[1], 'END']]:
                    path.write_text('\n'.join(bad) + '\n')
                    with self.assertRaises(ValueError):
                        validate_output(path, 2, arch)

    def test_changed_input_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / 'vectors.bin'
            source.write_bytes(b'original')
            manifest = {'sha256': {'vectors.bin': digest(source)}}
            verify_inputs(root, manifest)
            source.write_bytes(b'changed')
            with self.assertRaises(ValueError):
                verify_inputs(root, manifest)

    def test_directed_coverage(self):
        with tempfile.TemporaryDirectory() as tmp:
            prefix = Path(tmp) / 'vectors'
            prefix.with_suffix('.bin').write_bytes(b'')
            prefix.with_suffix('.json').write_text('[]')
            directed_sse(prefix)
            data = prefix.with_suffix('.bin').read_bytes()
            meta = json.loads(prefix.with_suffix('.json').read_text())
            self.assertEqual(len(data), 112 * 440)
            self.assertEqual([m['index'] for m in meta], list(range(112)))
            self.assertEqual(sum(m['family'] == 'hardware_daz_minmax' for m in meta), 64)
            unmasked = [struct.unpack_from('<I', data, i * 440 + 432)[0] for i in range(112)
                        if struct.unpack_from('<I', data, i * 440 + 432)[0] & 0x1f80 != 0x1f80]
            self.assertEqual(len(unmasked), 24)
            self.assertEqual({(~m & 0x1f80) >> 7 for m in unmasked}, {1 << bit for bit in range(6)})


if __name__ == '__main__':
    unittest.main()
