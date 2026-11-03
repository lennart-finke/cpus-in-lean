"""Model regressions for RMW fault intent, fault priority, and read-only controls.

Build x86test and x64test first. Run with --out pointing to a new evidence directory.
The expected faults and initial-memory hashes are independent of the models.
"""
import argparse
import itertools
import json
import struct
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
IP = 0x20100


def initial_hashes():
    data = bytearray()
    state = 1
    for _ in range(2048):
        state ^= (state << 13) & 0xffffffff
        state ^= state >> 17
        state ^= (state << 5) & 0xffffffff
        data.extend(struct.pack('<I', state))

    def fnv(data, bits, basis, prime):
        result = basis
        for byte in data:
            result = ((result ^ byte) * prime) & ((1 << bits) - 1)
        return result

    return [fnv(data, 32, 2166136261, 16777619)] + [
        fnv(data[k:k+4096], 64, 14695981039346656037, 1099511628211)
        for k in (0, 4096)]


def cases(arch):
    # All operands use [EBX/RBX]. CL=1 also supplies the bit index and shift count.
    operations = [
        ('add', '0103', True), ('add_imm', '830301', True),
        ('neg', 'f71b', True), ('not', 'f713', True),
        ('inc', 'ff03', True), ('dec', 'ff0b', True),
        ('xadd', '0fc10b', True), ('cmpxchg', '0fb10b', True),
        ('xchg', '870b', True), ('shl', 'd323', True),
        ('shl_zero', 'c12300', True), ('shld', '0fa40b01', True),
        ('shrd_zero', '0fac0b00', True),
        ('bts', '0fab0b', True), ('btr', '0fb30b', True), ('btc', '0fbb0b', True),
        ('cmp', '3903', False), ('cmp_imm', '833b01', False),
        ('test', '8503', False), ('test_imm', 'f70301000000', False),
        ('bt', '0fa30b', False), ('load', '8b03', False),
    ]
    expanded = []
    for width in ((2, 4) if arch == 'i386' else (2, 4, 8)):
        for name, code, write in operations:
            if name == 'test_imm' and width == 2:
                code = 'f7030100'
            expanded.append((name, (b'\x66' if width == 2 else b'\x48' if width == 8 else b'')
                             + bytes.fromhex(code), width, write))
    expanded.append(('cmpxchg8b', bytes.fromhex('0fc70b'), 8, True))
    # Crossing and non-crossing accesses distinguish error-code intent from priority.
    for (name, code, width, write), address, permissions in itertools.product(
            expanded, (0x10000, 0x10fff), itertools.product(('rw', 'r', 'none'), repeat=2)):
        regs = [0x12345678, 1, 0, address, 0x10800] + [0] * 11
        ptes = [{'rw': 0x67, 'r': 0x65, 'none': 0}[p] for p in permissions]
        fault = None
        for page, at in [(0, address)] + ([(1, 0x11000)] if address + width > 0x11000 else []):
            if permissions[page] == 'none' or (write and permissions[page] == 'r'):
                fault = [14, 4 + 2 * write + (permissions[page] != 'none'), at]
                break
        if arch == 'i386':
            record = struct.pack('<B15s8III4H2H2I3I', len(code), code.ljust(15, b'\0'),
                                 *regs[:8], 0x202, 1, *([0x23] * 4), 0xffff, 0xffff,
                                 0, 0, 3, *ptes)
        else:
            record = struct.pack('<16s16QQII2Q32QII', bytes([len(code)]) + code.ljust(15, b'\0'),
                                 *regs, 0x202, 1, 1, *ptes, *([0] * 32), 0x1f80, 0)
        yield record, dict(name=name, code=code.hex(), width=width, address=address,
                           permissions=permissions, write=write, fault=fault, regs=regs)


def run(out):
    out.mkdir(parents=True, exist_ok=False)
    hashes = initial_hashes()
    summary = {}
    for arch in ('i386', 'x86_64'):
        dest = out / arch
        dest.mkdir()
        records, metadata = zip(*cases(arch))
        (dest / 'vectors.bin').write_bytes(b''.join(records))
        (dest / 'cases.json').write_text(json.dumps(metadata, indent=2) + '\n')
        exe = ROOT / ('.lake/build/bin/x86test' if arch == 'i386'
                      else '../x86_64/.lake/build/bin/x64test')
        result = subprocess.run([exe, '--native-memory', dest / 'vectors.bin'],
                                check=True, capture_output=True, text=True, timeout=120)
        (dest / 'model.out').write_text(result.stdout)
        lines = result.stdout.splitlines()
        assert lines[0].split() == ['BEGIN', f'{len(records):0{8 if arch == "i386" else 16}x}']
        assert lines[-1] == 'END' and len(lines) == len(records) + 2
        failures = []
        for index, (meta, line) in enumerate(zip(metadata, lines[1:-1])):
            row = [int(x, 16) for x in line.split()]
            assert len(row) == (26 if arch == 'i386' else 60) and row[0] == index
            got = [row[1], row[2], row[19 if arch == 'i386' else 21]]
            faults = meta['fault'] is not None
            errors = []
            if faults and got != meta['fault']:
                errors.append(f'fault {got} != {meta["fault"]}')
            if not faults and row[1] != 3:
                errors.append(f'expected completion, got vector {row[1]}')
            if row[3] != IP + (0 if faults else len(bytes.fromhex(meta['code']))):
                errors.append('wrong restart/completion IP')
            if faults:
                nregs = 8 if arch == 'i386' else 16
                if row[4:4+nregs] != meta['regs'][:nregs] or row[4+nregs] & 0xdd5:
                    errors.append('fault changed registers or defined flags')
            if faults or not meta['write']:
                actual = ([row[18], row[22] | row[23] << 32, row[24] | row[25] << 32]
                          if arch == 'i386' else [row[22], row[58], row[59]])
                if actual != hashes:
                    errors.append('fault/read-only instruction changed data memory')
            if errors:
                failures.append(dict(index=index, **meta, errors=errors))
        (dest / 'failures.json').write_text(json.dumps(failures, indent=2) + '\n')
        summary[arch] = dict(count=len(records), failures=len(failures))
        print(arch, summary[arch])
    (out / 'regression.json').write_text(json.dumps(summary, indent=2) + '\n')
    return int(any(result['failures'] for result in summary.values()))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    raise SystemExit(run(parser.parse_args().out.resolve()))
