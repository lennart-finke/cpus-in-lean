#!/usr/bin/env python3
"""Small, strict ELF64 linker for this freestanding test harness.

Accepts only the relocation kinds emitted by clang for these sources. All symbol
references and relocation ranges are checked. QEMU loads the resulting ELF image;
the Lean model never calls this tool to execute instructions.
"""
import struct
import sys
from pathlib import Path

BASE = 0x100000

def align(n, a):
    return (n + a - 1) & -a

def link(inputs, output):
    objects, symbols, sections = [], {}, []
    pos = BASE
    for name in inputs:
        data = Path(name).read_bytes()
        if data[:6] != b'\x7fELF\x02\x01':
            raise ValueError(f'{name}: expected little-endian ELF64')
        hdr = struct.unpack_from('<16sHHIQQQIHHHHHH', data)
        if hdr[1:3] != (1, 62):
            raise ValueError(f'{name}: expected x86-64 relocatable ELF')
        sh = [struct.unpack_from('<IIQQQQIIQQ', data, hdr[6] + k * hdr[11]) for k in range(hdr[12])]
        obj = {'data': data, 'sh': sh, 'where': {}, 'syms': {}}
        objects.append(obj)
        for k, sec in enumerate(sh):
            if sec[2] & 2:
                pos = align(pos, max(sec[8], 1))
                obj['where'][k] = pos
                payload = bytearray(sec[5]) if sec[1] == 8 else bytearray(data[sec[4]:sec[4]+sec[5]])
                sections.append((pos, payload))
                pos += sec[5]
        for k, sec in enumerate(sh):
            if sec[1] == 2:
                st = sh[sec[6]]
                strings = data[st[4]:st[4]+st[5]]
                vals = []
                for off in range(sec[4], sec[4]+sec[5], sec[9]):
                    sn, info, other, ndx, value, size = struct.unpack_from('<IBBHQQ', data, off)
                    nm = strings[sn:strings.find(b'\0', sn)].decode()
                    addr = None if ndx == 0 else value if ndx == 0xfff1 else obj['where'].get(ndx, 0) + value
                    vals.append((nm, addr))
                    if info >> 4 in (1, 2) and addr is not None:
                        if nm in symbols:
                            raise ValueError(f'duplicate symbol {nm}')
                        symbols[nm] = addr
                obj['syms'][k] = vals
    image = bytearray(pos-BASE)
    for addr, data in sections:
        image[addr-BASE:addr-BASE+len(data)] = data
    for obj in objects:
        for sec in obj['sh']:
            if sec[1] != 4 or sec[7] not in obj['where']:
                continue
            syms = obj['syms'][sec[6]]
            for off in range(sec[4], sec[4]+sec[5], sec[9]):
                target, info, addend = struct.unpack_from('<QQq', obj['data'], off)
                nm, sym = syms[info >> 32]
                if sym is None:
                    if nm not in symbols:
                        raise ValueError(f'undefined symbol {nm}')
                    sym = symbols[nm]
                kind = info & 0xffffffff
                addr = obj['where'][sec[7]] + target
                value = sym + addend
                if kind in (2, 4):
                    value -= addr
                if kind == 1:
                    fmt = '<Q'
                elif kind in (2, 4, 11):
                    fmt = '<i'
                elif kind == 10:
                    fmt = '<I'
                else:
                    raise ValueError(f'unsupported relocation {kind}')
                struct.pack_into(fmt, image, addr-BASE, value)
    entry = symbols['_start']
    # ELF32 container allows QEMU's multiboot loader to enter the 32-bit stub.
    ident = b'\x7fELF\x01\x01\x01' + bytes(9)
    header = struct.pack('<16sHHIIIIIHHHHHH', ident, 2, 3, 1, entry, 52, 0, 0, 52, 32, 1, 0, 0, 0)
    ph = struct.pack('<IIIIIIII', 1, 4096, BASE, BASE, len(image), len(image), 7, 4096)
    Path(output).write_bytes(header + ph + bytes(4096-len(header)-len(ph)) + image)

if __name__ == '__main__':
    link(sys.argv[2:], sys.argv[1])
