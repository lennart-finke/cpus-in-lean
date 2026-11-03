#!/usr/bin/env python3
"""Small, strict ELF32 linker for this freestanding test harness.

Accepts only the relocation kinds emitted by clang for these sources (R_386_32,
R_386_PC32). All symbol references are checked. The layout follows link.ld: a
single segment at 1 MiB with the multiboot header first. QEMU loads the result;
the Lean model never calls this tool to execute instructions.
"""
import struct
import sys
from pathlib import Path

BASE = 0x100000
SHF_ALLOC, SHT_PROGBITS, SHT_SYMTAB, SHT_NOBITS, SHT_REL, SHT_RELA = 2, 1, 2, 8, 9, 4

def align(n, a):
    return (n + a - 1) & -a

def link(inputs, output):
    objects, symbols, placed = [], {}, []
    for name in inputs:
        data = Path(name).read_bytes()
        if data[:6] != b'\x7fELF\x01\x01':
            raise ValueError(f'{name}: expected little-endian ELF32')
        hdr = struct.unpack_from('<16sHHIIIIIHHHHHH', data)
        if hdr[1:3] != (1, 3):
            raise ValueError(f'{name}: expected i386 relocatable ELF')
        sh = [struct.unpack_from('<IIIIIIIIII', data, hdr[6] + k * hdr[11]) for k in range(hdr[12])]
        shstr = sh[hdr[13]]
        names = [data[shstr[4]+s[0]:data.index(b'\0', shstr[4]+s[0])].decode() for s in sh]
        if any(s[1] == SHT_RELA for s in sh):
            raise ValueError(f'{name}: unexpected RELA section')
        objects.append({'data': data, 'sh': sh, 'where': {}, 'syms': {}})
        placed += [(names[k] != '.multiboot', s[1] == SHT_NOBITS, len(objects) - 1, k)
                   for k, s in enumerate(sh) if s[2] & SHF_ALLOC and s[5]]
    # Multiboot header first, then loaded data, then zero-initialised sections.
    pos, sections = BASE, []
    for _, _, i, k in sorted(placed):
        obj, sec = objects[i], objects[i]['sh'][k]
        pos = align(pos, max(sec[8], 1))
        obj['where'][k] = pos
        payload = bytearray(sec[5]) if sec[1] == SHT_NOBITS else bytearray(obj['data'][sec[4]:sec[4]+sec[5]])
        sections.append((pos, payload))
        pos += sec[5]
    for obj in objects:
        data, sh = obj['data'], obj['sh']
        for k, sec in enumerate(sh):
            if sec[1] != SHT_SYMTAB:
                continue
            st = sh[sec[6]]
            strings = data[st[4]:st[4]+st[5]]
            vals = []
            for off in range(sec[4], sec[4]+sec[5], sec[9]):
                sn, value, size, info, other, ndx = struct.unpack_from('<IIIBBH', data, off)
                nm = strings[sn:strings.find(b'\0', sn)].decode()
                if ndx == 0xfff2:
                    raise ValueError(f'common symbol {nm}; compile with -fno-common')
                addr = None if ndx == 0 else value if ndx == 0xfff1 else obj['where'].get(ndx, 0) + value
                vals.append((nm, addr))
                if info >> 4 in (1, 2) and addr is not None:
                    if nm in symbols:
                        raise ValueError(f'duplicate symbol {nm}')
                    symbols[nm] = addr
            obj['syms'][k] = vals
    image = bytearray(pos-BASE)
    for addr, payload in sections:
        image[addr-BASE:addr-BASE+len(payload)] = payload
    for obj in objects:
        for sec in obj['sh']:
            if sec[1] != SHT_REL or sec[7] not in obj['where']:
                continue
            syms = obj['syms'][sec[6]]
            for off in range(sec[4], sec[4]+sec[5], sec[9]):
                target, info = struct.unpack_from('<II', obj['data'], off)
                nm, sym = syms[info >> 8]
                if sym is None:
                    if nm not in symbols:
                        raise ValueError(f'undefined symbol {nm}')
                    sym = symbols[nm]
                kind = info & 0xff
                addr = obj['where'][sec[7]] + target
                addend = struct.unpack_from('<i', image, addr-BASE)[0]
                if kind == 1:
                    value = sym + addend
                elif kind == 2:
                    value = sym + addend - addr
                else:
                    raise ValueError(f'unsupported relocation {kind}')
                struct.pack_into('<I', image, addr-BASE, value & 0xffffffff)
    if image[:4] != struct.pack('<I', 0x1BADB002):
        raise ValueError('multiboot header is not at the start of the image')
    entry = symbols['_start']
    ident = b'\x7fELF\x01\x01\x01' + bytes(9)
    header = struct.pack('<16sHHIIIIIHHHHHH', ident, 2, 3, 1, entry, 52, 0, 0, 52, 32, 1, 0, 0, 0)
    ph = struct.pack('<IIIIIIII', 1, 4096, BASE, BASE, len(image), len(image), 7, 4096)
    Path(output).write_bytes(header + ph + bytes(4096-len(header)-len(ph)) + image)

if __name__ == '__main__':
    link(sys.argv[2:], sys.argv[1])
