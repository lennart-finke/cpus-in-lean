"""The EFLAGS bits an IA-32 integer instruction leaves undefined (Intel SDM vol. 2 / AMD APM vol. 3
"Flags affected"), for the extended native families. The extended bundle recorded them as observations
(`flags_observe`, field `eflags.undefined`); since its EPYC 7742 run the model computes the 7742's value of
every one of them (validation/README.md, "The EPYC 7742 runs", the undefined-flag table), so they are
`PINNED`: the comparison checks them strictly (`native_fp.PINNED_UNDEFINED`) and the generators mark only
`observed_flags` (none). `undefined_flags` still lists what the manuals leave undefined."""
from native_ext import layout

CF, PF, AF, ZF, SF, OF = 1, 4, 0x10, 0x40, 0x80, 0x800
ARITH = CF | PF | AF | ZF | SF | OF
PINNED = ARITH   # the documented-undefined flags whose EPYC 7742 value the model computes
LOGIC = {0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x30, 0x31, 0x32, 0x33, 0x34,
         0x35, 0x84, 0x85, 0xA8, 0xA9}


def undefined_flags(code, regs):
    """The undefined arithmetic flags of `code` with the GPR inputs `regs` ({number: value}), as the model
    decodes it; 0 for an instruction that leaves no flag undefined (or is not decoded)."""
    n, op, pfx, at, disp, imm = layout(code)
    if n > 15: return 0
    b = bytes(code) + b'\xcc' * 24
    opsz = 2 if 0x66 in b[:pfx] else 4
    rep = next((x for x in reversed(b[:pfx]) if x in (0xF2, 0xF3)), 0)
    reg = b[at] >> 3 & 7 if at is not None else 0
    vex = b[pfx] in (0xC4, 0xC5) and b[pfx + 1] >= 0xC0
    cl = regs.get(1, 0) & 0xFF
    immv = int.from_bytes(b[imm[0]:imm[0] + imm[1]], 'little') if imm else 0
    if vex:
        pp = (b[pfx + 1] if b[pfx] == 0xC5 else b[pfx + 2]) & 3
        if op in (0x2F2, 0x2F3, 0x2F5) and pp == 0: return AF | PF          # ANDN, BLSR/BLSMSK/BLSI, BZHI
        if op == 0x2F7 and pp == 0: return AF | SF | PF                       # BEXTR
        return 0
    if op in LOGIC or (op in (0x80, 0x81, 0x82, 0x83) and reg in (1, 4, 6)) or (op in (0xF6, 0xF7) and reg in (0, 1)):
        return AF
    if op in (0xC0, 0xC1, 0xD0, 0xD1, 0xD2, 0xD3):
        bits = 8 if op in (0xC0, 0xD0, 0xD2) else opsz * 8
        cnt = (immv if op in (0xC0, 0xC1) else 1 if op in (0xD0, 0xD1) else cl) & 0x1F
        u = 0
        if cnt:
            if cnt != 1: u |= OF
            if reg >= 4:
                u |= AF
                if cnt >= bits: u |= CF | (OF)
        return u
    if (op in (0xF6, 0xF7) and reg in (4, 5)) or op in (0x69, 0x6B, 0x1AF): return SF | ZF | AF | PF
    if op in (0xF6, 0xF7) and reg in (6, 7): return ARITH
    if op in (0x37, 0x3F): return OF | SF | ZF | PF
    if op in (0x27, 0x2F): return OF
    if op in (0xD4, 0xD5): return OF | AF | CF
    if op in (0x1A4, 0x1A5, 0x1AC, 0x1AD):
        cnt = (immv if op in (0x1A4, 0x1AC) else cl) & 0x1F
        if not cnt: return 0
        if opsz == 2 and cnt > 16: return ARITH
        return AF | (OF if cnt != 1 else 0)
    if op in (0x1A3, 0x1AB, 0x1B3, 0x1BB, 0x1BA): return OF | SF | AF | PF
    if op in (0x1BC, 0x1BD): return OF | SF | AF | PF if rep == 0xF3 else CF | OF | SF | AF | PF
    return 0


def observed_flags(code, regs):
    """The undefined flags of `code` a case records as observations (`flags_observe`) rather than
    comparing them strictly: those not `PINNED` (none since the extended EPYC 7742 run)."""
    return undefined_flags(code, regs) & ~PINNED
