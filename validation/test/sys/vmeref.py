#!/usr/bin/env python3
"""Independent reference for CR4.VME / CR4.PVI (model-only VME/PVI fuzzer of t_vm86.c).

Written from the manuals, not from the Lean model: AMD APM vol. 3 rev. 3.39, the pseudocode of CLI,
STI, PUSHF/PUSHFD, POPF/POPFD, IRET/IRETD and INT (virtual-8086 mode with and without VME, protected
mode with PVI); AMD APM vol. 2, 8.8 (table 8-11, "Virtual-8086 Mode Interrupt Mechanisms") and
8.10; Intel SDM vol. 3, 23.3 (table 23-2) and the vol. 2 pages of the same instructions, which agree
for every case generated here. TCG does not implement VME or PVI (QEMU's CPUID lacks VME; its decoder
raises #GP(0) for every IOPL-sensitive instruction in virtual-8086 mode with IOPL < 3), so these
cases cannot be compared with QEMU.

    vmeref.py table N SEED > vme_cases.h    (default 800, 1)
    vmeref.py selftest

Each case runs one instruction, followed by HLT, from either virtual-8086 mode (CS 0800h, code at
linear 8000h; SS:SP = 0A00h:0100h; IVT entry k = 0900h:k, 256 HLT bytes at linear 9000h) or ring 3
of protected mode (flat; code at +0 and 256 HLT bytes at +100h of a buffer, the stack at another
buffer + 100h; the test reports EIP and ESP relative to them). Every case ends in a ring-0 handler:
the #GP(0) of the HLT (or of the instruction), or the handler of INT n / INT3 / INTO. The table holds
the inputs (mode, instruction, vector, CR4.VME/PVI, the vector's IRB bit, EFLAGS, the 20 bytes of
stack around SP) and the expected frame (vector, error code, EIP, CS, EFLAGS image, SP) and stack
bytes afterwards. The fault image of EFLAGS has RF = 1 (faults; SDM vol. 3, 17.3.1.1, as the model
and QEMU do everywhere), the trap image of INT3/INTO/INT n RF = 0.
"""
import random
import sys

CF, PF, AF, ZF, SF, TF, IF, DF, OF = 1, 4, 0x10, 0x40, 0x80, 0x100, 0x200, 0x400, 0x800
IOPL, NT, RF, VM, AC, VIF, VIP, ID = 0x3000, 0x4000, 0x10000, 0x20000, 0x40000, 0x80000, 0x100000, 0x200000
ARITH = CF | PF | AF | ZF | SF | OF
VALID = 0x003F7FD5         # EFLAGS bits that exist (3, 5, 15 and 22-31 reserved)
OPS = [  # name, bytes
    ('cli', [0xFA]), ('sti', [0xFB]), ('pushf', [0x9C]), ('pushfd', [0x66, 0x9C]), ('popf', [0x9D]),
    ('popfd', [0x66, 0x9D]), ('iret', [0xCF]), ('iretd', [0x66, 0xCF]), ('int', [0xCD]), ('int3', [0xCC]),
    ('into', [0xCE])]
OPN = [o[0] for o in OPS]
NOEC = {8, 10, 11, 12, 13, 14, 17}          # stubs that expect a CPU error code: not used as INT n
def enc(mode, op, n):
    """Instruction bytes: the default operand size is 16 bits in virtual-8086 mode, 32 in the flat
    protected-mode code, so the 66 prefix selects the other size."""
    name = OPN[op]
    b = list(OPS[op][1])
    if mode == 1 and name in ('pushf', 'pushfd', 'popf', 'popfd', 'iret', 'iretd'):
        b = [0x66, b[0]] if len(b) == 1 else [b[1]]
    if name == 'int':
        b.append(n)
    return b


def dpl3(n): return 0x40 <= n < 0x50 or n in (3, 4)   # IDT gates the test makes DPL 3
WIN = 20            # stack window: SP-8 .. SP+12
SP0 = 0x100
V86_CS, LAND_CS = 0x0800, 0x0900
UCODE = 0x1B


class GP(Exception):
    pass


class Case:
    def __init__(self, mode, op, n, cr4, irb, efl, win):
        self.mode, self.op, self.n, self.cr4, self.irb, self.efl = mode, op, n, cr4, irb, efl
        self.win = bytearray(win)


def run(c):
    """Expected (vec, err, eip, cs, eflags image, sp, window bytes)."""
    w = bytearray(c.win)
    efl = c.efl | 2
    sp = SP0
    vm = c.mode == 0
    iopl = (efl >> 12) & 3
    vme = vm and c.cr4 & 1 and iopl < 3
    pvi = (not vm) and c.cr4 & 2 and iopl < 3        # CPL is 3 in both modes
    name = OPN[c.op]
    length = len(enc(c.mode, c.op, c.n))
    code_cs = V86_CS if vm else UCODE
    ip, cs = length, code_cs                        # where the HLT is

    def push(v, n):
        nonlocal sp
        sp -= n
        for k in range(n):
            w[8 + sp - SP0 + k] = (v >> (8 * k)) & 0xFF

    def pop(n):
        nonlocal sp
        v = sum(w[8 + sp - SP0 + k] << (8 * k) for k in range(n))
        sp += n
        return v

    def fault(vec, err):
        # the instruction faults: state as before it, RF set in the image
        return (vec, err, 0, code_cs, (c.efl | 2) | RF, SP0, bytes(c.win))

    try:
        if name in ('cli', 'sti'):
            bit = IF
            if iopl < 3:
                if not (vme or pvi):
                    raise GP
                if name == 'sti' and efl & VIP:
                    raise GP
                bit = VIF
            efl = efl & ~bit if name == 'cli' else efl | bit
        elif name == 'pushf':
            if vm and iopl < 3:
                if not vme:
                    raise GP
                img = (efl & 0xFFFF & ~(IF | IOPL)) | (IF if efl & VIF else 0) | IOPL
            else:
                img = efl & 0xFFFF
            push(img, 2)
        elif name == 'pushfd':
            if vm and iopl < 3:
                raise GP
            push(efl & 0x00FCFFFF, 4)          # VM and RF cleared in the image
        elif name in ('popf', 'popfd', 'iret', 'iretd'):
            wide = name.endswith('d')
            n = 4 if wide else 2
            if vm and iopl < 3 and (wide or not vme):
                raise GP
            if name.startswith('iret'):
                nip, ncs, v = pop(n), pop(n), pop(n)
            else:
                v = pop(n)
            if vm and iopl < 3:                # VME, 16-bit
                if v & TF or (v & IF and efl & VIP):
                    raise GP
                keep = 0xFFFF0000 | IF | IOPL
                efl = (efl & keep & ~VIF) | (v & VALID & 0xFFFF & ~keep) | (VIF if v & IF else 0) | 2
            else:
                mask = ARITH | TF | DF | NT
                if iopl == 3:                  # CPL 3 <= IOPL
                    mask |= IF
                if wide:
                    mask |= AC | ID
                    if name == 'iretd':
                        mask |= RF
                if not wide:
                    mask &= 0xFFFF
                efl = (efl & ~mask) | (v & mask)
            if name.startswith('iret'):
                ip, cs = nip & 0xFFFFFFFF, ncs & 0xFFFF
                if vm and ip > 0xFFFF:
                    raise GP
        elif name == 'int':
            n = c.n
            if vm and c.cr4 & 1 and c.irb == 0:
                # redirected to the 8086 handler: IVT[n] = 0900h:n
                img = (efl & 0xFFFF) if iopl == 3 else \
                    (efl & 0xFFFF & ~(IF | IOPL)) | (IF if efl & VIF else 0) | IOPL
                push(img, 2)
                push(code_cs, 2)
                push(length, 2)
                efl &= ~(TF | RF)
                efl &= ~(IF if iopl == 3 else VIF)
                ip, cs = n, LAND_CS
            else:
                if vm and iopl < 3:
                    raise GP
                if not dpl3(n):
                    return (13, n * 8 + 2, 0, code_cs, (c.efl | 2) | RF, SP0, bytes(c.win))
                return (n, 0, length, code_cs, efl, sp, bytes(w))
        elif name == 'int3':
            return (3, 0, length, code_cs, efl, sp, bytes(w))
        elif name == 'into':
            if efl & OF:
                return (4, 0, length, code_cs, efl, sp, bytes(w))
    except GP:
        return fault(13, 0)
    # the HLT faults: #GP(0) at CPL 3
    return (13, 0, ip, cs, efl | RF, sp, bytes(w))


def gen(rnd, mode):
    if mode == 0:
        op = rnd.randrange(len(OPS))
    else:
        op = OPN.index(rnd.choice(['cli', 'sti', 'pushf', 'pushfd', 'popf', 'popfd', 'iretd']))
    name = OPN[op]
    n = rnd.choice([k for k in range(256) if k not in NOEC])
    if rnd.random() < 0.3:
        n = rnd.choice([0x10, 0x21, 0x41, 0x4F, 0x80, 0xFF, 3, 4, 0, 7])
    cr4 = rnd.randrange(4)
    irb = rnd.randrange(2)
    efl = 2 | (rnd.getrandbits(32) & (ARITH | DF | ID)) | (rnd.randrange(4) << 12)
    if rnd.random() < 0.5:
        efl |= IF
    if rnd.random() < 0.5:
        efl |= VIF
    if rnd.random() < 0.35:
        efl |= VIP
    if mode == 0:
        efl |= VM
    iopl = (efl >> 12) & 3
    win = bytearray(rnd.getrandbits(8) for _ in range(WIN))
    for k in range(8):
        win[k] = 0xCC
    # what the instruction pops
    sens = mode == 0 and iopl < 3
    fl = rnd.getrandbits(32) & (ARITH | DF | IF | NT | AC | ID | IOPL | VIF | VIP | VM | 0x8000 | 0x20)
    if sens and rnd.random() < 0.3:
        fl |= TF
    fl |= 2
    if name in ('iret', 'iretd'):
        tgt = rnd.randrange(256)
        if name == 'iret':
            vals, sz = [tgt, LAND_CS, fl], 2
        else:
            vals, sz = [tgt + (0x100 if mode == 1 else 0), LAND_CS if mode == 0 else UCODE, fl], 4
            if mode == 0 and rnd.random() < 0.1:
                vals[0] |= 0x10000           # EIP beyond 0FFFFh: #GP(0)
        for i, v in enumerate(vals):
            for k in range(sz):
                win[8 + i * sz + k] = (v >> (8 * k)) & 0xFF
    elif name in ('popf', 'popfd'):
        sz = 4 if name == 'popfd' else 2
        for k in range(sz):
            win[8 + k] = (fl >> (8 * k)) & 0xFF
    return Case(mode, op, n, cr4, irb, efl, win)


def dwords(b):
    return [b[i] | b[i + 1] << 8 | b[i + 2] << 16 | b[i + 3] << 24 for i in range(0, WIN, 4)]


def table(count, seed):
    rnd = random.Random(seed)
    out = ['/* generated by vmeref.py table %d %d: CR4.VME / CR4.PVI cases with expected results */' % (count, seed),
           'static const struct vmec vme_cases[] = {']
    for i in range(count):
        c = gen(rnd, 0 if i % 8 < 5 else 1)
        vec, err, eip, cs, efl, sp, wout = run(c)
        fx = lambda vs: ', '.join('0x%x' % v for v in vs)
        code = enc(c.mode, c.op, c.n)
        out.append('\t{ %d, %d, 0x%x, %d, %d, %d, { %s }, 0x%x, { %s }, 0x%x, 0x%x, 0x%x, 0x%x, 0x%x, 0x%x, { %s } },' % (
            c.mode, c.op, c.n, c.cr4, c.irb, len(code), fx(code + [0] * (4 - len(code))), c.efl, fx(dwords(c.win)),
            vec, err, eip, cs, efl, sp, fx(dwords(wout))))
    out.append('};')
    return '\n'.join(out) + '\n'


def selftest():
    # APM vol. 3 PUSHF (VME): VIF in the IF position, IOPL = 3
    c = Case(0, OPN.index('pushf'), 0, 1, 0, VM | VIF | 2, bytes(WIN))
    r = run(c)
    assert r[0] == 13 and r[2] == 1 and r[5] == SP0 - 2 and r[6][6] | r[6][7] << 8 == IF | IOPL | 2, r
    # STI with VIP: #GP(0), nothing changes
    c = Case(0, OPN.index('sti'), 0, 1, 0, VM | VIP | 2, bytes(WIN))
    assert run(c)[:3] == (13, 0, 0)
    # INT n, IOPL < 3, IRB bit clear: redirected, VIF cleared, IF unchanged
    c = Case(0, OPN.index('int'), 0x21, 1, 0, VM | VIF | IF | 2, bytes(WIN))
    r = run(c)
    assert r[3] == LAND_CS and r[2] == 0x21 and r[4] & (VIF | IF) == IF, r
    # PVI: CLI at CPL 3 with IOPL 0 clears VIF only
    c = Case(1, OPN.index('cli'), 0, 2, 0, IF | VIF | 2, bytes(WIN))
    r = run(c)
    assert r[4] & (IF | VIF) == IF and r[2] == 1, r
    print('vmeref selftest ok')


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'selftest':
        selftest()
    elif len(sys.argv) > 1 and sys.argv[1] == 'table':
        n = int(sys.argv[2]) if len(sys.argv) > 2 else 800
        s = int(sys.argv[3]) if len(sys.argv) > 3 else 1
        sys.stdout.write(table(n, s))
    else:
        print(__doc__)
