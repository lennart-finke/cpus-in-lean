#!/usr/bin/env python3
"""Independent reference for SVM (model-only part of t_svm.c).

Written from the AMD64 APM vol. 2 (24593 rev. 3.43) chapter 15 and vol. 3 (24594 rev. 3.39), not
from the Lean model:
  * the intercept decision of table 15-7 (which exceptions are checked before an instruction's
    intercept and which after), the exit codes of appendix C, EXITINFO1 of IOIO (figure 15-2), MSR
    (15.11), MOV CRx/DRx, INTn and INVLPG (decode assists, 15.8), nRIP (15.7.1) and the exception
    intercepts (15.12), for the SVM fuzzer's instruction pool (`fz_case` in t_svm.c, whose random
    choices are replayed here with the same xorshift32 generator);
  * the two-dimensional nested-paging walk of 15.25.5-15.25.7 (guest tables read through the nested
    tables as user writes, nested faults before the guest fault at each level, the guest permission
    check, then the final nested walk; EXITINFO1 bits P/RW/US/RSV/ID and 32/33; EXITINFO2 the guest
    physical address; accessed/dirty bits in both dimensions), with the nested tables in the host's
    32-bit or PAE format (15.25.3) and guests without paging, with 32-bit and PAE paging.
Two points the APM leaves open are not derived from it; the table follows one documented reading
and marks every case whose outcome depends on the choice (`open` = 1), so the kernel's report counts
them separately (they check consistency with that reading, not the APM):
  * A/D bits of a leaf entry (nested or guest) on an access the leaf's permissions refuse: not set
    (the alternative sets them before the permission check);
  * a PAE guest's PDPTEs under nested paging: read at each walk through the nested tables (the
    alternative loads them at VMRUN/MOV CR3, so a nested fault on the PDPT page would not occur in the
    walk).

    svmref.py table [NSVF] [NNPF] [SEED] > svm_cases.h   (default 400 400 1)
    svmref.py selftest
"""
import random
import sys

M32 = 0xFFFFFFFF


def xs(s):
    s ^= (s << 13) & M32
    s ^= s >> 17
    s ^= (s << 5) & M32
    return s & M32


class Rng:
    def __init__(self, seed):
        self.s = seed or 1

    def __call__(self):
        self.s = xs(self.s)
        return self.s


# ---------------------------------------------------------------- the SVM fuzzer's pool

# vector 3 / 4 intercept bits (VMCB 00Ch, 010h)
I = dict(INTR=0, NMI=1, SMI=2, INIT=3, VINTR=4, CR0SEL=5, IDTRR=6, GDTRR=7, LDTRR=8, TRR=9, IDTRW=10,
         GDTRW=11, LDTRW=12, TRW=13, RDTSC=14, RDPMC=15, PUSHF=16, POPF=17, CPUID=18, RSM=19, IRET=20,
         INTN=21, INVD=22, PAUSE=23, HLT=24, INVLPG=25, INVLPGA=26, IOIO=27, MSR=28, TASK=29, FERR=30,
         SHUTDOWN=31)
I4 = dict(VMRUN=0, VMMCALL=1, VMLOAD=2, VMSAVE=3, STGI=4, CLGI=5, SKINIT=6, RDTSCP=7, ICEBP=8, WBINVD=9,
          MONITOR=10, MWAIT=11, MWAITC=12, XSETBV=13, RDPRU=14)

# (name, length, need, v3, v4) in the order of t_svm.c `fpool`
POOL = [
    ('nop', 1, 0, None, None), ('pushf', 1, 0, 'PUSHF', None), ('popf', 1, 0, 'POPF', None),
    ('int41', 2, 0, 'INTN', None), ('invd', 2, 2, 'INVD', None), ('pause', 2, 0, 'PAUSE', None),
    ('hlt', 1, 1, 'HLT', None), ('invlpg', 3, 0, 'INVLPG', None), ('sidt', 3, 0, 'IDTRR', None),
    ('sgdt', 3, 0, 'GDTRR', None), ('sldt', 3, 0, 'LDTRR', None), ('str', 3, 0, 'TRR', None),
    ('rdcr0', 3, 0, None, None), ('wrcr0', 3, 0, None, None), ('clts', 2, 0, None, None),
    ('smsw', 3, 0, None, None), ('wrcr3', 3, 0, None, None), ('wrcr2', 3, 0, None, None),
    ('rddr0', 3, 0, None, None), ('wrdr1', 3, 0, None, None), ('rddr7', 3, 0, None, None),
    ('in80', 2, 0, 'IOIO', None), ('out80', 2, 0, 'IOIO', None), ('inwdx', 2, 0, 'IOIO', None),
    ('outldx', 1, 0, 'IOIO', None), ('rdmsr', 2, 0, 'MSR', None), ('wrmsr', 2, 0, 'MSR', None),
    ('wbinvd', 2, 2, None, 'WBINVD'), ('stgi', 3, 0, None, 'STGI'), ('clgi', 3, 0, None, 'CLGI'),
    ('vmload', 3, 1, None, 'VMLOAD'), ('vmsave', 3, 1, None, 'VMSAVE'), ('invlpga', 3, 0, 'INVLPGA', None),
    ('vmmcall', 3, 0, None, 'VMMCALL'), ('rsm', 2, 0, 'RSM', None), ('iret', 1, 1, 'IRET', None),
    ('xsetbv', 3, 0, None, 'XSETBV'), ('ud2', 2, 0, None, None), ('div0', 2, 0, None, None),
    ('movds', 2, 0, None, None), ('int3', 1, 4, None, None), ('lmsw', 3, 8, None, None),
    ('vmrun', 3, 0, None, 'VMRUN'), ('lldt', 3, 0, 'LDTRW', None),
]

KCODE, KDATA, UCODE, UDATA = 0x08, 0x10, 0x1B, 0x23
SELS = [0, KDATA, KCODE, UDATA, 0x1234, 0xF8, 0x13]


def bit(v, b):
    return (v >> b) & 1


class Case:
    pass


def gen_svf(seed):
    """Replay t_svm.c fz_case(seed, 0) (the model-only variant: no TCG restrictions)."""
    r = Rng(seed)
    c = Case()
    c.seed = seed
    c.k = r() % len(POOL)
    name, length, need, v3, v4 = POOL[c.k]
    c.name, c.len = name, length
    c.cpl = 3 if (not (need & 2)) and r() % 3 == 0 else 0
    excl = (1 << I['INTR']) | (1 << I['NMI']) | (1 << I['SMI']) | (1 << I['INIT']) | (1 << I['VINTR']) | \
        (1 << I['FERR']) | (1 << I['SHUTDOWN']) | (1 << I['TASK'])
    a, b = r(), r()
    c.i3 = a & b & ~excl & M32
    a, b = r(), r()
    c.i4 = ((a & b) & 0x3FF & ~((1 << I4['SKINIT']) | (1 << I4['RDTSCP']) | (1 << I4['ICEBP']))) | 3
    c.icr = r() & 0x00190009
    c.idr = r() & 0x00FF00FF
    c.exc = (r() | (1 << 8)) & M32
    if need & 1:
        if v3:
            c.i3 |= 1 << I[v3]
        if v4:
            c.i4 |= 1 << I4[v4]
    c.iopm80 = r() & 0xFF
    c.iopm88 = r() & 0xFF
    c.msr = [0x174, 0xC0000081, 0x40000000, 0x175][r() % 4]
    c.msrpm = 0
    if c.msr in (0x174, 0x175):
        c.msrpm = r() & 0xFF
    if c.msr == 0xC0000081:
        c.msrpm = r() & 0xFF
    c.edx = 0x7E + r() % 12
    c.ebx = r()
    r()   # EBP
    c.esi = r() & 0x3F0
    c.edi = r() & 0x3F0
    c.cr0 = 0x11 | (r() & 0x1002E)
    if r() % 2:
        c.rax = c.cr0 ^ (r() & 0x2E)
    else:
        c.rax = SELS[r() % 7]
    if name == 'div0':
        c.esi = 0
    if name == 'wrcr3':
        c.edi = 0
    if name == 'lmsw':
        c.ebx = c.cr0 ^ (r() & 0xE)
    c.cr4 = r() & 0x10C
    r()   # RFLAGS
    r()   # (the DR7 expression draws a value it masks to 0)
    return c


# the kernel's GDT while the fuzzer runs (t_svm.c clears entries 6..30): limit 255
def gdt_desc(idx):
    """(present, s, code, readable, conforming, dpl) or None for a zero descriptor."""
    return {1: (1, 1, 1, 1, 0, 0), 2: (1, 1, 0, 1, 0, 0), 3: (1, 1, 1, 1, 0, 3), 4: (1, 1, 0, 1, 0, 3),
            5: (1, 0, 0, 0, 0, 0), 31: (0, 1, 0, 1, 0, 0)}.get(idx)


def expect_svf(c):
    """Expected (EXITCODE, EXITINFO1, nRIP - rIP or None, stub vector or None). An exception that is
    not intercepted is delivered through the guest's IDT, whose stubs exit with VMMCALL (EAX = the
    vector); an instruction that completes runs into the VMMCALL that follows it."""
    i3, i4, cpl = c.i3, c.i4, c.cpl
    DONE = (0x81, 0, 3, None)

    def exc(v, err=0, nrip=None):
        if v not in (2, 9) and bit(c.exc, v):
            return (0x40 + v, err, nrip, None)
        return (0x81, 0, 3, v)

    def icpt(code, info, n):
        return (code, info, n, None)

    gp = exc(13, 0)
    n = c.name
    L = c.len
    if n == 'nop':
        return DONE
    if n in ('pushf', 'popf'):   # priority over every exception
        return icpt(0x70 if n == 'pushf' else 0x71, 0, L) if bit(i3, I['PUSHF' if n == 'pushf' else 'POPF']) else DONE
    if n == 'int41':             # before any exception
        return icpt(0x75, 0x41, L) if bit(i3, I['INTN']) else (0x81, 0, 3, 0x41)
    if n in ('invd', 'hlt', 'invlpg', 'invlpga', 'wbinvd', 'stgi', 'clgi', 'lmsw', 'clts', 'wrcr0', 'wrcr2',
             'wrcr3', 'rdcr0', 'rddr0', 'rddr7', 'wrdr1', 'rdmsr', 'wrmsr', 'lldt', 'vmload', 'vmsave', 'vmrun') \
            and cpl == 3:
        return gp                # CPL checks before the intercept
    if n == 'invd':
        return icpt(0x76, 0, L) if bit(i3, I['INVD']) else DONE
    if n == 'hlt':
        return icpt(0x78, 0, L)
    if n == 'pause':
        return icpt(0x77, 0, L) if bit(i3, I['PAUSE']) else DONE   # PAUSE filter count 0
    if n == 'invlpg':
        return icpt(0x79, c.msr, L) if bit(i3, I['INVLPG']) else DONE
    if n in ('sidt', 'sgdt', 'sldt', 'str'):
        b = {'sidt': 'IDTRR', 'sgdt': 'GDTRR', 'sldt': 'LDTRR', 'str': 'TRR'}[n]
        return icpt(0x60 + I[b], 0, L) if bit(i3, I[b]) else DONE
    if n == 'invlpga':
        return icpt(0x7A, 0, L) if bit(i3, I['INVLPGA']) else DONE
    if n == 'rdcr0':
        return icpt(0x00, (1 << 63) | 2, L) if bit(c.icr, 0) else DONE
    if n == 'smsw':
        return icpt(0x00, 0, L) if bit(c.icr, 0) else DONE
    if n == 'wrcr0':
        new = (c.rax & 0xE005003F) | 0x10
        if bit(c.icr, 16):
            return icpt(0x10, 1 << 63, L)
        if bit(i3, I['CR0SEL']) and (c.cr0 ^ new) & ~0xA:
            return icpt(0x65, 1 << 63, L)
        return DONE
    if n == 'clts':
        return icpt(0x10, 0, L) if bit(c.icr, 16) else DONE
    if n == 'lmsw':
        if bit(c.icr, 16):
            return icpt(0x10, 0, L)
        return icpt(0x65, 0, L) if bit(i3, I['CR0SEL']) else DONE
    if n == 'wrcr3':
        return icpt(0x13, (1 << 63) | 7, L) if bit(c.icr, 19) else DONE
    if n == 'wrcr2':
        return icpt(0x12, (1 << 63) | 3, L) if bit(c.icr, 18) else DONE
    if n in ('rddr0', 'rddr7', 'wrdr1'):
        reg, wr, gpr = {'rddr0': (0, 0, 2), 'rddr7': (7, 0, 2), 'wrdr1': (1, 1, 3)}[n]
        return icpt((0x30 if wr else 0x20) + reg, gpr, L) if bit(c.idr, reg + 16 * wr) else DONE
    if n in ('in80', 'out80', 'inwdx', 'outldx'):
        if cpl == 3:   # IOPL 0: the TSS bitmap (beyond the TSS limit) faults before the intercept
            return gp
        port, size, inp = {'in80': (0x80, 1, 1), 'out80': (0x80, 1, 0), 'inwdx': (c.edx, 2, 1),
                           'outldx': (c.edx, 4, 0)}[n]
        hit = False
        for p in range(port, port + size):
            byte = c.iopm80 if 0x80 <= p <= 0x87 else c.iopm88 if 0x88 <= p <= 0x8F else 0
            hit |= bool((byte >> (p & 7)) & 1)
        if bit(i3, I['IOIO']) and hit:
            info = (port << 16) | 0x100 | {1: 0x10, 2: 0x20, 4: 0x40}[size] | inp
            return icpt(0x7B, info, L)
        return DONE
    if n in ('rdmsr', 'wrmsr'):
        w = n == 'wrmsr'
        if bit(i3, I['MSR']):
            if c.msr == 0x40000000:
                return icpt(0x7C, int(w), L)
            pos = {0x174: 0x174 * 2, 0x175: 0x175 * 2, 0xC0000081: 0x81 * 2}[c.msr] + int(w)
            if (c.msrpm >> (pos & 7)) & 1:
                return icpt(0x7C, int(w), L)
        return gp if c.msr == 0x40000000 else DONE
    if n == 'wbinvd':
        return icpt(0x89, 0, L) if bit(i4, I4['WBINVD']) else DONE
    if n in ('stgi', 'clgi'):
        b = I4['STGI' if n == 'stgi' else 'CLGI']
        return icpt(0x80 + b, 0, L) if bit(i4, b) else DONE
    if n in ('vmload', 'vmsave', 'vmrun'):
        if c.rax & 0xFFF:
            return gp
        b = I4[n.upper()]
        return icpt(0x80 + b, 0, L)
    if n == 'vmmcall':
        return icpt(0x81, 0, L)
    if n == 'rsm':               # priority over every exception, else #UD outside SMM
        return icpt(0x73, 0, L) if bit(i3, I['RSM']) else exc(6)
    if n == 'iret':
        return icpt(0x74, 0, L)
    if n == 'xsetbv':            # the intercept before #UD (CR4.OSXSAVE = 0)
        return icpt(0x8D, 0, L) if bit(i4, I4['XSETBV']) else exc(6)
    if n == 'ud2':
        return exc(6)
    if n == 'div0':
        return exc(0)
    if n == 'int3':              # #BP: its exception intercept with nRIP, else delivered (gate DPL 3)
        return exc(3, 0, L) if bit(c.exc, 3) else (0x81, 0, 3, 3)
    if n == 'movds':
        sel = c.rax & 0xFFFF
        idx, ti, rpl = sel >> 3, sel & 4, sel & 3
        if sel & 0xFFFC == 0:
            return DONE
        if ti or idx * 8 + 7 > 255:
            return exc(13, sel & 0xFFFC)
        d = gdt_desc(idx)
        if d is None or not d[1]:
            return exc(13, sel & 0xFFFC)
        present, s, code, readable, conf, dpl = d
        if code and not readable:
            return exc(13, sel & 0xFFFC)
        if not (code and conf) and dpl < max(cpl, rpl):
            return exc(13, sel & 0xFFFC)
        if not present:
            return exc(11, sel & 0xFFFC)
        return DONE
    if n == 'lldt':
        if bit(i3, I['LDTRW']):
            return icpt(0x6C, 0, L)
        sel = c.rax & 0xFFFF
        if sel & 0xFFFC == 0:
            return DONE
        return exc(13, sel & 0xFFFC)    # no LDT descriptor in the GDT
    raise ValueError(n)


# ---------------------------------------------------------------- nested paging

GPA0 = 0x10000000
NWIN = 0x40000000


def attr(a, pae):
    """Entry bits of t_svm.c attr_bits: P, R/W, U/S, NX (PAE), A, D, a reserved bit (PAE: 52)."""
    e = 0
    if a & 1:
        e |= 1
    if a & 2:
        e |= 2
    if a & 4:
        e |= 4
    if (a & 8) and pae:
        e |= 1 << 63
    if a & 0x10:
        e |= 0x20
    if a & 0x20:
        e |= 0x40
    if (a & 0x40) and pae:
        e |= 1 << 52
    return e


class Fault(Exception):
    def __init__(self, code, info1, info2):
        self.code, self.info1, self.info2 = code, info1, info2


class Walk2D:
    """The state of one nested-paging case: the nested entries of the window (PDE and PTEs of pages
    0..11) and the guest's paging entries, as dicts updated with A/D bits. `alt_ad`: the other reading
    of the first open point (leaf A/D set before the permission check)."""

    def __init__(self, c, alt_ad=False):
        self.c = c
        self.alt_ad = alt_ad
        hp = c['hmode'] == 2
        self.hp = hp
        self.npde = attr(c['npde'], hp)
        self.npte = [attr(c['npte'][k], hp) for k in range(8)] + [attr(c['ntab'], hp)] * 4
        self.npte = list(self.npte)
        self.gpte = [0] * 8
        if c['gmode']:
            mask = (1 << 63) | 0x67 if c['gmode'] == 2 else 0x67
            self.gpde = attr(c['gpde'], c['gmode'] == 2) & mask
            self.gpte = [attr(c['gpte'][k], c['gmode'] == 2) & mask for k in range(8)]

    # nested walk of guest-physical gpa for a user access (15.25.5)
    def nested(self, gpa, write, fetch, kind):
        hp = self.hp
        rsv = ((1 << 64) - (1 << 52)) & ~(1 << 63) | (0xF << 48) if hp else 0   # bits 62:48 (NXE: bit 63 is NX)
        def fault(prot, rsvd):
            e = (1 if prot else 0) | (2 if write else 0) | 4 | (8 if rsvd else 0) | (0x10 if fetch else 0)
            raise Fault(0x400, e | kind, gpa)
        if not (GPA0 <= gpa < GPA0 + 0x10000):
            return gpa, True, True, False   # the identity part (present, writable, user, executable)
        pde = self.npde
        if not pde & 1:
            fault(False, False)
        if pde & rsv:
            fault(True, True)
        self.npde |= 0x20                   # the PDE's accessed bit when it is used
        k = (gpa - GPA0) >> 12
        pte = self.npte[k]
        if not pte & 1:
            fault(False, False)
        if pte & rsv:
            fault(True, True)
        perm = pde & pte
        xd = hp and bool((pde | pte) >> 63)   # host EFER.NXE = 1 with PAE
        if self.alt_ad:
            self.npte[k] = pte | 0x20 | (0x40 if write else 0)
        if not perm & 4 or (write and not perm & 2) or (fetch and xd):
            fault(True, False)
        self.npte[k] = pte | 0x20 | (0x40 if write else 0)
        return gpa, bool(perm & 2), bool(self.npte[k] & 0x40), xd

    def access(self, lin, write, user, fetch):
        c = self.c
        g = c['gmode']
        TABLE, FINAL = 1 << 33, 1 << 32
        if g == 0:
            self.nested(lin, write, fetch, FINAL)
            return
        # the instruction itself is fetched first, at NPCODE (21000h), through the guest's identity
        # PDE 0 (a large page) in window page 8 (32-bit) or the PDPTE in page 8 and PD0 in page 9 (PAE)
        if g == 1:
            self.nested(GPA0 + 0x8000, True, False, TABLE)
        else:
            self.nested(GPA0 + 0x8000, True, False, TABLE)
            self.nested(GPA0 + 0x9000, True, False, TABLE)
        wp = c['wp']
        if g == 1:
            pde_gpa = GPA0 + 0x8000 + (lin >> 22) * 4
            pte_gpa = GPA0 + 0xB000 + ((lin >> 12) & 0x3FF) * 4
            idf = False          # 32-bit paging: I/D only with SMEP (not set here)
            rsvd = 0
        else:
            nxe = c['nxe']
            idf = fetch and nxe
            rsvd = (0x7FF << 52) | (0xF << 48) | (0 if nxe else 1 << 63)
            pdpte_gpa = GPA0 + 0x8000 + (lin >> 30) * 8
            pde_gpa = GPA0 + 0xA000 + ((lin >> 21) & 0x1FF) * 8
            pte_gpa = GPA0 + 0xB000 + ((lin >> 12) & 0x1FF) * 8

        def pf(prot, rs):
            e = (1 if prot else 0) | (2 if write else 0) | (4 if user else 0) | (8 if rs else 0) | \
                (0x10 if idf else 0)
            raise Fault(0x4E, e, lin)
        if g == 2:
            self.nested(pdpte_gpa, True, False, TABLE)   # the PDPTE (present, no reserved bits)
        self.nested(pde_gpa, True, False, TABLE)
        pde = self.gpde
        if not pde & 1:
            pf(False, False)
        if pde & rsvd:
            pf(True, True)
        self.gpde = pde | 0x20
        self.nested(pte_gpa, True, False, TABLE)
        k = (lin >> 12) & 7
        pte = self.gpte[k]
        if not pte & 1:
            pf(False, False)
        if pte & rsvd:
            pf(True, True)
        perm = pde & pte
        xd = g == 2 and c['nxe'] and bool((pde | pte) >> 63)
        if self.alt_ad:
            self.gpte[k] = pte | 0x20 | (0x40 if write else 0)
        if (user and not perm & 4) or (write and not perm & 2 and (user or wp)) or (fetch and xd):
            pf(True, False)
        self.gpte[k] = pte | 0x20 | (0x40 if write else 0)
        self.nested(GPA0 + 0x1000 * k + (lin & 0xFFF), write, fetch, FINAL)


def expect_npf(c, alt_ad=False):
    """(code, info1 low, info1 high, info2, value, memory word, A/D bits) of t_svm.c npc_out."""
    w = Walk2D(c, alt_ad)
    pg, acc = c['pg'], c['acc']
    off = 0x100 if acc == 2 else 0
    lin = (NWIN if c['gmode'] else GPA0) + 0x1000 * pg + off
    mem = 0xD0000000 | pg
    try:
        w.access(lin, acc == 1, c['cpl'] == 3, acc == 2)
        code, i1, i2 = 0x81, 0, 0
        val = 0 if acc == 1 else (0xC0DE0000 | pg if acc == 2 else mem)
        if acc == 1:
            mem = 0xA5A5A5A5
    except Fault as f:
        code, i1, i2, val = f.code, f.info1, f.info2, 0
    ad = ((w.npte[pg] >> 5) & 3) | (((w.gpte[pg] >> 5) & 3) << 2 if c['gmode'] else 0)
    return (code, i1 & M32, i1 >> 32, i2, val, mem, ad)


def npf_open(c):
    """1 if the outcome depends on a point the APM leaves open (see the module documentation)."""
    if expect_npf(c, alt_ad=True) != expect_npf(c):
        return 1
    if c['gmode'] == 2:
        try:
            Walk2D(c).nested(GPA0 + 0x8000, True, False, 1 << 33)   # the PDPT page's nested translation
        except Fault:
            return 1
    return 0


def gen_npf(r):
    """A random case (as t_svm.c npc_rand with both host modes)."""
    def ra():
        return ((1 if r() % 8 else 0) | (2 if r() % 4 else 0) | (4 if r() % 4 else 0) | (0 if r() % 4 else 8) |
                (0x10 if r() % 2 else 0) | (0x20 if r() % 2 else 0) | (0 if r() % 16 else 0x40))
    c = dict(hmode=1 + r() % 2, gmode=r() % 3, wp=r() % 2, nxe=r() % 2, cpl=3 if r() % 4 == 0 else 0,
             acc=r() % 3, pg=r() % 8)
    c['npde'] = ra() | 1
    c['ntab'] = ra() | 1
    c['gpde'] = ra() | 1
    if r() % 8 == 0:
        c['npde'] &= ~1
    if r() % 8 == 0:
        c['ntab'] &= ~2
    c['npde'] &= ~0x40
    c['gpde'] &= ~0x40
    c['npte'] = [ra() for _ in range(8)]
    c['gpte'] = [ra() for _ in range(8)]
    return c


def table(nsvf, nnpf, seed):
    out = ['/* Generated by svmref.py table %d %d %d: SVM fuzzer seeds and nested-paging cases with their' % (nsvf, nnpf, seed),
           '   expected results (see t_svm.c, test_svm_model). */',
           'struct svfx { u32 seed; u32 code; u64 info1; u32 nrip; u32 vec; };',
           'static const struct svfx svfx[] = {']
    r = Rng(seed * 2654435761 & M32)
    for _ in range(nsvf):
        s = r()
        c = gen_svf(s)
        code, i1, nrip, vec = expect_svf(c)
        out.append('{0x%x, 0x%x, 0x%xull, 0x%x, 0x%x},' % (s, code, i1, 0xFFFFFFFF if nrip is None else nrip,
                                                         0xFFFF if vec is None else vec))
    out.append('};')
    out.append('struct npx { struct npc c; u32 o[7]; u32 open; };')
    out.append('static const struct npx npx[] = {')
    for _ in range(nnpf):
        c = gen_npf(r)
        o = expect_npf(c)
        out.append('{{%d, %d, %d, %d, %d, %d, %d, 0x%x, 0x%x, 0x%x, {%s}, {%s}}, {%s}, %d},' % (
            c['hmode'], c['gmode'], c['wp'], c['nxe'], 1 if c['cpl'] else 0, c['acc'], c['pg'], c['ntab'],
            c['npde'], c['gpde'], ', '.join('0x%x' % a for a in c['npte']), ', '.join('0x%x' % a for a in c['gpte']),
            ', '.join('0x%x' % v for v in o), npf_open(c)))
    out.append('};')
    return '\n'.join(out) + '\n'


def selftest():
    # a present, writable, user mapping: a read completes, A set in both dimensions
    c = dict(hmode=2, gmode=2, wp=0, nxe=1, cpl=0, acc=0, pg=0, ntab=7, npde=7, gpde=7, npte=[7] * 8, gpte=[7] * 8)
    assert expect_npf(c) == (0x81, 0, 0, 0, 0xD0000000, 0xD0000000, 5), expect_npf(c)
    # a not-present nested PTE of the final page: NPF, final-address bit, US
    c['npte'] = [6] + [7] * 7
    assert expect_npf(c)[:4] == (0x400, 4, 1, GPA0), expect_npf(c)
    # a read-only nested page table: the table access (a user write) faults first
    c['npte'] = [7] * 8
    c['ntab'] = 5
    assert expect_npf(c)[:4] == (0x400, 7, 2, GPA0 + 0x8000), expect_npf(c)
    # guest #PF: user access to a supervisor page
    c = dict(hmode=1, gmode=1, wp=0, nxe=0, cpl=3, acc=1, pg=3, ntab=7, npde=7, gpde=7, npte=[7] * 8,
             gpte=[7, 7, 7, 3, 7, 7, 7, 7])
    assert expect_npf(c)[:4] == (0x4E, 7, 0, NWIN + 0x3000), expect_npf(c)
    # the SVM pool: INT n with its intercept, the vector in EXITINFO1
    for s in range(1, 4000):
        c = gen_svf(s)
        if c.name == 'int41' and bit(c.i3, I['INTN']):
            assert expect_svf(c) == (0x75, 0x41, 2, None)
            break
    print('svmref selftest ok')


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'table':
        a = [int(x, 0) for x in sys.argv[2:]] + [400, 400, 1][len(sys.argv) - 2:]
        sys.stdout.write(table(a[0], a[1], a[2]))
    elif len(sys.argv) > 1 and sys.argv[1] == 'selftest':
        selftest()
    else:
        print(__doc__)
