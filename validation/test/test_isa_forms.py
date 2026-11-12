#!/usr/bin/env python3
"""Cross-check of isa_forms.py against an independent decoder: LLVM's x86 disassembler (llvm-mc,
-triple=i386 -mcpu=znver2, i.e. 32-bit protected mode).

* Every concrete encoding of every isa_forms.IMPLEMENTED row (each opcode byte, each allowed
  mandatory prefix, ModRM register and memory forms with every ModRM.reg (and ModRM.rm) the row
  allows, every VEX.L and VEX.W it allows; two-byte VEX where possible) must disassemble as exactly
  one instruction of the expected length (the ModRM/SIB/displacement/imm8 tail laid out as in
  x86_32/EXTENDING.md "Opcode numbering").
* The encodings that the 'ud' family of gen.py treats as undefined must not disassemble: every
  undefined legacy 0F 38 / 0F 3A opcode and prefix, every undefined gen.UD_0F opcode and prefix,
  every VEX map 1..3 encoding (prefix, opcode, VEX.L, VEX.W, ModRM.mod class and reg) for which
  isa_forms.defined() is false (this includes every isa_forms.vex_neighbours() form), each with a
  register and a memory ModRM for every ModRM.reg, and a deterministic sample of gen.ud_form's
  output of every kind (also VEX after a legacy prefix, unknown VEX maps, EVEX, XOP).

LLVM's disassembler ignores -mcpu (it decodes the instructions of every x86 CPU) and some fields that
the hardware checks, and it is stricter than the hardware in a few places. Each such disagreement must
match an entry of IMPLEMENTED_DIFFERENCES / UNDEFINED_DIFFERENCES below, which says why, citing the
manuals; the test prints how many encodings each entry covers and fails on an entry that matches
nothing (a stale entry would hide a later disagreement).

Skipped when no llvm-mc is found (LLVM_MC, PATH, xcrun, Homebrew's or Debian's llvm).
"""
import collections, glob, os, random, re, shutil, subprocess, sys, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import isa_forms
import gen


def find_llvm_mc():
    cands = [os.environ.get('LLVM_MC'), shutil.which('llvm-mc')]
    try:
        cands.append(subprocess.run(['xcrun', '--find', 'llvm-mc'], capture_output=True, text=True).stdout.strip())
    except OSError:
        pass
    cands += ['/opt/homebrew/opt/llvm/bin/llvm-mc', '/usr/local/opt/llvm/bin/llvm-mc']
    cands += sorted(glob.glob('/usr/lib/llvm-*/bin/llvm-mc'), reverse=True)
    for c in cands:
        if c and os.path.isfile(c) and os.access(c, os.X_OK):
            return c
    return None


MARKER = b'\xcd\x7b'   # INT 7Bh, disassembled after each test encoding to delimit the output


def disassemble(mc, encodings):
    """For each encoding (status, text): 'ok' if LLVM decodes all its bytes as exactly one
    instruction, 'invalid' if it decodes nothing at its first byte, 'partial' otherwise (an
    instruction with bytes left over, or a prefix decoded as an instruction of its own)."""
    lines = []
    for e in encodings:
        lines.append('[' + ' '.join('0x%02x' % b for b in e) + ']')   # one instruction per [...]
        lines.append('[' + ' '.join('0x%02x' % b for b in MARKER) + ']')
    p = subprocess.run([mc, '--disassemble', '-triple=i386', '-mcpu=znver2'], input='\n'.join(lines) + '\n',
                       capture_output=True, text=True)
    warn = collections.defaultdict(list)
    for m in re.finditer(r'^<stdin>:(\d+):(\d+): (warning|error): (.*)$', p.stderr, re.M):
        line, col = int(m.group(1)), int(m.group(2))
        if line % 2 == 0:
            raise AssertionError('marker not decoded: ' + m.group(0))
        warn[(line - 1) // 2].append((col, m.group(4)))
    groups, cur = [], []
    for ln in p.stdout.splitlines():
        ln = ln.strip()
        if not ln or ln.startswith('.'):
            continue
        if re.fullmatch(r'int\s+\$123', ln):
            groups.append(cur)
            cur = []
        else:
            cur.append(re.sub(r'\s+', ' ', ln))
    assert len(groups) == len(encodings), (len(groups), len(encodings), p.stderr[-2000:])
    out = []
    for i, insns in enumerate(groups):
        w = warn.get(i, [])
        if any(col == 2 for col, _ in w):          # (column 1 is the '[')
            st = 'invalid'
        elif w or len(insns) != 1:
            st = 'partial'
        else:
            st = 'ok'
        out.append((st, ' ; '.join(insns)))
    return out


# --- encodings ---

PP_BYTE = {0: b'', 1: b'\x66', 2: b'\xf3', 3: b'\xf2'}
NO_MODRM_0F = {0x05, 0x07, 0x09, 0x33, 0x34, 0x35}   # SYSCALL, SYSRET, WBNOINVD, RDPMC, SYSENTER, SYSEXIT


def legacy_layout(map_, pp, op):
    """(ModRM, number of imm8) of a legacy 0F / 0F 38 / 0F 3A form (EXTENDING.md "Opcode numbering")."""
    if map_ == 2:
        return True, 0
    if map_ == 3:
        return True, 1
    if op in NO_MODRM_0F or (op in gen.UD_0F and op not in gen.MODRM_0F):
        return False, 0
    if op == 0x78 and pp in (1, 3):   # EXTRQ xmm, imm8, imm8 / INSERTQ xmm, xmm, imm8, imm8
        return True, 2
    return True, 0


def vex_prefix(map_, pp, L, W, two):
    """VEX with R, X, B = 0 (stored inverted) and VEX.vvvv = 1111b (no register / XMM0)."""
    vb = (0xF << 3) | (L << 2) | pp
    return bytes([0xC5, 0x80 | vb]) if two else bytes([0xC4, 0xE0 | map_, (W << 7) | vb])


def modrm_bytes(mod, reg, rm):
    """ModRM (+ SIB, displacement): mod 'reg' = 11b; 'mem' = mod 00 ([EAX], [EAX+ECX] with a SIB
    for rm = 100b, [disp32] for rm = 101b)."""
    if mod == 'reg':
        return bytes([0xC0 | reg << 3 | rm])
    if rm == 4:
        return bytes([reg << 3 | 4, 0x08])
    if rm == 5:
        return bytes([reg << 3 | 5]) + (0x8000).to_bytes(4, 'little')
    return bytes([reg << 3 | rm])


def modrm_variants(modrm, all_rm=False):
    """ModRM bytes for every ModRM.mod class, reg and rm that `modrm` (a Form constraint) allows;
    an unconstrained rm is [EAX] in memory forms and ECX in register forms, or with `all_rm` every
    register (ModRM.rm selects the instruction in some groups, e.g. 0F 01 C8..CF)."""
    m, r, rms = (tuple(modrm) + (None,))[:3] if modrm else (None, None, None)
    return [modrm_bytes(mod, reg, rm)
            for mod in (['reg', 'mem'] if m is None else [m])
            for reg in (range(8) if r is None else [r])
            for rm in (rms or (range(8) if all_rm else (1,)) if mod == 'reg' else rms or (0,))]


def form_encodings(f):
    """Every concrete encoding of the isa_forms row `f`."""
    out = []
    for op in f.ops:
        for pp in (range(4) if f.pp is None else [f.pp]):
            if f.encoding == 'vex':
                lay = gen.vex_layout(f.map, op, pp)
                assert lay is not None, (f, op)
                heads = [vex_prefix(f.map, pp, L, W, f.map == 1 and W == 0)
                         for L in ([0, 1] if f.L is None else [f.L]) for W in ([0, 1] if f.W is None else [f.W])]
            else:
                lay = legacy_layout(f.map, pp, op)
                heads = [(b'\xf0' if f.encoding == 'legacy-lock' else b'') + PP_BYTE[pp] + b'\x0f' +
                         {1: b'', 2: b'\x38', 3: b'\x3a'}[f.map]]
            tails = modrm_variants(f.modrm, all_rm=True) if lay[0] else [b'']
            out += [h + bytes([op]) + t + b'\x01' * lay[1] for h in heads for t in tails]
    return out


def undefined_encodings():
    """The undefined encodings that the 'ud' family draws from, enumerated (kind, bytes)."""
    out = []
    for m in (2, 3):
        for pp in range(4):
            for op in range(256):
                if not isa_forms.defined('legacy', m, pp, op):
                    out += [('map%d' % m, PP_BYTE[pp] + bytes([0x0F, 0x38 if m == 2 else 0x3A, op]) + t + b'\x01' * (m == 3))
                            for t in modrm_variants(None)]
    for op in gen.UD_0F:
        for pp in range(4):
            if not isa_forms.defined('legacy', 1, pp, op):
                out += [('0f', PP_BYTE[pp] + bytes([0x0F, op]) + t)
                        for t in (modrm_variants(None) if op in gen.MODRM_0F else [b''])]
    nb = set(isa_forms.vex_neighbours())
    for m in (1, 2, 3):
        for pp in range(4):
            for op in range(256):
                lay = gen.vex_layout(m, op, pp)
                if lay is None or (m, pp, op) == (1, 0, 0xC4):   # (not generated by the 'ud' family)
                    continue
                for L in (0, 1):
                    for W in (0, 1):
                        for mod in (('reg', 'mem') if lay[0] else (None,)):
                            for reg in (range(8) if lay[0] else (None,)):
                                if isa_forms.defined('vex', m, pp, op, None if mod is None else 3 if mod == 'reg' else 0,
                                                     reg, L=L, W=W):
                                    continue
                                t = modrm_bytes(mod, reg, 1 if mod == 'reg' else 0) if lay[0] else b''
                                out.append(('vexnb' if (m, pp, op, L) in nb else 'vex',
                                            vex_prefix(m, pp, L, W, m == 1 and W == 0) + bytes([op]) + t + b'\x01' * lay[1]))
    return out


def ud_sample(n=600, seed=12345):
    """A deterministic sample of gen.ud_form's encodings, every kind: (kind, bytes)."""
    state, saved = random.getstate(), dict(gen._vexnb)
    try:
        random.seed(seed)
        gen._vexnb.update(list=None, next=0, n=0)
        out = []
        while len(out) < n:
            body, kind = gen.ud_form(gen.Gen(), False)
            if body is not None:
                out.append((kind, body))
        return out
    finally:
        random.setstate(state)
        gen._vexnb.clear()
        gen._vexnb.update(saved)


def parse(e):
    """The fields of an encoding: enc ('legacy', 'legacy-lock', 'vex' or 'other' (one-byte map)),
    pfx (legacy prefixes), map, pp, op, L, W, mod (0..3), reg."""
    i = 0
    while e[i] in (0x66, 0xF2, 0xF3, 0xF0, 0x26, 0x2E, 0x36, 0x3E, 0x64, 0x65, 0x67):
        i += 1
    p = dict(pfx=bytes(e[:i]), L=None, W=None, mod=None, reg=None, pp=None)
    if e[i] == 0xC5:
        p.update(enc='vex', map=1, W=0, L=e[i + 1] >> 2 & 1, pp=e[i + 1] & 3)
        i += 2
    elif e[i] == 0xC4:
        p.update(enc='vex', map=e[i + 1] & 0x1F, W=e[i + 2] >> 7, L=e[i + 2] >> 2 & 1, pp=e[i + 2] & 3)
        i += 3
    elif e[i] == 0x0F:
        f2f3 = [b for b in p['pfx'] if b in (0xF2, 0xF3)]   # the last F2/F3 wins over 66
        pp = {0xF3: 2, 0xF2: 3}[f2f3[-1]] if f2f3 else 1 if 0x66 in p['pfx'] else 0
        m = {0x38: 2, 0x3A: 3}.get(e[i + 1], 1)
        i += 1 if m == 1 else 2
        p.update(enc='legacy-lock' if 0xF0 in p['pfx'] else 'legacy', map=m, pp=pp)
    else:
        p.update(enc='other', map=0)
    p['op'] = e[i]
    if p['enc'] == 'vex':
        lay = gen.vex_layout(p['map'], p['op'], p['pp']) if 1 <= p['map'] <= 3 else None
        has_modrm = lay is not None and lay[0]
    elif p['enc'] == 'other':
        has_modrm = True
    else:
        has_modrm = legacy_layout(p['map'], p['pp'], p['op'])[0]
    if has_modrm and i + 1 < len(e):
        p['mod'], p['reg'] = e[i + 1] >> 6, e[i + 1] >> 3 & 7
    return p


def mnemonic(text):
    """The first instruction's mnemonic, without LLVM's {vex}/{evex} pseudo prefixes."""
    return next((w for w in text.split() if not w.startswith('{')), '')


def mn_in(*names):
    return lambda p, t: mnemonic(t) in names


def mn_match(regex):
    return lambda p, t: re.fullmatch(regex, mnemonic(t)) is not None


Diff = collections.namedtuple('Diff', 'name pred why sample_only', defaults=(False,))

# IMPLEMENTED encodings that LLVM does not decode (as exactly one instruction).
IMPLEMENTED_DIFFERENCES = [
    Diff('PREFETCH reserved types 0F 0D /3../7',
         lambda p, t: p['enc'] == 'legacy' and p['map'] == 1 and p['op'] == 0x0D and p['reg'] >= 3,
         'LLVM knows /0 PREFETCH, /1 PREFETCHW and /2 (Intel PREFETCHWT1) only. AMD APM vol. 3, '
         'PREFETCH/PREFETCHW and the opcode map (group P, 0F 0D): the reserved ModRM.reg values /2../7 '
         'are prefetches executed as PREFETCH; x86_32/X86/Ext/Gpr.lean does the same'),
    Diff('LOCK MOV CRn (AltMovCr8)',
         lambda p, t: p['enc'] == 'legacy-lock' and p['map'] == 1 and p['op'] in (0x20, 0x22),
         'LLVM does not know AMD\'s alternate CR8 encoding and decodes LOCK as an instruction of its own '
         '(then MOV CR0, or, with ModRM.mod != 11b, nothing: it requires mod = 11b). AMD APM vol. 3 MOV '
         'CRn: with a LOCK prefix MOV CR0 accesses CR8 outside 64-bit mode (CPUID 8000_0001:ECX[4] '
         'AltMovCr8); SDM vol. 2B MOV (control registers): "The 2 bits in the mod field are ignored"'),
]

NOT_ZEN2 = ('not a Zen 2 instruction (LLVM decodes the instructions of every CPU whatever -mcpu says): '
            'CPUID on the EPYC 7742 (x86_32/X86/Cpuid.lean, AMD PPR family 17h model 31h) reports none of '
            'these features, and an instruction of an unsupported feature raises #UD (SDM vol. 2 and AMD '
            'APM vol. 3/4, each instruction\'s "#UD If CPUID.(...) = 0")')

# Undefined encodings (the 'ud' family expects #UD) that LLVM decodes.
UNDEFINED_DIFFERENCES = [
    # --- LLVM ignores a prefix that the hardware checks ---
    Diff('VEX after a 66/F2/F3/LOCK prefix', lambda p, t: p['enc'] == 'vex' and any(b in p['pfx'] for b in b'\x66\xf2\xf3\xf0'),
         'LLVM decodes the legacy prefix separately or ignores it. SDM vol. 2A 2.3.2: "Any VEX-encoded '
         'instruction with a LOCK/66H/F2H/F3H/REX prefix preceding VEX will #UD"; AMD APM vol. 3, '
         '"VEX and XOP Prefixes" (the same rule)'),
    Diff('SSSE3 MMX forms with F2/F3',
         lambda p, t: p['enc'] == 'legacy' and p['pp'] in (2, 3) and (
             p['map'] == 2 and (p['op'] <= 0x0B or 0x1C <= p['op'] <= 0x1E) or p['map'] == 3 and p['op'] == 0x0F)
         and re.fullmatch(r'pshufb|ph(add|sub)s?[wd]|pmaddubsw|psign[bwd]|pmulhrsw|pabs[bwd]|palignr', mnemonic(t)),
         'LLVM ignores the F2/F3 prefix (decodes the NP form). SDM vol. 2 PSHUFB etc.: "NP 0F 38 00 /r", '
         'and 3.1.1.2: NP = '
         '"the use of 66/F2/F3 prefixes ... are not allowed ... will either cause an invalid-opcode '
         'exception (#UD) or result in the encoding for a different instruction"'),
    Diff('SHA with 66/F2/F3',
         lambda p, t: p['enc'] == 'legacy' and p['pp'] != 0 and (
             p['map'] == 2 and 0xC8 <= p['op'] <= 0xCD or p['map'] == 3 and p['op'] == 0xCC)
         and mnemonic(t).startswith('sha'),
         'LLVM ignores the prefix (decodes the NP form). SDM vol. 2 SHA1RNDS4/SHA1NEXTE/...: "NP 0F 3A CC", "NP 0F 38 C8" '
         '(see 3.1.1.2); the model raises #UD (isa_forms.py, Crypto rows)'),
    Diff('MOVBE with F3', lambda p, t: p['enc'] == 'legacy' and p['map'] == 2 and p['pp'] == 2 and p['op'] in (0xF0, 0xF1)
         and mnemonic(t).startswith('movbe'),
         'LLVM ignores the F3 prefix. SDM vol. 2 MOVBE: "0F 38 F0 /r" and "66 0F 38 F0" only; Table A-4 '
         '(0F 38 map) and the 0F 38 opcode map of AMD APM vol. 3 Appendix A assign nothing to F3 0F 38 F0/F1'),
    # --- instructions of other CPUs ---
    Diff('EVEX (AVX-512, APX)', lambda p, t: p['enc'] == 'other' and p['op'] == 0x62,
         'Zen 2 has no AVX-512 (CPUID 7:EBX[16] = 0); outside 64-bit mode 62 with ModRM.mod = 11b is '
         'BOUND with a register operand, #UD (APM vol. 3 BOUND; SDM BOUND "#UD If second operand is not '
         'a memory location")', True),
    Diff('3DNow! FEMMS', mn_in('femms'),
         NOT_ZEN2 + ' (3DNow!: CPUID 8000_0001:EDX[31] = 0; AMD APM vol. 5 FEMMS)'),
    Diff('VMX', mn_in('vmreadl', 'vmwritel', 'invept', 'invvpid'),
         NOT_ZEN2 + ' (Intel VMX: CPUID 1:ECX[5] = 0; Zen 2 has SVM)'),
    Diff('later legacy-map extensions',
         mn_in('invpcid', 'movdiri', 'movdir64b', 'enqcmd', 'enqcmds', 'wrssd', 'wrussd', 'aaddl', 'aandl', 'aorl',
               'axorl', 'aesenc128kl', 'aesenc256kl', 'aesdec128kl', 'aesdec256kl', 'aesencwide128kl',
               'aesencwide256kl', 'aesdecwide128kl', 'aesdecwide256kl', 'encodekey128', 'encodekey256',
               'loadiwkey', 'urdmsr', 'uwrmsr', 'gf2p8mulb', 'gf2p8affineqb', 'gf2p8affineinvqb'),
         NOT_ZEN2 + ' (INVPCID, MOVDIRI, MOVDIR64B, ENQCMD, CET shadow stacks, RAO-INT, Key Locker, '
         'USER_MSR, GFNI)'),
    Diff('AVX-512 opmask instructions (VEX)', lambda p, t: p['enc'] == 'vex' and re.fullmatch(r'k[a-z]+[bwdq]', mnemonic(t)),
         NOT_ZEN2 + ' (AVX512F/BW/DQ: CPUID 7:EBX[16,17,30] = 0)'),
    Diff('AMX', mn_match(r'ldtilecfg|sttilecfg|tdp\w+|tcmm\w+'),
         NOT_ZEN2 + ' (AMX, also 64-bit mode only)'),
    Diff('later VEX extensions',
         mn_match(r'vpdpbu?s?ds?|vpdpb[su][su]ds?|vpdpw[su][su]ds?|vpdpwssds?|vpmadd52[lh]uq|vbcstne\w+|'
                  r'vcvtne\w+|vsha512\w+|vsm3\w+|vsm4\w+|cmp\w*xadd|vgf2p8\w+'),
         NOT_ZEN2 + ' (AVX-VNNI, AVX-IFMA, AVX-NE-CONVERT, AVX-VNNI-INT8/INT16, SHA512, SM3, SM4, GFNI; '
         'CMPccXADD, also 64-bit mode only)'),
    Diff('VAES / VPCLMULQDQ with VEX.L = 1',
         lambda p, t: p['enc'] == 'vex' and p['L'] == 1 and mnemonic(t) in (
             'vaesenc', 'vaesenclast', 'vaesdec', 'vaesdeclast', 'vpclmulqdq'),
         NOT_ZEN2 + ' (VAES, VPCLMULQDQ: CPUID 7:ECX[9,10] = 0 (Zen 3 adds them); the VEX.128 forms are '
         'AVX + AES/PCLMULQDQ and in IMPLEMENTED)'),
    Diff('FMA4 and VPERMIL2PS/PD', mn_match(r'vf(n?m(add|sub)|maddsub|msubadd)(p|s)[sd]|vpermil2p[sd]'),
         NOT_ZEN2 + ' (AMD family 15h: FMA4 CPUID 8000_0001:ECX[16] = 0, XOP (VPERMIL2Px, APM vol. 4) '
         'CPUID 8000_0001:ECX[11] = 0; the FMA3 forms are VEX.0F38 and in IMPLEMENTED)'),
]


def classify(diffs, items):
    """items: (bytes, (status, text)). Returns (per-entry counts, unexplained items)."""
    counts, left = collections.Counter(), []
    for e, r in items:
        p = parse(e)
        hit = next((d for d in diffs if d.pred(p, r[1])), None)
        if hit is None:
            left.append((e, r))
        else:
            counts[hit.name] += 1
    return counts, left


def report(title, diffs, counts):
    print('  expected differences (%s):' % title, file=sys.stderr)
    for d in diffs:
        print('    %6d  %s' % (counts[d.name], d.name), file=sys.stderr)


@unittest.skipIf(find_llvm_mc() is None, 'no llvm-mc found (set LLVM_MC, or install LLVM, e.g. Homebrew llvm)')
class LlvmCrossCheck(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.mc = find_llvm_mc()

    def check(self, title, diffs, items, want):
        res = disassemble(self.mc, [e for e in items])
        bad = [(e, r) for e, r in zip(items, res) if r[0] != want]
        counts, left = classify(diffs, bad)
        print('\n%s: %d encodings, %d %s for LLVM (%d explained)' % (
            title, len(items), len(bad), 'not decoded' if want == 'ok' else 'decoded', len(bad) - len(left)),
            file=sys.stderr)
        report(title, diffs, counts)
        for e, r in left[:100]:
            print('  unexplained: %s %s %r' % (e.hex(' '), r[0], r[1]), file=sys.stderr)
        self.assertEqual([(e.hex(' '), r) for e, r in left], [])
        stale = [d.name for d in diffs if counts[d.name] == 0 and not d.sample_only]
        self.assertEqual(stale, [], 'entries that match no encoding')

    def test_implemented_forms_decode(self):
        items = [e for f in isa_forms.IMPLEMENTED for e in form_encodings(f)]
        print('\nIMPLEMENTED: %d rows' % len(isa_forms.IMPLEMENTED), file=sys.stderr)
        self.check('IMPLEMENTED', IMPLEMENTED_DIFFERENCES, items, 'ok')

    def test_undefined_forms_do_not_decode(self):
        enum = undefined_encodings()
        sample = ud_sample()
        kinds = collections.Counter(k for k, _ in enum + sample)
        print('\nundefined: %d enumerated, %d sampled from gen.ud_form; by kind: %s' % (
            len(enum), len(sample), ', '.join('%s %d' % kv for kv in sorted(kinds.items()))), file=sys.stderr)
        self.check('undefined', UNDEFINED_DIFFERENCES, [e for _, e in enum + sample], 'invalid')


if __name__ == '__main__':
    unittest.main()
