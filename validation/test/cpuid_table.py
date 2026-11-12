#!/usr/bin/env python3
"""The CPUID table of the IA-32 model against a real AMD EPYC 7742: every feature bit of the 7742's
CPUID dump (test/fixtures/epyc7742-cpuid.txt, InstLatx64, logical CPU #0) is either reported by the
model or masked for a documented reason, and the model reports no bit the dump lacks.

The model side is what `x86run --cpuid --smp 128` prints (CPU 0 of 128, CR4.OSXSAVE = 1, XCR0 = 7:
the state the dump was taken in), i.e. the Lean definitions themselves (`X86/Cpuid.lean`). The bit
names are AMD's (AMD64 APM vol. 3 rev. 3.33, appendix E); the reasons for masked features are kept
here and must match the model's masked features exactly (the Lean comments in `implemented` give
the same reasons).

  cpuid_table.py write [x86run]   regenerate x86_32/CPUID.md
  cpuid_table.py check [x86run]   check the model against the dump and CPUID.md (also a unit test)
"""
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..'))
DUMP = os.path.join(HERE, 'fixtures', 'epyc7742-cpuid.txt')
DOC = os.path.join(ROOT, 'x86_32', 'CPUID.md')
X86RUN = os.path.join(ROOT, 'validation', '.lake', 'build', 'bin', 'x86run')
NCPU = 128          # the dump's package: 128 logical processors
REGS = 'EAX EBX ECX EDX'.split()
MIRROR_MASK = 0x0183F3FF   # 8000_0001:EDX bits AMD copies from 1:EDX (APM vol. 3, E.4.2)

# Feature registers: (leaf, subleaf, register) -> {bit: AMD name}
_MIRROR = {0: 'FPU', 1: 'VME', 2: 'DE', 3: 'PSE', 4: 'TSC', 5: 'MSR', 6: 'PAE', 7: 'MCE', 8: 'CMPXCHG8B',
           9: 'APIC', 12: 'MTRR', 13: 'PGE', 14: 'MCA', 15: 'CMOV', 16: 'PAT', 17: 'PSE36', 23: 'MMX',
           24: 'FXSR'}
BITS = {
    (1, 0, 2): {0: 'SSE3', 1: 'PCLMULQDQ', 3: 'MONITOR', 9: 'SSSE3', 12: 'FMA', 13: 'CMPXCHG16B',
                19: 'SSE41', 20: 'SSE42', 21: 'X2APIC', 22: 'MOVBE', 23: 'POPCNT', 25: 'AES', 26: 'XSAVE',
                27: 'OSXSAVE', 28: 'AVX', 29: 'F16C', 30: 'RDRAND', 31: '(hypervisor)'},
    (1, 0, 3): {**_MIRROR, 11: 'SysEnterSysExit', 19: 'CLFSH', 25: 'SSE', 26: 'SSE2', 28: 'HTT'},
    (6, 0, 0): {2: 'ARAT'},
    (6, 0, 2): {0: 'EffFreq'},
    (7, 0, 1): {0: 'FSGSBASE', 3: 'BMI1', 5: 'AVX2', 7: 'SMEP', 8: 'BMI2', 12: 'PQM', 15: 'PQE', 18: 'RDSEED',
                19: 'ADX', 20: 'SMAP', 23: 'CLFLUSHOPT', 24: 'CLWB', 29: 'SHA'},
    (7, 0, 2): {2: 'UMIP', 22: 'RDPID'},
    (7, 0, 3): {},
    (0xD, 0, 0): {0: 'XCR0 x87', 1: 'XCR0 SSE', 2: 'XCR0 YMM', 9: 'XCR0 PKRU'},
    (0xD, 1, 0): {0: 'XSAVEOPT', 1: 'XSAVEC', 2: 'XGETBV_ECX1', 3: 'XSAVES'},
    (0xD, 1, 2): {},
    (0x80000001, 0, 2): {0: 'LahfSahf', 1: 'CmpLegacy', 2: 'SVM', 3: 'ExtApicSpace', 4: 'AltMovCr8', 5: 'ABM',
                         6: 'SSE4A', 7: 'MisAlignSse', 8: '3DNowPrefetch', 9: 'OSVW', 10: 'IBS', 12: 'SKINIT',
                         13: 'WDT', 17: 'TCE', 22: 'TopologyExtensions', 23: 'PerfCtrExtCore',
                         24: 'PerfCtrExtNB', 26: 'DataBkptExt', 28: 'PerfCtrExtLLC', 29: 'MONITORX',
                         30: 'AddrMaskExt'},
    (0x80000001, 0, 3): {**_MIRROR, 11: 'SysCallSysRet', 20: 'NX', 22: 'MmxExt', 25: 'FFXSR',
                                         26: 'Page1GB', 27: 'RDTSCP', 29: 'LM'},
    (0x80000007, 0, 1): {0: 'McaOverflowRecov', 1: 'SUCCOR', 2: 'HWA', 3: 'ScalableMca',
                         4: '(bit 4, unnamed in APM 3.33)'},
    (0x80000007, 0, 3): {0: 'TS', 3: 'TTP', 4: 'TM', 7: 'HwPstate', 8: 'TscInvariant', 9: 'CPB',
                         10: 'EffFreqRO', 11: 'ProcFeedbackInterface', 12: 'ProcPowerReporting',
                         13: 'ConnectedStandby', 14: 'RAPL'},
    (0x80000008, 0, 1): {0: 'CLZERO', 1: 'InstRetCntMsr', 2: 'RstrFpErrPtrs', 4: 'RDPRU',
                         6: '(bit 6, reserved in APM 3.33)', 8: 'MCOMMIT', 9: 'WBNOINVD',
                         10: '(bit 10, reserved in APM 3.33)', 12: 'IBPB', 13: 'INT_WBINVD', 14: 'IBRS',
                         15: 'STIBP', 17: 'StibpAlwaysOn', 18: 'IbrsPreferred', 19: 'IbrsSameMode',
                         23: 'PPIN', 24: 'SSBD'},
    (0x8000001F, 0, 0): {0: 'SME', 1: 'SEV', 2: 'PageFlushMsr', 3: 'SevEs', 16: '(bit 16)'},
    (0x8000000A, 0, 3): {0: 'NP', 1: 'LbrVirt', 2: 'SVML', 3: 'NRIPS', 4: 'TscRateMsr', 5: 'VmcbClean',
                         6: 'FlushByAsid', 7: 'DecodeAssists', 10: 'PauseFilter',
                         11: '(bit 11, reserved in APM 3.33)', 12: 'PauseFilterThreshold', 13: 'AVIC',
                         15: 'VMSAVEvirt', 16: 'VGIF', 17: 'GMET', 20: 'SpecCtrl'},
}

# Why each masked feature (`implemented f = false` in X86/Cpuid.lean) is not reported.
REASONS = {
    'cx16': 'CMPXCHG16B needs REX.W, i.e. 64-bit mode, which the model does not execute (the x86-64 model lacks it too)',
    'pqm': 'L3 QoS monitoring: no caches are modelled',
    'pqe': 'L3 QoS enforcement: no caches are modelled',
    'ibs': 'instruction-based sampling: no sampling hardware is modelled',
    'perfCtrExtCore': 'no performance events are modelled; the four legacy counters RDPMC needs exist and never count',
    'perfCtrExtNb': 'northbridge counters: no performance events are modelled',
    'perfCtrExtLlc': 'L3 counters: no performance events are modelled',
    'dataBkptExt': 'the DR0..DR3 address-mask MSRs are not modelled (breakpoints match exactly)',
    'adMskExtn': 'the DR0..DR3 address-mask MSRs are not modelled (breakpoints match exactly)',
    'mcaRecovery': 'no machine-check source is modelled and the scalable MCA MSRs are absent (the legacy MCA banks exist)',
    'powerMgmt': 'no thermal sensor, P-states, boost or power reporting are modelled',
    'ext8Misc': 'hints the timing-free model cannot honour (INT_WBINVD, IbrsPreferred, IbrsSameMode) and bits without a documented meaning',
    'svmUnimpl': 'LbrVirt (no LBR stack), AVIC (no AVIC), GMET, and a bit reserved in the APM',
    'ppin': 'the protected processor inventory number MSRs are not modelled',
    'memEncrypt': 'SME/SEV/SEV-ES: no memory encryption is modelled',
}

# Leaves the dump fills that the model reports as zero: the feature that gates them.
MASKED_LEAVES = {0xF: 'pqm', 0x10: 'pqe', 0x8000001B: 'ibs', 0x8000001F: 'memEncrypt', 0x80000020: 'pqe'}

# Register differences in the dump state other than feature bits, with the reason.
OTHER = {
    (0xD, 0, 0): 'XCR0 bit 9 (PKRU) is listed by the 7742 although it has no PKU (CPUID 7:ECX[3] = 0); the model has no PKRU register',
    (0xD, 0, 2): 'maximum XSAVE area size without the PKRU component: 340h instead of 380h',
    (0xD, 9, 0): 'leaf 0xD subleaf 9 (PKRU component): not reported',
    (0xD, 9, 1): 'leaf 0xD subleaf 9 (PKRU component): not reported',
}


def parse_dump(path=DUMP):
    d = {}
    for line in open(path):
        m = re.match(r'CPUID ([0-9A-F]{8}): ([0-9A-F]{8})-([0-9A-F]{8})-([0-9A-F]{8})-([0-9A-F]{8})(?: \[SL (\w+)\])?', line)
        if m:
            leaf = int(m.group(1), 16)
            sub = int(m.group(6), 16) if m.group(6) else None
            d[(leaf, sub)] = tuple(int(m.group(i), 16) for i in range(2, 6))
    return d


SUBLEAF_LEAVES = (7, 0xB, 0xD, 0xF, 0x10, 0x8000001D)   # leaves indexed by ECX


def dump_regs(d, leaf, sub):
    """The dump's value for (leaf, sub): a subleaf-less entry applies to every subleaf of a leaf that
    ignores ECX, and to subleaf 0 of one indexed by ECX (InstLatx64 lists only the valid subleaves)."""
    if (leaf, sub) in d:
        return d[(leaf, sub)]
    if (leaf, None) in d and (leaf not in SUBLEAF_LEAVES or sub == 0):
        return d[(leaf, None)]
    if leaf == 0xB and sub >= 2:
        # an invalid level: EAX = EBX = 0, ECX[7:0] echoes ECX (AMD APM vol. 3, E.3.7 Fn0000_000B)
        return (0, 0, sub & 0xFF, 0)
    return (0, 0, 0, 0)


def run_model(x86run=X86RUN):
    out = subprocess.run([x86run, '--cpuid', '--smp', str(NCPU)], check=True, capture_output=True,
                         text=True).stdout
    regs, feats = {}, []
    for line in out.splitlines():
        p = line.split()
        if p[0] == 'cpuid':
            regs[(int(p[1], 16), int(p[2], 16))] = tuple(int(x, 16) for x in p[3:7])
        elif p[0] == 'feature':
            feats.append((p[1], int(p[2], 16), int(p[3], 16), int(p[4]), int(p[5], 16), p[6] == 'implemented'))
    return regs, feats


def analyse(regs, feats, d):
    """Rows of the table and the list of errors."""
    errors, rows = [], []
    owner = {}
    for name, leaf, sub, k, mask, impl in feats:
        for b in range(32):
            if mask >> b & 1:
                owner[(leaf, sub, k, b)] = (name, impl)
    masked = {f[0] for f in feats if not f[5]}
    if masked != set(REASONS):
        errors.append(f'masked features {sorted(masked)} != documented reasons {sorted(REASONS)}')
    for (leaf, sub, k), names in BITS.items():
        dv = dump_regs(d, leaf, sub)[k]
        mv = regs.get((leaf, sub), (0, 0, 0, 0))[k]
        for b in range(32):
            if not (dv >> b & 1 or mv >> b & 1):
                continue
            name = names.get(b, f'(bit {b})')
            if mv >> b & 1 and not dv >> b & 1:
                errors.append(f'{leaf:08X}.{sub} {REGS[k]}[{b}] {name}: reported but not in the 7742 dump')
                continue
            f = owner.get((leaf, sub if leaf in (7, 0xD) else 0, k, b))
            if f is None and (leaf, k) == (0x80000001, 3) and MIRROR_MASK >> b & 1:
                f = owner.get((1, 0, 3, b))   # AMD copies these bits from CPUID 1:EDX
            if mv >> b & 1:
                status = 'reported'
                if f is None and (leaf, sub, k) not in ((0xD, 0, 0),) and not (leaf, k, b) == (1, 2, 27):
                    errors.append(f'{leaf:08X}.{sub} {REGS[k]}[{b}] {name}: reported, no Feature covers it')
            elif (leaf, sub, k) in OTHER:
                status = 'not reported: ' + OTHER[(leaf, sub, k)]
            elif f is None:
                errors.append(f'{leaf:08X}.{sub} {REGS[k]}[{b}] {name}: in the dump, neither reported nor a masked Feature')
                continue
            else:
                fname, impl = f
                if impl:
                    errors.append(f'{leaf:08X}.{sub} {REGS[k]}[{b}] {name}: Feature {fname} implemented but bit clear')
                    continue
                status = f'masked ({fname}): {REASONS.get(fname, "NO REASON")}'
            rows.append((leaf, sub, k, b, name, status))
    # every other register of every leaf the dump or the model has: equal, or explained
    keys = {(l, 0 if s is None else s) for (l, s) in d} | set(regs)
    for (leaf, sub) in sorted(keys, key=lambda x: (x[0], -1 if x[1] is None else x[1])):
        for s in [sub]:
            dv, mv = dump_regs(d, leaf, s), regs.get((leaf, s), (0, 0, 0, 0))
            for k in range(4):
                if (leaf, s, k) in BITS or dv[k] == mv[k]:
                    continue
                if leaf in MASKED_LEAVES and mv == (0, 0, 0, 0):
                    continue
                if (leaf, s, k) in OTHER:
                    continue
                errors.append(f'{leaf:08X}.{s} {REGS[k]}: model {mv[k]:08X}, dump {dv[k]:08X} (unexplained)')
    # the native campaign gates its families on these CPUID bits (native_fp.FEATURES): the model must
    # report every one of them, or a family would run on the EPYC but be skipped on the model
    sys.path.insert(0, HERE)
    import native_fp
    for name, (leaf, sub, k, b) in native_fp.FEATURES.items():
        if not regs.get((leaf, sub), (0, 0, 0, 0))[k] >> b & 1:
            errors.append(f'native_fp.FEATURES[{name!r}] ({leaf:08X}.{sub} {REGS[k]}[{b}]) is not reported by the model')
    for leaf, f in MASKED_LEAVES.items():
        if f not in masked:
            errors.append(f'leaf {leaf:08X} gated by {f}, which is not masked')
        if any(regs.get((leaf, s), (0, 0, 0, 0)) != (0, 0, 0, 0) for s in range(10)):
            errors.append(f'leaf {leaf:08X} is not zero although {f} is masked')
    return rows, errors


def render(rows, d):
    rep = sum(1 for r in rows if r[5] == 'reported')
    msk = [r for r in rows if r[5] != 'reported']
    out = ['# CPUID of the model vs. a real AMD EPYC 7742', '',
           'Generated by `validation/test/cpuid_table.py write` from what the model reports',
           '(`x86run --cpuid --smp 128`: CPU 0 of 128 with CR4.OSXSAVE = 1 and XCR0 = 7, the state the dump was',
           'taken in) and the CPUID dump of a real 7742 (`validation/test/fixtures/epyc7742-cpuid.txt`, InstLatx64,',
           'logical CPU #0); `cpuid_table.py check` (a unit test) fails if the model, the reasons or this file',
           'drift apart. Do not edit by hand. The Lean side: `X86/Cpuid.lean` (`implemented`, with the same',
           'reasons) and `X86/Proofs/Ext.lean` (`cpuid_epyc`, `cpuid_epyc_dump`: no reported bit is missing',
           'from the dump).', '',
           f'Feature bits set in the dump: {len(rows)}; reported by the model: {rep}; not reported: {len(msk)}.',
           'Identity, brand string, cache/TLB descriptors (8000_0005/6/19/1D), address sizes (8000_0008),',
           'MONITOR (5), the topology (1, 0Bh, 8000_0008 ECX, 8000_001E) and the SVM revision/ASIDs equal the dump',
           '(the topology fields for N CPUs: `Cpuid.topo`; with N = 1 HTT and CmpLegacy are 0).', '',
           '## Not reported', '', '| leaf.sub | reg | bit | name | reason |', '|---|---|---|---|---|']
    for (leaf, sub, k, b, name, status) in msk:
        out.append(f'| {leaf:08X}.{sub} | {REGS[k]} | {b} | {name} | {status.split(": ", 1)[1] if ": " in status else status} |'
                   .replace('| masked', '|'))
    out += ['', 'Leaves the dump fills and the model reports as zero (their feature is masked): ' +
            ', '.join(f'{l:08X}h ({f})' for l, f in sorted(MASKED_LEAVES.items())) + '.', '',
            '## Every feature bit of the dump', '', '| leaf.sub | reg | bit | name | model |', '|---|---|---|---|---|']
    for (leaf, sub, k, b, name, status) in rows:
        st = 'reported' if status == 'reported' else ('not reported (' + status.split(' ', 1)[1].split(')')[0].lstrip('(') + ')'
                                                     if status.startswith('masked') else 'not reported')
        out.append(f'| {leaf:08X}.{sub} | {REGS[k]} | {b} | {name} | {st} |')
    return '\n'.join(out) + '\n'


def main():
    if len(sys.argv) < 2 or sys.argv[1] not in ('write', 'check'):
        print(__doc__)
        return 2
    x86run = sys.argv[2] if len(sys.argv) > 2 else X86RUN
    d = parse_dump()
    regs, feats = run_model(x86run)
    rows, errors = analyse(regs, feats, d)
    for e in errors:
        print('cpuid_table: ' + e)
    text = render(rows, d)
    if sys.argv[1] == 'write':
        open(DOC, 'w').write(text)
    elif not os.path.exists(DOC) or open(DOC).read() != text:
        errors.append('x86_32/CPUID.md is out of date (cpuid_table.py write)')
        print('cpuid_table: ' + errors[-1])
    rep = sum(1 for r in rows if r[5] == 'reported')
    print(f'cpuid_table: {len(rows)} feature bits in the 7742 dump, {rep} reported, {len(rows) - rep} not reported '
          f'(all with a reason), {len(errors)} errors')
    return 1 if errors else 0


if __name__ == '__main__':
    sys.exit(main())
