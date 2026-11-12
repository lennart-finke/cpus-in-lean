#!/usr/bin/env python3
"""Independent reference for the CPUID topology of the first N threads of an AMD EPYC 7742 package,
written from the AMD APM vol. 3 (appendix E: Fn0000_0001_EBX, Fn0000_000B, Fn8000_0001_ECX[CmpLegacy],
Fn8000_0008_ECX, Fn8000_001E) and the CPUID dump of a real 7742 (InstLatx64
AuthenticAMD0830F10_K17_Rome: 64 cores, 2 threads per core, APIC ID = 2*core + thread, leaf 1 EBX
00800800h, 0Bh subleaf 0 = 1/2/100h, subleaf 1 = 7/80h/201h, 8000_0008 ECX 707Fh, 8000_001E EBX 100h),
not from the Lean model. The model describes N threads as the package with only its first N threads
enabled; a core's thread count is the number of its enabled threads.

  topo_ref.py check N transcript     check the `smpn k:` lines of the test kernel (x86sys --smp N
                                     --cmdline smpn=N) against the expectation
  topo_ref.py cpuinfo N transcript   check Linux's /proc/cpuinfo topology fields (processor,
                                     physical id, siblings, core id, cpu cores, apicid, initial apicid)
"""
import re
import sys

THREADS_PER_CORE = 2      # 7742: SMT2
APIC_ID_SIZE = 7          # Fn8000_0008_ECX[15:12] on the 7742: 128 logical processors per package
CLFLUSH_QW = 8            # Fn0000_0001_EBX[15:8]: 64-byte lines
MAX_EXT = 0x80000020      # Fn8000_0000_EAX of the 7742: 8000_001E (and 8000_001D) are reachable


def core_of(k):
    return k // THREADS_PER_CORE


def threads_in_core(n, k):
    """Enabled threads of the core holding thread k (the first n threads are enabled)."""
    first = core_of(k) * THREADS_PER_CORE
    return min(THREADS_PER_CORE, n - first)


def expected(n, k):
    """CPUID topology fields of logical processor k (initial APIC ID k) of n."""
    e = {}
    # Fn0000_0001_EBX: [31:24] LocalApicId, [23:16] LogicalProcessorCount (valid with HTT), [15:8] CLFLUSH
    e['apic'] = k
    e['l1ebx'] = (k << 24) | ((n if n >= 2 else 0) << 16) | (CLFLUSH_QW << 8)
    # Fn0000_0001_EDX[HTT] / Fn8000_0001_ECX[CmpLegacy]: more than one logical processor in the package
    e['htt'] = 1 if n >= 2 else 0
    e['cmpl'] = 1 if n >= 2 else 0
    # Fn0000_000B subleaf 0 (SMT level): shift to the core ID, logical processors in this core, level
    # type 1 (SMT) << 8 | level number 0, x2APIC ID; subleaf 1 (core level): shift to the package ID
    # (ApicIdSize), logical processors in the package, type 2 << 8 | 1, x2APIC ID
    e['b0'] = (1, threads_in_core(n, k), 0x100, k)
    e['b1'] = (APIC_ID_SIZE, n, 0x201, k)
    # Fn8000_0008_ECX: [15:12] ApicIdSize, [7:0] NC = threads - 1
    e['c88'] = (APIC_ID_SIZE << 12) | (n - 1)
    # Fn8000_001E (xAPIC mode): EAX ExtendedApicId = APIC ID, EBX [15:8] ThreadsPerComputeUnit - 1,
    # [7:0] ComputeUnitId = the core, ECX NodesPerProcessor - 1 = 0, NodeId 0 (one node)
    e['e1e'] = (k, ((min(THREADS_PER_CORE, n) - 1) << 8) | core_of(k), 0)
    return e


LINE = re.compile(r'smpn (\d+): apic=(\w+) l1ebx=(\w+) htt=(\d+) b0=(\w+),(\w+),(\w+),(\w+) '
                  r'b1=(\w+),(\w+),(\w+),(\w+) cmpl=(\d+) c88=(\w+) maxext=(\w+) e1e=(\w+),(\w+),(\w+)')


def check(n, path):
    seen, bad = 0, 0
    for line in open(path, errors='replace'):
        m = LINE.search(line)
        if not m:
            continue
        g = [int(x, 16) if i not in (0, 3, 12) else int(x) for i, x in enumerate(m.groups())]
        k = g[0]
        e = expected(n, k)
        got = {'apic': g[1], 'l1ebx': g[2], 'htt': g[3], 'b0': tuple(g[4:8]), 'b1': tuple(g[8:12]),
               'cmpl': g[12], 'c88': g[13], 'e1e': tuple(g[15:18])}
        maxext = g[14]
        if maxext != MAX_EXT:
            bad += 1
            print(f'cpu {k}: highest extended leaf {maxext:#x}, expected {MAX_EXT:#x}')
        for key in e:
            if got[key] != e[key]:
                bad += 1
                print(f'cpu {k}: {key} = {got[key]}, expected {e[key]}')
        seen += 1
    if seen != n:
        print(f'{seen} of {n} CPUs reported')
        bad += 1
    print(f'topo_ref: {seen} CPUs of {n} checked, {bad} differences')
    return bad == 0


def linux_expected(n, k):
    """/proc/cpuinfo topology of processor k (Linux 6.12, arch/x86/kernel/cpu/topology_common.c and
    proc.c): the SMT and core shifts come from leaf 0Bh (1 and ApicIdSize = 7), so physical id =
    APIC ID >> 7, core id = (APIC ID & 7Fh) >> 1, siblings = online threads of the package, cpu cores
    = cores with an online thread."""
    cores = len({core_of(j) for j in range(n)})
    return {'processor': k, 'physical id': k >> APIC_ID_SIZE, 'siblings': n,
            'core id': (k & ((1 << APIC_ID_SIZE) - 1)) >> 1, 'cpu cores': cores, 'apicid': k,
            'initial apicid': k}


def cpuinfo(n, path):
    fields, cur = [], None
    for line in open(path, errors='replace'):
        m = re.match(r'^(processor|physical id|siblings|core id|cpu cores|apicid|initial apicid)\s*:\s*(\d+)\s*$',
                     line.replace('\r', ''))
        if not m:
            continue
        if m.group(1) == 'processor':
            cur = {}
            fields.append(cur)
        if cur is not None:
            cur[m.group(1)] = int(m.group(2))
    bad = 0
    for k, f in enumerate(fields):
        e = linux_expected(n, k)
        for key in e:
            if f.get(key) != e[key]:
                bad += 1
                print(f'processor {k}: {key} = {f.get(key)}, expected {e[key]}')
    if len(fields) != n:
        print(f'{len(fields)} processors listed, expected {n}')
        bad += 1
    print(f'topo_ref: /proc/cpuinfo of {len(fields)} processors checked, {bad} differences')
    return bad == 0


if __name__ == '__main__':
    if len(sys.argv) != 4 or sys.argv[1] not in ('check', 'cpuinfo'):
        print(__doc__)
        sys.exit(2)
    ok = (check if sys.argv[1] == 'check' else cpuinfo)(int(sys.argv[2]), sys.argv[3])
    sys.exit(0 if ok else 1)
