"""Shared pieces of the extended native families (bundle format v3; validation/test/FP-HARDWARE.md,
"The extended bundle").

* `record3`: a v3 record: the v2 record of `fp_cases.record` (with any GPRs, ESP included) followed by
  the 128-byte extension (x87 FIP/FDP/FOP inputs, a 64-byte dump window, up to eight dword patches of the
  arena; native/signal_oracle.c, FpMain.lean).
* `layout`: the instruction layout as the model decodes it (Decode.lean `decodeRaw`; the same as
  native/record_check.h `rc_decode`), for generators that need the position of a displacement.
* `select`: model-in-the-loop case selection for generators that produce candidate encodings (the
  encoding fuzz, the random integer core): a candidate becomes a case only if the oracle's own validation
  (native/record_check.h, host build) accepts it and the model (`x86fp --probe`, compatibility and legacy
  mode) runs it to an outcome the oracle can observe, with every memory access inside the model's 256 KiB
  (a #PF's CR2 below 0x40000; the model maps exactly what the oracle process maps there). Instructions
  whose result depends on the operating system or on time (CPUID, RDTSC, RDRAND, UMIP-emulated SGDT, ...)
  get per-case 'observe' fields. Every refusal is counted by reason (the fuzz's blind spots). The
  selected cases depend on the model (the selection runs it), so they are cached per model hash.
"""
import collections
import concurrent.futures
import hashlib
import json
import os
import struct
import subprocess
import tempfile
from pathlib import Path

import fp_cases

HERE = Path(__file__).resolve().parent
X86FP = HERE.parent / '.lake' / 'build' / 'bin' / 'x86fp'
CACHE = HERE / 'out' / '.select-cache'
V3_SIZE = 904
VECTOR_SIGNAL = {0: 8, 1: 5, 3: 5, 4: 11, 5: 11, 6: 4, 11: 7, 12: 7, 13: 11, 14: 11, 16: 8, 17: 7, 19: 8}
ARENA = 0x10000
CODE = 0x20000
ARITH = 0x8D5


def record3(code, *, regs=None, ext_flags=0, fop=0, fip=0, fdp=0, dump=None, patches=(), **kw):
    """A v3 record: `regs` maps register numbers 0..7 (ESP = 4 included) to values; `dump` an arena
    offset whose 64 bytes the row reports; `patches` [(arena offset, dword[, count])] (at most 8; the
    dword is stored count times from the offset, in order)."""
    r = bytearray(fp_cases.record(code, **kw))
    for k, v in (regs or {}).items():
        struct.pack_into('<Q', r, 16 + 8 * k, v & 0xFFFFFFFF)
    flags = ext_flags | (2 if dump is not None else 0)
    patches = [p if len(p) == 3 else (p[0], p[1], 1) for p in patches]   # (offset, dword, count)
    assert len(patches) <= 8 and all(0 <= o and o + 4 * n <= 8192 for o, _, n in patches)
    assert dump is None or 0 <= dump <= 8192 - 64
    ext = struct.pack('<IHHQQB7x', flags, fop, dump or 0, fip, fdp, len(patches))
    ext += b''.join(struct.pack('<HHI', o, n, v & 0xFFFFFFFF) for o, v, n in patches)
    return bytes(r) + ext.ljust(128, b'\0')


def meta3(family, name, code, **kw):
    """Metadata of a v3 case: its family is its own campaign group (new campaigns, never mixed with
    the cases of earlier families)."""
    m = fp_cases.meta(family, name, code, **kw)
    m['campaign_group'] = family
    return m


# ---------------------------------------------------------------------------------------------------
# Instruction layout (Decode.lean decodeRaw / opInfo)

PREFIXES = {0x26, 0x2E, 0x36, 0x3E, 0x64, 0x65, 0x66, 0x67, 0xF0, 0xF2, 0xF3}


def op_info(op):
    if op >= 0x300: return 0x11
    if op >= 0x200: return 0x01
    if op < 0x100:
        b = op
        if b < 0x40:
            lo = b & 7
            return 0x01 if lo < 4 else 0x10 if lo == 4 else 0x30 if lo == 5 else 0
        if b < 0x60: return 0
        if 0x70 <= b <= 0x7F: return 0x10
        if 0x84 <= b <= 0x8F: return 0x01
        if 0xB0 <= b <= 0xB7: return 0x10
        if 0xB8 <= b <= 0xBF: return 0x30
        if 0xD0 <= b <= 0xD3 or 0xD8 <= b <= 0xDF: return 0x01
        if 0xE0 <= b <= 0xE7: return 0x10
        return {0x62: 1, 0x63: 1, 0x68: 0x30, 0x69: 0x31, 0x6A: 0x10, 0x6B: 0x11, 0x80: 0x11, 0x82: 0x11,
                0x83: 0x11, 0x81: 0x31, 0x9A: 0x50, 0xEA: 0x50, 0xA0: 0x40, 0xA1: 0x40, 0xA2: 0x40, 0xA3: 0x40,
                0xA8: 0x10, 0xA9: 0x30, 0xC0: 0x11, 0xC1: 0x11, 0xC6: 0x11, 0xC7: 0x31, 0xC2: 0x20, 0xCA: 0x20,
                0xC4: 1, 0xC5: 1, 0xC8: 0x60, 0xCD: 0x10, 0xD4: 0x10, 0xD5: 0x10, 0xEB: 0x10, 0xE8: 0x30,
                0xE9: 0x30, 0xF6: 0x71, 0xF7: 0x81, 0xFE: 1, 0xFF: 1}.get(b, 0)
    b = op - 0x100
    if b <= 3 or b == 0x0D or 0x18 <= b <= 0x1F or 0x20 <= b <= 0x23 or 0x40 <= b <= 0x4F or 0x90 <= b <= 0x9F:
        return 0x01
    if 0x80 <= b <= 0x8F: return 0x30
    if (0x10 <= b <= 0x17 or 0x28 <= b <= 0x2F or 0x50 <= b <= 0x6F or 0x74 <= b <= 0x76 or b == 0x79 or
            0x7C <= b <= 0x7F or 0xD0 <= b <= 0xFE):
        return 0x01
    if 0x70 <= b <= 0x73 or b == 0xC2 or 0xC4 <= b <= 0xC6: return 0x11
    if b == 0x78: return 0x91
    if b in (0xA3, 0xA5, 0xAB, 0xAD, 0xAE, 0xAF) or 0xB0 <= b <= 0xB9 or 0xBB <= b <= 0xBF or \
            b in (0xC0, 0xC1, 0xC3, 0xC7, 0xFF):
        return 0x01
    if b in (0xA4, 0xAC, 0xBA): return 0x11
    return 0


def layout(code):
    """(length, op, prefix count, modrm offset or None, displacement (offset, size) or None, immediate
    (offset, size) or None) of `code` followed by 0xCC bytes, as the model decodes it (length 16: #GP)."""
    b = bytes(code) + b'\xcc' * 40
    n = 0; opsz = adsz = 4; rep = 0
    while n < 15 and b[n] in PREFIXES:
        if b[n] == 0x66: opsz = 2
        elif b[n] == 0x67: adsz = 2
        elif b[n] in (0xF2, 0xF3): rep = b[n]
        n += 1
    pfx = n
    if n >= 15: return 16, 0x1000, pfx, None, None, None
    op = b[n]; n += 1; vx = 0; pre = None
    if op == 0x0F:
        b1 = b[n]; n += 1
        if b1 in (0x38, 0x3A): op = (0x200 if b1 == 0x38 else 0x300) + b[n]; n += 1
        else: op = 0x100 + b1
    elif op in (0xC4, 0xC5):
        v1 = b[n]; n += 1
        if v1 & 0xC0 == 0xC0:
            if op == 0xC5: vx = 0x10000 | v1; op = 0x100 + b[n]; n += 1
            else:
                v2, ob, mp = b[n], b[n + 1], v1 & 0x1F; n += 2; vx = 0x18000 | v2
                op = mp * 0x100 + ob if 1 <= mp <= 3 else ob
        else:
            pre = n - 1
    info = 0 if vx and op < 0x100 else op_info(op)
    modrm_at = disp = imm = None; reg = 0
    if info & 1:
        if pre is None: modrm_at = n; n += 1
        else: modrm_at = pre
        modrm = b[modrm_at]; md, rm, reg = modrm >> 6, modrm & 7, modrm >> 3 & 7
        if md != 3 and not 0x120 <= op <= 0x123:
            if adsz == 4:
                if rm == 4:
                    sib = b[n]; n += 1
                    if sib & 7 == 5 and md == 0: disp = (n, 4); n += 4
                elif rm == 5 and md == 0: disp = (n, 4); n += 4
                if md == 1: disp = (n, 1); n += 1
                elif md == 2: disp = (n, 4); n += 4
            else:
                if md == 0 and rm == 6: disp = (n, 2); n += 2
                elif md == 1: disp = (n, 1); n += 1
                elif md == 2: disp = (n, 2); n += 2
    kind = info >> 4
    if kind:
        pp = (vx & 3) if vx else 2 if rep == 0xF3 else 3 if rep == 0xF2 else 1 if opsz == 2 else 0
        k = {1: 1, 2: 2, 3: opsz, 4: adsz, 5: opsz, 6: 2, 7: 1 if reg < 2 else 0, 8: opsz if reg < 2 else 0,
             9: 1 if pp in (1, 3) else 0}.get(kind, 0)
        if k: imm = (n, k); n += k
        if kind == 5: n += 2
        elif kind == 6 or (kind == 9 and k): n += 1
    return n, op, pfx, modrm_at, disp, imm


def windows_safe(code, low=0x50000, high=0x1200000):
    """No four consecutive bytes of the instruction and the 0xCC filling read as a dword in [low, high):
    with every GPR below 0x12000 (base + 8 x index < 0xA2000), no displacement or immediate that any
    decoding could take as an address reaches the oracle's image at 1 MiB."""
    b = bytes(code) + b'\xcc' * 3
    return all(not low <= int.from_bytes(b[i:i + 4], 'little') < high for i in range(len(b) - 3))


# ---------------------------------------------------------------------------------------------------
# Instructions whose outcome depends on the OS, the machine or time: per-case observe fields.

GPR = ['r0', 'r1', 'r2', 'r3', 'r4', 'r5', 'r6', 'r7']


def os_dependent(op, modrm, vexbits, mem):
    """(observe fields, reason) for an instruction (the model's decode: op, ModRM, the probe's VEX/prefix
    bits) whose result the model cannot know, else None."""
    vex = vexbits & 1
    pp = vexbits >> 1 & 3
    if vex:
        return None
    reg = modrm >> 3 & 7
    if op == 0x1A2: return (['r0', 'r1', 'r2', 'r3'], 'CPUID: machine and CPU specific')
    if op == 0x131: return (['r0', 'r2'], 'RDTSC: time')
    if op == 0x133: return (['*'], 'RDPMC: CR4.PCE is set by Linux per task (perf)')
    if op == 0x101 and modrm == 0xF9: return (['r0', 'r1', 'r2'], 'RDTSCP: time and TSC_AUX (CPU number)')
    if op == 0x101 and modrm == 0xFD: return (['r0', 'r2', 'eflags'], 'RDPRU: MPERF/APERF')
    if op == 0x1C7 and not mem and reg in (6, 7):
        return (GPR + ['eflags'], 'RDRAND/RDSEED/RDPID: random numbers, CPU number')
    if op == 0x101 and 0xD8 <= modrm <= 0xDF:
        return (['*'], 'SVM instruction: depends on EFER.SVME (KVM)')
    if op == 0x101 and (reg in (0, 1, 4) and (mem or reg == 4)):
        return (['*'], 'SGDT/SIDT/SMSW: emulated by Linux under UMIP (dummy values)')
    if op == 0x100 and reg in (0, 1, 4, 5):
        return (['*'], 'SLDT/STR (UMIP), VERR/VERW: depend on the kernel GDT/LDT')
    if op in (0x102, 0x103):
        return (['*'], 'LAR/LSL: depend on the kernel GDT/LDT')
    if op in (0x17, 0x1B2) or (op == 0x8E and reg == 2):
        return (['*'], 'SS loads: depend on the kernel GDT (the model has none)')
    return None


# ---------------------------------------------------------------------------------------------------
# Model-in-the-loop selection

def _bin(records):
    v3 = all(len(r) == V3_SIZE for r in records)
    assert v3 or all(len(r) == fp_cases.SIZE for r in records)
    return (len(records) | 1 << 63 | (1 << 62 if v3 else 0)).to_bytes(8, 'little') + b''.join(records)


def _run_model(records, compat, probe, model):
    with tempfile.NamedTemporaryFile(suffix='.bin', delete=False) as f:
        f.write(_bin(records)); name = f.name
    try:
        args = [str(model)] + (['--compat'] if compat else []) + (['--probe'] if probe else []) + [name]
        p = subprocess.run(args, capture_output=True, text=True, timeout=3600)
        if p.returncode != 0: raise RuntimeError(f'x86fp failed: {p.stderr.strip()[:300]}')
        lines = p.stdout.splitlines()
        assert lines[0] == f'BEGIN {len(records):016x}' and lines[-1] == 'END'
        return [[int(x, 16) for x in l.split()] for l in lines[1:-1]]
    finally:
        os.unlink(name)


def _parallel(records, fn, chunk=2000):
    parts = [records[i:i + chunk] for i in range(0, len(records), chunk)]
    with concurrent.futures.ThreadPoolExecutor(os.cpu_count() or 4) as pool:
        out = []
        for r in pool.map(fn, parts): out += r
    return out


_checker = None


def checker():
    global _checker
    if _checker is None:
        d = tempfile.mkdtemp(prefix='rcheck')
        path = Path(d) / 'check_records'
        cc = os.environ.get('HOST_CC', 'cc')
        subprocess.run([cc, '-O2', '-Wall', '-Wextra', '-Werror', '-o', str(path), str(HERE / 'native/check_records.c')],
                       check=True)
        _checker = path
    return _checker


def check(records):
    """{index: reason} of the records the oracle refuses on the EPYC (vendor AMD)."""
    p = subprocess.run([str(checker()), '--amd'], input=_bin(records), capture_output=True)
    if p.returncode not in (0, 3): raise RuntimeError(p.stderr.decode())
    out = {}
    for line in p.stdout.decode().splitlines():
        if line.startswith('REJECT'):
            f = line.split(maxsplit=3); out[int(f[1], 16)] = f[3]
    return out


def model_hash(model=X86FP):
    return hashlib.sha256(Path(model).read_bytes()).hexdigest()


def select(candidates, stats, model=X86FP):
    """The candidates (raw, meta) that become cases (see the module documentation); `stats` (a Counter)
    gets the number of candidates refused per reason. The metadata of a selected case gets the model's
    decode (`model_op`) and, for OS-dependent instructions, `observe_fields` and `reason`; `compat_only`
    when legacy protected mode gives another result (fp_model_check.py)."""
    if not candidates: return []
    raws = [r for r, _ in candidates]
    refused = check(raws)
    for why in refused.values(): stats['refused by the oracle validation: ' + why.split(' (')[0].split(':')[0]] += 1
    keep = [i for i in range(len(candidates)) if i not in refused]
    sub = [raws[i] for i in keep]
    pc = _parallel(sub, lambda r: _run_model(r, True, True, model))
    pl = _parallel(sub, lambda r: _run_model(r, False, True, model))
    good = []
    for i, c, l in zip(keep, pc, pl):
        status, vec, err, eip, cr2, length, op, modrm, bits = c[1:10]
        if status or l[1]:
            stats['the model cannot run it (unsupported outcome)'] += 1; continue
        if vec not in VECTOR_SIGNAL:
            stats[f'model vector {vec} has no Linux signal'] += 1; continue
        if not CODE <= eip < CODE + 0x1000:
            stats['model EIP outside the code page'] += 1; continue
        if vec == 14 and cr2 >= 0x40000:
            stats['model #PF outside the low 256 KiB'] += 1; continue
        good.append((i, c))
    if not good: return []
    rows_c = _parallel([raws[i] for i, _ in good], lambda r: _run_model(r, True, False, model))
    rows_l = _parallel([raws[i] for i, _ in good], lambda r: _run_model(r, False, False, model))
    out = []
    for (i, c), rc, rl in zip(good, rows_c, rows_l):
        raw, m = candidates[i]
        m = dict(m)
        status, vec, err, eip, cr2, length, op, modrm, bits = c[1:10]
        m['model_op'] = f'{op:03x}/{modrm:02x}' if length else 'undecoded'
        od = os_dependent(op, modrm, bits, bits >> 5 & 1) if length else None
        if od:
            m['observe_fields'], m['reason'] = od
        if rc[1:] != rl[1:]: m['compat_only'] = True
        stats['selected'] += 1
        out.append((raw, m))
    return out


def cached(family, key, produce):
    """produce() -> (cases, stats), cached under test/out/.select-cache per (family, key, model hash,
    the sources of the selection)."""
    sources = [HERE / 'native_ext.py', HERE / 'native/record_check.h', HERE / 'fp_cases.py']
    sources += [HERE / f'{n}.py' for n in ('native_fuzz', 'native_int', 'native_depth', 'native_x87rules', 'native_flags')
                if (HERE / f'{n}.py').exists()] + [HERE / 'gen.py']
    h = hashlib.sha256(json.dumps([family, key]).encode())
    h.update(model_hash().encode())
    for s in sources: h.update(s.read_bytes())
    tag = h.hexdigest()[:24]
    path = CACHE / f'{family}-{tag}'
    if (path.with_suffix('.json')).exists():
        metas = json.loads(path.with_suffix('.json').read_text())
        data = path.with_suffix('.bin').read_bytes()
        cases = [(data[k * V3_SIZE:(k + 1) * V3_SIZE], m) for k, m in enumerate(metas['cases'])]
        return cases, collections.Counter(metas['stats'])
    cases, stats = produce()
    CACHE.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix('.tmp')
    tmp.write_bytes(b''.join(r for r, _ in cases))
    os.replace(tmp, path.with_suffix('.bin'))
    path.with_suffix('.json').write_text(json.dumps(dict(cases=[m for _, m in cases], stats=stats)))
    return cases, stats


STATS = {}   # family -> Counter of the last generation (written into the bundle manifest by prepare)
