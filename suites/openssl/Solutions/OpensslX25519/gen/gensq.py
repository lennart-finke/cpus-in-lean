# Generates the run pieces of fe_sq (body between the prologue and the output stores).
#   python3 gensq.py <sq.txt> <out.lean> <first piece> <last piece>   (piece range for test files)
import sys
from asm import read
from symx import Machine, STREGS

FS = 468   # frame: locals 0x1c0, 4 saved registers, the return address at fb + 464
WS = 464   # the part the run writes
PRE = 'sq'
BODY = (0x10236a, 0x102c87)
SLOTS = {0x1cc: 'ebp0', 0x1c8: 'ebx0', 0x1c4: 'edi0', 0x1c0: 'esi0'}
PTRS = ['fp']   # input pointers of ext loads

HDR = """import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
namespace Solutions.OpensslX25519
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000
"""


def ptrs_of(p):
    return [b for b in PTRS if any(kind == 'ext' and (key == b or key.startswith(f"(UInt32.add {b} "))
                                   for (kind, key, _) in p['loads'])]


def split_pieces(ins, maxi=8, maxs=4):
    pieces, cur, st = [], [], 0
    for i in ins:
        s = 1 if (i.ops and i.ops[-1].kind == 'mem' and i.mn != 'leal') else 0
        # an adc must not consume, inside one cbv run, the carry of an add of an immediate
        # (the kernel check of that run explodes): cut before it
        immadd = any(c.mn == 'addl' and c.ops[0].kind == 'imm' for c in cur)
        if cur and (len(cur) >= maxi or st + s > maxs or (i.mn == 'adcl' and immadd)):
            carry = [cur.pop()] if cur[-1].mn == 'mull' else []   # its flags are not modelled
            pieces.append(cur)
            cur, st = carry, 0
        cur.append(i)
        st += s
        if i.mn in ('addl', 'andl') and i.ops[0].kind == 'imm':
            # its flags (an operation on an immediate) must not be carried through further steps
            # of the same cbv run: the check of such runs explodes. Cut after it.
            pieces.append(cur)
            cur, st = [], 0
    if cur:
        pieces.append(cur)
    return pieces


def st(mem, regs, eip, flag, ic):
    r = [regs[x] for x in STREGS]
    # St fields: mem eax ecx edx ebx esp ebp esi edi eip fl ic
    return f"St.m ⟨{mem}, {r[0]}, {r[1]}, {r[2]}, {r[3]}, fb, {r[4]}, {r[5]}, {r[6]}, 0x{eip:x}, efl {flag}, {ic}⟩"


def run(path):
    ins = read(path)
    body = [i for i in ins if BODY[0] <= i.addr < BODY[1]]
    m = Machine({'eax': 'a0', 'ecx': 'hp', 'edx': 'fp', 'ebx': 'ebx0', 'ebp': 'ebp0', 'esi': 'esi0',
                 'edi': 'edi0'}, 'g0')
    m.slots = dict(SLOTS)
    pieces = split_pieces(body)
    out = []
    ic = 5
    for k, pc in enumerate(pieces):
        m.reset_piece()
        for i in pc:
            m.step(i)
        out.append(dict(k=k, ins=pc, inregs=m.p_inregs, inflag=m.p_inflag, loads=list(m.p_loads),
                        defs=list(m.p_defs), stores=list(m.p_stores), xstores=list(m.p_xstores),
                        outregs=dict(m.regs), outflag=m.flag, eip0=pc[0].addr, eip1=pc[-1].nxt,
                        ic0=ic, ic1=ic + len(pc)))
        ic += len(pc)
    return out, m


def lemma(p):
    k = p['k']
    params, seen = [], set()

    def addp(n):
        if n not in seen and not n[0].isdigit():
            seen.add(n)
            params.append(n)
    for r in STREGS:
        addp(p['inregs'][r])
    addp(p['inflag'])
    for (_, _, n) in p['loads']:
        addp(n)
    for d in p['defs']:
        addp(d.name)
    hyps = []
    pre = []
    for (kind, key, n) in p['loads']:
        if kind == 'slot':
            hyps.append(f"(l_{n} : l.lookup {key} = some {n})")
            if key == 0:
                pre.append(f"have r_{n} := hF.rd0 l_{n}; subst r_{n}")
            else:
                pre.append(f"have r_{n} := hF.rd l_{n} {key} rfl; subst r_{n}")
        else:
            hyps.append(f"(l_{n} : rdRaw N.get {key} 4 = {n})")
            pre.append(f"subst l_{n}")
    if any(kind == 'ext' for (kind, _, _) in p['loads']):
        for b in ptrs_of(p):
            hyps.append(f"(h{b} : {b}.toNat + 40 ≤ N.get.size)")
            hyps.append(f"(h{b}' : {b}.toNat + 40 ≤ fb.toNat ∨ fb.toNat + {FS} ≤ {b}.toNat)")
    for d in p['defs']:
        hyps.append(f"(e_{d.name} : {d.name} = {d.term})")
    substs = [f"subst e_{d.name}" for d in reversed(p['defs'])]
    # memory after the stores, frame list, pres
    mem = "N"
    fr = "hF"
    pres = "hP"
    lst = "l"
    first = True
    for (off, v) in p['stores']:
        hs = "hS" if first else "stF_FB" if not mem.startswith("(stF0") else "stF0_FB"
        if off == 0:
            mem = f"(stF0 {mem} fb {FS} {v} {hs} (by decide))"
            fr = f"({fr}.wrF0)"
            pres = f"({pres}.wrF0 (by decide))"
        else:
            mem = f"(stF {mem} fb {FS} {off} {v} {hs} (by decide))"
            fr = f"({fr}.wrF {off} rfl rfl)"
            pres = f"({pres}.wrF (by decide))"
        lst = f"({off}, {v}) :: {lst}"
        first = False
    s0 = st("N.get", p['inregs'], p['eip0'], p['inflag'], p['ic0'])
    s1 = st("N'.get", p['outregs'], p['eip1'], p['outflag'], p['ic1'])
    txt = f"""
/-- {' ; '.join(f'{i.mn} ' + ', '.join(_fmt(o) for o in i.ops) for i in p['ins'])} -/
theorem {PRE}_p{k} (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb {FS}) (l : List (Nat × UInt32))
    (hF : Frame N fb {FS} l) (hP : Pres G N (OutF fb {WS})) ({' '.join(params)} : UInt32)
    {chr(10).join('    ' + h for h in hyps)} :
    ∃ N' : XMem, Run img ({s0})
      ({s1}) ∧
      Frame N' fb {FS} ({lst}) ∧ Pres G N' (OutF fb {WS}) := by
  refine ⟨{mem}, run_of_runOk (k := {len(p['ins'])}) ?_, {fr}, {pres}⟩
  {chr(10).join('  ' + x for x in substs).strip()}
  {chr(10).join('  ' + x for x in pre).strip()}
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv
"""
    return txt


def _fmt(o):
    if o.kind == 'reg':
        return '%' + o.r
    if o.kind == 'imm':
        return '$' + hex(o.v)
    s = f"{hex(o.disp) if o.disp else ''}("
    s += ('%' + o.base) if o.base else ''
    if o.idx:
        s += f",%{o.idx},{o.sc}"
    return s + ')'


def call_piece(p, Nin, Nout, idx, hsz):
    """the main-proof lines running body piece p from memory Nin"""
    lines = []
    for d in p['defs']:
        lines.append(f"obtain ⟨{d.name}, e_{d.name}⟩ : ∃ y : UInt32, y = {d.term} := ⟨_, rfl⟩")
    params, seen = [], set()

    def addp(n):
        if n not in seen and not n[0].isdigit():
            seen.add(n)
            params.append(n)
    for r in STREGS:
        addp(p['inregs'][r])
    addp(p['inflag'])
    for (_, _, n) in p['loads']:
        addp(n)
    for d in p['defs']:
        addp(d.name)
    args = []
    for (kind, key, n) in p['loads']:
        if kind == 'slot':
            args.append("rfl")
        else:
            args.append(f"(hin_{n} {Nin} P{idx})")
    for b in ptrs_of(p):
        args.append(f"(by rw [P{idx}.1]; exact h{b}m) h{b}s")
    for d in p['defs']:
        args.append(f"e_{d.name}")
    k = p['k']
    lines.append(f"obtain ⟨{Nout}, r{idx + 1}, F{idx + 1}, P{idx + 1}⟩ := {PRE}_p{k} G {Nin} fb ({hsz}) _ F{idx} P{idx} "
                 + ' '.join(params) + ' ' + ' '.join(args))
    lines.append(f"have Rn{idx + 1} := Rn{idx}.trans r{idx + 1}")
    return lines


if __name__ == '__main__':
    out, m = run(sys.argv[1])
    a, b = int(sys.argv[3]), int(sys.argv[4])
    txt = HDR + "".join(lemma(p) for p in out[a:b + 1]) + "\nend Solutions.OpensslX25519\n"
    open(sys.argv[2], 'w').write(txt)
    print(len(out), "pieces")
