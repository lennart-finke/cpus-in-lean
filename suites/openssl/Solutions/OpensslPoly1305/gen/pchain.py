"""Composite theorems: a chain of psym pieces as one run (`chain`)."""
import re
from psym import V, REGS, KEYWORDS

SSA = re.compile(r'^[vgx]\d+$')


def lookup_proof(lst, k, tail_proof):
    """proof of `L.lookup k = some v` for L = entries `lst` (first first) :: tail"""
    keys = [j for (j, _) in lst]
    if k in keys:
        i = keys.index(k)
        pf = "lk_here"
        for _ in reversed(lst[:i]):
            pf = f"(lk_skip {pf} rfl)"
        return pf
    pf = tail_proof
    for _ in reversed(lst):
        pf = f"(lk_skip {pf} rfl)"
    return pf


def names_in(t):
    return [n for n in re.findall(r'(?<![\w.])([a-z][a-z_]*\d*)(?![\w.])', t) if n not in KEYWORDS]


def chain(seg, pieces, name, ins, init_U, init_C, exts, outs_U, outs_C, pnames, extra_hyps=(),
          branch_args=None, extra_concl=None, keep=(), explicit_C=False):
    """ins: the start state (regs, esp, eip, flag, ic); init_U/init_C: [(off, V)] known words at the start;
    exts: [(pointer, L)] read-only regions; outs_U/outs_C: offsets listed in the conclusion; pnames: the
    piece theorems; branch_args[i]: arguments for the branch hypotheses of piece i; extra_concl: a
    conjunct proved by `subst` of all definitions and `rfl`; keep: SSA names to quantify anyway."""
    C = seg.Cname
    regs0, esp0, eip0, fl0, ic0 = ins
    inputs, seen = [], {'U', C}

    def addn(t):
        for n in names_in(t):
            if n not in seen:
                seen.add(n)
                inputs.append(n)
    for r in REGS:
        addn(regs0[r].term())
    addn(fl0)
    for (_, v) in list(init_U) + list(init_C):
        addn(v.term())
    extloads = []
    for p in pieces:
        for (kind, key, v) in p['loads']:
            if kind == 'ext' and not v.is_lit() and v.term() not in [x for (_, x) in extloads]:
                al = getattr(seg, 'alias', {})
                if key in al:
                    extloads.append((f"(UInt32.add {al[key][0]} {al[key][1]})", v.term()))
                else:
                    extloads.append((key, v.term()))
                addn(v.term())
    for p in pieces:
        if p['ret'] is not None:
            addn(p['ret'].term())
    hyps = [f"(hlU : LK lU [{', '.join(f'({o}, {v.term()})' for (o, v) in init_U)}])",
            f"(hlC : LK lC [{', '.join(f'({o}, {v.term()})' for (o, v) in init_C)}])"]
    for (pn, L) in exts:
        hyps.append(f"(E_{pn} : ExtR G P {pn} {L})")
    for (key, x) in extloads:
        hyps.append(f"(hx_{x} : rdRaw G.get {key} 4 = {x})")
    for (nm, prop, vs) in seg.facts:
        hyps.append(f"({nm} : {prop.replace('N.get.size', 'G.get.size')})")
    hyps += list(extra_hyps)

    def lk_init(init, k, hname):
        idx = [o for (o, _) in init].index(k)
        return f"{hname}" + ".2" * idx + ".1"

    def lkp(lst, init, o, hname):
        tail = lk_init(init, o, hname) if o not in [x for (x, _) in lst] else None
        return lookup_proof(lst, o, tail)
    lines = []
    curU, curC = [], []
    M, Nn = "hM", "N"
    for i, (p, pn) in enumerate(zip(pieces, pnames)):
        params, hl = seg.sig(p)
        for (nm, t) in p['defs']:
            lines.append(f"obtain ⟨{nm}, e_{nm}⟩ : ∃ y : UInt32, y = {t} := ⟨_, rfl⟩")
        args = []
        for (hn, prop, kind, data) in hl:
            if kind in ('load', 'loadlit'):
                k_, key, v = data
                if k_ == 'U':
                    lp = lkp(curU, init_U, key, 'hlU')
                    args.append(f"({M}.rdU0 {lp})" if key == 0 else f"({M}.rdU (k := {key}) {lp} {key} rfl)")
                elif k_ == 'C':
                    lp = lkp(curC, init_C, key, 'hlC')
                    args.append(f"({M}.rdC0 {lp})" if key == 0 else f"({M}.rdC (k := {key}) {lp} {key} rfl)")
                elif key == '1050108':
                    args.append(f"(img_word {Nn})")
                elif key in getattr(seg, 'alias', {}):
                    pb, pk = seg.alias[key]
                    args.append(f"({M}.rdEa E_{pb} {pk} (by decide) hx_{v.term()} e_{key})")
                else:
                    m = re.match(r'^\(UInt32\.add (\w+) (\d+)\)$', key)
                    if m:
                        args.append(f"({M}.rdE E_{m.group(1)} {m.group(2)} (by decide) hx_{v.term()})")
                    else:
                        args.append(f"({M}.rdE0 E_{key} (by decide) hx_{v.term()})")
            elif kind == 'fact':
                prop0 = [pr for (nm, pr, _) in seg.facts if nm == data][0]
                args.append(f"(by rw [{M}.size]; exact {data})" if 'N.get.size' in prop0 else data)
            elif kind == 'cptr':
                args.append(f"(by rw [e_{data}, addF_fst'])")
            elif kind == 'alias1':
                pb, pk = seg.alias[data]
                args.append(f"(by rw [alias_toNat E_{pb} {pk} (by decide) e_{data}, {M}.size]; "
                            f"have := E_{pb}.fit; simp only [UInt32.reduceToNat]; omega)")
            elif kind == 'alias2':
                pb, pk = seg.alias[data]
                args.append(f"(by rw [alias_toNat E_{pb} {pk} (by decide) e_{data}]; simp only [UInt32.reduceToNat]; omega)")
            elif kind == 'branch':
                if branch_args is None:
                    hyps.append(f"(hbr{i}_{data} : {prop})")
                    args.append(f"hbr{i}_{data}")
                else:
                    args.append(branch_args[i][data])
            else:
                args.append(f"e_{data}")
        Nn1 = f"NN{i + 1}"
        lines.append(f"obtain ⟨{Nn1}, rr{i + 1}, MM{i + 1}⟩ := {pn} ic0 hic G {Nn} U {C} _ _ P {M} "
                     + " ".join(params) + " " + " ".join(args))
        lines.append(f"have RR{i + 1} := " + ("rr1" if i == 0 else f"RR{i}.trans rr{i + 1}"))
        for (kind, off, v) in p['stores']:
            (curU if kind == 'U' else curC).insert(0, (off, v.term()))
        M, Nn = f"MM{i + 1}", Nn1
    n = len(pieces)
    last = pieces[-1]
    final_regs = last['regs1']
    junk = []

    def J(t):
        for x in names_in(t):
            if SSA.match(x) and x not in junk and x not in inputs:
                junk.append(x)
    for r in REGS:
        J(final_regs[r].term())
    J(last['fl1'])
    slotsU = {o: v.term() for (o, v) in init_U}
    for (o, v) in reversed(curU):
        slotsU[o] = v
    slotsC = {o: v.term() for (o, v) in init_C}
    for (o, v) in reversed(curC):
        slotsC[o] = v
    for o in outs_U:
        J(slotsU[o])
    for o in outs_C:
        J(slotsC[o])
    for k in keep:
        if k not in junk:
            junk.append(k)
    s0 = seg.st("N.get", regs0, esp0, eip0, fl0, ic0)
    eip1 = last['eip1'] if last['eip1'] is not None else last['ret'].term()
    s1 = seg.st("N'.get", final_regs, last['esp1'], eip1, last['fl1'], last['ic1'])
    lkU = ", ".join(f"({o}, {slotsU[o]})" for o in outs_U)
    lkC = ", ".join(f"({o}, {slotsC[o]})" for o in outs_C)
    sig = f"MemOK G N U {seg.nU} lU {C} {seg.nC} {seg.mC} lC P"
    ex = " ".join(junk)
    # explicit_C: the context words after the run are the stores (latest first) on top of `lC`
    lCt = "(" + "".join(f"({o}, {v}) :: " for (o, v) in curC) + "lC)" if explicit_C else "lC'"
    exC = "lU'" if explicit_C else "lU' lC'"
    concl = (f"∃ (N' : PMem) ({exC} : List (Nat × UInt32)){' (' + ex + ' : UInt32)' if ex else ''},\n"
             f"      Run img ({s0})\n        ({s1}) ∧\n"
             f"      MemOK G N' U {seg.nU} lU' {C} {seg.nC} {seg.mC} {lCt} P ∧ LK lU' [{lkU}] ∧ LK {lCt} [{lkC}]")
    if extra_concl:
        concl += f" ∧\n      {extra_concl}"
    txt = f"""
theorem {name} (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (G N : PMem) (U {C} : UInt32)
    (lU lC : List (Nat × UInt32)) (P : Nat → Prop) (hM : {sig})
    ({' '.join(inputs)} : UInt32)
    {chr(10).join('    ' + h for h in hyps)} :
    {concl} := by
"""
    body = list(lines)
    pU = "⟨" + ", ".join([lkp(curU, init_U, o, 'hlU') for o in outs_U] + ["trivial"]) + "⟩" if outs_U else "trivial"
    pC = "⟨" + ", ".join([lkp(curC, init_C, o, 'hlC') for o in outs_C] + ["trivial"]) + "⟩" if outs_C else "trivial"
    if extra_concl:
        body.append(f"refine ⟨NN{n}, _{'' if explicit_C else ', _'}{', ' + ', '.join(junk) if junk else ''}, RR{n}, MM{n}, {pU}, {pC}, ?_⟩")
        body.append("clear " + " ".join([f"rr{i + 1}" for i in range(n)] + [f"RR{i + 1}" for i in range(n)]
                                        + [f"MM{i + 1}" for i in range(n)]))
        defs = [nm for p in pieces for (nm, _) in p['defs']]
        body += [f"subst e_{nm}" for nm in reversed(defs)]
        nconj = extra_concl.count(" ∧ ") + 1
        body.append("exact rfl" if nconj == 1 else "exact ⟨" + ", ".join(["rfl"] * nconj) + "⟩")
    else:
        body.append(f"exact ⟨NN{n}, _{'' if explicit_C else ', _'}{', ' + ', '.join(junk) if junk else ''}, RR{n}, MM{n}, {pU}, {pC}⟩")
    return txt + "".join("  " + b + "\n" for b in body), inputs, junk


def expand(t, defs):
    """t with the SSA names defined in `defs` replaced (recursively) by their definitions"""
    def rep(m):
        n = m.group(1)
        if n in defs:
            return "(" + expand(defs[n], defs) + ")"
        return n
    return re.sub(r'(?<![\w.])([a-z][a-z_]*\d*)(?![\w.])', rep, t)
