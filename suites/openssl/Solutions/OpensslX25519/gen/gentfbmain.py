"""fe_frombytes: the call contract I/FbCall.lean (prover Q).

    python3 gentfbmain.py        (from this directory; uses gentfb, genfbmath, fbmain.lean.in)
"""
import os, re
import gentfb, genfbmath

G = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(G, '..')


def addr_k(a):
    if a == 's':
        return 0
    return int(re.fullmatch(r'\(UInt32\.add s (\d+)\)', a).group(1))


def reads(m):
    """The loads of the run: values, preservation under the callee's writes, byte sums, bounds. Side conditions come
    from the helpers hRd / hOk1 / hOkJ of the template (no omega in the large context)."""
    L = []
    w = L.append
    for (a, n, y) in m.loads:
        k = addr_k(a)
        hk = "" if k == 0 else f"rw [hs{k}]; "
        sz = f"(by {hk}exact hRd {k} {n} (by decide))"
        w(f"  obtain ⟨{y}, h{y}⟩ : ∃ y : UInt32, rdRaw G.get {a} {n} = y := ⟨_, rfl⟩")
        if n == 4:
            if k == 0:
                out = "(fun j hj => hOk1 j (Nat.lt_of_lt_of_le hj (by decide)))"
            else:
                out = f"(fun j hj => by rw [hs{k}]; exact hOkJ {k} j (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj {k}) (by decide)))"
            rd = f"(P.rd htop {sz} {out})"
        elif n == 2:
            rd = (f"(P.rd2 htop {sz} (by {hk}exact hOk1 {k} (by decide)) (by {hk}exact hOkJ {k} 1 (by decide)))")
        else:
            rd = f"(P.rd1 htop {sz} (by {hk}exact hOk1 {k} (by decide)))"
        w(f"  have hin_{y} : ∀ N : XMem, Pres G N (OutF L 68) → rdRaw N.get {a} {n} = {y} := fun N P => {rd}.trans h{y}")
        bs = [f"(G.get.get! (s.toNat + {k + j})).toNat" for j in range(n)]
        rhs = ' + '.join(bs[:1] + [f"2 ^ {8 * j} * {b}" for j, b in enumerate(bs) if j > 0])
        lem = {1: 'rd1_toNat', 2: 'rd2_toNat', 4: "rd4_toNat'"}[n]
        rwk = "" if k == 0 else f", hs{k}"
        w(f"  have hv_{y} : {y}.toNat = {rhs} := by rw [← h{y}, {lem} {sz}{rwk}]" + ("; rfl" if k == 0 else ""))
        lts = ' '.join(f"({b[:-6]}.toNat_lt)" for b in bs)
        if n == 4:
            pf = f"by rw [hv_{y}]; exact fz_b4 {lts}"
        elif n == 2:
            pf = f"by rw [hv_{y}]; exact fz_b2 {lts}"
        else:
            pf = f"by rw [hv_{y}]; exact {lts}"
        w(f"  have hb_{y} : {y}.toNat < 2 ^ {8 * n} := {pf}")
    return '\n'.join(L)


def pieces(ps):
    L = []
    w = L.append
    k_mem = 1
    for k, p in enumerate(ps):
        prm = gentfb.params_of(p)
        args = []
        for (o, n) in p['sl']:
            args.append('rfl')
        pres = [f"P{k_mem}"]
        cur = pres[0]
        for (off, v) in p['fs']:
            cur = f"({cur}.wrF0 (by decide))" if off == 0 else f"({cur}.wrF (by decide))"
            pres.append(cur)
        for (a, n, y, j) in p['xl']:
            args.append(f"(hin_{y} _ {pres[j]})")
        if p['xl']:
            args.append(f"(by rw [P{k_mem}.1]; exact hsm) hsi hsL")
        for (n, _) in p['defs'] + p['xdefs']:
            args.append(f"e_{n}")
        lem = gentfb.lemma(k, p)
        hpa = " (hp := hp)" if re.search(r'\bhp\b', lem) else ""
        c0, c1 = p['ic0'], p['ic1']
        nk = k_mem + 1
        w(f"  obtain ⟨N{nk}, r{k}, F{nk}, P{nk}⟩ := fb_p{k} (icAdd ic0 {c0}) (hicB {c0} (by decide)) G N{k_mem} L s{hpa} "
          f"hS{k_mem} _ F{k_mem} P{k_mem} " + ' '.join(prm) + ' ' + ' '.join(args))
        w(f"  rw [icAdd_add, icAdd_add] at r{k}")
        w(f"  have hS{nk} : FB N{nk}.get.size L 72 := hS.size_eq P{nk}.1")
        w(f"  have Rn := Rn.trans r{k}")
        w(f"  clear r{k} F{k_mem} hS{k_mem}" + (f" P{k_mem}" if k_mem > 1 else ""))
        k_mem = nk
    return '\n'.join(L), k_mem


if __name__ == '__main__':
    ps, m = gentfb.run()
    lemmas, facts, calls = genfbmath.run()
    tmpl = open(os.path.join(G, 'fbmain.lean.in')).read()
    defs = '\n'.join(f"  obtain ⟨{n}, e_{n}⟩ : ∃ y : UInt32, y = {t} := ⟨_, rfl⟩" for (n, t) in m.defs)
    pp, km = pieces(ps)
    last = ps[-1]
    regs = ' '.join(last['outregs'][r] for r in gentfb.STREGS)
    txt = tmpl.replace('-- @@READS', reads(m)).replace('-- @@DEFS', defs).replace('-- @@FACTS', '\n'.join(facts)) \
        .replace('-- @@CALLS', '\n'.join(calls)).replace('-- @@PIECES', pp).replace('@K', str(km)) \
        .replace('@FL', last['outflag'])
    b = lambda i: f"(G.get.get! (s.toNat + {i})).toNat"
    horner = "0"
    for i in reversed(range(32)):
        horner = f"{b(i) + ' % 128' if i == 31 else b(i)} + 256 * ({horner})"
    o = last['outregs']
    oregs = ' '.join(o[r] for r in gentfb.STREGS)
    r2 = dict(o); r2['eax'] = 'hp'; r2['ebp'] = 'v68'
    r3 = dict(r2); r3['ebp'] = 'v76'
    rwo = lambda r: ' '.join(r[x] for x in gentfb.STREGS[1:])
    fl = last['outflag']
    txt = txt.replace('@HS', '\n'.join(f"  have hs{k} : (UInt32.add s {k}).toNat = s.toNat + {k} := hAs {k} (by decide)" for k in range(1, 32)))
    txt = txt.replace('@MBS', ', '.join(f"mb{i}" for i in range(32)))
    txt = txt.replace('@MB', '\n'.join(f"  have mb{i} := mbAs {i} (by decide)" for i in range(32)))
    txt = txt.replace('@HORNER', horner)
    txt = txt.replace('@BARGS', ' '.join(b(i) for i in range(32)) + ' ' + ' '.join(f"y{i}.toNat" for i in range(1, 19)) + ' _' * 21 + ' _')
    txt = txt.replace('@BBNDS', ' '.join(f"(G.get.get! (s.toNat + {i})).toNat_lt" for i in range(32)))
    txt = txt.replace('@HVS', ' '.join(f"hv_y{i}" for i in range(1, 19)))
    txt = txt.replace('@OREGS', oregs).replace('@O2REGS', rwo(r2) + ' ' + fl).replace('@O3REGS', rwo(r3) + ' ' + fl)
    txt = txt.replace('@O4REGS0', 'hp ' + rwo(r3)).replace('@O4REGS', 'hp ' + rwo(r3) + ' ' + fl)
    open(os.path.join(D, 'I', 'FbCall.lean'), 'w').write(txt)
    print('ok', km, regs)
