"""fe_tobytes: the byte lemmas I/TbBytes.lean and the call contract I/TbCall.lean (prover Q).

    python3 gentbmain.py        (from this directory; uses gentb.run and tbmain.lean.in)
"""
import os, re
import gentb

G = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(G, '..')
TS = ['v26', 'v28', 'v30', 'v32', 'v35', 'v56', 'v58', 'v60', 'v62', 'v66']   # the ten chain words


def nat_fact(name, t):
    """(Nat expression over 'n_<arg>' placeholders, proof term) of v.toNat for the definition t"""
    m = re.fullmatch(r'UInt32\.add (\w+) \(UInt32\.shiftLeft (\w+) (\d+)\)', t)
    if m:
        a, b, k = m.groups()
        return f"(@{a} + @{b} * 2 ^ {k} % 2 ^ 32) % 2 ^ 32", f"tn_lea {k} e_{name} rfl", [a, b]
    m = re.fullmatch(r'UInt32\.add (\w+) (\w+)', t)
    if m:
        a, b = m.groups()
        return f"(@{a} + @{b}) % 2 ^ 32", f"tn_add e_{name}", [a, b]
    m = re.fullmatch(r'shrR (\w+) (\d+)', t)
    if m:
        a, k = m.groups()
        return f"@{a} / 2 ^ {k}", f"tn_shr {k} e_{name} rfl (by decide) (by decide)", [a]
    m = re.fullmatch(r'shlR (\w+) (\d+)', t)
    if m:
        a, k = m.groups()
        return f"@{a} * 2 ^ {k} % 2 ^ 32", f"tn_shl {k} e_{name} rfl (by decide) (by decide)", [a]
    m = re.fullmatch(r'\(logicF 4 \(UInt32\.land (\w+) (\d+)\)\)\.1', t)
    if m:
        a, k = m.groups()
        j = (int(k) + 1).bit_length() - 1
        assert 2 ** j == int(k) + 1
        return f"@{a} % 2 ^ {j}", f"tn_and {j} e_{name} (by decide)", [a]
    m = re.fullmatch(r'\(logicF 4 \(UInt32\.lor (\w+) (\w+)\)\)\.1', t)
    if m:
        a, b = m.groups()
        return f"@{a} + @{b}", None, [a, b]   # proof built by the caller (needs the shift count)
    raise Exception(t)


def run():
    ps, m, ins = gentb.run()
    defs = dict(m.defs)
    order = [n for (n, _) in m.defs]
    # the stored bytes: (byte index, value-name, kind)
    bytes_ = []
    for p in ps:
        for (o, v) in p['bs']:
            mm = re.fullmatch(r'\(UInt32\.land \(UInt32\.shiftRight (\w+) 8\) 255\)', v)
            if mm:
                bytes_.append((o, mm.group(1), 'hi8'))
            else:
                mm = re.fullmatch(r'\(UInt32\.land (\w+) 255\)', v)
                bytes_.append((o, mm.group(1), 'lo8'))
        for (o, v) in p['ws']:
            mm = re.fullmatch(r'\(UInt32\.land (\w+) 65535\)', v)
            bytes_.append((o, mm.group(1), 'wlo'))
            bytes_.append((o + 1, mm.group(1), 'whi'))
    assert [b[0] for b in bytes_] == list(range(32)), bytes_
    return ps, m, defs, order, bytes_


def deps(n, defs, acc):
    if n in TS or n not in defs or n in acc:
        return
    _, _, args = nat_fact(n, defs[n])
    for a in args:
        deps(a, defs, acc)
    acc.append(n)


def stored_nat(x, kind):
    return {'lo8': f"@{x} % 2 ^ 8", 'hi8': f"@{x} / 2 ^ 8 % 2 ^ 8", 'wlo': f"@{x} % 2 ^ 16",
            'whi': f"@{x} % 2 ^ 16 / 2 ^ 8"}[kind]


def stored_rw(kind):
    return {'lo8': "rw [tn_land 8 (by decide)]", 'hi8': "rw [tn_land 8 (by decide), tn_shr8]",
            'wlo': "rw [tn_land 16 (by decide)]", 'whi': "rw [tn_shr8, tn_land 16 (by decide)]"}[kind]


def subst_nat(e, f):
    return re.sub(r'@(\w+)', lambda mm: f(mm.group(1)), e)


def byte_lemmas(defs, bytes_):
    out = []
    for (j, x, kind) in bytes_:
        acc = []
        deps(x, defs, acc)
        tv = ' '.join(f"t{i}" for i in range(10))
        av = ' '.join(f"a{n[1:]}" for n in acc)
        hyps = [f"(ht{i} : t{i} < 2 ^ 32)" for i in range(10)]
        var = lambda n: f"t{TS.index(n)}" if n in TS else f"a{n[1:]}"
        for n in acc:
            e, _, _ = nat_fact(n, defs[n])
            hyps.append(f"(h{n[1:]} : a{n[1:]} = {subst_nat(e, var)})")
        s = subst_nat(stored_nat(x, kind), var)
        out.append(f"""
theorem tbb{j} ({tv}{' ' + av if av else ''} : Nat) {' '.join(hyps)} :
    {s} % 256 = tbVN {tv} / 2 ^ (8 * {j}) % 256 := by
  unfold tbVN; omega
""")
    return ''.join(out)


def main_proof(ps, m, defs, order, bytes_):
    L = []
    w = L.append
    # all definitions up front (values and flags)
    w("  obtain ⟨g0, eg0⟩ : ∃ y : UInt32, y = (subF 4 (UInt32.add L 24) 24 0).2 := ⟨_, rfl⟩")
    for (n, t) in m.defs:
        w(f"  obtain ⟨{n}, e_{n}⟩ : ∃ y : UInt32, y = {t} := ⟨_, rfl⟩")
    # the value and the byte facts
    w(f"  obtain ⟨V, eV⟩ : ∃ V : Nat, V = tbV {' '.join(TS)} := ⟨_, rfl⟩")
    need = []
    for (j, x, kind) in bytes_:
        deps(x, defs, need)
    for n in need:
        e, pf, args = nat_fact(n, defs[n])
        tn = subst_nat(e, lambda a: f"{a}.toNat")
        if pf is None:
            a, b = args
            k = re.fullmatch(r'shlR \w+ (\d+)', defs[a]).group(1)
            pf = f"tn_or {k} e_{n} (by rw [n_{a}]; exact mod_shl_zero _ {k} (by decide)) (by rw [n_{b}]; exact Nat.mod_lt _ (by decide))"
        w(f"  have n_{n} : {n}.toNat = {tn} := {pf}")
    for (j, x, kind) in bytes_:
        acc = []
        deps(x, defs, acc)
        st = {'lo8': f"(UInt32.land {x} 255)", 'hi8': f"(UInt32.land (UInt32.shiftRight {x} 8) 255)",
              'wlo': f"(UInt32.land {x} 65535)", 'whi': f"(UInt32.shiftRight (UInt32.land {x} 65535) 8)"}[kind]
        args = ' '.join(f"{t}.toNat" for t in TS) + ''.join(f" {n}.toNat" for n in acc)
        args += ''.join(f" (UInt32.toNat_lt {t})" for t in TS) + ''.join(f" n_{n}" for n in acc)
        w(f"  have hb{j} : {st}.toUInt8 = tbB V {j} := u8_tbB _ _ _ (by {stored_rw(kind)}; rw [eV]; exact tbb{j} {args})")
    return '\n'.join(L)


def pieces_proof(ps, m):
    L = []
    w = L.append
    cur = 'N1'
    k_mem = 1
    lst = '((24, esi0) :: (28, edi0) :: (32, ebx0) :: (36, ebp0) :: [(40, ret)])'
    nb = 0          # bytes written so far
    for k, p in enumerate(ps):
        prm = gentb.params_of(p)
        if p['kind'] == 'fs':
            args = []
            for (o, n) in p['sl']:
                args.append('rfl')
            for (o, n) in p['xl']:
                args.append(f"(hin_{n} {cur} P{k_mem})")
            if p['xl']:
                args.append(f"(by rw [P{k_mem}.1]; exact hpm) hpi hpL")
            for (n, _) in p['defs']:
                args.append(f"e_{n}")
            nxt = f"N{k_mem + 1}"
            w(f"  obtain ⟨{nxt}, r{k}, F{k_mem + 1}, P{k_mem + 1}⟩ := tb_p{k} ic0 hic G {cur} L hp (out := out) hS{k_mem} _ F{k_mem} P{k_mem} "
              + ' '.join(prm) + ' ' + ' '.join(args))
            w(f"  have hS{k_mem + 1} : FB {nxt}.get.size L 44 := hS.size_eq P{k_mem + 1}.1")
            w(f"  have Rn := Rn.trans r{k}")
            cur = nxt
            k_mem += 1
            for (off, v) in p['fs']:
                lst = f"(({off}, {v}) :: {lst})"
            if k + 1 < len(ps) and ps[k + 1]['kind'] != 'fs':
                # start of the output phase
                w(f"  have sz{k_mem} : {cur}.get.size = G.get.size := P{k_mem}.1")
                w(f"  have Q{k_mem} : Pres {cur} {cur} (OutO out) := Pres.refl _ _")
                w(f"  have B{k_mem} : ∀ i, i < 0 → memByte {cur}.get (out + i.toUInt32) = tbB V i := fun i hi => absurd hi (Nat.not_lt_zero i)")
                w(f"  clear P1 P2 P3")
                base = cur
                LST = lst
            continue
        args = []
        for (o, n) in p['sl']:
            if o == 0:
                args.append(f"(F{k_mem}.rd0 (rfl : List.lookup 0 _ = some {n}))")
            else:
                args.append(f"(F{k_mem}.rd (rfl : List.lookup {o} _ = some {n}) {o} rfl)")
        for (n, _) in p['defs']:
            args.append(f"e_{n}")
        head = f"tb_p{k} ic0 hic {cur} L out hp (hS.size_eq sz{k_mem}) (by rw [sz{k_mem}]; exact hom) hoi " + ' '.join(prm) + ' ' + ' '.join(args)
        if p['kind'] == 'c':
            w(f"  have Rn := Rn.trans ({head})")
            continue
        stores = []
        if p['kind'] == 'b':
            (o, v), = p['bs']
            stores = [(o, v)]
        else:
            (o, v), = p['ws']
            stores = [(o, v), (o + 1, f"(UInt32.shiftRight {v} 8)")]
        oks = []
        mem = cur
        for (o, v) in stores:
            a = gentb.addr_t('out', o)
            nk = k_mem + 1
            w(f"  have ok{nk} : StoreOk1 Image.base Image.size ({mem}).mem {a} := ok1_of ({mem}) _ out {o} ha{o} (by decide) (by rw [sz{k_mem}]; exact hom) hoi")
            w(f"  have sz{nk} : (CodeMem.wr1 ({mem}) {a} {v} ok{nk}).get.size = G.get.size := (wr1_get_size _ _ _ _).trans sz{k_mem}")
            w(f"  have F{nk} := F{k_mem}.wrO1 (hS.size_eq sz{k_mem}) (v := {v}) ok{nk} (by rw [ha{o}]; exact hdL {o} (by decide))")
            w(f"  have Q{nk} := Q{k_mem}.wr1 (v := {v}) ok{nk} (fun x hx => by rw [ha{o}]; exact hdO {o} (by decide) x hx)")
            w(f"  have B{nk} := bytes_step ({mem}) out {a} {v} ok{nk} V {o} ha{o} (by decide) (by rw [sz{k_mem}]; exact hom) (by rw [sz{k_mem}]; exact htop) B{k_mem} hb{o}")
            oks.append(f"ok{nk}")
            mem = f"CodeMem.wr1 ({mem}) {a} {v} ok{nk}"
            k_mem = nk
        w(f"  have r{k} := {head} {' '.join(oks)}")
        nxt = f"N{k_mem}"
        w(f"  generalize {mem} = {nxt} at r{k} sz{k_mem} F{k_mem} Q{k_mem} B{k_mem}")
        w(f"  have Rn := Rn.trans r{k}")
        cur = nxt
    return '\n'.join(L), cur, k_mem, base


if __name__ == '__main__':
    ps, m, defs, order, bytes_ = run()
    tmpl = open(os.path.join(G, 'tbmain.lean.in')).read()
    bl = byte_lemmas(defs, bytes_)
    open(os.path.join(D, 'I', 'TbBytes.lean'), 'w').write(tmpl.split('-- @@MAIN')[0].replace('-- @@BYTES', bl))
    mp = main_proof(ps, m, defs, order, bytes_)
    pp, cur, km, base = pieces_proof(ps, m)
    main = tmpl.split('-- @@MAIN')[1]
    main = main.replace('-- @@DEFS', mp).replace('-- @@PIECES', pp).replace('@NF', cur).replace('@KF', str(km)) \
        .replace('@B', base[1:]) \
        .replace('@REGS', ' '.join(ps[-1]['outregs'][r] for r in gentb.STREGS)).replace('@FL', ps[-1]['outflag'])
    open(os.path.join(D, 'I', 'TbCall.lean'), 'w').write(main)
    print('ok', len(bytes_), cur, km, base)
