"""fe_frombytes: per-limb lemmas I/FbLimbs.lean and the Nat facts of the main proof (prover Q).

    python3 genfbmath.py         (from this directory)

For each output word (h0..h9 of fe_frombytes) the lemma `fbl<i>` states, from the Nat facts of the
definitions it depends on, `(w : Int) = h_i % 2^32` and the fe_mul output bound of h_i, where h_i is the
limb after the carries, in terms of H0..H9 (the loaded limbs) and the carries c0..c9.
"""
import os, re
import gentfb

G = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(G, '..')
OUT = ['v63', 'v61', 'v70', 'v68', 'v76', 'v74', 'v82', 'v80', 'v88', 'v86']
YS = [f"y{i}" for i in range(1, 19)]
YB = {**{y: 32 for y in ['y1', 'y10']}, **{f"y{i}": 16 for i in [2, 4, 6, 8, 11, 13, 15, 17]},
      **{f"y{i}": 8 for i in [3, 5, 7, 9, 12, 14, 16, 18]}}
HDEF = {
    'H0': 'y1', 'H1': '(y3 * 65536 + y2) * 2 ^ 6', 'H2': '(y5 * 65536 + y4) * 2 ^ 5', 'H3': '(y7 * 65536 + y6) * 2 ^ 3',
    'H4': '(y9 * 65536 + y8) * 2 ^ 2', 'H5': 'y10', 'H6': '(y12 * 65536 + y11) * 2 ^ 7',
    'H7': '(y14 * 65536 + y13) * 2 ^ 5', 'H8': '(y16 * 65536 + y15) * 2 ^ 4', 'H9': '(y18 * 65536 + y17) * 2 ^ 2 % 2 ^ 25',
    'c9': '(H9 + 16777216) / 2 ^ 25', 'T0': 'H0 + 19 * c9', 'c0': '(T0 + 33554432) / 2 ^ 26',
    'c1': '(H1 + 16777216) / 2 ^ 25', 'c2': '(H2 + c1 + 33554432) / 2 ^ 26',
    'c3': '(H3 + 16777216) / 2 ^ 25', 'c4': '(H4 + c3 + 33554432) / 2 ^ 26',
    'c5': '(H5 + 16777216) / 2 ^ 25', 'c6': '(H6 + c5 + 33554432) / 2 ^ 26',
    'c7': '(H7 + 16777216) / 2 ^ 25', 'c8': '(H8 + c7 + 33554432) / 2 ^ 26'}
HV = list(HDEF.keys())
HLIMB = ['(T0 : Int) - c0 * 2 ^ 26', '(H1 : Int) - c1 * 2 ^ 25 + c0', '(H2 : Int) + c1 - c2 * 2 ^ 26',
         '(H3 : Int) - c3 * 2 ^ 25 + c2', '(H4 : Int) + c3 - c4 * 2 ^ 26', '(H5 : Int) - c5 * 2 ^ 25 + c4',
         '(H6 : Int) + c5 - c6 * 2 ^ 26', '(H7 : Int) - c7 * 2 ^ 25 + c6', '(H8 : Int) + c7 - c8 * 2 ^ 26',
         '(H9 : Int) - c9 * 2 ^ 25 + c8']
BND = [33889976, 16944988] * 5


def masks(m):
    for j in range(1, 33):
        for s in range(0, j):
            if ((2 ** j - 1) & (2 ** 32 - 2 ** s)) == m:
                return j, s
    raise Exception(m)


def fact(n, t, defs):
    """(nat expression with @x for the toNat of x and %g for (cfBit g).toNat, proof term, deps)"""
    def r(p, s):
        return re.fullmatch(p, s)
    if m := r(r'shlR (\w+) (\d+)', t):
        a, k = m.groups()
        return f"@{a} * 2 ^ {k} % 2 ^ 32", f"tn_shl {k} e_{n} rfl (by decide) (by decide)", [a]
    if m := r(r'shrR (\w+) (\d+)', t):
        a, k = m.groups()
        return f"@{a} / 2 ^ {k}", f"tn_shr {k} e_{n} rfl (by decide) (by decide)", [a]
    if m := r(r'\(logicF 4 \(UInt32\.lor (\w+) (\w+)\)\)\.1', t):
        a, b = m.groups()
        k = r(r'shlR \w+ (\d+)', defs[a]).group(1)
        return (f"@{a} + @{b}", f"tn_or {k} e_{n} (by rw [n_{a}]; exact fb_mod_shl_zero _ {k} (by decide)) hb_{b}", [a, b])
    if m := r(r'\(logicF 4 \(UInt32\.land (\w+) (\d+)\)\)\.1', t):
        a, mm = m.groups()
        j, s = masks(int(mm))
        return f"@{a} % 2 ^ {j} / 2 ^ {s} * 2 ^ {s}", f"tn_landb {j} {s} e_{n} (by decide) (by decide)", [a]
    if m := r(r'UInt32\.add (\w+) (\d+)', t):
        a, k = m.groups()
        return f"(@{a} + {k}) % 2 ^ 32", f"tn_addk {k} e_{n} rfl", [a]
    if m := r(r'UInt32\.add \(UInt32\.add (\w+) (\w+)\) (\d+)', t):
        a, b, k = m.groups()
        return f"((@{a} + @{b}) % 2 ^ 32 + {k}) % 2 ^ 32", f"tn_add2k {k} e_{n} rfl", [a, b]
    if m := r(r'UInt32\.add \(\(?UInt32\.shiftLeft (\w+) (\d+)\)?\) (\d+)', t):
        a, k, c = m.groups()
        return f"(@{a} * 2 ^ {k} % 2 ^ 32 + {c}) % 2 ^ 32", f"tn_shlk {k} {c} e_{n} rfl rfl", [a]
    if m := r(r'UInt32\.add \(UInt32\.add (\w+) \(UInt32\.shiftLeft (\w+) (\d+)\)\) (\d+)', t):
        a, b, k, c = m.groups()
        lk = 'tn_leak0' if a == '0' else 'tn_leak'
        return (f"((@{a} + @{b} * 2 ^ {k} % 2 ^ 32) % 2 ^ 32 + {c}) % 2 ^ 32", f"{lk} {k} {c} e_{n} rfl rfl", [a, b])
    if m := r(r'UInt32\.add (\w+) \(UInt32\.shiftLeft (\w+) (\d+)\)', t):
        a, b, k = m.groups()
        return f"(@{a} + @{b} * 2 ^ {k} % 2 ^ 32) % 2 ^ 32", f"tn_lea {k} e_{n} rfl", [a, b]
    if m := r(r'UInt32\.add (\w+) (\w+)', t):
        a, b = m.groups()
        return f"(@{a} + @{b}) % 2 ^ 32", f"tn_add e_{n}", [a, b]
    if m := r(r'UInt64\.toUInt32 \(UInt64\.mul \(UInt32\.toUInt64 (\w+)\) 19\)', t):
        a, = m.groups()
        return f"@{a} * 19 % 2 ^ 32", f"tn_mullo e_{n}", [a]
    if m := r(r'UInt64\.toUInt32 \(UInt64\.shiftRight \(UInt64\.mul \(UInt32\.toUInt64 (\w+)\) 19\) 32\)', t):
        a, = m.groups()
        return f"@{a} * 19 / 2 ^ 32", f"tn_mulhi e_{n}", [a]
    if m := r(r'\(addF 4 (\w+) (\w+) \(cfBit (\w+)\)\)\.1', t):
        a, b, g = m.groups()
        bb = b if b[0].isdigit() else f"@{b}"
        return f"(@{a} + {bb} + %{g}) % 2 ^ 32", f"tn_adc e_{n}", [a, g] + ([] if b[0].isdigit() else [b])
    if m := r(r'UInt32\.lor 0 \(UInt32\.land \(bitU \(cfB (\w+)\)\) 255\)', t):
        g, = m.groups()
        return f"%{g}", f"tn_setb' e_{n}", [g]
    if m := r(r'sdR true (\w+) (\w+) (\d+)', t):
        c, a, k = m.groups()
        mul = {'6': 64, '7': 128}[k]
        return f"(@{c} * 2 ^ 32 + @{a}) * {mul} % 2 ^ 64 / 2 ^ 32 % 2 ^ 32", f"tn_shld{k} e_{n}", [c, a]
    if m := r(r'\(subF 4 (\w+) (\w+) 0\)\.1', t):
        a, b = m.groups()
        return f"(@{a} + 2 ^ 33 - @{b}) % 2 ^ 32", f"tn_sub e_{n}", [a, b]
    raise Exception((n, t))


def flag_fact(g, t):
    m = re.fullmatch(r'\(addF 4 (\w+) (\w+) 0\)\.2', t)
    a, b = m.groups()
    bb = b if b[0].isdigit() else f"@{b}"
    return f"(@{a} + {bb}) / 2 ^ 32", f"tn_cf e_{g}", [a] + ([] if b[0].isdigit() else [b])


def closure(n, defs, acc):
    if n in acc or n in YS:
        return
    if n[0] == 'g':
        _, _, deps = flag_fact(n, defs[n])
    else:
        _, _, deps = fact(n, defs[n], defs)
    for d in deps:
        if not d.isdigit():
            closure(d, defs, acc)
    acc.append(n)


def var(x):
    return f"f{x}" if x[0] == 'g' else x


def nat_expr(e):
    e = re.sub(r'@(\w+)', lambda m: m.group(1), e)
    return re.sub(r'%(g\d+)', lambda m: 'f' + m.group(1), e)


def main_expr(e):
    e = re.sub(r'@(\w+)', lambda m: m.group(1) if m.group(1).isdigit() else f"{m.group(1)}.toNat", e)
    return re.sub(r'%(g\d+)', lambda m: f"(cfBit {m.group(1)}).toNat", e)


def run():
    ps, m = gentfb.run()
    defs = dict(m.defs)
    lemmas = []
    need = []
    for i, w in enumerate(OUT):
        acc = []
        closure(w, defs, acc)
        for x in acc:
            if x not in need:
                need.append(x)
    vs = ' '.join(YS + HV + [var(x) for x in need])
    hy = ' '.join(f"(hb_{y} : {y} < 2 ^ {YB[y]})" for y in YS)
    hh = ' '.join(f"(h_{h} : {h} = {HDEF[h]})" for h in HV)
    hf = []
    for x in need:
        if x[0] == 'g':
            e, _, _ = flag_fact(x, defs[x])
        else:
            e, _, _ = fact(x, defs[x], defs)
        hf.append(f"(n_{x} : {var(x)} = {nat_expr(e)})")
    concl = ' ∧\n    '.join(f"(({w} : Int) = ({HLIMB[i]}) % 2 ^ 32 ∧ -{BND[i]} ≤ {HLIMB[i]} ∧ {HLIMB[i]} ≤ {BND[i]})"
                              for i, w in enumerate(OUT))
    body = open(os.path.join(G, 'fblimbs_body.lean.in')).read()
    lemmas.append(f"""
set_option maxHeartbeats 2000000 in
theorem fb_limbs ({vs} : Nat) {hy}
    {hh}
    {' '.join(hf)} :
    {concl} := by
{body}""")
    # main-proof Nat facts
    facts = []
    for x in need:
        if x[0] == 'g':
            e, pf, _ = flag_fact(x, defs[x])
            facts.append(f"  have n_{x} : (cfBit {x}).toNat = {main_expr(e)} := {pf}")
        else:
            e, pf, _ = fact(x, defs[x], defs)
            facts.append(f"  have n_{x} : {x}.toNat = {main_expr(e)} := {pf}")
    args = ' '.join(f"{y}.toNat" for y in YS) + ' _' * len(HV) + ' ' + \
        ' '.join(f"(cfBit {x}).toNat" if x[0] == 'g' else f"{x}.toNat" for x in need)
    args += ' ' + ' '.join(f"hb_{y}" for y in YS) + ' rfl' * len(HV) + ' ' + ' '.join(f"n_{x}" for x in need)
    pat = ', '.join(f"⟨m{i}, b{i}, b{i}'⟩" for i in range(10))
    calls = [f"  obtain ⟨{pat}⟩ := fb_limbs {args}"]
    # the value: the limbs after the carries, read in radix 2^25.5, are decodeU minus c9 * p
    bs = ' '.join(f"b{i}" for i in range(32))
    hb = ' '.join(f"(hb{i} : b{i} < 256)" for i in range(32))
    loads = [(a, n, y) for (a, n, y) in gentfb.run()[1].loads]
    hv = []
    for (a, n, y) in loads:
        k = 0 if a == 's' else int(re.fullmatch(r'\(UInt32\.add s (\d+)\)', a).group(1))
        terms = [f"b{k}"] + [f"2 ^ {8 * j} * b{k + j}" for j in range(1, n)]
        hv.append(f"(hv_{y} : {y} = {' + '.join(terms)})")
    horner = "0"
    for i in reversed(range(32)):
        t = "b31 % 128" if i == 31 else f"b{i}"
        horner = f"{t} + 256 * ({horner})"
    xs = ' '.join(f"X{i}" for i in range(10))
    hx = ' '.join(f"(hx{i} : X{i} = {HLIMB[i]})" for i in range(10))
    HS = ['H0', 'H1', 'H2', 'H3', 'H4', 'H5', 'H6', 'H7', 'H8', 'H9']
    hh = ' '.join(f"(h_{h} : {h} = {HDEF[h]})" for h in HS + ['T0'])
    offs = [0, 26, 51, 77, 102, 128, 153, 179, 204, 230]
    snat = ' + '.join(f"H{i} * 2 ^ {o}" for i, o in enumerate(offs))
    sint = ' + '.join(f"(H{i} : Int) * 2 ^ {o}" for i, o in enumerate(offs))
    clr1 = ' '.join([f"hb{i}" for i in range(32)] + [f"hv_{y}" for (a, n, y) in loads] + [f"h_{h}" for h in HS] + ['hD'])
    clr2 = ' '.join([f"hx{i}" for i in range(10)] + ['h_T0'])
    xl = ', '.join(f"X{i}" for i in range(10))
    lemmas.append(f"""
theorem fb_value ({bs} {' '.join(YS)} {' '.join(HV)} D : Nat) ({xs} : Int) {hb}
    {' '.join(hv)}
    {hh}
    {hx} (hD : D = {horner}) :
    L10.val ⟨{xl}⟩ % pI = (D : Int) % pI := by
  have e1 : L10.val ⟨{xl}⟩ = ({sint}) + (-(c9 : Int)) * (2 ^ 255 - 19) := by
    simp only [L10.val]
    clear {clr1}
    omega
  have e2 : {snat} = D := by
    clear e1 {clr2}
    omega
  rw [e1, pI_eq, Int.add_mul_emod_self_right]
  congr 1
  clear e1 {clr1} {clr2}
  omega
""")
    return lemmas, facts, calls


if __name__ == '__main__':
    lemmas, facts, calls = run()
    hdr = """import Solutions.OpensslX25519.I.FbMath
import Solutions.OpensslX25519.I.ToBytesMath
import Solutions.OpensslX25519.I.FbZ
/-!
# `fe_frombytes`: the ten output limbs

Generated by `gen/genfbmath.py` (provers Q, R): `fb_limbs` gives each output word from the `toNat` facts of the
run as the limb after the carries (`H` the loaded limbs, `c` the carries) modulo 2^32, within the `fe_mul` output
bounds, by a chain of the small steps of `I/FbZ` (body: `gen/fblimbs_body.lean.in`); `fb_value`: the limbs read in
radix 2^25.5 are the 255-bit decoding of the input modulo `p`.
-/
namespace Solutions.OpensslX25519.I
open X86 Solutions.Exec Solutions.OpensslX25519 Ssl.OpensslX25519

theorem fb_mod_shl_zero (t k : Nat) (hk : k ≤ 32) : t * 2 ^ k % 2 ^ 32 % 2 ^ k = 0 := by
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hk), Nat.mul_mod_left]

theorem fb_bnd_even {w : UInt32} {X : Int} (h : sv w = X) (h1 : -33889976 ≤ X) (h2 : X ≤ 33889976) :
    (sv w).natAbs * 100 ≤ 101 * 2 ^ (25 - 0 % 2) := by
  rw [h]; show X.natAbs * 100 ≤ 101 * 2 ^ 25; omega

theorem fb_bnd_odd {w : UInt32} {X : Int} (h : sv w = X) (h1 : -16944988 ≤ X) (h2 : X ≤ 16944988) :
    (sv w).natAbs * 100 ≤ 101 * 2 ^ (25 - 1 % 2) := by
  rw [h]; show X.natAbs * 100 ≤ 101 * 2 ^ 24; omega

/-- `tn_leak` with the base register absent (`leal disp(,%r,k)`: `UInt32.add 0 …`). -/
theorem tn_leak0 {v b k c : UInt32} (n m : Nat) (e : v = UInt32.add (UInt32.add 0 (UInt32.shiftLeft b k)) c)
    (hk : k.toNat % 32 = n) (hc : c.toNat = m) :
    v.toNat = ((0 + b.toNat * 2 ^ n % 2 ^ 32) % 2 ^ 32 + m) % 2 ^ 32 := by
  have := tn_leak n m e hk hc
  rw [this, show (0 : UInt32).toNat = 0 from rfl]
"""
    open(os.path.join(D, 'I', 'FbLimbs.lean'), 'w').write(hdr + ''.join(lemmas) + "\nend Solutions.OpensslX25519.I\n")
    open(os.path.join(G, 'fbfacts.txt'), 'w').write('\n'.join(facts) + '\n' + '\n'.join(calls) + '\n')
    print(len(lemmas), len(facts))
