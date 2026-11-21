"""fe_mul121666 as a callee: I/M121Arith.lean (shld by 7, bound and final-word lemmas over chain121)
and I/M121Call.lean (`fe_mul121666_call`), from the body pieces of gen/genm121.py.

    python3 genm121main.py          (from this directory)
"""
import os
import genm121  # noqa: F401  (configures gensq for fe_mul121666)
import gensq
from sem import Sem, Fact, Poly, par

G = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(G, '..')
XS = "X0 X1 X2 X3 X4 X5 X6 X7 X8 X9"
LX = "⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩"
CH = f"(chain121 (m121Raw {LX}))"


class Sem121(Sem):
    def __init__(self, inputs, out):
        super().__init__(inputs, pre='m121')
        self.limbs = []
        self.hargs = XS
        self.sv['121666'] = Fact('sv_k121666', '121666', Poly.const(121666), 121666)
        self.sv['19'] = Fact('sv_k19', '19', Poly.const(19), 19)
        out.append("have sv_k121666 : sv 121666 = 121666 := by decide")
        out.append("have sv_k19 : sv 19 = 19 := by decide")
        self.slemmas = []

    def canon(self, key, out):
        pass

    def bargs(self):
        cs = [c for (c, _, _) in self.carries]
        return ' '.join([XS] + cs + ['hA'] + [f"h{c}" for c in cs])

    def step(self, v, out):
        if v.op == 'shldl' and v.args[2] == 7:
            c, x, k = v.args
            T = self.pair[(x, c)]
            self.nC += 1
            C = f"C{self.nC}"
            fn = f"w_{v.name}"
            self.defs[v.name] = v
            out.append(f"obtain ⟨{C}, h{C}, {fn}⟩ := shld25 {T.name} e_{v.name}")
            self.carries.append((C, T.es, 25))
            self.cof[(x, c)] = (C, 25)
            self.m32[v.name] = Fact(fn, C, Poly.atom(C))
            return
        if v.op == 'imulHi':
            x, y = v.args
            if x not in self.sv:
                f = self.m32[x]
                j = len(self.slemmas)
                self.slemmas.append((j, f.es, list(self.carries)))
                out.append(f"have sv_{x} := sv_of_M32 {f.name} (m121_s{j} {self.bargs()})")
                self.sv[x] = Fact(f"sv_{x}", f.es, f.poly, 2 ** 31)
        super().step(v, out)


def chyps(carries):
    cs = ' '.join(c for (c, _, _) in carries)
    hs = ''.join(f"\n    (h{c} : {c} = ({t}) / {2 ** s})" for (c, t, s) in carries)
    return cs, hs


def binder(carries):
    cs, hs = chyps(carries)
    return f"({XS}{' ' + cs if cs else ''} : Int) (hA : InA {LX}){hs}"


def blemma(j, tes, carries):
    return f"""
theorem m121_b{j} {binder(carries)} :
    -2 ^ 63 ≤ {tes} ∧ {tes} < 2 ^ 63 := by
  simp only [InA] at hA
  omega
"""


def slemma(j, es, carries):
    return f"""
theorem m121_s{j} {binder(carries)} :
    -2 ^ 31 ≤ {es} ∧ {es} < 2 ^ 31 := by
  simp only [InA] at hA
  omega
"""


CRF = {'C1': ('121666 * X9', 24), 'C2': ('121666 * X1', 24), 'C3': ('121666 * X3', 24),
       'C4': ('121666 * X5', 24), 'C5': ('121666 * X7', 24), 'C6': ('121666 * X0 + C1 * 19', 25),
       'C7': ('121666 * X2 + C2', 25), 'C8': ('121666 * X4 + C3', 25), 'C9': ('121666 * X6 + C4', 25),
       'C10': ('121666 * X8 + C5', 25)}
CS10 = ' '.join(f"C{k}" for k in range(1, 11))


def chainM(carries):
    cs, hs = chyps(carries)
    assert cs == CS10
    ks = ''.join(f"\n  have k{k} : C{k} = cr ({CRF[f'C{k}'][0]}) {CRF[f'C{k}'][1]} := by\n"
                 f"    rw [hC{k}]; simp only [cr, Int.reducePow, Nat.reduceAdd] <;> omega" for k in range(1, 11))
    return f"""
theorem m121_chainM ({XS} {cs} : Int){hs} :
    {CH} = M121V {XS} {cs} := by{ks}
  exact m121_chain {XS} {cs} {' '.join(f'k{k}' for k in range(1, 11))}
"""


def flemma(i, es, carries):
    cs, hs = chyps(carries)
    hcs = ' '.join(f"h{c}" for (c, _, _) in carries)
    return f"""
theorem m121_f{i} {binder(carries)} :
    (-2 ^ 31 ≤ {CH}.get {i} ∧ {CH}.get {i} < 2 ^ 31) ∧
      {es} = {CH}.get {i} := by
  rw [m121_chainM {XS} {cs} {hcs}]
  simp only [M121V, L10.get]
  simp only [InA] at hA
  omega
"""


ARITH_HDR = """import Solutions.OpensslX25519.I.M121Math
import Solutions.OpensslX25519.Pair
/-!
# The arithmetic of the run of `fe_mul121666`

Generated (`gen/genm121main.py`): the low word of `shld $7` (the carry `t >> 25` of a pair), the
values `fe_mul121666` shifts are within the signed 64-bit range (`m121_b*`), the carry it multiplies
by `19` is within the signed 32-bit range (`m121_s*`), and the words it stores are the limbs of
`chain121 (m121Raw f)` (`m121_f*`), all by `omega` from the input bounds `InA`.
-/
namespace Solutions.OpensslX25519.I
open X86 Solutions.Exec Solutions.Exec.Mul Solutions.OpensslX25519

theorem shld_toNat7 (c a : UInt32) :
    (sdR true c a 7).toNat = (c.toNat * 2 ^ 32 + a.toNat) * 128 % 2 ^ 64 / 2 ^ 32 % 2 ^ 32 := by
  have e : sdR true c a 7 = (((((c.toUInt64 <<< 32) ||| a.toUInt64) <<< (7 : UInt64)) >>> 32).toUInt32) := rfl
  rw [e, UInt64.toNat_toUInt32, u64_shr, u64_shl, or_lo,
    show (7 : UInt64).toNat % 64 = 7 from rfl, show (32 : UInt64).toNat % 64 = 32 from rfl]

theorem shld25 {a c x : UInt32} {T : Int} (h : M64 a c T) (e : x = sdR true c a 7) :
    ∃ C : Int, C = T / 33554432 ∧ M32 x C := by
  refine ⟨_, rfl, ?_⟩
  subst e
  unfold M64 pv at h; unfold M32
  rw [shld_toNat7]
  have := a.toNat_lt; have := c.toNat_lt
  omega

/-- The limbs of `chain121 (m121Raw X)` in terms of its ten carries. -/
def M121V (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 : Int) : L10 :=
  ⟨121666 * X0 + C1 * 19 - C6 * 2 ^ 26, 121666 * X1 - C2 * 2 ^ 25 + C6, 121666 * X2 + C2 - C7 * 2 ^ 26,
    121666 * X3 - C3 * 2 ^ 25 + C7, 121666 * X4 + C3 - C8 * 2 ^ 26, 121666 * X5 - C4 * 2 ^ 25 + C8,
    121666 * X6 + C4 - C9 * 2 ^ 26, 121666 * X7 - C5 * 2 ^ 25 + C9, 121666 * X8 + C5 - C10 * 2 ^ 26,
    121666 * X9 - C1 * 2 ^ 25 + C10⟩

theorem m121_chain (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 : Int)
    (k1 : C1 = cr (121666 * X9) 24) (k2 : C2 = cr (121666 * X1) 24) (k3 : C3 = cr (121666 * X3) 24)
    (k4 : C4 = cr (121666 * X5) 24) (k5 : C5 = cr (121666 * X7) 24) (k6 : C6 = cr (121666 * X0 + C1 * 19) 25)
    (k7 : C7 = cr (121666 * X2 + C2) 25) (k8 : C8 = cr (121666 * X4 + C3) 25)
    (k9 : C9 = cr (121666 * X6 + C4) 25) (k10 : C10 = cr (121666 * X8 + C5) 25) :
    chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩) =
      M121V X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 := by
  subst k6 k7 k8 k9 k10
  subst k1 k2 k3 k4 k5
  rfl
"""


def main():
    out, m = gensq.run(os.path.join(G, 'm121.txt'))
    inputs, addr_of = {}, {}
    for p in out:
        for (kind, key, nm) in p['loads']:
            if kind == 'ext':
                off = 0 if key == 'fp' else int(key.split()[-1].rstrip(')'))
                inputs[nm] = off // 4
                addr_of[nm] = key
    assert len(inputs) == 10
    body = []
    S = Sem121(inputs, body)
    Nin = "B0"
    for idx, p in enumerate(out):
        Nout = f"B{idx + 1}"
        ls = gensq.call_piece(p, Nin, Nout, idx, f"hS.size_eq P{idx}.1")
        ls = [l.replace(f"m121_p{p['k']} G", f"m121_p{p['k']} ic0 hic G") for l in ls]
        body += ls
        for v in p['defs']:
            S.step(v, body)
        Nin = Nout
    NB = len(out)
    r = m.regs
    fl = m.flag
    sl = m.slots
    w = [sl[12], sl[8], sl[4], sl[16], r['edi'], sl[0], r['esi'], r['ecx'], r['edx'], r['ebp']]
    fin = []
    wf = [S.word(x, fin) for x in w]
    carries = S.carries
    cs = ' '.join(c for (c, _, _) in carries)
    hcs = ' '.join(f"h{c}" for (c, _, _) in carries)

    mt = [ARITH_HDR]
    for (j, tes, cr) in S.blemmas:
        mt.append(blemma(j, tes, cr))
    for (j, es, cr) in S.slemmas:
        mt.append(slemma(j, es, cr))
    mt.append(chainM(carries))
    for i, f in enumerate(wf):
        mt.append(flemma(i, f.es, carries))
    mt.append("\nend Solutions.OpensslX25519.I\n")
    open(os.path.join(D, 'I', 'M121Arith.lean'), 'w').write(''.join(mt))

    L = []
    a = L.append
    a("""import Solutions.OpensslX25519.I.M121Ends
import Solutions.OpensslX25519.I.M121Arith
import Solutions.OpensslX25519.Pair
import Solutions.OpensslX25519.Peel
import Solutions.OpensslX25519.I.Base
import Solutions.OpensslX25519.Call1
""")
    for i in range((NB + 5) // 6):
        a(f"import Solutions.OpensslX25519.I.M121Run{i + 1:02d}\n")
    a("""/-!
# `fe_mul121666` as a callee

Generated by `gen/genm121main.py`. The run of `fe_mul121666(h, f)` (`h` in `ecx`, `f` in `edx`) put
together from its pieces (`I/M121Ends`, `I/M121Run*`) at any instruction count and return address;
every value it computes is named and its meaning as a word or a 64-bit pair follows from `Pair`; the
stored words are the limbs of `chain121 (m121Raw f)` (`I/M121Arith`), and `fe_m121_math` gives the
`fe_mul` output bounds and the value `121666·f` modulo `p`, for an input within the `fe_add`/`fe_sub`
output bounds.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.OpensslX25519

attribute [local irreducible] rdRaw

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem fe_mul121666_call (G : XMem) (sp hp fp ret : UInt32) (fv : Array UInt32)
    (F : Facts1W 84 G.get.size sp.toNat hp.toNat fp.toNat) (hret0 : rdRaw G.get sp 4 = ret)
    (hfv : memWords G.get fp 10 = fv) (hin : AddOut fv) (a0 ebx0 ebp0 esi0 edi0 fl0 : UInt32)
    (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) :
    ∃ (N : XMem) (eax ecx edx fl : UInt32),
      Run img (St.m ⟨G.get, a0, hp, fp, ebx0, sp, ebp0, esi0, edi0, 0x103c00, efl fl0, ic0⟩)
        (St.m ⟨N.get, eax, ecx, edx, ebx0, sp + 4, ebp0, esi0, edi0, ret, efl fl, icAdd ic0 183⟩) ∧
      Pres G N (OutH (sp - 84) 84 hp) ∧
      MulOut (memWords N.get hp 10) ∧ feValI (memWords N.get hp 10) % pI = 121666 * feValI fv % pI := by
  have hTop : G.get.size ≤ ramTop := F.ram
  have hTop' : G.get.size ≤ 0xFEC00000 := hTop
  obtain ⟨fb, hfb⟩ : ∃ fb : UInt32, fb = sp - (84 : Nat).toUInt32 := ⟨_, rfl⟩
  have hfbN : fb.toNat = sp.toNat - 84 := by rw [hfb]; exact fb_toNatW F.sp_lo 84 (by decide)
  have hspfb : sp = UInt32.add fb 84 := by
    apply UInt32.toNat_inj.1
    rw [toNat_uadd, hfbN]
    have := F.sp_lo; have := sp.toNat_lt
    simp only [UInt32.reduceToNat]; omega
  have hS : FB G.get.size fb 88 := ⟨F.ram, by have := F.sp_hi; have := F.sp_lo; show _ ≤ G.get.size; omega,
    by have := F.sp_img; have := F.sp_lo; omega⟩
  have hH : FB G.get.size hp 40 := ⟨F.ram, F.h_mem, F.h_img⟩
  have hd : hp.toNat + 40 ≤ fb.toNat ∨ fb.toNat + 88 ≤ hp.toNat := by have := F.h_stk; have := F.sp_lo; omega
  have hfpm : fp.toNat + 40 ≤ G.get.size := F.f_mem
  have hfps : fp.toNat + 40 ≤ fb.toNat ∨ fb.toNat + 88 ≤ fp.toNat := by have := F.f_stk; have := F.sp_lo; omega
  have hret : rdRaw G.get (UInt32.add fb (84 : Nat).toUInt32) 4 = ret := by
    rw [show UInt32.add fb (84 : Nat).toUInt32 = sp from hspfb.symm]
    exact hret0
  have F0 : Frame G fb 88 [(84, ret)] := by
    intro k v hl
    rw [lookup_cons] at hl
    split at hl
    · rename_i hk; subst hk; simp only [Option.some.injEq] at hl; subst hl; exact ⟨rfl, by decide, hret⟩
    · simp at hl
  have e0 : St.m ⟨G.get, a0, hp, fp, ebx0, sp, ebp0, esi0, edi0, 0x103c00, efl fl0, ic0⟩ =
      St.m ⟨G.get, a0, hp, fp, ebx0, UInt32.add fb 84, ebp0, esi0, edi0, 0x103c00, efl fl0, icAdd ic0 0⟩ := by
    rw [← hspfb]; rfl
  rw [e0]
  obtain ⟨B0, Rn0', F00, P0⟩ := m121_pro ic0 hic G fb hS _ F0 a0 hp fp ebx0 ebp0 esi0 edi0 fl0
  have r1 := m121_sub ic0 hic B0 fb (hS.size_eq P0.1) a0 hp fp ebx0 ebp0 esi0 edi0 fl0
  obtain ⟨g0, eg0⟩ : ∃ y : UInt32, y = (subF 4 (UInt32.add fb 68) 68 0).2 := ⟨_, rfl⟩
  rw [← eg0] at r1
  have Rn0 := Rn0'.trans r1
  clear Rn0' r1
""")
    for nm, i in sorted(inputs.items(), key=lambda t: t[1]):
        key = addr_of[nm]
        sm = "" if key == 'fp' else "simp only [toNat_uadd, UInt32.reduceToNat]; "
        a(f"  obtain ⟨{nm}, h{nm}⟩ : ∃ y : UInt32, rdRaw G.get {key} 4 = y := ⟨_, rfl⟩\n")
        a(f"  have hin_{nm} : ∀ N : XMem, Pres G N (OutF fb 84) → rdRaw N.get {key} 4 = {nm} := fun N P =>\n"
          f"    (P.rd hTop (by {sm}omega) (fun k hk => by\n"
          f"      unfold OutF; {sm}omega)).trans h{nm}\n")
        a(f"  have hfv{i} : fv[{i}]! = {nm} := by\n"
          f"    rw [← hfv, memWords_getElem! _ _ _ _ (by decide), ← h{nm}]\n"
          f"    {'congr 1; simp' if i == 0 else 'rfl'}\n")
    for nm, i in sorted(inputs.items(), key=lambda t: t[1]):
        a(f"  obtain ⟨X{i}, hX{i}⟩ : ∃ X : Int, X = sv {nm} := ⟨_, rfl⟩\n")
        a(f"  have sx_{nm} : sv {nm} = X{i} := hX{i}.symm\n")
    a(f"  have hL : lift fv = {LX} := by\n"
      f"    rw [{', '.join(f'hX{i}' for i in range(10))}, {', '.join(f'← hfv{i}' for i in range(10))}]; rfl\n")
    a(f"  have hA : InA {LX} := hL ▸ inA_of_addOut hin\n")
    a("  have F0 := F00\n")
    for line in body + fin:
        a("  " + line + "\n")
    for i, f in enumerate(wf):
        a(f"  have fw{i} := sv_of_M32 ({f.name}.congr (m121_f{i} {XS} {cs} hA {hcs}).2) "
          f"(m121_f{i} {XS} {cs} hA {hcs}).1\n")
    a(f"""  have rld := m121_ld ic0 hic B{NB} fb (hS.size_eq P{NB}.1) {r['eax']} {r['ecx']} {r['edx']} {r['ebx']} {r['ebp']} {r['esi']} {r['edi']} {fl}
  rw [F{NB}.rd (rfl : List.lookup 64 _ = some hp) 64 rfl] at rld
  have Rn{NB}' := Rn{NB}.trans rld
  obtain ⟨O1, ro1, FO1, FH1, PO1⟩ := m121_o1 ic0 hic G B{NB} fb hp (hS.size_eq P{NB}.1) (hH.size_eq P{NB}.1) hd _ [] F{NB}
    (Frame.nil _ _ _) (P{NB}.toH hp) {r['ecx']} {r['edx']} {r['ebx']} {r['ebp']} {r['esi']} {r['edi']} {fl} {w[0]} {w[1]} {w[2]} {w[3]} rfl rfl rfl rfl
  obtain ⟨O2, ro2, FO2, FH2, PO2⟩ := m121_o2 ic0 hic G O1 fb hp (hS.size_eq PO1.1) (hH.size_eq PO1.1) hd _ _ FO1 FH1 PO1
    {r['ecx']} {r['edx']} {w[3]} {r['ebp']} {r['esi']} {r['edi']} {fl} {w[5]} rfl
  obtain ⟨O3, ro3, FO3, FH3, PO3⟩ := m121_o3 ic0 hic G O2 fb hp (hS.size_eq PO2.1) (hH.size_eq PO2.1) hd _ _ FO2 FH2 PO2
    {r['ecx']} {r['edx']} {w[3]} {r['ebp']} {r['esi']} {w[5]} {fl}
  have ra := m121_add ic0 hic O3 fb (hS.size_eq PO3.1) hp {r['ecx']} {r['edx']} {w[3]} {r['ebp']} {r['esi']} {w[5]} {fl}
  have re := m121_epi ic0 hic O3 fb (hS.size_eq PO3.1) _ FO3 hp {r['ecx']} {r['edx']} {w[3]} {r['ebp']} {r['esi']} {w[5]}
    (addF 4 fb 68 0).2 esi0 edi0 ebx0 ebp0 ret rfl rfl rfl rfl rfl
  have hsfb : sp - 84 = fb := by rw [hfb]; rfl
  have hesp : UInt32.add fb 88 = sp + 4 := by
    rw [hspfb]
    apply UInt32.toNat_inj.1
    rw [toNat_uadd, UInt32.toNat_add, toNat_uadd]
    have := hS.fit; have := hS.top; unfold ramTop at *; simp only [UInt32.reduceToNat]; omega
  have RR := Rn{NB}'.trans (ro1.trans (ro2.trans (ro3.trans (ra.trans re))))
  rw [hesp] at RR
  refine ⟨O3, _, _, _, _, RR, by rw [hsfb]; exact PO3, ?_⟩
  · have hw : ∀ i, i < 10 → (memWords O3.get hp 10)[i]!.toInt32.toInt =
        (chain121 (m121Raw (lift fv))).get i := by
      intro i hi
      rw [hL]
      rw [memWords_getElem! _ _ _ _ hi]
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
""")
    for i in range(10):
        a(f"      · exact (congrArg (fun x : UInt32 => x.toInt32.toInt) (FH3.rd (rfl : List.lookup {4 * i} _ = some {w[i]}) "
          f"(4 * ((({i} : Nat)).toUInt32)) rfl)).trans fw{i}\n")
    a("""    exact fe_m121_math fv _ hin (by simp [memWords]) hw

end Solutions.OpensslX25519.I
""")
    open(os.path.join(D, 'I', 'M121Call.lean'), 'w').write(''.join(L))
    print('pieces', NB, 'words', w, 'carries', [(c, s) for (c, _, s) in carries])


if __name__ == '__main__':
    main()
