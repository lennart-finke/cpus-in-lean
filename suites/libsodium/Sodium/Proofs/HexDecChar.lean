import Sodium.Proofs.HexDecLoop1
import Sodium.Proofs.HexDecLoop2
import Sodium.Proofs.HexDecDigits
import Sodium.Proofs.HexEncLoop
/-!
# `sodium_hex2bin`: one character of the loop

`head`: the 26 steps from the loop head to the branch on the state: the index `d` is kept at `t + 4`,
the character `v` at `T + d` is loaded and checked (`rOf v ≠ 0`), the output index `b` checked
against the output size `Q`, `bxOf v` is kept at `t`, the value of the digit is `valOf v`.
`char1`: then, for a first digit (state `al = 0`): `hivOf v` is kept at `t + 8`, the state becomes
`0xff`, back to the loop head. `char2`: for a second digit (`al = 0xff`): the byte `outOf v A` (from
the high nibble `A` at `t + 8`) is stored at `B + b`, `b` incremented, the state back to 0; it stops
before the loop's last branch. The reads of the stack and of the text are turned into the given
values `T`, `v`, `Q`, `L`, `A`, `B`.
-/
namespace Sodium.Proofs.HexDec
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Solutions.Logic.Cmp Solutions.Logic.Shb Sodium.Proofs
  Sodium.Utils Sodium.Spec
open Sodium.Proofs.Memzero (neHalt tf_efl u64_succ_toNat u32_toNat_add toNat_toUInt32)
open Sodium.Proofs.Memcmp (ic_chain)
open Sodium.Proofs.HexEnc (pst icb)

def headPath : List UInt32 :=
  [0x10026D, 0x10026F, 0x100273, 0x100277, 0x10027B, 0x10027D, 0x100280, 0x100286, 0x100289, 0x10028C,
   0x10028F, 0x100292, 0x100298, 0x10029E, 0x1002A0, 0x1002A3, 0x1002A5, 0x1002A7, 0x1002A9, 0x1002AC,
   0x1002AE, 0x1002B0, 0x1002B4, 0x1002BA, 0x1002BC, 0x1002BE]

def char1Path : List UInt32 :=
  headPath ++ [0x1002C0, 0x1002C2, 0x1002C4, 0x1002C7, 0x1002CB, 0x10025C, 0x10025E, 0x100262, 0x100263, 0x100267]

def char2Path : List UInt32 :=
  headPath ++ [0x1002C0, 0x1002C2, 0x100250, 0x100254, 0x100258, 0x10025B, 0x10025C, 0x10025E, 0x100262, 0x100263]

/-- The stack words `[t, t + 64)` are in memory and apart from the code. -/
structure Stk (M : SMem) (t : UInt32) : Prop where
  hsz : M.get.size ≤ 4273995776
  hst : t.toNat + 64 ≤ M.get.size
  hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat

theorem tk {t : UInt32} (k : Nat) (hk : k < 64) (h : t.toNat + 64 ≤ 4273995776) :
    (t.add k.toUInt32).toNat = t.toNat + k := by
  rw [u32_toNat_add (by rw [toNat_toUInt32 (by omega)]; omega), toNat_toUInt32 (by omega)]

theorem stk_size {M M' : SMem} {t : UInt32} (hS : Stk M t) (h : M'.get.size = M.get.size) : Stk M' t :=
  ⟨by rw [h]; exact hS.hsz, by rw [h]; exact hS.hst, hS.hap⟩

theorem storeOk_of {M : SMem} {a : UInt32} (h1 : a.toNat + 4 ≤ M.get.size)
    (h2 : a.toNat + 4 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ a.toNat) : StoreOk Image.base Image.size M.mem a :=
  ⟨h1, by simp only [Image.base, Image.size, UInt32.reduceToNat]; omega⟩

theorem storeOk1_of {M : SMem} {a : UInt32} (h1 : a.toNat < M.get.size)
    (h2 : a.toNat < 0x100000 ∨ 0x100000 + 3560 ≤ a.toNat) : StoreOk1 Image.base Image.size M.mem a :=
  ⟨h1, by simp only [Image.base, Image.size, UInt32.reduceToNat]; omega⟩

/-- The byte read back from a word just stored. -/
theorem rdBytes1_wrBytes4_self {mem : ByteArray} {a v : UInt32} (h : a.toNat + 4 ≤ mem.size) :
    rdBytes (wrBytes mem a 4 v) a 1 = v.toUInt8.toUInt32 := by
  rw [rdBytes1_eq (by rw [size_wrBytes4 h]; omega), memByte_def (by rw [size_wrBytes4 h]; omega),
    get!_wrBytes4 h, if_pos rfl]

set_option maxHeartbeats 0 in
/-- The steps up to the branch on the state. -/
theorem head (M : SMem) (t a c d b p s i F T v Q : UInt32) (ic : UInt64) (hS : Stk M t)
    (hT : rdRaw M.get (t.add 40) 4 = T) (hv : rdRaw M.get (T.add d) 1 = v)
    (hTd : (T.add d).toNat < M.get.size) (hTdi : (T.add d).toNat < 0x100000 ∨ 0x100000 + 3560 ≤ (T.add d).toNat)
    (hTdt : (T.add d).toNat < t.toNat ∨ t.toNat + 64 ≤ (T.add d).toNat)
    (hQ : rdRaw M.get (t.add 36) 4 = Q) (hval : (rOf v).toNat ≠ 0) (hbQ : b.toNat < Q.toNat)
    (hic : ic.toNat + 40 < 2 ^ 64) :
    ∃ (M2 : SMem), M2.get = wrBytes (wrBytes M.get (t.add 4) 4 d) t 4 (bxOf v) ∧
      PRun img headPath (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10026D, efl F, ic⟩)
        (St.m ⟨M2.get, a, (aOf v).land (alOf v), valOf v, b, t, b, v.xor 48, alOf v, 0x1002C0,
          efl (logicF 4 (valOf v)).2, ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩) := by
  have hsz := hS.hsz; have hst := hS.hst; have hap := hS.hap
  have h4 : (t.add 4).toNat = t.toNat + 4 := tk 4 (by decide) (by omega)
  have h36 : (t.add 36).toNat = t.toNat + 36 := tk 36 (by decide) (by omega)
  have ok1 : StoreOk Image.base Image.size M.mem (t.add 4) := storeOk_of (by rw [h4]; omega) (by rw [h4]; omega)
  let M1 := CodeMem.wr4 M (t.add 4) d ok1
  have s1 : M1.get.size = M.get.size := wr4_get_size _ _ _ _
  have hS1 : Stk M1 t := stk_size hS s1
  have ok2 : StoreOk Image.base Image.size M1.mem t := storeOk_of (by rw [s1]; omega) (by omega)
  let M2 := CodeMem.wr4 M1 t (bxOf v) ok2
  have hS2 : Stk M2 t := stk_size hS (by rw [wr4_get_size, s1])
  have rv : rdRaw M1.get (T.add d) 1 = v := by
    rw [rdRaw_wr4_other1 _ _ _ _ _ hTd (by rw [h4]; omega), hv]
  have rQ : rdRaw M2.get (t.add 36) 4 = Q := by
    rw [rdRaw_wr4_other4 _ _ _ _ _ (by rw [s1, h36]; omega) (by rw [h36]; omega),
      rdRaw_wr4_other4 _ _ _ _ _ (by rw [h36]; omega) (by rw [h36, h4]; omega), hQ]
  have p1 := pst (s26d M a c d b t p s i F ic hS.hsz hS.hst hS.hap)
    (icb 0 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p2 := pst (s26f M a c d b t b s i F (ic + 1) hS.hsz hS.hst hS.hap)
    (icb 1 (by omega)) (tf_efl _) (neHalt _ (by decide))
  rw [hT] at p2
  have p3 := pst (s273 M a T d b t b s i F (ic + 1 + 1) hS.hsz hS.hst hS.hap ok1)
    (icb 2 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p4 := pst (s277 M1 a T d b t b s i F (ic + 1 + 1 + 1) (hS1).hsz (hS1).hst hS.hap (by rw [s1]; exact hTd) hTdi)
    (icb 3 (by omega)) (tf_efl _) (neHalt _ (by decide))
  rw [rv] at p4
  have p5 := pst (s27b M1 a v d b t b s i F (ic + 1 + 1 + 1 + 1) (hS1).hsz (hS1).hst hS.hap)
    (icb 4 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p6 := pst (s27d M1 a v d b t b v i F (ic + 1 + 1 + 1 + 1 + 1) (hS1).hsz (hS1).hst hS.hap)
    (icb 5 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p7 := pst (s280 M1 a v d b t b (v.xor 48) i (logicF 4 (v.xor 48)).2 (ic + 1 + 1 + 1 + 1 + 1 + 1) (hS1).hsz (hS1).hst hS.hap)
    (icb 6 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p8 := pst (s286 M1 a v ((v.xor 48).add 65526) b t b (v.xor 48) i (logicF 4 (v.xor 48)).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS1).hsz (hS1).hst hS.hap)
    (icb 7 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p9 := pst (s289 M1 a v (nOf v) b t b (v.xor 48) i (shFl 5 ((v.xor 48).add 65526) 8) (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS1).hsz (hS1).hst hS.hap)
    (icb 8 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p10 := pst (s28c M1 a ((v.land 4294967040).lor (((v.land 255).land 223).land 255)) (nOf v) b t b (v.xor 48) i (logicF 1 ((v.land 255).land 223)).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS1).hsz (hS1).hst hS.hap)
    (icb 9 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p11 := pst (s28f M1 a ((((v.land 4294967040).lor (((v.land 255).land 223).land 255)).land 4294967040).lor ((addF 1 (((v.land 4294967040).lor (((v.land 255).land 223).land 255)).land 255) 201 0).1.land 255)) (nOf v) b t b (v.xor 48) i (addF 1 (((v.land 4294967040).lor (((v.land 255).land 223).land 255)).land 255) 201 0).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS1).hsz (hS1).hst hS.hap)
    (icb 10 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p12 := pst (s292 M1 a ((((v.land 4294967040).lor (((v.land 255).land 223).land 255)).land 4294967040).lor ((addF 1 (((v.land 4294967040).lor (((v.land 255).land 223).land 255)).land 255) 201 0).1.land 255)) (nOf v) b t b (v.xor 48) (alOf v) (addF 1 (((v.land 4294967040).lor (((v.land 255).land 223).land 255)).land 255) 201 0).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS1).hsz (hS1).hst hS.hap)
    (icb 11 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p13 := pst (s298 M1 a ((alOf v).add 65526) (nOf v) b t b (v.xor 48) (alOf v) (addF 1 (((v.land 4294967040).lor (((v.land 255).land 223).land 255)).land 255) 201 0).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS1).hsz (hS1).hst hS.hap)
    (icb 12 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p14 := pst (s29e M1 a ((alOf v).add 65526) (nOf v) ((alOf v).add 65520) t b (v.xor 48) (alOf v) (addF 1 (((v.land 4294967040).lor (((v.land 255).land 223).land 255)).land 255) 201 0).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS1).hsz (hS1).hst hS.hap)
    (icb 13 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p15 := pst (s2a0 M1 a (((alOf v).add 65526).xor ((alOf v).add 65520)) (nOf v) ((alOf v).add 65520) t b (v.xor 48) (alOf v) (logicF 4 (((alOf v).add 65526).xor ((alOf v).add 65520))).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS1).hsz (hS1).hst hS.hap)
    (icb 14 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p16 := pst (s2a3 M1 a (aOf v) (nOf v) ((alOf v).add 65520) t b (v.xor 48) (alOf v) (shFl 5 (((alOf v).add 65526).xor ((alOf v).add 65520)) 8) (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS1).hsz (hS1).hst hS.hap)
    (icb 15 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p17 := pst (s2a5 M1 a (aOf v) (nOf v) (nOf v) t b (v.xor 48) (alOf v) (shFl 5 (((alOf v).add 65526).xor ((alOf v).add 65520)) 8) (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS1).hsz (hS1).hst hS.hap)
    (icb 16 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p18 := pst (s2a7 M1 a (aOf v) (nOf v) (((nOf v).land 4294967040).lor ((rOf v).land 255)) t b (v.xor 48) (alOf v) (logicF 1 (rOf v)).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS1).hsz (hS1).hst hS.hap)
    (icb 17 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p19 := pst (s2a9 M1 a (aOf v) (nOf v) (bxOf v) t b (v.xor 48) (alOf v) (logicF 1 (rOf v)).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS1).hsz (hS1).hst hS.hap ok2)
    (icb 18 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p20 := pst (s2ac M2 a (aOf v) (nOf v) (bxOf v) t b (v.xor 48) (alOf v) 0 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS2).hsz (hS2).hst hS.hap (rOf v) hval)
    (icb 19 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p21 := pst (s2ae M2 a (aOf v) (nOf v) (bxOf v) t b (v.xor 48) (alOf v) (logicF 1 (rOf v)).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS2).hsz (hS2).hst hS.hap)
    (icb 20 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p22 := pst (s2b0 M2 a (aOf v) (nOf v) b t b (v.xor 48) (alOf v) (logicF 1 (rOf v)).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS2).hsz (hS2).hst hS.hap)
    (icb 21 (by omega)) (tf_efl _) (neHalt _ (by decide))
  rw [rQ] at p22
  have p23 := pst (s2b4 M2 a (aOf v) (nOf v) b t b (v.xor 48) (alOf v) 0 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS2).hsz (hS2).hst hS.hap Q hbQ)
    (icb 22 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p24 := pst (s2ba M2 a (aOf v) (nOf v) b t b (v.xor 48) (alOf v) (subF 4 b Q 0).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS2).hsz (hS2).hst hS.hap)
    (icb 23 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p25 := pst (s2bc M2 a ((aOf v).land (alOf v)) (nOf v) b t b (v.xor 48) (alOf v) (logicF 4 ((aOf v).land (alOf v))).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS2).hsz (hS2).hst hS.hap)
    (icb 24 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p26 := pst (s2be M2 a ((aOf v).land (alOf v)) ((nOf v).land (v.xor 48)) b t b (v.xor 48) (alOf v) (logicF 4 ((nOf v).land (v.xor 48))).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS2).hsz (hS2).hst hS.hap)
    (icb 25 (by omega)) (tf_efl _) (neHalt _ (by decide))
  exact ⟨M2, rfl, (p1.append (p2.append (p3.append (p4.append (p5.append (p6.append (p7.append (p8.append (p9.append (p10.append (p11.append (p12.append (p13.append (p14.append (p15.append (p16.append (p17.append (p18.append (p19.append (p20.append (p21.append (p22.append (p23.append (p24.append (p25.append (p26)))))))))))))))))))))))))).cast rfl⟩

set_option maxHeartbeats 0 in
/-- A first digit. -/
theorem char1 (M : SMem) (t c d b p s i F T v Q L : UInt32) (ic : UInt64) (hS : Stk M t)
    (hT : rdRaw M.get (t.add 40) 4 = T) (hv : rdRaw M.get (T.add d) 1 = v)
    (hTd : (T.add d).toNat < M.get.size) (hTdi : (T.add d).toNat < 0x100000 ∨ 0x100000 + 3560 ≤ (T.add d).toNat)
    (hTdt : (T.add d).toNat < t.toNat ∨ t.toNat + 64 ≤ (T.add d).toNat)
    (hQ : rdRaw M.get (t.add 36) 4 = Q) (hval : (rOf v).toNat ≠ 0) (hbQ : b.toNat < Q.toNat)
    (hic : ic.toNat + 40 < 2 ^ 64)
    (hL : rdRaw M.get (t.add 44) 4 = L) (hne : L.toNat ≠ (d.add 1).toNat) :
    ∃ (M' : SMem) (c' s' i' : UInt32) (ic' : UInt64),
      M'.get = wrBytes (wrBytes (wrBytes M.get (t.add 4) 4 d) t 4 (bxOf v)) (t.add 8) 4 (hivOf v) ∧
      PRun img char1Path (St.m ⟨M.get, 0, c, d, b, t, p, s, i, 0x10026D, efl F, ic⟩)
        (St.m ⟨M'.get, 255, c', d.add 1, b, t, b, s', i', 0x10026D, efl (subF 4 L (d.add 1) 0).2, ic'⟩) ∧
      ic'.toNat = ic.toNat + 36 := by
  have hsz := hS.hsz; have hst := hS.hst; have hap := hS.hap
  have h4 : (t.add 4).toNat = t.toNat + 4 := tk 4 (by decide) (by omega)
  have h8 : (t.add 8).toNat = t.toNat + 8 := tk 8 (by decide) (by omega)
  have h44 : (t.add 44).toNat = t.toNat + 44 := tk 44 (by decide) (by omega)
  obtain ⟨M2, hM2, ph⟩ := head M t 0 c d b p s i F T v Q ic hS hT hv hTd hTdi hTdt hQ hval hbQ hic
  have s2 : M2.get.size = M.get.size := by rw [hM2, size_wrBytes, size_wrBytes]
  have hS2 : Stk M2 t := stk_size hS s2
  have ok3 : StoreOk Image.base Image.size M2.mem (t.add 8) := storeOk_of (by rw [s2, h8]; omega) (by rw [h8]; omega)
  let M3 := CodeMem.wr4 M2 (t.add 8) (hivOf v) ok3
  have hS3 : Stk M3 t := stk_size hS (by rw [wr4_get_size, s2])
  have rd4 : rdRaw M3.get (t.add 4) 4 = d := by
    show rdBytes (wrBytes M2.get (t.add 8) 4 (hivOf v)) (t.add 4) 4 = d
    rw [rdBytes4_wrBytes4_other (by rw [s2, h8]; omega) (by rw [s2, h4]; omega) (by rw [h4, h8]; omega), hM2,
      rdBytes4_wrBytes4_other (by rw [size_wrBytes]; omega) (by rw [size_wrBytes, h4]; omega) (by rw [h4]; omega),
      rdBytes4_wrBytes4_self (by rw [h4]; omega)]
  have rL : rdRaw M3.get (t.add 44) 4 = L := by
    show rdBytes (wrBytes M2.get (t.add 8) 4 (hivOf v)) (t.add 44) 4 = L
    rw [rdBytes4_wrBytes4_other (by rw [s2, h8]; omega) (by rw [s2, h44]; omega) (by rw [h44, h8]; omega), hM2,
      rdBytes4_wrBytes4_other (by rw [size_wrBytes]; omega) (by rw [size_wrBytes, h44]; omega) (by rw [h44]; omega),
      rdBytes4_wrBytes4_other (by rw [h4]; omega) (by rw [h44]; omega) (by rw [h44, h4]; omega)]
    exact hL
  have p27 := pst (s2c0z M2 0 ((aOf v).land (alOf v)) (valOf v) b t b (v.xor 48) (alOf v) (logicF 4 (valOf v)).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS2).hsz (hS2).hst hS.hap)
    (icb 26 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p28 := pst (s2c2z M2 0 ((aOf v).land (alOf v)) (valOf v) b t b (v.xor 48) (alOf v) 0 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS2).hsz (hS2).hst hS.hap)
    (icb 27 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p29 := pst (s2c4 M2 0 ((aOf v).land (alOf v)) (valOf v) b t b (v.xor 48) (alOf v) (logicF 1 0).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS2).hsz (hS2).hst hS.hap)
    (icb 28 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p30 := pst (s2c7 M2 0 ((aOf v).land (alOf v)) (hivOf v) b t b (v.xor 48) (alOf v) (shFl1 4 ((valOf v).land 255) 4) (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS2).hsz (hS2).hst hS.hap ok3)
    (icb 29 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p31 := pst (s2cb M3 0 ((aOf v).land (alOf v)) (hivOf v) b t b (v.xor 48) (alOf v) (shFl1 4 ((valOf v).land 255) 4) (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS3).hsz (hS3).hst hS.hap)
    (icb 30 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p32 := pst (s25cz M3 0 ((aOf v).land (alOf v)) (hivOf v) b t b (v.xor 48) (alOf v) (shFl1 4 ((valOf v).land 255) 4) (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS3).hsz (hS3).hst hS.hap)
    (icb 31 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p33 := pst (s25e M3 255 ((aOf v).land (alOf v)) (hivOf v) b t b (v.xor 48) (alOf v) (shFl1 4 ((valOf v).land 255) 4) (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS3).hsz (hS3).hst hS.hap)
    (icb 32 (by omega)) (tf_efl _) (neHalt _ (by decide))
  rw [rd4] at p33
  have p34 := pst (s262 M3 255 ((aOf v).land (alOf v)) d b t b (v.xor 48) (alOf v) (shFl1 4 ((valOf v).land 255) 4) (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS3).hsz (hS3).hst hS.hap)
    (icb 33 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p35 := pst (s263 M3 255 ((aOf v).land (alOf v)) (d.add 1) b t b (v.xor 48) (alOf v) (mixF (shFl1 4 ((valOf v).land 255) 4) (addF 4 d 1 0).2 2260) (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS3).hsz (hS3).hst hS.hap)
    (icb 34 (by omega)) (tf_efl _) (neHalt _ (by decide))
  rw [rL] at p35
  have p36 := pst (s267b M3 255 ((aOf v).land (alOf v)) (d.add 1) b t b (v.xor 48) (alOf v) 0 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS3).hsz (hS3).hst hS.hap L hne)
    (icb 35 (by omega)) (tf_efl _) (neHalt _ (by decide))
  refine ⟨M3, _, _, _, _, (by show wrBytes M2.get (t.add 8) 4 (hivOf v) = _; rw [hM2]), (ph.append (p27.append (p28.append (p29.append (p30.append (p31.append (p32.append (p33.append (p34.append (p35.append (p36))))))))))).cast rfl, ic_chain 36 (by omega)⟩

set_option maxHeartbeats 0 in
/-- A second digit, up to the loop's last branch. -/
theorem char2 (M : SMem) (t c d b p s i F T v Q L A B : UInt32) (ic : UInt64) (hS : Stk M t)
    (hT : rdRaw M.get (t.add 40) 4 = T) (hv : rdRaw M.get (T.add d) 1 = v)
    (hTd : (T.add d).toNat < M.get.size) (hTdi : (T.add d).toNat < 0x100000 ∨ 0x100000 + 3560 ≤ (T.add d).toNat)
    (hTdt : (T.add d).toNat < t.toNat ∨ t.toNat + 64 ≤ (T.add d).toNat)
    (hQ : rdRaw M.get (t.add 36) 4 = Q) (hval : (rOf v).toNat ≠ 0) (hbQ : b.toNat < Q.toNat)
    (hic : ic.toNat + 40 < 2 ^ 64)
    (hL : rdRaw M.get (t.add 44) 4 = L) (hA : rdRaw M.get (t.add 8) 1 = A) (hB : rdRaw M.get (t.add 32) 4 = B)
    (hBb : (B.add b).toNat < M.get.size) (hBbi : (B.add b).toNat < 0x100000 ∨ 0x100000 + 3560 ≤ (B.add b).toNat)
    (hBbt : (B.add b).toNat < t.toNat ∨ t.toNat + 64 ≤ (B.add b).toNat) :
    ∃ (M' : SMem) (s' i' : UInt32) (ic' : UInt64),
      M'.get = wrBytes (wrBytes (wrBytes M.get (t.add 4) 4 d) t 4 (bxOf v)) (B.add b) 1 ((outOf v A).land 255) ∧
      PRun img char2Path (St.m ⟨M.get, 255, c, d, b, t, p, s, i, 0x10026D, efl F, ic⟩)
        (St.m ⟨M'.get, 0, B, d.add 1, b.add 1, t, b, s', i', 0x100267, efl (subF 4 L (d.add 1) 0).2, ic'⟩) ∧
      ic'.toNat = ic.toNat + 36 := by
  have hsz := hS.hsz; have hst := hS.hst; have hap := hS.hap
  have h4 : (t.add 4).toNat = t.toNat + 4 := tk 4 (by decide) (by omega)
  have h8 : (t.add 8).toNat = t.toNat + 8 := tk 8 (by decide) (by omega)
  have h32 : (t.add 32).toNat = t.toNat + 32 := tk 32 (by decide) (by omega)
  have h44 : (t.add 44).toNat = t.toNat + 44 := tk 44 (by decide) (by omega)
  obtain ⟨M2, hM2, ph⟩ := head M t 255 c d b p s i F T v Q ic hS hT hv hTd hTdi hTdt hQ hval hbQ hic
  have s2 : M2.get.size = M.get.size := by rw [hM2, size_wrBytes, size_wrBytes]
  have hS2 : Stk M2 t := stk_size hS s2
  have rA : rdRaw M2.get (t.add 8) 1 = A := by
    show rdBytes M2.get (t.add 8) 1 = A
    rw [hM2, rdBytes1_wrBytes4_other (by rw [size_wrBytes]; omega) (by rw [size_wrBytes, h8]; omega) (by rw [h8]; omega),
      rdBytes1_wrBytes4_other (by rw [h4]; omega) (by rw [h8]; omega) (by rw [h8, h4]; omega)]
    exact hA
  have rB : rdRaw M2.get (t.add 32) 4 = B := by
    show rdBytes M2.get (t.add 32) 4 = B
    rw [hM2, rdBytes4_wrBytes4_other (by rw [size_wrBytes]; omega) (by rw [size_wrBytes, h32]; omega) (by rw [h32]; omega),
      rdBytes4_wrBytes4_other (by rw [h4]; omega) (by rw [h32]; omega) (by rw [h32, h4]; omega)]
    exact hB
  have ok4 : StoreOk1 Image.base Image.size M2.mem (B.add b) := storeOk1_of (by rw [s2]; exact hBb) hBbi
  let M4 := CodeMem.wr1 M2 (B.add b) ((outOf v A).land 255) ok4
  have s4 : M4.get.size = M.get.size := by rw [wr1_get_size, s2]
  have hS4 : Stk M4 t := stk_size hS s4
  have rd4 : rdRaw M4.get (t.add 4) 4 = d := by
    show rdBytes (wrBytes M2.get (B.add b) 1 ((outOf v A).land 255)) (t.add 4) 4 = d
    rw [rdBytes4_wrBytes1_other (by rw [s2]; exact hBb) (by rw [s2, h4]; omega) (by rw [h4]; omega), hM2,
      rdBytes4_wrBytes4_other (by rw [size_wrBytes]; omega) (by rw [size_wrBytes, h4]; omega) (by rw [h4]; omega),
      rdBytes4_wrBytes4_self (by rw [h4]; omega)]
  have rL : rdRaw M4.get (t.add 44) 4 = L := by
    show rdBytes (wrBytes M2.get (B.add b) 1 ((outOf v A).land 255)) (t.add 44) 4 = L
    rw [rdBytes4_wrBytes1_other (by rw [s2]; exact hBb) (by rw [s2, h44]; omega) (by rw [h44]; omega), hM2,
      rdBytes4_wrBytes4_other (by rw [size_wrBytes]; omega) (by rw [size_wrBytes, h44]; omega) (by rw [h44]; omega),
      rdBytes4_wrBytes4_other (by rw [h4]; omega) (by rw [h44]; omega) (by rw [h44, h4]; omega)]
    exact hL
  have p27 := pst (s2c0f M2 255 ((aOf v).land (alOf v)) (valOf v) b t b (v.xor 48) (alOf v) (logicF 4 (valOf v)).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS2).hsz (hS2).hst hS.hap)
    (icb 26 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p28 := pst (s2c2f M2 255 ((aOf v).land (alOf v)) (valOf v) b t b (v.xor 48) (alOf v) 0 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS2).hsz (hS2).hst hS.hap)
    (icb 27 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p29 := pst (s250 M2 255 ((aOf v).land (alOf v)) (valOf v) b t b (v.xor 48) (alOf v) (logicF 1 255).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS2).hsz (hS2).hst hS.hap)
    (icb 28 (by omega)) (tf_efl _) (neHalt _ (by decide))
  rw [rA] at p29
  have p30 := pst (s254 M2 255 ((aOf v).land (alOf v)) (outOf v A) b t b (v.xor 48) (alOf v) (logicF 1 (((valOf v).land 255).lor A)).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS2).hsz (hS2).hst hS.hap)
    (icb 29 (by omega)) (tf_efl _) (neHalt _ (by decide))
  rw [rB] at p30
  have p31 := pst (s258 M2 255 B (outOf v A) b t b (v.xor 48) (alOf v) (logicF 1 (((valOf v).land 255).lor A)).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS2).hsz (hS2).hst hS.hap (by rw [s2]; exact hBb) hBbi ok4)
    (icb 30 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p32 := pst (s25b M4 255 B (outOf v A) b t b (v.xor 48) (alOf v) (logicF 1 (((valOf v).land 255).lor A)).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS4).hsz (hS4).hst hS.hap)
    (icb 31 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p33 := pst (s25cf M4 255 B (outOf v A) (b.add 1) t b (v.xor 48) (alOf v) (mixF (logicF 1 (((valOf v).land 255).lor A)).2 (addF 4 b 1 0).2 2260) (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS4).hsz (hS4).hst hS.hap)
    (icb 32 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p34 := pst (s25e M4 0 B (outOf v A) (b.add 1) t b (v.xor 48) (alOf v) (mixF (logicF 1 (((valOf v).land 255).lor A)).2 (addF 4 b 1 0).2 2260) (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS4).hsz (hS4).hst hS.hap)
    (icb 33 (by omega)) (tf_efl _) (neHalt _ (by decide))
  rw [rd4] at p34
  have p35 := pst (s262 M4 0 B d (b.add 1) t b (v.xor 48) (alOf v) (mixF (logicF 1 (((valOf v).land 255).lor A)).2 (addF 4 b 1 0).2 2260) (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS4).hsz (hS4).hst hS.hap)
    (icb 34 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p36 := pst (s263 M4 0 B (d.add 1) (b.add 1) t b (v.xor 48) (alOf v) (mixF (mixF (logicF 1 (((valOf v).land 255).lor A)).2 (addF 4 b 1 0).2 2260) (addF 4 d 1 0).2 2260) (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (hS4).hsz (hS4).hst hS.hap)
    (icb 35 (by omega)) (tf_efl _) (neHalt _ (by decide))
  rw [rL] at p36
  refine ⟨M4, _, _, _, (by show wrBytes M2.get (B.add b) 1 ((outOf v A).land 255) = _; rw [hM2]), (ph.append (p27.append (p28.append (p29.append (p30.append (p31.append (p32.append (p33.append (p34.append (p35.append (p36))))))))))).cast rfl, ic_chain 36 (by omega)⟩

end Sodium.Proofs.HexDec
