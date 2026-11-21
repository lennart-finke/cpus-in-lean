import Sodium.Proofs.HexEncSteps
import Sodium.Proofs.HexDigits
import Sodium.Proofs.Memcmp
/-!
# `sodium_bin2hex`: the loop

One iteration (`body`, the steps of `HexEncSteps` composed) loads the byte `v` at `B + i` and stores
`hiOf v` at `P + 2i` and `loOf v` at `P + 2i + 1`. The loop invariant (`Inv`) says that the bytes of
`[P, P + 2i)` are the first `2i` digits of `hex x` and all other bytes those at the loop entry
(`HexOk`), in the style of `Memzero.BytesOk`. Every iteration runs along the same addresses
(`iterPath`).
-/
namespace Sodium.Proofs.HexEnc
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Solutions.Logic.Cmp Sodium.Proofs Sodium.Utils Sodium.Spec
open Sodium.Proofs.Memzero (running_of_eip neHalt tf_efl u64_succ_toNat u64_lt_max toNat_toUInt32
  succ_toUInt32 u32_toNat_sub u32_toNat_add)
open Sodium.Proofs.Memcmp (pstep2 ic_chain)

/-! ## Paths -/

/-- The addresses of an iteration up to the branch. -/
def bodyPath : List UInt32 :=
  [0x100030, 0x100034, 0x100036, 0x100039, 0x10003C, 0x100042, 0x100045, 0x10004B, 0x100052, 0x100058,
   0x10005B, 0x100061, 0x100063, 0x100066, 0x100069, 0x10006D, 0x10006E]

/-- The addresses of an iteration. -/
def iterPath : List UInt32 := bodyPath ++ [0x100070]

/-- `pstep2` with the step first (so that it fixes the instruction count). -/
theorem pst {mem mem' : ByteArray} {eax ecx edx ebx esp ebp esi edi eip fl eax' ecx' edx' ebx' esp' ebp' esi'
      edi' eip' fl' : UInt32} {ic : UInt64}
    (hx : okState (execInstr (St.m ⟨mem, eax, ecx, edx, ebx, esp, ebp, esi, edi, eip, fl, ic⟩)) =
      some (St.m ⟨mem', eax', ecx', edx', ebx', esp', ebp', esi', edi', eip', fl', ic⟩))
    (hic : ic.toNat + 1 < 2 ^ 64) (hTF : fl &&& Flag.TF = 0) (he : eip ≠ Image.sym_halt) :
    PRun img [eip] (St.m ⟨mem, eax, ecx, edx, ebx, esp, ebp, esi, edi, eip, fl, ic⟩)
      (St.m ⟨mem', eax', ecx', edx', ebx', esp', ebp', esi', edi', eip', fl', ic + 1⟩) :=
  pstep2 hic hTF hx he

theorem icb {ic : UInt64} (k : Nat) (hk : ic.toNat + k + 1 < 2 ^ 64) :
    (Nat.rec ic (fun _ x => x + 1) k : UInt64).toNat + 1 < 2 ^ 64 := by
  rw [ic_chain k (by omega)]; exact hk

/-! ## One iteration -/

set_option maxHeartbeats 0 in
/-- The seventeen steps of an iteration up to the branch. -/
theorem body (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hi : i.toNat < N.toNat) (hN : N.toNat < 1073741824) (hBs : B.toNat + N.toNat ≤ M.get.size)
    (hBi : B.toNat + N.toNat ≤ 0x100000 ∨ 0x100000 + 3560 ≤ B.toNat)
    (hPs : P.toNat + 2 * N.toNat < M.get.size)
    (hPi : P.toNat + 2 * N.toNat < 0x100000 ∨ 0x100000 + 3560 ≤ P.toNat)
    (ok1 : StoreOk1 Image.base Image.size M.mem (P.add (i.add i)))
    (ok2 : StoreOk1 Image.base Image.size
      (CodeMem.wr1 M (P.add (i.add i)) (hiOf (rdRaw M.get (B.add i) 1)) ok1).mem ((P.add (i.add i)).add 1))
    (hic : ic.toNat + 18 < 2 ^ 64) :
    ∃ (c' d' b' : UInt32) (ic' : UInt64), PRun img bodyPath
      (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100030, efl F, ic⟩)
      (St.m ⟨(CodeMem.wr1 (CodeMem.wr1 M (P.add (i.add i)) (hiOf (rdRaw M.get (B.add i) 1)) ok1)
          ((P.add (i.add i)).add 1) (loOf (rdRaw M.get (B.add i) 1)) ok2).get,
        P, c', d', b', t, N, B, i.add 1, 0x100070, efl (subF 4 N (i.add 1) 0).2, ic'⟩) ∧
      ic'.toNat = ic.toNat + 17 := by
  let v := rdRaw M.get (B.add i) 1
  let c2 := v.land 15
  let b1 := v.shiftRight 4
  let d5 := c2.add 65526
  let c3 := c2.shiftLeft 8
  let d7 := d5.land 55552
  let c4 := (c3.add d7).add 22272
  let d9 := b1.add 65526
  let d10 := d9.shiftRight 8
  let d11 := d10.land 217
  let d12 := d11.add b1
  let d13 := (d12.land 4294967040).lor ((addF 1 (d12.land 255) 87 0).1.land 255)
  let M1 := CodeMem.wr1 M (P.add (i.add i)) (hiOf v) ok1
  let M2 := CodeMem.wr1 M1 ((P.add (i.add i)).add 1) (loOf v) ok2
  have s1 : M1.get.size ≤ 4273995776 := by rw [wr1_get_size]; exact hsz
  have s2 : M2.get.size ≤ 4273995776 := by rw [wr1_get_size, wr1_get_size]; exact hsz
  have q1 : M1.get.size = M.get.size := wr1_get_size _ _ _ _
  have p1 := pst (l01 M P c d b t N B i F ic hsz hi hBs hBi) (icb 0 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p2 := pst (l02 M P c d v t N B i F (ic + 1) hsz) (icb 1 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p3 := pst (l03 M P v d v t N B i F (ic + 1 + 1) hsz) (icb 2 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p4 := pst (l04 M P c2 d v t N B i (logicF 4 c2).2 (ic + 1 + 1 + 1) hsz) (icb 3 (by omega)) (tf_efl _)
    (neHalt _ (by decide))
  have p5 := pst (l05 M P c2 d b1 t N B i (shFl 5 v 4) (ic + 1 + 1 + 1 + 1) hsz) (icb 4 (by omega)) (tf_efl _)
    (neHalt _ (by decide))
  have p6 := pst (l06 M P c2 d5 b1 t N B i (shFl 5 v 4) (ic + 1 + 1 + 1 + 1 + 1) hsz) (icb 5 (by omega))
    (tf_efl _) (neHalt _ (by decide))
  have p7 := pst (l07 M P c3 d5 b1 t N B i (shFl 4 c2 8) (ic + 1 + 1 + 1 + 1 + 1 + 1) hsz) (icb 6 (by omega))
    (tf_efl _) (neHalt _ (by decide))
  have p8 := pst (l08 M P c3 d7 b1 t N B i (logicF 4 d7).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1) hsz)
    (icb 7 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p9 := pst (l09 M P c4 d7 b1 t N B i (logicF 4 d7).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) hsz)
    (icb 8 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p10 := pst (l10 M P c4 d9 b1 t N B i (logicF 4 d7).2 (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) hsz)
    (icb 9 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p11 := pst (l11 M P c4 d10 b1 t N B i (shFl 5 d9 8) (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) hsz)
    (icb 10 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p12 := pst (l12 M P c4 d11 b1 t N B i (logicF 4 d11).2
    (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) hsz) (icb 11 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p13 := pst (l13 M P c4 d12 b1 t N B i (addF 4 d11 b1 0).2
    (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) hsz) (icb 12 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p14 := pst (l14 M P c4 d13 b1 t N B i (addF 1 (d12.land 255) 87 0).2
    (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) hsz hi hN hPs hPi ok1) (icb 13 (by omega)) (tf_efl _)
    (neHalt _ (by decide))
  have p15 := pst (l15 M1 P c4 d13 b1 t N B i (addF 1 (d12.land 255) 87 0).2
    (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) s1 hi hN (by rw [q1]; exact hPs) hPi ok2)
    (icb 14 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p16 := pst (l16 M2 P c4 d13 b1 t N B i (addF 1 (d12.land 255) 87 0).2
    (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) s2)
    (icb 15 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have p17 := pst (l17 M2 P c4 d13 b1 t N B (i.add 1) (mixF (addF 1 (d12.land 255) 87 0).2 (addF 4 i 1 0).2 2260)
    (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) s2)
    (icb 16 (by omega)) (tf_efl _) (neHalt _ (by decide))
  refine ⟨c4, d13, b1, _, (p1.append (p2.append (p3.append (p4.append (p5.append (p6.append (p7.append
    (p8.append (p9.append (p10.append (p11.append (p12.append (p13.append (p14.append (p15.append
    (p16.append p17)))))))))))))))).cast rfl, ic_chain 17 (by omega)⟩

/-! ## The loop invariant -/

/-- The memory `H` at the loop head: the first `k` bytes from `P` are those of `hex x`, all others
those of `M0` (the memory at the loop entry). -/
def HexOk (M0 H : ByteArray) (P : UInt32) (x : List UInt8) (k : Nat) : Prop :=
  H.size = M0.size ∧ ∀ j, j < M0.size →
    H.get! j = if P.toNat ≤ j ∧ j < P.toNat + k then (hex x).getD (j - P.toNat) 0 else M0.get! j

/-- The loop invariant at the loop head after `i` iterations. -/
def Inv (M0 : ByteArray) (P t N B : UInt32) (x : List UInt8) (i : Nat) (m : Machine) : Prop :=
  ∃ (H : SMem) (c d b F : UInt32) (ic : UInt64),
    m = St.m ⟨H.get, P, c, d, b, t, N, B, i.toUInt32, 0x100030, efl F, ic⟩ ∧ ic.toNat ≤ 21 + 18 * i ∧
    HexOk M0 H.get P x (2 * i)

/-- What the loop needs of the call: the input `x` at `B` (its `n` bytes in `M0`), the output
buffer of `2n` bytes at `P` apart from it and from the image. -/
structure Facts (M0 : ByteArray) (P B : UInt32) (n : Nat) (x : List UInt8) : Prop where
  hsz : M0.size ≤ 4273995776
  hn : n < 1073741824
  hlen : x.length = n
  hBs : B.toNat + n ≤ M0.size
  hBi : B.toNat + n ≤ 0x100000 ∨ 0x100000 + 3560 ≤ B.toNat
  hPs : P.toNat + 2 * n < M0.size
  hPi : P.toNat + 2 * n < 0x100000 ∨ 0x100000 + 3560 ≤ P.toNat
  hPB : P.toNat + 2 * n ≤ B.toNat ∨ B.toNat + n ≤ P.toNat
  hx : ∀ k, k < n → M0.get! (B.toNat + k) = x.getD k 0

set_option maxHeartbeats 0 in
/-- An iteration up to the branch: two more digits. -/
theorem iter (M0 : ByteArray) (P t B : UInt32) (n : Nat) (x : List UInt8) (hF : Facts M0 P B n x)
    (i : Nat) (m : Machine) (hi : i < n) (hI : Inv M0 P t n.toUInt32 B x i m) :
    ∃ (H : SMem) (c d b : UInt32) (ic : UInt64), PRun img bodyPath m
      (St.m ⟨H.get, P, c, d, b, t, n.toUInt32, B, (i + 1).toUInt32, 0x100070,
        efl (subF 4 n.toUInt32 (i + 1).toUInt32 0).2, ic⟩) ∧
      ic.toNat ≤ 21 + 18 * i + 17 ∧ HexOk M0 H.get P x (2 * (i + 1)) := by
  obtain ⟨H, c, d, b, F, ic, rfl, hic, hs, hB⟩ := hI
  have hn := hF.hn
  have hPs := hF.hPs
  have hM := hF.hsz
  have hiN : i.toUInt32.toNat = i := toNat_toUInt32 (by omega)
  have hnN : n.toUInt32.toNat = n := toNat_toUInt32 (by omega)
  have hii : (i.toUInt32.add i.toUInt32).toNat = 2 * i := by
    rw [u32_toNat_add (by rw [hiN]; omega), hiN]; omega
  have ha1 : (P.add (i.toUInt32.add i.toUInt32)).toNat = P.toNat + 2 * i := by
    rw [u32_toNat_add (by rw [hii]; omega), hii]
  have ha2 : ((P.add (i.toUInt32.add i.toUInt32)).add 1).toNat = P.toNat + 2 * i + 1 := by
    rw [u32_toNat_add (by rw [ha1]; simp; omega), ha1]; simp
  have hBi' : (B.add i.toUInt32).toNat = B.toNat + i := by
    rw [u32_toNat_add (by rw [hiN]; have := hF.hBs; omega), hiN]
  have hsz : H.get.size ≤ 4273995776 := by rw [hs]; exact hM
  have ok1 : StoreOk1 Image.base Image.size H.mem (P.add (i.toUInt32.add i.toUInt32)) := by
    refine ⟨by show _ < H.get.size; rw [ha1, hs]; omega, ?_⟩
    rw [ha1]; have := hF.hPi; simp only [Image.base, Image.size, UInt32.reduceToNat]; omega
  have ok2 : StoreOk1 Image.base Image.size (CodeMem.wr1 H (P.add (i.toUInt32.add i.toUInt32))
      (hiOf (rdRaw H.get (B.add i.toUInt32) 1)) ok1).mem ((P.add (i.toUInt32.add i.toUInt32)).add 1) := by
    refine ⟨by show _ < (CodeMem.wr1 H _ _ ok1).get.size; rw [wr1_get_size, ha2, hs]; omega, ?_⟩
    rw [ha2]; have := hF.hPi; simp only [Image.base, Image.size, UInt32.reduceToNat]; omega
  obtain ⟨c', d', b', ic', hp, hic'⟩ := body H P c d b t n.toUInt32 B i.toUInt32 F ic hsz
    (by rw [hiN, hnN]; exact hi) (by rw [hnN]; exact hn) (by rw [hnN, hs]; exact hF.hBs)
    (by rw [hnN]; exact hF.hBi) (by rw [hnN, hs]; exact hPs) (by rw [hnN]; exact hF.hPi) ok1 ok2 (by omega)
  rw [succ_toUInt32] at hp
  refine ⟨_, c', d', b', ic', hp, by omega, ?_⟩
  -- the byte loaded is `x[i]`
  have hv : rdRaw H.get (B.add i.toUInt32) 1 = (x.getD i 0).toUInt32 := by
    show rdBytes H.get (B.add i.toUInt32) 1 = _
    have hlt : (B.add i.toUInt32).toNat < H.get.size := by rw [hBi', hs]; have := hF.hBs; omega
    rw [rdBytes1_eq hlt, memByte_def hlt, hBi', hB _ (by have := hF.hBs; omega),
      if_neg (by have := hF.hPB; omega), hF.hx i hi]
  have hlen := hF.hlen
  refine ⟨by rw [wr1_get_size, wr1_get_size, hs], fun j hj => ?_⟩
  have h1 : (P.add (i.toUInt32.add i.toUInt32)).toNat < H.get.size := by rw [ha1, hs]; omega
  have h2 : ((P.add (i.toUInt32.add i.toUInt32)).add 1).toNat <
      (wrBytes H.get (P.add (i.toUInt32.add i.toUInt32)) 1 (hiOf (rdRaw H.get (B.add i.toUInt32) 1))).size := by
    rw [size_wrBytes1 h1, ha2, hs]; omega
  show (wrBytes (wrBytes H.get (P.add (i.toUInt32.add i.toUInt32)) 1 (hiOf (rdRaw H.get (B.add i.toUInt32) 1)))
    ((P.add (i.toUInt32.add i.toUInt32)).add 1) 1 (loOf (rdRaw H.get (B.add i.toUInt32) 1))).get! j = _
  rw [get!_wrBytes1 h2, get!_wrBytes1 h1, hB j hj, ha1, ha2, hv]
  by_cases e2 : j = P.toNat + 2 * i + 1
  · rw [if_pos e2, if_pos (by omega), show j - P.toNat = 2 * i + 1 by omega, hex_getD_lo x i (by omega),
      loOf_spec]
  · rw [if_neg e2]
    by_cases e1 : j = P.toNat + 2 * i
    · rw [if_pos e1, if_pos (by omega), show j - P.toNat = 2 * i by omega, hex_getD_hi x i (by omega),
        hiOf_spec]
    · rw [if_neg e1]
      by_cases hin : P.toNat ≤ j ∧ j < P.toNat + 2 * i
      · rw [if_pos hin, if_pos (by omega)]
      · rw [if_neg hin, if_neg (by omega)]

/-- One iteration that goes back to the loop head. -/
theorem loop_step (M0 : ByteArray) (P t B : UInt32) (n : Nat) (x : List UInt8) (hF : Facts M0 P B n x)
    (i : Nat) (m : Machine) (hi : i + 1 < n) (hI : Inv M0 P t n.toUInt32 B x i m) :
    ∃ m', PRun img iterPath m m' ∧ Inv M0 P t n.toUInt32 B x (i + 1) m' := by
  obtain ⟨H, c, d, b, ic, hp, hic, hB⟩ := iter M0 P t B n x hF i m (by omega) hI
  have hn := hF.hn
  have hsz : H.get.size ≤ 4273995776 := by rw [hB.1]; exact hF.hsz
  have hne : n.toUInt32.toNat ≠ (i + 1).toUInt32.toNat := by
    rw [toNat_toUInt32 (by omega), toNat_toUInt32 (by omega)]; omega
  have pj := pst (l18b H P c d b t n.toUInt32 B (i + 1).toUInt32 0 ic hsz hne) (by omega) (tf_efl _)
    (neHalt _ (by decide))
  exact ⟨_, hp.append pj, H, c, d, b, _, ic + 1, rfl, by rw [u64_succ_toNat (by omega)]; omega, hB⟩

/-- The last iteration, to the end of the loop. -/
theorem loop_last (M0 : ByteArray) (P t B : UInt32) (n : Nat) (x : List UInt8) (hF : Facts M0 P B n x)
    (m : Machine) (hn0 : 0 < n) (hI : Inv M0 P t n.toUInt32 B x (n - 1) m) :
    ∃ (H : SMem) (c d b : UInt32) (ic : UInt64), PRun img iterPath m
      (St.m ⟨H.get, P, c, d, b, t, n.toUInt32, B, n.toUInt32, 0x100072,
        efl (subF 4 n.toUInt32 n.toUInt32 0).2, ic⟩) ∧
      ic.toNat ≤ 21 + 18 * n ∧ HexOk M0 H.get P x (2 * n) := by
  obtain ⟨H, c, d, b, ic, hp, hic, hB⟩ := iter M0 P t B n x hF (n - 1) m (by omega) hI
  rw [Nat.sub_add_cancel hn0] at hp hB
  have hn := hF.hn
  have hsz : H.get.size ≤ 4273995776 := by rw [hB.1]; exact hF.hsz
  have pj := pst (l18o H P c d b t n.toUInt32 B n.toUInt32 0 ic hsz rfl) (by omega) (tf_efl _)
    (neHalt _ (by decide))
  exact ⟨H, c, d, b, ic + 1, hp.append pj, by rw [u64_succ_toNat (by omega)]; omega, hB⟩

end Sodium.Proofs.HexEnc
