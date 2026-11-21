import Sodium.Proofs.MemcmpSteps
import Sodium.Proofs.MemcmpSpec
import Sodium.Proofs.Memzero
import Solutions.Logic.Path
/-!
# `memcmp_correct` and `memcmp_constant_time`

The run of `sodium_memcmp` (`MemcmpSteps`) follows a path of instruction addresses that depends only
on the length (`path`): the prologue, one eight-instruction path per byte, the epilogue. Along it
the accumulator byte at `t + 3` is the OR of the XORs of the bytes compared so far
(`MemcmpSpec.acc`), and the result is 0 exactly when it is 0. `run` gives both the path and the
outcome; correctness and constant time follow from it.
-/
namespace Sodium.Proofs.Memcmp
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Sodium.Proofs Sodium.Utils
set_option maxHeartbeats 1000000

open Sodium.Proofs.Memzero (running_of_eip neHalt tf_efl u64_succ_toNat u64_lt_max toNat_toUInt32
  succ_toUInt32 u32_toNat_sub u32_toNat_add img_size img_base toNat_padd)

/-! ## Paths -/

def iterPath : List UInt32 :=
  [0x100C60, 0x100C64, 0x100C68, 0x100C6C, 0x100C6F, 0x100C73, 0x100C74, 0x100C76]

def exitPath : List UInt32 :=
  [0x100C78, 0x100C7D, 0x100C7E, 0x100C80, 0x100C84, 0x100C87, 0x100C8A, 0x100C8B]

/-- The instruction addresses of a call on `n` bytes. -/
def path (n : Nat) : List UInt32 :=
  if n = 0 then zeroPath else prePath ++ (List.replicate (n - 1) iterPath).flatten ++ iterPath ++ exitPath

/-- A step proved through `execInstr`, along its address. -/
theorem pstep (s s' : St) (hic : s.ic.toNat + 1 < 2 ^ 64) (hTF : s.fl &&& Flag.TF = 0)
    (hx : okState (execInstr s.m) = some s'.m) (hic' : s'.ic = s.ic) (he : s.eip ≠ Image.sym_halt) :
    PRun img [s.eip] s.m { s' with ic := s.ic + 1 }.m :=
  prun_step img s s' (u64_lt_max hic) hTF hx hic' (running_of_eip s he)

/-- `pstep` with the states written out field by field (so that runs compose by syntactic matching,
not by unfolding structure updates). -/
theorem pstep2 {mem mem' : ByteArray} {eax ecx edx ebx esp ebp esi edi eip fl eax' ecx' edx' ebx' esp' ebp' esi'
      edi' eip' fl' : UInt32} {ic : UInt64} (hic : ic.toNat + 1 < 2 ^ 64) (hTF : fl &&& Flag.TF = 0)
    (hx : okState (execInstr (St.m ⟨mem, eax, ecx, edx, ebx, esp, ebp, esi, edi, eip, fl, ic⟩)) =
      some (St.m ⟨mem', eax', ecx', edx', ebx', esp', ebp', esi', edi', eip', fl', ic⟩))
    (he : eip ≠ Image.sym_halt) :
    PRun img [eip] (St.m ⟨mem, eax, ecx, edx, ebx, esp, ebp, esi, edi, eip, fl, ic⟩)
      (St.m ⟨mem', eax', ecx', edx', ebx', esp', ebp', esi', edi', eip', fl', ic + 1⟩) :=
  pstep _ _ hic hTF hx rfl he

/-- The OR-accumulation of one byte pair. -/
theorem orxor_byte (v a b : UInt32) :
    (UInt32.lor v.toUInt8.toUInt32 (UInt32.land (UInt32.lor (UInt32.land a 4294967040)
      (UInt32.land (UInt32.xor (UInt32.land a 255) b) 255)) 255)).toUInt8
      = v.toUInt8 ||| (a.toUInt8 ^^^ b.toUInt8) := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  show (UInt32.toUInt8 (v.toUInt8.toUInt32 ||| ((a &&& 4294967040 ||| ((a &&& 255 ^^^ b) &&& 255)) &&& 255))).toBitVec.getLsbD i = _
  simp only [UInt32.toBitVec_toUInt8, UInt8.toBitVec_toUInt32, UInt32.toBitVec_or, UInt32.toBitVec_and,
    UInt32.toBitVec_xor, UInt8.toBitVec_or, UInt8.toBitVec_xor, BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_xor, hi, decide_true, Bool.true_and]
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-! ## One iteration -/

/-- The value the iteration stores. -/
def stored (G : SMem) (A B w i : UInt32) : UInt32 :=
  w.toUInt8.toUInt32.lor
    ((((rdRaw G.get (A.add i) 1).land 4294967040).lor
      ((((rdRaw G.get (A.add i) 1).land 255).xor (rdRaw G.get (B.add i) 1)).land 255)).land 255)

/-- The first seven instructions of an iteration. -/
theorem iter7 (G : SMem) (e A B w N i edx ebx esi ebp edi F t : UInt32) (ic : UInt64)
    (ok0 : StoreOk Image.base Image.size G.mem (t.add 12))
    (okA : StoreOk Image.base Image.size (CodeMem.wr4 G (t.add 12) e ok0).mem (t.add 8))
    (okB : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 G (t.add 12) e ok0) (t.add 8) A okA).mem
      (t.add 4))
    (ok : StoreOk1 Image.base Image.size (Fr G t e A B ok0 okA okB).mem (t.add 3))
    (ok' : StoreOk1 Image.base Image.size (CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).mem (t.add 3))
    (hsz : G.get.size ≤ 4273995776) (hst : t.toNat + 32 ≤ G.get.size) (hap : StackApart t)
    (hi : i.toNat < N.toNat) (hAs : A.toNat + N.toNat ≤ G.get.size)
    (hAa : A.toNat + N.toNat ≤ t.toNat ∨ t.toNat + 32 ≤ A.toNat)
    (hAi : A.toNat + N.toNat ≤ 0x100000 ∨ 0x100000 + 3560 ≤ A.toNat)
    (hBs : B.toNat + N.toNat ≤ G.get.size)
    (hBa : B.toNat + N.toNat ≤ t.toNat ∨ t.toNat + 32 ≤ B.toNat)
    (hBi : B.toNat + N.toNat ≤ 0x100000 ∨ 0x100000 + 3560 ≤ B.toNat)
    (hic : ic.toNat + 8 < 2 ^ 64) :
    PRun img [0x100C60, 0x100C64, 0x100C68, 0x100C6C, 0x100C6F, 0x100C73, 0x100C74]
      (St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).get, N, i, edx, ebx, t, ebp, esi, edi,
        0x100C60, efl F, ic⟩)
      (St.m ⟨(CodeMem.wr1 (CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok) (t.add 3)
          (stored G A B w i) ok').get, N, i.add 1,
        ((rdRaw G.get (A.add i) 1).land 4294967040).lor
          ((((rdRaw G.get (A.add i) 1).land 255).xor (rdRaw G.get (B.add i) 1)).land 255),
        ebx, t, ebp, B, edi, 0x100C76, efl (subF 4 N (i.add 1) 0).2, ic + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩) := by
  have e1 : (ic + 1).toNat = ic.toNat + 1 := u64_succ_toNat (by omega)
  have e2 : (ic + 1 + 1).toNat = ic.toNat + 2 := by rw [u64_succ_toNat (by omega), e1]
  have e3 : (ic + 1 + 1 + 1).toNat = ic.toNat + 3 := by rw [u64_succ_toNat (by omega), e2]
  have e4 : (ic + 1 + 1 + 1 + 1).toNat = ic.toNat + 4 := by rw [u64_succ_toNat (by omega), e3]
  have e5 : (ic + 1 + 1 + 1 + 1 + 1).toNat = ic.toNat + 5 := by rw [u64_succ_toNat (by omega), e4]
  have e6 : (ic + 1 + 1 + 1 + 1 + 1 + 1).toNat = ic.toNat + 6 := by rw [u64_succ_toNat (by omega), e5]
  have hsz1 : (CodeMem.wr1 (CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok) (t.add 3)
      (stored G A B w i) ok').get.size ≤ 4273995776 := by
    rw [wr1_get_size, wr1_get_size]; unfold Fr; rw [wr4_get_size, wr4_get_size, wr4_get_size]; exact hsz
  have p1 := pstep2 (show ic.toNat + 1 < 2 ^ 64 by omega) (tf_efl F)
    (ex_ldA (G := G) (e := e) (A := A) (B := B) (w := w) (N := N) (i := i) (ebx := ebx) (edx := edx) (esi := esi)
      (ebp := ebp) (edi := edi) (F := F) (t := t) (ic := ic) (ok0 := ok0) (okA := okA) (okB := okB) (ok := ok)
      hsz hst hap) (neHalt 0x100C60 (by decide))
  have p2 := pstep2 (show (ic + 1).toNat + 1 < 2 ^ 64 by omega) (tf_efl F)
    (ex_ldbyteA (G := G) (e := e) (A := A) (B := B) (w := w) (N := N) (i := i) (ebx := ebx) (esi := esi)
      (ebp := ebp) (edi := edi) (F := F) (t := t) (ic := ic + 1) (ok0 := ok0) (okA := okA) (okB := okB) (ok := ok)
      hsz hst hap hi hAs hAa hAi) (neHalt 0x100C64 (by decide))
  have p3 := pstep2 (show (ic + 1 + 1).toNat + 1 < 2 ^ 64 by omega) (tf_efl F)
    (ex_ldB (G := G) (e := e) (A := A) (B := B) (w := w) (N := N) (i := i) (a := rdRaw G.get (A.add i) 1)
      (ebx := ebx) (esi := esi) (ebp := ebp) (edi := edi) (F := F) (t := t) (ic := ic + 1 + 1) (ok0 := ok0)
      (okA := okA) (okB := okB) (ok := ok) hsz hst hap) (neHalt 0x100C68 (by decide))
  have p4 := pstep2 (show (ic + 1 + 1 + 1).toNat + 1 < 2 ^ 64 by omega) (tf_efl F)
    (ex_xorB (G := G) (e := e) (A := A) (B := B) (w := w) (N := N) (i := i) (a := rdRaw G.get (A.add i) 1)
      (ebx := ebx) (ebp := ebp) (edi := edi) (F := F) (t := t) (ic := ic + 1 + 1 + 1) (ok0 := ok0)
      (okA := okA) (okB := okB) (ok := ok) hsz hst hap hi hBs hBa hBi) (neHalt 0x100C6C (by decide))
  have p5 := pstep2 (show (ic + 1 + 1 + 1 + 1).toNat + 1 < 2 ^ 64 by omega) (tf_efl _)
    (ex_or (G := G) (e := e) (A := A) (B := B) (w := w) (N := N) (i := i)
      (d := ((rdRaw G.get (A.add i) 1).land 4294967040).lor
          ((((rdRaw G.get (A.add i) 1).land 255).xor (rdRaw G.get (B.add i) 1)).land 255))
      (ebx := ebx) (ebp := ebp) (edi := edi)
      (F := (logicF 1 (((rdRaw G.get (A.add i) 1).land 255).xor (rdRaw G.get (B.add i) 1))).2) (t := t)
      (ic := ic + 1 + 1 + 1 + 1) (ok0 := ok0) (okA := okA) (okB := okB) (ok := ok) hsz hst hap ok')
    (neHalt 0x100C6F (by decide))
  have p6 := pstep2 (show (ic + 1 + 1 + 1 + 1 + 1).toNat + 1 < 2 ^ 64 by omega) (tf_efl _)
    (ex_inc (M := CodeMem.wr1 (CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok) (t.add 3)
        (stored G A B w i) ok') (N := N) (i := i)
      (d := ((rdRaw G.get (A.add i) 1).land 4294967040).lor
          ((((rdRaw G.get (A.add i) 1).land 255).xor (rdRaw G.get (B.add i) 1)).land 255))
      (ebx := ebx) (t := t) (ebp := ebp) (esi := B) (edi := edi) (F := (logicF 1 (stored G A B w i)).2)
      (ic := ic + 1 + 1 + 1 + 1 + 1) (hsz := hsz1))
    (neHalt 0x100C73 (by decide))
  have p7 := pstep2 (show (ic + 1 + 1 + 1 + 1 + 1 + 1).toNat + 1 < 2 ^ 64 by omega) (tf_efl _)
    (ex_cmp (M := CodeMem.wr1 (CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok) (t.add 3)
        (stored G A B w i) ok') (N := N) (i := i.add 1)
      (d := ((rdRaw G.get (A.add i) 1).land 4294967040).lor
          ((((rdRaw G.get (A.add i) 1).land 255).xor (rdRaw G.get (B.add i) 1)).land 255))
      (ebx := ebx) (t := t) (ebp := ebp) (esi := B) (edi := edi)
      (F := mixF (logicF 1 (stored G A B w i)).2 (addF 4 i 1 0).2 2260) (ic := ic + 1 + 1 + 1 + 1 + 1 + 1) (hsz := hsz1))
    (neHalt 0x100C74 (by decide))
  exact p1.append (p2.append (p3.append (p4.append (p5.append (p6.append p7)))))

/-! ## The loop -/

theorem storeOk1_again (L : SMem) (a v : UInt32) (ok : StoreOk1 Image.base Image.size L.mem a) :
    StoreOk1 Image.base Image.size (CodeMem.wr1 L a v ok).mem a :=
  ⟨by show a.toNat < (CodeMem.wr1 L a v ok).get.size; rw [wr1_get_size]; exact ok.1, ok.2⟩

/-- The loop invariant at the loop head after `i` iterations. -/
def Inv (G : SMem) (t e A B N ebx ebp edi : UInt32) (ok0 : StoreOk Image.base Image.size G.mem (t.add 12))
    (okA : StoreOk Image.base Image.size (CodeMem.wr4 G (t.add 12) e ok0).mem (t.add 8))
    (okB : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 G (t.add 12) e ok0) (t.add 8) A okA).mem
      (t.add 4))
    (ok : StoreOk1 Image.base Image.size (Fr G t e A B ok0 okA okB).mem (t.add 3)) (a b : List UInt8)
    (i : Nat) (m : Machine) : Prop :=
  ∃ (w F edx esi : UInt32) (ic : UInt64),
    m = St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).get, N, i.toUInt32, edx, ebx, t, ebp, esi,
      edi, 0x100C60, efl F, ic⟩ ∧ ic.toNat ≤ 24 + 8 * i ∧ w.toUInt8 = acc a b i

/-- The facts about the call the loop needs. -/
structure Facts (G : SMem) (t A B : UInt32) (n : Nat) (a b : List UInt8) : Prop where
  hsz : G.get.size ≤ 4273995776
  hst : t.toNat + 32 ≤ G.get.size
  hap : StackApart t
  hn : n < 2 ^ 31
  hAs : A.toNat + n ≤ G.get.size
  hAa : A.toNat + n ≤ t.toNat - 112 ∨ t.toNat + 32 ≤ A.toNat
  hAi : A.toNat + n ≤ 0x100000 ∨ 0x100000 + 3560 ≤ A.toNat
  hBs : B.toNat + n ≤ G.get.size
  hBa : B.toNat + n ≤ t.toNat - 112 ∨ t.toNat + 32 ≤ B.toNat
  hBi : B.toNat + n ≤ 0x100000 ∨ 0x100000 + 3560 ≤ B.toNat
  ha : ∀ k, k < n → (rdRaw G.get (A.add k.toUInt32) 1).toUInt8 = a.getD k 0
  hb : ∀ k, k < n → (rdRaw G.get (B.add k.toUInt32) 1).toUInt8 = b.getD k 0

theorem stored_acc (G : SMem) (A B w : UInt32) (a b : List UInt8) (n i : Nat) (hF : Facts G t A B n a b)
    (hi : i < n) (hw : w.toUInt8 = acc a b i) : (stored G A B w i.toUInt32).toUInt8 = acc a b (i + 1) := by
  unfold stored
  rw [orxor_byte, hw, hF.ha i hi, hF.hb i hi, acc_succ]


theorem ic_chain {ic : UInt64} (k : Nat) (h : ic.toNat + k < 2 ^ 64) :
    (Nat.rec ic (fun _ x => x + 1) k : UInt64).toNat = ic.toNat + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show ((Nat.rec ic (fun _ x => x + 1) k : UInt64) + 1).toNat = _
    rw [u64_succ_toNat (by rw [ih (by omega)]; omega), ih (by omega)]; omega

/-- One iteration that goes back to the loop head. -/
theorem loop_step (G : SMem) (t e A B ebx ebp edi : UInt32) (n : Nat) (a b : List UInt8)
    (ok0 : StoreOk Image.base Image.size G.mem (t.add 12))
    (okA : StoreOk Image.base Image.size (CodeMem.wr4 G (t.add 12) e ok0).mem (t.add 8))
    (okB : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 G (t.add 12) e ok0) (t.add 8) A okA).mem
      (t.add 4))
    (ok : StoreOk1 Image.base Image.size (Fr G t e A B ok0 okA okB).mem (t.add 3))
    (hF : Facts G t A B n a b) (i : Nat) (m : Machine) (hi : i + 1 < n)
    (hI : Inv G t e A B n.toUInt32 ebx ebp edi ok0 okA okB ok a b i m) :
    ∃ m', PRun img iterPath m m' ∧ Inv G t e A B n.toUInt32 ebx ebp edi ok0 okA okB ok a b (i + 1) m' := by
  obtain ⟨w, F, edx, esi, ic, rfl, hic, hw⟩ := hI
  have hn := hF.hn
  have hiN : i.toUInt32.toNat = i := toNat_toUInt32 (by omega)
  have hnN : n.toUInt32.toNat = n := toNat_toUInt32 (by omega)
  have hi1 : (i.toUInt32.add 1).toNat = i + 1 := by rw [succ_toUInt32, toNat_toUInt32 (by omega)]
  have ok' := storeOk1_again (Fr G t e A B ok0 okA okB) (t.add 3) w ok
  have hAs := hF.hAs; have hAa := hF.hAa; have hAi := hF.hAi
  have hBs := hF.hBs; have hBa := hF.hBa; have hBi := hF.hBi
  have p := iter7 G e A B w n.toUInt32 i.toUInt32 edx ebx esi ebp edi F t ic ok0 okA okB ok ok' hF.hsz hF.hst
    hF.hap (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have e7 : (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat = ic.toNat + 7 := ic_chain 7 (by omega)
  have hsz1 : (CodeMem.wr1 (CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok) (t.add 3)
      (stored G A B w i.toUInt32) ok').get.size ≤ 4273995776 := by
    rw [wr1_get_size, wr1_get_size]; unfold Fr; rw [wr4_get_size, wr4_get_size, wr4_get_size]; exact hF.hsz
  have p8 := pstep2 (show (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat + 1 < 2 ^ 64 by omega) (tf_efl _)
    (ex_jne_back (CodeMem.wr1 (CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok) (t.add 3)
      (stored G A B w i.toUInt32) ok') n.toUInt32 (i.toUInt32.add 1)
      (((rdRaw G.get (A.add i.toUInt32) 1).land 4294967040).lor
        ((((rdRaw G.get (A.add i.toUInt32) 1).land 255).xor (rdRaw G.get (B.add i.toUInt32) 1)).land 255)) ebx t ebp B edi
      (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1) hsz1 (by omega)) (neHalt 0x100C76 (by decide))
  have hrun : PRun img iterPath
      (St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).get, n.toUInt32, i.toUInt32, edx, ebx, t, ebp,
        esi, edi, 0x100C60, efl F, ic⟩)
      (St.m ⟨(CodeMem.wr1 (CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok) (t.add 3)
          (stored G A B w i.toUInt32) ok').get, n.toUInt32, i.toUInt32.add 1,
        ((rdRaw G.get (A.add i.toUInt32) 1).land 4294967040).lor
          ((((rdRaw G.get (A.add i.toUInt32) 1).land 255).xor (rdRaw G.get (B.add i.toUInt32) 1)).land 255),
        ebx, t, ebp, B, edi, 0x100C60, efl (subF 4 n.toUInt32 (i.toUInt32.add 1) 0).2,
        ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩) := (p.append p8).cast rfl
  rw [wr1_wr1, succ_toUInt32] at hrun
  refine ⟨_, hrun, stored G A B w i.toUInt32, _, _, B, ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1, rfl, ?_, ?_⟩
  · have e8 : (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat = ic.toNat + 8 := ic_chain 8 (by omega)
    rw [e8]; omega
  · exact stored_acc G A B w a b n i hF (by omega) hw

/-- The result of the epilogue from the accumulator `x`. -/
noncomputable def eaxOf (x : UInt32) : UInt32 :=
  (addF 4 0 4294967295
    (if Bool.rec true false (decide ((mixF (logicF 4 0).2
        (if Bool.rec true false (decide (((x.add 4294967295).shiftRight 8).land 1 = 0)) = true then Flag.CF else 0)
        1).land 1 = 0)) = true then 1 else 0)).1

theorem eaxOf_fin : ∀ k : Fin 256, eaxOf k.val.toUInt8.toUInt32 = if k.val.toUInt8 = 0 then 0 else 0xFFFFFFFF := by
  decide +kernel

theorem eaxZ_fin : ∀ k : Fin 256, eaxZ k.val.toUInt8.toUInt32 = if k.val.toUInt8 = 0 then 0 else 0xFFFFFFFF := by
  decide +kernel

theorem eaxOf_spec (d : UInt8) : eaxOf d.toUInt32 = if d = 0 then 0 else 0xFFFFFFFF := by
  have h := eaxOf_fin ⟨d.toNat, d.toNat_lt⟩
  simpa using h

theorem eaxZ_zero : eaxZ 0 = 0 := by decide +kernel


/-- The last iteration and the epilogue. -/
theorem loop_last (G : SMem) (t e A B ebx ebp edi : UInt32) (n : Nat) (a b : List UInt8)
    (ok0 : StoreOk Image.base Image.size G.mem (t.add 12))
    (okA : StoreOk Image.base Image.size (CodeMem.wr4 G (t.add 12) e ok0).mem (t.add 8))
    (okB : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 G (t.add 12) e ok0) (t.add 8) A okA).mem
      (t.add 4))
    (ok : StoreOk1 Image.base Image.size (Fr G t e A B ok0 okA okB).mem (t.add 3))
    (hF : Facts G t A B n a b) (m : Machine) (hn0 : 0 < n)
    (hI : Inv G t e A B n.toUInt32 ebx ebp edi ok0 okA okB ok a b (n - 1) m) :
    ∃ (W ecx edx F : UInt32) (ic : UInt64), PRun img (iterPath ++ exitPath) m
      (St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) W ok).get, eaxOf W.toUInt8.toUInt32, ecx, edx, ebx,
        t.add 20, ebp, e, edi, rdRaw G.get (t.add 16) 4, efl F, ic⟩) ∧ W.toUInt8 = acc a b n := by
  obtain ⟨w, F, edx, esi, ic, rfl, hic, hw⟩ := hI
  have hn := hF.hn
  have hiN : (n - 1).toUInt32.toNat = n - 1 := toNat_toUInt32 (by omega)
  have hnN : n.toUInt32.toNat = n := toNat_toUInt32 (by omega)
  have hi1 : ((n - 1).toUInt32.add 1).toNat = n := by
    rw [succ_toUInt32, toNat_toUInt32 (by omega)]; omega
  have ok' := storeOk1_again (Fr G t e A B ok0 okA okB) (t.add 3) w ok
  have hAs := hF.hAs; have hAa := hF.hAa; have hAi := hF.hAi
  have hBs := hF.hBs; have hBa := hF.hBa; have hBi := hF.hBi
  have p := iter7 G e A B w n.toUInt32 (n - 1).toUInt32 edx ebx esi ebp edi F t ic ok0 okA okB ok ok' hF.hsz
    hF.hst hF.hap (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hic' : ic.toNat + 16 < 2 ^ 64 := by omega
  have e7 : (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat = ic.toNat + 7 := ic_chain 7 (by omega)
  have e8 : (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat = ic.toNat + 8 := ic_chain 8 (by omega)
  have e9 : (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat = ic.toNat + 9 := ic_chain 9 (by omega)
  have e10 : (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat = ic.toNat + 10 := ic_chain 10 (by omega)
  have e11 : (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat = ic.toNat + 11 := ic_chain 11 (by omega)
  have e12 : (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat = ic.toNat + 12 := ic_chain 12 (by omega)
  have e13 : (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat = ic.toNat + 13 := ic_chain 13 (by omega)
  have e14 : (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat = ic.toNat + 14 := ic_chain 14 (by omega)
  have e15 : (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat = ic.toNat + 15 := ic_chain 15 (by omega)
  have e16 : (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat = ic.toNat + 16 := ic_chain 16 (by omega)
  have hsz1 : (CodeMem.wr1 (CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok) (t.add 3)
      (stored G A B w (n - 1).toUInt32) ok').get.size ≤ 4273995776 := by
    rw [wr1_get_size, wr1_get_size]; unfold Fr; rw [wr4_get_size, wr4_get_size, wr4_get_size]; exact hF.hsz
  have p8 := pstep2 (show (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat + 1 < 2 ^ 64 by omega)
    (tf_efl _)
    (ex_jne_out (CodeMem.wr1 (CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok) (t.add 3)
      (stored G A B w (n - 1).toUInt32) ok') n.toUInt32 ((n - 1).toUInt32.add 1)
      (((rdRaw G.get (A.add (n - 1).toUInt32) 1).land 4294967040).lor
        ((((rdRaw G.get (A.add (n - 1).toUInt32) 1).land 255).xor (rdRaw G.get (B.add (n - 1).toUInt32) 1)).land 255)) ebx t ebp B edi
      (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1) hsz1 (by omega)) (neHalt 0x100C76 (by decide))
  have hrun := (p.append p8)
  rw [wr1_wr1] at hrun
  -- the epilogue
  have hszf : (CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) (stored G A B w (n - 1).toUInt32) ok).get.size
      ≤ 4273995776 := by
    rw [wr1_get_size]; unfold Fr; rw [wr4_get_size, wr4_get_size, wr4_get_size]; exact hF.hsz
  let W := stored G A B w (n - 1).toUInt32
  let D := ((rdRaw G.get (A.add (n - 1).toUInt32) 1).land 4294967040).lor
    ((((rdRaw G.get (A.add (n - 1).toUInt32) 1).land 255).xor (rdRaw G.get (B.add (n - 1).toUInt32) 1)).land 255)
  let x := W.toUInt8.toUInt32
  let Mf := CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) W ok
  have q1 := pstep2 (show (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat + 1 < 2 ^ 64 by omega) (tf_efl _)
    (ex_ldacc (G := G) (e := e) (A := A) (B := B) (w := W) (N := n.toUInt32) (i := (n - 1).toUInt32.add 1)
      (d := D) (ebx := ebx) (esi := B) (ebp := ebp) (edi := edi)
      (F := (subF 4 n.toUInt32 ((n - 1).toUInt32.add 1) 0).2) (t := t)
      (ic := ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (ok0 := ok0) (okA := okA) (okB := okB) (ok := ok)
      hF.hsz hF.hst hF.hap) (neHalt 0x100C78 (by decide))
  have q2 := pstep2 (show (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat + 1 < 2 ^ 64 by omega) (tf_efl _)
    (ex_dec (M := Mf) (N := n.toUInt32) (i := x) (d := D) (ebx := ebx) (t := t) (ebp := ebp) (esi := B)
      (edi := edi) (F := (subF 4 n.toUInt32 ((n - 1).toUInt32.add 1) 0).2)
      (ic := ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) hszf) (neHalt 0x100C7D (by decide))
  have q3 := pstep2 (show (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat + 1 < 2 ^ 64 by omega) (tf_efl _)
    (ex_xor (M := Mf) (N := n.toUInt32) (i := x.add 4294967295) (d := D) (ebx := ebx) (t := t) (ebp := ebp)
      (esi := B) (edi := edi) (F := mixF (subF 4 n.toUInt32 ((n - 1).toUInt32.add 1) 0).2 (subF 4 x 1 0).2 2260)
      (ic := ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) hszf) (neHalt 0x100C7E (by decide))
  have q4 := pstep2 (show (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat + 1 < 2 ^ 64 by omega)
    (tf_efl _)
    (ex_bt (M := Mf) (N := 0) (i := x.add 4294967295) (d := D) (ebx := ebx) (t := t) (ebp := ebp)
      (esi := B) (edi := edi) (F := (logicF 4 0).2)
      (ic := ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) hszf) (neHalt 0x100C80 (by decide))
  have q5 := pstep2 (show (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat + 1 < 2 ^ 64 by omega)
    (tf_efl _)
    (ex_adc (M := Mf) (N := 0) (i := x.add 4294967295) (d := D) (ebx := ebx) (t := t) (ebp := ebp)
      (esi := B) (edi := edi)
      (F := mixF (logicF 4 0).2
        (if Bool.rec true false (decide (((x.add 4294967295).shiftRight 8).land 1 = 0)) = true then Flag.CF else 0) 1)
      (ic := ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) hszf) (neHalt 0x100C84 (by decide))
  have q6 := pstep2 (show (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat + 1 < 2 ^ 64 by omega)
    (tf_efl _)
    (ex_add (G := G) (e := e) (A := A) (B := B) (w := W) (N := eaxOf x) (i := x.add 4294967295) (d := D)
      (ebx := ebx) (esi := B) (ebp := ebp) (edi := edi)
      (F := (addF 4 0 4294967295 (if Bool.rec true false (decide ((mixF (logicF 4 0).2
        (if Bool.rec true false (decide (((x.add 4294967295).shiftRight 8).land 1 = 0)) = true then Flag.CF else 0)
        1).land 1 = 0)) = true then 1 else 0)).2) (t := t)
      (ic := ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (ok0 := ok0) (okA := okA) (okB := okB)
      (ok := ok) hF.hsz hF.hst hF.hap) (neHalt 0x100C87 (by decide))
  have q7 := pstep2
    (show (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat + 1 < 2 ^ 64 by omega) (tf_efl _)
    (ex_pop (G := G) (e := e) (A := A) (B := B) (w := W) (N := eaxOf x) (i := x.add 4294967295) (d := D)
      (ebx := ebx) (esi := B) (ebp := ebp) (edi := edi) (F := (addF 4 t 12 0).2) (t := t)
      (ic := ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (ok0 := ok0) (okA := okA) (okB := okB)
      (ok := ok) hF.hsz hF.hst hF.hap) (neHalt 0x100C8A (by decide))
  have q8 := pstep2
    (show (ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat + 1 < 2 ^ 64 by omega) (tf_efl _)
    (ex_ret (G := G) (e := e) (A := A) (B := B) (w := W) (N := eaxOf x) (i := x.add 4294967295) (d := D)
      (ebx := ebx) (esi := e) (ebp := ebp) (edi := edi) (F := (addF 4 t 12 0).2) (t := t)
      (ic := ic + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (ok0 := ok0) (okA := okA) (okB := okB)
      (ok := ok) hF.hsz hF.hst hF.hap) (neHalt 0x100C8B (by decide))
  refine ⟨W, x.add 4294967295, D, (addF 4 t 12 0).2, _,
    ((hrun.append (q1.append (q2.append (q3.append (q4.append (q5.append (q6.append (q7.append q8)))))))).cast
      rfl), ?_⟩
  exact stored_acc G A B w a b n (n - 1) hF (by omega) hw |>.trans (by rw [Nat.sub_add_cancel hn0])


/-! ## The call -/

/-- The bytes outside the frame `[t, t + 16)` are those of the caller. -/
theorem frame_byte (G : SMem) (t e A B W : UInt32)
    (ok0 : StoreOk Image.base Image.size G.mem (t.add 12))
    (okA : StoreOk Image.base Image.size (CodeMem.wr4 G (t.add 12) e ok0).mem (t.add 8))
    (okB : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 G (t.add 12) e ok0) (t.add 8) A okA).mem
      (t.add 4))
    (ok : StoreOk1 Image.base Image.size (Fr G t e A B ok0 okA okB).mem (t.add 3))
    (hst : t.toNat + 32 ≤ G.get.size) (hsz : G.get.size ≤ 4273995776) (x : UInt32) (hx : x.toNat < G.get.size)
    (hd : x.toNat < t.toNat ∨ t.toNat + 16 ≤ x.toNat) :
    memByte (CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) W ok).get x = memByte G.get x := by
  have h3 : (t.add 3).toNat = t.toNat + 3 := u32_toNat_add (by simp; omega)
  have h4 : (t.add 4).toNat = t.toNat + 4 := u32_toNat_add (by simp; omega)
  have h8 : (t.add 8).toNat = t.toNat + 8 := u32_toNat_add (by simp; omega)
  have h12 : (t.add 12).toNat = t.toNat + 12 := u32_toNat_add (by simp; omega)
  show memByte (wrBytes (wrBytes (wrBytes (wrBytes G.get (t.add 12) 4 e) (t.add 8) 4 A) (t.add 4) 4 B)
    (t.add 3) 1 W) x = _
  have s1 : (wrBytes G.get (t.add 12) 4 e).size = G.get.size := size_wrBytes4 (by omega)
  have s2 : (wrBytes (wrBytes G.get (t.add 12) 4 e) (t.add 8) 4 A).size = G.get.size := by
    rw [size_wrBytes4 (by omega), s1]
  have s3 : (wrBytes (wrBytes (wrBytes G.get (t.add 12) 4 e) (t.add 8) 4 A) (t.add 4) 4 B).size = G.get.size := by
    rw [size_wrBytes4 (by omega), s2]
  rw [memByte_wrBytes1 (by omega) (by omega), if_neg (fun h => by subst h; omega),
    memByte_wrBytes4_other (by omega) (by omega) (by omega), memByte_wrBytes4_other (by omega) (by omega) (by omega),
    memByte_wrBytes4_other (by omega) (by omega) (by omega)]

theorem frame_size (G : SMem) (t e A B W : UInt32)
    (ok0 : StoreOk Image.base Image.size G.mem (t.add 12))
    (okA : StoreOk Image.base Image.size (CodeMem.wr4 G (t.add 12) e ok0).mem (t.add 8))
    (okB : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 G (t.add 12) e ok0) (t.add 8) A okA).mem
      (t.add 4))
    (ok : StoreOk1 Image.base Image.size (Fr G t e A B ok0 okA okB).mem (t.add 3)) :
    (CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) W ok).get.size = G.get.size := by
  rw [wr1_get_size]; unfold Fr; rw [wr4_get_size, wr4_get_size, wr4_get_size]


theorem toUInt8_byte (x : UInt8) : x.toUInt32.toUInt8 = x := by
  apply UInt8.toNat_inj.1; simp

set_option maxHeartbeats 0 in
/-- A call: its path of instruction addresses, its return, and its result. -/
theorem run (c : Caller) (ap bp : UInt32) (a b : List UInt8) (h : MemcmpPre c ap bp a b) :
    ∃ r, PRun img (path a.length) (c.enter Image.sym_sodium_memcmp) r ∧
      Returned img (c.enter Image.sym_sodium_memcmp) r ∧ CalleeSaved (c.enter Image.sym_sodium_memcmp) r ∧
      Preserved (c.enter Image.sym_sodium_memcmp) r stackBound NoWrites ∧
      r.cpu.eax = (if a = b then 0 else minusOne) := by
  obtain ⟨hc, hbA, hbB, hlen, hma, hmb⟩ := h
  have hsz : c.mem.size ≤ 4273995776 := hc.1
  have hsp : 128 ≤ c.sp.toNat := hc.2.2.2.2.1
  have hsp16 : c.sp.toNat + 16 ≤ c.mem.size := by have := hc.2.2.2.2.2.1; simpa using this
  have hlo : (c.stackLo stackBound).toNat = c.sp.toNat - 128 := u32_toNat_sub hsp (by decide)
  have hap0 : c.sp.toNat - 128 + 144 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ c.sp.toNat - 128 := by
    have h := hc.2.2.2.2.2.2
    unfold Apart at h
    rw [hlo, img_size, img_base] at h
    simp only [stackSize, List.length_cons, List.length_nil, stackBound] at h
    have : Image.base.toNat = 0x100000 := rfl
    omega
  let t : UInt32 := c.sp - (16 : Nat).toUInt32
  have ht : t.toNat = c.sp.toNat - 16 := u32_toNat_sub (by omega) (by decide)
  have hspt : c.sp = t.add 16 := by
    apply UInt32.toNat_inj.1; rw [u32_toNat_add (by simp; omega)]; simp; omega
  let G : SMem := codeMem c hc
  have hG : G.get = c.mem := rfl
  have hst : t.toNat + 32 ≤ G.get.size := by rw [hG]; omega
  have hap : StackApart t := by unfold StackApart; omega
  have hk : ∀ k : Nat, k < 3 → t.add (20 + 4 * k).toUInt32 = c.sp + 4 * (k + 1).toUInt32 := by
    intro k hk3
    apply UInt32.toNat_inj.1
    rw [u32_toNat_add (by simp; omega), UInt32.toNat_add]; simp; omega
  have hA' : rdRaw G.get (t.add 20) 4 = ap := by
    have := hk 0 (by decide); simp at this; rw [this]; exact calls_arg hc 0 (by simp)
  have hB' : rdRaw G.get (t.add 24) 4 = bp := by
    have := hk 1 (by decide); simp at this; rw [this]; exact calls_arg hc 1 (by simp)
  have hN' : rdRaw G.get (t.add 28) 4 = a.length.toUInt32 := by
    have := hk 2 (by decide); simp at this; rw [this]; exact calls_arg hc 2 (by simp)
  have hret : rdRaw G.get (t.add 16) 4 = Image.sym_halt := by rw [← hspt]; exact calls_ret hc
  have h12 : (t.add 12).toNat = t.toNat + 12 := u32_toNat_add (by simp; omega)
  have h8 : (t.add 8).toNat = t.toNat + 8 := u32_toNat_add (by simp; omega)
  have h4 : (t.add 4).toNat = t.toNat + 4 := u32_toNat_add (by simp; omega)
  have h3 : (t.add 3).toNat = t.toNat + 3 := u32_toNat_add (by simp; omega)
  have hbase : (Image.base).toNat = 0x100000 := rfl
  have ok0 : StoreOk Image.base Image.size G.mem (t.add 12) := by
    refine ⟨by show _ ≤ G.get.size; omega, ?_⟩
    simp only [Image.size, hbase, h12]; omega
  have okA : StoreOk Image.base Image.size (CodeMem.wr4 G (t.add 12) c.regs.esi ok0).mem (t.add 8) := by
    refine ⟨by show _ ≤ (CodeMem.wr4 G (t.add 12) c.regs.esi ok0).get.size; rw [wr4_get_size]; omega, ?_⟩
    simp only [Image.size, hbase, h8]; omega
  have okB : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 G (t.add 12) c.regs.esi ok0) (t.add 8)
      (rdRaw G.get (t.add 20) 4) okA).mem (t.add 4) := by
    refine ⟨by show _ ≤ (CodeMem.wr4 (CodeMem.wr4 G (t.add 12) c.regs.esi ok0) (t.add 8)
      (rdRaw G.get (t.add 20) 4) okA).get.size; rw [wr4_get_size, wr4_get_size]; omega, ?_⟩
    simp only [Image.size, hbase, h4]; omega
  have ok3 : StoreOk1 Image.base Image.size (Fr G t c.regs.esi (rdRaw G.get (t.add 20) 4) (rdRaw G.get (t.add 24) 4)
      ok0 okA okB).mem (t.add 3) := by
    refine ⟨by show _ < (Fr G t c.regs.esi _ _ ok0 okA okB).get.size; unfold Fr; rw [wr4_get_size, wr4_get_size, wr4_get_size]; omega, ?_⟩
    simp only [Image.size, hbase, h3]; omega
  have e0 : c.enter Image.sym_sodium_memcmp =
      St.m ⟨G.get, c.regs.eax, c.regs.ecx, c.regs.edx, c.regs.ebx, t.add 16, c.regs.ebp, c.regs.esi,
        c.regs.edi, 0x100C30, efl c.regs.flags, 0⟩ := by
    rw [← hspt]; rfl
  have hesp : (t.add 16) + 4 = t.add 20 := by
    apply UInt32.toNat_inj.1
    rw [UInt32.toNat_add, u32_toNat_add (by simp; omega), u32_toNat_add (by simp; omega)]; simp; omega
  have hstack : ∀ x : UInt32, ¬ InRange (t.add 16 - (stackBound : Nat).toUInt32) stackBound x →
      x.toNat < t.toNat ∨ t.toNat + 16 ≤ x.toNat := by
    intro x hx
    rw [inRange_iff, u32_toNat_sub (by rw [u32_toNat_add (by simp; omega)]; simp [stackBound]; omega) (by decide),
      u32_toNat_add (by simp; omega)] at hx
    simp [stackBound] at hx; omega
  rw [e0]
  rcases Nat.eq_zero_or_pos a.length with hn0 | hn0
  · -- an empty buffer
    have ha0 : a = [] := List.eq_nil_of_length_eq_zero hn0
    have hb0 : b = [] := List.eq_nil_of_length_eq_zero (hlen ▸ hn0)
    have hz : (rdRaw G.get (t.add 28) 4).toNat = 0 := by rw [hN', hn0]; rfl
    have hr := prun_of_runOkP (run_zero G c.regs.eax c.regs.ecx c.regs.edx c.regs.ebx t c.regs.ebp c.regs.esi
      c.regs.edi c.regs.flags hsz hst hap hz ok0 okA okB ok3)
    rw [hret, eaxZ_zero] at hr
    refine ⟨_, hr.cast ?_, ⟨rfl, hesp.symm, efl_DF _⟩, ⟨rfl, rfl, rfl, rfl⟩,
      ⟨frame_size G t c.regs.esi _ _ 0 ok0 okA okB ok3,
        fun x hx _ hs => frame_byte G t c.regs.esi _ _ 0 ok0 okA okB ok3 hst hsz x hx (hstack x hs)⟩, ?_⟩
    · rw [path, if_pos hn0]
    · show (0 : UInt32) = if a = b then 0 else minusOne
      rw [if_pos (by rw [ha0, hb0])]
  · -- the loop
    have hn : a.length < 2 ^ 31 := by have := hbA.2.1; unfold maxObject at this; omega
    have hF : Facts G t (rdRaw G.get (t.add 20) 4) (rdRaw G.get (t.add 24) 4) a.length a b := by
      rw [hA', hB']
      obtain ⟨hfa, -, hia, hsa⟩ := hbA
      obtain ⟨hfb, -, hib, hsb⟩ := hbB
      unfold Fits at hfa hfb
      unfold Apart at hia hsa hib hsb
      rw [img_size, img_base] at hia hib
      rw [hlo] at hsa hsb
      simp only [stackSize, stackBound] at hsa hsb
      rw [← hlen] at hfb hib hsb
      refine ⟨hsz, hst, hap, hn, by rw [hG]; omega, by omega, by omega, by rw [hG]; omega, by omega, by omega,
        fun k hk => ?_, fun k hk => ?_⟩
      · show memByte c.mem (ap + k.toUInt32) = _
        rw [← memBytes_getElem c.mem ap a.length k (by rw [memBytes_length]; exact hk)]
        simp only [hma]
        simp [hk]
      · show memByte c.mem (bp + k.toUInt32) = _
        rw [← memBytes_getElem c.mem bp b.length k (by rw [memBytes_length]; omega)]
        simp only [hmb]
        simp [show k < b.length by omega]
    have hz : 0 < (rdRaw G.get (t.add 28) 4).toNat := by rw [hN', toNat_toUInt32 (by omega)]; exact hn0
    have hr0 := prun_of_runOkP (run_pre G c.regs.eax c.regs.ecx c.regs.edx c.regs.ebx t c.regs.ebp c.regs.esi
      c.regs.edi c.regs.flags hsz hst hap hz ok0 okA okB ok3)
    rw [hN'] at hr0
    have hI0 : Inv G t c.regs.esi (rdRaw G.get (t.add 20) 4) (rdRaw G.get (t.add 24) 4) a.length.toUInt32
        c.regs.ebx c.regs.ebp c.regs.edi ok0 okA okB ok3 a b 0
        (St.m ⟨(CodeMem.wr1 (Fr G t c.regs.esi (rdRaw G.get (t.add 20) 4) (rdRaw G.get (t.add 24) 4) ok0 okA okB)
          (t.add 3) 0 ok3).get, a.length.toUInt32, 0, rdRaw G.get (t.add 20) 4, c.regs.ebx, t, c.regs.ebp,
          c.regs.esi, c.regs.edi, 0x100C60, efl (logicF 4 0).2, 24⟩) :=
      ⟨0, (logicF 4 0).2, rdRaw G.get (t.add 20) 4, c.regs.esi, 24, rfl, by decide, by rw [acc_zero]; rfl⟩
    obtain ⟨m1, hL, hI1⟩ := PRun.loop (img := img) iterPath
      (fun i m => Inv G t c.regs.esi (rdRaw G.get (t.add 20) 4) (rdRaw G.get (t.add 24) 4) a.length.toUInt32
        c.regs.ebx c.regs.ebp c.regs.edi ok0 okA okB ok3 a b i m) (a.length - 1)
      (fun i m hi hI => loop_step G t c.regs.esi _ _ c.regs.ebx c.regs.ebp c.regs.edi a.length a b ok0 okA okB ok3
        hF i m (by omega) hI) hI0
    obtain ⟨W, ecx, edx, F, ic, hE, hW⟩ := loop_last G t c.regs.esi _ _ c.regs.ebx c.regs.ebp c.regs.edi a.length
      a b ok0 okA okB ok3 hF m1 hn0 hI1
    have hrun := hr0.append (hL.append hE)
    rw [hret] at hrun
    refine ⟨_, hrun.cast ?_, ⟨rfl, hesp.symm, efl_DF _⟩, ⟨rfl, rfl, rfl, rfl⟩,
      ⟨frame_size G t c.regs.esi _ _ W ok0 okA okB ok3,
        fun x hx _ hs => frame_byte G t c.regs.esi _ _ W ok0 okA okB ok3 hst hsz x hx (hstack x hs)⟩, ?_⟩
    · rw [path, if_neg (by omega)]
      simp only [List.append_assoc]
    · show eaxOf W.toUInt8.toUInt32 = if a = b then 0 else minusOne
      rw [eaxOf_spec, hW]
      by_cases hab : a = b
      · rw [if_pos ((acc_eq_zero_iff a b hlen).2 hab), if_pos hab]
      · rw [if_neg (fun h => hab ((acc_eq_zero_iff a b hlen).1 h)), if_neg hab]; rfl

theorem _root_.Sodium.Proofs.memcmp_correct : Sodium.Utils.memcmp_correct := by
  intro c ap bp a b h
  obtain ⟨r, hp, hR, hC, hP, hQ⟩ := run c ap bp a b h
  exact Returns.intro hp.run hR hC hP hQ

theorem _root_.Sodium.Proofs.memcmp_constant_time : Sodium.Utils.memcmp_constant_time := by
  intro c c' ap bp a b a' b' hl h h'
  obtain ⟨r, hp, hR, -⟩ := run c ap bp a b h
  obtain ⟨r', hp', hR', -⟩ := run c' ap bp a' b' h'
  rw [hl] at hp
  exact SameTraceG.of_prun hp hp' hR.1 hR'.1

end Sodium.Proofs.Memcmp
