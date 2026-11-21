import Sodium.Proofs.MemzeroSteps
import Solutions.Logic.Run
/-!
# `memzero_correct`

The run of `sodium_memzero` (`MemzeroSteps`): the prologue up to the loop, `n` iterations of the
five-instruction loop, each zeroing one byte, and the epilogue. The loop invariant (`Inv`) keeps the
memory as a `CodeMem` with the stack slot `t` written last, and says which bytes are zero.
-/
namespace Sodium.Proofs.Memzero
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Sodium.Proofs Sodium.Utils

/-! ## Steps as runs -/

theorem running_of_eip (s : St) (h : s.eip ≠ Image.sym_halt) : Running img s.m := by
  unfold Running returned
  have : (s.eip == Image.sym_halt) = false := by simpa using h
  simp [St.m, img, this]

theorem neHalt (a : UInt32) (h : a ≠ 0x100DE1) : a ≠ Image.sym_halt := h

/-- A step proved by `execInstr`, as a run. -/
theorem run_step (s s' : St) (hic : s.ic < 0xFFFFFFFFFFFFFFFF) (hTF : s.fl &&& Flag.TF = 0)
    (hx : okState (execInstr s.m) = some s'.m) (hic' : s'.ic = s.ic) (he : s.eip ≠ Image.sym_halt) :
    Run img s.m { s' with ic := s.ic + 1 }.m :=
  Run.single (running_of_eip s he) (step_of_okState s hic hTF s' hx hic')

theorem tf_efl (f : UInt32) : efl f &&& Flag.TF = 0 := efl_TF f

theorem u64_succ_toNat {ic : UInt64} (h : ic.toNat + 1 < 2 ^ 64) : (ic + 1).toNat = ic.toNat + 1 := by
  rw [UInt64.toNat_add]; simp; omega

theorem u64_lt_max {ic : UInt64} (h : ic.toNat + 1 < 2 ^ 64) : ic < 0xFFFFFFFFFFFFFFFF := by
  rw [UInt64.lt_iff_toNat_lt]; simp; omega

/-- The four steps of an iteration up to the branch. -/
theorem run_iter (H : SMem) (p N i edx ebx t ebp esi edi F : UInt32) (ic : UInt64) (n : Nat)
    (okH : StoreOk Image.base Image.size H.mem t)
    (hsz : H.get.size ≤ ramTop) (hst : t.toNat + 16 ≤ H.get.size) (hap : StackApart t)
    (hi : i.toNat < n) (hP : p.toNat + n ≤ H.get.size)
    (hPi : p.toNat + n ≤ 0x100000 ∨ 0x100000 + 3560 ≤ p.toNat)
    (hPs : p.toNat + n ≤ t.toNat - 124 ∨ t.toNat + 16 ≤ p.toNat)
    (ok1 : StoreOk1 Image.base Image.size (CodeMem.wr4 H t p okH).mem (p.add i))
    (hic : ic.toNat + 4 < 2 ^ 64) :
    Run img (St.m ⟨(CodeMem.wr4 H t p okH).get, N, i, edx, ebx, t, ebp, esi, edi, 0x100C20, efl F, ic⟩)
      (St.m ⟨(CodeMem.wr1 (CodeMem.wr4 H t p okH) (p.add i) 0 ok1).get, N, i.add 1, p, ebx, t, ebp, esi, edi,
        0x100C2A, efl (subF 4 N (i.add 1) 0).2, ic + 1 + 1 + 1 + 1⟩) := by
  have h1 : (ic + 1).toNat = ic.toNat + 1 := u64_succ_toNat (by omega)
  have h2 : (ic + 1 + 1).toNat = ic.toNat + 2 := by rw [u64_succ_toNat (by omega), h1]
  have h3 : (ic + 1 + 1 + 1).toNat = ic.toNat + 3 := by rw [u64_succ_toNat (by omega), h2]
  refine Run.trans (run_step _ _ (u64_lt_max (show ic.toNat + 1 < 2 ^ 64 by omega)) (tf_efl F)
    (ex_load H p N i edx ebx t ebp esi edi F ic okH hsz hst) rfl (neHalt 0x100C20 (by decide))) ?_
  refine Run.trans (run_step _ _ (u64_lt_max (show (ic + 1).toNat + 1 < 2 ^ 64 by omega)) (tf_efl F)
    (ex_store H p N i ebx t ebp esi edi F (ic + 1) n okH hsz hst hap hi hP hPi hPs ok1) rfl
    (neHalt 0x100C23 (by decide))) ?_
  refine Run.trans (run_step _ _ (u64_lt_max (show (ic + 1 + 1).toNat + 1 < 2 ^ 64 by omega)) (tf_efl F)
    (ex_inc _ p N i ebx t ebp esi edi F (ic + 1 + 1) (by rw [wr1_get_size, wr4_get_size]; exact hsz))
    rfl (neHalt 0x100C27 (by decide))) ?_
  exact run_step _ _ (u64_lt_max (show (ic + 1 + 1 + 1).toNat + 1 < 2 ^ 64 by omega)) (tf_efl _)
    (ex_cmp _ p N (i.add 1) ebx t ebp esi edi _ (ic + 1 + 1 + 1) (by rw [wr1_get_size, wr4_get_size]; exact hsz))
    rfl (neHalt 0x100C28 (by decide))

/-! ## The loop -/

/-- A byte store below a word store, moved above it (they are disjoint). -/
theorem comm_mem (H : SMem) (t p a : UInt32) (okH : StoreOk Image.base Image.size H.mem t)
    (ok1 : StoreOk1 Image.base Image.size (CodeMem.wr4 H t p okH).mem a)
    (hd : a.toNat < t.toNat ∨ t.toNat + 4 ≤ a.toNat) :
    ∃ (ok1' : StoreOk1 Image.base Image.size H.mem a)
      (okH' : StoreOk Image.base Image.size (CodeMem.wr1 H a 0 ok1').mem t),
      (CodeMem.wr1 (CodeMem.wr4 H t p okH) a 0 ok1).get = (CodeMem.wr4 (CodeMem.wr1 H a 0 ok1') t p okH').get := by
  have hs4 : (CodeMem.wr4 H t p okH).mem.size = H.mem.size := wr4_get_size H t p okH
  have ok1' : StoreOk1 Image.base Image.size H.mem a := ⟨by rw [← hs4]; exact ok1.1, ok1.2⟩
  have hs1 : (CodeMem.wr1 H a 0 ok1').mem.size = H.mem.size := wr1_get_size H a 0 ok1'
  have okH' : StoreOk Image.base Image.size (CodeMem.wr1 H a 0 ok1').mem t := ⟨by rw [hs1]; exact okH.1, okH.2⟩
  refine ⟨ok1', okH', ?_⟩
  show wrBytes (wrBytes H.mem t 4 p) a 1 0 = wrBytes (wrBytes H.mem a 1 0) t 4 p
  exact wrBytes_comm14 okH.1 ok1'.1 hd

/-- The memory at the loop head: as at the entry, except the stack slot and the first `k` bytes of
the buffer, which are zero. -/
def BytesOk (M0 H : ByteArray) (t p : UInt32) (k : Nat) : Prop :=
  H.size = M0.size ∧ ∀ a : Nat, a < M0.size → ¬(t.toNat ≤ a ∧ a < t.toNat + 4) →
    H.get! a = if p.toNat ≤ a ∧ a < p.toNat + k then 0 else M0.get! a

/-- The loop invariant at the loop head, after `i` iterations. -/
def Inv (M0 : ByteArray) (t p N ebx ebp esi edi : UInt32) (i : Nat) (m : Machine) : Prop :=
  ∃ (H : SMem) (okH : StoreOk Image.base Image.size H.mem t) (F : UInt32) (ic : UInt64) (edx : UInt32),
    m = St.m ⟨(CodeMem.wr4 H t p okH).get, N, i.toUInt32, edx, ebx, t, ebp, esi, edi, 0x100C20, efl F, ic⟩ ∧
    ic.toNat ≤ 21 + 5 * i ∧ BytesOk M0 H.get t p i

/-- The facts about the call the loop needs, in `toNat` form. -/
structure Facts (M0 : ByteArray) (t p : UInt32) (n : Nat) : Prop where
  hsz : M0.size ≤ ramTop
  hst : t.toNat + 16 ≤ M0.size
  hap : StackApart t
  hn : n < 2 ^ 31
  hP : p.toNat + n ≤ M0.size
  hPi : p.toNat + n ≤ 0x100000 ∨ 0x100000 + 3560 ≤ p.toNat
  hPs : p.toNat + n ≤ t.toNat - 124 ∨ t.toNat + 16 ≤ p.toNat
  hst4 : 128 ≤ t.toNat + 4

theorem toNat_padd {p : UInt32} {k : Nat} (h : p.toNat + k < 2 ^ 32) : (p.add k.toUInt32).toNat = p.toNat + k :=
  toNat_add_of_lt h

theorem toNat_toUInt32 {k : Nat} (h : k < 2 ^ 32) : k.toUInt32.toNat = k := by
  simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt h

theorem succ_toUInt32 (i : Nat) : (i.toUInt32).add 1 = (i + 1).toUInt32 := by
  apply UInt32.toNat_inj.1
  show (i.toUInt32 + 1).toNat = _
  simp only [UInt32.toNat_add, Nat.toUInt32_eq, UInt32.toNat_ofNat', UInt32.reduceToNat]
  omega

/-- One iteration that goes back to the loop head. -/
theorem loop_step (M0 : ByteArray) (t p ebx ebp esi edi : UInt32) (n : Nat) (hF : Facts M0 t p n)
    (i : Nat) (m : Machine) (hi : i + 1 < n)
    (hI : Inv M0 t p n.toUInt32 ebx ebp esi edi i m) :
    ∃ m', Run img m m' ∧ Inv M0 t p n.toUInt32 ebx ebp esi edi (i + 1) m' := by
  obtain ⟨H, okH, F, ic, edx, rfl, hic, hsz', hB⟩ := hI
  have hlt : p.toNat + i < 2 ^ 32 := by have := hF.hP; have := hF.hsz; unfold ramTop at *; omega
  have hpi : (p.add i.toUInt32).toNat = p.toNat + i := toNat_padd hlt
  have hiN : (i.toUInt32).toNat = i := toNat_toUInt32 (by have := hF.hn; omega)
  have hsz : H.get.size ≤ ramTop := by rw [hsz']; exact hF.hsz
  have hst : t.toNat + 16 ≤ H.get.size := by rw [hsz']; exact hF.hst
  have hP : p.toNat + n ≤ H.get.size := by rw [hsz']; exact hF.hP
  have hs4 : (CodeMem.wr4 H t p okH).mem.size = H.get.size := wr4_get_size H t p okH
  have ok1 : StoreOk1 Image.base Image.size (CodeMem.wr4 H t p okH).mem (p.add i.toUInt32) := by
    refine ⟨?_, ?_⟩
    · rw [hs4, hpi]; omega
    · have := hF.hPi; rw [hpi]; simp only [Image.base, Image.size, UInt32.reduceToNat]; omega
  have hr := run_iter H p n.toUInt32 i.toUInt32 edx ebx t ebp esi edi F ic n okH hsz hst hF.hap
    (by rw [hiN]; omega) hP hF.hPi hF.hPs ok1 (by omega)
  have hnN : (n.toUInt32).toNat = n := toNat_toUInt32 (by have := hF.hn; omega)
  have hi1 : ((i + 1).toUInt32).toNat = i + 1 := toNat_toUInt32 (by have := hF.hn; omega)
  have hne : (n.toUInt32).toNat ≠ (i.toUInt32.add 1).toNat := by
    rw [succ_toUInt32, hi1, hnN]; omega
  have e1 : (ic + 1).toNat = ic.toNat + 1 := u64_succ_toNat (by omega)
  have e2 : (ic + 1 + 1).toNat = ic.toNat + 2 := by rw [u64_succ_toNat (by omega), e1]
  have e3 : (ic + 1 + 1 + 1).toNat = ic.toNat + 3 := by rw [u64_succ_toNat (by omega), e2]
  have e4 : (ic + 1 + 1 + 1 + 1).toNat = ic.toNat + 4 := by rw [u64_succ_toNat (by omega), e3]
  have e5 : (ic + 1 + 1 + 1 + 1 + 1).toNat = ic.toNat + 5 := by rw [u64_succ_toNat (by omega), e4]
  have hj := run_step _ _ (u64_lt_max (show (ic + 1 + 1 + 1 + 1).toNat + 1 < 2 ^ 64 by omega)) (tf_efl _)
    (ex_jne_back (CodeMem.wr1 (CodeMem.wr4 H t p okH) (p.add i.toUInt32) 0 ok1) p n.toUInt32 (i.toUInt32.add 1)
      ebx t ebp esi edi (ic + 1 + 1 + 1 + 1)
      (by rw [wr1_get_size, wr4_get_size]; exact hsz) hne) rfl (neHalt 0x100C2A (by decide))
  obtain ⟨ok1', okH', heq⟩ := comm_mem H t p (p.add i.toUInt32) okH ok1
    (by have := hF.hPs; rw [hpi]; omega)
  have hrun : Run img (St.m ⟨(CodeMem.wr4 H t p okH).get, n.toUInt32, i.toUInt32, edx, ebx, t, ebp, esi, edi,
      0x100C20, efl F, ic⟩)
      (St.m ⟨(CodeMem.wr1 (CodeMem.wr4 H t p okH) (p.add i.toUInt32) 0 ok1).get, n.toUInt32, i.toUInt32.add 1, p,
        ebx, t, ebp, esi, edi, 0x100C20, efl (subF 4 n.toUInt32 (i.toUInt32.add 1) 0).2, ic + 1 + 1 + 1 + 1 + 1⟩) :=
    hr.trans hj
  rw [heq, succ_toUInt32] at hrun
  refine ⟨_, hrun, CodeMem.wr1 H (p.add i.toUInt32) 0 ok1', okH', _, ic + 1 + 1 + 1 + 1 + 1, p, rfl, ?_, ?_⟩
  · rw [e5]; omega
  · refine ⟨by rw [wr1_get_size]; exact hsz', fun a ha hns => ?_⟩
    rw [wr1_get, get!_wrBytes1 (by rw [hpi]; omega), hB a ha hns, hpi]
    by_cases hai : a = p.toNat + i
    · subst hai; simp
    · rw [if_neg hai]
      by_cases hin : p.toNat ≤ a ∧ a < p.toNat + i
      · rw [if_pos hin, if_pos (by omega)]
      · rw [if_neg hin, if_neg (by omega)]

set_option maxHeartbeats 0 in
/-- The last iteration and the epilogue. -/
theorem loop_exit (M0 : ByteArray) (t p ebx ebp esi edi : UInt32) (n : Nat) (hF : Facts M0 t p n)
    (m : Machine) (hn0 : 0 < n) (hI : Inv M0 t p n.toUInt32 ebx ebp esi edi (n - 1) m) :
    ∃ (H : SMem) (okH : StoreOk Image.base Image.size H.mem t) (F ecx : UInt32) (ic : UInt64),
      Run img m (St.m ⟨(CodeMem.wr4 H t p okH).get, p, ecx, p, ebx, t.add 8, ebp, esi, edi,
        rdRaw H.get (t.add 4) 4, efl F, ic⟩) ∧ BytesOk M0 H.get t p n := by
  obtain ⟨H, okH, F, ic, edx, rfl, hic, hsz', hB⟩ := hI
  have hlt : p.toNat + (n - 1) < 2 ^ 32 := by have := hF.hP; have := hF.hsz; unfold ramTop at *; omega
  have hpi : (p.add (n - 1).toUInt32).toNat = p.toNat + (n - 1) := toNat_padd hlt
  have hiN : ((n - 1).toUInt32).toNat = n - 1 := toNat_toUInt32 (by have := hF.hn; omega)
  have hsz : H.get.size ≤ ramTop := by rw [hsz']; exact hF.hsz
  have hst : t.toNat + 16 ≤ H.get.size := by rw [hsz']; exact hF.hst
  have hP : p.toNat + n ≤ H.get.size := by rw [hsz']; exact hF.hP
  have hs4 : (CodeMem.wr4 H t p okH).mem.size = H.get.size := wr4_get_size H t p okH
  have ok1 : StoreOk1 Image.base Image.size (CodeMem.wr4 H t p okH).mem (p.add (n - 1).toUInt32) := by
    refine ⟨?_, ?_⟩
    · rw [hs4, hpi]; omega
    · have := hF.hPi; rw [hpi]; simp only [Image.base, Image.size, UInt32.reduceToNat]; omega
  have hr := run_iter H p n.toUInt32 (n - 1).toUInt32 edx ebx t ebp esi edi F ic n okH hsz hst hF.hap
    (by rw [hiN]; omega) hP hF.hPi hF.hPs ok1 (by omega)
  have hnN : (n.toUInt32).toNat = n := toNat_toUInt32 (by have := hF.hn; omega)
  have heqN : (n.toUInt32).toNat = ((n - 1).toUInt32.add 1).toNat := by
    rw [succ_toUInt32, Nat.sub_add_cancel hn0]
  have e1 : (ic + 1).toNat = ic.toNat + 1 := u64_succ_toNat (by omega)
  have e2 : (ic + 1 + 1).toNat = ic.toNat + 2 := by rw [u64_succ_toNat (by omega), e1]
  have e3 : (ic + 1 + 1 + 1).toNat = ic.toNat + 3 := by rw [u64_succ_toNat (by omega), e2]
  have e4 : (ic + 1 + 1 + 1 + 1).toNat = ic.toNat + 4 := by rw [u64_succ_toNat (by omega), e3]
  have e5 : (ic + 1 + 1 + 1 + 1 + 1).toNat = ic.toNat + 5 := by rw [u64_succ_toNat (by omega), e4]
  have e6 : (ic + 1 + 1 + 1 + 1 + 1 + 1).toNat = ic.toNat + 6 := by rw [u64_succ_toNat (by omega), e5]
  have hj := run_step _ _ (u64_lt_max (show (ic + 1 + 1 + 1 + 1).toNat + 1 < 2 ^ 64 by omega)) (tf_efl _)
    (ex_jne_out (CodeMem.wr1 (CodeMem.wr4 H t p okH) (p.add (n - 1).toUInt32) 0 ok1) p n.toUInt32
      ((n - 1).toUInt32.add 1) ebx t ebp esi edi (ic + 1 + 1 + 1 + 1)
      (by rw [wr1_get_size, wr4_get_size]; exact hsz) heqN) rfl (neHalt 0x100C2A (by decide))
  obtain ⟨ok1', okH', heq⟩ := comm_mem H t p (p.add (n - 1).toUInt32) okH ok1
    (by have := hF.hPs; rw [hpi]; omega)
  have hrun : Run img (St.m ⟨(CodeMem.wr4 H t p okH).get, n.toUInt32, (n - 1).toUInt32, edx, ebx, t, ebp, esi,
      edi, 0x100C20, efl F, ic⟩)
      (St.m ⟨(CodeMem.wr1 (CodeMem.wr4 H t p okH) (p.add (n - 1).toUInt32) 0 ok1).get, n.toUInt32,
        (n - 1).toUInt32.add 1, p, ebx, t, ebp, esi, edi, 0x100C2C,
        efl (subF 4 n.toUInt32 ((n - 1).toUInt32.add 1) 0).2, ic + 1 + 1 + 1 + 1 + 1⟩) :=
    hr.trans hj
  rw [heq] at hrun
  have hsz1 : (CodeMem.wr1 H (p.add (n - 1).toUInt32) 0 ok1').get.size = H.get.size := wr1_get_size H _ 0 ok1'
  have hp := run_step _ _ (u64_lt_max (show (ic + 1 + 1 + 1 + 1 + 1).toNat + 1 < 2 ^ 64 by omega)) (tf_efl _)
    (ex_pop (CodeMem.wr1 H (p.add (n - 1).toUInt32) 0 ok1') p n.toUInt32 ((n - 1).toUInt32.add 1) p ebx t ebp
      esi edi (subF 4 n.toUInt32 ((n - 1).toUInt32.add 1) 0).2 (ic + 1 + 1 + 1 + 1 + 1) okH'
      (by rw [hsz1]; exact hsz) (by rw [hsz1]; exact hst)) rfl (neHalt 0x100C2C (by decide))
  have hrt := run_step _ _ (u64_lt_max (show (ic + 1 + 1 + 1 + 1 + 1 + 1).toNat + 1 < 2 ^ 64 by omega)) (tf_efl _)
    (ex_ret (CodeMem.wr1 H (p.add (n - 1).toUInt32) 0 ok1') p p ((n - 1).toUInt32.add 1) p ebx t ebp
      esi edi (subF 4 n.toUInt32 ((n - 1).toUInt32.add 1) 0).2 (ic + 1 + 1 + 1 + 1 + 1 + 1) okH'
      (by rw [hsz1]; exact hsz) (by rw [hsz1]; exact hst)) rfl (neHalt 0x100C2D (by decide))
  refine ⟨CodeMem.wr1 H (p.add (n - 1).toUInt32) 0 ok1', okH', (subF 4 n.toUInt32 ((n - 1).toUInt32.add 1) 0).2,
    (n - 1).toUInt32.add 1, ic + 1 + 1 + 1 + 1 + 1 + 1 + 1, hrun.trans (hp.trans hrt), ?_⟩
  refine ⟨by rw [hsz1, hsz'], fun a ha hns => ?_⟩
  rw [wr1_get, get!_wrBytes1 (by rw [hpi]; omega), hB a ha hns, hpi]
  by_cases hai : a = p.toNat + (n - 1)
  · subst hai; simp; omega
  · rw [if_neg hai]
    by_cases hin : p.toNat ≤ a ∧ a < p.toNat + (n - 1)
    · rw [if_pos hin, if_pos (by omega)]
    · rw [if_neg hin, if_neg (by omega)]

/-! ## The task -/

theorem u32_toNat_sub {a : UInt32} {k : Nat} (h : k ≤ a.toNat) (hk : k < 2 ^ 32) :
    (a - k.toUInt32).toNat = a.toNat - k := by
  rw [UInt32.toNat_sub_of_le]
  · rw [toNat_toUInt32 hk]
  · rw [UInt32.le_iff_toNat_le, toNat_toUInt32 hk]; exact h

theorem u32_toNat_add {a b : UInt32} (h : a.toNat + b.toNat < 2 ^ 32) : (a.add b).toNat = a.toNat + b.toNat := by
  show (a + b).toNat = _
  rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt h

theorem img_size : img.bytes.size = 3560 := image_size
theorem img_base : img.base.toNat = 0x100000 := rfl

set_option maxHeartbeats 0 in
theorem _root_.Sodium.Proofs.memzero_correct : Sodium.Utils.memzero_correct := by
  intro c p n ⟨hc, hb⟩
  have hsz : c.mem.size ≤ ramTop := hc.1
  have hsp : 128 ≤ c.sp.toNat := hc.2.2.2.2.1
  have hsp12 : c.sp.toNat + 12 ≤ c.mem.size := by have := hc.2.2.2.2.2.1; simpa using this
  have hlo : (c.stackLo stackBound).toNat = c.sp.toNat - 128 := u32_toNat_sub hsp (by decide)
  have hap0 : c.sp.toNat - 128 + 140 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ c.sp.toNat - 128 := by
    have h := hc.2.2.2.2.2.2
    unfold Apart at h
    rw [hlo, img_size, img_base] at h
    simp only [stackSize, List.length_cons, List.length_nil, stackBound] at h
    omega
  have hramT : ramTop < 2 ^ 32 := by decide
  -- the slot of the pushed register
  let t : UInt32 := c.sp - (4 : Nat).toUInt32
  have ht : t.toNat = c.sp.toNat - 4 := u32_toNat_sub (by omega) (by decide)
  have hspt : c.sp = t.add 4 := by
    apply UInt32.toNat_inj.1; rw [u32_toNat_add (by simp; omega)]; simp; omega
  let G : SMem := codeMem c hc
  have hG : G.get = c.mem := rfl
  have hst : t.toNat + 16 ≤ c.mem.size := by omega
  have hap : StackApart t := by unfold StackApart; omega
  have h8 : t.add 8 = c.sp + 4 * (0 + 1 : Nat).toUInt32 := by
    apply UInt32.toNat_inj.1
    rw [u32_toNat_add (by simp; omega), UInt32.toNat_add]; simp; omega
  have h12 : t.add 12 = c.sp + 4 * (1 + 1 : Nat).toUInt32 := by
    apply UInt32.toNat_inj.1
    rw [u32_toNat_add (by simp; omega), UInt32.toNat_add]; simp; omega
  have hP' : rdRaw G.get (t.add 8) 4 = p := by
    rw [h8]; exact calls_arg hc 0 (by simp)
  have hN' : rdRaw G.get (t.add 12) 4 = n.toUInt32 := by
    rw [h12]; exact calls_arg hc 1 (by simp)
  have hret : rdRaw G.get (t.add 4) 4 = Image.sym_halt := by
    rw [← hspt]; exact calls_ret hc
  have ok0 : StoreOk Image.base Image.size G.mem t := by
    refine ⟨by show t.toNat + 4 ≤ c.mem.size; omega, ?_⟩
    simp only [Image.base, Image.size, UInt32.reduceToNat]; omega
  have ok1 : StoreOk Image.base Image.size (CodeMem.wr4 G t c.regs.eax ok0).mem t :=
    ⟨by show t.toNat + 4 ≤ (CodeMem.wr4 G t c.regs.eax ok0).get.size; rw [wr4_get_size]; exact ok0.1, ok0.2⟩
  have e0 : c.enter Image.sym_sodium_memzero =
      St.m ⟨G.get, c.regs.eax, c.regs.ecx, c.regs.edx, c.regs.ebx, t.add 4, c.regs.ebp, c.regs.esi,
        c.regs.edi, 0x100C00, efl c.regs.flags, 0⟩ := by
    rw [← hspt]; rfl
  have hn : n < 2 ^ 31 := by have := hb.2.1; unfold maxObject at this; omega
  have hnN : (n.toUInt32).toNat = n := toNat_toUInt32 (by omega)
  have hesp : (t.add 4) + 4 = t.add 8 := by
    apply UInt32.toNat_inj.1
    rw [UInt32.toNat_add, u32_toNat_add (by simp; omega), u32_toNat_add (by simp; omega)]; simp; omega
  have hstack : ∀ a : UInt32, ¬ InRange (t.add 4 - (stackBound : Nat).toUInt32) stackBound a →
      ¬(t.toNat ≤ a.toNat ∧ a.toNat < t.toNat + 4) := by
    intro a ha hin
    apply ha
    rw [inRange_iff, u32_toNat_sub (by rw [u32_toNat_add (by simp; omega)]; simp [stackBound]; omega) (by decide),
      u32_toNat_add (by simp; omega)]
    simp [stackBound]; omega
  rw [e0]
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · -- an empty buffer
    subst hn0
    have hz : (rdRaw G.get (t.add 12) 4).toNat = 0 := by rw [hN']; rfl
    have hrun := run_of_runOk (run_zero G c.regs.eax c.regs.ecx c.regs.edx c.regs.ebx t c.regs.ebp c.regs.esi
      c.regs.edi c.regs.flags hsz hst hap hz ok0 ok1)
    rw [hret] at hrun
    refine Returns.intro hrun ⟨rfl, ?_, efl_DF _⟩ ⟨rfl, rfl, rfl, rfl⟩ ⟨?_, ?_⟩ ?_
    · show t.add 8 = (t.add 4) + 4
      exact hesp.symm
    · show (CodeMem.wr4 (CodeMem.wr4 G t c.regs.eax ok0) t (rdRaw G.get (t.add 8) 4) ok1).get.size = c.mem.size
      rw [wr4_get_size, wr4_get_size]; rfl
    · intro a ha _ hs
      have hd := hstack a hs
      show memByte (wrBytes (wrBytes c.mem t 4 c.regs.eax) t 4 (rdRaw G.get (t.add 8) 4)) a = memByte c.mem a
      rw [memByte_wrBytes4_other (mem := wrBytes c.mem t 4 c.regs.eax) (by rw [size_wrBytes4 (by omega)]; omega)
        (by rw [size_wrBytes4 (by omega)]; exact ha) (by omega),
        memByte_wrBytes4_other (mem := c.mem) (by omega) ha (by omega)]
    · simp [bytesAt, memBytes]
  · -- the loop
    have hF : Facts c.mem t p n := by
      have hfit := hb.1
      have hai := hb.2.2.1
      have has := hb.2.2.2
      unfold Fits at hfit
      unfold Apart at hai has
      rw [img_size, img_base] at hai
      rw [hlo] at has
      simp only [stackSize, stackBound] at has
      exact ⟨hsz, hst, hap, hn, by omega, by omega, by omega, by omega⟩
    have hz : 0 < (rdRaw G.get (t.add 12) 4).toNat := by rw [hN', hnN]; exact hn0
    have hrun0 := run_of_runOk (run_pre G c.regs.eax c.regs.ecx c.regs.edx c.regs.ebx t c.regs.ebp c.regs.esi
      c.regs.edi c.regs.flags hsz hst hap hz ok0 ok1)
    rw [hP', hN'] at hrun0
    have hI0 : Inv c.mem t p n.toUInt32 c.regs.ebx c.regs.ebp c.regs.esi c.regs.edi 0
        (St.m ⟨(CodeMem.wr4 (CodeMem.wr4 G t c.regs.eax ok0) t p ok1).get, n.toUInt32, 0, c.regs.edx, c.regs.ebx, t,
          c.regs.ebp, c.regs.esi, c.regs.edi, 0x100C20, efl (logicF 4 0).2, 21⟩) := by
      refine ⟨CodeMem.wr4 G t c.regs.eax ok0, ok1, (logicF 4 0).2, 21, c.regs.edx, rfl, by decide,
        by rw [wr4_get_size]; rfl, fun a ha hns => ?_⟩
      rw [wr4_get, get!_wrBytes4 (by rw [hG]; omega)]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rfl
    obtain ⟨m1, hL, hI1⟩ := Run.loop (img := img) (Inv c.mem t p n.toUInt32 c.regs.ebx c.regs.ebp c.regs.esi
      c.regs.edi) (n - 1) (fun i m hi hI => loop_step c.mem t p c.regs.ebx c.regs.ebp c.regs.esi c.regs.edi n hF
        i m (by omega) hI) hI0
    obtain ⟨H, okH, F, ecx, ic, hE, hBy⟩ := loop_exit c.mem t p c.regs.ebx c.regs.ebp c.regs.esi c.regs.edi n hF
      m1 hn0 hI1
    obtain ⟨hHs, hHb⟩ := hBy
    have hfe : rdRaw H.get (t.add 4) 4 = Image.sym_halt := by
      rw [← hret, hG]
      have h4 : (t.add 4).toNat = t.toNat + 4 := u32_toNat_add (by simp; omega)
      apply rdBytes4_congr (by rw [hHs, h4]; omega) (by rw [h4]; omega)
      intro k hk
      rw [h4, hHb _ (by omega) (by omega), if_neg (by have := hF.hPs; omega)]
    have hrun := hrun0.trans (hL.trans hE)
    rw [hfe] at hrun
    refine Returns.intro hrun ⟨rfl, ?_, efl_DF _⟩ ⟨rfl, rfl, rfl, rfl⟩ ⟨?_, ?_⟩ ?_
    · show t.add 8 = (t.add 4) + 4
      exact hesp.symm
    · show (CodeMem.wr4 H t p okH).get.size = c.mem.size
      rw [wr4_get_size, hHs]
    · intro a ha hw hs
      have hd := hstack a hs
      show memByte (wrBytes H.get t 4 p) a = memByte c.mem a
      rw [memByte_wrBytes4_other (mem := H.get) (by rw [hHs]; omega) (by rw [hHs]; exact ha) (by omega),
        memByte_def (mem := H.get) (by rw [hHs]; exact ha), memByte_def (mem := c.mem) ha, hHb _ ha hd]
      rw [if_neg (fun h => hw (inRange_iff.2 h))]
    · show memBytes (wrBytes H.get t 4 p) p n = List.replicate n 0
      apply memBytes_eq_iff.2
      refine ⟨by simp, fun k hk => ?_⟩
      simp only [List.length_replicate] at hk
      have hpk : (p + k.toUInt32).toNat = p.toNat + k := toNat_add_of_lt (by have := hF.hP; omega)
      have hPs := hF.hPs
      rw [memByte_wrBytes4_other (mem := H.get) (by rw [hHs]; omega) (by rw [hpk, hHs]; have := hF.hP; omega)
        (by omega), memByte_def (mem := H.get) (by rw [hpk, hHs]; have := hF.hP; omega), hpk, hHb _ (by have := hF.hP; omega) (by omega),
        if_pos (by omega)]
      simp

end Sodium.Proofs.Memzero
