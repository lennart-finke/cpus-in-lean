import Sodium.Proofs.UnpadPre
import Sodium.Proofs.UnpadBody
import Sodium.Proofs.UnpadExit
import Sodium.Proofs.UnpadSpec
/-!
# `unpad_correct` and `unpad_constant_time`

The run of `sodium_unpad` (`UnpadSteps`): the prologue, `block - 1` iterations of the loop body
back to the loop head, and the last iteration followed by the epilogue. All of it is a run along
the path `upath block`, which depends on the block size only: this is `unpad_constant_time`.

The loop invariant (`Inv`) keeps the memory equal to the one the prologue left (`P`) outside the
`pad_len` slot at `t`, and the registers and the slot equal to `UnpadSpec.run` of the bytes read so
far, from the end of the buffer. `UnpadSpec.run_spec` and `UnpadSpec.unpad_spec` give the result.
-/
namespace Sodium.Proofs.Unpad
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Sodium.Proofs Sodium.Utils Sodium.Proofs.PadLib
  Sodium.Proofs.PadRun Sodium.Spec

/-- The instruction addresses of a call with block size `block`. -/
def upath (block : Nat) : List UInt32 := Lpre ++ (List.replicate (block - 1) Lbody).flatten ++ Lexit

/-! ## Arithmetic -/

theorem t_add {t : UInt32} {k : Nat} (h : t.toNat + k < 2 ^ 32) : (t.add k.toUInt32).toNat = t.toNat + k :=
  toNat_add_of_lt h

theorem toNat_u32 {k : Nat} (h : k < 2 ^ 32) : k.toUInt32.toNat = k := by
  simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt h

theorem u64_add (ic : UInt64) (k : Nat) (h : ic.toNat + k < 2 ^ 64) : (ic + Nat.toUInt64 k).toNat = ic.toNat + k := by
  rw [UInt64.toNat_add]
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (a := k) (by omega)]
  exact Nat.mod_eq_of_lt h

theorem succ_u32 (i : Nat) : (i.toUInt32).add 1 = (i + 1).toUInt32 := by
  apply UInt32.toNat_inj.1
  show (i.toUInt32 + 1).toNat = _
  simp only [UInt32.toNat_add, Nat.toUInt32_eq, UInt32.toNat_ofNat', UInt32.reduceToNat]
  omega

theorem sub1 (x : UInt32) : x - 1 = x.add 4294967295 := usub_of x 1 4294967295 rfl

theorem ubit_eq (c pl acc : UInt32) : ubit c pl acc = barrier acc pl c := by
  unfold ubit barrier
  simp only [sub1]
  rfl

theorem upl_eq (c pl acc : UInt32) (i : Nat) :
    upl c pl acc i.toUInt32 = pl ||| (i.toUInt32 &&& (0 - barrier acc pl c)) := by
  unfold upl
  rw [ubit_eq]
  show pl ||| ((0 - barrier acc pl c) &&& i.toUInt32) = _
  rw [UInt32.and_comm]

/-- The bytes of the buffer from its end. -/
def cb (buf : List UInt8) (j : Nat) : UInt32 := (buf.getD (buf.length - 1 - j) 0).toUInt32

theorem run_succ (buf : List UInt8) (i : Nat) (c : UInt32) (hc : c = cb buf i) :
    run (cb buf) (i + 1) =
      ((run (cb buf) i).1.lor c,
       (run (cb buf) i).2.1.lor (ubit c (run (cb buf) i).2.2 (run (cb buf) i).1),
       upl c (run (cb buf) i).2.2 (run (cb buf) i).1 i.toUInt32) := by
  subst hc
  rw [upl_eq, ubit_eq]
  rfl

/-! ## The facts of a call -/

/-- The facts about a call that the run needs, in `toNat` form; `t` is the loop's stack pointer. -/
structure Facts (c : Caller) (t lp bp : UInt32) (buf : List UInt8) (B : Nat) : Prop where
  sz : c.mem.size ≤ 0xFEC00000
  st : t.toNat + 44 ≤ c.mem.size
  t104 : 104 ≤ t.toNat
  ap : t.toNat + 44 ≤ 0x100000 ∨ 0x100000 + 3560 + 104 ≤ t.toNat
  bL : bp.toNat + buf.length ≤ c.mem.size
  bi : bp.toNat + buf.length ≤ 0x100000 ∨ 0x100000 + 3560 ≤ bp.toNat
  bs : bp.toNat + buf.length ≤ t.toNat - 104 ∨ t.toNat + 44 ≤ bp.toNat
  lsz : lp.toNat + 4 ≤ c.mem.size
  li : lp.toNat + 4 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ lp.toNat
  ls : lp.toNat + 4 ≤ t.toNat - 104 ∨ t.toNat + 44 ≤ lp.toNat
  B0 : 0 < B
  BL : B ≤ buf.length
  Lmax : buf.length < 2 ^ 31
  a28 : rdRaw c.mem (t.add 28) 4 = lp
  a32 : rdRaw c.mem (t.add 32) 4 = bp
  a36 : rdRaw c.mem (t.add 36) 4 = buf.length.toUInt32
  a40 : rdRaw c.mem (t.add 40) 4 = B.toUInt32
  a24 : rdRaw c.mem (t.add 24) 4 = Image.sym_halt
  bytes : memBytes c.mem bp buf.length = buf

theorem u32_sub {a : UInt32} {k : Nat} (h : k ≤ a.toNat) (hk : k < 2 ^ 32) :
    (a - k.toUInt32).toNat = a.toNat - k := by
  rw [UInt32.toNat_sub_of_le]
  · rw [toNat_u32 hk]
  · rw [UInt32.le_iff_toNat_le, toNat_u32 hk]; exact h

theorem img_size : img.bytes.size = 3560 := image_size
theorem img_base : img.base.toNat = 0x100000 := rfl

theorem sp_arg {sp t : UInt32} (ht : t = sp - (24 : Nat).toUInt32) (h24 : 24 ≤ sp.toNat) (hs : sp.toNat + 20 < 2 ^ 32)
    (j : Nat) (hj : j < 5) (k : UInt32) (hk : k.toNat = 24 + 4 * j) : t.add k = sp + 4 * j.toUInt32 := by
  apply UInt32.toNat_inj.1
  have htn : t.toNat = sp.toNat - 24 := by rw [ht]; exact u32_sub h24 (by decide)
  show (t + k).toNat = _
  rw [UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_mul, toNat_u32 (by omega), hk, htn]
  simp only [UInt32.reduceToNat]
  rw [Nat.mod_eq_of_lt (a := 4 * j) (by omega)]
  omega

theorem facts_of (c : Caller) (lp bp : UInt32) (buf : List UInt8) (B : Nat)
    (h : UnpadPre c lp bp buf B) :
    Facts c (c.sp - (24 : Nat).toUInt32) lp bp buf B := by
  obtain ⟨hc, hb, hl, hap, hmem, hB0, hBL⟩ := h
  have hsz : c.mem.size ≤ 0xFEC00000 := hc.1
  have hsp : 128 ≤ c.sp.toNat := hc.2.2.2.2.1
  have hsp20 : c.sp.toNat + 20 ≤ c.mem.size := by have := hc.2.2.2.2.2.1; simpa using this
  have hlo : (c.stackLo stackBound).toNat = c.sp.toNat - 128 := u32_sub hsp (by decide)
  have ht : (c.sp - (24 : Nat).toUInt32).toNat = c.sp.toNat - 24 := u32_sub (by omega) (by decide)
  have hap0 : c.sp.toNat - 128 + 148 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ c.sp.toNat - 128 := by
    have h := hc.2.2.2.2.2.2
    unfold Apart at h
    rw [hlo, img_size, img_base] at h
    simp only [stackSize, List.length_cons, List.length_nil, stackBound] at h
    omega
  have hLmax : buf.length < 2 ^ 31 := by have := hb.2.1; unfold maxObject at this; omega
  obtain ⟨hbf, -, hbi, hbs⟩ := hb
  obtain ⟨hlf, -, hli, hls⟩ := hl
  unfold Fits at hbf hlf
  unfold Apart at hbi hbs hli hls
  rw [img_size, img_base] at hbi hli
  rw [hlo] at hbs hls
  simp only [stackSize, stackBound] at hbs hls
  have e := fun j hj => sp_arg (sp := c.sp) (t := c.sp - (24 : Nat).toUInt32) rfl (by omega) (by omega) j hj
  have a := fun j (hj : j < 4) => calls_arg hc j (by simp; omega)
  have hr := calls_ret hc
  refine ⟨hsz, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, hB0, hBL,
    hLmax, ?_, ?_, ?_, ?_, ?_, hmem⟩
  · have := e 1 (by omega) 28 rfl; have h' := a 0 (by omega)
    show rdBytes _ _ 4 = _; rw [this]; simpa using h'
  · have := e 2 (by omega) 32 rfl; have h' := a 1 (by omega)
    show rdBytes _ _ 4 = _; rw [this]; simpa using h'
  · have := e 3 (by omega) 36 rfl; have h' := a 2 (by omega)
    show rdBytes _ _ 4 = _; rw [this]; simpa using h'
  · have := e 4 (by omega) 40 rfl; have h' := a 3 (by omega)
    show rdBytes _ _ 4 = _; rw [this]; simpa using h'
  · have := e 0 (by omega) 24 rfl
    show rdBytes _ _ 4 = _; rw [this, show c.sp + 4 * (0 : Nat).toUInt32 = c.sp by simp]; exact hr

/-! ## The prologue's memory -/

/-- The memory after the prologue. -/
def preMem (G : ByteArray) (t ebp ebx edi esi y : UInt32) : ByteArray :=
  wrBytes (wrBytes (wrBytes (wrBytes (wrBytes (wrBytes G (t.add 20) 4 ebp) (t.add 16) 4 ebx)
    (t.add 12) 4 edi) (t.add 8) 4 esi) t 4 0) (t.add 4) 4 y

theorem tk {t : UInt32} (ht : t.toNat + 44 < 2 ^ 32) (k : UInt32) (hk : k.toNat ≤ 44) :
    (t.add k).toNat = t.toNat + k.toNat := by
  show (t + k).toNat = _
  rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)

theorem preMem_agree (G : ByteArray) (t ebp ebx edi esi y : UInt32) (h : t.toNat + 44 ≤ G.size)
    (ht : t.toNat + 44 < 2 ^ 32) :
    Agree (preMem G t ebp ebx edi esi y) G t.toNat (t.toNat + 24) := by
  have e4 := tk ht 4 (by decide); have e8 := tk ht 8 (by decide); have e12 := tk ht 12 (by decide)
  have e16 := tk ht 16 (by decide); have e20 := tk ht 20 (by decide)
  simp only [UInt32.reduceToNat] at e4 e8 e12 e16 e20
  unfold preMem
  refine Agree.wr4 (Agree.wr4 (Agree.wr4 (Agree.wr4 (Agree.wr4 (Agree.wr4 (Agree.refl G _ _) _ _ ?_ ?_ ?_)
    _ _ ?_ ?_ ?_) _ _ ?_ ?_ ?_) _ _ ?_ ?_ ?_) _ _ ?_ ?_ ?_) _ _ ?_ ?_ ?_ <;>
    (try simp only [size_wrBytes, e4, e8, e12, e16, e20]) <;> omega

theorem rd_other {mem : ByteArray} {a b v : UInt32} (ha : a.toNat + 4 ≤ mem.size) (hb : b.toNat + 4 ≤ mem.size)
    (hd : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    rdRaw (wrBytes mem a 4 v) b 4 = rdRaw mem b 4 := rdBytes4_wrBytes4_other ha hb hd

theorem rd_self {mem : ByteArray} {a v : UInt32} (ha : a.toNat + 4 ≤ mem.size) :
    rdRaw (wrBytes mem a 4 v) a 4 = v := rdBytes4_wrBytes4_self ha

theorem preMem_rd (G : ByteArray) (t ebp ebx edi esi y : UInt32) (h : t.toNat + 44 ≤ G.size)
    (ht : t.toNat + 44 < 2 ^ 32) :
    rdRaw (preMem G t ebp ebx edi esi y) (t.add 4) 4 = y ∧
    rdRaw (preMem G t ebp ebx edi esi y) (t.add 8) 4 = esi ∧
    rdRaw (preMem G t ebp ebx edi esi y) (t.add 12) 4 = edi ∧
    rdRaw (preMem G t ebp ebx edi esi y) (t.add 16) 4 = ebx ∧
    rdRaw (preMem G t ebp ebx edi esi y) (t.add 20) 4 = ebp := by
  have e4 := tk ht 4 (by decide); have e8 := tk ht 8 (by decide); have e12 := tk ht 12 (by decide)
  have e16 := tk ht 16 (by decide); have e20 := tk ht 20 (by decide)
  simp only [UInt32.reduceToNat] at e4 e8 e12 e16 e20
  unfold preMem
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [rd_self (by simp only [size_wrBytes, e4]; omega)]
  · rw [rd_other (by simp only [size_wrBytes, e4]; omega) (by simp only [size_wrBytes, e8]; omega) (by omega),
      rd_other (by simp only [size_wrBytes]; omega) (by simp only [size_wrBytes, e8]; omega) (by omega),
      rd_self (by simp only [size_wrBytes, e8]; omega)]
  · rw [rd_other (by simp only [size_wrBytes, e4]; omega) (by simp only [size_wrBytes, e12]; omega) (by omega),
      rd_other (by simp only [size_wrBytes]; omega) (by simp only [size_wrBytes, e12]; omega) (by omega),
      rd_other (by simp only [size_wrBytes, e8]; omega) (by simp only [size_wrBytes, e12]; omega) (by omega),
      rd_self (by simp only [size_wrBytes, e12]; omega)]
  · rw [rd_other (by simp only [size_wrBytes, e4]; omega) (by simp only [size_wrBytes, e16]; omega) (by omega),
      rd_other (by simp only [size_wrBytes]; omega) (by simp only [size_wrBytes, e16]; omega) (by omega),
      rd_other (by simp only [size_wrBytes, e8]; omega) (by simp only [size_wrBytes, e16]; omega) (by omega),
      rd_other (by simp only [size_wrBytes, e12]; omega) (by simp only [size_wrBytes, e16]; omega) (by omega),
      rd_self (by simp only [size_wrBytes, e16]; omega)]
  · rw [rd_other (by simp only [size_wrBytes, e4]; omega) (by simp only [size_wrBytes, e20]; omega) (by omega),
      rd_other (by simp only [size_wrBytes]; omega) (by simp only [size_wrBytes, e20]; omega) (by omega),
      rd_other (by simp only [size_wrBytes, e8]; omega) (by simp only [size_wrBytes, e20]; omega) (by omega),
      rd_other (by simp only [size_wrBytes, e12]; omega) (by simp only [size_wrBytes, e20]; omega) (by omega),
      rd_other (by simp only [size_wrBytes, e16]; omega) (by simp only [size_wrBytes, e20]; omega) (by omega),
      rd_self (by simp only [size_wrBytes, e20]; omega)]

/-! ## The loop -/

/-- The loop head after `i` iterations: `P` is the memory the prologue left. -/
def LoopInv (t bp : UInt32) (buf : List UInt8) (P : ByteArray) (i : Nat) (m : Machine) : Prop :=
  ∃ (M : SMem) (ecx edx esi f edi : UInt32) (ic : UInt64),
    m = St.m ⟨M.get, (run (cb buf) i).2.1, ecx, edx, i.toUInt32, t, (run (cb buf) i).1, esi, edi, 0x100D70,
      efl f, ic⟩ ∧
    ic.toNat ≤ 30 + 20 * i ∧ edi.toNat = bp.toNat + (buf.length - 1 - i) ∧
    Agree M.get P t.toNat (t.toNat + 4) ∧ rdRaw M.get t 4 = (run (cb buf) i).2.2

theorem rd4_out {M P G : ByteArray} {t : UInt32} (hM : Agree M P t.toNat (t.toNat + 4))
    (hP : Agree P G t.toNat (t.toNat + 24)) (a : UInt32) (ha : a.toNat + 4 ≤ G.size)
    (hout : a.toNat + 4 ≤ t.toNat ∨ t.toNat + 24 ≤ a.toNat) : rdRaw M a 4 = rdRaw G a 4 :=
  (hM.rd4 a (by rw [hP.1]; exact ha) (by omega)).trans (hP.rd4 a ha hout)

theorem rd4_mid {M P : ByteArray} {t : UInt32} (hM : Agree M P t.toNat (t.toNat + 4)) (a : UInt32)
    (ha : a.toNat + 4 ≤ P.size) (hout : t.toNat + 4 ≤ a.toNat) : rdRaw M a 4 = rdRaw P a 4 :=
  hM.rd4 a ha (Or.inr hout)

theorem rd1_out {M P G : ByteArray} {t : UInt32} (hM : Agree M P t.toNat (t.toNat + 4))
    (hP : Agree P G t.toNat (t.toNat + 24)) (a : UInt32) (ha : a.toNat < G.size)
    (hout : a.toNat < t.toNat ∨ t.toNat + 24 ≤ a.toNat) : rdRaw M a 1 = rdRaw G a 1 :=
  (hM.rd1 a (by rw [hP.1]; exact ha) (by omega)).trans (hP.rd1 a ha hout)

theorem dec_toNat (x : UInt32) (h : 1 ≤ x.toNat) : (x.add 4294967295).toNat = x.toNat - 1 := by
  show (x + 4294967295).toNat = _
  have := x.toNat_lt
  rw [UInt32.toNat_add]; simp only [UInt32.reduceToNat]; omega

/-- The byte the loop reads in iteration `i`. -/
theorem byte_eq {c : Caller} {t lp bp : UInt32} {buf : List UInt8} {B : Nat} (F : Facts c t lp bp buf B)
    (i : Nat) (hi : i < buf.length) (edi : UInt32) (he : edi.toNat = bp.toNat + (buf.length - 1 - i)) :
    rdRaw c.mem edi 1 = cb buf i := by
  have hlt : edi.toNat < c.mem.size := by have := F.bL; omega
  have hk : buf.length - 1 - i < buf.length := by omega
  have e : edi = bp + (buf.length - 1 - i).toUInt32 := by
    apply UInt32.toNat_inj.1
    rw [he, toNat_add_of_lt (by have := F.bL; have := F.sz; omega)]
  show rdBytes c.mem edi 1 = _
  rw [rdBytes1_eq hlt]
  have := (memBytes_eq_iff.mp F.bytes).2 (buf.length - 1 - i) hk
  rw [← e] at this
  rw [this]
  unfold cb
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]

theorem toNat_i {i B : Nat} (h : i < B) (hB : B < 2 ^ 31) : (i.toUInt32).toNat = i := toNat_u32 (by omega)

/-- One iteration back to the loop head. -/
theorem loop_step {c : Caller} {t lp bp : UInt32} {buf : List UInt8} {B : Nat} (F : Facts c t lp bp buf B)
    {P : ByteArray} (hP : Agree P c.mem t.toNat (t.toNat + 24)) (i : Nat) (m : Machine) (hi : i + 1 < B)
    (hI : LoopInv t bp buf P i m) : ∃ m', PRun img Lbody m m' ∧ LoopInv t bp buf P (i + 1) m' := by
  obtain ⟨M, ecx, edx, esi, f, edi, ic, rfl, hic, hedi, hA, hpl⟩ := hI
  have hsz : M.get.size = c.mem.size := hA.1.trans hP.1
  have hL := F.BL; have hLm := F.Lmax; have hst := F.st; have hsz0 := F.sz
  have e40 := tk (t := t) (by omega) 40 (by decide)
  simp only [UInt32.reduceToNat] at e40
  have h40 : rdRaw M.get (t.add 40) 4 = B.toUInt32 :=
    (rd4_out hA hP _ (by omega) (by omega)).trans F.a40
  have hiN := toNat_i (i := i) (B := B) (by omega) (by omega)
  have hBN : (B.toUInt32).toNat = B := toNat_u32 (by omega)
  obtain ⟨M', ecx', edx', esi', F', hM', hrun⟩ := body M (run (cb buf) i).2.1 ecx edx i.toUInt32 t
    (run (cb buf) i).1 esi edi f ic (by rw [hsz]; exact hsz0) (by rw [hsz]; exact hst) (by have := F.ap; omega)
    (by rw [hsz]; have := F.bL; omega) (by have := F.bi; omega) (by omega)
    (by rw [h40, hiN, hBN]; exact hi)
  have hc : rdRaw M.get edi 1 = cb buf i := by
    rw [rd1_out hA hP _ (by have := F.bL; omega) (by have := F.bs; omega)]
    exact byte_eq F i (by omega) edi hedi
  rw [hc, hpl] at hrun hM'
  refine ⟨_, hrun, M', ecx', edx', esi', F', edi.add 4294967295, ic + Nat.toUInt64 20, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_succ buf i (cb buf i) rfl, succ_u32]
  · rw [u64_add ic 20 (by omega)]; omega
  · rw [dec_toNat edi (by omega)]; omega
  · rw [hM']; exact hA.wr4 t _ (Nat.le_refl _) (Nat.le_refl _) (by rw [hsz]; omega)
  · rw [hM', rd_self (by rw [hsz]; omega), run_succ buf i (cb buf i) rfl]

/-! ## What the loop computes -/

theorem cb_lt (buf : List UInt8) (j : Nat) : (cb buf j).toNat < 256 := by
  unfold cb; simp only [UInt8.toNat_toUInt32]; exact UInt8.toNat_lt _

theorem cb_eq (buf : List UInt8) (j : Nat) (hj : j < buf.length) :
    cb buf j = (buf[buf.length - 1 - j]'(by omega)).toUInt32 := by
  unfold cb; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem u8_u32_eq (x : UInt8) (k : UInt8) : x.toUInt32 = k.toUInt32 ↔ x = k := by
  constructor
  · intro h
    apply UInt8.toNat_inj.1
    have := congrArg UInt32.toNat h
    simpa using this
  · intro h; rw [h]

theorem run_final (buf : List UInt8) (B : Nat) (hB0 : 0 < B) (hBL : B ≤ buf.length) :
    Sodium.Proofs.Unpad.Inv (cb buf) (zeros buf) B (run (cb buf) B) :=
  run_inv (cb buf) B (zeros buf) (fun j _ => cb_lt buf j)
    (fun j hj hjB => by
      rw [cb_eq buf j (by omega), zeros_zero buf j hj]; rfl)
    (fun hz => by
      have hzl : zeros buf < buf.length := by omega
      rw [cb_eq buf _ hzl]
      intro h
      apply zeros_stop buf hzl
      exact (u8_u32_eq _ 0).1 h)
    B (Nat.le_refl _)

/-- What a call computes, as `unpad_correct` states it. -/
def Post (buf : List UInt8) (B : Nat) (lp : UInt32) (m : Machine) : Prop :=
  match unpad buf B with
  | some n => m.cpu.eax = 0 ∧ wordAt m lp = n.toUInt32
  | none => m.cpu.eax = minusOne

theorem post_of (buf : List UInt8) (B : Nat) (hB0 : 0 < B) (hBL : B ≤ buf.length) (hL : buf.length < 2 ^ 31)
    (lp : UInt32) (m : Machine)
    (heax : m.cpu.eax = (run (cb buf) B).2.1.add 4294967295)
    (hw : wordAt m lp = (buf.length.toUInt32.add 4294967295).sub (run (cb buf) B).2.2) :
    Post buf B lp m := by
  have hinv := run_final buf B hB0 hBL
  unfold Post
  rw [unpad_spec buf B hBL]
  unfold Sodium.Proofs.Unpad.Inv at hinv
  by_cases hz : zeros buf < B
  · rw [dif_pos hz]
    rw [if_neg (by omega)] at hinv
    obtain ⟨_, _, hv, hp⟩ := hinv
    have hzl : zeros buf < buf.length := by omega
    have hcz : (cb buf (zeros buf) = 0x80) ↔ (buf[buf.length - 1 - zeros buf]'(by omega) = 0x80) := by
      rw [cb_eq buf _ hzl]; exact u8_u32_eq _ 0x80
    by_cases h80 : buf[buf.length - 1 - zeros buf]'(by omega) = 0x80
    · rw [if_pos h80]
      rw [if_pos (hcz.2 h80)] at hv hp
      refine ⟨by rw [heax, hv]; rfl, ?_⟩
      rw [hw, hp]
      apply UInt32.toNat_inj.1
      show (buf.length.toUInt32 + 4294967295 - (zeros buf).toUInt32).toNat = _
      rw [UInt32.toNat_sub_of_le, UInt32.toNat_add, toNat_u32 (by omega), toNat_u32 (by omega), toNat_u32 (by omega)]
      · simp only [UInt32.reduceToNat]; omega
      · rw [UInt32.le_iff_toNat_le, UInt32.toNat_add, toNat_u32 (by omega), toNat_u32 (by omega)]
        simp only [UInt32.reduceToNat]; omega
    · rw [if_neg h80]
      rw [if_neg (fun h => h80 (hcz.1 h))] at hv
      rw [heax, hv]; rfl
  · rw [dif_neg hz]
    rw [if_pos (by omega)] at hinv
    rw [heax, hinv]; rfl

/-! ## The whole run -/

theorem returned_of (s : St) (h : s.eip = Image.sym_halt) : returned img s.m = true := by
  unfold returned
  simp [St.m, img, h]

theorem edi0 (bp : UInt32) (L : Nat) (h : bp.toNat + L < 2 ^ 32) (hL : 1 ≤ L) :
    ((bp.add L.toUInt32).add 4294967295).toNat = bp.toNat + (L - 1 - 0) := by
  show ((bp + L.toUInt32) + 4294967295).toNat = _
  rw [UInt32.toNat_add, UInt32.toNat_add, toNat_u32 (by omega)]
  simp only [UInt32.reduceToNat]
  omega

theorem preMem_t (G : ByteArray) (t ebp ebx edi esi y : UInt32) (h : t.toNat + 44 ≤ G.size)
    (ht : t.toNat + 44 < 2 ^ 32) : rdRaw (preMem G t ebp ebx edi esi y) t 4 = 0 := by
  have e4 := tk ht 4 (by decide)
  simp only [UInt32.reduceToNat] at e4
  unfold preMem
  rw [rd_other (by simp only [size_wrBytes, e4]; omega) (by simp only [size_wrBytes]; omega) (by omega),
    rd_self (by simp only [size_wrBytes]; omega)]

set_option maxHeartbeats 2000000 in
theorem unpad_run (c : Caller) (lp bp : UInt32) (buf : List UInt8) (B : Nat) (h : UnpadPre c lp bp buf B) :
    ∃ m1, PRun img (upath B) (c.enter Image.sym_sodium_unpad) m1 ∧
      Returned img (c.enter Image.sym_sodium_unpad) m1 ∧ CalleeSaved (c.enter Image.sym_sodium_unpad) m1 ∧
      Preserved (c.enter Image.sym_sodium_unpad) m1 stackBound (InRange lp 4) ∧ Post buf B lp m1 := by
  have hc := h.1
  obtain ⟨t, ht⟩ : ∃ t, t = c.sp - (24 : Nat).toUInt32 := ⟨_, rfl⟩
  have F : Facts c t lp bp buf B := ht ▸ facts_of c lp bp buf B h
  have hsp : 128 ≤ c.sp.toNat := hc.2.2.2.2.1
  have htn : t.toNat = c.sp.toNat - 24 := by rw [ht]; exact u32_sub (by omega) (by decide)
  have hst := F.st; have hsz := F.sz; have hL := F.BL; have hLm := F.Lmax; have hB0 := F.B0
  have hspt : c.sp = t.add 24 := by
    apply UInt32.toNat_inj.1
    rw [tk (by omega) 24 (by decide)]; simp only [UInt32.reduceToNat]; omega
  let G : SMem := codeMem c hc
  have e0 : c.enter Image.sym_sodium_unpad =
      St.m ⟨G.get, c.regs.eax, c.regs.ecx, c.regs.edx, c.regs.ebx, t.add 24, c.regs.ebp, c.regs.esi,
        c.regs.edi, 0x100D30, efl c.regs.flags, 0⟩ := by
    rw [← hspt]; rfl
  -- the prologue
  obtain ⟨P, ecx1, esi1, F1, hPg, hpre⟩ := pre G c.regs.eax c.regs.ecx c.regs.edx c.regs.ebx t c.regs.ebp
    c.regs.esi c.regs.edi c.regs.flags hsz hst (by have := F.ap; omega)
    (by show 0 < (rdRaw c.mem (t.add 40) 4).toNat; rw [F.a40, toNat_u32 (by omega)]; exact hB0)
    (by show (rdRaw c.mem (t.add 40) 4).toNat ≤ (rdRaw c.mem (t.add 36) 4).toNat
        rw [F.a40, F.a36, toNat_u32 (by omega), toNat_u32 (by omega)]; exact hL)
  have hPm : P.get = preMem c.mem t c.regs.ebp c.regs.ebx c.regs.edi c.regs.esi
      ((rdRaw c.mem (t.add 36) 4).add 4294967295) := hPg
  have hP : Agree P.get c.mem t.toNat (t.toNat + 24) := hPm ▸ preMem_agree _ _ _ _ _ _ _ hst (by omega)
  have hPr := preMem_rd c.mem t c.regs.ebp c.regs.ebx c.regs.edi c.regs.esi
    ((rdRaw c.mem (t.add 36) 4).add 4294967295) hst (by omega)
  rw [← hPm] at hPr
  have hI0 : LoopInv t bp buf P.get 0 (St.m ⟨P.get, 0, ecx1, c.regs.edx, 0, t, 0, esi1,
      ((rdRaw G.get (t.add 32) 4).add (rdRaw G.get (t.add 36) 4)).add 4294967295, 0x100D70, efl F1,
      0 + Nat.toUInt64 30⟩) := by
    refine ⟨P, ecx1, c.regs.edx, esi1, F1, _, _, rfl, by decide, ?_, Agree.refl _ _ _, ?_⟩
    · show (((rdRaw c.mem (t.add 32) 4).add (rdRaw c.mem (t.add 36) 4)).add 4294967295).toNat = _
      rw [F.a32, F.a36]; exact edi0 bp buf.length (by have := F.bL; omega) (by omega)
    · rw [hPm]; exact preMem_t _ _ _ _ _ _ _ hst (by omega)
  -- the loop
  obtain ⟨m1, hL1, hI1⟩ := PRun.loop (img := img) Lbody (LoopInv t bp buf P.get) (B - 1)
    (fun i m hi hI => loop_step F hP i m (by omega) hI) hI0
  -- the last iteration and the epilogue
  obtain ⟨M, ecx, edx, esi, f, edi, ic, rfl, hic, hedi, hA, hpl⟩ := hI1
  have hMs : M.get.size = c.mem.size := hA.1.trans hP.1
  have e40 := tk (t := t) (by omega) 40 (by decide)
  have e28 := tk (t := t) (by omega) 28 (by decide)
  have e24 := tk (t := t) (by omega) 24 (by decide)
  have e4 := tk (t := t) (by omega) 4 (by decide); have e8 := tk (t := t) (by omega) 8 (by decide)
  have e12 := tk (t := t) (by omega) 12 (by decide); have e16 := tk (t := t) (by omega) 16 (by decide)
  have e20 := tk (t := t) (by omega) 20 (by decide)
  simp only [UInt32.reduceToNat] at e40 e28 e24 e4 e8 e12 e16 e20
  have h40 : rdRaw M.get (t.add 40) 4 = B.toUInt32 := (rd4_out hA hP _ (by omega) (by omega)).trans F.a40
  have h28 : rdRaw M.get (t.add 28) 4 = lp := (rd4_out hA hP _ (by omega) (by omega)).trans F.a28
  have h24 : rdRaw M.get (t.add 24) 4 = Image.sym_halt := (rd4_out hA hP _ (by omega) (by omega)).trans F.a24
  have h4 : rdRaw M.get (t.add 4) 4 = buf.length.toUInt32.add 4294967295 := by
    rw [rd4_mid hA _ (by rw [hP.1]; omega) (by omega), hPr.1, F.a36]
  have h8 : rdRaw M.get (t.add 8) 4 = c.regs.esi := by
    rw [rd4_mid hA _ (by rw [hP.1]; omega) (by omega), hPr.2.1]
  have h12 : rdRaw M.get (t.add 12) 4 = c.regs.edi := by
    rw [rd4_mid hA _ (by rw [hP.1]; omega) (by omega), hPr.2.2.1]
  have h16 : rdRaw M.get (t.add 16) 4 = c.regs.ebx := by
    rw [rd4_mid hA _ (by rw [hP.1]; omega) (by omega), hPr.2.2.2.1]
  have h20 : rdRaw M.get (t.add 20) 4 = c.regs.ebp := by
    rw [rd4_mid hA _ (by rw [hP.1]; omega) (by omega), hPr.2.2.2.2]
  have hiN := toNat_i (i := B - 1) (B := B) (by omega) (by omega)
  have hBN : (B.toUInt32).toNat = B := toNat_u32 (by omega)
  obtain ⟨M', ecx', F', hM', hrun⟩ := exit M (run (cb buf) (B - 1)).2.1 ecx edx (B - 1).toUInt32 t
    (run (cb buf) (B - 1)).1 esi edi f ic (by rw [hMs]; exact hsz) (by rw [hMs]; exact hst)
    (by have := F.ap; omega) (by rw [hMs]; have := F.bL; omega) (by have := F.bi; omega) (by omega)
    (by rw [h28, hMs]; exact F.lsz) (by rw [h28]; exact F.li) (by rw [h28]; have := F.ls; omega)
    (by rw [h40, hiN, hBN]; omega) (by rw [h40, hBN]; omega)
  have hc1 : rdRaw M.get edi 1 = cb buf (B - 1) := by
    rw [rd1_out hA hP _ (by have := F.bL; omega) (by have := F.bs; omega)]
    exact byte_eq F (B - 1) (by omega) edi hedi
  rw [hc1, hpl, h24, h16, h20, h8, h12, h28] at hrun
  rw [hc1, hpl, h4, h28] at hM'
  have hB1 : B - 1 + 1 = B := by omega
  have hrs := run_succ buf (B - 1) (cb buf (B - 1)) rfl
  rw [hB1] at hrs
  have hpath := hpre.append (hL1.append hrun)
  rw [← List.append_assoc, ← e0] at hpath
  refine ⟨_, hpath, ⟨returned_of _ rfl, ?_, efl_DF _⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨?_, ?_⟩, ?_⟩
  · show t.add 28 = c.sp + 4
    apply UInt32.toNat_inj.1
    rw [UInt32.toNat_add, e28]
    simp only [UInt32.reduceToNat]; omega
  · show M'.get.size = c.mem.size
    rw [hM', size_wrBytes, size_wrBytes, hMs]
  · intro a ha hw hs
    show memByte M'.get a = memByte c.mem a
    have hlo : (c.sp - (stackBound : Nat).toUInt32).toNat = c.sp.toNat - 128 := u32_sub hsp (by decide)
    have hs' : ¬ (c.sp.toNat - 128 ≤ a.toNat ∧ a.toNat < c.sp.toNat - 128 + 128) := by
      intro hh; apply hs; rw [inRange_iff, show (c.enter Image.sym_sodium_unpad).cpu.esp = c.sp from rfl, hlo]
      exact hh
    have hw' : ¬ (lp.toNat ≤ a.toNat ∧ a.toNat < lp.toNat + 4) := fun hh => hw (inRange_iff.2 hh)
    rw [hM', memByte_wrBytes4_other (by simp only [size_wrBytes]; rw [hMs]; exact F.lsz)
      (by simp only [size_wrBytes]; rw [hMs]; exact ha) (by omega)]
    have hA' := hA.wr4 t (upl (cb buf (B - 1)) (run (cb buf) (B - 1)).2.2 (run (cb buf) (B - 1)).1
      (B - 1).toUInt32) (Nat.le_refl _) (Nat.le_refl _) (by rw [hMs]; omega)
    exact ((hA'.byte a (by rw [hP.1]; exact ha) (by omega)).trans (hP.byte a ha (by omega)))
  · apply post_of buf B hB0 hL hLm lp _
    · show ((run (cb buf) (B - 1)).2.1.lor (ubit (cb buf (B - 1)) (run (cb buf) (B - 1)).2.2
          (run (cb buf) (B - 1)).1)).add 4294967295 = _
      rw [hrs]
    · show rdBytes M'.get lp 4 = _
      rw [hM', rdBytes4_wrBytes4_self (by rw [size_wrBytes, hMs]; exact F.lsz), hrs]

/-! ## The tasks -/

theorem _root_.Sodium.Proofs.unpad_correct : Sodium.Utils.unpad_correct := by
  intro c lenp bufp buf block h
  obtain ⟨m1, hr, hret, hcs, hpres, hpost⟩ := unpad_run c lenp bufp buf block h
  exact Returns.intro hr.run hret hcs hpres hpost

theorem _root_.Sodium.Proofs.unpad_constant_time : Sodium.Utils.unpad_constant_time := by
  intro c c' lenp bufp buf buf' block _ h h'
  obtain ⟨m1, hr, hret, -⟩ := unpad_run c lenp bufp buf block h
  obtain ⟨m1', hr', hret', -⟩ := unpad_run c' lenp bufp buf' block h'
  exact SameTraceG.of_prun hr hr' hret.1 hret'.1

end Sodium.Proofs.Unpad
