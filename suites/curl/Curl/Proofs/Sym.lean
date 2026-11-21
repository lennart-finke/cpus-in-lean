import Curl.Proofs.SymMem
import Curl.Proofs.Flags
import Solutions.Logic.Run
import Solutions.Logic.Step
import Solutions.Exec.Dispatch
import Solutions.Exec.Cbv
import Lean
/-!
# Executing the curl image symbolically with `cbv`

A `cbv` set-up (scoped to `Curl.Proofs.Sym`) that evaluates `execInstr` of a machine `St.m s` whose
memory is a `CMem` (the image at its link address, possibly after stores) and whose registers are
arbitrary terms:

* data accesses inside memory are plain loads and stores (`rdBytes`/`wrBytes`); the side conditions
  are discharged by `omega` from the hypotheses in context (`omegaP?`);
* a store outside the code keeps the memory a `CMem` (`CMem.wr`), a load through stores and frames
  (`Frame` hypotheses) reads the stored value or the older memory;
* code bytes are read from `Image.byte`, also at an address only known to lie in the image, and words
  of the jump tables through `jtRule` (a word that is the same for a range of indices);
* the arithmetic flags read by `jcc`/`setcc` are `cond (pdec P) bit 0` with `P` about `toNat`
  (`Curl.Proofs.Flags`), and `pdec P` is decided by `omega` when the context decides it.

What `omega` cannot decide stays in the result: an undecided `pdec P` is where a proof splits cases.
-/
namespace Curl.Proofs.Sym
open X86 Ssl Solutions.Logic Solutions.Exec Curl.Proofs Curl.Hostcheck Lean Meta

/-! ## EFLAGS -/

theorem efl_and_zero (f k : UInt32) (h2 : (2 : UInt32) &&& k = 0) (h3 : (0x8D5 : UInt32) &&& k = 0) :
    efl f &&& k = 0 := by
  unfold efl
  apply UInt32.toBitVec_inj.1
  have h2' := congrArg UInt32.toBitVec h2
  have h3' := congrArg UInt32.toBitVec h3
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or] at *
  rw [BitVec.and_or_distrib_right, h2',
    show f.toBitVec &&& (0x8D5 : UInt32).toBitVec &&& k.toBitVec =
      f.toBitVec &&& ((0x8D5 : UInt32).toBitVec &&& k.toBitVec) by ac_rfl, h3']
  simp

theorem efl_set (f v mask : UInt32) (hm : mask &&& ~~~0x8D5 = 0) :
    (efl f &&& ~~~mask) ||| (v &&& mask) = efl (mixF f v mask) := by
  unfold efl mixF
  apply UInt32.toBitVec_inj.1
  have hm' := congrArg UInt32.toBitVec hm
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, UInt32.toBitVec_not] at *
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb := congrArg (fun x => BitVec.getLsbD x i) hm'
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_zero, hi,
    decide_true, Bool.true_and] at hb ⊢
  have h2 := congrArg (fun x => BitVec.getLsbD x i)
    (show (2 : UInt32).toBitVec &&& (0x8D5 : UInt32).toBitVec = 0 by decide)
  have hz : ∀ j, (UInt32.toBitVec 0).getLsbD j = false := fun j => by simp
  have hz' : ∀ j, (0 : BitVec 32).getLsbD j = false := fun j => by simp
  rw [BitVec.getLsbD_and, hz'] at h2
  rw [hz] at hb
  cases ha : (2 : UInt32).toBitVec.getLsbD i <;> cases hb2 : (0x8D5 : UInt32).toBitVec.getLsbD i <;>
    cases hmi : mask.toBitVec.getLsbD i <;> cases f.toBitVec.getLsbD i <;> cases v.toBitVec.getLsbD i <;>
    simp_all

theorem efl_set_arith (f v : UInt32) : (efl f &&& ~~~0x8D5) ||| (v &&& 0x8D5) = efl v := by
  rw [efl_set f v 0x8D5 (by decide)]
  unfold efl mixF
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, UInt32.toBitVec_not, BitVec.getLsbD_and,
    BitVec.getLsbD_or, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases (0x8D5 : UInt32).toBitVec.getLsbD i <;> simp

/-- A bit `k` of the arithmetic flags of `efl f` is that of `f`. -/
theorem efl_bit (f k : UInt32) (hk : ∀ i, i < 32 → k.toBitVec.getLsbD i = true →
    (0x8D5 : UInt32).toBitVec.getLsbD i = true ∧ (2 : UInt32).toBitVec.getLsbD i = false) :
    efl f &&& k = f &&& k := by
  unfold efl
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases hki : k.toBitVec.getLsbD i
  · simp
  · obtain ⟨h1, h2⟩ := hk i hi hki
    have h1' : (2261#32).getLsbD i = true := h1
    have h2' : (2#32).getLsbD i = false := h2
    simp [h1', h2']

/-- A bit `k` of `mixF f v m`. -/
theorem mixF_bit (f v m k : UInt32) : mixF f v m &&& k = (f &&& (k &&& ~~~m)) ||| (v &&& (k &&& m)) := by
  unfold mixF
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, UInt32.toBitVec_not, BitVec.getLsbD_and,
    BitVec.getLsbD_or, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases f.toBitVec.getLsbD i <;> cases v.toBitVec.getLsbD i <;> cases m.toBitVec.getLsbD i <;>
    cases k.toBitVec.getLsbD i <;> rfl

section rules
set_option linter.unusedVariables false
theorem efl_TF (f : UInt32) : UInt32.land (efl f) 256 = 0 := efl_and_zero f 256 (by decide) (by decide)
theorem efl_IF (f : UInt32) : UInt32.land (efl f) 512 = 0 := efl_and_zero f 512 (by decide) (by decide)
theorem efl_DF (f : UInt32) : UInt32.land (efl f) 1024 = 0 := efl_and_zero f 1024 (by decide) (by decide)
theorem efl_NT (f : UInt32) : UInt32.land (efl f) 16384 = 0 := efl_and_zero f 16384 (by decide) (by decide)
theorem efl_RF (f : UInt32) : UInt32.land (efl f) 65536 = 0 := efl_and_zero f 65536 (by decide) (by decide)
theorem efl_VM (f : UInt32) : UInt32.land (efl f) 131072 = 0 := efl_and_zero f 131072 (by decide) (by decide)
theorem efl_AC (f : UInt32) : UInt32.land (efl f) 262144 = 0 := efl_and_zero f 262144 (by decide) (by decide)
theorem efl_setArith (f v : UInt32) :
    UInt32.lor (UInt32.land (efl f) 4294965034) (UInt32.land v 2261) = efl v := efl_set_arith f v
theorem efl_setNoCF (f v : UInt32) :
    UInt32.lor (UInt32.land (efl f) 4294965035) (UInt32.land v 2260) = efl (mixF f v 2260) :=
  efl_set f v 2260 (by decide)
theorem efl_setCFOF (f v : UInt32) :
    UInt32.lor (UInt32.land (efl f) 4294965246) (UInt32.land v 2049) = efl (mixF f v 2049) :=
  efl_set f v 2049 (by decide)
theorem efl_CF (f : UInt32) : UInt32.land (efl f) 1 = UInt32.land f 1 := efl_bit f 1 (by decide)
theorem efl_ZF (f : UInt32) : UInt32.land (efl f) 64 = UInt32.land f 64 := efl_bit f 64 (by decide)
theorem efl_SF (f : UInt32) : UInt32.land (efl f) 128 = UInt32.land f 128 := efl_bit f 128 (by decide)
theorem efl_OF (f : UInt32) : UInt32.land (efl f) 2048 = UInt32.land f 2048 := efl_bit f 2048 (by decide)
theorem efl_CZ (f : UInt32) : UInt32.land (efl f) 65 = UInt32.land f 65 := efl_bit f 65 (by decide)
theorem mixF_land (f v m k : UInt32) :
    UInt32.land (mixF f v m) k = UInt32.lor (UInt32.land f (k &&& ~~~m)) (UInt32.land v (k &&& m)) :=
  mixF_bit f v m k
theorem land_zero' (x : UInt32) : UInt32.land x 0 = 0 := UInt32.and_zero
theorem lor_zero' (x : UInt32) : UInt32.lor x 0 = x := UInt32.or_zero
theorem zero_lor' (x : UInt32) : UInt32.lor 0 x = x := UInt32.zero_or
/-- A 32-bit target is never above the flat code segment's limit (`jumpTo`). -/
theorem max_lt_false (t : UInt32) : ((4294967295 : UInt32) < t) = False := by
  apply propext; constructor
  · intro h; rw [UInt32.lt_iff_toNat_lt] at h; have := t.toNat_lt; simp at h; omega
  · intro h; exact h.elim

theorem cond_true' {α : Type} (a b : α) : cond true a b = a := rfl
theorem cond_false' {α : Type} (a b : α) : cond false a b = b := rfl

/-! Results of the ALU -/
theorem addF4_fst (a b : UInt32) : (addF 4 a b 0).1 = UInt32.add a b := Solutions.Exec.addF_fst a b
theorem subF4_fst (a b : UInt32) : (subF 4 a b 0).1 = UInt32.sub a b := Solutions.Exec.subF_fst a b
theorem u64_add_toUInt32 (a b : UInt32) : (a.toUInt64 + b.toUInt64 + (0 : UInt32).toUInt64).toUInt32 = a + b := by
  apply UInt32.toNat_inj.1
  simp only [UInt64.toNat_toUInt32, UInt64.toNat_add, UInt32.toNat_toUInt64, UInt32.toNat_add]
  have := a.toNat_lt; have := b.toNat_lt
  simp
theorem addF1_fst (a b : UInt32) : (addF 1 a b 0).1 = UInt32.land (UInt32.add a b) 255 := by
  simp only [addF, addCore, Sz.mask]
  simp only [show ((1 : UInt8) == 1) = true by decide, ite_true]
  rw [u64_add_toUInt32]; rfl
theorem subF1_fst (a b : UInt32) : (subF 1 a b 0).1 = UInt32.land (UInt32.sub a b) 255 := by
  simp only [subF, subCore, Sz.mask]
  simp only [show ((1 : UInt8) == 1) = true by decide, ite_true, UInt32.sub_zero]
  rfl
theorem logicF_fst' (sz : Sz) (r : UInt32) : (logicF sz r).1 = r := rfl

/-! Flag bits of the ALU, as `cond (pdec P) bit 0` -/
theorem subF_CF (sz : Sz) (a b : UInt32) :
    UInt32.land (subF sz a b 0).2 1 = cond (pdec (a.toNat < b.toNat)) 1 0 := by
  show (subCore sz a b 0).2.pack &&& 1 = _; rw [pack_cf, subCore_cf]
theorem subF4_ZF (a b : UInt32) :
    UInt32.land (subF 4 a b 0).2 64 = cond (pdec (a.toNat = b.toNat)) 64 0 := by
  show (subCore 4 a b 0).2.pack &&& 64 = _; rw [pack_zf, subCore4_zf]
theorem subF1_ZF (a b : UInt32) :
    UInt32.land (subF 1 a b 0).2 64 = cond (pdec ((a.toNat + (2 ^ 32 - b.toNat)) % 256 = 0)) 64 0 := by
  show (subCore 1 a b 0).2.pack &&& 64 = _; rw [pack_zf, subCore1_zf]
theorem subF4_SF (a b : UInt32) :
    UInt32.land (subF 4 a b 0).2 128 = cond (pdec (2 ^ 31 ≤ (a.toNat + (2 ^ 32 - b.toNat)) % 2 ^ 32)) 128 0 := by
  show (subCore 4 a b 0).2.pack &&& 128 = _; rw [pack_sf, subCore4_sf]
theorem subF4_OF (a b : UInt32) :
    UInt32.land (subF 4 a b 0).2 2048 = cond (pdec ((2 ^ 31 ≤ a.toNat ↔ ¬ 2 ^ 31 ≤ b.toNat) ∧
      (2 ^ 31 ≤ a.toNat ↔ ¬ 2 ^ 31 ≤ (a.toNat + (2 ^ 32 - b.toNat)) % 2 ^ 32))) 2048 0 := by
  show (subCore 4 a b 0).2.pack &&& 2048 = _; rw [pack_of, subCore4_of]
theorem subF4_CZ (a b : UInt32) :
    UInt32.land (subF 4 a b 0).2 65 =
      UInt32.lor (cond (pdec (a.toNat < b.toNat)) 1 0) (cond (pdec (a.toNat = b.toNat)) 64 0) := by
  show (subCore 4 a b 0).2.pack &&& 65 = _; rw [pack_cz, subCore_cf, subCore4_zf]; rfl
theorem subF1_CZ (a b : UInt32) :
    UInt32.land (subF 1 a b 0).2 65 =
      UInt32.lor (cond (pdec (a.toNat < b.toNat)) 1 0)
        (cond (pdec ((a.toNat + (2 ^ 32 - b.toNat)) % 256 = 0)) 64 0) := by
  show (subCore 1 a b 0).2.pack &&& 65 = _; rw [pack_cz, subCore_cf, subCore1_zf]; rfl
theorem logicF_CF (sz : Sz) (r : UInt32) : UInt32.land (logicF sz r).2 1 = 0 := by
  show (logicCore sz r).2.pack &&& 1 = _; rw [pack_cf]; rfl
theorem logicF_OF (sz : Sz) (r : UInt32) : UInt32.land (logicF sz r).2 2048 = 0 := by
  show (logicCore sz r).2.pack &&& 2048 = _; rw [pack_of]; rfl
theorem logicF_ZF (sz : Sz) (r : UInt32) :
    UInt32.land (logicF sz r).2 64 = cond (pdec (r.toNat = 0)) 64 0 := by
  show (logicCore sz r).2.pack &&& 64 = _; rw [pack_zf, logicCore_zf]
theorem logicF_CZ (sz : Sz) (r : UInt32) :
    UInt32.land (logicF sz r).2 65 = cond (pdec (r.toNat = 0)) 64 0 := by
  show (logicCore sz r).2.pack &&& 65 = _; rw [pack_cz, logicCore_zf]
  show cond false 1 0 ||| _ = _; exact UInt32.zero_or
theorem logicF4_SF (r : UInt32) : UInt32.land (logicF 4 r).2 128 = cond (pdec (2 ^ 31 ≤ r.toNat)) 128 0 := by
  show (logicCore 4 r).2.pack &&& 128 = _; rw [pack_sf, logicCore4_sf]
theorem logicF1_SF (r : UInt32) : UInt32.land (logicF 1 r).2 128 = cond (pdec (r.toNat / 128 % 2 = 1)) 128 0 := by
  show (logicCore 1 r).2.pack &&& 128 = _; rw [pack_sf, logicCore1_sf]
theorem addF4_ZF (a b : UInt32) :
    UInt32.land (addF 4 a b 0).2 64 = cond (pdec ((a.toNat + b.toNat) % 2 ^ 32 = 0)) 64 0 := by
  show (addCore 4 a b 0).2.pack &&& 64 = _; rw [pack_zf, addCore_zf4]
theorem addF4_CF (a b : UInt32) :
    UInt32.land (addF 4 a b 0).2 1 = cond (pdec (2 ^ 32 ≤ a.toNat + b.toNat)) 1 0 := by
  show (addCore 4 a b 0).2.pack &&& 1 = _; rw [pack_cf, addCore_cf4]
end rules

/-! The flag facts behind opaque names, so that `cbv` leaves them alone (their definitions are
unfolded only by `xomega`). -/
def PltU (a b : UInt32) : Prop := a.toNat < b.toNat
def PeqU (a b : UInt32) : Prop := a.toNat = b.toNat
def PeqB (a b : UInt32) : Prop := (a.toNat + (2 ^ 32 - b.toNat)) % 256 = 0
def PsfU (a b : UInt32) : Prop := 2 ^ 31 ≤ (a.toNat + (2 ^ 32 - b.toNat)) % 2 ^ 32
def PofU (a b : UInt32) : Prop := (2 ^ 31 ≤ a.toNat ↔ ¬ 2 ^ 31 ≤ b.toNat) ∧
  (2 ^ 31 ≤ a.toNat ↔ ¬ 2 ^ 31 ≤ (a.toNat + (2 ^ 32 - b.toNat)) % 2 ^ 32)
def PzU (r : UInt32) : Prop := r.toNat = 0
def Psf4 (r : UInt32) : Prop := 2 ^ 31 ≤ r.toNat
def Psf1 (r : UInt32) : Prop := r.toNat / 128 % 2 = 1
def PaddZ (a b : UInt32) : Prop := (a.toNat + b.toNat) % 2 ^ 32 = 0
def PaddC (a b : UInt32) : Prop := 2 ^ 32 ≤ a.toNat + b.toNat
instance (a b : UInt32) : Decidable (PltU a b) := by unfold PltU; infer_instance
instance (a b : UInt32) : Decidable (PeqU a b) := by unfold PeqU; infer_instance
instance (a b : UInt32) : Decidable (PeqB a b) := by unfold PeqB; infer_instance
instance (a b : UInt32) : Decidable (PsfU a b) := by unfold PsfU; infer_instance
instance (a b : UInt32) : Decidable (PofU a b) := by unfold PofU; infer_instance
instance (r : UInt32) : Decidable (PzU r) := by unfold PzU; infer_instance
instance (r : UInt32) : Decidable (Psf4 r) := by unfold Psf4; infer_instance
instance (r : UInt32) : Decidable (Psf1 r) := by unfold Psf1; infer_instance
instance (a b : UInt32) : Decidable (PaddZ a b) := by unfold PaddZ; infer_instance
instance (a b : UInt32) : Decidable (PaddC a b) := by unfold PaddC; infer_instance

theorem pdec_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : pdec P = pdec Q := pdec_congr h

theorem subF_CF' (sz : Sz) (a b : UInt32) : UInt32.land (subF sz a b 0).2 1 = cond (pdec (PltU a b)) 1 0 := by
  rw [subF_CF]; rfl
theorem subF4_ZF' (a b : UInt32) : UInt32.land (subF 4 a b 0).2 64 = cond (pdec (PeqU a b)) 64 0 := by
  rw [subF4_ZF]; rfl
theorem subF1_ZF' (a b : UInt32) : UInt32.land (subF 1 a b 0).2 64 = cond (pdec (PeqB a b)) 64 0 := by
  rw [subF1_ZF]; rfl
theorem subF4_SF' (a b : UInt32) : UInt32.land (subF 4 a b 0).2 128 = cond (pdec (PsfU a b)) 128 0 := by
  rw [subF4_SF]; rfl
theorem subF4_OF' (a b : UInt32) : UInt32.land (subF 4 a b 0).2 2048 = cond (pdec (PofU a b)) 2048 0 := by
  rw [subF4_OF]; rfl
theorem subF4_CZ' (a b : UInt32) : UInt32.land (subF 4 a b 0).2 65 =
    UInt32.lor (cond (pdec (PltU a b)) 1 0) (cond (pdec (PeqU a b)) 64 0) := by
  rw [subF4_CZ]; rfl
theorem subF1_CZ' (a b : UInt32) : UInt32.land (subF 1 a b 0).2 65 =
    UInt32.lor (cond (pdec (PltU a b)) 1 0) (cond (pdec (PeqB a b)) 64 0) := by
  rw [subF1_CZ]; rfl
theorem logicF_ZF' (sz : Sz) (r : UInt32) : UInt32.land (logicF sz r).2 64 = cond (pdec (PzU r)) 64 0 := by
  rw [logicF_ZF]; rfl
theorem logicF_CZ' (sz : Sz) (r : UInt32) : UInt32.land (logicF sz r).2 65 = cond (pdec (PzU r)) 64 0 := by
  rw [logicF_CZ]; rfl
theorem logicF4_SF' (r : UInt32) : UInt32.land (logicF 4 r).2 128 = cond (pdec (Psf4 r)) 128 0 := by
  rw [logicF4_SF]; rfl
theorem logicF1_SF' (r : UInt32) : UInt32.land (logicF 1 r).2 128 = cond (pdec (Psf1 r)) 128 0 := by
  rw [logicF1_SF]; rfl
theorem addF4_ZF' (a b : UInt32) : UInt32.land (addF 4 a b 0).2 64 = cond (pdec (PaddZ a b)) 64 0 := by
  rw [addF4_ZF]; rfl
theorem addF4_CF' (a b : UInt32) : UInt32.land (addF 4 a b 0).2 1 = cond (pdec (PaddC a b)) 1 0 := by
  rw [addF4_CF]; rfl

/-! ## Byte registers and sign extension -/

theorem lor_land_255 (x v : UInt32) :
    UInt32.land (UInt32.lor (UInt32.land x 4294967040) (UInt32.land v 255)) 255 = UInt32.land v 255 := by
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  show ((x &&& 4294967040 ||| v &&& 255) &&& 255 : UInt32).toBitVec.getLsbD i = (v &&& 255 : UInt32).toBitVec.getLsbD i
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, BitVec.getLsbD_and, BitVec.getLsbD_or]
  have h1 : ∀ j, j < 32 → (UInt32.toBitVec 4294967040).getLsbD j = decide (8 ≤ j) := by decide
  have h2 : ∀ j, j < 32 → (UInt32.toBitVec 255).getLsbD j = decide (j < 8) := by decide
  rw [h1 i hi, h2 i hi]
  by_cases h : i < 8
  · simp [h, show ¬ 8 ≤ i by omega]
  · simp [h]

theorem xor_self' (x : UInt32) : UInt32.xor x x = 0 := UInt32.xor_self (a := x)
theorem land_self' (x : UInt32) : UInt32.land x x = x := UInt32.and_self (a := x)
theorem lor_self' (x : UInt32) : UInt32.lor x x = x := UInt32.or_self (a := x)

theorem land_land_255 (v : UInt32) : UInt32.land (UInt32.land v 255) 255 = UInt32.land v 255 := by
  show (v &&& 255 &&& 255 : UInt32) = v &&& 255
  rw [UInt32.and_assoc]; rfl

/-- `sext 1`, opaque; it is evaluated on literals by `cbvSextB`. -/
def sextB (x : UInt32) : UInt32 := sext 1 x

theorem sext_one (x : UInt32) : sext 1 x = sextB x := rfl

theorem sextB_land (x : UInt32) : UInt32.land (sextB x) 255 = UInt32.land x 255 := by
  show (sext 1 x &&& 255 : UInt32) = x &&& 255
  unfold sext
  simp only [show ((1 : UInt8) == 1) = true by decide, ite_true]
  split
  · apply UInt32.toBitVec_inj.1
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, BitVec.getLsbD_and, BitVec.getLsbD_or]
    have h1 : ∀ j, j < 32 → (UInt32.toBitVec 4294967040).getLsbD j = decide (8 ≤ j) := by decide
    have h2 : ∀ j, j < 32 → (UInt32.toBitVec 255).getLsbD j = decide (j < 8) := by decide
    rw [h1 i hi, h2 i hi]
    by_cases h : i < 8
    · simp [h, show ¬ 8 ≤ i by omega]
    · simp [h]
  · rw [UInt32.and_assoc]; rfl

/-! ## The discharger -/

theorem toNat_uadd (a b : UInt32) : (UInt32.add a b).toNat = (a.toNat + b.toNat) % 2 ^ 32 :=
  UInt32.toNat_add a b
theorem toNat_usub (a b : UInt32) : (UInt32.sub a b).toNat = (a.toNat + (2 ^ 32 - b.toNat)) % 2 ^ 32 := by
  show (a - b).toNat = _; rw [UInt32.toNat_sub]; omega
theorem toNat_land255 (x : UInt32) : (UInt32.land x 255).toNat = x.toNat % 256 := by
  show (x &&& 255).toNat = _
  rw [UInt32.toNat_and, show (255 : UInt32).toNat = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
theorem toNat_land15 (x : UInt32) : (UInt32.land x 15).toNat = x.toNat % 16 := by
  show (x &&& 15).toNat = _
  rw [UInt32.toNat_and, show (15 : UInt32).toNat = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
theorem toNat_landFFFF (x : UInt32) : (UInt32.land x 65535).toNat = x.toNat % 65536 := by
  show (x &&& 65535).toNat = _
  rw [UInt32.toNat_and, show (65535 : UInt32).toNat = 2 ^ 16 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
theorem toNat_xor_self (x : UInt32) : (UInt32.xor x x).toNat = 0 := by
  rw [xor_self']; rfl
theorem toNat_u8u32 (x : UInt8) : x.toUInt32.toNat = x.toNat := UInt8.toNat_toUInt32 x
theorem toNat_u32u8 (x : UInt32) : x.toUInt8.toNat = x.toNat % 256 := UInt32.toNat_toUInt8 x
theorem toNat_u64add (a b : UInt64) : (UInt64.add a b).toNat = (a.toNat + b.toNat) % 2 ^ 64 :=
  UInt64.toNat_add a b
theorem toNat_shr8 (x : UInt32) : (UInt32.shiftRight x 8).toNat = x.toNat / 256 := by
  have := UInt32.toNat_shiftRight x 8
  exact this.trans (by simp [Nat.shiftRight_eq_div_pow])
theorem toNat_lor_byte (x v : UInt32) :
    (UInt32.lor (UInt32.land x 4294967040) (UInt32.land v 255)).toNat = x.toNat / 256 * 256 + v.toNat % 256 := by
  show ((x &&& 4294967040) ||| (v &&& 255) : UInt32).toNat = _
  have hd : ((x &&& 4294967040) ||| (v &&& 255) : UInt32) = (x &&& 4294967040) + (v &&& 255) := by
    apply UInt32.toBitVec_inj.1
    simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, UInt32.toBitVec_add]
    rw [BitVec.add_eq_or_of_and_eq_zero]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero]
    have h1 : ∀ j, j < 32 → (UInt32.toBitVec 4294967040).getLsbD j = decide (8 ≤ j) := by decide
    have h2 : ∀ j, j < 32 → (UInt32.toBitVec 255).getLsbD j = decide (j < 8) := by decide
    rw [h1 i hi, h2 i hi]
    by_cases h : i < 8
    · simp [show ¬ 8 ≤ i by omega]
    · simp [h]
  rw [hd, UInt32.toNat_add, UInt32.toNat_and, UInt32.toNat_and,
    show (255 : UInt32).toNat = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  have e : x.toNat &&& (4294967040 : UInt32).toNat = x.toNat / 256 * 256 := by
    have hx := x.toNat_lt
    rw [show (4294967040 : UInt32).toNat = 4294967040 from rfl, show (256 : Nat) = 2 ^ 8 from rfl]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
    by_cases hj : 8 ≤ j
    · rw [show j - 8 + 8 = j by omega]
      by_cases hj2 : j < 32
      · have : (4294967040 : Nat).testBit j = true := by
          have : ∀ k, k < 32 → 8 ≤ k → (4294967040 : Nat).testBit k = true := by decide
          exact this j hj2 hj
        simp [this, hj]
      · have h0 : x.toNat.testBit j = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx
          (Nat.pow_le_pow_right (by decide) (by omega)))
        simp [h0]
    · have : (4294967040 : Nat).testBit j = false := by
        have : ∀ k, k < 8 → (4294967040 : Nat).testBit k = false := by decide
        exact this j (by omega)
      simp [this, hj]
  rw [e]
  have hx := x.toNat_lt
  have : x.toNat / 256 * 256 + x.toNat % 256 = x.toNat := Nat.div_add_mod' x.toNat 256
  omega

/-- The rewriting `xomega` does before `omega`. -/
macro "xomega_simp" : tactic =>
  `(tactic| simp only [toNat_uadd, toNat_usub, toNat_land255, toNat_land15, toNat_landFFFF, toNat_u8u32,
      toNat_u32u8, toNat_u64add, toNat_xor_self, PltU, PeqU, PeqB, PsfU, PofU, PzU, Psf4, Psf1, PaddZ, PaddC, toNat_shr8, toNat_lor_byte, UInt32.toNat_add, UInt32.toNat_sub,
      UInt64.toNat_add, UInt32.reduceToNat, UInt64.reduceToNat, UInt8.reduceToNat, ramTop,
      CMem.wr_size, size_wrBytes, Nat.reducePow, or_true, true_or, and_true,
      true_and, or_false, false_or, not_true, not_false_eq_true] at *)

/-- The subterms of `e` satisfying `p`. -/
partial def collectApps (p : Expr → Bool) (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc := if p e then acc.push e else acc
  match e with
  | .app f a => collectApps p a (collectApps p f acc)
  | .lam _ t b _ => collectApps p b (collectApps p t acc)
  | .forallE _ t b _ => collectApps p b (collectApps p t acc)
  | .letE _ t v b _ => collectApps p b (collectApps p v (collectApps p t acc))
  | .mdata _ b => collectApps p b acc
  | .proj _ _ b => collectApps p b acc
  | _ => acc

/-- Bounds of the `toNat` atoms in the goal and the hypotheses. -/
elab "xbounds" : tactic => Elab.Tactic.withMainContext do
  let g ← Elab.Tactic.getMainGoal
  let mut ts : Array Expr := #[(← g.getType)]
  for d in (← getLCtx) do
    unless d.isImplementationDetail do
      if ← isProp d.type then ts := ts.push (← instantiateMVars d.type)
  let mut seen : Std.HashSet Expr := {}
  let mut facts : Array (Name × Expr × Expr) := #[]
  for t in ts do
    for s in collectApps (fun e => e.isAppOfArity ``UInt32.toNat 1 || e.isAppOfArity ``UInt8.toNat 1 ||
        e.isAppOfArity ``UInt64.toNat 1) t #[] do
      if seen.contains s then continue
      seen := seen.insert s
      let x := s.appArg!
      if x.hasLooseBVars then continue
      let (lem, bound) :=
        if s.isAppOfArity ``UInt32.toNat 1 then (``UInt32.toNat_lt, 2 ^ 32)
        else if s.isAppOfArity ``UInt8.toNat 1 then (``UInt8.toNat_lt, 2 ^ 8)
        else (``UInt64.toNat_lt, 2 ^ 64)
      let pf := mkApp (mkConst lem) x
      let ty ← mkLT s (mkNatLit bound)
      facts := facts.push (`hb, ty, pf)
  let hs := facts.map fun (n, ty, pf) => { userName := n, type := ty, value := pf : Hypothesis }
  let (_, g') ← g.assertHypotheses hs
  Elab.Tactic.replaceMainGoal [g']

macro "xomega" : tactic => `(tactic| ((try xomega_simp) <;> xbounds <;> omega))

theorem rdRaw1_lt (m : ByteArray) (a : UInt32) : (rdRaw m a 1).toNat < 256 := by
  show (rdBytes m a 1).toNat < 256
  by_cases h : a.toNat + 1 ≤ m.size
  · have e : rdBytes m a 1 = (m.get! a.toNat).toUInt32 := by unfold rdBytes; simp [h]
    rw [e, UInt8.toNat_toUInt32]; exact UInt8.toNat_lt _
  · have e : rdBytes m a 1 = rdBytes.go m a.toNat 1 0 := by unfold rdBytes; simp [h]
    rw [e]
    simp only [rdBytes.go]
    split
    · have e0 : ShiftLeft.shiftLeft (m.get! a.toNat).toUInt32 (0 : UInt32) = (m.get! a.toNat).toUInt32 :=
        UInt32.shiftLeft_zero
      simp [e0]; exact UInt8.toNat_lt _
    · decide

namespace Discharge

/-- Prove `P` by `xomega` in the current context (only the hypotheses connected to the variables of
`P`), without error recovery; `none` if that fails or leaves a hole. -/
initialize omegaCache : IO.Ref (Std.HashMap Expr (Option Expr)) ← IO.mkRef {}

/-- Forget the cached `omega` results (they are valid in one local context only). -/
def resetOmegaCache : MetaM Unit := omegaCache.set {}

def omegaCore0? (P : Expr) : MetaM (Option Expr) := do
  let g ← mkFreshExprMVar P
  let msgs := (← getThe Core.State).messages
  let P ← instantiateMVars P
  -- the connected component of the variables of `P` among the propositional hypotheses
  let lctx ← getLCtx
  let mut props : Array (FVarId × Array FVarId) := #[]
  for d in lctx do
    if d.isImplementationDetail then continue
    unless ← isProp d.type do continue
    let vs := (collectFVars {} (← instantiateMVars d.type)).fvarIds
    props := props.push (d.fvarId, vs)
  let mut vars : Std.HashSet FVarId := {}
  for v in (collectFVars {} P).fvarIds do vars := vars.insert v
  let mut keep : Std.HashSet FVarId := {}
  let mut changed := true
  while changed do
    changed := false
    for (h, vs) in props do
      if keep.contains h then continue
      let interesting := vs.any fun v => vars.contains v
      if interesting || vs.isEmpty then
        keep := keep.insert h
        changed := true
        for v in vs do
          let t ← whnfR (← inferType (mkFVar v))
          unless t.isAppOf ``CodeMem do vars := vars.insert v
  let drop := props.filterMap fun (h, _) => if keep.contains h then none else some h
  let mv ← g.mvarId!.tryClearMany drop
  let ok ← try
      let gs ← Elab.Term.TermElabM.run' (Elab.Term.withoutErrToSorry
        (Elab.Tactic.run mv (Elab.Tactic.withoutRecover (Elab.Tactic.evalTactic (← `(tactic| xomega))))))
      pure gs.isEmpty
    catch ex =>
      let hs ← mv.withContext do
        let lc ← getLCtx
        let mut out : Array MessageData := #[]
        for d in lc do
          unless d.isImplementationDetail do out := out.push m!"{d.userName} : {d.type}"
        pure out
      trace[Meta.Tactic.cbv.rewrite] "OMEGAFAIL {P}: {ex.toMessageData}\nCTX {hs}"
      pure false
  modifyThe Core.State fun st => { st with messages := msgs }
  unless ok do return none
  let pf ← instantiateMVars g
  if pf.hasExprMVar || pf.hasSyntheticSorry then return none
  return some pf

/-- `omegaCore0?` with the store proofs inside `P` replaced by local hypotheses (so that `P` does not
depend on the hypotheses `omega`'s preprocessing rewrites). -/
def omegaCore? (P : Expr) : MetaM (Option Expr) := do
  let P ← instantiateMVars P
  let oks := collectApps (fun e => e.isAppOfArity ``CMem.wr 5) P #[] |>.map (·.getArg! 4)
  let oks := oks.foldl (fun acc o => if acc.contains o then acc else acc.push o) #[]
  if oks.isEmpty then return ← omegaCore0? P
  let tys ← oks.mapM inferType
  let decls := (List.range oks.size).toArray.map fun i => ((`hok).appendIndexAfter i, fun _ => pure tys[i]!)
  withLocalDeclsD decls fun xs => do
    let mut P' := P
    for i in [0:oks.size] do
      P' := P'.replace fun e => if e == oks[i]! then some xs[i]! else none
    let some pf ← omegaCore0? P' | return none
    let lam ← mkLambdaFVars xs pf
    return some (mkAppN lam oks).headBeta

def omegaP? (P : Expr) : MetaM (Option Expr) := do
  let P ← instantiateMVars P
  if let some r := (← omegaCache.get).get? P then return r
  -- a closed decidable fact is decided by evaluation
  let r ← if !P.hasFVar && !(P.find? (fun t => t.isConstOf ``Image.byte)).isSome then
      (try
        let v ← withTransparency .all <| whnf (← mkDecide P)
        if v.isConstOf ``Bool.true then pure (some (← mkDecideProof P)) else pure none
      catch _ => pure none)
    else pure none
  let r ← match r with
    | some pf => pure (some pf)
    | none => omegaCore? P
  omegaCache.modify (·.insert P r)
  return r

/-- Field `fieldName` of the structure literal `e`, reduced. -/
def field (e : Expr) (structName fieldName : Name) : MetaM Expr := do
  let some idx := (getStructureFields (← getEnv) structName).idxOf? fieldName
    | throwError "no field {fieldName}"
  whnfCore (Expr.proj structName idx e)

/-- `Eq.refl` at the elaborated equation `stx`, left to the kernel to check. -/
def reflOf (stx : Term) : MetaM (Option Expr) := do
  try
    let ty ← Elab.Term.TermElabM.run' do
      let e ← Elab.Term.elabTerm stx (some (mkSort .zero))
      Elab.Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    let some (_, a, _) := ty.eq? | return none
    return some (← mkExpectedTypeHint (← mkEqRefl a) ty)
  catch _ => return none

def elabPf (stx : Term) : MetaM (Option Expr) := do
  try
    let e ← Elab.Term.TermElabM.run' do
      let e ← Elab.Term.elabTerm stx none
      Elab.Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    if e.hasExprMVar then return none
    return some e
  catch _ => return none

/-- A literal natural number in any of the usual forms. -/
def natLit? (n : Expr) : Option Nat :=
  match (Sym.getNatValue? n).run with
  | some v => some v
  | none =>
    if n.isAppOfArity ``UInt8.toUInt32 1 then (Sym.getNatValue? n.appArg!).run
    else none

end Discharge
open Discharge

theorem cpl_zero (c : Cpu) (f : UInt32) (h1 : c.cr0 = 17) (h2 : c.eflags = efl f) (h3 : c.cs.sel = 8) :
    c.cpl = 0 := by
  have hv := efl_VM f
  simp only [Cpu.cpl, Cpu.pe, Cpu.vm86, h1, h2, h3, Flag.VM, CR0.PE]
  rw [show efl f &&& 131072 = UInt32.land (efl f) 131072 from rfl, hv]
  decide

theorem flatM_intro (m : Machine) (h1 : m.cpu.cr0 &&& CR0.PG = 0) (h2 : m.cpu.npOn = false)
    (h3 : m.cpu.bpOn = false) (h4 : m.tso = none) (h5 : m.apic.mmio = 0xFEE00000) (h6 : m.watch = #[]) :
    FlatM m := ⟨h1, h2, h3, h4, h5, h6⟩

theorem flatSeg_intro (sr : SegReg) (h1 : sr.base = 0) (h2 : sr.limit = 0xFFFFFFFF) (h3 : sr.attr = 0xC093) :
    FlatSeg sr := ⟨h1, h2, h3⟩

/-- The proofs that the machine literal `m` is flat at CPL 0 with segment `s` flat, and that the
access of `n` bytes at `off` is inside memory below `ramTop`. -/
def accessProofs (m s off n : Expr) : MetaM (Option (Array Expr)) := do
  let some nv := natLit? n | return none
  let n := toExpr nv.toUInt32
  unless nv == 1 || nv == 2 || nv == 4 do return none
  let cpu ← field m ``Machine `cpu
  let ef ← field cpu ``Cpu `eflags
  unless ef.isAppOfArity ``efl 1 do return none
  let f := ef.appArg!
  let mS ← Elab.Term.TermElabM.run' (Elab.Term.exprToSyntax m)
  let sS ← Elab.Term.TermElabM.run' (Elab.Term.exprToSyntax s)
  let fS ← Elab.Term.TermElabM.run' (Elab.Term.exprToSyntax f)
  let nS ← Elab.Term.TermElabM.run' (Elab.Term.exprToSyntax n)
  let some f1 ← reflOf (← `(($mS).cpu.cr0 &&& CR0.PG = 0)) | return none
  let some f2 ← reflOf (← `(($mS).cpu.npOn = false)) | return none
  let some f3 ← reflOf (← `(($mS).cpu.bpOn = false)) | return none
  let some f4 ← reflOf (← `(($mS).tso = none)) | return none
  let some f5 ← reflOf (← `(($mS).apic.mmio = 0xFEE00000)) | return none
  let some f6 ← reflOf (← `(($mS).watch = #[])) | return none
  let hflat := mkAppN (mkConst ``flatM_intro) #[m, f1, f2, f3, f4, f5, f6]
  let some c1 ← reflOf (← `(($mS).cpu.cr0 = 17)) | return none
  let some c2 ← reflOf (← `(($mS).cpu.eflags = efl $fS)) | return none
  let some c3 ← reflOf (← `(($mS).cpu.cs.sel = 8)) | return none
  let hcpl := mkAppN (mkConst ``cpl_zero) #[cpu, f, c1, c2, c3]
  let some s1 ← reflOf (← `((($mS).cpu.getSeg $sS).base = 0)) | return none
  let some s2 ← reflOf (← `((($mS).cpu.getSeg $sS).limit = 0xFFFFFFFF)) | return none
  let some s3 ← reflOf (← `((($mS).cpu.getSeg $sS).attr = 0xC093)) | return none
  let hs := mkAppN (mkConst ``flatSeg_intro) #[mkApp2 (mkConst ``Cpu.getSeg) (mkApp (mkConst ``Machine.cpu) m) s, s1, s2, s3]
  let some hn ← elabPf (← `((by decide : $nS = 1 ∨ $nS = 2 ∨ $nS = 4))) | return none
  let mem ← field m ``Machine `mem
  let size := mkApp (mkConst ``ByteArray.size) mem
  let lhs ← mkAdd (mkApp (mkConst ``UInt32.toNat) off) (mkApp (mkConst ``UInt32.toNat) n)
  let some hr ← omegaP? (← mkLE lhs size) | do
    trace[Meta.Tactic.cbv.rewrite] "access out of range? {lhs} ≤ {size}"
    return none
  let some hm ← omegaP? (← mkLE size (mkConst ``ramTop)) | return none
  return some #[hflat, hcpl, hs, hn, hr, hm]

attribute [scoped cbv_opaque] Image.byte PltU PeqU PeqB PsfU PofU PzU Psf4 Psf1 PaddZ PaddC EStateM.bind X86.eaOff efl mixF pdec sextB UInt32.add UInt32.sub UInt32.mul UInt32.land UInt32.lor
  UInt32.xor UInt32.shiftLeft UInt32.shiftRight UInt32.complement UInt64.add UInt64.sub UInt64.land UInt64.lor
  CMem.wr StOk Array.replicate X86.cmosInit X86.rdMem X86.wrMem X86.addF X86.subF X86.logicF
  X86.imulCore X86.rdBytes X86.wrBytes X86.opInfoTable X86.execTable rdRaw CodeMem.get Image.bytes

attribute [scoped cbv_eval] efl_TF efl_IF efl_DF efl_NT efl_RF efl_VM efl_AC efl_setArith efl_setNoCF
  efl_setCFOF efl_CF efl_ZF efl_SF efl_OF efl_CZ mixF_land land_zero' lor_zero' zero_lor' max_lt_false
  addF4_fst subF4_fst addF1_fst subF1_fst logicF_fst'
  lor_land_255 land_land_255 sext_one sextB_land
  Solutions.Logic.opInfoTable_get Solutions.Logic.execTable_get

/-! ## Simprocs -/

/-- `rdMem` of a flat machine inside memory: `rdBytes`. -/
scoped cbv_simproc cbv_eval xRdMem (rdMem _ _ _ _ _ _) := fun e => do
  let_expr rdMem s off n w al m := e | return .rfl
  let some hs ← accessProofs m s off n | return .rfl
  let pf ← mkAppM ``rdMem_flat (hs ++ #[w, al])
  let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
  let rhs ← Sym.share rhs
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

/-- `wrMem` of a flat machine inside memory: `wrBytes`. -/
scoped cbv_simproc cbv_eval xWrMem (wrMem _ _ _ _ _ _) := fun e => do
  let_expr wrMem s off n v al m := e | return .rfl
  let some hs ← accessProofs m s off n | return .rfl
  let pf ← mkAppM ``wrMem_flat (hs ++ #[v, al])
  let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
  let rhs ← Sym.share rhs
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

theorem rdBytes_rdRaw (m : ByteArray) (a n : UInt32) : rdBytes m a n = rdRaw m a n := rfl

/-- The code byte at a symbolic address, opaque to `cbv`. -/
def codeB (a : UInt32) : UInt8 := Image.byte (a.toNat - 0x100000)

theorem rdBytes_codeB (g : CMem) (a : UInt32) (h1 : 0x100000 ≤ a.toNat) (h2 : a.toNat < 0x100000 + 3971) :
    rdBytes g.get a 1 = (codeB a).toUInt32 := rdBytes_code1 g a h1 h2

attribute [scoped cbv_opaque] codeB UInt8.toUInt32

/-- A jump-table entry: for every index `j` in `[lo, hi]`, the code word at `T + 4j` is `v`. -/
structure JT where
  T : Nat
  lo : Nat
  hi : Nat
  v : Nat
  lem : Name

initialize jtExt : SimplePersistentEnvExtension JT (Array JT) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := fun as => as.foldl (· ++ ·) #[] }

/-- Loads from a `CMem`: code bytes and jump-table words, otherwise the opaque `rdRaw`. -/
scoped cbv_simproc cbv_eval xRdCode (rdBytes (CodeMem.get _) _ _) := fun e => do
  let_expr rdBytes mem a n := e | return .rfl
  let_expr CodeMem.get _ _ _ G := mem | return .rfl
  let some nv := natLit? n | return .rfl
  let toNat (x : Expr) := mkApp (mkConst ``UInt32.toNat) x
  if nv == 1 then
    let lo ← mkLE (mkNatLit 0x100000) (toNat a)
    let hi ← mkLT (toNat a) (mkNatLit (0x100000 + 3971))
    if let some av := natLit? a then
      if 0x100000 ≤ av && av < 0x100000 + 3971 then
        let some h1 ← omegaP? lo | return .rfl
        let some h2 ← omegaP? hi | return .rfl
        let pf := mkAppN (mkConst ``rdBytes_code1) #[G, a, h1, h2]
        let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
        return .step (← Sym.share rhs) pf
    else
      if let some h1 ← omegaP? lo then
        if let some h2 ← omegaP? hi then
          let pf := mkAppN (mkConst ``rdBytes_codeB) #[G, a, h1, h2]
          let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
          return .step (← Sym.share rhs) pf
  if nv == 4 && (natLit? a).isNone then
    for jt in jtExt.getState (← getEnv) do
      let P1 ← mkLE (mkNatLit (jt.T + 4 * jt.lo)) (toNat a)
      let P2 ← mkLE (toNat a) (mkNatLit (jt.T + 4 * jt.hi))
      let P3 ← mkEq (← mkAppM ``HMod.hMod #[← mkSub (toNat a) (mkNatLit jt.T), mkNatLit 4]) (mkNatLit 0)
      let some h1 ← omegaP? P1 | continue
      let some h2 ← omegaP? P2 | continue
      let some h3 ← omegaP? P3 | continue
      let pf := mkAppN (mkConst jt.lem) #[G, a, h1, h2, h3]
      let some (_, _, rhs) := (← inferType pf).eq? | continue
      return .step (← Sym.share rhs) pf
  let rhs := mkApp3 (mkConst ``rdRaw) mem a n
  return .step rhs (mkApp3 (mkConst ``rdBytes_rdRaw) mem a n)

/-- A store outside the code keeps the memory a `CMem` (`CMem.wr`). -/
scoped cbv_simproc cbv_eval xWr (wrBytes (CodeMem.get _) _ _ _) := fun e => do
  let_expr wrBytes mem a n v := e | return .rfl
  let_expr CodeMem.get _ _ _ G := mem | return .rfl
  let some nv := natLit? n | return .rfl
  unless nv == 1 || nv == 2 || nv == 4 do return .rfl
  let toNat (x : Expr) := mkApp (mkConst ``UInt32.toNat) x
  let gmem := mkApp4 (mkConst ``CodeMem.mem) (mkConst ``Image.base) (mkConst ``Image.size) (mkConst ``Image.byte) G
  let P := mkApp3 (mkConst ``StOk) gmem a n
  -- a hypothesis `StOk _ a n` in context
  let mut hyp : Option Expr := none
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if (← instantiateMVars d.type).isAppOfArity ``StOk 3 then
      if ← withNewMCtxDepth (isDefEq d.type P) then hyp := some d.toExpr; break
  if let some h := hyp then
    let rhs := mkApp4 (mkConst ``CodeMem.get) (mkConst ``Image.base) (mkConst ``Image.size) (mkConst ``Image.byte)
      (mkAppN (mkConst ``CMem.wr) #[G, a, n, v, h])
    return .step rhs (← mkEqSymm (mkAppN (mkConst ``CMem.wr_get) #[G, a, n, v, h]))
  let some P' ← unfoldDefinition? (mkApp3 (mkConst ``StOk) mem a n) | return .rfl
  let some hP ← omegaP? (← instantiateMVars (P'.headBeta)) | do
    trace[Meta.Tactic.cbv.rewrite] "store not ok {a}"
    return .rfl
  let ok ← mkExpectedTypeHint hP P
  let rhs := mkApp (mkConst ``CodeMem.get) (mkAppN (mkConst ``CMem.wr) #[G, a, n, v, ok])
  let rhs := mkApp4 (mkConst ``CodeMem.get) (mkConst ``Image.base) (mkConst ``Image.size) (mkConst ``Image.byte)
    (mkAppN (mkConst ``CMem.wr) #[G, a, n, v, ok])
  let pf ← mkEqSymm (mkAppN (mkConst ``CMem.wr_get) #[G, a, n, v, ok])
  return .step rhs pf

/-- Loads through stores and frames. -/
scoped cbv_simproc cbv_eval xLoad (rdRaw (CodeMem.get _) _ _) := fun e => do
  let_expr rdRaw mem b k := e | return .rfl
  let_expr CodeMem.get _ _ _ G := mem | return .rfl
  let some kv := natLit? k | return .rfl
  unless kv == 1 || kv == 2 || kv == 4 do return .rfl
  let toNat (x : Expr) := mkApp (mkConst ``UInt32.toNat) x
  let some hk ← elabPf (← `((by decide : UInt32.toNat $(← Elab.Term.TermElabM.run' (Elab.Term.exprToSyntax k)) = 1 ∨
      UInt32.toNat $(← Elab.Term.TermElabM.run' (Elab.Term.exprToSyntax k)) = 2 ∨
      UInt32.toNat $(← Elab.Term.TermElabM.run' (Elab.Term.exprToSyntax k)) = 4))) | return .rfl
  match_expr G with
  | CMem.wr G0 a n v h =>
    let some nv := natLit? n | return .rfl
    if nv == kv then
      if let some hab ← omegaP? (← mkEq (toNat a) (toNat b)) then
        if kv == 4 then
          let pf := mkAppN (mkConst ``rdRaw_wr_same4) #[G0, a, b, v, h, hab]
          return .step v pf
        if kv == 1 then
          let pf := mkAppN (mkConst ``rdRaw_wr_same1) #[G0, a, b, v, h, hab]
          let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
          return .step (← Sym.share rhs) pf
    let size := mkApp (mkConst ``ByteArray.size) (mkApp (mkConst ``CodeMem.get) G0)
    let size := mkApp (mkConst ``ByteArray.size)
      (mkApp4 (mkConst ``CodeMem.get) (mkConst ``Image.base) (mkConst ``Image.size) (mkConst ``Image.byte) G0)
    let some hb ← omegaP? (← mkLE (← mkAdd (toNat b) (toNat k)) size) | return .rfl
    let some hd ← omegaP? (mkOr (← mkLE (← mkAdd (toNat b) (toNat k)) (toNat a))
        (← mkLE (← mkAdd (toNat a) (toNat n)) (toNat b))) | return .rfl
    let pf := mkAppN (mkConst ``rdRaw_wr_other) #[G0, a, n, v, h, b, k, hk, hb, hd]
    let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
    return .step (← Sym.share rhs) pf
  | _ =>
    -- a frame hypothesis `Frame G0 G lo hi` in context
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let_expr Frame G0 G' lo hi := ty | continue
      unless (← isDefEq G' G) do continue
      let size := mkApp (mkConst ``ByteArray.size)
        (mkApp4 (mkConst ``CodeMem.get) (mkConst ``Image.base) (mkConst ``Image.size) (mkConst ``Image.byte) G0)
      let some hb ← omegaP? (← mkLE (← mkAdd (toNat b) (toNat k)) size) | continue
      let some hd ← omegaP? (mkOr (← mkLE (← mkAdd (toNat b) (toNat k)) lo) (← mkLE hi (toNat b))) | continue
      let pf := mkAppN (mkConst ``rdRaw_frame) #[G0, G, lo, hi, d.toExpr, b, k, hk, hb, hd]
      let some (_, _, rhs) := (← inferType pf).eq? | continue
      return .step (← Sym.share rhs) pf
    return .rfl

/-- `pdec P` decided by `omega` from the context. -/
scoped cbv_simproc cbv_eval xPdec (pdec _) := fun e => do
  let_expr pdec P inst := e | return .rfl
  if let some h ← omegaP? P then
    let pf := mkApp3 (mkConst ``pdec_true) P inst h
    return .step (mkConst ``Bool.true) pf
  if let some h ← omegaP? (mkNot P) then
    let pf := mkApp3 (mkConst ``pdec_false) P inst h
    return .step (mkConst ``Bool.false) pf
  return .rfl

/-- `sextB` of a literal. -/
scoped cbv_simproc cbv_eval xSextB (sextB _) := fun e => do
  let some x := natLit? e.appArg! | return .rfl
  let r := toExpr (sext 1 x.toUInt32)
  return .step r (← mkExpectedTypeHint (← mkEqRefl r) (← mkEq e r))

universe uB
theorem ebind_ok {ε σ α β : Type uB} (x : EStateM ε σ α) (f : α → EStateM ε σ β) (s : σ) (a : α) (s' : σ)
    (h : x s = .ok a s') : EStateM.bind x f s = f a s' := by
  simp only [EStateM.bind, h]
theorem ebind_err {ε σ α β : Type uB} (x : EStateM ε σ α) (f : α → EStateM ε σ β) (s : σ) (e : ε) (s' : σ)
    (h : x s = .error e s') : EStateM.bind x f s = .error e s' := by
  simp only [EStateM.bind, h]

/-- The continuation of `bind` on a result, opaque to `cbv`. -/
def bindRes {ε σ α β : Type uB} (r : EStateM.Result ε σ α) (f : α → EStateM ε σ β) : EStateM.Result ε σ β :=
  match r with
  | .ok a s => f a s
  | .error e s => .error e s

attribute [scoped cbv_opaque] bindRes

theorem ebind_res {ε σ α β : Type uB} (x : EStateM ε σ α) (f : α → EStateM ε σ β) (s : σ) (v : EStateM.Result ε σ α)
    (h : x s = v) : EStateM.bind x f s = bindRes v f := by
  subst h; rfl

/-- `bind x f s` by first evaluating `x s`: the step is then a proof, and the kernel never has to
evaluate `x s` itself to check it. -/
scoped cbv_simproc cbv_eval xBind (EStateM.bind _ _ _) := fun e => do
  unless e.isAppOfArity ``EStateM.bind 7 do return .rfl
  let lv := e.getAppFn.constLevels!
  let args := e.getAppArgs
  let (ε, σ, α, β, x, f, s) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!, args[6]!)
  let xs := (mkApp x s).headBeta
  let r ← Sym.Simp.simp xs
  let (v, h) ← match r with
    | .step v h .. => pure (v, h)
    | .rfl .. => pure (xs, ← mkEqRefl xs)
  if v.isAppOfArity ``EStateM.Result.ok 5 then
    let a := v.getArg! 3
    let s' := v.getArg! 4
    let pf := mkAppN (mkConst ``ebind_ok lv) #[ε, σ, α, β, x, f, s, a, s', h]
    let rhs := (mkApp2 f a s').headBeta
    return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))
  if v.isAppOfArity ``EStateM.Result.error 5 then
    let er := v.getArg! 3
    let s' := v.getArg! 4
    let pf := mkAppN (mkConst ``ebind_err lv) #[ε, σ, α, β, x, f, s, er, s', h]
    let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
    return .step rhs pf
  if v == xs then return .rfl
  -- not evaluated to a result: keep what was computed, behind the opaque `bindRes`
  let pf := mkAppN (mkConst ``ebind_res lv) #[ε, σ, α, β, x, f, s, v, h]
  let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
  return .step rhs pf

/-- A code byte at a literal offset, evaluated (the code bytes are opaque to `cbv` otherwise). -/
scoped cbv_simproc cbv_eval xImgByte (Image.byte _) := fun e => do
  let some n := (Sym.getNatValue? e.appArg!).run | return .rfl
  let r := toExpr (Image.byte n)
  return .step r (← mkExpectedTypeHint (← mkEqRefl r) (← mkEq e r))

/-- A binary operation of `UInt32` on two literals, folded (checked by the kernel by evaluation). -/
def foldLit2 (op : UInt32 → UInt32 → UInt32) (e : Expr) : MetaM Sym.Simp.Result := do
  let some a := natLit? e.appFn!.appArg! | return .rfl
  let some b := natLit? e.appArg! | return .rfl
  let r := toExpr (op a.toUInt32 b.toUInt32)
  return .step r (← mkExpectedTypeHint (← mkEqRefl r) (← mkEq e r))

scoped cbv_simproc cbv_eval xLor (UInt32.lor _ _) := fun e => foldLit2 (· ||| ·) e
scoped cbv_simproc cbv_eval xXor (UInt32.xor _ _) := fun e => foldLit2 (· ^^^ ·) e
scoped cbv_simproc cbv_eval xShl (UInt32.shiftLeft _ _) := fun e => foldLit2 (· <<< ·) e
scoped cbv_simproc cbv_eval xShr (UInt32.shiftRight _ _) := fun e => foldLit2 (· >>> ·) e

/-- The second component of a pair, as `Prod.snd` or as a projection. -/
def sndOf? (x : Expr) : Option Expr :=
  if x.isAppOfArity ``Prod.snd 3 then some x.appArg!
  else match x with
    | .proj ``Prod 1 p => some p
    | _ => none

/-- Flag bits of the ALU results (the rules `subF_CF`, `logicF_ZF`, …), with the pair's second
component in either form; `x & x` is `x`. -/
scoped cbv_simproc cbv_eval xFlagBit (UInt32.land _ _) := fun e => do
  let_expr UInt32.land x k := e | return .rfl
  if (natLit? x).isSome && (natLit? k).isSome then return ← foldLit2 (· &&& ·) e
  if x == k then
    let pf := mkApp (mkConst ``land_self') x
    return .step x pf
  let some kv := natLit? k | return .rfl
  let some p := sndOf? x | return .rfl
  let sz? := natLit? (p.getArg! 0)
  let lem? : Option (Name × Array Expr) :=
    if p.isAppOfArity ``subF 4 then
      let (sz, a, b) := (p.getArg! 0, p.getArg! 1, p.getArg! 2)
      match kv, sz? with
      | 1, _ => some (``subF_CF', #[sz, a, b])
      | 64, some 4 => some (``subF4_ZF', #[a, b])
      | 64, some 1 => some (``subF1_ZF', #[a, b])
      | 128, some 4 => some (``subF4_SF', #[a, b])
      | 2048, some 4 => some (``subF4_OF', #[a, b])
      | 65, some 4 => some (``subF4_CZ', #[a, b])
      | 65, some 1 => some (``subF1_CZ', #[a, b])
      | _, _ => none
    else if p.isAppOfArity ``logicF 2 then
      let (sz, r) := (p.getArg! 0, p.getArg! 1)
      match kv, sz? with
      | 1, _ => some (``logicF_CF, #[sz, r])
      | 2048, _ => some (``logicF_OF, #[sz, r])
      | 64, _ => some (``logicF_ZF', #[sz, r])
      | 65, _ => some (``logicF_CZ', #[sz, r])
      | 128, some 4 => some (``logicF4_SF', #[r])
      | 128, some 1 => some (``logicF1_SF', #[r])
      | _, _ => none
    else if p.isAppOfArity ``addF 4 then
      let (a, b) := (p.getArg! 1, p.getArg! 2)
      match kv, sz? with
      | 64, some 4 => some (``addF4_ZF', #[a, b])
      | 1, some 4 => some (``addF4_CF', #[a, b])
      | _, _ => none
    else none
  let some (lem, args) := lem? | return .rfl
  let pf := mkAppN (mkConst lem) args
  let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
  let pf ← mkExpectedTypeHint pf (← mkEq e rhs)
  -- decide the `pdec`s now; the propositions themselves are left alone (`done`)
  let mut rhs := rhs
  let mut pf := pf
  for t in collectApps (fun t => t.isAppOfArity ``pdec 2) rhs #[] do
    let P := t.getArg! 0
    let inst := t.getArg! 1
    let some (v, h) ← (do
        if let some h ← omegaP? P then return some (mkConst ``Bool.true, mkApp3 (mkConst ``pdec_true) P inst h)
        if let some h ← omegaP? (mkNot P) then return some (mkConst ``Bool.false, mkApp3 (mkConst ``pdec_false) P inst h)
        return none) | continue
    let rhs' := rhs.replace fun u => if u == t then some v else none
    let motive ← withLocalDeclD `b (mkConst ``Bool) fun bv => do
      mkLambdaFVars #[bv] (← mkEq e (rhs.replace fun u => if u == t then some bv else none))
    pf ← mkEqMP (← mkCongrArg motive h) pf
    rhs := rhs'
  -- `cond` on literals
  let rhs2 ← Meta.transform rhs (post := fun u => do
    if u.isAppOfArity ``cond 4 then
      if u.getArg! 1 == mkConst ``Bool.true then return .done (u.getArg! 2)
      if u.getArg! 1 == mkConst ``Bool.false then return .done (u.getArg! 3)
    return .continue)
  if rhs2 != rhs then
    pf ← mkExpectedTypeHint pf (← mkEq e rhs2)
    rhs := rhs2
  return .step rhs pf (done := !(collectApps (fun t => t.isAppOfArity ``pdec 2) rhs #[]).isEmpty)

theorem eaOff_eq (i : Inst) (m : Machine) : eaOff i m =
    .ok (if i.adsz == 2 then ((if i.base < 8 then m.cpu.getReg i.base else 0) +
      (if i.index < 8 then m.cpu.getReg i.index <<< i.scale.toUInt32 else 0) + i.disp) &&& 0xFFFF
      else (if i.base < 8 then m.cpu.getReg i.base else 0) +
      (if i.index < 8 then m.cpu.getReg i.index <<< i.scale.toUInt32 else 0) + i.disp) m := rfl

attribute [scoped cbv_eval] eaOff_eq

theorem shl_zero_of (x k : UInt32) (h : k = 0) : UInt32.shiftLeft x k = x := by
  subst h; exact UInt32.shiftLeft_zero

/-- `x <<< 0` (an address with scale 1), whatever form the literal `0` has. -/
scoped cbv_simproc cbv_eval xShl0 (UInt32.shiftLeft _ _) := fun e => do
  let_expr UInt32.shiftLeft x k := e | return .rfl
  let kn ← whnfD (mkApp (mkConst ``UInt32.toNat) k)
  let v : Option Nat := match kn.rawNatLit? with
    | some v => some v
    | none => (Sym.getNatValue? kn).run
  unless v == some 0 do return .rfl
  let zero := toExpr (0 : UInt32)
  let hk ← mkExpectedTypeHint (← mkEqRefl zero) (← mkEq k zero)
  let pf := mkApp3 (mkConst ``shl_zero_of) x k hk
  return .step x (← mkExpectedTypeHint pf (← mkEq e x))

/-! ## Address normal form

Addresses are kept as `x + k` or `x - k` with a literal `k < 2 ^ 31`, never as `x + k` with a large
`k`: the kernel unfolds `Nat.add n k` along `k` when it has to reduce such a term, so `x - 1` must not
be written `x + 0xFFFFFFFF`. -/

theorem uadd_zero (x : UInt32) : UInt32.add x 0 = x := UInt32.add_zero x
theorem usub_zero (x : UInt32) : UInt32.sub x 0 = x := UInt32.sub_zero x

private theorem u32_ext {a b : UInt32} (h : a.toNat = b.toNat) : a = b := UInt32.toNat_inj.mp h

theorem n_add_add (x a b c : UInt32) (h : c = a + b) : UInt32.add (UInt32.add x a) b = UInt32.add x c := by
  subst h; exact UInt32.add_assoc x a b
theorem n_add_to_sub (x b c : UInt32) (h : b + c = 0) : UInt32.add x b = UInt32.sub x c := by
  show x + b = x - c
  apply u32_ext
  have h' := congrArg UInt32.toNat h
  have := x.toNat_lt; have := b.toNat_lt; have := c.toNat_lt
  simp only [UInt32.toNat_add, UInt32.toNat_sub, UInt32.size, UInt32.reduceToNat] at *
  omega
theorem n_sub_to_add (x k c : UInt32) (h : c + k = 0) : UInt32.sub x k = UInt32.add x c := by
  show x - k = x + c
  apply u32_ext
  have h' := congrArg UInt32.toNat h
  have := x.toNat_lt; have := k.toNat_lt; have := c.toNat_lt
  simp only [UInt32.toNat_add, UInt32.toNat_sub, UInt32.size, UInt32.reduceToNat] at *
  omega
theorem n_sub_add (x a b c : UInt32) (h : b = a + c) : UInt32.add (UInt32.sub x a) b = UInt32.add x c := by
  subst h; show x - a + (a + c) = x + c; apply u32_ext; first | (simp [UInt32.toNat_sub, UInt32.toNat_add]; done) | (simp [UInt32.toNat_sub, UInt32.toNat_add]; xbounds; omega)
theorem n_sub_add' (x a b c : UInt32) (h : a = b + c) : UInt32.add (UInt32.sub x a) b = UInt32.sub x c := by
  subst h; show x - (b + c) + b = x - c; apply u32_ext; first | (simp [UInt32.toNat_sub, UInt32.toNat_add]; done) | (simp [UInt32.toNat_sub, UInt32.toNat_add]; xbounds; omega)
theorem n_add_sub (x a b c : UInt32) (h : a = b + c) : UInt32.sub (UInt32.add x a) b = UInt32.add x c := by
  subst h; show x + (b + c) - b = x + c; apply u32_ext; first | (simp [UInt32.toNat_sub, UInt32.toNat_add]; done) | (simp [UInt32.toNat_sub, UInt32.toNat_add]; xbounds; omega)
theorem n_add_sub' (x a b c : UInt32) (h : b = a + c) : UInt32.sub (UInt32.add x a) b = UInt32.sub x c := by
  subst h; show x + a - (a + c) = x - c; apply u32_ext; first | (simp [UInt32.toNat_sub, UInt32.toNat_add]; done) | (simp [UInt32.toNat_sub, UInt32.toNat_add]; xbounds; omega)
theorem n_sub_sub (x a b c : UInt32) (h : c = a + b) : UInt32.sub (UInt32.sub x a) b = UInt32.sub x c := by
  subst h; show x - a - b = x - (a + b); apply u32_ext; first | (simp [UInt32.toNat_sub, UInt32.toNat_add]; done) | (simp [UInt32.toNat_sub, UInt32.toNat_add]; xbounds; omega)
theorem n_add_cancel (x a : UInt32) : UInt32.sub (UInt32.add x a) a = x := by
  show x + a - a = x; apply u32_ext; first | (simp [UInt32.toNat_sub, UInt32.toNat_add]; done) | (simp [UInt32.toNat_sub, UInt32.toNat_add]; xbounds; omega)
theorem n_sub_cancel (x a : UInt32) : UInt32.add (UInt32.sub x a) a = x := by
  show x - a + a = x; apply u32_ext; first | (simp [UInt32.toNat_sub, UInt32.toNat_add]; done) | (simp [UInt32.toNat_sub, UInt32.toNat_add]; xbounds; omega)

/-- `x + k` (`pos`) or `x - k` with `k` reduced below `2 ^ 32`. -/
def mkOff (x : Expr) (pos : Bool) (k : Nat) : Expr :=
  if k == 0 then x else
  mkApp2 (mkConst (if pos then ``UInt32.add else ``UInt32.sub)) x (toExpr k.toUInt32)

/-- The proof `lhs = rhs` of a literal equation of `UInt32`, by evaluation. -/
def litEq (lhs rhs : Expr) : MetaM Expr := do
  mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq lhs rhs)

def u32 (n : Nat) : Expr := toExpr n.toUInt32

/-- Normalize `x ± k` (`isAdd`) whose argument may itself be `y ± a`. -/
def normOff (e x : Expr) (isAdd : Bool) (kv : Nat) : MetaM Sym.Simp.Result := do
  let kv : Nat := kv % 2 ^ 32
  -- the signed offset of `e` from the base `y`
  let (y, a, inner?) ← do
    if x.isAppOfArity ``UInt32.add 2 then
      if let some av := (Sym.getNatValue? x.appArg!).run then pure (x.appFn!.appArg!, (av % 2 ^ 32 : Int), some true)
      else pure (x, (0 : Int), none)
    else if x.isAppOfArity ``UInt32.sub 2 then
      if let some av := (Sym.getNatValue? x.appArg!).run then pure (x.appFn!.appArg!, -(av % 2 ^ 32 : Int), some false)
      else pure (x, (0 : Int), none)
    else pure (x, (0 : Int), none)
  let k : Int := if isAdd then kv else -kv
  let tot : Int := (a + k) % (2 ^ 32 : Int)
  -- the canonical form: `+ t` for `t < 2^31`, `- (2^32 - t)` otherwise
  let (pos, m) := if tot < 2 ^ 31 then (true, tot.toNat) else (false, (2 ^ 32 - tot).toNat)
  let r := mkOff y pos m
  if r == e then return .rfl
  let kE := e.appArg!
  let pf ← match inner? with
    | none =>
      -- `e = y ± k` with a large `k`, or `k = 0`
      if m == 0 then
        if isAdd then pure (mkApp (mkConst ``uadd_zero) y) else pure (mkApp (mkConst ``usub_zero) y)
      else if isAdd then
        -- y + k with k ≥ 2^31: y - m, m + k = 0
        pure (mkApp4 (mkConst ``n_add_to_sub) y kE (u32 m) (← litEq (← mkAdd kE (u32 m)) (u32 0)))
      else
        pure (mkApp4 (mkConst ``n_sub_to_add) y kE (u32 m) (← litEq (← mkAdd (u32 m) kE) (u32 0)))
    | some innerAdd =>
      let aE := x.appArg!
      let av : Nat := (Sym.getNatValue? aE).run.get! % 2 ^ 32
      -- first combine into `y + c` or `y - c` without the size rule, then fix the sign
      let (pos1, c1, pf1) ← do
        if innerAdd && isAdd then
          let c := (av + kv) % 2 ^ 32
          pure (true, c, mkApp5 (mkConst ``n_add_add) y aE kE (u32 c) (← litEq (u32 c) (← mkAdd aE kE)))
        else if !innerAdd && !isAdd then
          let c := (av + kv) % 2 ^ 32
          pure (false, c, mkApp5 (mkConst ``n_sub_sub) y aE kE (u32 c) (← litEq (u32 c) (← mkAdd aE kE)))
        else if !innerAdd && isAdd then
          if kv ≥ av then
            pure (true, kv - av, mkApp5 (mkConst ``n_sub_add) y aE kE (u32 (kv - av)) (← litEq kE (← mkAdd aE (u32 (kv - av)))))
          else
            pure (false, av - kv, mkApp5 (mkConst ``n_sub_add') y aE kE (u32 (av - kv)) (← litEq aE (← mkAdd kE (u32 (av - kv)))))
        else
          if av ≥ kv then
            pure (true, av - kv, mkApp5 (mkConst ``n_add_sub) y aE kE (u32 (av - kv)) (← litEq aE (← mkAdd kE (u32 (av - kv)))))
          else
            pure (false, kv - av, mkApp5 (mkConst ``n_add_sub') y aE kE (u32 (kv - av)) (← litEq kE (← mkAdd aE (u32 (kv - av)))))
      let mid := mkApp2 (mkConst (if pos1 then ``UInt32.add else ``UInt32.sub)) y (u32 c1)
      -- `mid` to `r`
      let pf2 ← do
        if c1 == 0 then
          pure (some (if pos1 then mkApp (mkConst ``uadd_zero) y else mkApp (mkConst ``usub_zero) y))
        else if mid == r then pure none
        else if pos1 then
          pure (some (mkApp4 (mkConst ``n_add_to_sub) y (u32 c1) (u32 m) (← litEq (← mkAdd (u32 c1) (u32 m)) (u32 0))))
        else
          pure (some (mkApp4 (mkConst ``n_sub_to_add) y (u32 c1) (u32 m) (← litEq (← mkAdd (u32 m) (u32 c1)) (u32 0))))
      match pf2 with
      | none => pure pf1
      | some p2 => mkEqTrans pf1 p2
  return .step r (← mkExpectedTypeHint pf (← mkEq e r))

scoped cbv_simproc cbv_eval xUAdd (UInt32.add _ _) := fun e => do
  let_expr UInt32.add x b := e | return .rfl
  let some bv := (Sym.getNatValue? b).run | return .rfl
  normOff e x true bv

scoped cbv_simproc cbv_eval xUSub (UInt32.sub _ _) := fun e => do
  let_expr UInt32.sub x k := e | return .rfl
  let some kv := (Sym.getNatValue? k).run | return .rfl
  normOff e x false kv

end Curl.Proofs.Sym
