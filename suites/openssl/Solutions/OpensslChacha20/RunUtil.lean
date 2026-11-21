import Solutions.OpensslChacha20.Frame2
import Solutions.OpensslChacha20.Exec
/-!
# Runs of the ChaCha20 image from `exN` evaluations, and byte facts
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20

theorem img_halt : img.halt = Image.sym_halt := rfl

/-- An evaluated run of `k` instructions is a run of the image. -/
theorem run_of_exN {k : Nat} {s s' : St} (h : exN Image.sym_halt k s = some s') (hb : s.ic.toNat + k < 2 ^ 64) :
    Run img s.m s'.m :=
  exN_run (img := img) k s s' h hb

theorem u64_add_toNat {ic : UInt64} {k : Nat} (hk : k < 2 ^ 64) (h : ic.toNat + k < 2 ^ 64) :
    (ic + k.toUInt64).toNat = ic.toNat + k := by
  rw [UInt64.toNat_add]
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt hk]
  exact Nat.mod_eq_of_lt h

theorem u64_add_lit {ic : UInt64} {k : Nat} (hk : k < 2 ^ 64) (h : ic.toNat + k < 2 ^ 64) :
    (ic + (OfNat.ofNat k : UInt64)).toNat = ic.toNat + k := by
  have : (OfNat.ofNat k : UInt64) = k.toUInt64 := rfl
  rw [this]; exact u64_add_toNat hk h

theorem toNat_uadd_of_lt {a b : UInt32} (h : a.toNat + b.toNat < 2 ^ 32) : (UInt32.add a b).toNat = a.toNat + b.toNat := by
  show (a + b).toNat = _
  rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt h

theorem toNat_natAdd {a : UInt32} {k : Nat} (h : a.toNat + k < 2 ^ 32) : (a + k.toUInt32).toNat = a.toNat + k := by
  rw [UInt32.toNat_add]
  simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']
  have : k % 2 ^ 32 = k := Nat.mod_eq_of_lt (by omega)
  rw [this]; exact Nat.mod_eq_of_lt h

/-- The low byte of a zero-extended byte. -/
theorem land255_toUInt8 (b : UInt8) : (UInt32.land b.toUInt32 255).toUInt8 = b := by
  apply UInt8.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  show ((b.toUInt32 &&& 255).toUInt8).toBitVec.getLsbD i = _
  simp only [UInt32.toBitVec_toUInt8, BitVec.getLsbD_setWidth, UInt32.toBitVec_and, BitVec.getLsbD_and,
    UInt8.toBitVec_toUInt32, hi, decide_true, Bool.true_and]
  have h2 : ∀ j, j < 8 → (UInt32.toBitVec 255).getLsbD j = true := by decide
  rw [h2 i hi]
  simp only [Bool.and_true]
  cases hb : b.toBitVec.getLsbD i <;> simp_all <;> omega

/-- A one-byte load is the byte, zero-extended. -/
theorem rdRaw1 {M : ByteArray} {a : UInt32} (h : a.toNat < M.size) : rdRaw M a 1 = (M.get! a.toNat).toUInt32 := by
  unfold rdRaw; rw [rdBytes1_eq h, memByte_def h]

/-- The byte a one-byte store leaves. -/
theorem get!_wr1_self {M : ByteArray} {a v : UInt32} (h : a.toNat < M.size) :
    (wrBytes M a 1 v).get! a.toNat = v.toUInt8 := by
  rw [get!_wrBytes1 h, if_pos rfl]

theorem get!_wr1_other {M : ByteArray} {a v : UInt32} (h : a.toNat < M.size) {b : Nat} (hb : b ≠ a.toNat) :
    (wrBytes M a 1 v).get! b = M.get! b := by
  rw [get!_wrBytes1 h, if_neg hb]

/-- Two words with the same four bytes are equal, wherever they are. -/
theorem rdRaw4_of_bytes {M M' : ByteArray} {a a' : UInt32} (h : a.toNat + 4 ≤ M.size) (h' : a'.toNat + 4 ≤ M'.size)
    (hb : ∀ k, k < 4 → M.get! (a.toNat + k) = M'.get! (a'.toNat + k)) : rdRaw M a 4 = rdRaw M' a' 4 := by
  unfold rdRaw
  rw [rdBytes4_eq h, rdBytes4_eq h']
  have h0 := hb 0 (by omega)
  have h1 := hb 1 (by omega)
  have h2 := hb 2 (by omega)
  have h3 := hb 3 (by omega)
  simp only [Nat.add_zero] at h0
  rw [h0, h1, h2, h3]

end Solutions.OpensslChacha20
