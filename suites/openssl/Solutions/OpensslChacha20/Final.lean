import Solutions.OpensslChacha20.Main
import Solutions.Exec.Call
/-!
# `ChaCha20_ctr32_correct`
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20 Ssl.Spec.Chacha

theorem img_bytes_size : img.bytes.size = 1072 := by simp [img, Image.bytes, ByteArray.size, Image.size]
theorem img_base_toNat : img.base.toNat = 0x100000 := rfl

theorem apart_nat {a : UInt32} {n : Nat} {b : UInt32} {k : Nat} (h : Apart a n b k) (hn : n ≠ 0)
    (hk : k ≠ 0) : a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat := by
  rcases h with h | h | h <;> omega

/-- The address facts of a call, from its precondition. -/
theorem facts_of_pre {c : Caller} {out inp keyp ctrp : UInt32} {key ctr : Array UInt32} {src : List UInt8}
    (hpre : Pre c out inp keyp ctrp key ctr src) (hl : src.length ≠ 0) (C : UInt32)
    (hC : C.toNat + 288 = c.sp.toNat) :
    Facts c.mem.size C out inp src.length := by
  obtain ⟨hcalls, hks, hcs, hbo, hbi, hbk, hbc, hio, hok, hoc, hkey, hctr, hsrc⟩ := hpre
  have hsz : c.mem.size ≤ 4273995776 := hcalls.1
  have hsp : 512 ≤ c.sp.toNat := hcalls.2.2.2.2.1
  have hspfit : c.sp.toNat + 24 ≤ c.mem.size := by
    have := hcalls.2.2.2.2.2.1; simpa [args] using this
  have hlo : (c.stackLo stackBound).toNat = c.sp.toNat - 512 := by
    unfold Caller.stackLo stackBound
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    simp
  have himg := apart_nat hcalls.2.2.2.2.2.2 (by simp [stackSize]) (by rw [img_bytes_size]; decide)
  rw [hlo, img_bytes_size, img_base_toNat] at himg
  simp only [stackSize, stackBound, args, List.length] at himg
  obtain ⟨hfo, hmo, haio, haso⟩ := hbo
  obtain ⟨hfi, hmi, haii, hasi⟩ := hbi
  have ho1 := apart_nat haio hl (by rw [img_bytes_size]; decide)
  have hi1 := apart_nat haii hl (by rw [img_bytes_size]; decide)
  have ho2 := apart_nat haso hl (by simp [stackSize])
  have hi2 := apart_nat hasi hl (by simp [stackSize])
  rw [img_bytes_size, img_base_toNat] at ho1 hi1
  rw [hlo] at ho2 hi2
  simp only [stackSize, stackBound] at ho2 hi2
  have hfo' : out.toNat + src.length ≤ c.mem.size := by rcases hfo with h | h <;> omega
  have hfi' : inp.toNat + src.length ≤ c.mem.size := by rcases hfi with h | h <;> omega
  unfold maxObject at hmo
  refine ⟨hsz, by omega, by omega, by omega, by omega, hfo', hfi', by omega, by omega, by omega, by omega, ?_⟩
  rcases hio with e | e
  · exact Or.inl e.symm
  · have := apart_nat e hl hl; omega

theorem uadd_eq {a : UInt32} {k m : Nat} (h : k % 2 ^ 32 = m % 2 ^ 32) :
    a + (OfNat.ofNat k : UInt32) = a.add (OfNat.ofNat m) := by
  apply UInt32.toNat_inj.1
  show (a + OfNat.ofNat k).toNat = (a + OfNat.ofNat m).toNat
  rw [UInt32.toNat_add, UInt32.toNat_add]
  show (a.toNat + k % 2 ^ 32) % 2 ^ 32 = (a.toNat + m % 2 ^ 32) % 2 ^ 32
  rw [h]

/-- Word `i` of `memWords`, at the address in the form the steps use. -/
theorem word_at {M : ByteArray} {a : UInt32} {n : Nat} {ws : Array UInt32} (h : memWords M a n = ws)
    (i : Nat) (hi : i < n) (hw : i < ws.size) (k : Nat) (hk : k = 4 * i) (hi32 : i < 2 ^ 30) :
    rdRaw M (a.add (OfNat.ofNat k)) 4 = ws[i]! := by
  have := memWords_get h i hi hw
  rw [getElem!_pos ws i hw, ← this]
  unfold rdRaw memWord
  congr 1
  apply UInt32.toNat_inj.1
  show (a + OfNat.ofNat k).toNat = (a + 4 * i.toUInt32).toNat
  rw [UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_mul]
  subst hk
  have e1 : (OfNat.ofNat (4 * i) : UInt32).toNat = (4 * i) % 2 ^ 32 := by
    show ((4 * i).toUInt32).toNat = _
    simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']
  have e2 : (i.toUInt32).toNat = i % 2 ^ 32 := by simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']
  rw [e1, e2, show (4 : UInt32).toNat = 4 from rfl]
  omega

theorem word_at0 {M : ByteArray} {a : UInt32} {n : Nat} {ws : Array UInt32} (h : memWords M a n = ws)
    (hi : 0 < n) (hw : 0 < ws.size) : rdRaw M a 4 = ws[0]! := by
  have := word_at h 0 hi hw 0 rfl (by decide)
  rw [show a.add (OfNat.ofNat 0) = a from UInt32.add_zero a] at this
  exact this

theorem w0_x {key ctr : Array UInt32} (hk : key.size = 8) (hc : ctr.size = 4) :
    (wJ key ctr 0).x0 = 0x61707865 ∧ (wJ key ctr 0).x1 = 0x3320646e ∧ (wJ key ctr 0).x2 = 0x79622d32 ∧
    (wJ key ctr 0).x3 = 0x6b206574 ∧ (wJ key ctr 0).x4 = key[0]! ∧ (wJ key ctr 0).x5 = key[1]! ∧
    (wJ key ctr 0).x6 = key[2]! ∧ (wJ key ctr 0).x7 = key[3]! ∧ (wJ key ctr 0).x8 = key[4]! ∧
    (wJ key ctr 0).x9 = key[5]! ∧ (wJ key ctr 0).x10 = key[6]! ∧ (wJ key ctr 0).x11 = key[7]! ∧
    (wJ key ctr 0).x12 = ctr[0]! ∧ (wJ key ctr 0).x13 = ctr[1]! ∧ (wJ key ctr 0).x14 = ctr[2]! ∧
    (wJ key ctr 0).x15 = ctr[3]! := by
  simp only [wJ, Nat.repeat, w0, V16.ofArr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [state_get hk hc _ (by decide)] <;> simp [sigma]

end Solutions.OpensslChacha20
