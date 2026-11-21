import Solutions.OpensslX25519.Frame
/-!
# Calls `fn(h, f)` with no stack arguments (`fe_sq`)

The address facts of a `FieldCall1`, and the stack frame of a function that pushes four registers and
reserves `locals` bytes below them: its base `fb = sp - (locals + 16)`, with the return address at
`fb + locals + 16 = sp`.
-/
namespace Solutions.OpensslX25519
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

/-- The address facts of a field call `fn(h, f)` without stack arguments. -/
structure Facts1 (size sp h f : Nat) : Prop where
  ram : size ≤ ramTop
  fit : 0x100000 + 47024 ≤ size
  sp_lo : 2048 ≤ sp
  sp_hi : sp + 4 ≤ size
  sp_img : sp + 4 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ sp - 2048
  h_mem : h + 40 ≤ size
  f_mem : f + 40 ≤ size
  h_img : h + 40 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ h
  f_img : f + 40 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ f
  h_stk : h + 40 ≤ sp - 2048 ∨ sp + 4 ≤ h
  f_stk : f + 40 ≤ sp - 2048 ∨ sp + 4 ≤ f
  hf : h = f ∨ h + 40 ≤ f ∨ f + 40 ≤ h

theorem bufFacts0 {c : Caller} {p : UInt32} (hs : 2048 ≤ c.sp.toNat)
    (hb : Buffer img c stackBound 0 p 40) :
    p.toNat + 40 ≤ c.mem.size ∧ (p.toNat + 40 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ p.toNat) ∧
      (p.toNat + 40 ≤ c.sp.toNat - 2048 ∨ c.sp.toNat + 4 ≤ p.toNat) := by
  obtain ⟨hfit, -, hai, has⟩ := hb
  have hlo := stackLo_toNat (c := c) (stack := stackBound) hs
  refine ⟨by rcases hfit with h | h <;> omega, ?_, ?_⟩
  · have := apart_nat hai (by decide) (by rw [img_size]; decide)
    rw [img_size, img_base] at this
    exact this
  · have := apart_nat has (by decide) (by simp [stackSize])
    rw [hlo] at this
    simp only [stackSize, stackBound] at this
    omega

theorem facts1 {c : Caller} {h f : UInt32} {fv : Array UInt32} (hc : FieldCall1 c h f fv) :
    Facts1 c.mem.size c.sp.toNat h.toNat f.toNat := by
  obtain ⟨hcall, -, -, hbh, hbf, hsh, -⟩ := hc
  have hs : 2048 ≤ c.sp.toNat := hcall.2.2.2.2.1
  have hlo := stackLo_toNat (c := c) (stack := stackBound) hs
  have himg := apart_nat hcall.2.2.2.2.2.2 (by simp [stackSize]) (by rw [img_size]; decide)
  rw [hlo, img_size, img_base] at himg
  simp only [stackSize, stackBound, List.length] at himg
  have hsp : c.sp.toNat + 4 * ([].length + 1) ≤ c.mem.size := hcall.2.2.2.2.2.1
  simp only [List.length] at hsp
  have bh := bufFacts0 hs hbh
  have bf := bufFacts0 hs hbf
  have hfit := hcall.2.1
  rw [img_size, img_base] at hfit
  exact ⟨ramTop_of_calls hcall, by omega, hs, by omega, by omega, bh.1, bf.1, bh.2.1,
    bf.2.1, bh.2.2, bf.2.2, sameFacts hsh⟩

/-- The frame base: `sp - k` for `k ≤ 2048`. -/
theorem fb_toNat {sp : UInt32} (hs : 2048 ≤ sp.toNat) (k : Nat) (hk : k ≤ 2048) :
    (sp - k.toUInt32).toNat = sp.toNat - k := by
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, Nat.toUInt32, UInt32.toNat_ofNat']; omega),
    Nat.toUInt32, UInt32.toNat_ofNat']
  omega

end Solutions.OpensslX25519
