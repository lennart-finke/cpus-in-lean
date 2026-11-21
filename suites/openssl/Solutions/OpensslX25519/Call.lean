import Solutions.Exec.Call
import Ssl.OpensslX25519.Statement
/-!
# Calls of the X25519 image

The image in the caller's memory (`XMem`), and the facts of a field call (`FieldCall2`) as the
arithmetic on addresses that `exec_omega` uses: every buffer is inside memory, apart from the image
and from the call's stack, and the output is the input or apart from it.
-/
namespace Solutions.OpensslX25519
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

abbrev XMem := CodeMem Image.base Image.size Image.byte

theorem image_size : Image.bytes.size = Image.size := by simp [Image.bytes, ByteArray.size]

/-- The memory of a call of the X25519 image. -/
def xmem {c : Caller} {stack : Nat} {args : List UInt32} (h : Calls img c stack args) : XMem :=
  callMem (byte := Image.byte) rfl h

theorem xmem_get {c : Caller} {stack : Nat} {args : List UInt32} (h : Calls img c stack args) :
    (xmem h).get = c.mem := rfl

theorem apart_nat {a : UInt32} {n : Nat} {b : UInt32} {k : Nat} (h : Apart a n b k) (hn : n ≠ 0)
    (hk : k ≠ 0) : a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat := by
  rcases h with h | h | h <;> omega

theorem stackLo_toNat {c : Caller} {stack : Nat} (h : stack ≤ c.sp.toNat) :
    (c.stackLo stack).toNat = c.sp.toNat - stack := by
  unfold Caller.stackLo
  have hs : stack < 2 ^ 32 := by have := c.sp.toNat_lt; omega
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
  simp; omega

/-- The address facts of a field call `fn(h, f, g)` with `g` on the stack. -/
structure FieldFacts (size sp h f g : Nat) : Prop where
  ram : size ≤ ramTop
  fit : 0x100000 + 47024 ≤ size
  sp_lo : 2048 ≤ sp
  sp_hi : sp + 8 ≤ size
  sp_img : sp + 8 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ sp - 2048
  h_mem : h + 40 ≤ size
  f_mem : f + 40 ≤ size
  g_mem : g + 40 ≤ size
  h_img : h + 40 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ h
  f_img : f + 40 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ f
  g_img : g + 40 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ g
  h_stk : h + 40 ≤ sp - 2048 ∨ sp + 8 ≤ h
  f_stk : f + 40 ≤ sp - 2048 ∨ sp + 8 ≤ f
  g_stk : g + 40 ≤ sp - 2048 ∨ sp + 8 ≤ g
  hf : h = f ∨ h + 40 ≤ f ∨ f + 40 ≤ h
  hg : h = g ∨ h + 40 ≤ g ∨ g + 40 ≤ h

theorem img_size : img.bytes.size = 47024 := image_size
theorem img_base : img.base.toNat = 0x100000 := rfl

theorem bufFacts {c : Caller} {p : UInt32} (hs : 2048 ≤ c.sp.toNat)
    (hb : Buffer img c stackBound 1 p 40) :
    p.toNat + 40 ≤ c.mem.size ∧ (p.toNat + 40 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ p.toNat) ∧
      (p.toNat + 40 ≤ c.sp.toNat - 2048 ∨ c.sp.toNat + 8 ≤ p.toNat) := by
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

theorem sameFacts {h p : UInt32} (hp : SameOrApart h p) :
    h.toNat = p.toNat ∨ h.toNat + 40 ≤ p.toNat ∨ p.toNat + 40 ≤ h.toNat := by
  rcases hp with rfl | hp
  · exact Or.inl rfl
  · exact Or.inr (apart_nat hp (by decide) (by decide))

theorem fieldFacts {c : Caller} {h f g : UInt32} {fv gv : Array UInt32} (hc : FieldCall2 c h f g fv gv) :
    FieldFacts c.mem.size c.sp.toNat h.toNat f.toNat g.toNat := by
  obtain ⟨hcall, -, -, hbh, hbf, hbg, hsh, hsg, -, -⟩ := hc
  have hs : 2048 ≤ c.sp.toNat := hcall.2.2.2.2.1
  have hlo := stackLo_toNat (c := c) (stack := stackBound) hs
  have himg := apart_nat hcall.2.2.2.2.2.2 (by simp [stackSize]) (by rw [img_size]; decide)
  rw [hlo, img_size, img_base] at himg
  simp only [stackSize, stackBound, List.length] at himg
  have hsp : c.sp.toNat + 4 * ([g].length + 1) ≤ c.mem.size := hcall.2.2.2.2.2.1
  simp only [List.length] at hsp
  have bh := bufFacts hs hbh
  have bf := bufFacts hs hbf
  have bg := bufFacts hs hbg
  have hfit := hcall.2.1
  rw [img_size, img_base] at hfit
  exact ⟨ramTop_of_calls hcall, by omega, hs, by omega, by omega, bh.1, bf.1, bg.1, bh.2.1,
    bf.2.1, bg.2.1, bh.2.2, bf.2.2, bg.2.2, sameFacts hsh, sameFacts hsg⟩

end Solutions.OpensslX25519
