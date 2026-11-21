import Solutions.OpensslX25519.Call
import Solutions.Exec.RunI
/-!
# Calls at any instruction count and return address

The field functions as callees of other functions: the call starts at an arbitrary instruction count
`ic0` (below `2^63`, far from the disarmed timer), returns to an arbitrary address `ret`, and uses
exactly its own stack frame (`W` bytes below the stack pointer) rather than the harness's
`stackBound`. `Facts1W`/`FieldFactsW` are `Facts1`/`FieldFacts` with that window.
-/
namespace Solutions.OpensslX25519
open X86 Ssl Solutions.Logic Solutions.Exec

/-- A piece of `k` instructions starting `n` instructions into a call that started at `x`. -/
theorem icB {x : UInt64} (h : x.toNat < 2 ^ 63) {n k : Nat} (hn : n + k < 2 ^ 63) :
    (icAdd x n).toNat + k < 2 ^ 64 - 1 := by
  rw [icAdd_toNat _ _ (by omega)]; omega

/-- The address facts of a call `fn(h, f)` whose frame is the `W` bytes below `sp`. -/
structure Facts1W (W size sp h f : Nat) : Prop where
  ram : size ≤ ramTop
  fit : 0x100000 + 47024 ≤ size
  sp_lo : W ≤ sp
  sp_hi : sp + 4 ≤ size
  sp_img : sp + 4 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ sp - W
  h_mem : h + 40 ≤ size
  f_mem : f + 40 ≤ size
  h_img : h + 40 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ h
  f_img : f + 40 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ f
  h_stk : h + 40 ≤ sp - W ∨ sp + 4 ≤ h
  f_stk : f + 40 ≤ sp - W ∨ sp + 4 ≤ f
  hf : h = f ∨ h + 40 ≤ f ∨ f + 40 ≤ h

/-- The address facts of a call `fn(h, f, g)` (`g` on the stack) whose frame is the `W` bytes below `sp`. -/
structure FieldFactsW (W size sp h f g : Nat) : Prop where
  ram : size ≤ ramTop
  fit : 0x100000 + 47024 ≤ size
  sp_lo : W ≤ sp
  sp_hi : sp + 8 ≤ size
  sp_img : sp + 8 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ sp - W
  h_mem : h + 40 ≤ size
  f_mem : f + 40 ≤ size
  g_mem : g + 40 ≤ size
  h_img : h + 40 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ h
  f_img : f + 40 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ f
  g_img : g + 40 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ g
  h_stk : h + 40 ≤ sp - W ∨ sp + 8 ≤ h
  f_stk : f + 40 ≤ sp - W ∨ sp + 8 ≤ f
  g_stk : g + 40 ≤ sp - W ∨ sp + 8 ≤ g
  hf : h = f ∨ h + 40 ≤ f ∨ f + 40 ≤ h
  hg : h = g ∨ h + 40 ≤ g ∨ g + 40 ≤ h

/-- The frame base: `sp - k` for `k ≤ W ≤ sp`. -/
theorem fb_toNatW {W : Nat} {sp : UInt32} (hs : W ≤ sp.toNat) (k : Nat) (hk : k ≤ W) :
    (sp - k.toUInt32).toNat = sp.toNat - k := by
  have : k < 2 ^ 32 := by have := sp.toNat_lt; omega
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, Nat.toUInt32, UInt32.toNat_ofNat']; omega),
    Nat.toUInt32, UInt32.toNat_ofNat']
  omega

end Solutions.OpensslX25519
