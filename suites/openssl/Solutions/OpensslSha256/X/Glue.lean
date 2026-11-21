import Solutions.OpensslSha256.X.Cleanse
import Solutions.OpensslSha256.SpecCtx
/-!
# From runs to the contracts of the statements

`returns_of_run`: a run from the entry of a call to the sentinel, with the callee-saved registers
back, the stack pointer popped and memory changed only in a region `P` (in byte addresses), is a
`Returns` of the call when `P` lies inside the writable set and the stack bytes. Also the words of a
byte list read from memory (`lw_memBytes`).
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256
open Solutions.OpensslSha256 (lw Good hOf tailOf)

theorem returns_of_run (c : Caller) (fn : UInt32) (W : UInt32 → Prop) (Q : Machine → Prop) (M' : ByteArray)
    (eax' ecx' edx' fl' : UInt32) (ic' : UInt64) (P : Nat → Prop)
    (hrun : Run img (c.enter fn)
      (St.m ⟨M', eax', ecx', edx', c.regs.ebx, c.sp + 4, c.regs.ebp, c.regs.esi, c.regs.edi, Image.sym_halt, efl fl', ic'⟩))
    (hA : AgreeOn P c.mem M')
    (hP : ∀ a : UInt32, P a.toNat → W a ∨ InRange (c.sp - (512 : Nat).toUInt32) 512 a)
    (hQ : Q (St.m ⟨M', eax', ecx', edx', c.regs.ebx, c.sp + 4, c.regs.ebp, c.regs.esi, c.regs.edi, Image.sym_halt,
      efl fl', ic'⟩)) :
    Returns img (c.enter fn) stackBound W Q := by
  refine Returns.intro hrun ⟨rfl, rfl, efl_DF fl'⟩ ⟨rfl, rfl, rfl, rfl⟩ ⟨hA.1, fun a ha hw hs => ?_⟩ hQ
  change a.toNat < c.mem.size at ha
  show memByte M' a = memByte c.mem a
  rw [memByte_def (by rw [hA.1]; exact ha), memByte_def ha]
  refine hA.2 a.toNat ha fun hp => ?_
  rcases hP a hp with h | h
  · exact hw h
  · exact hs h

/-- The memory of a call, with the image. -/
def cmemOf {c : Caller} {args : List UInt32} (h : Calls img c stackBound args) : CMem := callMem rfl h

theorem cmemOf_get {c : Caller} {args : List UInt32} (h : Calls img c stackBound args) : (cmemOf h).get = c.mem := rfl

theorem toUInt32_lt {i : Nat} (h : i < 2 ^ 32) : (i.toUInt32).toNat = i := by
  simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt h

theorem memBytes_get {M : ByteArray} {a : UInt32} {n i : Nat} (hi : i < n) (hfit : a.toNat + n ≤ M.size)
    (hM : M.size < 2 ^ 32) : (memBytes M a n)[i]! = M.get! (a.toNat + i) := by
  rw [getElem!_pos _ i (by rw [memBytes_length]; exact hi), memBytes_getElem]
  have e : (a + i.toUInt32).toNat = a.toNat + i := by
    rw [UInt32.toNat_add, toUInt32_lt (by omega)]; exact Nat.mod_eq_of_lt (by omega)
  rw [memByte_def (by rw [e]; omega), e]

/-- A word of the bytes read from memory is the word in memory. -/
theorem lw_memBytes {M : ByteArray} {a : UInt32} {n k : Nat} (hk : k + 4 ≤ n) (hfit : a.toNat + n ≤ M.size)
    (hM : M.size < 2 ^ 32) : lw (memBytes M a n) k = rdRaw M (a + k.toUInt32) 4 := by
  have e : (a + k.toUInt32).toNat = a.toNat + k := by
    rw [UInt32.toNat_add, toUInt32_lt (by omega)]; exact Nat.mod_eq_of_lt (by omega)
  unfold lw rdRaw
  rw [rdBytes4_eq (by rw [e]; omega), e, memBytes_get (by omega) hfit hM, memBytes_get (by omega) hfit hM,
    memBytes_get (by omega) hfit hM, memBytes_get (by omega) hfit hM]
  simp only [Nat.add_assoc]
  rfl

end Solutions.ShaX
