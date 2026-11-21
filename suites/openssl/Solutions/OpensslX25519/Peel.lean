import Solutions.Exec.Step
import Solutions.Exec.Frame
import Solutions.OpensslX25519.Call
/-!
# Loads through the stores of a run

After a run, memory is a chain of code-keeping stores (`CodeMem.wr4`) over the caller's memory. A
load of a word through a store is the stored word when it is the same word (`rdRaw_wr4_same`) and
the older memory when the two are disjoint (`rdRaw_wr4_other`); `peel` applies these through a whole
chain, deciding each case by `exec_omega` from the hypotheses in context. Likewise for the bytes of
`Ssl.memByte` (`memByte_wr4_other`).
-/
namespace Solutions.OpensslX25519
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

theorem rdRaw_wr4_other (N : XMem) (a v : UInt32) (ok : StoreOk Image.base Image.size N.mem a) {b : UInt32}
    (hb : b.toNat + 4 ≤ N.get.size) (hd : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    rdRaw (CodeMem.wr4 N a v ok).get b 4 = rdRaw N.get b 4 :=
  rdBytes4_wrBytes4_other ok.1 hb hd

theorem rdRaw_wr4_same (N : XMem) (a v : UInt32) (ok : StoreOk Image.base Image.size N.mem a) {b : UInt32}
    (hab : a.toNat = b.toNat) : rdRaw (CodeMem.wr4 N a v ok).get b 4 = v :=
  rdBytes4_wrBytes4_same ok.1 hab

theorem memByte_wr4 (N : XMem) (a v : UInt32) (ok : StoreOk Image.base Image.size N.mem a) {b : UInt32}
    (hb : b.toNat < N.get.size) (hd : b.toNat < a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    memByte (CodeMem.wr4 N a v ok).get b = memByte N.get b :=
  memByte_wr4_other N a v ok hb hd

theorem storeOk_intro (N : XMem) (a : UInt32) (h1 : a.toNat + 4 ≤ N.get.size)
    (h2 : a.toNat + 4 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ a.toNat) : StoreOk Image.base Image.size N.mem a :=
  ⟨h1, h2⟩

/-- A word store into the output `h` of a field call. -/
theorem storeOk_h (N : XMem) {sp h f g : Nat} {hp : UInt32} (hh : hp.toNat = h)
    (F : FieldFacts N.get.size sp h f g) (k : UInt32) (hk : k.toNat + 4 ≤ 40) :
    StoreOk Image.base Image.size N.mem (UInt32.add hp k) := by
  have h6 := F.h_mem
  have h9 := F.h_img
  have h1 := F.ram
  have hl : (UInt32.add hp k).toNat = hp.toNat + k.toNat := by
    show (hp + k).toNat = _
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by simp [ramTop] at h1; omega)]
  refine ⟨?_, ?_⟩
  · show (UInt32.add hp k).toNat + 4 ≤ N.get.size
    omega
  · show _ ∨ _
    simp only [Image.base, Image.size, UInt32.reduceToNat]
    omega

theorem storeOk_h0 (N : XMem) {sp h f g : Nat} {hp : UInt32} (hh : hp.toNat = h)
    (F : FieldFacts N.get.size sp h f g) : StoreOk Image.base Image.size N.mem hp := by
  have h6 := F.h_mem
  have h9 := F.h_img
  refine ⟨?_, ?_⟩
  · show hp.toNat + 4 ≤ N.get.size
    omega
  · show _ ∨ _
    simp only [Image.base, Image.size, UInt32.reduceToNat]
    omega

/-- The word below the stack pointer of a field call. -/
theorem storeOk_sp (N : XMem) {h f g : Nat} {sp : UInt32}
    (F : FieldFacts N.get.size sp.toNat h f g) : StoreOk Image.base Image.size N.mem (UInt32.sub sp 4) := by
  have h3 := F.sp_lo
  have h4 := F.sp_hi
  have h5 := F.sp_img
  have hl : (UInt32.sub sp 4).toNat = sp.toNat - 4 := by
    show (sp - 4).toNat = _
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    simp
  refine ⟨?_, ?_⟩
  · show (UInt32.sub sp 4).toNat + 4 ≤ N.get.size
    omega
  · show _ ∨ _
    simp only [Image.base, Image.size, UInt32.reduceToNat]
    omega

theorem wr4_size (N : XMem) (a v : UInt32) (ok : StoreOk Image.base Image.size N.mem a) :
    (CodeMem.wr4 N a v ok).get.size = N.get.size := wr4_get_size N a v ok

theorem FieldFacts.size_eq {s s' sp h f g : Nat} (e : s' = s) (F : FieldFacts s sp h f g) :
    FieldFacts s' sp h f g := e ▸ F

/-- Load through a chain of code-keeping stores, and bytes outside them. -/
macro "peel" : tactic =>
  `(tactic| simp (disch := exec_omega') only [rdRaw_wr4_other, rdRaw_wr4_same, memByte_wr4])

theorem memWords_getElem! (mem : ByteArray) (a : UInt32) (n i : Nat) (hi : i < n) :
    (memWords mem a n)[i]! = rdRaw mem (a + 4 * i.toUInt32) 4 := by
  simp [memWords, memWord, hi, rdRaw]

/-! ## One store at a time, with small contexts

The lemmas below take the few facts they need, so that a chain of stores is peeled by rewriting
with them, each side condition being a literal comparison (`decide`) or a field of `FieldFacts`.
Word `j` of a 40-byte buffer at `p` is an address `a` with `a.toNat = p + j`. -/

/-- Word `k` of a buffer below `ramTop`. -/
theorem at_b {hp : UInt32} {S p : Nat} (hh : hp.toNat = p) (hm : p + 40 ≤ S) (hS : S ≤ ramTop)
    (k : UInt32) (hk : k.toNat ≤ 36) : (UInt32.add hp k).toNat = p + k.toNat := by
  show (hp + k).toNat = _
  rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by simp [ramTop] at hS; omega)]
  omega

theorem at0 (hp : UInt32) : hp.toNat = hp.toNat + 0 := (Nat.add_zero _).symm

/-- The word below the stack pointer. -/
theorem at_s {sp : UInt32} (hsp : 2048 ≤ sp.toNat) : (UInt32.sub sp 4).toNat = sp.toNat - 4 := by
  show (sp - 4).toNat = _
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
  simp

/-- The word at the stack pointer, reached from the word below it. -/
theorem at_s4 {sp : UInt32} (hsp : 2048 ≤ sp.toNat) :
    (UInt32.add (UInt32.sub sp 4) 4).toNat = sp.toNat - 4 + 4 := by
  have := sp.toNat_lt
  show (sp - 4 + 4).toNat = _
  rw [UInt32.toNat_add, show (sp - 4).toNat = sp.toNat - 4 from at_s hsp]
  simp
  omega

/-- Load from buffer `q` through a store into buffer `p`, at a different word or buffer. -/
theorem rd_bb (N : XMem) {S : Nat} (hs : N.get.size = S) {a b v : UInt32}
    {ok : StoreOk Image.base Image.size N.mem a} {p q j k : Nat}
    (ha : a.toNat = p + j) (hb : b.toNat = q + k) (hq : q + 40 ≤ S)
    (hpq : p = q ∨ p + 40 ≤ q ∨ q + 40 ≤ p) (hjk : j + 4 ≤ k ∨ k + 4 ≤ j) (hj : j + 4 ≤ 40)
    (hk : k + 4 ≤ 40) : rdRaw (CodeMem.wr4 N a v ok).get b 4 = rdRaw N.get b 4 :=
  rdRaw_wr4_other N a v ok (by omega) (by omega)

/-- Load from a buffer through the store below the stack pointer. -/
theorem rd_bs (N : XMem) {S : Nat} (hs : N.get.size = S) {a b v : UInt32}
    {ok : StoreOk Image.base Image.size N.mem a} {sp q k : Nat}
    (ha : a.toNat = sp - 4) (hb : b.toNat = q + k) (hq : q + 40 ≤ S)
    (hst : q + 40 ≤ sp - 2048 ∨ sp + 8 ≤ q) (hsp : 2048 ≤ sp) (hk : k + 4 ≤ 40) :
    rdRaw (CodeMem.wr4 N a v ok).get b 4 = rdRaw N.get b 4 :=
  rdRaw_wr4_other N a v ok (by omega) (by omega)

/-- Load from the stack (at `sp - 4` or `sp`) through a store into a buffer. -/
theorem rd_sb (N : XMem) {S : Nat} (hs : N.get.size = S) {a b v : UInt32}
    {ok : StoreOk Image.base Image.size N.mem a} {sp p j t : Nat}
    (ha : a.toNat = p + j) (hb : b.toNat = sp - 4 + t) (ht : t ≤ 4) (hj : j + 4 ≤ 40)
    (hst : p + 40 ≤ sp - 2048 ∨ sp + 8 ≤ p) (hsp : 2048 ≤ sp) (hsz : sp + 8 ≤ S) :
    rdRaw (CodeMem.wr4 N a v ok).get b 4 = rdRaw N.get b 4 :=
  rdRaw_wr4_other N a v ok (by omega) (by omega)

/-- Load from `sp` through the store at `sp - 4`. -/
theorem rd_ss (N : XMem) {S : Nat} (hs : N.get.size = S) {a b v : UInt32}
    {ok : StoreOk Image.base Image.size N.mem a} {sp : Nat}
    (ha : a.toNat = sp - 4) (hb : b.toNat = sp - 4 + 4) (hsp : 2048 ≤ sp) (hsz : sp + 8 ≤ S) :
    rdRaw (CodeMem.wr4 N a v ok).get b 4 = rdRaw N.get b 4 :=
  rdRaw_wr4_other N a v ok (by omega) (by omega)

/-- A byte outside buffer `p` through a store into it. -/
theorem mb_b (N : XMem) {S : Nat} (hs : N.get.size = S) {a x v : UInt32}
    {ok : StoreOk Image.base Image.size N.mem a} {p j : Nat}
    (ha : a.toNat = p + j) (hj : j + 4 ≤ 40) (hx : x.toNat < S) (hW : x.toNat < p ∨ p + 40 ≤ x.toNat) :
    memByte (CodeMem.wr4 N a v ok).get x = memByte N.get x :=
  memByte_wr4 N a v ok (by omega) (by omega)

/-- A byte outside the stack bytes through the store below the stack pointer. -/
theorem mb_s (N : XMem) {S : Nat} (hs : N.get.size = S) {a x v : UInt32}
    {ok : StoreOk Image.base Image.size N.mem a} {sp : Nat}
    (ha : a.toNat = sp - 4) (hx : x.toNat < S) (hsp : 2048 ≤ sp)
    (hS : x.toNat < sp - 2048 ∨ sp ≤ x.toNat) :
    memByte (CodeMem.wr4 N a v ok).get x = memByte N.get x :=
  memByte_wr4 N a v ok (by omega) (by omega)

theorem not_inRange_h {h x : UInt32} (hW : ¬ InRange h 40 x) : x.toNat < h.toNat ∨ h.toNat + 40 ≤ x.toNat := by
  unfold InRange at hW
  rw [UInt32.le_iff_toNat_le] at hW
  omega

theorem not_inRange_stack {sp x : UInt32} (hsp : 2048 ≤ sp.toNat)
    (hS : ¬ InRange (sp - stackBound.toUInt32) stackBound x) : x.toNat < sp.toNat - 2048 ∨ sp.toNat ≤ x.toNat := by
  have e : (sp - stackBound.toUInt32).toNat = sp.toNat - 2048 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp [stackBound]; omega)]
    simp [stackBound]
  unfold InRange at hS
  rw [UInt32.le_iff_toNat_le, e] at hS
  simp only [stackBound] at hS
  omega

theorem esp_ret {sp : UInt32} (hsp : 2048 ≤ sp.toNat) : UInt32.add (UInt32.sub sp 4) 8 = sp + 4 := by
  apply UInt32.toNat_inj.1
  have := sp.toNat_lt
  show (sp - 4 + 8).toNat = _
  rw [UInt32.toNat_add, UInt32.toNat_add, show (sp - 4).toNat = sp.toNat - 4 from at_s hsp]
  simp
  omega

end Solutions.OpensslX25519
