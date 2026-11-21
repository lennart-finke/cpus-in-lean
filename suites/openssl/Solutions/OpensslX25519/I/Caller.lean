import Solutions.OpensslX25519.Frame
import Solutions.OpensslX25519.Peel
import Solutions.OpensslX25519.I.Base
/-!
# Callers of the field functions: what a call keeps

A callee's contract states `Pres G N P`: the memory after the call agrees with the memory before it at
the addresses satisfying `P` (outside the callee's stack window and its output buffer). In the caller
this gives the words of its own frame (`Frame.pres`) and the limb vectors of the buffers the call does
not write (`memWords_pres`); `Pres.trans` chains the calls.
-/
namespace Solutions.OpensslX25519
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

theorem Pres.trans {G N M : XMem} {P Q : Nat → Prop} (h1 : Pres G N P) (h2 : Pres N M Q) :
    Pres G M (fun x => P x ∧ Q x) :=
  ⟨h2.1.trans h1.1, fun a ha hpq => (h2.2 a (by rw [h1.1]; exact ha) hpq.2).trans (h1.2 a ha hpq.1)⟩

/-- A word load at addresses satisfying `P`, from the memory after the call. -/
theorem Pres.rd' {N N' : XMem} {P : Nat → Prop} (hP : Pres N N' P) (htop : N.get.size ≤ ramTop)
    {a : UInt32} (ha : a.toNat + 4 ≤ N.get.size) (hout : ∀ k, k < 4 → P (a.toNat + k)) :
    rdRaw N'.get a 4 = rdRaw N.get a 4 := hP.rd htop ha hout

theorem toNat_add4i {q : UInt32} {i : Nat} (hq : q.toNat + 4 * i < 2 ^ 32) (hi : i < 2 ^ 30) :
    (q + 4 * i.toUInt32).toNat = q.toNat + 4 * i := by
  rw [UInt32.toNat_add, UInt32.toNat_mul, Nat.toUInt32, UInt32.toNat_ofNat']
  have : (4 : UInt32).toNat = 4 := rfl
  rw [this, Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (a := 4 * i) (by omega)]
  exact Nat.mod_eq_of_lt hq

/-- The ten words of a buffer the call does not write. -/
theorem memWords_pres {N N' : XMem} {P : Nat → Prop} (hP : Pres N N' P) (htop : N.get.size ≤ ramTop)
    {q : UInt32} (hq : q.toNat + 40 ≤ N.get.size) (hout : ∀ k, k < 40 → P (q.toNat + k)) :
    memWords N'.get q 10 = memWords N.get q 10 := by
  unfold memWords
  congr 1
  funext i
  have hi := i.isLt
  have e := toNat_add4i (q := q) (i := i.val) (by unfold ramTop at htop; omega) (by omega)
  show rdRaw N'.get _ 4 = rdRaw N.get _ 4
  exact hP.rd htop (by rw [e]; omega) (fun k hk => by rw [e, Nat.add_assoc]; exact hout _ (by omega))

/-- The listed words of a region the call does not write. -/
theorem Frame.pres {N N' : XMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame N b n l)
    (hS : FB N.get.size b n) {P : Nat → Prop} (hP : Pres N N' P)
    (h : ∀ x, b.toNat ≤ x → x < b.toNat + n → P x) : Frame N' b n l := by
  intro k v hl
  obtain ⟨h1, h2, h3⟩ := hF k v hl
  refine ⟨h1, h2, ?_⟩
  have e := Frame.add_toNat hS (k := k) (by omega)
  have := hS.fit
  rw [← h3]
  exact hP.rd hS.top (by rw [e]; omega) (fun j hj => h _ (by rw [e]; omega) (by rw [e]; omega))

theorem FB.pres {N N' : XMem} {b : UInt32} {n : Nat} (hS : FB N.get.size b n) {P : Nat → Prop}
    (hP : Pres N N' P) : FB N'.get.size b n := hS.size_eq hP.1

end Solutions.OpensslX25519
