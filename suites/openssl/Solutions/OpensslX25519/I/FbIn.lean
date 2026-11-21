import Solutions.OpensslX25519.I.FbMath
import Solutions.OpensslX25519.I.Caller
import Solutions.OpensslX25519.I.MemCall
/-!
# `fe_frombytes`: the bytes it loads

Reads of 1, 2 and 4 bytes as sums of the memory bytes (`rd1_toNat`, `rd2_toNat`, `rd4_toNat'`), reads of 1 or 2
bytes outside the written region (`Pres.rd1`, `Pres.rd2`), and `decodeU` of 32 bytes as a sum
(`decodeU_horner`). Prover Q.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.OpensslX25519 Ssl.OpensslX25519

theorem shl32' (a b : UInt32) : (ShiftLeft.shiftLeft a b).toNat = a.toNat * 2 ^ (b.toNat % 32) % 2 ^ 32 := by
  show (UInt32.shiftLeft a b).toNat = _
  rw [u32_shl, nat_shl]

theorem rdBytes2_eq {mem : ByteArray} {a : UInt32} (h : a.toNat + 2 ≤ mem.size) :
    rdBytes mem a 2 = (mem.get! a.toNat).toUInt32 ||| ((mem.get! (a.toNat + 1)).toUInt32 <<< 8) := by
  unfold rdBytes
  have : a.toNat + (2 : UInt32).toNat ≤ mem.size := by simp; omega
  simp only [this, ite_true]
  rfl

theorem rd1_toNat {mem : ByteArray} {a : UInt32} (h : a.toNat + 1 ≤ mem.size) :
    (rdRaw mem a 1).toNat = (mem.get! a.toNat).toNat := by
  show (rdBytes mem a 1).toNat = _
  rw [rdBytes1_eq (by omega), memByte_def (by omega)]
  simp

theorem rd2_toNat {mem : ByteArray} {a : UInt32} (h : a.toNat + 2 ≤ mem.size) :
    (rdRaw mem a 2).toNat = (mem.get! a.toNat).toNat + 2 ^ 8 * (mem.get! (a.toNat + 1)).toNat := by
  show (rdBytes mem a 2).toNat = _
  rw [rdBytes2_eq h]
  have b0 := (mem.get! a.toNat).toNat_lt
  have b1 := (mem.get! (a.toNat + 1)).toNat_lt
  simp only [UInt32.toNat_or, shl32', UInt8.toNat_toUInt32]
  simp only [show (8 : UInt32).toNat % 32 = 8 from rfl]
  rw [Nat.mod_eq_of_lt (by omega : (mem.get! (a.toNat + 1)).toNat * 2 ^ 8 < 2 ^ 32), or_high _ _ 8 (by omega)]
  omega

theorem rd4_toNat' {mem : ByteArray} {a : UInt32} (h : a.toNat + 4 ≤ mem.size) :
    (rdRaw mem a 4).toNat = (mem.get! a.toNat).toNat + 2 ^ 8 * (mem.get! (a.toNat + 1)).toNat +
      2 ^ 16 * (mem.get! (a.toNat + 2)).toNat + 2 ^ 24 * (mem.get! (a.toNat + 3)).toNat := by
  show (rdBytes mem a 4).toNat = _
  rw [rdBytes4_eq h]
  have b0 := (mem.get! a.toNat).toNat_lt
  have b1 := (mem.get! (a.toNat + 1)).toNat_lt
  have b2 := (mem.get! (a.toNat + 2)).toNat_lt
  have b3 := (mem.get! (a.toNat + 3)).toNat_lt
  simp only [UInt32.toNat_or, shl32', UInt8.toNat_toUInt32]
  simp only [show (8 : UInt32).toNat % 32 = 8 from rfl, show (16 : UInt32).toNat % 32 = 16 from rfl,
    show (24 : UInt32).toNat % 32 = 24 from rfl]
  rw [Nat.mod_eq_of_lt (by omega : (mem.get! (a.toNat + 1)).toNat * 2 ^ 8 < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : (mem.get! (a.toNat + 2)).toNat * 2 ^ 16 < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : (mem.get! (a.toNat + 3)).toNat * 2 ^ 24 < 2 ^ 32)]
  rw [or_high _ _ 8 (by omega), or_high _ _ 16 (by omega), or_high _ _ 24 (by omega)]
  omega

/-- A byte where `P` holds is that of `G`. -/
theorem pres_get {G N : XMem} {P : Nat → Prop} (hP : Pres G N P) (htop : G.get.size ≤ ramTop)
    {x : Nat} (hx : x < G.get.size) (hp : P x) : N.get.get! x = G.get.get! x := by
  have hb : (x.toUInt32).toNat = x := by
    rw [Nat.toUInt32, UInt32.toNat_ofNat']; unfold ramTop at htop; omega
  have := hP.2 x.toUInt32 (by rw [hb]; exact hx) (by rw [hb]; exact hp)
  rwa [memByte_def (by rw [hb, hP.1]; exact hx), memByte_def (by rw [hb]; exact hx), hb] at this

theorem _root_.Solutions.OpensslX25519.Pres.rd1 {G N : XMem} {P : Nat → Prop} (hP : Pres G N P)
    (htop : G.get.size ≤ ramTop) {a : UInt32} (ha : a.toNat + 1 ≤ G.get.size) (hout : P a.toNat) :
    rdRaw N.get a 1 = rdRaw G.get a 1 := by
  apply UInt32.toNat_inj.1
  rw [rd1_toNat (by rw [hP.1]; exact ha), rd1_toNat ha, pres_get hP htop (by omega) hout]

theorem _root_.Solutions.OpensslX25519.Pres.rd2 {G N : XMem} {P : Nat → Prop} (hP : Pres G N P)
    (htop : G.get.size ≤ ramTop) {a : UInt32} (ha : a.toNat + 2 ≤ G.get.size) (h0 : P a.toNat)
    (h1 : P (a.toNat + 1)) : rdRaw N.get a 2 = rdRaw G.get a 2 := by
  apply UInt32.toNat_inj.1
  rw [rd2_toNat (by rw [hP.1]; exact ha), rd2_toNat ha, pres_get hP htop (by omega) h0,
    pres_get hP htop (by omega) h1]

theorem decodeU_horner (f : Nat → UInt8) :
    Ssl.Spec.X25519.decodeU ((List.range 32).map f) = (f 0).toNat + 256 * ((f 1).toNat + 256 * ((f 2).toNat + 256 * ((f 3).toNat + 256 * ((f 4).toNat + 256 * ((f 5).toNat + 256 * ((f 6).toNat + 256 * ((f 7).toNat + 256 * ((f 8).toNat + 256 * ((f 9).toNat + 256 * ((f 10).toNat + 256 * ((f 11).toNat + 256 * ((f 12).toNat + 256 * ((f 13).toNat + 256 * ((f 14).toNat + 256 * ((f 15).toNat + 256 * ((f 16).toNat + 256 * ((f 17).toNat + 256 * ((f 18).toNat + 256 * ((f 19).toNat + 256 * ((f 20).toNat + 256 * ((f 21).toNat + 256 * ((f 22).toNat + 256 * ((f 23).toNat + 256 * ((f 24).toNat + 256 * ((f 25).toNat + 256 * ((f 26).toNat + 256 * ((f 27).toNat + 256 * ((f 28).toNat + 256 * ((f 29).toNat + 256 * ((f 30).toNat + 256 * ((f 31 &&& 127).toNat + 256 * (0)))))))))))))))))))))))))))))))) := by
  rfl

theorem u8_and127 (b : UInt8) : (b &&& 127).toNat = b.toNat % 128 := by
  rw [UInt8.toNat_and, show (127 : UInt8).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem mulOut_fn (w : Nat → UInt32) (h : ∀ i, i < 10 → (sv (w i)).natAbs * 100 ≤ 101 * 2 ^ (25 - i % 2)) :
    MulOut (Array.ofFn (n := 10) fun i => w i.val) := by
  refine ⟨by simp, fun i hi => ?_⟩
  have := h i hi
  unfold sv at this
  rwa [getElem!_pos _ i (by simp; omega), Array.getElem_ofFn]

theorem feValI_fn (w : Nat → UInt32) :
    feValI (Array.ofFn (n := 10) fun i => w i.val) =
      L10.val ⟨sv (w 0), sv (w 1), sv (w 2), sv (w 3), sv (w 4), sv (w 5), sv (w 6), sv (w 7), sv (w 8), sv (w 9)⟩ := by
  rw [← lift_val]; rfl

theorem bnd_even (x : Int) (h1 : -33889976 ≤ x) (h2 : x ≤ 33889976) : x.natAbs * 100 ≤ 101 * 2 ^ 25 := by omega
theorem bnd_odd (x : Int) (h1 : -16944988 ≤ x) (h2 : x ≤ 16944988) : x.natAbs * 100 ≤ 101 * 2 ^ 24 := by omega

end Solutions.OpensslX25519.I
