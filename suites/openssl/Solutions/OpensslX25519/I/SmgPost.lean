import Solutions.OpensslX25519.I.SmgLem
import Solutions.OpensslX25519.I.SmgRun2
import Solutions.OpensslX25519.I.LadFinal
/-!
# `x25519_scalar_mult_generic`: after the ladder loop

`fe_invert(z2, z2)`, `fe_mul(x2, x2, z2)` and `fe_tobytes(out, x2)` as frame-state call steps with the argument
pieces of `I/SmgRun2`: the 32 bytes at `out` become `leBytes 32 (x2 · z2⁻¹ mod p)` of the residues the loop left.
Prover R.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem smg_post (G N : XMem) (L out b : UInt32) (w : Nat → UInt32) (s0 s1 s2 s3 : UInt32)
    (vz3 vx2 vx3 vt0 vz2 vx1 vt1 : Array UInt32) (X2 Z2 : Nat)
    (C : CSt G N L 344 1012 (ladSl out b w s0 s1 s2 s3)
      [(48, vz3), (88, vx2), (128, vx3), (168, vt0), (208, vz2), (248, vx1), (288, vt1)])
    (mx2 : MulOut vx2) (mz2 : MulOut vz2) (rx2 : Rep vx2 X2) (rz2 : Rep vz2 Z2)
    (hom : out.toNat + 32 ≤ N.get.size) (hoi : out.toNat + 32 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ out.toNat)
    (hoL : out.toNat + 32 ≤ L.toNat - 1012 ∨ L.toNat + 344 ≤ out.toNat)
    (eax ecx edx ebx ebp esi edi f : UInt32) (ic0 : UInt64) (c : Nat) (hic : ic0.toNat + c + 200000 < 2 ^ 62)
    (s00 : Machine)
    (R0 : Run img s00 (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x103afd, efl f,
      icAdd ic0 c⟩)) :
    ∃ (N' : XMem) (eax' ecx' edx' esi' edi' fl' : UInt32),
      Run img s00 (St.m ⟨N'.get, eax', ecx', edx', ebx, UInt32.add L 8, ebp, esi', edi', 0x103b28, efl fl',
        icAdd ic0 (c + 157698)⟩) ∧
      Pres G N' (fun x => (x < L.toNat - 1012 ∨ L.toNat + 344 ≤ x) ∧ (x < out.toNat ∨ out.toNat + 32 ≤ x)) ∧
      rdRaw N'.get (UInt32.add L 328) 4 = s0 ∧ rdRaw N'.get (UInt32.add L 332) 4 = s1 ∧
      rdRaw N'.get (UInt32.add L 336) 4 = s2 ∧ rdRaw N'.get (UInt32.add L 340) 4 = s3 ∧
      memBytes N'.get out 32 = Ssl.Spec.X25519.leBytes 32 (Ssl.Spec.X25519.mulp X2 (Ssl.Spec.X25519.inv Z2)) := by
  generalize hI : icAdd ic0 c = ic1 at R0
  have hic1 : ic1.toNat + 200000 < 2 ^ 62 := by rw [← hI, icAdd_toNat _ _ (by omega)]; omega
  have hic1' : ic1.toNat < 2 ^ 62 := by omega
  have hicL : ∀ a b : Nat, a + b ≤ 200000 → ic1.toNat + a + b < 2 ^ 62 := fun a b h => by omega
  have hicM : ∀ a b : Nat, a + b ≤ 200000 → ic1.toNat + a + b < 2 ^ 63 := fun a b h => by omega
  have P7 := smg_b7 ic1 (by omega) N L C.fb eax ecx edx ebx ebp esi edi f
  obtain ⟨N1, a1, c1, d1, f1, R1, C1, Mo1, V1⟩ := C.inv (by decide) (by decide) 208 208 (by simp) (vs := vz2) rfl
    (mulIn_of_mulOut mz2) 0x103b0d eax ebx ebp esi (UInt32.add L 208) f ic1 4 (hicL 4 156631 (by decide)) s00
    (by decide) (R0.trans P7)
  have rz2' := Rep.inv rz2 V1
  rw [show (4 + 156631 : Nat) = 156635 from rfl] at R1
  have P8 := smg_b8 (icAdd ic1 156635) (icAdd_lt hic1' (by decide)) N1 L C1.fb a1 c1 d1 ebx ebp esi
    (UInt32.add L 208) f1
  rw [icAdd_add, icAdd_add, show (156635 + 0 : Nat) = 156635 from rfl, show (156635 + 5 : Nat) = 156640 from rfl] at P8
  obtain ⟨N2, a2, c2, d2, f2, R2, C2, Mo2, V2⟩ := C1.mul (by decide) (by decide) 88 88 208 (by simp [upd])
    (vf := vx2) (vg := memWords N1.get (UInt32.add L (208 : Nat).toUInt32) 10) rfl rfl (mulIn_of_mulOut mx2)
    (mulIn_of_mulOut Mo1) 0x103b1b a1 ebx ebp (UInt32.add L 88) (UInt32.add L 208) f1 ic1 156640
    (hicM 156640 891 (by decide)) s00 (by decide) (by decide) (R1.trans P8)
  have rx2' := Rep.mul rx2 rz2' V2
  rw [show (156640 + 891 : Nat) = 157531 from rfl] at R2
  have A9 := smg_a9 (icAdd ic1 157531) (icAdd_lt hic1' (by decide)) N2 L (hS := C2.fb) a2 c2 d2 ebx ebp
    (UInt32.add L 88) (UInt32.add L 208) f2
  rw [icAdd_add, icAdd_add, show (157531 + 0 : Nat) = 157531 from rfl, show (157531 + 1 : Nat) = 157532 from rfl] at A9
  have ho : rdRaw N2.get (UInt32.add L 8) 4 = out := C2.slot 8 out rfl
  have P10 := smg_b10 (icAdd ic1 157532) (icAdd_lt hic1' (by decide)) N2 L out C2.fb a2 c2 d2 ebx ebp
    (UInt32.add L 88) (UInt32.add L 208) (addF 4 (UInt32.add L 4) 4 0).2 ho
  rw [icAdd_add, icAdd_add, show (157532 + 0 : Nat) = 157532 from rfl, show (157532 + 3 : Nat) = 157535 from rfl] at P10
  obtain ⟨N3, a3, c3, d3, f3, R3, P3, V3⟩ := C2.tob (by decide) (by decide) 88
    (vs := memWords N2.get (UInt32.add L (88 : Nat).toUInt32) 10) rfl Mo2 out (by rw [C2.pres.1, ← C.pres.1]; exact hom) hoi hoL
    0x103b28 a2 ebx ebp (UInt32.add L 88) (UInt32.add L 208) (addF 4 (UInt32.add L 4) 4 0).2 ic1 157535
    (hicL 157535 163 (by decide)) s00 (by decide) ((R2.trans A9).trans P10)
  have hi := C2.hi; have ht := C2.top; have hw := C2.w_lo
  have sv : ∀ (k : Nat) (v : UInt32), k ∈ [328, 332, 336, 340] →
      (ladSl out b w s0 s1 s2 s3).lookup k = some v → rdRaw N3.get (UInt32.add L k.toUInt32) 4 = v := by
    intro k v hk hl
    have ek := C2.addr (k := k) (by simp at hk; omega)
    rw [P3.rd' C2.top (by rw [ek]; simp at hk; omega) (fun i hi => by rw [ek]; simp at hk; omega)]
    exact C2.slot k v hl
  refine ⟨N3, a3, c3, d3, UInt32.add L 88, UInt32.add L 208, f3, ?_, (C2.pres.trans P3).mono fun x hx =>
    ⟨hx.1, by have := hx.1; have := hx.2; omega⟩, sv 328 s0 (by simp) rfl, sv 332 s1 (by simp) rfl,
    sv 336 s2 (by simp) rfl, sv 340 s3 (by simp) rfl, ?_⟩
  · rw [show (157535 + 163 : Nat) = 157698 from rfl] at R3
    rw [← icAdd_add, hI]
    exact R3
  · rw [V3, rx2']
    rfl

end Solutions.OpensslX25519.I
