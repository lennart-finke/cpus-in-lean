import Solutions.OpensslX25519.I.SmgLem
import Solutions.OpensslX25519.I.SmgRun2
/-!
# `x25519_scalar_mult_generic`: from the clamp to the loop head

`fe_frombytes(x1, u)`, `fe_1(x2)`, `fe_0(z2)`, `fe_copy(x3, x1)`, `fe_1(z3)` as frame-state call steps
(`I/CSt3`, `I/CSt4`) with the argument pieces of `I/SmgRun2`, then `movl $0xfe, %esi ; xorl %edi, %edi`: the state
the ladder loop (`lad_loop`) starts from, `(x2, z2, x3, z3) = (1, 0, x1, 1)` with `x1 ≡ decodeU u`. Prover R.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem smg_init (G N : XMem) (L out b0 : UInt32) (w : Nat → UInt32) (s0 s1 s2 s3 : UInt32)
    (C : CSt G N L 344 1012 (ladSl out b0 w s0 s1 s2 s3) (smgBufs N.get L))
    (up : UInt32) (u : List UInt8) (hum : up.toNat + 32 ≤ N.get.size)
    (hui : up.toNat + 32 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ up.toNat)
    (huL : up.toNat + 32 ≤ L.toNat - 1012 ∨ L.toNat + 344 ≤ up.toNat) (hu : memBytes N.get up 32 = u)
    (eax ecx edx ebx ebp edi f : UInt32) (ic0 : UInt64) (c : Nat) (hic : ic0.toNat + c + 2000 < 2 ^ 62)
    (s00 : Machine)
    (R0 : Run img s00 (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, up, edi, 0x103946, efl f, icAdd ic0 c⟩)) :
    ∃ (N' : XMem) (vx1 vt0 vt1 : Array UInt32) (eax' ecx' edx' fl' : UInt32),
      Run img s00 (St.m ⟨N'.get, eax', ecx', edx', ebx, UInt32.add L 8, ebp, 254, (logicF 4 0).1, 0x103990,
        efl fl', icAdd ic0 (c + 1036)⟩) ∧
      CSt G N' L 344 1012 (ladSl out b0 w s0 s1 s2 s3)
        [(48, #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (88, #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (128, vx1), (168, vt0),
          (208, #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (248, vx1), (288, vt1)] ∧
      MulOut vx1 ∧ Rep vx1 (Ssl.Spec.X25519.decodeU u % Ssl.Spec.X25519.p) := by
  generalize hI : icAdd ic0 c = ic1 at R0
  have hic1 : ic1.toNat + 2000 < 2 ^ 62 := by rw [← hI, icAdd_toNat _ _ (by omega)]; omega
  have hic1' : ic1.toNat < 2 ^ 62 := by omega
  have hicL : ∀ a b : Nat, a + b ≤ 2000 → ic1.toNat + a + b < 2 ^ 62 := fun a b h => by omega
  have P1 := smg_b1 ic1 (by omega) N L C.fb eax ecx edx ebx ebp up edi f
  obtain ⟨N1, a1, c1, d1, f1, R1, C1, Mo1, V1⟩ := C.fromb (by decide) (by decide) 248 (by simp [smgBufs]) up u hum
    hui huL hu 0x103956 eax ebx ebp up (UInt32.add L 248) f ic1 4 (hicL 4 210 (by decide)) s00 (by decide)
    (R0.trans P1)
  have P2 := smg_b2 (icAdd ic1 214) (icAdd_lt hic1' (by decide)) N1 L C1.fb a1 c1 d1 ebx ebp up (UInt32.add L 248) f1
  simp only [icAdd_add] at P2
  obtain ⟨N2, a2, c2, d2, f2, R2, C2, V2⟩ := C1.fe1 (by decide) (by decide) 88 (by simp [upd, smgBufs])
    0x10395f a1 d1 ebx ebp up (UInt32.add L 248) f1 ic1 216 (hicL 216 192 (by decide)) s00 (by decide) (R1.trans P2)
  have P3 := smg_b3 (icAdd ic1 408) (icAdd_lt hic1' (by decide)) N2 L C2.fb a2 c2 d2 ebx ebp up (UInt32.add L 248) f2
  simp only [icAdd_add] at P3
  obtain ⟨N3, a3, c3, d3, f3, R3, C3, V3⟩ := C2.fe0 (by decide) (by decide) 208 (by simp [upd, smgBufs])
    0x10396b a2 d2 ebx ebp up (UInt32.add L 248) f2 ic1 410 (hicL 410 188 (by decide)) s00 (by decide) (R2.trans P3)
  have P4 := smg_b4 (icAdd ic1 598) (icAdd_lt hic1' (by decide)) N3 L C3.fb a3 c3 d3 ebx ebp up (UInt32.add L 248) f3
  simp only [icAdd_add] at P4
  obtain ⟨N4, a4, c4, d4, f4, R4, C4, V4⟩ := C3.copy (by decide) (by decide) 128 248 (by simp [upd, smgBufs])
    (vs := memWords N1.get (UInt32.add L (248 : Nat).toUInt32) 10) rfl (by decide)
    0x103976 a3 ebx ebp up (UInt32.add L 248) f3 ic1 601 (hicL 601 229 (by decide)) s00 (by decide) (R3.trans P4)
  have P5 := smg_b5 (icAdd ic1 830) (icAdd_lt hic1' (by decide)) N4 L C4.fb a4 c4 d4 ebx ebp up (UInt32.add L 248) f4
  simp only [icAdd_add] at P5
  obtain ⟨N5, a5, c5, d5, f5, R5, C5, V5⟩ := C4.fe1 (by decide) (by decide) 48 (by simp [upd, smgBufs])
    0x10397f a4 d4 ebx ebp up (UInt32.add L 248) f4 ic1 832 (hicL 832 192 (by decide)) s00 (by decide) (R4.trans P5)
  have P6 := smg_b6 (icAdd ic1 1024) (icAdd_lt hic1' (by decide)) N5 L C5.fb a5 c5 d5 ebx ebp up (UInt32.add L 248) f5
  simp only [icAdd_add] at P6
  have C5' := C5.set7 48 88 128 168 208 248 288 _ _ _ _ _ _ _ (by simp [keys_upd, upd, smgBufs]) rfl rfl rfl rfl rfl
    rfl rfl
  rw [V5, V2, V3, V4] at C5'
  refine ⟨N5, memWords N1.get (UInt32.add L (248 : Nat).toUInt32) 10, _, _, a5, c5, d5, (logicF 4 0).2, ?_, C5', Mo1,
    V1.trans (natCast_mod_p _).symm⟩
  rw [← icAdd_add, hI]
  exact R5.trans P6

end Solutions.OpensslX25519.I
