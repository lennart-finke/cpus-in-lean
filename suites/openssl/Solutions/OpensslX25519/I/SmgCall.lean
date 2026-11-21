import Solutions.OpensslX25519.I.SmgHead
import Solutions.OpensslX25519.I.SmgInit
import Solutions.OpensslX25519.I.SmgPost
import Solutions.OpensslX25519.I.LadLoop
/-!
# `x25519_scalar_mult_generic` as a callee

The whole run (`smg_head`, `smg_init`, `lad_loop` over 255 bits, `smg_post`, then `OPENSSL_cleanse` of the scalar
copy and the epilogue, `I/SmgRun1`) from the entry (esp `Lb + 376`, `Lb = L - 32`; return address there, the u
pointer at `Lb + 380`, `out` in `ecx`, the scalar pointer in `edx`) to the return: it writes only
`[L - 1012, L + 344)` and the 32 bytes at `out`, which become RFC 7748's `x25519 k u` (`ladder_eq`,
`decodeScalar_even`). Prover R.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem smg_call (G : XMem) (Lb L out kp up ret : UInt32) (k u : List UInt8)
    (hS : FB G.get.size Lb 384) (hfit : 0x100000 + 47024 ≤ G.get.size) (hLb : Lb.toNat + 32 = L.toNat)
    (hW : 1012 ≤ L.toNat) (himg : L.toNat + 352 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ L.toNat - 1012)
    (hret : rdRaw G.get (UInt32.add Lb 376) 4 = ret) (hup : rdRaw G.get (UInt32.add Lb 380) 4 = up)
    (hkm : kp.toNat + 32 ≤ G.get.size) (hki : kp.toNat + 32 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ kp.toNat)
    (hkL : kp.toNat + 32 ≤ L.toNat - 1012 ∨ L.toNat + 352 ≤ kp.toNat) (hk : memBytes G.get kp 32 = k)
    (hum : up.toNat + 32 ≤ G.get.size) (hui : up.toNat + 32 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ up.toNat)
    (huL : up.toNat + 32 ≤ L.toNat - 1012 ∨ L.toNat + 352 ≤ up.toNat) (hu : memBytes G.get up 32 = u)
    (hom : out.toNat + 32 ≤ G.get.size) (hoi : out.toNat + 32 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ out.toNat)
    (hoL : out.toNat + 32 ≤ L.toNat - 1012 ∨ L.toNat + 352 ≤ out.toNat)
    (a0 ebx0 ebp0 esi0 edi0 fl0 : UInt32) (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 61) :
    ∃ (N : XMem) (eax ecx edx fl : UInt32),
      Run img (St.m ⟨G.get, a0, out, kp, ebx0, UInt32.add Lb 376, ebp0, esi0, edi0, 0x103910, efl fl0, icAdd ic0 0⟩)
        (St.m ⟨N.get, eax, ecx, edx, ebx0, UInt32.add Lb 380, ebp0, esi0, edi0, ret, efl fl, icAdd ic0 2064462⟩) ∧
      Pres G N (fun x => (x < L.toNat - 1012 ∨ L.toNat + 344 ≤ x) ∧ (x < out.toNat ∨ out.toNat + 32 ≤ x)) ∧
      memBytes N.get out 32 = Ssl.Spec.X25519.x25519 k u := by
  have htop : G.get.size ≤ ramTop := hS.top
  have hT : G.get.size < 2 ^ 32 := by unfold ramTop at htop; omega
  have hLs : Lb.toNat + 384 ≤ G.get.size := hS.fit
  have hA : ∀ a b : UInt32, a.toNat = b.toNat + 32 → UInt32.add Lb a = UInt32.add L b :=
    fun a b h => uadd_shift hLb a b h
  have eLb : ∀ j : Nat, j < 384 → (UInt32.add Lb j.toUInt32).toNat = Lb.toNat + j := fun j hj => by
    rw [toNat_uadd, Nat.toUInt32, UInt32.toNat_ofNat']; omega
  have hSL : FB G.get.size L 344 := ⟨htop, by omega, by omega⟩
  -- head
  obtain ⟨N1, e1, c1, d1, f1, R1, C1, EB1⟩ := smg_head G Lb L out kp up ret k hS hfit hLb hW himg hret hup hkm
    hki hkL hk a0 ebx0 ebp0 esi0 edi0 fl0 ic0 (by omega)
  have sz1 : N1.get.size = G.get.size := C1.pres.1
  have hu1 : memBytes N1.get up 32 = u := by
    rw [memBytes_pres C1.pres up 32 (fun i hi => by rw [uadd_nat_toNat up i (by omega)]; omega)]; exact hu
  -- init
  obtain ⟨N2, vx1, vt0, vt1, e2, c2, d2, f2, R2, C2, mx1, rx1⟩ := smg_init G N1 L out _ _ esi0 edi0 ebx0 ebp0 C1 up
    u (by rw [sz1]; exact hum) hui (by omega) hu1 e1 c1 d1 ebx0 ebp0 edi0 f1 ic0 201 (by omega) _ R1
  rw [show (201 + 1036 : Nat) = 1237 from rfl] at R2
  -- the loop
  have hlen : (Ssl.Spec.X25519.clamp k).length = 32 := by simp [Ssl.Spec.X25519.clamp]
  have r1 : Rep #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0] 1 := by unfold Rep; decide
  have r0 : Rep #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0 := by unfold Rep; decide
  have m1 : MulOut #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by unfold MulOut; decide
  have m0 : MulOut #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by unfold MulOut; decide
  obtain ⟨N3, bitv, vz3', vx2', vx3', vt0', vz2', vt1', e3, c3, d3, b3, p3, s3, f3, R3, C3, mz3, mx2, mx3, mz2,
      hbv, rx2, rz2, rx3, rz3⟩ :=
    lad_loop G L hSL out esi0 edi0 ebx0 ebp0 _ (Ssl.Spec.X25519.clamp k) EB1 hlen vx1 (mulIn_of_mulOut mx1) _ rx1 ic0 _
      255 N2 _ _ _ _ _ _ _ 1 0 _ 1 (logicF 4 0).1 1237 e2 c2 d2 ebx0 ebp0 f2 (by decide) (by decide) C2 m1 m1 mx1 m0
      r1 r1 rx1 r0 (Or.inl rfl) (by unfold ladK; omega) R2
  rw [show (1237 + ladK * 255 : Nat) = 1906597 from rfl] at R3
  -- after the loop
  obtain ⟨N4, e4, c4, d4, s4, i4, f4, R4, P4, l328, l332, l336, l340, V4⟩ := smg_post G N3 L out bitv _ esi0 edi0
    ebx0 ebp0 _ _ _ _ _ vx1 _ _ _ C3 mx2 mz2 rx2 rz2 (by rw [C3.pres.1]; exact hom) hoi (by omega) e3 c3 d3 b3 p3 s3
    bitv f3 ic0 1906597 (by omega) _ R3
  rw [show (1906597 + 157698 : Nat) = 2064295 from rfl, ← hA 40 8 (by decide)] at R4
  have sz4 : N4.get.size = G.get.size := P4.1
  have hS4 : FB N4.get.size Lb 384 := hS.size_eq sz4
  -- cleanse and epilogue
  have R5 := smg_cl (icAdd ic0 2064295) (icAdd_lt (by omega) (by decide)) N4 Lb hS4 e4 c4 d4 b3 p3 s4 i4 f4
  rw [icAdd_add, icAdd_add, show (2064295 + 0 : Nat) = 2064295 from rfl,
    show (2064295 + 4 : Nat) = 2064299 from rfl] at R5
  have F5 := (((Frame.nil N4 Lb 384).wrF (j := 36) (v := 32) (h := hS4) (hj := by decide) 36 rfl rfl).wrF (j := 32)
    (v := UInt32.add Lb 48) (h := stF_FB) (hj := by decide) 32 rfl rfl).wrF (j := 28) (v := 0x103b34) (h := stF_FB)
    (hj := by decide) 28 rfl rfl
  have P5 : Pres N4 _ (OutF Lb 40) := (((Pres.refl N4 _).wrF (j := 36) (v := 32) (h := hS4) (hj := by decide)
    (by decide)).wrF (j := 32) (v := UInt32.add Lb 48) (h := stF_FB) (hj := by decide) (by decide)).wrF (j := 28)
    (v := 0x103b34) (h := stF_FB) (hj := by decide) (by decide)
  generalize (stF (stF (stF N4 Lb 384 36 32 hS4 _) Lb 384 32 (UInt32.add Lb 48) stF_FB _) Lb 384 28 0x103b34
    stF_FB _) = N5 at R5 F5 P5
  have sz5 : N5.get.size = G.get.size := P5.1.trans sz4
  have e8 : (UInt32.add Lb 8).toNat = Lb.toNat + 8 := eLb 8 (by decide)
  have e48 : (UInt32.add Lb 48).toNat = Lb.toNat + 48 := eLb 48 (by decide)
  have hSc : FB N5.get.size (UInt32.add Lb 8) 32 := ⟨by rw [sz5]; exact htop, by rw [e8, sz5]; omega,
    by rw [e8]; have := hS.img; omega⟩
  have u20 : UInt32.add (UInt32.add Lb 8) 20 = UInt32.add Lb 28 := uadd_uadd _ _ _ _ (by decide)
  have u24 : UInt32.add (UInt32.add Lb 8) 24 = UInt32.add Lb 32 := uadd_uadd _ _ _ _ (by decide)
  have u28 : UInt32.add (UInt32.add Lb 8) 28 = UInt32.add Lb 36 := uadd_uadd _ _ _ _ (by decide)
  obtain ⟨N6, e6, c6, d6, f6, R6, P6, Z6⟩ := cleanse32 N5 (UInt32.add Lb 8) 0x103b34 (UInt32.add Lb 48)
    (UInt32.add Lb 48) c4 d4 b3 p3 s4 i4 f4 (icAdd ic0 2064299) hSc
    (by rw [u20]; exact F5.rd (k := 28) (v := 0x103b34) rfl 28 rfl)
    (by rw [u24]; exact F5.rd (k := 32) (v := UInt32.add Lb 48) rfl 32 rfl)
    (by rw [u28]; exact F5.rd (k := 36) (v := 32) rfl 36 rfl)
    (by rw [e48, sz5]; omega) (by rw [e48]; have := hS.img; omega) (by rw [e48, e8]; omega)
    (by rw [icAdd_toNat _ _ (by omega)]; omega)
  rw [u20, u24, icAdd_add ic0 2064299 157, show (2064299 + 157 : Nat) = 2064456 from rfl] at R6
  have sz6 : N6.get.size = G.get.size := P6.1.trans sz5
  have hS6 : FB N6.get.size Lb 384 := hS.size_eq sz6
  have R7 := smg_add2 (icAdd ic0 2064456) (icAdd_lt (by omega) (by decide)) N6 Lb hS6 e6 c6 d6 b3 p3 s4 i4 f6
  rw [icAdd_add, icAdd_add, show (2064456 + 0 : Nat) = 2064456 from rfl,
    show (2064456 + 1 : Nat) = 2064457 from rfl] at R7
  -- the memory after the post part, read back at the end
  have P46 : Pres N4 N6 (fun x => OutF Lb 40 x ∧ ((x < (UInt32.add Lb 8).toNat ∨ (UInt32.add Lb 8).toNat + 20 ≤ x) ∧
      (x < (UInt32.add Lb 48).toNat ∨ (UInt32.add Lb 48).toNat + 32 ≤ x))) := P5.trans P6
  have rd46 : ∀ j : Nat, 80 ≤ j → j + 4 ≤ 384 → rdRaw N6.get (UInt32.add Lb j.toUInt32) 4 =
      rdRaw N4.get (UInt32.add Lb j.toUInt32) 4 := fun j h1 h2 => by
    have ej := eLb j (by omega)
    exact P46.rd' (by rw [sz4]; exact htop) (by rw [ej, sz4]; omega) (fun i hi => by
      rw [ej]; unfold OutF; rw [e8, e48]; omega)
  have l5 : ∀ (j : Nat) (b : UInt32) (v : UInt32), j = b.toNat + 32 → 80 ≤ j → j + 4 ≤ 384 →
      rdRaw N4.get (UInt32.add L b) 4 = v → rdRaw N6.get (UInt32.add Lb j.toUInt32) 4 = v := by
    intro j b v hjb h1 h2 hv
    rw [rd46 j h1 h2, hA j.toUInt32 b (by rw [Nat.toUInt32, UInt32.toNat_ofNat']; omega)]
    exact hv
  have e376 : (UInt32.add Lb 376).toNat = Lb.toNat + 376 := eLb 376 (by decide)
  have hret4 : rdRaw N4.get (UInt32.add L 344) 4 = ret := by
    rw [← hA 376 344 (by decide), ← hret]
    exact P4.rd' htop (by rw [e376]; omega) (fun i hi => by rw [e376]; omega)
  have R8 := smg_epi (icAdd ic0 2064457) (icAdd_lt (by omega) (by decide)) N6 Lb hS6 e6 c6 d6 b3 p3 s4 i4
    (addF 4 (UInt32.add Lb 32) 328 0).2 esi0 edi0 ebx0 ebp0 ret
    (l5 360 328 esi0 (by decide) (by decide) (by decide) l328) (l5 364 332 edi0 (by decide) (by decide) (by decide) l332)
    (l5 368 336 ebx0 (by decide) (by decide) (by decide) l336) (l5 372 340 ebp0 (by decide) (by decide) (by decide) l340)
    (l5 376 344 ret (by decide) (by decide) (by decide) hret4)
  rw [icAdd_add, icAdd_add, show (2064457 + 0 : Nat) = 2064457 from rfl,
    show (2064457 + 5 : Nat) = 2064462 from rfl] at R8
  refine ⟨N6, e6, c6, d6, _, R4.trans (R5.trans (R6.trans (R7.trans R8))), ?_, ?_⟩
  · exact (P4.trans P46).mono fun x hx => ⟨hx, by unfold OutF; rw [e8, e48]; omega⟩
  · rw [memBytes_pres P46 out 32 (fun i hi => by
      rw [uadd_nat_toNat out i (by omega), sz4]; unfold OutF; rw [e8, e48]; omega), V4]
    unfold Ssl.Spec.X25519.x25519
    rw [ladder_eq _ _ (decodeScalar_even k)]
    rfl

end Solutions.OpensslX25519.I
