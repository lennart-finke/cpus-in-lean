import Solutions.OpensslX25519.I.SmgLem
import Solutions.OpensslX25519.I.SmgRun1
import Solutions.OpensslX25519.I.Memcpy
/-!
# `x25519_scalar_mult_generic`: from the entry to the frame state of the ladder

The prologue (`I/SmgRun1`), `memcpy` of the scalar into `L + 16` (`memcpy_call`) and the clamp, as a run from the
entry (esp `Lb + 376`, `Lb = L - 32`) to `0x103946` with a frame state `CSt G N L 344 1012` whose slots are the
output pointer, the scalar words `w t` (holding the bytes of RFC 7748's `clamp k`) and the saved registers.
Prover R.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem smg_head (G : XMem) (Lb L out kp up ret : UInt32) (k : List UInt8)
    (hS : FB G.get.size Lb 384) (hfit : 0x100000 + 47024 ≤ G.get.size) (hLb : Lb.toNat + 32 = L.toNat)
    (hW : 1012 ≤ L.toNat) (himg : L.toNat + 352 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ L.toNat - 1012)
    (hret : rdRaw G.get (UInt32.add Lb 376) 4 = ret) (hup : rdRaw G.get (UInt32.add Lb 380) 4 = up)
    (hkm : kp.toNat + 32 ≤ G.get.size) (hki : kp.toNat + 32 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ kp.toNat)
    (hkL : kp.toNat + 32 ≤ L.toNat - 1012 ∨ L.toNat + 352 ≤ kp.toNat) (hk : memBytes G.get kp 32 = k)
    (a0 ebx0 ebp0 esi0 edi0 fl0 : UInt32) (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 62) :
    ∃ (N : XMem) (eax ecx edx fl : UInt32),
      Run img (St.m ⟨G.get, a0, out, kp, ebx0, UInt32.add Lb 376, ebp0, esi0, edi0, 0x103910, efl fl0, icAdd ic0 0⟩)
        (St.m ⟨N.get, eax, ecx, edx, ebx0, UInt32.add L 8, ebp0, up, edi0, 0x103946, efl fl, icAdd ic0 201⟩) ∧
      CSt G N L 344 1012 (ladSl out (rdRaw N.get (UInt32.add L 12) 4)
        (fun t => rdRaw N.get (UInt32.add L (16 + 4 * t).toUInt32) 4) esi0 edi0 ebx0 ebp0) (smgBufs N.get L) ∧
      EB (fun t => rdRaw N.get (UInt32.add L (16 + 4 * t).toUInt32) 4) (Ssl.Spec.X25519.clamp k) := by
  have htop : G.get.size ≤ ramTop := hS.top
  have hT : G.get.size < 2 ^ 32 := by unfold ramTop at htop; omega
  have hLs : Lb.toNat + 384 ≤ G.get.size := hS.fit
  have hLi := hS.img
  have hicB : ∀ m : Nat, m ≤ 1000 → (icAdd ic0 m).toNat < 2 ^ 63 := fun m hm => icB' (k := 0) (by omega)
  have hA : ∀ a b : UInt32, a.toNat = b.toNat + 32 → UInt32.add Lb a = UInt32.add L b :=
    fun a b h => uadd_shift hLb a b h
  have eLb : ∀ j : Nat, j < 384 → (UInt32.add Lb j.toUInt32).toNat = Lb.toNat + j := fun j hj => by
    rw [toNat_uadd, Nat.toUInt32, UInt32.toNat_ofNat']; omega
  have e48 : (UInt32.add Lb 48).toNat = Lb.toNat + 48 := eLb 48 (by decide)
  have e79 : (UInt32.add Lb 79).toNat = Lb.toNat + 79 := eLb 79 (by decide)
  have e16 : (UInt32.add Lb 16).toNat = Lb.toNat + 16 := eLb 16 (by decide)
  -- the frame
  have F0 : Frame G Lb 384 [(376, ret), (380, up)] := by
    intro j v hl
    simp only [List.lookup] at hl
    split at hl
    · rename_i h; simp at h; subst h; simp at hl; subst hl; exact ⟨rfl, by decide, hret⟩
    split at hl
    · rename_i h; simp at h; subst h; simp at hl; subst hl; exact ⟨rfl, by decide, hup⟩
    simp at hl
  obtain ⟨N1, R1, F1, P1⟩ := smg_pro ic0 (by omega) G Lb hS _ F0 a0 out kp ebx0 ebp0 esi0 edi0 fl0
  have hS1 : FB N1.get.size Lb 384 := hS.size_eq P1.1
  have R2 := smg_sub (icAdd ic0 4) (hicB 4 (by decide)) N1 Lb hS1 a0 out kp ebx0 ebp0 esi0 edi0 fl0
  rw [icAdd_add, icAdd_add] at R2
  have R3 := smg_st (icAdd ic0 5) (hicB 5 (by decide)) N1 Lb hS1 a0 out kp ebx0 ebp0 esi0 edi0
    (subF 4 (UInt32.add Lb 360) 320 0).2
  rw [icAdd_add, icAdd_add] at R3
  have F2 := F1.wrF (j := 40) (v := out) (h := hS1) (hj := by decide) 40 rfl rfl
  have P2 : Pres G (stF N1 Lb 384 40 out hS1 (by decide)) (OutF Lb 376) := P1.wrF (by decide)
  generalize stF N1 Lb 384 40 out hS1 (by decide) = N2 at R3 F2 P2
  have hS2 : FB N2.get.size Lb 384 := hS.size_eq P2.1
  have hu2 : rdRaw N2.get (UInt32.add Lb 380) 4 = up := F2.rd (rfl : List.lookup 380 _ = some up) 380 rfl
  have R4 := smg_mc (icAdd ic0 6) (hicB 6 (by decide)) N2 Lb up hS2 a0 out kp ebx0 ebp0 esi0 edi0
    (subF 4 (UInt32.add Lb 360) 320 0).2 hu2
  rw [icAdd_add, icAdd_add] at R4
  have F3 := (((F2.wrF (j := 36) (v := 32) (h := hS2) (hj := by decide) 36 rfl rfl).wrF (j := 32) (v := kp)
    (h := stF_FB) (hj := by decide) 32 rfl rfl).wrF (j := 28) (v := UInt32.add Lb 48) (h := stF_FB) (hj := by decide)
    28 rfl rfl).wrF (j := 24) (v := 0x103931) (h := stF_FB) (hj := by decide) 24 rfl rfl
  have P3 := (((P2.wrF (j := 36) (v := 32) (h := hS2) (hj := by decide) (by decide)).wrF (j := 32) (v := kp)
    (h := stF_FB) (hj := by decide) (by decide)).wrF (j := 28) (v := UInt32.add Lb 48) (h := stF_FB)
    (hj := by decide) (by decide)).wrF (j := 24) (v := 0x103931) (h := stF_FB) (hj := by decide) (by decide)
  generalize (stF (stF (stF (stF N2 Lb 384 36 32 hS2 _) Lb 384 32 kp stF_FB _) Lb 384 28 (UInt32.add Lb 48) stF_FB _)
    Lb 384 24 0x103931 stF_FB _) = N3 at R4 F3 P3
  have hS3 : FB N3.get.size Lb 384 := hS.size_eq P3.1
  have sz3 : N3.get.size = G.get.size := P3.1
  -- memcpy
  have hSm : FB N3.get.size (UInt32.add Lb 16) 24 := ⟨hS3.top, by rw [e16, sz3]; omega, by rw [e16]; omega⟩
  have eL8 : UInt32.add (UInt32.add Lb 16) 8 = UInt32.add Lb 24 := uadd_uadd _ _ _ _ (by decide)
  have eL12 : UInt32.add (UInt32.add Lb 16) 12 = UInt32.add Lb 28 := uadd_uadd _ _ _ _ (by decide)
  have eL16 : UInt32.add (UInt32.add Lb 16) 16 = UInt32.add Lb 32 := uadd_uadd _ _ _ _ (by decide)
  have eL20 : UInt32.add (UInt32.add Lb 16) 20 = UInt32.add Lb 36 := uadd_uadd _ _ _ _ (by decide)
  have e32 : (32 : UInt32).toNat = 32 := rfl
  have m1 : rdRaw N3.get (UInt32.add (UInt32.add Lb 16) 8) 4 = 0x103931 := by
    rw [eL8]; exact F3.rd (k := 24) (v := 0x103931) rfl 24 rfl
  have m2 : rdRaw N3.get (UInt32.add (UInt32.add Lb 16) 12) 4 = UInt32.add Lb 48 := by
    rw [eL12]; exact F3.rd (k := 28) (v := (UInt32.add Lb 48)) rfl 28 rfl
  have m3 : rdRaw N3.get (UInt32.add (UInt32.add Lb 16) 16) 4 = kp := by
    rw [eL16]; exact F3.rd (k := 32) (v := kp) rfl 32 rfl
  have m4 : rdRaw N3.get (UInt32.add (UInt32.add Lb 16) 20) 4 = 32 := by
    rw [eL20]; exact F3.rd (k := 36) (v := 32) rfl 36 rfl
  have c1 : (UInt32.add Lb 48).toNat + 32 ≤ N3.get.size := by rw [e48, sz3]; omega
  have c2 : kp.toNat + 32 ≤ N3.get.size := by rw [sz3]; omega
  have c3 : (UInt32.add Lb 48).toNat + 32 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ (UInt32.add Lb 48).toNat := by
    rw [e48]; omega
  have c5 : (UInt32.add Lb 48).toNat + 32 ≤ kp.toNat ∨ kp.toNat + 32 ≤ (UInt32.add Lb 48).toNat := by
    rw [e48]; omega
  have c6 : (UInt32.add Lb 48).toNat + 32 ≤ (UInt32.add Lb 16).toNat ∨ (UInt32.add Lb 16).toNat + 24 ≤ (UInt32.add Lb 48).toNat := by
    rw [e48, e16]; omega
  have c7 : kp.toNat + 32 ≤ (UInt32.add Lb 16).toNat ∨ (UInt32.add Lb 16).toNat + 8 ≤ kp.toNat := by
    rw [e16]; omega
  have c8 : (icAdd ic0 12).toNat + 190 < 2 ^ 63 := by
    rw [icAdd_toNat _ _ (by omega)]; omega
  obtain ⟨N4, ea4, ec4, ed4, f4, Rm, Pm, Bm⟩ := memcpy32 N3 (UInt32.add Lb 16) 0x103931 (UInt32.add Lb 48) kp
    (UInt32.add Lb 48) out kp ebx0 ebp0 up edi0 (subF 4 (UInt32.add Lb 360) 320 0).2 (icAdd ic0 12) hSm
    m1 m2 m3 m4 c1 c2 c3 hki c5 c6 c7 c8
  rw [eL12, eL8, icAdd_add ic0 12 183] at Rm
  have sz4 : N4.get.size = G.get.size := Pm.1.trans sz3
  have hS4 : FB N4.get.size Lb 384 := hS.size_eq sz4
  have R5 := smg_add (icAdd ic0 195) (hicB 195 (by decide)) N4 Lb hS4 ea4 ec4 ed4 ebx0 ebp0 up edi0 f4
  rw [icAdd_add, icAdd_add] at R5
  -- the clamp
  have ok1 : StoreOk1 Image.base Image.size N4.mem (UInt32.add Lb 48) :=
    ok1_of N4 (UInt32.add Lb 48) (UInt32.add Lb 48) 0 (by omega) (by decide) (by rw [e48, sz4]; omega)
      (by rw [e48]; omega)
  have R6 := smg_c1 (icAdd ic0 196) (hicB 196 (by decide)) N4 Lb hS4 ea4 ec4 ed4 ebx0 ebp0 up edi0
    (addF 4 (UInt32.add Lb 28) 12 0).2 ok1
  rw [icAdd_add, icAdd_add] at R6
  obtain ⟨x0, hx0⟩ : ∃ x, rdRaw N4.get (UInt32.add Lb 48) 1 = x := ⟨_, rfl⟩
  rw [hx0] at R6
  have sz5 : (CodeMem.wr1 N4 (UInt32.add Lb 48) (logicF 1 (UInt32.land x0 248)).1 ok1).get.size = G.get.size :=
    (wr1_get_size _ _ _ _).trans sz4
  have m50 := memByte_wr1_self N4 (UInt32.add Lb 48) (logicF 1 (UInt32.land x0 248)).1 ok1
  have m5o := fun (b : UInt32) (hb : b.toNat < N4.get.size) (hab : b.toNat ≠ (UInt32.add Lb 48).toNat) =>
    memByte_wr1_other N4 (UInt32.add Lb 48) (logicF 1 (UInt32.land x0 248)).1 ok1 hb hab
  have P5 := Pm.wr1 (v := (logicF 1 (UInt32.land x0 248)).1) ok1 (fun x hx => by rw [e48]; have := hx.2; omega)
  generalize CodeMem.wr1 N4 (UInt32.add Lb 48) (logicF 1 (UInt32.land x0 248)).1 ok1 = N5 at R6 sz5 m50 m5o P5
  have hS5 : FB N5.get.size Lb 384 := hS.size_eq sz5
  have R7 := smg_c2 (icAdd ic0 197) (hicB 197 (by decide)) N5 Lb hS5 ea4 ec4 ed4 ebx0 ebp0 up edi0
    (logicF 1 (UInt32.land x0 248)).2
  rw [icAdd_add, icAdd_add] at R7
  obtain ⟨x31, hx31⟩ : ∃ x, rdRaw N5.get (UInt32.add Lb 79) 1 = x := ⟨_, rfl⟩
  rw [hx31] at R7
  obtain ⟨eax1, he1⟩ : ∃ y : UInt32, y = UInt32.lor (UInt32.land x31 4294967040)
      (UInt32.land (logicF 1 (UInt32.land (UInt32.land x31 255) 63)).1 255) := ⟨_, rfl⟩
  rw [← he1] at R7
  have R8 := smg_c3 (icAdd ic0 199) (hicB 199 (by decide)) N5 Lb hS5 eax1 ec4 ed4 ebx0 ebp0 up edi0
    (logicF 1 (UInt32.land (UInt32.land x31 255) 63)).2
  rw [icAdd_add, icAdd_add] at R8
  obtain ⟨eax2, he2⟩ : ∃ y : UInt32, y = UInt32.lor (UInt32.land eax1 4294967040)
      (UInt32.land (logicF 1 (UInt32.lor (UInt32.land eax1 255) 64)).1 255) := ⟨_, rfl⟩
  rw [← he2] at R8
  have ok2 : StoreOk1 Image.base Image.size N5.mem (UInt32.add Lb 79) :=
    ok1_of N5 (UInt32.add Lb 79) (UInt32.add Lb 48) 31 (by rw [e79, e48]) (by decide) (by rw [e48, sz5]; omega)
      (by rw [e48]; omega)
  have R9 := smg_c4 (icAdd ic0 200) (hicB 200 (by decide)) N5 Lb hS5 eax2 ec4 ed4 ebx0 ebp0 up edi0
    (logicF 1 (UInt32.lor (UInt32.land eax1 255) 64)).2 ok2
  rw [icAdd_add, icAdd_add] at R9
  have sz6 : (CodeMem.wr1 N5 (UInt32.add Lb 79) (UInt32.land eax2 255) ok2).get.size = G.get.size :=
    (wr1_get_size _ _ _ _).trans sz5
  have m631 := memByte_wr1_self N5 (UInt32.add Lb 79) (UInt32.land eax2 255) ok2
  have m6o := fun (b : UInt32) (hb : b.toNat < N5.get.size) (hab : b.toNat ≠ (UInt32.add Lb 79).toNat) =>
    memByte_wr1_other N5 (UInt32.add Lb 79) (UInt32.land eax2 255) ok2 hb hab
  have P6 := P5.wr1 (v := UInt32.land eax2 255) ok2 (fun x hx => by rw [e79]; have := hx.2; omega)
  generalize CodeMem.wr1 N5 (UInt32.add Lb 79) (UInt32.land eax2 255) ok2 = N6 at R9 sz6 m631 m6o P6
  have RT := R1.trans (R2.trans (R3.trans (R4.trans (Rm.trans (R5.trans (R6.trans (R7.trans (R8.trans R9))))))))
  rw [hA 40 8 (by decide)] at RT
  -- the words of the frame
  have e40 : (UInt32.add Lb 40).toNat = Lb.toNat + 40 := eLb 40 (by decide)
  have rd6 : ∀ (j : Nat) (v : UInt32), j ∈ [40, 360, 364, 368, 372] → List.lookup j
      [(24, (0x103931 : UInt32)), (28, UInt32.add Lb 48), (32, kp), (36, (32 : UInt32)), (40, out), (360, esi0),
        (364, edi0), (368, ebx0), (372, ebp0), (376, ret), (380, up)] = some v →
      rdRaw N6.get (UInt32.add Lb j.toUInt32) 4 = v := by
    intro j v hj hl
    have ej := eLb j (by simp at hj; omega)
    rw [P6.rd' hS3.top (by rw [ej, sz3]; simp at hj; omega) (fun i hi => by
      rw [ej, e16, e48]; simp at hj; omega)]
    exact F3.rd hl j.toUInt32 (by rw [Nat.toUInt32, UInt32.toNat_ofNat']; simp at hj; omega)
  have C : CSt G N6 L 344 1012 (ladSl out (rdRaw N6.get (UInt32.add L 12) 4)
      (fun t => rdRaw N6.get (UInt32.add L (16 + 4 * t).toUInt32) 4) esi0 edi0 ebx0 ebp0) (smgBufs N6.get L) := by
    refine ⟨by rw [sz6]; exact htop, by rw [sz6]; exact hfit, hW, by rw [sz6]; omega, by omega,
      (P3.trans P6).mono fun x hx => ⟨?_, ?_, ?_⟩, ?_, smgBufs_buf N6.get L, smg_lay _ _ _ _ _ _ _ _ _⟩
    · unfold OutF; omega
    · rw [e16]; omega
    · rw [e48]; omega
    · refine ladSl_slot ?_ rfl (fun t _ => rfl) ?_ ?_ ?_ ?_
      · rw [← hA 40 8 (by decide)]; exact rd6 40 out (by simp) rfl
      · rw [← hA 360 328 (by decide)]; exact rd6 360 esi0 (by simp) rfl
      · rw [← hA 364 332 (by decide)]; exact rd6 364 edi0 (by simp) rfl
      · rw [← hA 368 336 (by decide)]; exact rd6 368 ebx0 (by simp) rfl
      · rw [← hA 372 340 (by decide)]; exact rd6 372 ebp0 (by simp) rfl
  refine ⟨N6, eax2, ec4, ed4, _, RT, C, ?_⟩
  refine smg_eb (by rw [sz6]; omega) (by rw [sz6]; exact hT) ?_
  intro i hi a ha
  have ekp : (kp + i.toUInt32).toNat = kp.toNat + i := uadd_nat_toNat kp i (by omega)
  have g3 : memByte N3.get (kp + i.toUInt32) = memByte G.get (kp + i.toUInt32) :=
    P3.2 _ (by rw [ekp]; omega) (by unfold OutF; rw [ekp]; omega)
  have ea' : UInt32.add (UInt32.add Lb 48) i.toUInt32 = a := by
    apply UInt32.toNat_inj.1; rw [toNat_uadd, e48, ha, Nat.toUInt32, UInt32.toNat_ofNat']; omega
  have gk : memByte N4.get a = memByte G.get (kp + i.toUInt32) := by rw [← ea']; exact (Bm i hi).trans g3
  have hkk : k[i]! = memByte G.get (kp + i.toUInt32) := by rw [← hk]; exact memBytes_get G.get kp 32 i hi
  rw [clamp_get k i hi, hkk]
  have sa4 : a.toNat < N4.get.size := by rw [sz4, ha]; omega
  have sa5 : a.toNat < N5.get.size := by rw [sz5, ha]; omega
  by_cases h0 : i = 0
  · subst h0
    have ea : a = UInt32.add Lb 48 := by apply UInt32.toNat_inj.1; rw [ha, e48]; omega
    subst ea
    rw [if_pos rfl, m6o _ sa5 (by rw [e48, e79]; omega), m50, ← hx0, rd1_memByte (by rw [e48, sz4]; omega), gk]
    exact clamp0 _
  by_cases h31 : i = 31
  · subst h31
    have ea : a = UInt32.add Lb 79 := by apply UInt32.toNat_inj.1; rw [ha, e79]; omega
    subst ea
    rw [if_neg (by decide), if_pos rfl, m631, he2, he1, ← hx31, rd1_memByte (by rw [e79, sz5]; omega),
      m5o _ (by rw [sz4, e79]; omega) (by rw [e79, e48]; omega), gk]
    exact clamp31 _
  · rw [if_neg h0, if_neg h31, m6o _ sa5 (by rw [ha, e79]; omega), m5o _ sa4 (by rw [ha, e48]; omega), gk]

end Solutions.OpensslX25519.I
