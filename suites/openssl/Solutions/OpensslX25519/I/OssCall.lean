import Solutions.OpensslX25519.I.SmgCall
import Solutions.OpensslX25519.I.OssRun
import Solutions.OpensslX25519.I.Memcmp
/-!
# `ossl_x25519` (`0x100420`) as a run

From the entry (esp `Lb + 388`, `Lb = sp - 388`, the arguments `out`, `kp`, `up` at `Lb + 392 … Lb + 400`) to the
return: `x25519_scalar_mult` (`smg_call`, frame `L = Lb + 32`), `CRYPTO_memcmp(kZeros, out, 32)` (`memcmp_call`,
`kZeros = 0x103f8c` holds 32 zero bytes of the image) and `setne`: the 32 bytes at `out` are `x25519 k u` and
`eax = retVal (x25519 k u)`. Prover R.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

set_option maxRecDepth 100000 in
theorem kz_bytes : ∀ k, k < 32 → Image.byte (16268 + k) = 0 := by decide

theorem kzeros_byte (H : XMem) (k : Nat) (hk : k < 32) : memByte H.get (UInt32.add 0x103f8c k.toUInt32) = 0 := by
  have hf : 1048576 + 47024 ≤ H.get.size := H.fits
  have e : (UInt32.add 0x103f8c k.toUInt32).toNat = 0x100000 + (16268 + k) := by
    rw [toNat_uadd, Nat.toUInt32, UInt32.toNat_ofNat']; simp only [UInt32.reduceToNat]; omega
  rw [memByte_def (by rw [e]; omega), e]
  exact (H.ok (16268 + k) (by show 16268 + k < 47024; omega)).trans (kz_bytes k hk)

theorem memBytes_zero_iff (m : ByteArray) (a : UInt32) :
    memBytes m a 32 = List.replicate 32 0 ↔ ∀ i, i < 32 → memByte m (a + i.toUInt32) = 0 := by
  unfold memBytes
  rw [List.eq_replicate_iff]
  simp only [List.length_map, List.length_range, true_and, List.mem_map, List.mem_range]
  constructor
  · intro h i hi; exact h _ ⟨i, hi, rfl⟩
  · rintro h b ⟨i, hi, rfl⟩; exact h i hi

/-- `memcmp_call` for 32 bytes, from the count `ic0` to `icAdd ic0 247`. -/
theorem memcmp32 (G : XMem) (L ret a b eax ecx edx ebx ebp esi edi fl : UInt32) (ic0 : UInt64)
    (hS : FB G.get.size L 28) (lr : rdRaw G.get (UInt32.add L 12) 4 = ret)
    (la : rdRaw G.get (UInt32.add L 16) 4 = a) (lb : rdRaw G.get (UInt32.add L 20) 4 = b)
    (ln : rdRaw G.get (UInt32.add L 24) 4 = 32) (ha : a.toNat + 32 ≤ G.get.size)
    (hb : b.toNat + 32 ≤ G.get.size) (haL : a.toNat + 32 ≤ L.toNat ∨ L.toNat + 12 ≤ a.toNat)
    (hbL : b.toNat + 32 ≤ L.toNat ∨ L.toNat + 12 ≤ b.toNat) (hic : ic0.toNat + 254 < 2 ^ 63) :
    ∃ (N : XMem) (r ecx' edx' fl' : UInt32),
      Run img (St.m ⟨G.get, eax, ecx, edx, ebx, UInt32.add L 12, ebp, esi, edi, 0x103ea0, efl fl, ic0⟩)
        (St.m ⟨N.get, r, ecx', edx', ebx, UInt32.add L 16, ebp, esi, edi, ret, efl fl', icAdd ic0 247⟩) ∧
      Pres G N (fun x => x < L.toNat ∨ L.toNat + 12 ≤ x) ∧
      (r = 0 ↔ ∀ k : Nat, k < 32 → memByte G.get (UInt32.add a k.toUInt32) = memByte G.get (UInt32.add b k.toUInt32)) :=
  memcmp_call G L ret a b 32 eax ecx edx ebx ebp esi edi fl ic0 hS lr la lb ln (by decide) ha hb haL hbL hic

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ossl_run (G : XMem) (Lb L out kp up ret esi0 : UInt32) (k u : List UInt8)
    (hS : FB G.get.size Lb 404) (hfit : 0x100000 + 47024 ≤ G.get.size) (hLb : Lb.toNat + 32 = L.toNat)
    (hW : 1012 ≤ L.toNat) (himg : Lb.toNat + 404 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ L.toNat - 1012)
    (hret : rdRaw G.get (UInt32.add Lb 388) 4 = ret) (hout : rdRaw G.get (UInt32.add Lb 392) 4 = out)
    (hkp : rdRaw G.get (UInt32.add Lb 396) 4 = kp) (hup : rdRaw G.get (UInt32.add Lb 400) 4 = up)
    (hkm : kp.toNat + 32 ≤ G.get.size) (hki : kp.toNat + 32 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ kp.toNat)
    (hkL : kp.toNat + 32 ≤ L.toNat - 1012 ∨ Lb.toNat + 404 ≤ kp.toNat) (hk : memBytes G.get kp 32 = k)
    (hum : up.toNat + 32 ≤ G.get.size) (hui : up.toNat + 32 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ up.toNat)
    (huL : up.toNat + 32 ≤ L.toNat - 1012 ∨ Lb.toNat + 404 ≤ up.toNat) (hu : memBytes G.get up 32 = u)
    (hom : out.toNat + 32 ≤ G.get.size) (hoi : out.toNat + 32 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ out.toNat)
    (hoL : out.toNat + 32 ≤ L.toNat - 1012 ∨ Lb.toNat + 404 ≤ out.toNat)
    (a0 c0 d0 ebx0 ebp0 edi0 fl0 : UInt32) (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 60) :
    ∃ (N : XMem) (ecx edx fl : UInt32),
      Run img (St.m ⟨G.get, a0, c0, d0, ebx0, UInt32.add Lb 388, ebp0, esi0, edi0, 0x100420, efl fl0, icAdd ic0 0⟩)
        (St.m ⟨N.get, retVal (Ssl.Spec.X25519.x25519 k u), ecx, edx, ebx0, UInt32.add Lb 392, ebp0, esi0, edi0, ret,
          efl fl, icAdd ic0 2064728⟩) ∧
      Pres G N (fun x => (x < L.toNat - 1012 ∨ Lb.toNat + 388 ≤ x) ∧ (x < out.toNat ∨ out.toNat + 32 ≤ x)) ∧
      memBytes N.get out 32 = Ssl.Spec.X25519.x25519 k u := by
  have htop : G.get.size ≤ ramTop := hS.top
  have hT : G.get.size < 2 ^ 32 := by unfold ramTop at htop; omega
  have hLs : Lb.toNat + 404 ≤ G.get.size := hS.fit
  have eLb : ∀ j : Nat, j < 404 → (UInt32.add Lb j.toUInt32).toNat = Lb.toNat + j := fun j hj => by
    rw [toNat_uadd, Nat.toUInt32, UInt32.toNat_ofNat']; omega
  -- the call of x25519_scalar_mult
  have R1 := oss_o1 ic0 (by omega) G Lb hS a0 c0 d0 ebx0 ebp0 esi0 edi0 fl0 out kp up hout hkp hup
  have hJt : (icAdd ic0 7).toNat = ic0.toNat + 7 := icAdd_toNat _ _ (by omega)
  generalize hJ : icAdd ic0 7 = J at R1 hJt
  have F1 := (((Frame.nil G Lb 404).wrF (j := 384) (v := esi0) (h := hS) (hj := by decide) 384 rfl rfl).wrF
    (j := 380) (v := up) (h := stF_FB) (hj := by decide) 380 rfl rfl).wrF (j := 376) (v := 0x100434) (h := stF_FB)
    (hj := by decide) 376 rfl rfl
  have P1 : Pres G _ (OutF Lb 388) := (((Pres.refl G _).wrF (j := 384) (v := esi0) (h := hS) (hj := by decide)
    (by decide)).wrF (j := 380) (v := up) (h := stF_FB) (hj := by decide) (by decide)).wrF (j := 376)
    (v := 0x100434) (h := stF_FB) (hj := by decide) (by decide)
  generalize (stF (stF (stF G Lb 404 384 esi0 hS _) Lb 404 380 up stF_FB _) Lb 404 376 0x100434 stF_FB _) = M1
    at R1 F1 P1
  have sz1 : M1.get.size = G.get.size := P1.1
  have hS1 : FB M1.get.size Lb 384 := ⟨by rw [sz1]; exact htop, by rw [sz1]; omega, by have := hS.img; omega⟩
  have hk1 : memBytes M1.get kp 32 = k := by
    rw [memBytes_pres P1 kp 32 (fun i hi => by rw [uadd_nat_toNat kp i (by omega)]; unfold OutF; omega)]; exact hk
  have hu1 : memBytes M1.get up 32 = u := by
    rw [memBytes_pres P1 up 32 (fun i hi => by rw [uadd_nat_toNat up i (by omega)]; unfold OutF; omega)]; exact hu
  obtain ⟨M2, e2, c2, d2, f2, R2, P2, V2⟩ := smg_call M1 Lb L out kp up 0x100434 k u hS1 (by rw [sz1]; exact hfit)
    hLb hW (by omega) (F1.rd (k := 376) (v := 0x100434) rfl 376 rfl) (F1.rd (k := 380) (v := up) rfl 380 rfl)
    (by rw [sz1]; exact hkm) hki (by omega) hk1 (by rw [sz1]; exact hum) hui (by omega) hu1 (by rw [sz1]; exact hom)
    hoi (by omega) a0 ebx0 ebp0 out edi0 fl0 J (by omega)
  have sz2 : M2.get.size = G.get.size := P2.1.trans sz1
  have hS2 : FB M2.get.size Lb 404 := hS.size_eq sz2
  have R3 := oss_o2 (icAdd J 2064462) (icAdd_lt (by omega) (by decide)) M2 Lb hS2 e2 c2 d2 ebx0 ebp0 out edi0 f2
  rw [icAdd_add, icAdd_add, show (2064462 + 0 : Nat) = 2064462 from rfl,
    show (2064462 + 1 : Nat) = 2064463 from rfl] at R3
  -- CRYPTO_memcmp(kZeros, out, 32)
  have R4 := oss_o3 (icAdd J 2064463) (icAdd_lt (by omega) (by decide)) M2 Lb hS2 e2 c2 d2 ebx0 ebp0 out edi0
    (addF 4 (UInt32.add Lb 380) 4 0).2
  rw [icAdd_add, icAdd_add, show (2064463 + 0 : Nat) = 2064463 from rfl,
    show (2064463 + 4 : Nat) = 2064467 from rfl] at R4
  have F3 := ((((Frame.nil M2 Lb 404).wrF (j := 380) (v := 32) (h := hS2) (hj := by decide) 380 rfl rfl).wrF
    (j := 376) (v := out) (h := stF_FB) (hj := by decide) 376 rfl rfl).wrF (j := 372) (v := 0x103f8c) (h := stF_FB)
    (hj := by decide) 372 rfl rfl).wrF (j := 368) (v := 0x100444) (h := stF_FB) (hj := by decide) 368 rfl rfl
  have P3 : Pres M2 _ (OutF Lb 384) := ((((Pres.refl M2 _).wrF (j := 380) (v := 32) (h := hS2) (hj := by decide)
    (by decide)).wrF (j := 376) (v := out) (h := stF_FB) (hj := by decide) (by decide)).wrF (j := 372)
    (v := 0x103f8c) (h := stF_FB) (hj := by decide) (by decide)).wrF (j := 368) (v := 0x100444) (h := stF_FB)
    (hj := by decide) (by decide)
  generalize (stF (stF (stF (stF M2 Lb 404 380 32 hS2 _) Lb 404 376 out stF_FB _) Lb 404 372 0x103f8c stF_FB _) Lb 404
    368 0x100444 stF_FB _) = M3 at R4 F3 P3
  have sz3 : M3.get.size = G.get.size := P3.1.trans sz2
  have e356 : (UInt32.add Lb 356).toNat = Lb.toNat + 356 := eLb 356 (by decide)
  have hSm : FB M3.get.size (UInt32.add Lb 356) 28 := ⟨by rw [sz3]; exact htop, by rw [e356, sz3]; omega,
    by rw [e356]; have := hS.img; omega⟩
  have u12 : UInt32.add (UInt32.add Lb 356) 12 = UInt32.add Lb 368 := uadd_uadd _ _ _ _ (by decide)
  have u16 : UInt32.add (UInt32.add Lb 356) 16 = UInt32.add Lb 372 := uadd_uadd _ _ _ _ (by decide)
  have u20 : UInt32.add (UInt32.add Lb 356) 20 = UInt32.add Lb 376 := uadd_uadd _ _ _ _ (by decide)
  have u24 : UInt32.add (UInt32.add Lb 356) 24 = UInt32.add Lb 380 := uadd_uadd _ _ _ _ (by decide)
  have e32 : (32 : UInt32).toNat = 32 := rfl
  have ekz : (0x103f8c : UInt32).toNat = 0x103f8c := rfl
  obtain ⟨M4, r, c4, d4, f4, R5, P5, Hr⟩ := memcmp32 M3 (UInt32.add Lb 356) 0x100444 0x103f8c out e2 c2 d2 ebx0
    ebp0 out edi0 (addF 4 (UInt32.add Lb 380) 4 0).2 (icAdd J 2064467) hSm
    (by rw [u12]; exact F3.rd (k := 368) (v := 0x100444) rfl 368 rfl)
    (by rw [u16]; exact F3.rd (k := 372) (v := 0x103f8c) rfl 372 rfl)
    (by rw [u20]; exact F3.rd (k := 376) (v := out) rfl 376 rfl)
    (by rw [u24]; exact F3.rd (k := 380) (v := 32) rfl 380 rfl)
    (by rw [ekz, sz3]; omega) (by rw [sz3]; omega) (by rw [ekz, e356]; omega)
    (by rw [e356]; omega) (by rw [icAdd_toNat _ _ (by omega)]; omega)
  rw [u12, u16, icAdd_add J 2064467 247, show (2064467 + 247 : Nat) = 2064714 from rfl] at R5
  have sz4 : M4.get.size = G.get.size := P5.1.trans sz3
  have hS4 : FB M4.get.size Lb 404 := hS.size_eq sz4
  have R6 := oss_o4 (icAdd J 2064714) (icAdd_lt (by omega) (by decide)) M4 Lb hS4 r c4 d4 ebx0 ebp0 out edi0 f4
  rw [icAdd_add, icAdd_add, show (2064714 + 0 : Nat) = 2064714 from rfl,
    show (2064714 + 1 : Nat) = 2064715 from rfl] at R6
  have e384 : (UInt32.add Lb 384).toNat = Lb.toNat + 384 := eLb 384 (by decide)
  have e388 : (UInt32.add Lb 388).toNat = Lb.toNat + 388 := eLb 388 (by decide)
  have P14 := (P2.trans P3).trans P5
  have l1 : rdRaw M4.get (UInt32.add Lb 384) 4 = esi0 := by
    rw [P14.rd' (by rw [sz1]; exact htop) (by rw [e384, sz1]; omega) (fun i hi =>
      ⟨⟨⟨by rw [e384]; omega, by rw [e384]; omega⟩, by unfold OutF; rw [e384]; omega⟩, by rw [e384, e356]; omega⟩)]
    exact F1.rd (k := 384) (v := esi0) rfl 384 rfl
  have l2 : rdRaw M4.get (UInt32.add Lb 388) 4 = ret := by
    rw [(P1.trans P14).rd' htop (by rw [e388]; omega) (fun i hi =>
      ⟨by unfold OutF; rw [e388]; omega, ⟨⟨⟨by rw [e388]; omega, by rw [e388]; omega⟩, by unfold OutF; rw [e388]; omega⟩,
        by rw [e388, e356]; omega⟩⟩)]
    exact hret
  have hz3 : memBytes M3.get out 32 = Ssl.Spec.X25519.x25519 k u := by
    rw [memBytes_pres P3 out 32 (fun i hi => by rw [uadd_nat_toNat out i (by omega), sz2]; unfold OutF; omega)]
    exact V2
  have hz4 : memBytes M4.get out 32 = Ssl.Spec.X25519.x25519 k u := by
    rw [memBytes_pres P5 out 32 (fun i hi => by rw [uadd_nat_toNat out i (by omega), sz3, e356]; omega)]
    exact hz3
  have hr : r = 0 ↔ Ssl.Spec.X25519.x25519 k u = List.replicate 32 0 := by
    rw [Hr, ← hz3, memBytes_zero_iff]
    constructor
    · intro h i hi; exact (h i hi).symm.trans (kzeros_byte M3 i hi)
    · intro h i hi; exact (kzeros_byte M3 i hi).trans (h i hi).symm
  have PG : Pres G M4 (fun x => (x < L.toNat - 1012 ∨ Lb.toNat + 388 ≤ x) ∧ (x < out.toNat ∨ out.toNat + 32 ≤ x)) :=
    (P1.trans P14).mono fun x hx => ⟨by unfold OutF; omega, ⟨⟨⟨by omega, hx.2⟩, by unfold OutF; omega⟩,
      by rw [e356]; omega⟩⟩
  rw [show (2064728 : Nat) = 7 + 2064721 from rfl, ← icAdd_add, hJ]
  by_cases h0 : r = 0
  · have hz : UInt32.land (efl (logicF 4 (UInt32.land r r)).2) 64 = 64 := Branch.zf_test_zero r (by rw [h0]; rfl)
    have R7 := oss_o5z (icAdd J 2064715) (icAdd_lt (by omega) (by decide)) M4 Lb hS4 r c4 d4 ebx0 ebp0 out edi0
      (addF 4 (UInt32.add Lb 372) 12 0).2 esi0 ret hz l1 l2
    rw [icAdd_add, icAdd_add, show (2064715 + 0 : Nat) = 2064715 from rfl,
      show (2064715 + 6 : Nat) = 2064721 from rfl] at R7
    have hv : retVal (Ssl.Spec.X25519.x25519 k u) = UInt32.lor (UInt32.land (logicF 4 0).1 4294967040) 0 := by
      unfold retVal; rw [if_pos (hr.1 h0)]; rfl
    refine ⟨M4, UInt32.lor (UInt32.land (logicF 4 0).1 4294967040) 0, d4, (logicF 4 (UInt32.land r r)).2, ?_, PG, hz4⟩
    rw [hv]
    exact R1.trans (R2.trans (R3.trans (R4.trans (R5.trans (R6.trans R7)))))
  · have hz : UInt32.land (efl (logicF 4 (UInt32.land r r)).2) 64 = 0 :=
      Branch.zf_test_ne r (fun h => h0 (UInt32.toNat_inj.1 (by rw [h]; rfl)))
    have R7 := oss_o5n (icAdd J 2064715) (icAdd_lt (by omega) (by decide)) M4 Lb hS4 r c4 d4 ebx0 ebp0 out edi0
      (addF 4 (UInt32.add Lb 372) 12 0).2 esi0 ret hz l1 l2
    rw [icAdd_add, icAdd_add, show (2064715 + 0 : Nat) = 2064715 from rfl,
      show (2064715 + 6 : Nat) = 2064721 from rfl] at R7
    have hv : retVal (Ssl.Spec.X25519.x25519 k u) = UInt32.lor (UInt32.land (logicF 4 0).1 4294967040) 1 := by
      unfold retVal; rw [if_neg (fun h => h0 (hr.2 h))]; rfl
    refine ⟨M4, UInt32.lor (UInt32.land (logicF 4 0).1 4294967040) 1, d4, (logicF 4 (UInt32.land r r)).2, ?_, PG, hz4⟩
    rw [hv]
    exact R1.trans (R2.trans (R3.trans (R4.trans (R5.trans (R6.trans R7)))))

end Solutions.OpensslX25519.I
