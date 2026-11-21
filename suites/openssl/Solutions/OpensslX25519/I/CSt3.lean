import Solutions.OpensslX25519.I.CSt2
import Solutions.OpensslX25519.I.FeSmall
import Solutions.OpensslX25519.I.InvCall
/-!
# Call steps of the frame state for `fe_0`, `fe_1`, `fe_copy`, `fe_invert`

The proof of `CSt.sq` (`I/CSt`) with the contracts `fe_0_call`, `fe_1_call`, `fe_copy_call` (`I/FeSmall`) and
`fe_invert_call` (`I/InvCall`), for `x25519_scalar_mult_generic`. Prover P.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

/-- A call of `fe_0(L + kd)` from the frame. -/
theorem CSt.fe0 {G N : XMem} {L : UInt32} {n W : Nat} {sl : List (Nat × UInt32)} {bf : List (Nat × Array UInt32)}
    (C : CSt G N L n W sl bf) (hW : 16 ≤ W) (hn : 8 ≤ n) (kd : Nat) (hkd : kd ∈ bf.map Prod.fst)
    (r a d ebx ebp esi edi f : UInt32) (ic0 : UInt64) (c : Nat) (hic : ic0.toNat + c + 188 < 2 ^ 62) (s0 : Machine)
    (h4 : (4 : UInt32).toNat + 4 ≤ n)
    (R : Run img s0 (St.m ⟨(stF N L n 4 r C.fb h4).get, a, UInt32.add L kd.toUInt32, d, ebx,
      UInt32.add L 4, ebp, esi, edi, 0x1021e0, efl f, icAdd ic0 c⟩)) :
    ∃ (N' : XMem) (eax ecx edx fl : UInt32),
      Run img s0 (St.m ⟨N'.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, r, efl fl, icAdd ic0 (c + 188)⟩) ∧
      CSt G N' L n W sl (upd bf kd (memWords N'.get (UInt32.add L kd.toUInt32) 10)) ∧
      memWords N'.get (UInt32.add L kd.toUInt32) 10 = #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  have bd := lay_buf C.lay hkd
  have ed := C.addr (k := kd) (by omega)
  have e4 : (UInt32.add L 4).toNat = L.toNat + 4 := C.addr (k := 4) (by omega)
  have hsz : (stF N L n 4 r C.fb h4).get.size = N.get.size := stF_size
  have P1 : Pres N (stF N L n 4 r C.fb h4) (OutF L 8) := (Pres.refl N _).wrF (by decide)
  have hi := C.hi; have hw := C.w_lo; have himg := C.imgok; have htop := C.top
  have F1 : Facts1W 20 (stF N L n 4 r C.fb h4).get.size (UInt32.add L 4).toNat (UInt32.add L kd.toUInt32).toNat
      (UInt32.add L kd.toUInt32).toNat := by
    rw [hsz, e4, ed]
    exact ⟨htop, C.fit, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  have hret : rdRaw (stF N L n 4 r C.fb h4).get (UInt32.add L 4) 4 = r :=
    ((Frame.nil N L n).wrF 4 (j := 4) (v := r) (h := C.fb) (hj := h4) rfl rfl).rd
      (rfl : List.lookup 4 _ = some r) 4 rfl
  obtain ⟨N', eax, ecx, edx, fl, Rc, Pc, Va⟩ := fe_0_call (stF N L n 4 r C.fb h4) (UInt32.add L 4)
    (UInt32.add L kd.toUInt32) r F1 hret a d ebx ebp esi edi f (icAdd ic0 c)
    (by rw [icAdd_toNat _ _ (by omega)]; omega)
  rw [icAdd_add, uadd_four] at Rc
  refine ⟨N', eax, ecx, edx, fl, R.trans Rc, C.next kd hkd ((P1.trans Pc).mono fun x hx => ⟨?_, ?_⟩), Va⟩
  · unfold OutF; have := hx.1; omega
  · have e464 : (UInt32.add L 4 - 20).toNat = L.toNat + 4 - 20 := by
      rw [UInt32.toNat_sub, e4]; unfold ramTop at htop; simp only [UInt32.reduceToNat]; omega
    unfold OutH OutF; rw [e464, ed]; omega

/-- A call of `fe_1(L + kd)` from the frame. -/
theorem CSt.fe1 {G N : XMem} {L : UInt32} {n W : Nat} {sl : List (Nat × UInt32)} {bf : List (Nat × Array UInt32)}
    (C : CSt G N L n W sl bf) (hW : 20 ≤ W) (hn : 8 ≤ n) (kd : Nat) (hkd : kd ∈ bf.map Prod.fst)
    (r a d ebx ebp esi edi f : UInt32) (ic0 : UInt64) (c : Nat) (hic : ic0.toNat + c + 192 < 2 ^ 62) (s0 : Machine)
    (h4 : (4 : UInt32).toNat + 4 ≤ n)
    (R : Run img s0 (St.m ⟨(stF N L n 4 r C.fb h4).get, a, UInt32.add L kd.toUInt32, d, ebx,
      UInt32.add L 4, ebp, esi, edi, 0x1021f0, efl f, icAdd ic0 c⟩)) :
    ∃ (N' : XMem) (eax ecx edx fl : UInt32),
      Run img s0 (St.m ⟨N'.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, r, efl fl, icAdd ic0 (c + 192)⟩) ∧
      CSt G N' L n W sl (upd bf kd (memWords N'.get (UInt32.add L kd.toUInt32) 10)) ∧
      memWords N'.get (UInt32.add L kd.toUInt32) 10 = #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  have bd := lay_buf C.lay hkd
  have ed := C.addr (k := kd) (by omega)
  have e4 : (UInt32.add L 4).toNat = L.toNat + 4 := C.addr (k := 4) (by omega)
  have hsz : (stF N L n 4 r C.fb h4).get.size = N.get.size := stF_size
  have P1 : Pres N (stF N L n 4 r C.fb h4) (OutF L 8) := (Pres.refl N _).wrF (by decide)
  have hi := C.hi; have hw := C.w_lo; have himg := C.imgok; have htop := C.top
  have F1 : Facts1W 24 (stF N L n 4 r C.fb h4).get.size (UInt32.add L 4).toNat (UInt32.add L kd.toUInt32).toNat
      (UInt32.add L kd.toUInt32).toNat := by
    rw [hsz, e4, ed]
    exact ⟨htop, C.fit, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  have hret : rdRaw (stF N L n 4 r C.fb h4).get (UInt32.add L 4) 4 = r :=
    ((Frame.nil N L n).wrF 4 (j := 4) (v := r) (h := C.fb) (hj := h4) rfl rfl).rd
      (rfl : List.lookup 4 _ = some r) 4 rfl
  obtain ⟨N', eax, ecx, edx, fl, Rc, Pc, Va⟩ := fe_1_call (stF N L n 4 r C.fb h4) (UInt32.add L 4)
    (UInt32.add L kd.toUInt32) r F1 hret a d ebx ebp esi edi f (icAdd ic0 c)
    (by rw [icAdd_toNat _ _ (by omega)]; omega)
  rw [icAdd_add, uadd_four] at Rc
  refine ⟨N', eax, ecx, edx, fl, R.trans Rc, C.next kd hkd ((P1.trans Pc).mono fun x hx => ⟨?_, ?_⟩), Va⟩
  · unfold OutF; have := hx.1; omega
  · have e464 : (UInt32.add L 4 - 24).toNat = L.toNat + 4 - 24 := by
      rw [UInt32.toNat_sub, e4]; unfold ramTop at htop; simp only [UInt32.reduceToNat]; omega
    unfold OutH OutF; rw [e464, ed]; omega

/-- A call of `fe_copy(L + kd, L + ks)` from the frame. -/
theorem CSt.copy {G N : XMem} {L : UInt32} {n W : Nat} {sl : List (Nat × UInt32)} {bf : List (Nat × Array UInt32)}
    (C : CSt G N L n W sl bf) (hW : 20 ≤ W) (hn : 8 ≤ n) (kd ks : Nat) (hkd : kd ∈ bf.map Prod.fst)
    {vs : Array UInt32} (hks : bf.lookup ks = some vs) (hdk : kd + 40 ≤ ks)
    (r a ebx ebp esi edi f : UInt32) (ic0 : UInt64) (c : Nat) (hic : ic0.toNat + c + 229 < 2 ^ 62) (s0 : Machine)
    (h4 : (4 : UInt32).toNat + 4 ≤ n)
    (R : Run img s0 (St.m ⟨(stF N L n 4 r C.fb h4).get, a, UInt32.add L kd.toUInt32, UInt32.add L ks.toUInt32, ebx,
      UInt32.add L 4, ebp, esi, edi, 0x102280, efl f, icAdd ic0 c⟩)) :
    ∃ (N' : XMem) (eax ecx edx fl : UInt32),
      Run img s0 (St.m ⟨N'.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, r, efl fl, icAdd ic0 (c + 229)⟩) ∧
      CSt G N' L n W sl (upd bf kd (memWords N'.get (UInt32.add L kd.toUInt32) 10)) ∧
      memWords N'.get (UInt32.add L kd.toUInt32) 10 = vs := by
  have hks' := mem_of_lookup hks
  have bd := lay_buf C.lay hkd
  have bs := lay_buf C.lay hks'
  have bds := lay_bb C.lay hkd hks'
  have ed := C.addr (k := kd) (by omega)
  have es := C.addr (k := ks) (by omega)
  have e4 : (UInt32.add L 4).toNat = L.toNat + 4 := C.addr (k := 4) (by omega)
  have hsz : (stF N L n 4 r C.fb h4).get.size = N.get.size := stF_size
  have P1 : Pres N (stF N L n 4 r C.fb h4) (OutF L 8) := (Pres.refl N _).wrF (by decide)
  have hi := C.hi; have hw := C.w_lo; have himg := C.imgok; have htop := C.top
  have F1 : Facts1W 24 (stF N L n 4 r C.fb h4).get.size (UInt32.add L 4).toNat (UInt32.add L kd.toUInt32).toNat
      (UInt32.add L ks.toUInt32).toNat := by
    rw [hsz, e4, ed, es]
    exact ⟨htop, C.fit, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  have hret : rdRaw (stF N L n 4 r C.fb h4).get (UInt32.add L 4) 4 = r :=
    ((Frame.nil N L n).wrF 4 (j := 4) (v := r) (h := C.fb) (hj := h4) rfl rfl).rd
      (rfl : List.lookup 4 _ = some r) 4 rfl
  have hfv : memWords (stF N L n 4 r C.fb h4).get (UInt32.add L ks.toUInt32) 10 = vs := by
    rw [memWords_pres P1 htop (by rw [es]; omega) (fun j hj => by rw [es]; unfold OutF; omega)]
    exact C.buf ks vs hks
  obtain ⟨N', eax, ecx, edx, fl, Rc, Pc, Va⟩ := fe_copy_call (stF N L n 4 r C.fb h4) (UInt32.add L 4)
    (UInt32.add L kd.toUInt32) (UInt32.add L ks.toUInt32) r F1 (by rw [ed, es]; omega) hret a ebx ebp esi edi f (icAdd ic0 c)
    (by rw [icAdd_toNat _ _ (by omega)]; omega)
  rw [icAdd_add, uadd_four] at Rc
  refine ⟨N', eax, ecx, edx, fl, R.trans Rc, C.next kd hkd ((P1.trans Pc).mono fun x hx => ⟨?_, ?_⟩), (Va.trans hfv)⟩
  · unfold OutF; have := hx.1; omega
  · have e464 : (UInt32.add L 4 - 24).toNat = L.toNat + 4 - 24 := by
      rw [UInt32.toNat_sub, e4]; unfold ramTop at htop; simp only [UInt32.reduceToNat]; omega
    unfold OutH OutF; rw [e464, ed]; omega

/-- A call of `fe_invert(L + kd, L + ks)` from the frame. -/
theorem CSt.inv {G N : XMem} {L : UInt32} {n W : Nat} {sl : List (Nat × UInt32)} {bf : List (Nat × Array UInt32)}
    (C : CSt G N L n W sl bf) (hW : 1012 ≤ W) (hn : 8 ≤ n) (kd ks : Nat) (hkd : kd ∈ bf.map Prod.fst)
    {vs : Array UInt32} (hks : bf.lookup ks = some vs) (hin : MulIn vs)
    (r a ebx ebp esi edi f : UInt32) (ic0 : UInt64) (c : Nat) (hic : ic0.toNat + c + 156631 < 2 ^ 62) (s0 : Machine)
    (h4 : (4 : UInt32).toNat + 4 ≤ n)
    (R : Run img s0 (St.m ⟨(stF N L n 4 r C.fb h4).get, a, UInt32.add L kd.toUInt32, UInt32.add L ks.toUInt32, ebx,
      UInt32.add L 4, ebp, esi, edi, 0x1005d0, efl f, icAdd ic0 c⟩)) :
    ∃ (N' : XMem) (eax ecx edx fl : UInt32),
      Run img s0 (St.m ⟨N'.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, r, efl fl, icAdd ic0 (c + 156631)⟩) ∧
      CSt G N' L n W sl (upd bf kd (memWords N'.get (UInt32.add L kd.toUInt32) 10)) ∧
      MulOut (memWords N'.get (UInt32.add L kd.toUInt32) 10) ∧
      feValI (memWords N'.get (UInt32.add L kd.toUInt32) 10) % pI = feValI vs ^ (2 ^ 255 - 21) % pI := by
  have hks' := mem_of_lookup hks
  have bd := lay_buf C.lay hkd
  have bs := lay_buf C.lay hks'
  have bds := lay_bb C.lay hkd hks'
  have ed := C.addr (k := kd) (by omega)
  have es := C.addr (k := ks) (by omega)
  have e4 : (UInt32.add L 4).toNat = L.toNat + 4 := C.addr (k := 4) (by omega)
  have hsz : (stF N L n 4 r C.fb h4).get.size = N.get.size := stF_size
  have P1 : Pres N (stF N L n 4 r C.fb h4) (OutF L 8) := (Pres.refl N _).wrF (by decide)
  have hi := C.hi; have hw := C.w_lo; have himg := C.imgok; have htop := C.top
  have F1 : Facts1W 1016 (stF N L n 4 r C.fb h4).get.size (UInt32.add L 4).toNat (UInt32.add L kd.toUInt32).toNat
      (UInt32.add L ks.toUInt32).toNat := by
    rw [hsz, e4, ed, es]
    exact ⟨htop, C.fit, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  have hret : rdRaw (stF N L n 4 r C.fb h4).get (UInt32.add L 4) 4 = r :=
    ((Frame.nil N L n).wrF 4 (j := 4) (v := r) (h := C.fb) (hj := h4) rfl rfl).rd
      (rfl : List.lookup 4 _ = some r) 4 rfl
  have hfv : memWords (stF N L n 4 r C.fb h4).get (UInt32.add L ks.toUInt32) 10 = vs := by
    rw [memWords_pres P1 htop (by rw [es]; omega) (fun j hj => by rw [es]; unfold OutF; omega)]
    exact C.buf ks vs hks
  obtain ⟨N', eax, ecx, edx, fl, Rc, Pc, Mo, Va⟩ := fe_invert_call (stF N L n 4 r C.fb h4) (UInt32.add L 4)
    (UInt32.add L kd.toUInt32) (UInt32.add L ks.toUInt32) r vs F1 hret hfv hin a ebx ebp esi edi f (icAdd ic0 c)
    (by rw [icAdd_toNat _ _ (by omega)]; omega)
  rw [icAdd_add, uadd_four] at Rc
  refine ⟨N', eax, ecx, edx, fl, R.trans Rc, C.next kd hkd ((P1.trans Pc).mono fun x hx => ⟨?_, ?_⟩), Mo, Va⟩
  · unfold OutF; have := hx.1; omega
  · have e464 : (UInt32.add L 4 - 1016).toNat = L.toNat + 4 - 1016 := by
      rw [UInt32.toNat_sub, e4]; unfold ramTop at htop; simp only [UInt32.reduceToNat]; omega
    unfold OutH OutF; rw [e464, ed]; omega

end Solutions.OpensslX25519.I
