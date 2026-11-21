import Solutions.OpensslX25519.I.CSt3
import Solutions.OpensslX25519.I.FbCall
import Solutions.OpensslX25519.I.TbCall
/-!
# Call steps of the frame state for `fe_frombytes` and `fe_tobytes`

The proof of `CSt.copy` (`I/CSt3`) with `fe_frombytes_call` (frame `[L - 64, L + 8)`, the input `s` apart from the
frame) and `fe_tobytes_call` (frame `[L - 36, L + 8)`, the output `out` apart from the frame; the last step, so it
gives the facts about the memory instead of a `CSt`). Prover R.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

theorem uadd_shift {L Lf : UInt32} {d : Nat} (hf : Lf.toNat + d = L.toNat) (a b : UInt32)
    (hab : a.toNat = b.toNat + d) : UInt32.add Lf a = UInt32.add L b := by
  apply UInt32.toNat_inj.1; rw [toNat_uadd, toNat_uadd]; omega

theorem below_L {L : UInt32} {d : Nat} (hd : d ≤ L.toNat) : ∃ Lf : UInt32, Lf.toNat + d = L.toNat :=
  ⟨(L.toNat - d).toUInt32, by rw [Nat.toUInt32, UInt32.toNat_ofNat']; have := L.toNat_lt; omega⟩

theorem memBytes_pres {A B : XMem} {P : Nat → Prop} (hP : Pres A B P) (s : UInt32) (n : Nat)
    (h : ∀ i, i < n → (s + i.toUInt32).toNat < A.get.size ∧ P (s + i.toUInt32).toNat) :
    memBytes B.get s n = memBytes A.get s n := by
  unfold memBytes
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact hP.2 _ (h i hi).1 (h i hi).2

theorem uadd_nat_toNat (s : UInt32) (i : Nat) (h : s.toNat + i < 2 ^ 32) : (s + i.toUInt32).toNat = s.toNat + i := by
  rw [UInt32.toNat_add, Nat.toUInt32, UInt32.toNat_ofNat']; omega

/-- A call of `fe_frombytes(L + kd, s)` from the frame. -/
theorem CSt.fromb {G N : XMem} {L : UInt32} {n W : Nat} {sl : List (Nat × UInt32)} {bf : List (Nat × Array UInt32)}
    (C : CSt G N L n W sl bf) (hW : 64 ≤ W) (hn : 8 ≤ n) (kd : Nat) (hkd : kd ∈ bf.map Prod.fst)
    (s : UInt32) (u : List UInt8) (hsm : s.toNat + 32 ≤ N.get.size)
    (hsi : s.toNat + 32 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ s.toNat)
    (hsL : s.toNat + 32 ≤ L.toNat - W ∨ L.toNat + n ≤ s.toNat) (hu : memBytes N.get s 32 = u)
    (r a ebx ebp esi edi f : UInt32) (ic0 : UInt64) (c : Nat) (hic : ic0.toNat + c + 210 < 2 ^ 62) (s0 : Machine)
    (h4 : (4 : UInt32).toNat + 4 ≤ n)
    (R : Run img s0 (St.m ⟨(stF N L n 4 r C.fb h4).get, a, UInt32.add L kd.toUInt32, s, ebx,
      UInt32.add L 4, ebp, esi, edi, 0x1036f0, efl f, icAdd ic0 c⟩)) :
    ∃ (N' : XMem) (eax ecx edx fl : UInt32),
      Run img s0 (St.m ⟨N'.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, r, efl fl, icAdd ic0 (c + 210)⟩) ∧
      CSt G N' L n W sl (upd bf kd (memWords N'.get (UInt32.add L kd.toUInt32) 10)) ∧
      MulOut (memWords N'.get (UInt32.add L kd.toUInt32) 10) ∧
      feValI (memWords N'.get (UInt32.add L kd.toUInt32) 10) % pI = (Ssl.Spec.X25519.decodeU u : Int) % pI := by
  have bd := lay_buf C.lay hkd
  have ed := C.addr (k := kd) (by omega)
  have hsz : (stF N L n 4 r C.fb h4).get.size = N.get.size := stF_size
  have P1 : Pres N (stF N L n 4 r C.fb h4) (OutF L 8) := (Pres.refl N _).wrF (by decide)
  have hi := C.hi; have hw := C.w_lo; have himg := C.imgok; have htop := C.top
  obtain ⟨Lf, hLf⟩ := below_L (L := L) (d := 64) (by omega)
  have e68 : UInt32.add Lf 68 = UInt32.add L 4 := uadd_shift hLf 68 4 (by decide)
  have e72 : UInt32.add Lf 72 = UInt32.add L 8 := uadd_shift hLf 72 8 (by decide)
  have hS : FB (stF N L n 4 r C.fb h4).get.size Lf 72 := ⟨by rw [hsz]; exact htop, by rw [hsz]; omega, by omega⟩
  have hret : rdRaw (stF N L n 4 r C.fb h4).get (UInt32.add Lf 68) 4 = r := by
    rw [e68]
    exact ((Frame.nil N L n).wrF 4 (j := 4) (v := r) (h := C.fb) (hj := h4) rfl rfl).rd
      (rfl : List.lookup 4 _ = some r) 4 rfl
  have hu' : memBytes (stF N L n 4 r C.fb h4).get s 32 = u := by
    rw [memBytes_pres P1 s 32 (fun i hi => by
      rw [uadd_nat_toNat s i (by unfold ramTop at htop; omega)]; unfold OutF; omega)]
    exact hu
  obtain ⟨N', eax, ecx, edx, fl, Rc, Pc, Mo, Va⟩ := fe_frombytes_call (stF N L n 4 r C.fb h4) Lf
    (UInt32.add L kd.toUInt32) s r u hS hret (by rw [hsz, ed]; omega) (by rw [ed]; omega) (by rw [ed]; omega)
    (by rw [hsz]; exact hsm) hsi (by omega) hu' a ebx ebp esi edi f (icAdd ic0 c)
    (by rw [icAdd_toNat _ _ (by omega)]; omega)
  rw [show icAdd (icAdd ic0 c) 0 = icAdd ic0 c from rfl, icAdd_add, e68, e72] at Rc
  refine ⟨N', eax, ecx, edx, fl, R.trans Rc, C.next kd hkd ((P1.trans Pc).mono fun x hx => ⟨?_, ?_⟩), Mo, Va⟩
  · unfold OutF; have := hx.1; omega
  · unfold OutH OutF; rw [ed]; have := hx.1; have := hx.2; omega

/-- A call of `fe_tobytes(out, L + ks)` from the frame, `out` apart from `[L - W, L + n)`. -/
theorem CSt.tob {G N : XMem} {L : UInt32} {n W : Nat} {sl : List (Nat × UInt32)} {bf : List (Nat × Array UInt32)}
    (C : CSt G N L n W sl bf) (hW : 36 ≤ W) (hn : 8 ≤ n) (ks : Nat) {vs : Array UInt32}
    (hks : bf.lookup ks = some vs) (hin : MulOut vs) (out : UInt32) (hom : out.toNat + 32 ≤ N.get.size)
    (hoi : out.toNat + 32 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ out.toNat)
    (hoL : out.toNat + 32 ≤ L.toNat - W ∨ L.toNat + n ≤ out.toNat)
    (r a ebx ebp esi edi f : UInt32) (ic0 : UInt64) (c : Nat) (hic : ic0.toNat + c + 163 < 2 ^ 62) (s0 : Machine)
    (h4 : (4 : UInt32).toNat + 4 ≤ n)
    (R : Run img s0 (St.m ⟨(stF N L n 4 r C.fb h4).get, a, out, UInt32.add L ks.toUInt32, ebx,
      UInt32.add L 4, ebp, esi, edi, 0x101c30, efl f, icAdd ic0 c⟩)) :
    ∃ (N' : XMem) (eax ecx edx fl : UInt32),
      Run img s0 (St.m ⟨N'.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, r, efl fl, icAdd ic0 (c + 163)⟩) ∧
      Pres N N' (fun x => (x < L.toNat - 36 ∨ L.toNat + 8 ≤ x) ∧ (x < out.toNat ∨ out.toNat + 32 ≤ x)) ∧
      memBytes N'.get out 32 = Ssl.Spec.X25519.leBytes 32 (feValI vs % pI).toNat := by
  have hks' := mem_of_lookup hks
  have bs := lay_buf C.lay hks'
  have es := C.addr (k := ks) (by omega)
  have hsz : (stF N L n 4 r C.fb h4).get.size = N.get.size := stF_size
  have P1 : Pres N (stF N L n 4 r C.fb h4) (OutF L 8) := (Pres.refl N _).wrF (by decide)
  have hi := C.hi; have hw := C.w_lo; have himg := C.imgok; have htop := C.top
  obtain ⟨Lt, hLt⟩ := below_L (L := L) (d := 36) (by omega)
  have e40 : UInt32.add Lt 40 = UInt32.add L 4 := uadd_shift hLt 40 4 (by decide)
  have e44 : UInt32.add Lt 44 = UInt32.add L 8 := uadd_shift hLt 44 8 (by decide)
  have hS : FB (stF N L n 4 r C.fb h4).get.size Lt 44 := ⟨by rw [hsz]; exact htop, by rw [hsz]; omega, by omega⟩
  have hret : rdRaw (stF N L n 4 r C.fb h4).get (UInt32.add Lt 40) 4 = r := by
    rw [e40]
    exact ((Frame.nil N L n).wrF 4 (j := 4) (v := r) (h := C.fb) (hj := h4) rfl rfl).rd
      (rfl : List.lookup 4 _ = some r) 4 rfl
  have hfv : memWords (stF N L n 4 r C.fb h4).get (UInt32.add L ks.toUInt32) 10 = vs := by
    rw [memWords_pres P1 htop (by rw [es]; omega) (fun j hj => by rw [es]; unfold OutF; omega)]
    exact C.buf ks vs hks
  obtain ⟨N', eax, ecx, edx, fl, Rc, Pc, Vo⟩ := fe_tobytes_call (stF N L n 4 r C.fb h4) Lt out
    (UInt32.add L ks.toUInt32) r vs hS hret (by rw [hsz]; exact hom) hoi (by omega) (by rw [hsz, es]; omega)
    (by rw [es]; omega) (by rw [es]; omega) hfv hin a ebx ebp esi edi f (icAdd ic0 c)
    (by rw [icAdd_toNat _ _ (by omega)]; omega)
  rw [show icAdd (icAdd ic0 c) 0 = icAdd ic0 c from rfl, icAdd_add, e40, e44] at Rc
  refine ⟨N', eax, ecx, edx, fl, R.trans Rc, (P1.trans Pc).mono fun x hx => ⟨?_, ?_⟩, Vo⟩
  · unfold OutF; have := hx.1; omega
  · unfold OutF OutO; have := hx.1; have := hx.2; omega

end Solutions.OpensslX25519.I
