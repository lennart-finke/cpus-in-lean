import Solutions.OpensslX25519.I.SqCall
import Solutions.OpensslX25519.I.MulCall
import Solutions.OpensslX25519.I.Caller
/-!
# The frame of a caller of the field functions

`CSt G N L n W slots bufs`: the caller's frame is `[L, L + n)` (`L` its lowest stack pointer, below
the pushed arguments and the return address of its calls), the callees use the `W` bytes below `L`;
the memory `N` agrees with the entry memory `G` outside `[L - W, L + n)`, holds the words `slots`
(offset from `L`, value) and the limb vectors `bufs` (offset from `L`, words). `LayoutOK` (checked by
`decide`) puts the slots and buffers inside the frame above `L + 8` and apart from each other.

`CSt.sq` and `CSt.mul`: after the piece of the caller that loads the arguments and executes the
`call` (so that the memory is `N` with the return address, and for `fe_mul` the third argument,
stored below `L + 8`), the callee's contract continues the run to the return, and the state
after it is again a `CSt`, with the output buffer updated.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

/-! ## Lists of (offset, value) -/

def upd {α : Type} : List (Nat × α) → Nat → α → List (Nat × α)
  | [], _, _ => []
  | (k, w) :: l, j, v => if k = j then (k, v) :: l else (k, w) :: upd l j v

theorem keys_upd {α : Type} (l : List (Nat × α)) (j : Nat) (v : α) :
    (upd l j v).map Prod.fst = l.map Prod.fst := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k, w⟩ := p
    simp only [upd]
    split <;> simp [ih]

theorem lookup_upd_self {α : Type} (l : List (Nat × α)) (j : Nat) (v : α) (h : j ∈ l.map Prod.fst) :
    (upd l j v).lookup j = some v := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨k, w⟩ := p
    simp only [upd]
    by_cases hk : k = j
    · subst hk; simp
    · rw [if_neg hk]
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h.symm hk
      · simp only [List.lookup]
        have : (j == k) = false := by simp; omega
        rw [this]; exact ih h

theorem lookup_upd_ne {α : Type} (l : List (Nat × α)) (j k : Nat) (v : α) (h : k ≠ j) :
    (upd l j v).lookup k = l.lookup k := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k', w⟩ := p
    simp only [upd]
    by_cases hk : k' = j
    · subst hk
      simp only [ite_true, List.lookup]
      have : (k == k') = false := by simp; omega
      rw [this]
    · rw [if_neg hk]
      simp only [List.lookup]
      split <;> simp_all

theorem mem_of_lookup {α : Type} {l : List (Nat × α)} {k : Nat} {v : α} (h : l.lookup k = some v) :
    k ∈ l.map Prod.fst := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨k', w⟩ := p
    simp only [List.lookup] at h
    split at h
    · rename_i hk; simp at hk; simp [hk]
    · simp [ih h]

/-! ## The layout -/

def LayoutOK (n : Nat) (sk bk : List Nat) : Bool :=
  sk.all (fun k => decide (8 ≤ k) && decide (k + 4 ≤ n) && bk.all (fun b => decide (k + 4 ≤ b) || decide (b + 40 ≤ k))) &&
  bk.all (fun b => decide (8 ≤ b) && decide (b + 40 ≤ n) &&
    bk.all (fun c => decide (b = c) || decide (b + 40 ≤ c) || decide (c + 40 ≤ b)))

theorem lay_buf {n : Nat} {sk bk : List Nat} (h : LayoutOK n sk bk = true) {b : Nat} (hb : b ∈ bk) :
    8 ≤ b ∧ b + 40 ≤ n := by
  simp only [LayoutOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨(h.2 b hb).1.1, (h.2 b hb).1.2⟩

theorem lay_bb {n : Nat} {sk bk : List Nat} (h : LayoutOK n sk bk = true) {b c : Nat} (hb : b ∈ bk) (hc : c ∈ bk) :
    b = c ∨ b + 40 ≤ c ∨ c + 40 ≤ b := by
  simp only [LayoutOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
  have := (h.2 b hb).2 c hc
  rcases this with (h1 | h1) | h1 <;> simp_all

theorem lay_slot {n : Nat} {sk bk : List Nat} (h : LayoutOK n sk bk = true) {k : Nat} (hk : k ∈ sk) :
    8 ≤ k ∧ k + 4 ≤ n ∧ ∀ b, b ∈ bk → k + 4 ≤ b ∨ b + 40 ≤ k := by
  simp only [LayoutOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
  refine ⟨(h.1 k hk).1.1, (h.1 k hk).1.2, fun b hb => ?_⟩
  have := (h.1 k hk).2 b hb
  simp_all

/-! ## The state -/

structure CSt (G N : XMem) (L : UInt32) (n W : Nat) (slots : List (Nat × UInt32))
    (bufs : List (Nat × Array UInt32)) : Prop where
  top : N.get.size ≤ ramTop
  fit : 0x100000 + 47024 ≤ N.get.size
  w_lo : W ≤ L.toNat
  hi : L.toNat + n ≤ N.get.size
  imgok : L.toNat + n ≤ 0x100000 ∨ 0x100000 + 47024 ≤ L.toNat - W
  pres : Pres G N (fun x => x < L.toNat - W ∨ L.toNat + n ≤ x)
  slot : ∀ k v, slots.lookup k = some v → rdRaw N.get (UInt32.add L k.toUInt32) 4 = v
  buf : ∀ k v, bufs.lookup k = some v → memWords N.get (UInt32.add L k.toUInt32) 10 = v
  lay : LayoutOK n (slots.map Prod.fst) (bufs.map Prod.fst) = true

theorem CSt.addr {G N : XMem} {L : UInt32} {n W : Nat} {sl : List (Nat × UInt32)} {bf : List (Nat × Array UInt32)}
    (C : CSt G N L n W sl bf) {k : Nat} (hk : k ≤ n) : (UInt32.add L k.toUInt32).toNat = L.toNat + k := by
  have := C.hi; have := C.top; unfold ramTop at *
  have e : (k.toUInt32).toNat = k := by rw [Nat.toUInt32, UInt32.toNat_ofNat']; omega
  rw [toNat_uadd, e]; omega

theorem CSt.fb {G N : XMem} {L : UInt32} {n W : Nat} {sl : List (Nat × UInt32)} {bf : List (Nat × Array UInt32)}
    (C : CSt G N L n W sl bf) : FB N.get.size L n :=
  ⟨C.top, C.hi, by have := C.imgok; omega⟩

/-- A memory that agrees with `N` on `[L - W, L + n)` except below `L + 8` and in the buffer at
`kd`: a `CSt` with that buffer updated. -/
theorem CSt.next {G N N' : XMem} {L : UInt32} {n W : Nat} {sl : List (Nat × UInt32)} {bf : List (Nat × Array UInt32)}
    (C : CSt G N L n W sl bf) (kd : Nat) (hkd : kd ∈ bf.map Prod.fst)
    (hP : Pres N N' (fun x => (x < L.toNat - W ∨ L.toNat + 8 ≤ x) ∧ (x < L.toNat + kd ∨ L.toNat + kd + 40 ≤ x))) :
    CSt G N' L n W sl (upd bf kd (memWords N'.get (UInt32.add L kd.toUInt32) 10)) := by
  have hsz : N'.get.size = N.get.size := hP.1
  have hkb := lay_buf C.lay hkd
  refine ⟨by rw [hsz]; exact C.top, by rw [hsz]; exact C.fit, C.w_lo, by rw [hsz]; exact C.hi, C.imgok,
    (C.pres.trans hP).mono fun x hx => ⟨hx, ?_, ?_⟩, fun k v hl => ?_, fun k v hl => ?_, ?_⟩
  · omega
  · omega
  · have hk := lay_slot C.lay (mem_of_lookup hl)
    have e := C.addr (k := k) (by omega)
    rw [← C.slot k v hl]
    exact hP.rd C.top (by rw [e]; have := C.hi; omega) (fun j hj => by
      rw [e]; have := hk.2.2 kd hkd; omega)
  · by_cases hk : k = kd
    · subst hk
      rw [lookup_upd_self _ _ _ hkd] at hl
      cases hl; rfl
    · rw [lookup_upd_ne _ _ _ _ hk] at hl
      have hkm := mem_of_lookup hl
      have hb := lay_buf C.lay hkm
      have hbb := lay_bb C.lay hkm hkd
      have e := C.addr (k := k) (by omega)
      rw [← C.buf k v hl]
      exact memWords_pres hP C.top (by rw [e]; have := C.hi; omega) (fun j hj => by rw [e]; omega)
  · rw [keys_upd]; exact C.lay

theorem toNat_sub_lit {x : UInt32} {k : Nat} (hk : k ≤ x.toNat) (hk' : k < 2 ^ 32) :
    (x - (OfNat.ofNat k : UInt32)).toNat = x.toNat - k := by
  have e : (OfNat.ofNat k : UInt32).toNat = k := by
    show (UInt32.ofNat k).toNat = k
    rw [UInt32.toNat_ofNat']; omega
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, e]; exact hk), e]

theorem uadd_four (L : UInt32) : UInt32.add L 4 + 4 = UInt32.add L 8 := by
  show L + 4 + 4 = L + 8
  rw [UInt32.add_assoc]; rfl

/-- A call of `fe_sq(L + kd, L + ks)` from the frame. -/
theorem CSt.sq {G N : XMem} {L : UInt32} {n W : Nat} {sl : List (Nat × UInt32)} {bf : List (Nat × Array UInt32)}
    (C : CSt G N L n W sl bf) (hW : 460 ≤ W) (hn : 8 ≤ n) (kd ks : Nat) (hkd : kd ∈ bf.map Prod.fst)
    {vs : Array UInt32} (hks : bf.lookup ks = some vs) (hin : MulIn vs)
    (r a ebx ebp esi edi f : UInt32) (ic0 : UInt64) (c : Nat) (hic : ic0.toNat + c + 574 < 2 ^ 63) (s0 : Machine)
    (h4 : (4 : UInt32).toNat + 4 ≤ n)
    (R : Run img s0 (St.m ⟨(stF N L n 4 r C.fb h4).get, a, UInt32.add L kd.toUInt32, UInt32.add L ks.toUInt32, ebx,
      UInt32.add L 4, ebp, esi, edi, 0x102360, efl f, icAdd ic0 c⟩)) :
    ∃ (N' : XMem) (eax ecx edx fl : UInt32),
      Run img s0 (St.m ⟨N'.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, r, efl fl, icAdd ic0 (c + 574)⟩) ∧
      CSt G N' L n W sl (upd bf kd (memWords N'.get (UInt32.add L kd.toUInt32) 10)) ∧
      MulOut (memWords N'.get (UInt32.add L kd.toUInt32) 10) ∧
      feValI (memWords N'.get (UInt32.add L kd.toUInt32) 10) % pI = feValI vs * feValI vs % pI := by
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
  have F1 : Facts1W 464 (stF N L n 4 r C.fb h4).get.size (UInt32.add L 4).toNat (UInt32.add L kd.toUInt32).toNat
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
  obtain ⟨N', eax, ecx, edx, fl, Rc, Pc, Mo, Va⟩ := fe_sq_call (stF N L n 4 r C.fb h4) (UInt32.add L 4)
    (UInt32.add L kd.toUInt32) (UInt32.add L ks.toUInt32) r vs F1 hret hfv hin a ebx ebp esi edi f (icAdd ic0 c)
    (by rw [icAdd_toNat _ _ (by omega)]; omega)
  rw [icAdd_add, uadd_four] at Rc
  refine ⟨N', eax, ecx, edx, fl, R.trans Rc, C.next kd hkd ((P1.trans Pc).mono fun x hx => ⟨?_, ?_⟩), Mo, Va⟩
  · unfold OutF; have := hx.1; omega
  · have e464 : (UInt32.add L 4 - 464).toNat = L.toNat + 4 - 464 := by
      rw [UInt32.toNat_sub, e4]; unfold ramTop at htop; simp only [UInt32.reduceToNat]; omega
    unfold OutH OutF; rw [e464, ed]; omega

/-- A call of `fe_mul(L + kd, L + kf, L + kg)` from the frame. -/
theorem CSt.mul {G N : XMem} {L : UInt32} {n W : Nat} {sl : List (Nat × UInt32)} {bf : List (Nat × Array UInt32)}
    (C : CSt G N L n W sl bf) (hW : 828 ≤ W) (hn : 8 ≤ n) (kd kf kg : Nat) (hkd : kd ∈ bf.map Prod.fst)
    {vf vg : Array UInt32} (hkf : bf.lookup kf = some vf) (hkg : bf.lookup kg = some vg) (hfi : MulIn vf)
    (hgi : MulIn vg) (r a ebx ebp esi edi f : UInt32) (ic0 : UInt64) (c : Nat) (hic : ic0.toNat + c + 891 < 2 ^ 63)
    (s0 : Machine) (h4 : (4 : UInt32).toNat + 4 ≤ n) (h0 : 4 ≤ n)
    (R : Run img s0 (St.m ⟨(stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get, a,
      UInt32.add L kd.toUInt32, UInt32.add L kf.toUInt32, ebx, L, ebp, esi, edi, 0x100c20, efl f, icAdd ic0 c⟩)) :
    ∃ (N' : XMem) (eax ecx edx fl : UInt32),
      Run img s0 (St.m ⟨N'.get, eax, ecx, edx, ebx, UInt32.add L 4, ebp, esi, edi, r, efl fl, icAdd ic0 (c + 891)⟩) ∧
      CSt G N' L n W sl (upd bf kd (memWords N'.get (UInt32.add L kd.toUInt32) 10)) ∧
      MulOut (memWords N'.get (UInt32.add L kd.toUInt32) 10) ∧
      feValI (memWords N'.get (UInt32.add L kd.toUInt32) 10) % pI = feValI vf * feValI vg % pI := by
  have hkf' := mem_of_lookup hkf
  have hkg' := mem_of_lookup hkg
  have bd := lay_buf C.lay hkd
  have bf' := lay_buf C.lay hkf'
  have bg := lay_buf C.lay hkg'
  have bdf := lay_bb C.lay hkd hkf'
  have bdg := lay_bb C.lay hkd hkg'
  have ed := C.addr (k := kd) (by omega)
  have ef := C.addr (k := kf) (by omega)
  have eg := C.addr (k := kg) (by omega)
  have M1 := stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0
  have hsz : (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get.size = N.get.size := by
    rw [stF0_size, stF_size]
  have P1 : Pres N (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0) (OutF L 8) :=
    ((Pres.refl N _).wrF (by decide)).wrF0 (by decide)
  have hi := C.hi; have hw := C.w_lo; have himg := C.imgok; have htop := C.top
  have F1 : FieldFactsW 828 (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get.size L.toNat
      (UInt32.add L kd.toUInt32).toNat (UInt32.add L kf.toUInt32).toNat (UInt32.add L kg.toUInt32).toNat := by
    rw [hsz, ed, ef, eg]
    exact ⟨htop, C.fit, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega⟩
  have FF := ((Frame.nil N L n).wrF 4 (j := 4) (v := UInt32.add L kg.toUInt32) (h := C.fb) (hj := h4) rfl rfl).wrF0
    (v := r) (h := stF_FB) (hn := h0)
  have hret : rdRaw (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get L 4 = r :=
    FF.rd0 (rfl : List.lookup 0 _ = some r)
  have hg0 : rdRaw (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get (L + 4) 4 =
      UInt32.add L kg.toUInt32 := FF.rd (rfl : List.lookup 4 _ = some _) 4 rfl
  have hfv : memWords (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get
      (UInt32.add L kf.toUInt32) 10 = vf := by
    rw [memWords_pres P1 htop (by rw [ef]; omega) (fun j hj => by rw [ef]; unfold OutF; omega)]
    exact C.buf kf vf hkf
  have hgv : memWords (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get
      (UInt32.add L kg.toUInt32) 10 = vg := by
    rw [memWords_pres P1 htop (by rw [eg]; omega) (fun j hj => by rw [eg]; unfold OutF; omega)]
    exact C.buf kg vg hkg
  obtain ⟨N', eax, ecx, edx, fl, Rc, Pc, Mo, Va⟩ := fe_mul_call _ L (UInt32.add L kd.toUInt32)
    (UInt32.add L kf.toUInt32) (UInt32.add L kg.toUInt32) r vf vg F1 hret hg0 hfv hgv hfi hgi a ebx ebp esi edi f
    (icAdd ic0 c) (by rw [icAdd_toNat _ _ (by omega)]; omega)
  rw [icAdd_add] at Rc
  refine ⟨N', eax, ecx, edx, fl, R.trans Rc, C.next kd hkd ((P1.trans Pc).mono fun x hx => ⟨?_, ?_⟩), Mo, Va⟩
  · unfold OutF; have := hx.1; omega
  · have e828 : (L - 828).toNat = L.toNat - 828 := by
      rw [UInt32.toNat_sub]; unfold ramTop at htop; simp only [UInt32.reduceToNat]; omega
    unfold OutH OutF; rw [e828, ed]; omega

/-- The buffers as a list of four (keeps the terms of a long chain of calls small). -/
theorem CSt.set4 {G N : XMem} {L : UInt32} {n W : Nat} {sl : List (Nat × UInt32)} {bf : List (Nat × Array UInt32)}
    (C : CSt G N L n W sl bf) (k1 k2 k3 k4 : Nat) (v1 v2 v3 v4 : Array UInt32)
    (hk : bf.map Prod.fst = [k1, k2, k3, k4]) (h1 : bf.lookup k1 = some v1) (h2 : bf.lookup k2 = some v2)
    (h3 : bf.lookup k3 = some v3) (h4 : bf.lookup k4 = some v4) :
    CSt G N L n W sl [(k1, v1), (k2, v2), (k3, v3), (k4, v4)] := by
  refine ⟨C.top, C.fit, C.w_lo, C.hi, C.imgok, C.pres, C.slot, fun k v hl => C.buf k v ?_, ?_⟩
  · simp only [List.lookup] at hl
    split at hl
    · rename_i h; simp at h hl; subst h hl; exact h1
    split at hl
    · rename_i h; simp at h hl; subst h hl; exact h2
    split at hl
    · rename_i h; simp at h hl; subst h hl; exact h3
    split at hl
    · rename_i h; simp at h hl; subst h hl; exact h4
    simp at hl
  · have : ([(k1, v1), (k2, v2), (k3, v3), (k4, v4)] : List (Nat × Array UInt32)).map Prod.fst = [k1, k2, k3, k4] := rfl
    rw [this, ← hk]; exact C.lay

theorem icAdd_lt {ic0 : UInt64} (h : ic0.toNat < 2 ^ 62) {c : Nat} (hc : c ≤ 2 ^ 61) : (icAdd ic0 c).toNat < 2 ^ 63 := by
  rw [icAdd_toNat _ _ (by omega)]; omega

theorem ic_lt {ic0 : UInt64} (h : ic0.toNat < 2 ^ 62) {c d : Nat} (hc : c + d ≤ 2 ^ 61) : ic0.toNat + c + d < 2 ^ 63 := by
  omega

/-- The words outside the region are those of the entry memory. -/
theorem CSt.memWords_out {G N : XMem} {L : UInt32} {n W : Nat} {sl : List (Nat × UInt32)}
    {bf : List (Nat × Array UInt32)} (C : CSt G N L n W sl bf) {q : UInt32} (hq : q.toNat + 40 ≤ G.get.size)
    (hqs : q.toNat + 40 ≤ L.toNat - W ∨ L.toNat + n ≤ q.toNat) : memWords N.get q 10 = memWords G.get q 10 := by
  have h1 := C.pres
  have hsz : N.get.size = G.get.size := h1.1
  exact memWords_pres h1 (by rw [← hsz]; exact C.top) hq (fun j hj => by omega)

/-- A call of `fe_sq(L + kd, fp)` with `fp` outside the region. -/
theorem CSt.sq_x {G N : XMem} {L : UInt32} {n W : Nat} {sl : List (Nat × UInt32)} {bf : List (Nat × Array UInt32)}
    (C : CSt G N L n W sl bf) (hW : 460 ≤ W) (hn : 8 ≤ n) (kd : Nat) (hkd : kd ∈ bf.map Prod.fst)
    (fp : UInt32) {vs : Array UInt32} (hfm : fp.toNat + 40 ≤ G.get.size)
    (hfi : fp.toNat + 40 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ fp.toNat)
    (hfs : fp.toNat + 40 ≤ L.toNat - W ∨ L.toNat + n ≤ fp.toNat) (hfv0 : memWords G.get fp 10 = vs) (hin : MulIn vs)
    (r a ebx ebp esi edi f : UInt32) (ic0 : UInt64) (c : Nat) (hic : ic0.toNat + c + 574 < 2 ^ 63) (s0 : Machine)
    (h4 : (4 : UInt32).toNat + 4 ≤ n)
    (R : Run img s0 (St.m ⟨(stF N L n 4 r C.fb h4).get, a, UInt32.add L kd.toUInt32, fp, ebx,
      UInt32.add L 4, ebp, esi, edi, 0x102360, efl f, icAdd ic0 c⟩)) :
    ∃ (N' : XMem) (eax ecx edx fl : UInt32),
      Run img s0 (St.m ⟨N'.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, r, efl fl, icAdd ic0 (c + 574)⟩) ∧
      CSt G N' L n W sl (upd bf kd (memWords N'.get (UInt32.add L kd.toUInt32) 10)) ∧
      MulOut (memWords N'.get (UInt32.add L kd.toUInt32) 10) ∧
      feValI (memWords N'.get (UInt32.add L kd.toUInt32) 10) % pI = feValI vs * feValI vs % pI := by
  have bd := lay_buf C.lay hkd
  have ed := C.addr (k := kd) (by omega)
  have e4 : (UInt32.add L 4).toNat = L.toNat + 4 := C.addr (k := 4) (by omega)
  have hsz : (stF N L n 4 r C.fb h4).get.size = N.get.size := stF_size
  have hsG : N.get.size = G.get.size := C.pres.1
  have P1 : Pres N (stF N L n 4 r C.fb h4) (OutF L 8) := (Pres.refl N _).wrF (by decide)
  have hi := C.hi; have hw := C.w_lo; have himg := C.imgok; have htop := C.top
  have F1 : Facts1W 464 (stF N L n 4 r C.fb h4).get.size (UInt32.add L 4).toNat (UInt32.add L kd.toUInt32).toNat
      fp.toNat := by
    rw [hsz, e4, ed]
    exact ⟨htop, C.fit, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  have hret : rdRaw (stF N L n 4 r C.fb h4).get (UInt32.add L 4) 4 = r :=
    ((Frame.nil N L n).wrF 4 (j := 4) (v := r) (h := C.fb) (hj := h4) rfl rfl).rd
      (rfl : List.lookup 4 _ = some r) 4 rfl
  have hfv : memWords (stF N L n 4 r C.fb h4).get fp 10 = vs := by
    rw [memWords_pres P1 htop (by omega) (fun j hj => by unfold OutF; omega), C.memWords_out hfm hfs]
    exact hfv0
  obtain ⟨N', eax, ecx, edx, fl, Rc, Pc, Mo, Va⟩ := fe_sq_call (stF N L n 4 r C.fb h4) (UInt32.add L 4)
    (UInt32.add L kd.toUInt32) fp r vs F1 hret hfv hin a ebx ebp esi edi f (icAdd ic0 c)
    (by rw [icAdd_toNat _ _ (by omega)]; omega)
  rw [icAdd_add, uadd_four] at Rc
  refine ⟨N', eax, ecx, edx, fl, R.trans Rc, C.next kd hkd ((P1.trans Pc).mono fun x hx => ⟨?_, ?_⟩), Mo, Va⟩
  · unfold OutF; have := hx.1; omega
  · have e464 : (UInt32.add L 4 - 464).toNat = L.toNat + 4 - 464 := by
      rw [UInt32.toNat_sub, e4]; unfold ramTop at htop; simp only [UInt32.reduceToNat]; omega
    unfold OutH OutF; rw [e464, ed]; omega

/-- A call of `fe_mul(L + kd, fp, L + kg)` with `fp` outside the region. -/
theorem CSt.mul_xf {G N : XMem} {L : UInt32} {n W : Nat} {sl : List (Nat × UInt32)} {bf : List (Nat × Array UInt32)}
    (C : CSt G N L n W sl bf) (hW : 828 ≤ W) (hn : 8 ≤ n) (kd kg : Nat) (hkd : kd ∈ bf.map Prod.fst)
    (fp : UInt32) {vf vg : Array UInt32} (hfm : fp.toNat + 40 ≤ G.get.size)
    (hfi : fp.toNat + 40 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ fp.toNat)
    (hfs : fp.toNat + 40 ≤ L.toNat - W ∨ L.toNat + n ≤ fp.toNat) (hfv0 : memWords G.get fp 10 = vf)
    (hkg : bf.lookup kg = some vg) (hfi' : MulIn vf)
    (hgi : MulIn vg) (r a ebx ebp esi edi f : UInt32) (ic0 : UInt64) (c : Nat) (hic : ic0.toNat + c + 891 < 2 ^ 63)
    (s0 : Machine) (h4 : (4 : UInt32).toNat + 4 ≤ n) (h0 : 4 ≤ n)
    (R : Run img s0 (St.m ⟨(stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get, a,
      UInt32.add L kd.toUInt32, fp, ebx, L, ebp, esi, edi, 0x100c20, efl f, icAdd ic0 c⟩)) :
    ∃ (N' : XMem) (eax ecx edx fl : UInt32),
      Run img s0 (St.m ⟨N'.get, eax, ecx, edx, ebx, UInt32.add L 4, ebp, esi, edi, r, efl fl, icAdd ic0 (c + 891)⟩) ∧
      CSt G N' L n W sl (upd bf kd (memWords N'.get (UInt32.add L kd.toUInt32) 10)) ∧
      MulOut (memWords N'.get (UInt32.add L kd.toUInt32) 10) ∧
      feValI (memWords N'.get (UInt32.add L kd.toUInt32) 10) % pI = feValI vf * feValI vg % pI := by
  have hkg' := mem_of_lookup hkg
  have bd := lay_buf C.lay hkd
  have bg := lay_buf C.lay hkg'
  have bdg := lay_bb C.lay hkd hkg'
  have ed := C.addr (k := kd) (by omega)
  have eg := C.addr (k := kg) (by omega)
  have hsz : (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get.size = N.get.size := by
    rw [stF0_size, stF_size]
  have hsG : N.get.size = G.get.size := C.pres.1
  have P1 : Pres N (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0) (OutF L 8) :=
    ((Pres.refl N _).wrF (by decide)).wrF0 (by decide)
  have hi := C.hi; have hw := C.w_lo; have himg := C.imgok; have htop := C.top
  have F1 : FieldFactsW 828 (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get.size L.toNat
      (UInt32.add L kd.toUInt32).toNat fp.toNat (UInt32.add L kg.toUInt32).toNat := by
    rw [hsz, ed, eg]
    exact ⟨htop, C.fit, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega⟩
  have FF := ((Frame.nil N L n).wrF 4 (j := 4) (v := UInt32.add L kg.toUInt32) (h := C.fb) (hj := h4) rfl rfl).wrF0
    (v := r) (h := stF_FB) (hn := h0)
  have hret : rdRaw (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get L 4 = r :=
    FF.rd0 (rfl : List.lookup 0 _ = some r)
  have hg0 : rdRaw (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get (L + 4) 4 =
      UInt32.add L kg.toUInt32 := FF.rd (rfl : List.lookup 4 _ = some _) 4 rfl
  have hfv : memWords (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get fp 10 = vf := by
    rw [memWords_pres P1 htop (by omega) (fun j hj => by unfold OutF; omega), C.memWords_out hfm hfs]
    exact hfv0
  have hgv : memWords (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get
      (UInt32.add L kg.toUInt32) 10 = vg := by
    rw [memWords_pres P1 htop (by rw [eg]; omega) (fun j hj => by rw [eg]; unfold OutF; omega)]
    exact C.buf kg vg hkg
  obtain ⟨N', eax, ecx, edx, fl, Rc, Pc, Mo, Va⟩ := fe_mul_call _ L (UInt32.add L kd.toUInt32)
    fp (UInt32.add L kg.toUInt32) r vf vg F1 hret hg0 hfv hgv hfi' hgi a ebx ebp esi edi f
    (icAdd ic0 c) (by rw [icAdd_toNat _ _ (by omega)]; omega)
  rw [icAdd_add] at Rc
  refine ⟨N', eax, ecx, edx, fl, R.trans Rc, C.next kd hkd ((P1.trans Pc).mono fun x hx => ⟨?_, ?_⟩), Mo, Va⟩
  · unfold OutF; have := hx.1; omega
  · have e828 : (L - 828).toNat = L.toNat - 828 := by
      rw [UInt32.toNat_sub]; unfold ramTop at htop; simp only [UInt32.reduceToNat]; omega
    unfold OutH OutF; rw [e828, ed]; omega

/-- A call of `fe_mul(hp, L + kf, L + kg)` with the output `hp` outside the region (the last call of a
function): the memory then agrees with the entry memory outside the region and `hp`, and the slots stay. -/
theorem CSt.mul_out {G N : XMem} {L : UInt32} {n W : Nat} {sl : List (Nat × UInt32)} {bf : List (Nat × Array UInt32)}
    (C : CSt G N L n W sl bf) (hW : 828 ≤ W) (hn : 8 ≤ n) (hp : UInt32) (kf kg : Nat)
    (hhm : hp.toNat + 40 ≤ G.get.size) (hhi : hp.toNat + 40 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ hp.toNat)
    (hhs : hp.toNat + 40 ≤ L.toNat - W ∨ L.toNat + n ≤ hp.toNat)
    {vf vg : Array UInt32} (hkf : bf.lookup kf = some vf) (hkg : bf.lookup kg = some vg) (hfi : MulIn vf)
    (hgi : MulIn vg) (r a ebx ebp esi edi f : UInt32) (ic0 : UInt64) (c : Nat) (hic : ic0.toNat + c + 891 < 2 ^ 63)
    (s0 : Machine) (h4 : (4 : UInt32).toNat + 4 ≤ n) (h0 : 4 ≤ n)
    (R : Run img s0 (St.m ⟨(stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get, a,
      hp, UInt32.add L kf.toUInt32, ebx, L, ebp, esi, edi, 0x100c20, efl f, icAdd ic0 c⟩)) :
    ∃ (N' : XMem) (eax ecx edx fl : UInt32),
      Run img s0 (St.m ⟨N'.get, eax, ecx, edx, ebx, UInt32.add L 4, ebp, esi, edi, r, efl fl, icAdd ic0 (c + 891)⟩) ∧
      Pres G N' (fun x => (x < L.toNat - W ∨ L.toNat + n ≤ x) ∧ (x < hp.toNat ∨ hp.toNat + 40 ≤ x)) ∧
      (∀ k v, sl.lookup k = some v → rdRaw N'.get (UInt32.add L k.toUInt32) 4 = v) ∧
      MulOut (memWords N'.get hp 10) ∧ feValI (memWords N'.get hp 10) % pI = feValI vf * feValI vg % pI := by
  have hkf' := mem_of_lookup hkf
  have hkg' := mem_of_lookup hkg
  have bf' := lay_buf C.lay hkf'
  have bg := lay_buf C.lay hkg'
  have ef := C.addr (k := kf) (by omega)
  have eg := C.addr (k := kg) (by omega)
  have hsz : (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get.size = N.get.size := by
    rw [stF0_size, stF_size]
  have hsG : N.get.size = G.get.size := C.pres.1
  have P1 : Pres N (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0) (OutF L 8) :=
    ((Pres.refl N _).wrF (by decide)).wrF0 (by decide)
  have hi := C.hi; have hw := C.w_lo; have himg := C.imgok; have htop := C.top
  have F1 : FieldFactsW 828 (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get.size L.toNat
      hp.toNat (UInt32.add L kf.toUInt32).toNat (UInt32.add L kg.toUInt32).toNat := by
    rw [hsz, ef, eg]
    exact ⟨htop, C.fit, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega⟩
  have FF := ((Frame.nil N L n).wrF 4 (j := 4) (v := UInt32.add L kg.toUInt32) (h := C.fb) (hj := h4) rfl rfl).wrF0
    (v := r) (h := stF_FB) (hn := h0)
  have hret : rdRaw (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get L 4 = r :=
    FF.rd0 (rfl : List.lookup 0 _ = some r)
  have hg0 : rdRaw (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get (L + 4) 4 =
      UInt32.add L kg.toUInt32 := FF.rd (rfl : List.lookup 4 _ = some _) 4 rfl
  have hfv : memWords (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get
      (UInt32.add L kf.toUInt32) 10 = vf := by
    rw [memWords_pres P1 htop (by rw [ef]; omega) (fun j hj => by rw [ef]; unfold OutF; omega)]
    exact C.buf kf vf hkf
  have hgv : memWords (stF0 (stF N L n 4 (UInt32.add L kg.toUInt32) C.fb h4) L n r stF_FB h0).get
      (UInt32.add L kg.toUInt32) 10 = vg := by
    rw [memWords_pres P1 htop (by rw [eg]; omega) (fun j hj => by rw [eg]; unfold OutF; omega)]
    exact C.buf kg vg hkg
  obtain ⟨N', eax, ecx, edx, fl, Rc, Pc, Mo, Va⟩ := fe_mul_call _ L hp
    (UInt32.add L kf.toUInt32) (UInt32.add L kg.toUInt32) r vf vg F1 hret hg0 hfv hgv hfi hgi a ebx ebp esi edi f
    (icAdd ic0 c) (by rw [icAdd_toNat _ _ (by omega)]; omega)
  rw [icAdd_add] at Rc
  have e828 : (L - 828).toNat = L.toNat - 828 := by
    rw [UInt32.toNat_sub]; unfold ramTop at htop; simp only [UInt32.reduceToNat]; omega
  have P2 := (C.pres.trans (P1.trans Pc)).mono (Q := fun x => (x < L.toNat - W ∨ L.toNat + n ≤ x) ∧
    (x < hp.toNat ∨ hp.toNat + 40 ≤ x)) fun x hx => ⟨hx.1, by unfold OutF; omega, by unfold OutH OutF; rw [e828]; omega⟩
  refine ⟨N', eax, ecx, edx, fl, R.trans Rc, P2, fun k v hl => ?_, Mo, Va⟩
  have hk := lay_slot C.lay (mem_of_lookup hl)
  have e := C.addr (k := k) (by omega)
  rw [← C.slot k v hl]
  exact (P1.trans Pc).rd C.top (by rw [e]; omega) (fun j hj => by
    rw [e]; refine ⟨by unfold OutF; omega, ?_⟩; unfold OutH OutF; rw [e828]; omega)

end Solutions.OpensslX25519.I
