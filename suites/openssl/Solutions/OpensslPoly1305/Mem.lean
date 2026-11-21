import Solutions.OpensslPoly1305.Cbv
/-!
# The memory of a run: a stack region and one data region

`MemOK G N U nU lU C nC mC lC P`: the stack region `[U, U + nU)` and the data region `[C, C + nC)`
are inside memory, apart from the image and from each other; the words `lU`, `lC` are in them; at
the addresses satisfying `P`, `N` is the earlier memory `G`, and `P` excludes the stack region and
the first `mC` bytes of the data region (where the run may store). A word store into either region
gives the `MemOK` of the new memory (`stU`, `stC`, …).
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305

structure MemOK (G N : PMem) (U : UInt32) (nU : Nat) (lU : List (Nat × UInt32)) (C : UInt32) (nC mC : Nat)
    (lC : List (Nat × UInt32)) (P : Nat → Prop) : Prop where
  fU : FB N.get.size U nU
  fC : FB N.get.size C nC
  dUC : C.toNat + nC ≤ U.toNat ∨ U.toNat + nU ≤ C.toNat
  wU : Frame N U nU lU
  wC : Frame N C nC lC
  pres : Pres G N P
  pU : ∀ x, P x → OutF U nU x
  pC : ∀ x, P x → OutF C mC x

variable {G N : PMem} {U C : UInt32} {nU nC mC : Nat} {lU lC : List (Nat × UInt32)} {P : Nat → Prop}

theorem MemOK.stU (h : MemOK G N U nU lU C nC mC lC P) (j : UInt32) (k : Nat) (v : UInt32)
    (hj : j.toNat + 4 ≤ nU) (hk : j.toNat = k) (h4 : k % 4 = 0) :
    MemOK G (stF N U nU j v h.fU hj) U nU ((k, v) :: lU) C nC mC lC P :=
  ⟨stF_FB, h.fC.size_eq stF_size, h.dUC, h.wU.wrF k hk h4, h.wC.wrX h.fC (by have := h.dUC; omega), h.pres.wrF h.pU,
    h.pU, h.pC⟩

theorem MemOK.stU0 (h : MemOK G N U nU lU C nC mC lC P) (v : UInt32) (hn : 4 ≤ nU) :
    MemOK G (stF0 N U nU v h.fU hn) U nU ((0, v) :: lU) C nC mC lC P :=
  ⟨stF0_FB, h.fC.size_eq stF0_size, h.dUC, h.wU.wrF0, h.wC.wrX0 h.fC (by have := h.dUC; omega),
    h.pres.wrF0 h.pU, h.pU, h.pC⟩

theorem MemOK.stC (h : MemOK G N U nU lU C nC mC lC P) (j : UInt32) (k : Nat) (v : UInt32)
    (hj : j.toNat + 4 ≤ nC) (hk : j.toNat = k) (h4 : k % 4 = 0) (hm : k + 4 ≤ mC) :
    MemOK G (stF N C nC j v h.fC hj) U nU lU C nC mC ((k, v) :: lC) P :=
  ⟨h.fU.size_eq stF_size, stF_FB, h.dUC, h.wU.wrX h.fU (by have := h.dUC; omega), h.wC.wrF k hk h4,
    h.pres.wr _ (fun x hx => by
      have e := h.fC.add_toNat (j := j) (by omega); have := h.pC x hx; unfold OutF at this; omega),
    h.pU, h.pC⟩

theorem MemOK.stC0 (h : MemOK G N U nU lU C nC mC lC P) (v : UInt32) (hn : 4 ≤ nC) (hm : 4 ≤ mC) :
    MemOK G (stF0 N C nC v h.fC hn) U nU lU C nC mC ((0, v) :: lC) P :=
  ⟨h.fU.size_eq stF0_size, stF0_FB, h.dUC, h.wU.wrX0 h.fU (by have := h.dUC; omega), h.wC.wrF0,
    h.pres.wr _ (fun x hx => by have := h.pC x hx; unfold OutF at this; omega), h.pU, h.pC⟩

/-- Fewer known words. -/
theorem MemOK.sub (h : MemOK G N U nU lU C nC mC lC P) (lU' lC' : List (Nat × UInt32))
    (hU : ∀ k v, lU'.lookup k = some v → lU.lookup k = some v)
    (hC : ∀ k v, lC'.lookup k = some v → lC.lookup k = some v) :
    MemOK G N U nU lU' C nC mC lC' P :=
  ⟨h.fU, h.fC, h.dUC, h.wU.sub lU' hU, h.wC.sub lC' hC, h.pres, h.pU, h.pC⟩

theorem MemOK.rdU (h : MemOK G N U nU lU C nC mC lC P) {k : Nat} {v : UInt32} (hl : lU.lookup k = some v)
    (j : UInt32) (hj : j.toNat = k) : rdRaw N.get (UInt32.add U j) 4 = v := h.wU.rd hl j hj

theorem MemOK.rdU0 (h : MemOK G N U nU lU C nC mC lC P) {v : UInt32} (hl : lU.lookup 0 = some v) :
    rdRaw N.get U 4 = v := h.wU.rd0 hl

theorem MemOK.rdC (h : MemOK G N U nU lU C nC mC lC P) {k : Nat} {v : UInt32} (hl : lC.lookup k = some v)
    (j : UInt32) (hj : j.toNat = k) : rdRaw N.get (UInt32.add C j) 4 = v := h.wC.rd hl j hj

theorem MemOK.rdC0 (h : MemOK G N U nU lU C nC mC lC P) {v : UInt32} (hl : lC.lookup 0 = some v) :
    rdRaw N.get C 4 = v := h.wC.rd0 hl

/-- A load outside the stack region and the written part of the data region reads `G`. -/
theorem MemOK.rdG (h : MemOK G N U nU lU C nC mC lC P) {a : UInt32} (ha : a.toNat + 4 ≤ G.get.size)
    (hout : ∀ k, k < 4 → P (a.toNat + k)) : rdRaw N.get a 4 = rdRaw G.get a 4 :=
  h.pres.rd (by rw [← h.pres.1]; exact h.fU.top) ha hout

/-- The memory `N` as the reference memory of a new run (for a callee, or a piece that keeps more). -/
theorem MemOK.self (h : MemOK G N U nU lU C nC mC lC P) (Q : Nat → Prop) (hQU : ∀ x, Q x → OutF U nU x)
    (hQC : ∀ x, Q x → OutF C mC x) : MemOK N N U nU lU C nC mC lC Q :=
  ⟨h.fU, h.fC, h.dUC, h.wU, h.wC, Pres.refl N Q, hQU, hQC⟩

/-- A run from `N` that keeps more (`Q`) than `P` continues a run from `G`. -/
theorem MemOK.join {N' : PMem} {lU' lC' : List (Nat × UInt32)} {Q : Nat → Prop} (h1 : MemOK G N U nU lU C nC mC lC P)
    (h2 : MemOK N N' U nU lU' C nC mC lC' Q) (hPQ : ∀ x, P x → Q x) : MemOK G N' U nU lU' C nC mC lC' P :=
  ⟨h2.fU, h2.fC, h2.dUC, h2.wU, h2.wC, h1.pres.trans (h2.pres.mono hPQ), h1.pU, h1.pC⟩

/-! ## Known words, and loads outside the regions -/

/-- The words `es` are among the known words `l`. -/
def LK (l : List (Nat × UInt32)) : List (Nat × UInt32) → Prop
  | [] => True
  | (k, v) :: es => l.lookup k = some v ∧ LK l es

theorem lk_here {k : Nat} {w : UInt32} {l : List (Nat × UInt32)} : ((k, w) :: l).lookup k = some w := by
  simp [List.lookup]

theorem lk_skip {k j : Nat} {w v : UInt32} {l : List (Nat × UInt32)} (hl : l.lookup k = some v)
    (h : (k == j) = false) : ((j, w) :: l).lookup k = some v := by
  simp [List.lookup, h, hl]

theorem MemOK.size (h : MemOK G N U nU lU C nC mC lC P) : N.get.size = G.get.size := h.pres.1

/-- A region `[p, p + L)` of the earlier memory that the run does not write. -/
structure ExtR (G : PMem) (P : Nat → Prop) (p : UInt32) (L : Nat) : Prop where
  fit : p.toNat + L ≤ G.get.size
  top : G.get.size ≤ ramTop
  cov : ∀ x, p.toNat ≤ x → x < p.toNat + L → P x

theorem ExtR.add_toNat {G : PMem} {P : Nat → Prop} {p : UInt32} {L : Nat} (E : ExtR G P p L) {j : UInt32}
    (hj : j.toNat ≤ L) : (UInt32.add p j).toNat = p.toNat + j.toNat := by
  have := E.fit; have := E.top
  rw [toNat_uadd]; unfold ramTop at *; omega

theorem MemOK.rdE (h : MemOK G N U nU lU C nC mC lC P) {p : UInt32} {L : Nat} (E : ExtR G P p L)
    (j : UInt32) (hj : j.toNat + 4 ≤ L) {x : UInt32} (hx : rdRaw G.get (UInt32.add p j) 4 = x) :
    rdRaw N.get (UInt32.add p j) 4 = x := by
  have e := E.add_toNat (j := j) (by omega)
  refine (h.rdG ?_ ?_).trans hx
  · rw [e]; have := E.fit; omega
  · intro k hk; rw [e]; exact E.cov _ (by omega) (by omega)

theorem alias_toNat {G : PMem} {P : Nat → Prop} {p : UInt32} {L : Nat} (E : ExtR G P p L)
    (j : UInt32) (hj : j.toNat + 4 ≤ L) {v : UInt32} (hv : v = (addF 4 p j 0).1) :
    v.toNat = p.toNat + j.toNat := by
  rw [hv, Solutions.Exec.addF_fst]; exact E.add_toNat (by omega)

theorem MemOK.rdEa (h : MemOK G N U nU lU C nC mC lC P) {p : UInt32} {L : Nat} (E : ExtR G P p L)
    (j : UInt32) (hj : j.toNat + 4 ≤ L) {x v : UInt32} (hx : rdRaw G.get (UInt32.add p j) 4 = x)
    (hv : v = (addF 4 p j 0).1) : rdRaw N.get v 4 = x := by
  rw [hv, Solutions.Exec.addF_fst]; exact h.rdE E j hj hx

theorem MemOK.rdE0 (h : MemOK G N U nU lU C nC mC lC P) {p : UInt32} {L : Nat} (E : ExtR G P p L)
    (hL : 4 ≤ L) {x : UInt32} (hx : rdRaw G.get p 4 = x) : rdRaw N.get p 4 = x := by
  refine (h.rdG ?_ ?_).trans hx
  · have := E.fit; omega
  · intro k hk; exact E.cov _ (by omega) (by omega)

/-! ## Back from a callee -/

theorem mem_of_lookup : ∀ {l : List (Nat × UInt32)} {k : Nat} {v : UInt32}, l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => by simp at h
  | (j, w) :: l, k, v, h => by
    rw [lookup_cons] at h
    split at h
    · rename_i e; subst e; simp only [Option.some.injEq] at h; subst h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem lk_of_mem : ∀ {l e : List (Nat × UInt32)}, LK l e → ∀ k v, (k, v) ∈ e → l.lookup k = some v
  | _, [], _, _, _, h => by simp at h
  | l, (j, w) :: e, ⟨h1, h2⟩, k, v, h => by
    rcases List.mem_cons.1 h with h | h
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact h1
    · exact lk_of_mem h2 k v h

theorem Frame.ofMem {N : PMem} {b : UInt32} {n : Nat} (l : List (Nat × UInt32))
    (h : ∀ k v, (k, v) ∈ l → k % 4 = 0 ∧ k + 4 ≤ n ∧ rdRaw N.get (UInt32.add b k.toUInt32) 4 = v) :
    Frame N b n l := fun k v hl => h k v (mem_of_lookup hl)

/-- After a callee run from `N` (keeping `Q ⊇ P`), the caller's words `eU`, `eC`: words it knew where
`Q` holds, or (in the same data region) words the callee states. -/
theorem MemOK.back {N' : PMem} {U' C' : UInt32} {nU' nC' mC' : Nat} {lU' lC' : List (Nat × UInt32)}
    {Q : Nat → Prop} (h1 : MemOK G N U nU lU C nC mC lC P) (h2 : MemOK N N' U' nU' lU' C' nC' mC' lC' Q)
    (hPQ : ∀ x, P x → Q x) (eU eC : List (Nat × UInt32))
    (hU : ∀ k v, (k, v) ∈ eU → lU.lookup k = some v ∧ ∀ j, j < 4 → Q (U.toNat + k + j))
    (hC : ∀ k v, (k, v) ∈ eC → (lC.lookup k = some v ∧ ∀ j, j < 4 → Q (C.toNat + k + j)) ∨
      (C' = C ∧ nC' = nC ∧ lC'.lookup k = some v)) :
    MemOK G N' U nU eU C nC mC eC P := by
  have hs : N'.get.size = N.get.size := h2.pres.1
  have top : N.get.size ≤ ramTop := h1.fU.top
  refine ⟨h1.fU.size_eq hs, h1.fC.size_eq hs, h1.dUC, ?_, ?_, h1.pres.trans (h2.pres.mono hPQ), h1.pU, h1.pC⟩
  · refine Frame.ofMem eU (fun k v hm => ?_)
    obtain ⟨hl, hq⟩ := hU k v hm
    obtain ⟨a1, a2, a3⟩ := h1.wU k v hl
    have e := Frame.add_toNat h1.fU (k := k) (by omega)
    refine ⟨a1, a2, ?_⟩
    rw [← a3]
    exact h2.pres.rd top (by rw [e]; have := h1.fU.fit; omega) (fun j hj => by rw [e]; exact hq j hj)
  · refine Frame.ofMem eC (fun k v hm => ?_)
    rcases hC k v hm with ⟨hl, hq⟩ | ⟨rfl, rfl, hl⟩
    · obtain ⟨a1, a2, a3⟩ := h1.wC k v hl
      have e := Frame.add_toNat h1.fC (k := k) (by omega)
      refine ⟨a1, a2, ?_⟩
      rw [← a3]
      exact h2.pres.rd top (by rw [e]; have := h1.fC.fit; omega) (fun j hj => by rw [e]; exact hq j hj)
    · exact h2.wC k v hl

end Solutions.OpensslPoly1305
