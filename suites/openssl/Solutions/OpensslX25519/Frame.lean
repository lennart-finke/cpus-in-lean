import Solutions.OpensslX25519.Call
import Solutions.Exec.Frame
import Solutions.Exec.Step
/-!
# Stack frames of the field functions

`fe_sq` and `fe_mul` keep their values in a stack frame (locals, then the saved registers, then the
return address) and finally store ten words into the output buffer. The runs of their pieces are
stated over an arbitrary memory `N : XMem`; what the pieces know about it is

* `FB N.get.size b n`: the region `[b, b + n)` is inside memory, which ends below `ramTop`, and apart
  from the image (the arithmetic `cbv`'s discharger needs);
* `Frame N b n l`: the words listed in `l` (byte offset, value) are in the region; a store into it
  (`stF`) puts its word in front of the list (`Frame.wrF`), a store elsewhere keeps it
  (`Frame.wr_other`);
* `Pres G N P`: at the addresses satisfying `P` (outside what the run writes), `N` is the caller's
  memory `G`.
-/
namespace Solutions.OpensslX25519
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

/-- The region `[b, b + n)` is inside memory, which ends below `ramTop`, and apart from the image. -/
structure FB (size : Nat) (b : UInt32) (n : Nat) : Prop where
  top : size ≤ ramTop
  fit : b.toNat + n ≤ size
  img : b.toNat + n ≤ 0x100000 ∨ 0x100000 + 47024 ≤ b.toNat

theorem FB.size_eq {s s' : Nat} {b : UInt32} {n : Nat} (e : s' = s) (h : FB s b n) : FB s' b n := e ▸ h

theorem FB.add_toNat {size : Nat} {b : UInt32} {n : Nat} (h : FB size b n) {j : UInt32}
    (hj : j.toNat ≤ n) : (UInt32.add b j).toNat = b.toNat + j.toNat := by
  have := h.fit; have := h.top
  rw [toNat_uadd]; unfold ramTop at *; omega

theorem storeOk_fb (N : XMem) {b : UInt32} {n : Nat} (h : FB N.get.size b n) {j : UInt32}
    (hj : j.toNat + 4 ≤ n) : StoreOk Image.base Image.size N.mem (UInt32.add b j) := by
  have e := h.add_toNat (j := j) (by omega)
  have h1 := h.fit; have h2 := h.img
  have hb : Image.base.toNat = 0x100000 := rfl
  have hs : Image.size = 47024 := rfl
  refine ⟨?_, ?_⟩
  · show (UInt32.add b j).toNat + 4 ≤ N.get.size; omega
  · rw [hb, hs]; omega

theorem storeOk_fb0 (N : XMem) {b : UInt32} {n : Nat} (h : FB N.get.size b n) (hn : 4 ≤ n) :
    StoreOk Image.base Image.size N.mem b := by
  have h1 := h.fit; have h2 := h.img
  have hb : Image.base.toNat = 0x100000 := rfl
  have hs : Image.size = 47024 := rfl
  refine ⟨?_, ?_⟩
  · show b.toNat + 4 ≤ N.get.size; omega
  · rw [hb, hs]; omega

/-- A word store into the region, at `b + j`. -/
def stF (N : XMem) (b : UInt32) (n : Nat) (j v : UInt32) (h : FB N.get.size b n)
    (hj : j.toNat + 4 ≤ n) : XMem :=
  CodeMem.wr4 N (UInt32.add b j) v (storeOk_fb N h hj)

/-- A word store at the base `b` of the region. -/
def stF0 (N : XMem) (b : UInt32) (n : Nat) (v : UInt32) (h : FB N.get.size b n) (hn : 4 ≤ n) : XMem :=
  CodeMem.wr4 N b v (storeOk_fb0 N h hn)

theorem stF_size {N : XMem} {b : UInt32} {n : Nat} {j v : UInt32} {h : FB N.get.size b n}
    {hj : j.toNat + 4 ≤ n} : (stF N b n j v h hj).get.size = N.get.size := wr4_get_size _ _ _ _

theorem stF0_size {N : XMem} {b : UInt32} {n : Nat} {v : UInt32} {h : FB N.get.size b n}
    {hn : 4 ≤ n} : (stF0 N b n v h hn).get.size = N.get.size := wr4_get_size _ _ _ _

theorem stF_FB {N : XMem} {b : UInt32} {n : Nat} {j v : UInt32} {h : FB N.get.size b n}
    {hj : j.toNat + 4 ≤ n} : FB (stF N b n j v h hj).get.size b n := h.size_eq stF_size

theorem stF0_FB {N : XMem} {b : UInt32} {n : Nat} {v : UInt32} {h : FB N.get.size b n}
    {hn : 4 ≤ n} : FB (stF0 N b n v h hn).get.size b n := h.size_eq stF0_size

/-! ## The words of a region -/

/-- The words `l` (byte offset in the region, value; the first entry of an offset counts) are in the
region `[b, b + n)`. Offsets are word-aligned. -/
def Frame (N : XMem) (b : UInt32) (n : Nat) (l : List (Nat × UInt32)) : Prop :=
  ∀ k v, l.lookup k = some v → k % 4 = 0 ∧ k + 4 ≤ n ∧ rdRaw N.get (UInt32.add b k.toUInt32) 4 = v

theorem Frame.nil (N : XMem) (b : UInt32) (n : Nat) : Frame N b n [] := fun _ _ h => by
  simp at h

theorem toUInt32_of_toNat {j : UInt32} {k : Nat} (hj : j.toNat = k) : k.toUInt32 = j := by
  subst hj; exact UInt32.ofNat_toNat

theorem Frame.rd {N : XMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame N b n l)
    {k : Nat} {v : UInt32} (h : l.lookup k = some v) (j : UInt32) (hj : j.toNat = k) :
    rdRaw N.get (UInt32.add b j) 4 = v := by
  have := (hF k v h).2.2
  rwa [toUInt32_of_toNat hj] at this

theorem Frame.rd0 {N : XMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame N b n l)
    {v : UInt32} (h : l.lookup 0 = some v) : rdRaw N.get b 4 = v := by
  have := (hF 0 v h).2.2
  rwa [show (0 : Nat).toUInt32 = 0 from rfl, uadd_zero] at this

theorem lookup_cons {k j : Nat} {w : UInt32} {l : List (Nat × UInt32)} :
    ((j, w) :: l).lookup k = if k = j then some w else l.lookup k := by
  simp only [List.lookup]
  by_cases h : k = j
  · subst h; simp
  · have : (k == j) = false := by simp [h]
    simp [this, h]

theorem Frame.add_toNat {size : Nat} {b : UInt32} {n : Nat} (h : FB size b n) {k : Nat} (hk : k ≤ n) :
    (UInt32.add b k.toUInt32).toNat = b.toNat + k := by
  have hk32 : k < 2 ^ 32 := by have := h.fit; have := h.top; unfold ramTop at *; omega
  have e : k.toUInt32.toNat = k := by
    rw [Nat.toUInt32, UInt32.toNat_ofNat']; omega
  rw [h.add_toNat (by omega), e]

theorem rd_wr4_frame (N : XMem) {b : UInt32} {n : Nat} (h : FB N.get.size b n) {a v : UInt32}
    {ok : StoreOk Image.base Image.size N.mem a} {j k : Nat} (ha : a.toNat = b.toNat + j)
    (hj : j % 4 = 0) (hk : k % 4 = 0) (hks : k + 4 ≤ n) :
    rdRaw (CodeMem.wr4 N a v ok).get (UInt32.add b k.toUInt32) 4 =
      if k = j then v else rdRaw N.get (UInt32.add b k.toUInt32) 4 := by
  have e := Frame.add_toNat h (k := k) (by omega)
  have hf := h.fit
  split
  · rename_i hkj
    subst hkj
    have : UInt32.add b k.toUInt32 = a := UInt32.toNat_inj.1 (by rw [e, ha])
    rw [this]
    exact rdBytes4_wrBytes4_self ok.1
  · rename_i hkj
    exact rdBytes4_wrBytes4_other ok.1 (by show (UInt32.add b k.toUInt32).toNat + 4 ≤ N.get.size; omega)
      (by omega)

theorem Frame.wrF {N : XMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame N b n l)
    {j v : UInt32} {h : FB N.get.size b n} {hj : j.toNat + 4 ≤ n} (k : Nat) (hk : j.toNat = k)
    (h4 : k % 4 = 0) : Frame (stF N b n j v h hj) b n ((k, v) :: l) := by
  intro k' v' hl
  rw [lookup_cons] at hl
  have ha : (UInt32.add b j).toNat = b.toNat + k := by rw [h.add_toNat (by omega), hk]
  by_cases hkk : k' = k
  · subst hkk
    simp only [ite_true, Option.some.injEq] at hl
    subst hl
    refine ⟨h4, by omega, ?_⟩
    show rdRaw (CodeMem.wr4 N _ v _).get _ 4 = _
    rw [rd_wr4_frame N h ha h4 h4 (by omega), if_pos rfl]
  · rw [if_neg hkk] at hl
    obtain ⟨a1, a2, a3⟩ := hF k' v' hl
    refine ⟨a1, a2, ?_⟩
    show rdRaw (CodeMem.wr4 N _ v _).get _ 4 = _
    rw [rd_wr4_frame N h ha h4 a1 a2, if_neg hkk, a3]

theorem Frame.wrF0 {N : XMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame N b n l)
    {v : UInt32} {h : FB N.get.size b n} {hn : 4 ≤ n} :
    Frame (stF0 N b n v h hn) b n ((0, v) :: l) := by
  intro k' v' hl
  rw [lookup_cons] at hl
  have ha : b.toNat = b.toNat + 0 := rfl
  by_cases hkk : k' = 0
  · subst hkk
    simp only [ite_true, Option.some.injEq] at hl
    subst hl
    refine ⟨rfl, by omega, ?_⟩
    show rdRaw (CodeMem.wr4 N _ v _).get _ 4 = _
    rw [rd_wr4_frame N h ha rfl rfl (by omega), if_pos rfl]
  · rw [if_neg hkk] at hl
    obtain ⟨a1, a2, a3⟩ := hF k' v' hl
    refine ⟨a1, a2, ?_⟩
    show rdRaw (CodeMem.wr4 N _ v _).get _ 4 = _
    rw [rd_wr4_frame N h ha rfl a1 a2, if_neg hkk, a3]

/-- A store outside the region keeps its words. -/
theorem Frame.wr_other {N : XMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame N b n l)
    (h : FB N.get.size b n) {a v : UInt32} (ok : StoreOk Image.base Image.size N.mem a)
    (hd : a.toNat + 4 ≤ b.toNat ∨ b.toNat + n ≤ a.toNat) : Frame (CodeMem.wr4 N a v ok) b n l := by
  intro k v' hl
  obtain ⟨a1, a2, a3⟩ := hF k v' hl
  refine ⟨a1, a2, ?_⟩
  have e := Frame.add_toNat h (k := k) (by omega)
  have hf := h.fit
  rw [← a3]
  exact rdBytes4_wrBytes4_other ok.1 (by show (UInt32.add b k.toUInt32).toNat + 4 ≤ N.get.size; omega)
    (by omega)

/-- Fewer words of the region. -/
theorem Frame.sub {N : XMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame N b n l)
    (l' : List (Nat × UInt32)) (h : ∀ k v, l'.lookup k = some v → l.lookup k = some v) : Frame N b n l' :=
  fun k v hl => hF k v (h k v hl)

/-! ## Memory outside the written regions -/

/-- At the addresses whose offset satisfies `P`, `N` is `G`; it has the size of `G`. -/
def Pres (G N : XMem) (P : Nat → Prop) : Prop :=
  N.get.size = G.get.size ∧ ∀ a : UInt32, a.toNat < G.get.size → P a.toNat → memByte N.get a = memByte G.get a

/-- Outside the stack frame `[b, b + n)`. -/
def OutF (b : UInt32) (n : Nat) (x : Nat) : Prop := x < b.toNat ∨ b.toNat + n ≤ x

theorem Pres.refl (G : XMem) (P : Nat → Prop) : Pres G G P := ⟨rfl, fun _ _ _ => rfl⟩

theorem Pres.mono {G N : XMem} {P Q : Nat → Prop} (hP : Pres G N P) (h : ∀ x, Q x → P x) : Pres G N Q :=
  ⟨hP.1, fun a ha hq => hP.2 a ha (h _ hq)⟩

theorem Pres.wr {G N : XMem} {P : Nat → Prop} (hP : Pres G N P) {a v : UInt32}
    (ok : StoreOk Image.base Image.size N.mem a) (hd : ∀ x, P x → x < a.toNat ∨ a.toNat + 4 ≤ x) :
    Pres G (CodeMem.wr4 N a v ok) P := by
  refine ⟨(wr4_get_size _ _ _ _).trans hP.1, fun x hx hp => ?_⟩
  rw [← hP.2 x hx hp]
  exact memByte_wr4_other N a v ok (by rw [hP.1]; exact hx) (hd _ hp)

/-- A store into the stack frame, at `b + j` with `j + 4 ≤ m`, keeps the memory outside `[b, b + m)`. -/
theorem Pres.wrF {G N : XMem} {b : UInt32} {n m : Nat} (hP : Pres G N (OutF b m)) {j v : UInt32}
    {h : FB N.get.size b n} {hj : j.toNat + 4 ≤ n} (hjm : j.toNat + 4 ≤ m) :
    Pres G (stF N b n j v h hj) (OutF b m) :=
  hP.wr _ (fun x hx => by have := h.add_toNat (j := j) (by omega); unfold OutF at hx; omega)

theorem Pres.wrF0 {G N : XMem} {b : UInt32} {n m : Nat} (hP : Pres G N (OutF b m)) {v : UInt32}
    {h : FB N.get.size b n} {hn : 4 ≤ n} (hm : 4 ≤ m) : Pres G (stF0 N b n v h hn) (OutF b m) :=
  hP.wr _ (fun x hx => by unfold OutF at hx; omega)

/-- Outside the stack frame `[b, b + ws)` and outside the output buffer `[hp, hp + 40)`. -/
def OutH (b : UInt32) (ws : Nat) (hp : UInt32) (x : Nat) : Prop :=
  OutF b ws x ∧ (x < hp.toNat ∨ hp.toNat + 40 ≤ x)

theorem Pres.toH {G N : XMem} {b : UInt32} {ws : Nat} (hP : Pres G N (OutF b ws)) (hp : UInt32) :
    Pres G N (OutH b ws hp) := hP.mono fun _ hx => hx.1

theorem Pres.wrH {G N : XMem} {b hp : UInt32} {ws : Nat} (hP : Pres G N (OutH b ws hp)) {j v : UInt32}
    {h : FB N.get.size hp 40} {hj : j.toNat + 4 ≤ 40} : Pres G (stF N hp 40 j v h hj) (OutH b ws hp) :=
  hP.wr _ (fun x hx => by have := h.add_toNat (j := j) (by omega); unfold OutH OutF at hx; omega)

theorem Pres.wrH0 {G N : XMem} {b hp : UInt32} {ws : Nat} (hP : Pres G N (OutH b ws hp)) {v : UInt32}
    {h : FB N.get.size hp 40} {hn : 4 ≤ 40} : Pres G (stF0 N hp 40 v h hn) (OutH b ws hp) :=
  hP.wr _ (fun x hx => by unfold OutH OutF at hx; omega)

/-- A store into the output buffer keeps the words of the stack frame. -/
theorem Frame.wrH {N : XMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame N b n l)
    (hS : FB N.get.size b n) {hp j v : UInt32} {h : FB N.get.size hp 40} {hj : j.toNat + 4 ≤ 40}
    (hd : hp.toNat + 40 ≤ b.toNat ∨ b.toNat + n ≤ hp.toNat) : Frame (stF N hp 40 j v h hj) b n l :=
  hF.wr_other hS _ (by have := h.add_toNat (j := j) (by omega); omega)

theorem Frame.wrH0 {N : XMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame N b n l)
    (hS : FB N.get.size b n) {hp v : UInt32} {h : FB N.get.size hp 40} {hn : 4 ≤ 40}
    (hd : hp.toNat + 40 ≤ b.toNat ∨ b.toNat + n ≤ hp.toNat) : Frame (stF0 N hp 40 v h hn) b n l :=
  hF.wr_other hS _ (by omega)

/-- A word load at addresses satisfying `P` reads the caller's memory. -/
theorem Pres.rd {G N : XMem} {P : Nat → Prop} (hP : Pres G N P) (htop : G.get.size ≤ ramTop)
    {a : UInt32} (ha : a.toNat + 4 ≤ G.get.size) (hout : ∀ k, k < 4 → P (a.toNat + k)) :
    rdRaw N.get a 4 = rdRaw G.get a 4 := by
  show rdBytes N.get a 4 = rdBytes G.get a 4
  apply rdBytes4_congr (by rw [hP.1]; exact ha) ha
  intro k hk
  have hk32 : a.toNat + k < 2 ^ 32 := by unfold ramTop at htop; omega
  have hb : (a + k.toUInt32).toNat = a.toNat + k := by
    rw [UInt32.toNat_add, Nat.toUInt32, UInt32.toNat_ofNat']; omega
  have := hP.2 (a + k.toUInt32) (by omega) (by rw [hb]; exact hout k hk)
  rw [memByte_def (by rw [hP.1]; omega), memByte_def (by omega), hb] at this
  exact this

end Solutions.OpensslX25519
