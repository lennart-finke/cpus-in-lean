import Solutions.OpensslPoly1305.CtxSize
import Solutions.OpensslPoly1305.Shapes
import Solutions.Exec.RunI
import Solutions.Exec.Mul
import Solutions.Exec.Frame
import Solutions.Logic.CodeWr1
/-!
# Regions of memory in the runs of the Poly1305 image

(Adapted from `Solutions.OpensslX25519.Frame` for the Poly1305 image, 1536 bytes at `0x100000`.)
The runs are stated over an arbitrary memory `N : PMem` (the image in the caller's memory);
what a run knows about it is

* `FB N.get.size b n`: the region `[b, b + n)` is inside memory, which ends below `ramTop`, and
  apart from the image;
* `Frame N b n l`: the words listed in `l` (byte offset, value) are in the region; a store into
  it (`stF`) puts its word in front of the list (`Frame.wrF`), a store elsewhere keeps it;
* `Pres G N P`: at the addresses satisfying `P`, `N` is the earlier memory `G`.
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305

theorem image_size : Image.bytes.size = Image.size := by simp [Image.bytes, ByteArray.size]
theorem img_size : img.bytes.size = 1536 := image_size
theorem img_base : img.base.toNat = 0x100000 := rfl

/-- A piece of `k` instructions starting `n` instructions into a call that started at `x`. -/
theorem icB {x : UInt64} (h : x.toNat < 2 ^ 63) {n k : Nat} (hn : n + k < 2 ^ 63) :
    (icAdd x n).toNat + k < 2 ^ 64 - 1 := by
  rw [icAdd_toNat _ _ (by omega)]; omega

theorem icAdd0 (x : UInt64) : icAdd x 0 = x := rfl

/-- The region `[b, b + n)` is inside memory, which ends below `ramTop`, and apart from the image. -/
structure FB (size : Nat) (b : UInt32) (n : Nat) : Prop where
  top : size ≤ ramTop
  fit : b.toNat + n ≤ size
  img : b.toNat + n ≤ 0x100000 ∨ 0x100000 + 1536 ≤ b.toNat

theorem FB.size_eq {s s' : Nat} {b : UInt32} {n : Nat} (e : s' = s) (h : FB s b n) : FB s' b n := e ▸ h

theorem FB.add_toNat {size : Nat} {b : UInt32} {n : Nat} (h : FB size b n) {j : UInt32}
    (hj : j.toNat ≤ n) : (UInt32.add b j).toNat = b.toNat + j.toNat := by
  have := h.fit; have := h.top
  rw [toNat_uadd]; unfold ramTop at *; omega

theorem storeOk_fb (N : PMem) {b : UInt32} {n : Nat} (h : FB N.get.size b n) {j : UInt32}
    (hj : j.toNat + 4 ≤ n) : StoreOk Image.base Image.size N.mem (UInt32.add b j) := by
  have e := h.add_toNat (j := j) (by omega)
  have h1 := h.fit; have h2 := h.img
  have hb : Image.base.toNat = 0x100000 := rfl
  have hs : Image.size = 1536 := rfl
  refine ⟨?_, ?_⟩
  · show (UInt32.add b j).toNat + 4 ≤ N.get.size; omega
  · rw [hb, hs]; omega

theorem storeOk_fb0 (N : PMem) {b : UInt32} {n : Nat} (h : FB N.get.size b n) (hn : 4 ≤ n) :
    StoreOk Image.base Image.size N.mem b := by
  have h1 := h.fit; have h2 := h.img
  have hb : Image.base.toNat = 0x100000 := rfl
  have hs : Image.size = 1536 := rfl
  refine ⟨?_, ?_⟩
  · show b.toNat + 4 ≤ N.get.size; omega
  · rw [hb, hs]; omega

/-- A word store into the region, at `b + j`. -/
def stF (N : PMem) (b : UInt32) (n : Nat) (j v : UInt32) (h : FB N.get.size b n)
    (hj : j.toNat + 4 ≤ n) : PMem :=
  CodeMem.wr4 N (UInt32.add b j) v (storeOk_fb N h hj)

/-- A word store at the base `b` of the region. -/
def stF0 (N : PMem) (b : UInt32) (n : Nat) (v : UInt32) (h : FB N.get.size b n) (hn : 4 ≤ n) : PMem :=
  CodeMem.wr4 N b v (storeOk_fb0 N h hn)

theorem stF_size {N : PMem} {b : UInt32} {n : Nat} {j v : UInt32} {h : FB N.get.size b n}
    {hj : j.toNat + 4 ≤ n} : (stF N b n j v h hj).get.size = N.get.size := wr4_get_size _ _ _ _

theorem stF0_size {N : PMem} {b : UInt32} {n : Nat} {v : UInt32} {h : FB N.get.size b n}
    {hn : 4 ≤ n} : (stF0 N b n v h hn).get.size = N.get.size := wr4_get_size _ _ _ _

theorem stF_FB {N : PMem} {b : UInt32} {n : Nat} {j v : UInt32} {h : FB N.get.size b n}
    {hj : j.toNat + 4 ≤ n} : FB (stF N b n j v h hj).get.size b n := h.size_eq stF_size

theorem stF0_FB {N : PMem} {b : UInt32} {n : Nat} {v : UInt32} {h : FB N.get.size b n}
    {hn : 4 ≤ n} : FB (stF0 N b n v h hn).get.size b n := h.size_eq stF0_size

/-! ## The words of a region -/

/-- The words `l` (byte offset in the region, value; the first entry of an offset counts) are in the
region `[b, b + n)`. Offsets are word-aligned. -/
def Frame (N : PMem) (b : UInt32) (n : Nat) (l : List (Nat × UInt32)) : Prop :=
  ∀ k v, l.lookup k = some v → k % 4 = 0 ∧ k + 4 ≤ n ∧ rdRaw N.get (UInt32.add b k.toUInt32) 4 = v

theorem Frame.nil (N : PMem) (b : UInt32) (n : Nat) : Frame N b n [] := fun _ _ h => by
  simp at h

theorem toUInt32_of_toNat {j : UInt32} {k : Nat} (hj : j.toNat = k) : k.toUInt32 = j := by
  subst hj; exact UInt32.ofNat_toNat

theorem Frame.rd {N : PMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame N b n l)
    {k : Nat} {v : UInt32} (h : l.lookup k = some v) (j : UInt32) (hj : j.toNat = k) :
    rdRaw N.get (UInt32.add b j) 4 = v := by
  have := (hF k v h).2.2
  rwa [toUInt32_of_toNat hj] at this

theorem Frame.rd0 {N : PMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame N b n l)
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

theorem rd_wr4_frame (N : PMem) {b : UInt32} {n : Nat} (h : FB N.get.size b n) {a v : UInt32}
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

theorem Frame.wrF {N : PMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame N b n l)
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

theorem Frame.wrF0 {N : PMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame N b n l)
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
theorem Frame.wr_other {N : PMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame N b n l)
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

/-- A store into another region keeps the words of a region. -/
theorem Frame.wrX {N : PMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame N b n l)
    (hS : FB N.get.size b n) {c j v : UInt32} {m : Nat} {h : FB N.get.size c m} {hj : j.toNat + 4 ≤ m}
    (hd : c.toNat + m ≤ b.toNat ∨ b.toNat + n ≤ c.toNat) : Frame (stF N c m j v h hj) b n l :=
  hF.wr_other hS _ (by have := h.add_toNat (j := j) (by omega); omega)

theorem Frame.wrX0 {N : PMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame N b n l)
    (hS : FB N.get.size b n) {c v : UInt32} {m : Nat} {h : FB N.get.size c m} {hn : 4 ≤ m}
    (hd : c.toNat + m ≤ b.toNat ∨ b.toNat + n ≤ c.toNat) : Frame (stF0 N c m v h hn) b n l :=
  hF.wr_other hS _ (by omega)

/-- Fewer words of the region. -/
theorem Frame.sub {N : PMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame N b n l)
    (l' : List (Nat × UInt32)) (h : ∀ k v, l'.lookup k = some v → l.lookup k = some v) : Frame N b n l' :=
  fun k v hl => hF k v (h k v hl)

/-! ## Memory outside the written regions -/

/-- At the addresses satisfying `P`, `N` is `G`; it has the size of `G`. -/
def Pres (G N : PMem) (P : Nat → Prop) : Prop :=
  N.get.size = G.get.size ∧ ∀ a : UInt32, a.toNat < G.get.size → P a.toNat → memByte N.get a = memByte G.get a

/-- Outside the region `[b, b + n)`. -/
def OutF (b : UInt32) (n : Nat) (x : Nat) : Prop := x < b.toNat ∨ b.toNat + n ≤ x

theorem Pres.refl (G : PMem) (P : Nat → Prop) : Pres G G P := ⟨rfl, fun _ _ _ => rfl⟩

theorem Pres.mono {G N : PMem} {P Q : Nat → Prop} (hP : Pres G N P) (h : ∀ x, Q x → P x) : Pres G N Q :=
  ⟨hP.1, fun a ha hq => hP.2 a ha (h _ hq)⟩

theorem Pres.trans {G N K : PMem} {P : Nat → Prop} (h1 : Pres G N P) (h2 : Pres N K P) : Pres G K P :=
  ⟨h2.1.trans h1.1, fun a ha hp => (h2.2 a (by rw [h1.1]; exact ha) hp).trans (h1.2 a ha hp)⟩

theorem Pres.wr {G N : PMem} {P : Nat → Prop} (hP : Pres G N P) {a v : UInt32}
    (ok : StoreOk Image.base Image.size N.mem a) (hd : ∀ x, P x → x < a.toNat ∨ a.toNat + 4 ≤ x) :
    Pres G (CodeMem.wr4 N a v ok) P := by
  refine ⟨(wr4_get_size _ _ _ _).trans hP.1, fun x hx hp => ?_⟩
  rw [← hP.2 x hx hp]
  exact memByte_wr4_other N a v ok (by rw [hP.1]; exact hx) (hd _ hp)

/-- A store into a region `[b, b + n)`, at `b + j`, keeps the memory where `P` excludes the region. -/
theorem Pres.wrF {G N : PMem} {b : UInt32} {n : Nat} {P : Nat → Prop} (hP : Pres G N P) {j v : UInt32}
    {h : FB N.get.size b n} {hj : j.toNat + 4 ≤ n} (hx : ∀ x, P x → OutF b n x) :
    Pres G (stF N b n j v h hj) P :=
  hP.wr _ (fun x hp => by have := h.add_toNat (j := j) (by omega); have := hx x hp; unfold OutF at this; omega)

theorem Pres.wrF0 {G N : PMem} {b : UInt32} {n : Nat} {P : Nat → Prop} (hP : Pres G N P) {v : UInt32}
    {h : FB N.get.size b n} {hn : 4 ≤ n} (hx : ∀ x, P x → OutF b n x) : Pres G (stF0 N b n v h hn) P :=
  hP.wr _ (fun x hp => by have := hx x hp; unfold OutF at this; omega)

/-- A word load at addresses satisfying `P` reads the earlier memory. -/
theorem Pres.rd {G N : PMem} {P : Nat → Prop} (hP : Pres G N P) (htop : G.get.size ≤ ramTop)
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

/-- A frame's words survive a run that keeps the region. -/
theorem Frame.pres {G N : PMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame G b n l)
    (hS : FB G.get.size b n) {P : Nat → Prop} (hP : Pres G N P) (hin : ∀ x, b.toNat ≤ x → x < b.toNat + n → P x) :
    Frame N b n l := by
  intro k v hl
  obtain ⟨a1, a2, a3⟩ := hF k v hl
  refine ⟨a1, a2, ?_⟩
  have e := Frame.add_toNat hS (k := k) (by omega)
  rw [← a3]
  exact hP.rd hS.top (by rw [e]; have := hS.fit; omega) (fun j hj => hin _ (by omega) (by omega))

end Solutions.OpensslPoly1305
