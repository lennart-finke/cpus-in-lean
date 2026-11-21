import Solutions.OpensslSha256.Frame
/-!
# Steps of instructions whose operands depend on the registers

The kinds of `Frame` with the address, stored value and register update given as functions of the
registers, so that a chain of steps can be written without naming the intermediate states: the
functions are fixed by the instruction, the states are found by unification. `Seg` is a piece of a
run between two cut points: from the slots and registers given by a *pre* function of anything at
all, to those given by a *post* function of some state.
-/
namespace Solutions.OpensslSha256
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslSha256

theorem R.ext' {r s : R} (h1 : r.eax = s.eax) (h2 : r.ecx = s.ecx) (h3 : r.edx = s.edx) (h4 : r.ebx = s.ebx)
    (h5 : r.esp = s.esp) (h6 : r.ebp = s.ebp) (h7 : r.esi = s.esi) (h8 : r.edi = s.edi) : r = s := by
  cases r; cases s; simp_all

theorem Steps.congrR {E : Env} {n : Nat} {p p' : UInt32} {r r' r'' : R} {F F' : Nat → UInt32}
    (h : Steps E n p r F p' r' F') (hr : r' = r'') : Steps E n p r F p' r'' F' := hr ▸ h

theorem Steps.congrN {E : Env} {n n' : Nat} {p p' : UInt32} {r r' : R} {F F' : Nat → UInt32}
    (h : Steps E n p r F p' r' F') (hn : n = n') : Steps E n' p r F p' r' F' := hn ▸ h

theorem Steps.congrP {E : Env} {n : Nat} {p p' p'' : UInt32} {r r' : R} {F F' : Nat → UInt32}
    (h : Steps E n p r F p' r' F') (hp : p' = p'') : Steps E n p r F p'' r' F' := hp ▸ h

theorem Steps.load' {E : Env} {p p' : UInt32} {n : Nat} {code : Nat → UInt8} {r : R} {F : Nat → UInt32}
    (g : R → UInt32 → R) (fa : R → UInt32) (j : Nat) (hj : j < 56) (ha : fa r = slotAddr E j)
    (hp : p ≠ Image.sym_halt) (hc : CodeIn p n code)
    (hx : ∀ (G : CodeMem p n code) fl ic, G.get.size ≤ ramTop → (fa r).toNat + 4 ≤ G.get.size →
      ∃ fl', okState (execInstr (conc G.get r fl p ic)) = some (conc G.get (g r (rdRaw G.get (fa r) 4)) fl' p' ic)) :
    Steps E 1 p r F p' (g r (F j)) F :=
  Steps.load (g r) (fa r) j hj ha hp hc hx

theorem Steps.store' {E : Env} {p p' : UInt32} {n : Nat} {code : Nat → UInt8} {r : R} {F : Nat → UInt32}
    (fr : R → R) (fa fv : R → UInt32) (j : Nat) (hj : j < 56) (ha : fa r = slotAddr E j)
    (hp : p ≠ Image.sym_halt) (hc : CodeIn p n code)
    (hx : ∀ (G : CodeMem p n code) fl ic, G.get.size ≤ ramTop → (fa r).toNat + 4 ≤ G.get.size →
      ∃ fl', okState (execInstr (conc G.get r fl p ic)) = some (conc (wrBytes G.get (fa r) 4 (fv r)) (fr r) fl' p' ic)) :
    Steps E 1 p r F p' (fr r) (upd F j (fv r)) :=
  Steps.store (fa r) (fv r) j hj ha hp hc hx

theorem Steps.rmw' {E : Env} {p p' : UInt32} {n : Nat} {code : Nat → UInt8} {r : R} {F : Nat → UInt32}
    (fa : R → UInt32) (g : R → UInt32 → UInt32) (j : Nat) (hj : j < 56) (ha : fa r = slotAddr E j)
    (hp : p ≠ Image.sym_halt) (hc : CodeIn p n code)
    (hx : ∀ (G : CodeMem p n code) fl ic, G.get.size ≤ ramTop → (fa r).toNat + 4 ≤ G.get.size →
      ∃ fl', okState (execInstr (conc G.get r fl p ic)) =
        some (conc (wrBytes G.get (fa r) 4 (g r (rdRaw G.get (fa r) 4))) r fl' p' ic)) :
    Steps E 1 p r F p' r (upd F j (g r (F j))) :=
  Steps.rmw (fa r) (g r) j hj ha hp hc hx

/-- A word of the block. -/
def blkWord (E : Env) (k : Nat) : UInt32 := rdBytes E.M0 (E.blk + (4 * k).toUInt32) 4

theorem blk_toNat (E : Env) (k : Nat) (hk : k < 16) : (E.blk + (4 * k).toUInt32).toNat = E.blk.toNat + 4 * k := by
  have := E.hblk; have := E.hsz; unfold ramTop at *
  exact toNat_add_of_lt (by omega)

theorem Steps.loadBlk {E : Env} {p p' : UInt32} {n : Nat} {code : Nat → UInt8} {r : R} {F : Nat → UInt32}
    (g : R → UInt32 → R) (fa : R → UInt32) (k : Nat) (hk : k < 16) (ha : fa r = E.blk + (4 * k).toUInt32)
    (hp : p ≠ Image.sym_halt) (hc : CodeIn p n code)
    (hx : ∀ (G : CodeMem p n code) fl ic, G.get.size ≤ ramTop → (fa r).toNat + 4 ≤ G.get.size →
      ∃ fl', okState (execInstr (conc G.get r fl p ic)) = some (conc G.get (g r (rdRaw G.get (fa r) 4)) fl' p' ic)) :
    Steps E 1 p r F p' (g r (blkWord E k)) F := by
  have h1 := blk_toNat E k hk
  have := E.hblk; have := E.blk_sp; have := E.blk_ctx
  have := Steps.loadOut (E := E) (F := F) (g r) (fa r) (by rw [ha, h1]; omega)
    (fun i hi => by rw [ha, h1]; unfold InSlots; omega) hp hc hx
  rw [ha] at this
  exact this

/-- A word of the image. -/
def imgWord (i : Nat) : UInt32 :=
  (Image.byte i).toUInt32 ||| ((Image.byte (i + 1)).toUInt32 <<< 8) ||| ((Image.byte (i + 2)).toUInt32 <<< 16) |||
    ((Image.byte (i + 3)).toUInt32 <<< 24)

theorem img_byte (E : Env) (a : UInt32) (k : Nat) (h1 : imgBase ≤ a.toNat) (h2 : a.toNat + k < imgBase + imgSize) :
    E.M0.get! (a.toNat + k) = Image.byte (a.toNat - imgBase + k) :=
  (congrArg E.M0.get! (show imgBase + (a.toNat - imgBase + k) = a.toNat + k by omega)).symm.trans
    (E.hcode _ (by omega))

theorem img_word (E : Env) (a : UInt32) (ha : imgBase ≤ a.toNat ∧ a.toNat + 4 ≤ imgBase + imgSize) :
    rdBytes E.M0 a 4 = imgWord (a.toNat - imgBase) := by
  have hs := E.himg
  rw [rdBytes4_eq (by omega)]
  have e0 := img_byte E a 0 ha.1 (by omega)
  have e1 := img_byte E a 1 ha.1 (by omega)
  have e2 := img_byte E a 2 ha.1 (by omega)
  have e3 := img_byte E a 3 ha.1 (by omega)
  rw [Nat.add_zero, Nat.add_zero] at e0
  rw [e0, e1, e2, e3]
  rfl

theorem Steps.loadImg {E : Env} {p p' : UInt32} {n : Nat} {code : Nat → UInt8} {r : R} {F : Nat → UInt32}
    (g : R → UInt32 → R) (a : UInt32) (ha : imgBase ≤ a.toNat ∧ a.toNat + 4 ≤ imgBase + imgSize) (w : UInt32)
    (hw : imgWord (a.toNat - imgBase) = w)
    (hp : p ≠ Image.sym_halt) (hc : CodeIn p n code)
    (hx : ∀ (G : CodeMem p n code) fl ic, G.get.size ≤ ramTop → a.toNat + 4 ≤ G.get.size →
      ∃ fl', okState (execInstr (conc G.get r fl p ic)) = some (conc G.get (g r (rdRaw G.get a 4)) fl' p' ic)) :
    Steps E 1 p r F p' (g r w) F := by
  have := E.sp_img; have := E.ctx_img; have := E.himg
  have h := Steps.loadOut (E := E) (F := F) (g r) a (by unfold imgBase imgSize at *; omega)
    (fun i hi => by unfold InSlots imgBase imgSize at *; omega) hp hc hx
  rwa [img_word E a ha, hw] at h

/-- A piece of a run: from the registers `Pr r0` and slots `Pf F0` (for any `r0`, `F0`) to the
registers `Qr r1` and slots `Qf F1` for some `r1`, `F1`. -/
def Seg (E : Env) (n : Nat) (p : UInt32) (Pr : R → R) (Pf : (Nat → UInt32) → Nat → UInt32) (p' : UInt32)
    (Qr : R → R) (Qf : (Nat → UInt32) → Nat → UInt32) : Prop :=
  ∀ r0 F0, ∃ r1 F1, Steps E n p (Pr r0) (Pf F0) p' (Qr r1) (Qf F1)

theorem Seg.trans {E : Env} {n₁ n₂ : Nat} {p₁ p₂ p₃ : UInt32} {Pr Qr Sr : R → R}
    {Pf Qf Sf : (Nat → UInt32) → Nat → UInt32}
    (h₁ : Seg E n₁ p₁ Pr Pf p₂ Qr Qf) (h₂ : Seg E n₂ p₂ Qr Qf p₃ Sr Sf) : Seg E (n₁ + n₂) p₁ Pr Pf p₃ Sr Sf := by
  intro r0 F0
  obtain ⟨r1, F1, h⟩ := h₁ r0 F0
  obtain ⟨r2, F2, h'⟩ := h₂ r1 F1
  exact ⟨r2, F2, h.trans h'⟩

/-- `F` with the slots of the list set. -/
def updL (F : Nat → UInt32) : List (Nat × UInt32) → Nat → UInt32
  | [] => F
  | jv :: L => upd (updL F L) jv.1 jv.2

/-- `F` has the values of the list. -/
def AllEq (F : Nat → UInt32) : List (Nat × UInt32) → Prop
  | [] => True
  | jv :: L => F jv.1 = jv.2 ∧ AllEq F L

theorem updL_self (F : Nat → UInt32) : ∀ (L : List (Nat × UInt32)), AllEq F L → ∀ k, updL F L k = F k
  | [], _, _ => rfl
  | jv :: L, ⟨h, hL⟩, k => by
    unfold updL upd
    split
    · rename_i hk; rw [hk, h]
    · exact updL_self F L hL k

theorem sub_norm (x a b c : UInt32) (h : a - b = c) : x + a - b = x + c := by
  subst h
  apply UInt32.toNat_inj.1
  simp only [UInt32.toNat_add, UInt32.toNat_sub]
  have := x.toNat_lt; have := a.toNat_lt; have := b.toNat_lt
  omega

theorem add_norm (x a b c : UInt32) (h : a + b = c) : x + a + b = x + c := by
  subst h; exact UInt32.add_assoc x a b

/-! ## Runs with the flags given

`StepsF` is `Steps` with the arithmetic flags fixed at both ends: for the branches. -/

def StepsF (E : Env) (n : Nat) (p : UInt32) (r : R) (fl : UInt32) (F : Nat → UInt32) (p' : UInt32) (r' : R)
    (fl' : UInt32) (F' : Nat → UInt32) : Prop :=
  ∀ (M : ByteArray) (ic : UInt64), Inv E M F → ic.toNat + n < 2 ^ 64 →
    ∃ M', Run img (conc M r fl p ic) (conc M' r' fl' p' (ic + n.toUInt64)) ∧ Inv E M' F'

theorem StepsF.trans {E : Env} {n₁ n₂ : Nat} {p₁ p₂ p₃ : UInt32} {r₁ r₂ r₃ : R} {f₁ f₂ f₃ : UInt32}
    {F₁ F₂ F₃ : Nat → UInt32}
    (h₁ : StepsF E n₁ p₁ r₁ f₁ F₁ p₂ r₂ f₂ F₂) (h₂ : StepsF E n₂ p₂ r₂ f₂ F₂ p₃ r₃ f₃ F₃) :
    StepsF E (n₁ + n₂) p₁ r₁ f₁ F₁ p₃ r₃ f₃ F₃ := by
  intro M ic hI hic
  obtain ⟨M₁, hr₁, hI₁⟩ := h₁ M ic hI (by omega)
  have hic₁ : (ic + n₁.toUInt64).toNat = ic.toNat + n₁ := by
    rw [UInt64.toNat_add]; simp; omega
  obtain ⟨M₂, hr₂, hI₂⟩ := h₂ M₁ (ic + n₁.toUInt64) hI₁ (by omega)
  refine ⟨M₂, hr₁.trans ?_, hI₂⟩
  have : ic + n₁.toUInt64 + n₂.toUInt64 = ic + (n₁ + n₂).toUInt64 := by
    apply UInt64.toNat_inj.1
    simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  rw [← this]; exact hr₂

/-- Forget the flags. -/
theorem Steps.ofF {E : Env} {n : Nat} {p p' : UInt32} {r r' : R} {F F' : Nat → UInt32}
    (h : ∀ fl, ∃ fl', StepsF E n p r fl F p' r' fl' F') : Steps E n p r F p' r' F' := by
  intro M fl ic hI hic
  obtain ⟨fl', h'⟩ := h fl
  obtain ⟨M', hr, hI'⟩ := h' M ic hI hic
  exact ⟨M', fl', hr, hI'⟩

theorem StepsF.one {E : Env} {p p' : UInt32} {r r' : R} {fl fl' : UInt32} {F F' : Nat → UInt32}
    (hp : p ≠ Image.sym_halt)
    (h : ∀ M ic, Inv E M F → ∃ M', okState (execInstr (conc M r fl p ic)) = some (conc M' r' fl' p' ic) ∧
      Inv E M' F') : StepsF E 1 p r fl F p' r' fl' F' := by
  intro M ic hI hic
  obtain ⟨M', hx, hI'⟩ := h M ic hI
  refine ⟨M', ?_, hI'⟩
  have hlt : ic < 0xFFFFFFFFFFFFFFFF := by rw [UInt64.lt_iff_toNat_lt]; simp; omega
  have hTF : (efl fl) &&& Flag.TF = 0 := efl_TF fl
  have := step_of_okState ⟨M, r.eax, r.ecx, r.edx, r.ebx, r.esp, r.ebp, r.esi, r.edi, p, efl fl, ic⟩ hlt hTF
    ⟨M', r'.eax, r'.ecx, r'.edx, r'.ebx, r'.esp, r'.ebp, r'.esi, r'.edi, p', efl fl', ic⟩ hx rfl
  exact Run.single (running_conc M r fl p ic hp) this

theorem StepsF.reg {E : Env} {p p' : UInt32} {n : Nat} {code : Nat → UInt8} {r r' : R} {fl fl' : UInt32}
    {F : Nat → UInt32} (hp : p ≠ Image.sym_halt) (hc : CodeIn p n code)
    (hx : ∀ (G : CodeMem p n code) ic, G.get.size ≤ ramTop →
      okState (execInstr (conc G.get r fl p ic)) = some (conc G.get r' fl' p' ic)) :
    StepsF E 1 p r fl F p' r' fl' F :=
  StepsF.one hp fun M ic hI => ⟨M, hx (win hI hc) ic hI.ram, hI⟩

theorem StepsF.load' {E : Env} {p p' : UInt32} {n : Nat} {code : Nat → UInt8} {r : R} {fl : UInt32}
    {F : Nat → UInt32}
    (g : R → UInt32 → R) (fa : R → UInt32) (j : Nat) (hj : j < 56) (ha : fa r = slotAddr E j)
    (hp : p ≠ Image.sym_halt) (hc : CodeIn p n code)
    (hx : ∀ (G : CodeMem p n code) ic, G.get.size ≤ ramTop → (fa r).toNat + 4 ≤ G.get.size →
      okState (execInstr (conc G.get r fl p ic)) = some (conc G.get (g r (rdRaw G.get (fa r) 4)) fl p' ic)) :
    StepsF E 1 p r fl F p' (g r (F j)) fl F :=
  StepsF.one hp fun M ic hI => by
    have h := hx (win hI hc) ic hI.ram (hI.fits hj ha)
    rw [win_get, hI.load hj ha] at h
    exact ⟨M, h, hI⟩

theorem StepsF.store' {E : Env} {p p' : UInt32} {n : Nat} {code : Nat → UInt8} {r : R} {fl : UInt32}
    {F : Nat → UInt32}
    (fr : R → R) (fa fv : R → UInt32) (j : Nat) (hj : j < 56) (ha : fa r = slotAddr E j)
    (hp : p ≠ Image.sym_halt) (hc : CodeIn p n code)
    (hx : ∀ (G : CodeMem p n code) ic, G.get.size ≤ ramTop → (fa r).toNat + 4 ≤ G.get.size →
      okState (execInstr (conc G.get r fl p ic)) = some (conc (wrBytes G.get (fa r) 4 (fv r)) (fr r) fl p' ic)) :
    StepsF E 1 p r fl F p' (fr r) fl (upd F j (fv r)) :=
  StepsF.one hp fun M ic hI => ⟨_, hx (win hI hc) ic hI.ram (hI.fits hj ha), hI.store hj ha _⟩

/-- A chain step for `apply`: `k` steps, then the rest (the count is a literal, so that the
remaining count is found by unification). -/
theorem Steps.consK {E : Env} (k : Nat) {n : Nat} {p₁ p₂ p₃ : UInt32} {r₁ r₂ r₃ : R}
    {F₁ F₂ F₃ : Nat → UInt32} (h₁ : Steps E k p₁ r₁ F₁ p₂ r₂ F₂) (h₂ : Steps E n p₂ r₂ F₂ p₃ r₃ F₃) :
    Steps E (n + k) p₁ r₁ F₁ p₃ r₃ F₃ := by
  have := h₁.trans h₂; rwa [Nat.add_comm] at this

/-- Rename the stack pointer of the final state. -/
theorem Steps.congrEsp {E : Env} {n : Nat} {p p' : UInt32} {r r' : R} {F F' : Nat → UInt32}
    (h : Steps E n p r F p' r' F') (e : UInt32) (he : r'.esp = e) : Steps E n p r F p' { r' with esp := e } F' := by
  have : r' = { r' with esp := e } := by cases r'; simp_all
  rw [← this]; exact h

/-- A return through a slot: the next address is the slot's word. -/
theorem Steps.ret {E : Env} {p : UInt32} {n : Nat} {code : Nat → UInt8} {r : R} {F : Nat → UInt32}
    (fr : R → R) (fa : R → UInt32) (j : Nat) (hj : j < 56) (ha : fa r = slotAddr E j)
    (hp : p ≠ Image.sym_halt) (hc : CodeIn p n code)
    (hx : ∀ (G : CodeMem p n code) fl ic, G.get.size ≤ ramTop → (fa r).toNat + 4 ≤ G.get.size →
      ∃ fl', okState (execInstr (conc G.get r fl p ic)) = some (conc G.get (fr r) fl' (rdRaw G.get (fa r) 4) ic)) :
    Steps E 1 p r F (F j) (fr r) F :=
  Steps.one hp fun M fl ic hI => by
    obtain ⟨fl', h⟩ := hx (win hI hc) fl ic hI.ram (hI.fits hj ha)
    rw [win_get, hI.load hj ha] at h
    exact ⟨M, fl', h, hI⟩

/-- A load or a return through a word outside the slots, the image and the block (the three
words of the call above the frame): the caller's memory. -/
theorem Steps.loadOut' {E : Env} {p : UInt32} {n : Nat} {code : Nat → UInt8} {r : R} {F : Nat → UInt32}
    (r' : R → UInt32 → R) (p'' : R → UInt32 → UInt32) (fa : R → UInt32) (k : Nat) (hk : k < 3)
    (ha : fa r = E.sp + (192 + 4 * k).toUInt32)
    (hp : p ≠ Image.sym_halt) (hc : CodeIn p n code)
    (hx : ∀ (G : CodeMem p n code) fl ic, G.get.size ≤ ramTop → (fa r).toNat + 4 ≤ G.get.size →
      ∃ fl', okState (execInstr (conc G.get r fl p ic)) =
        some (conc G.get (r' r (rdRaw G.get (fa r) 4)) fl' (p'' r (rdRaw G.get (fa r) 4)) ic)) :
    Steps E 1 p r F (p'' r (rdBytes E.M0 (fa r) 4)) (r' r (rdBytes E.M0 (fa r) 4)) F := by
  have h1 : (fa r).toNat = E.sp.toNat + (192 + 4 * k) := by
    rw [ha]; have := E.hsp; have := E.hsz; unfold ramTop at *; exact toNat_add_of_lt (by omega)
  have := E.hsp; have := E.ctx_sp
  exact Steps.one hp fun M fl ic hI => by
    obtain ⟨fl', h⟩ := hx (win hI hc) fl ic hI.ram (by rw [win_get, hI.size, h1]; omega)
    rw [win_get, hI.loadOut (by rw [h1]; omega) (fun i hi => by rw [h1]; unfold InSlots; omega)] at h
    exact ⟨M, fl', h, hI⟩

theorem Steps.congrEcx {E : Env} {n : Nat} {p p' : UInt32} {r r' : R} {F F' : Nat → UInt32}
    (h : Steps E n p r F p' r' F') (e : UInt32) (he : r'.ecx = e) : Steps E n p r F p' { r' with ecx := e } F' := by
  have : r' = { r' with ecx := e } := by cases r'; simp_all
  rw [← this]; exact h

theorem Steps.congrEdx {E : Env} {n : Nat} {p p' : UInt32} {r r' : R} {F F' : Nat → UInt32}
    (h : Steps E n p r F p' r' F') (e : UInt32) (he : r'.edx = e) : Steps E n p r F p' { r' with edx := e } F' := by
  have : r' = { r' with edx := e } := by cases r'; simp_all
  rw [← this]; exact h

/-- A segment from a chain, with the post slots given by a list. -/
theorem Seg.ofL {E : Env} {n : Nat} {p p' : UInt32} {Pr Qr : R → R} {Pf : (Nat → UInt32) → Nat → UInt32}
    {L : List (Nat × UInt32)}
    (h : ∀ r0 F0, ∃ r1 F1, Steps E n p (Pr r0) (Pf F0) p' r1 F1 ∧ r1 = Qr r1 ∧ AllEq F1 L) :
    Seg E n p Pr Pf p' Qr (fun F => updL F L) := by
  intro r0 F0
  obtain ⟨r1, F1, hs, hr, hf⟩ := h r0 F0
  exact ⟨r1, F1, (Steps.congrF hs (fun j _ => (updL_self F1 L hf j).symm)).congrR hr⟩

/-- A segment from a chain of steps: the final registers and slots are the post functions of
themselves. -/
theorem Seg.of {E : Env} {n : Nat} {p p' : UInt32} {Pr Qr : R → R} {Pf Qf : (Nat → UInt32) → Nat → UInt32}
    (h : ∀ r0 F0, ∃ r1 F1, Steps E n p (Pr r0) (Pf F0) p' r1 F1 ∧ r1 = Qr r1 ∧ ∀ j, j < 56 → F1 j = Qf F1 j) :
    Seg E n p Pr Pf p' Qr Qf := by
  intro r0 F0
  obtain ⟨r1, F1, hs, hr, hf⟩ := h r0 F0
  exact ⟨r1, F1, (Steps.congrF hs hf).congrR hr⟩

end Solutions.OpensslSha256
