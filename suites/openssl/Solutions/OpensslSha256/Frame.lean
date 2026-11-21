import Solutions.OpensslSha256.Cbv
import Solutions.Logic.Run
import Ssl.OpensslSha256.Statement
/-!
# Runs of `SHA256_Transform` on an abstract state

The machine of the call is described by the eight general registers (`R`), the arithmetic flags
(left free: only the two branches look at them), the instruction address, and 56 *slots*: the 48
stack words of the call (`[sp, sp + 192)`, `sp` the stack pointer inside the block function) and the
8 words of the hash context. `Inv E M F` says that memory `M` agrees with the caller's memory
`E.M0` outside the slots and holds `F j` in slot `j`.

`Steps E n p r F p' r' F'`: from every memory with invariant `F` at address `p` with registers
`r`, `n` steps run (through running states) to address `p'` with registers `r'` and a memory with
invariant `F'`. Steps compose (`Steps.trans`); one instruction is a step (`Steps.one`).
-/
namespace Solutions.OpensslSha256
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslSha256

/-- The general registers. -/
structure R where
  eax : UInt32
  ecx : UInt32
  edx : UInt32
  ebx : UInt32
  esp : UInt32
  ebp : UInt32
  esi : UInt32
  edi : UInt32

/-- The machine with memory `M`, registers `r`, arithmetic flags `fl`, at `p`. -/
def conc (M : ByteArray) (r : R) (fl p : UInt32) (ic : UInt64) : Machine :=
  St.m ⟨M, r.eax, r.ecx, r.edx, r.ebx, r.esp, r.ebp, r.esi, r.edi, p, efl fl, ic⟩

def imgBase : Nat := 0x100000
def imgSize : Nat := 4944

/-- The fixed facts of a call: the caller's memory `M0` holds the image, the stack frame
`[sp, sp + 204)` (the 48 slot words and the three words of the call) and the context
`[ctx, ctx + 32)` are inside memory, apart from each other and from the image; the 64 bytes of the
block `[blk, blk + 64)` are inside memory and apart from the frame, the context and the image. -/
structure Env where
  M0 : ByteArray
  sp : UInt32
  ctx : UInt32
  blk : UInt32
  hsz : M0.size ≤ ramTop
  himg : imgBase + imgSize ≤ M0.size
  hcode : ∀ i, i < imgSize → M0.get! (imgBase + i) = Image.byte i
  hsp : sp.toNat + 204 ≤ M0.size
  hctx : ctx.toNat + 32 ≤ M0.size
  hblk : blk.toNat + 64 ≤ M0.size
  sp_img : sp.toNat + 204 ≤ imgBase ∨ imgBase + imgSize ≤ sp.toNat
  ctx_img : ctx.toNat + 32 ≤ imgBase ∨ imgBase + imgSize ≤ ctx.toNat
  blk_img : blk.toNat + 64 ≤ imgBase ∨ imgBase + imgSize ≤ blk.toNat
  ctx_sp : ctx.toNat + 32 ≤ sp.toNat ∨ sp.toNat + 204 ≤ ctx.toNat
  blk_sp : blk.toNat + 64 ≤ sp.toNat ∨ sp.toNat + 204 ≤ blk.toNat
  blk_ctx : blk.toNat + 64 ≤ ctx.toNat ∨ ctx.toNat + 32 ≤ blk.toNat

/-- The address of slot `j`. -/
def slotAddr (E : Env) (j : Nat) : UInt32 :=
  if j < 48 then E.sp + (4 * j).toUInt32 else E.ctx + (4 * (j - 48)).toUInt32

/-- The slots' bytes. -/
def InSlots (E : Env) (a : Nat) : Prop :=
  (E.sp.toNat ≤ a ∧ a < E.sp.toNat + 192) ∨ (E.ctx.toNat ≤ a ∧ a < E.ctx.toNat + 32)

structure Inv (E : Env) (M : ByteArray) (F : Nat → UInt32) : Prop where
  size : M.size = E.M0.size
  out : ∀ a, a < E.M0.size → ¬ InSlots E a → M.get! a = E.M0.get! a
  slot : ∀ j, j < 56 → rdBytes M (slotAddr E j) 4 = F j

/-- `F` with slot `j` replaced by `v`. -/
def upd (F : Nat → UInt32) (j : Nat) (v : UInt32) : Nat → UInt32 := fun k => if k = j then v else F k

/-- The slots given by a list. -/
def mkF (L : List UInt32) : Nat → UInt32 := fun k => L.getD k 0

theorem slotAddr_toNat (E : Env) (j : Nat) (hj : j < 56) :
    (slotAddr E j).toNat = if j < 48 then E.sp.toNat + 4 * j else E.ctx.toNat + 4 * (j - 48) := by
  have h1 := E.hsp; have h2 := E.hctx; have h3 := E.hsz
  unfold slotAddr ramTop at *
  split
  · exact toNat_add_of_lt (by omega)
  · exact toNat_add_of_lt (by omega)

theorem slot_fits (E : Env) (j : Nat) (hj : j < 56) : (slotAddr E j).toNat + 4 ≤ E.M0.size := by
  rw [slotAddr_toNat E j hj]
  have h1 := E.hsp; have h2 := E.hctx
  split <;> omega

theorem slot_in (E : Env) (j : Nat) (hj : j < 56) (k : Nat) (hk : k < 4) :
    InSlots E ((slotAddr E j).toNat + k) := by
  rw [slotAddr_toNat E j hj]
  unfold InSlots
  split <;> omega

theorem slots_apart (E : Env) (j k : Nat) (hj : j < 56) (hk : k < 56) (hjk : j ≠ k) :
    (slotAddr E j).toNat + 4 ≤ (slotAddr E k).toNat ∨ (slotAddr E k).toNat + 4 ≤ (slotAddr E j).toNat := by
  rw [slotAddr_toNat E j hj, slotAddr_toNat E k hk]
  have := E.ctx_sp
  split <;> split <;> omega

/-! ## The invariant under loads and stores -/

theorem Inv.load {E : Env} {M : ByteArray} {F : Nat → UInt32} (hI : Inv E M F) {j : Nat} (hj : j < 56)
    {a : UInt32} (ha : a = slotAddr E j) : rdRaw M a 4 = F j := by
  subst ha; exact hI.slot j hj

theorem Inv.fits {E : Env} {M : ByteArray} {F : Nat → UInt32} (hI : Inv E M F) {j : Nat} (hj : j < 56)
    {a : UInt32} (ha : a = slotAddr E j) : a.toNat + 4 ≤ M.size := by
  subst ha; rw [hI.size]; exact slot_fits E j hj

theorem Inv.store {E : Env} {M : ByteArray} {F : Nat → UInt32} (hI : Inv E M F) {j : Nat} (hj : j < 56)
    {a : UInt32} (ha : a = slotAddr E j) (v : UInt32) : Inv E (wrBytes M a 4 v) (upd F j v) := by
  subst ha
  have hfit : (slotAddr E j).toNat + 4 ≤ M.size := by rw [hI.size]; exact slot_fits E j hj
  refine ⟨by rw [size_wrBytes]; exact hI.size, fun b hb hn => ?_, fun k hk => ?_⟩
  · rw [get!_wrBytes4 hfit]
    have hne : ∀ k, k < 4 → b ≠ (slotAddr E j).toNat + k := fun k hk h => hn (h ▸ slot_in E j hj k hk)
    rw [if_neg (by simpa using hne 0 (by decide)), if_neg (hne 1 (by decide)),
      if_neg (hne 2 (by decide)), if_neg (hne 3 (by decide))]
    exact hI.out b hb hn
  · unfold upd
    by_cases hkj : k = j
    · subst hkj; rw [if_pos rfl]; exact rdBytes4_wrBytes4_self hfit
    · rw [if_neg hkj, rdBytes4_wrBytes4_other hfit (by rw [hI.size]; exact slot_fits E k hk)
        (slots_apart E j k hj hk (Ne.symm hkj))]
      exact hI.slot k hk

/-- A load outside the slots reads the caller's memory. -/
theorem Inv.loadOut {E : Env} {M : ByteArray} {F : Nat → UInt32} (hI : Inv E M F) {a : UInt32}
    (hfit : a.toNat + 4 ≤ E.M0.size) (hout : ∀ k, k < 4 → ¬ InSlots E (a.toNat + k)) :
    rdRaw M a 4 = rdBytes E.M0 a 4 :=
  rdBytes4_congr (by rw [hI.size]; exact hfit) hfit
    (fun k hk => hI.out _ (by omega) (hout k hk))

/-! ## The code window -/

/-- The `n` bytes `code i` are the image bytes at `p`. -/
def CodeIn (p : UInt32) (n : Nat) (code : Nat → UInt8) : Prop :=
  imgBase ≤ p.toNat ∧ p.toNat + n ≤ imgBase + imgSize ∧ ∀ i, i < n → Image.byte (p.toNat - imgBase + i) = code i

instance (p : UInt32) (n : Nat) (code : Nat → UInt8) : Decidable (CodeIn p n code) := by
  unfold CodeIn; infer_instance

/-- The memory `M` as a code window at `p`. -/
def win {E : Env} {M : ByteArray} {F : Nat → UInt32} (hI : Inv E M F) {p : UInt32} {n : Nat}
    {code : Nat → UInt8} (hc : CodeIn p n code) : CodeMem p n code where
  mem := M
  fits := by have := E.himg; have := hc.2.1; rw [hI.size]; unfold imgBase imgSize at *; omega
  ok := fun i hi => by
    obtain ⟨h1, h2, h3⟩ := hc
    have hni : ¬ InSlots E (p.toNat + i) := by
      have := E.sp_img; have := E.ctx_img
      unfold InSlots imgBase imgSize at *; omega
    rw [hI.out _ (by have := E.himg; unfold imgBase imgSize at *; omega) hni]
    have := E.hcode (p.toNat - imgBase + i) (by unfold imgBase imgSize at *; omega)
    rw [show imgBase + (p.toNat - imgBase + i) = p.toNat + i by omega] at this
    rw [this, h3 i hi]

theorem win_get {E : Env} {M : ByteArray} {F : Nat → UInt32} (hI : Inv E M F) {p : UInt32} {n : Nat}
    {code : Nat → UInt8} (hc : CodeIn p n code) : (win hI hc).get = M := rfl

theorem Inv.ram {E : Env} {M : ByteArray} {F : Nat → UInt32} (hI : Inv E M F) : M.size ≤ ramTop := by
  rw [hI.size]; exact E.hsz

/-! ## Steps -/

def Steps (E : Env) (n : Nat) (p : UInt32) (r : R) (F : Nat → UInt32) (p' : UInt32) (r' : R)
    (F' : Nat → UInt32) : Prop :=
  ∀ (M : ByteArray) (fl : UInt32) (ic : UInt64), Inv E M F → ic.toNat + n < 2 ^ 64 →
    ∃ M' fl', Run img (conc M r fl p ic) (conc M' r' fl' p' (ic + n.toUInt64)) ∧ Inv E M' F'

theorem Steps.refl (E : Env) (p : UInt32) (r : R) (F : Nat → UInt32) : Steps E 0 p r F p r F :=
  fun M fl ic hI _ => ⟨M, fl, by simpa using Run.refl img _, hI⟩

theorem Steps.trans {E : Env} {n₁ n₂ : Nat} {p₁ p₂ p₃ : UInt32} {r₁ r₂ r₃ : R} {F₁ F₂ F₃ : Nat → UInt32}
    (h₁ : Steps E n₁ p₁ r₁ F₁ p₂ r₂ F₂) (h₂ : Steps E n₂ p₂ r₂ F₂ p₃ r₃ F₃) :
    Steps E (n₁ + n₂) p₁ r₁ F₁ p₃ r₃ F₃ := by
  intro M fl ic hI hic
  obtain ⟨M₁, fl₁, hr₁, hI₁⟩ := h₁ M fl ic hI (by omega)
  have hic₁ : (ic + n₁.toUInt64).toNat = ic.toNat + n₁ := by
    rw [UInt64.toNat_add]; simp; omega
  obtain ⟨M₂, fl₂, hr₂, hI₂⟩ := h₂ M₁ fl₁ (ic + n₁.toUInt64) hI₁ (by omega)
  refine ⟨M₂, fl₂, hr₁.trans ?_, hI₂⟩
  have : ic + n₁.toUInt64 + n₂.toUInt64 = ic + (n₁ + n₂).toUInt64 := by
    apply UInt64.toNat_inj.1
    simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  rw [← this]; exact hr₂

/-- Replace the slots by slots that agree on the 56 slots. -/
theorem Steps.congrF {E : Env} {n : Nat} {p p' : UInt32} {r r' : R} {F F' G : Nat → UInt32}
    (h : Steps E n p r F p' r' F') (hG : ∀ j, j < 56 → F' j = G j) : Steps E n p r F p' r' G := by
  intro M fl ic hI hic
  obtain ⟨M', fl', hr, hI'⟩ := h M fl ic hI hic
  exact ⟨M', fl', hr, ⟨hI'.size, hI'.out, fun j hj => (hI'.slot j hj).trans (hG j hj)⟩⟩

theorem Steps.congrF₀ {E : Env} {n : Nat} {p p' : UInt32} {r r' : R} {F G F' : Nat → UInt32}
    (h : Steps E n p r F p' r' F') (hG : ∀ j, j < 56 → G j = F j) : Steps E n p r G p' r' F' := by
  intro M fl ic hI hic
  exact h M fl ic ⟨hI.size, hI.out, fun j hj => (hI.slot j hj).trans (hG j hj)⟩ hic

theorem running_conc (M : ByteArray) (r : R) (fl p : UInt32) (ic : UInt64) (hp : p ≠ Image.sym_halt) :
    Running img (conc M r fl p ic) := by
  unfold Running returned
  have : (p == Image.sym_halt) = false := by simpa using hp
  simp [conc, St.m, img, this]

/-- One instruction, from its effect on `execInstr`. -/
theorem Steps.one {E : Env} {p p' : UInt32} {r r' : R} {F F' : Nat → UInt32} (hp : p ≠ Image.sym_halt)
    (h : ∀ M fl ic, Inv E M F → ∃ M' fl', okState (execInstr (conc M r fl p ic)) = some (conc M' r' fl' p' ic) ∧
      Inv E M' F') : Steps E 1 p r F p' r' F' := by
  intro M fl ic hI hic
  obtain ⟨M', fl', hx, hI'⟩ := h M fl ic hI
  refine ⟨M', fl', ?_, hI'⟩
  have hlt : ic < 0xFFFFFFFFFFFFFFFF := by rw [UInt64.lt_iff_toNat_lt]; simp; omega
  have hTF : (efl fl) &&& Flag.TF = 0 := efl_TF fl
  have := step_of_okState ⟨M, r.eax, r.ecx, r.edx, r.ebx, r.esp, r.ebp, r.esi, r.edi, p, efl fl, ic⟩ hlt hTF
    ⟨M', r'.eax, r'.ecx, r'.edx, r'.ebx, r'.esp, r'.ebp, r'.esi, r'.edi, p', efl fl', ic⟩ hx rfl
  exact Run.single (running_conc M r fl p ic hp) this

/-! ## Instructions by kind

Each takes the `cbv` lemma of the instruction's encoding (`hx`), for a code window at `p` and the
side conditions the encoding needs. -/

/-- No memory access. -/
theorem Steps.reg {E : Env} {p p' : UInt32} {n : Nat} {code : Nat → UInt8} {r r' : R} {F : Nat → UInt32}
    (hp : p ≠ Image.sym_halt) (hc : CodeIn p n code)
    (hx : ∀ (G : CodeMem p n code) fl ic, G.get.size ≤ ramTop →
      ∃ fl', okState (execInstr (conc G.get r fl p ic)) = some (conc G.get r' fl' p' ic)) :
    Steps E 1 p r F p' r' F :=
  Steps.one hp fun M fl ic hI => by
    obtain ⟨fl', h⟩ := hx (win hI hc) fl ic hI.ram
    exact ⟨M, fl', h, hI⟩

/-- A load from a slot (the loaded word goes through `g`). -/
theorem Steps.load {E : Env} {p p' : UInt32} {n : Nat} {code : Nat → UInt8} {r : R} {F : Nat → UInt32}
    (g : UInt32 → R) (a : UInt32) (j : Nat) (hj : j < 56) (ha : a = slotAddr E j)
    (hp : p ≠ Image.sym_halt) (hc : CodeIn p n code)
    (hx : ∀ (G : CodeMem p n code) fl ic, G.get.size ≤ ramTop → a.toNat + 4 ≤ G.get.size →
      ∃ fl', okState (execInstr (conc G.get r fl p ic)) = some (conc G.get (g (rdRaw G.get a 4)) fl' p' ic)) :
    Steps E 1 p r F p' (g (F j)) F :=
  Steps.one hp fun M fl ic hI => by
    obtain ⟨fl', h⟩ := hx (win hI hc) fl ic hI.ram (hI.fits hj ha)
    rw [win_get, hI.load hj ha] at h
    exact ⟨M, fl', h, hI⟩

/-- A store of `v` to a slot (`r'` may differ from `r` in the stack pointer). -/
theorem Steps.store {E : Env} {p p' : UInt32} {n : Nat} {code : Nat → UInt8} {r r' : R} {F : Nat → UInt32}
    (a v : UInt32) (j : Nat) (hj : j < 56) (ha : a = slotAddr E j)
    (hp : p ≠ Image.sym_halt) (hc : CodeIn p n code)
    (hx : ∀ (G : CodeMem p n code) fl ic, G.get.size ≤ ramTop → a.toNat + 4 ≤ G.get.size →
      ∃ fl', okState (execInstr (conc G.get r fl p ic)) = some (conc (wrBytes G.get a 4 v) r' fl' p' ic)) :
    Steps E 1 p r F p' r' (upd F j v) :=
  Steps.one hp fun M fl ic hI => by
    obtain ⟨fl', h⟩ := hx (win hI hc) fl ic hI.ram (hI.fits hj ha)
    exact ⟨_, fl', h, hI.store hj ha v⟩

/-- A read-modify-write of a slot. -/
theorem Steps.rmw {E : Env} {p p' : UInt32} {n : Nat} {code : Nat → UInt8} {r r' : R} {F : Nat → UInt32}
    (a : UInt32) (g : UInt32 → UInt32) (j : Nat) (hj : j < 56) (ha : a = slotAddr E j)
    (hp : p ≠ Image.sym_halt) (hc : CodeIn p n code)
    (hx : ∀ (G : CodeMem p n code) fl ic, G.get.size ≤ ramTop → a.toNat + 4 ≤ G.get.size →
      ∃ fl', okState (execInstr (conc G.get r fl p ic)) =
        some (conc (wrBytes G.get a 4 (g (rdRaw G.get a 4))) r' fl' p' ic)) :
    Steps E 1 p r F p' r' (upd F j (g (F j))) :=
  Steps.one hp fun M fl ic hI => by
    obtain ⟨fl', h⟩ := hx (win hI hc) fl ic hI.ram (hI.fits hj ha)
    rw [win_get, hI.load hj ha] at h
    exact ⟨_, fl', h, hI.store hj ha _⟩

/-- A load outside the slots: the caller's memory. -/
theorem Steps.loadOut {E : Env} {p p' : UInt32} {n : Nat} {code : Nat → UInt8} {r : R} {F : Nat → UInt32}
    (g : UInt32 → R) (a : UInt32) (hfit : a.toNat + 4 ≤ E.M0.size)
    (hout : ∀ k, k < 4 → ¬ InSlots E (a.toNat + k))
    (hp : p ≠ Image.sym_halt) (hc : CodeIn p n code)
    (hx : ∀ (G : CodeMem p n code) fl ic, G.get.size ≤ ramTop → a.toNat + 4 ≤ G.get.size →
      ∃ fl', okState (execInstr (conc G.get r fl p ic)) = some (conc G.get (g (rdRaw G.get a 4)) fl' p' ic)) :
    Steps E 1 p r F p' (g (rdBytes E.M0 a 4)) F :=
  Steps.one hp fun M fl ic hI => by
    obtain ⟨fl', h⟩ := hx (win hI hc) fl ic hI.ram (by rw [win_get, hI.size]; exact hfit)
    rw [win_get, hI.loadOut hfit hout] at h
    exact ⟨M, fl', h, hI⟩

end Solutions.OpensslSha256
