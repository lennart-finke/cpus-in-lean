import Solutions.OpensslPoly1305.Mem
import Solutions.OpensslX25519.Pair
/-!
# From a harness call to a `MemOK` run, and back to `Returns`

`stk c` is the lowest address of the call's stack bytes (`c.sp - 256`); the stack region of a call
with `n` arguments is `[stk c, stk c + 256 + 4 (n + 1))` (the callee's 256 bytes, the return address,
the arguments). `word_at` reads a stack word of the call; `returns_of` turns a run to the return
address (with the memory described by `Pres` and the words of the argument area unchanged) into
the harness's `Returns`.
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305

set_option autoImplicit false

/-- The memory of a call of the image. -/
def pmem {c : Caller} {stack : Nat} {args : List UInt32} (h : Calls img c stack args) : PMem :=
  callMem (byte := Image.byte) rfl h

theorem pmem_get {c : Caller} {stack : Nat} {args : List UInt32} (h : Calls img c stack args) :
    (pmem h).get = c.mem := rfl

def stk (c : Caller) : UInt32 := c.sp - 256

theorem stk_toNat {c : Caller} (h : 256 ≤ c.sp.toNat) : (stk c).toNat = c.sp.toNat - 256 := by
  unfold stk
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
  simp

theorem sp_eq {c : Caller} (h : 256 ≤ c.sp.toNat) : c.sp = UInt32.add (stk c) 256 := by
  apply UInt32.toNat_inj.1
  rw [toNat_uadd, stk_toNat h]
  have := c.sp.toNat_lt; simp; omega

theorem apart_nat {a : UInt32} {n : Nat} {b : UInt32} {k : Nat} (h : Apart a n b k) (hn : n ≠ 0)
    (hk : k ≠ 0) : a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat := by
  rcases h with h | h | h <;> omega

/-- The address facts of a call with `n` arguments. -/
theorem calls_facts {c : Caller} {args : List UInt32} (hc : Calls img c stackBound args) :
    c.mem.size ≤ ramTop ∧ 0x100000 + 1536 ≤ c.mem.size ∧ 256 ≤ c.sp.toNat ∧
      c.sp.toNat + 4 * (args.length + 1) ≤ c.mem.size ∧
      (c.sp.toNat + 4 * (args.length + 1) ≤ 0x100000 ∨ 0x100000 + 1536 ≤ c.sp.toNat - 256) := by
  obtain ⟨h1, h2, -, -, h5, h6, h7⟩ := hc
  have hs : stackBound = 256 := rfl
  rw [hs] at h5 h7
  have := apart_nat h7 (by simp [stackSize]) (by rw [img_size]; decide)
  rw [img_size, img_base] at this h2
  have hlo : (c.stackLo 256).toNat = c.sp.toNat - 256 := stk_toNat h5
  rw [hlo] at this
  simp only [stackSize] at this
  exact ⟨h1, by omega, h5, h6, by omega⟩

/-- The facts of a buffer argument. -/
theorem buffer_facts {c : Caller} {args : List UInt32} {p : UInt32} {n : Nat} (hc : Calls img c stackBound args)
    (hb : Buffer img c stackBound args.length p n) (hn : n ≠ 0) :
    p.toNat + n ≤ c.mem.size ∧ (p.toNat + n ≤ 0x100000 ∨ 0x100000 + 1536 ≤ p.toNat) ∧
      (p.toNat + n ≤ c.sp.toNat - 256 ∨ c.sp.toNat + 4 * (args.length + 1) ≤ p.toNat) := by
  obtain ⟨hfit, -, hai, has⟩ := hb
  have h5 : 256 ≤ c.sp.toNat := hc.2.2.2.2.1
  have hlo : (c.stackLo 256).toNat = c.sp.toNat - 256 := stk_toNat h5
  refine ⟨by rcases hfit with h | h <;> omega, ?_, ?_⟩
  · have := apart_nat hai hn (by rw [img_size]; decide)
    rw [img_size, img_base] at this; exact this
  · have := apart_nat has hn (by simp [stackSize])
    rw [show stackBound = 256 from rfl, hlo] at this
    simp only [stackSize] at this
    omega

/-- The return address on the call's stack. -/
theorem word_ret {c : Caller} {args : List UInt32} (hc : Calls img c stackBound args) :
    rdRaw c.mem (UInt32.add (stk c) 256) 4 = img.halt := by
  rw [← sp_eq (calls_facts hc).2.2.1]; exact calls_ret hc

/-- The `i`-th argument on the call's stack, at offset `k = 260 + 4 i` from `stk c`. -/
theorem word_arg {c : Caller} {args : List UInt32} (hc : Calls img c stackBound args) (i : Nat)
    (hi : i < args.length) (k : UInt32) (hk : k.toNat = 260 + 4 * i) :
    rdRaw c.mem (UInt32.add (stk c) k) 4 = args[i] := by
  have hf := calls_facts hc
  have e : UInt32.add (stk c) k = c.sp + 4 * (i + 1).toUInt32 := by
    apply UInt32.toNat_inj.1
    rw [toNat_uadd, stk_toNat hf.2.2.1, hk, UInt32.toNat_add, UInt32.toNat_mul]
    simp only [Nat.toUInt32, UInt32.toNat_ofNat']
    have := c.sp.toNat_lt
    unfold ramTop at hf
    rw [Nat.mod_eq_of_lt (a := i + 1) (by omega)]
    simp; omega
  rw [e]; exact calls_arg hc i hi

/-! ## Words and bytes -/

theorem or_high' (x k i : Nat) (hx : x < 2 ^ i) : x ||| k * 2 ^ i = x + k * 2 ^ i :=
  Solutions.OpensslX25519.or_high x k i hx

theorem rd4_toNat {mem : ByteArray} {a : UInt32} (h : a.toNat + 4 ≤ mem.size) :
    (rdBytes mem a 4).toNat = (mem.get! a.toNat).toNat + 2 ^ 8 * (mem.get! (a.toNat + 1)).toNat +
      2 ^ 16 * (mem.get! (a.toNat + 2)).toNat + 2 ^ 24 * (mem.get! (a.toNat + 3)).toNat := by
  rw [rdBytes4_eq h]
  have b0 := (mem.get! a.toNat).toNat_lt
  have b1 := (mem.get! (a.toNat + 1)).toNat_lt
  have b2 := (mem.get! (a.toNat + 2)).toNat_lt
  have b3 := (mem.get! (a.toNat + 3)).toNat_lt
  simp only [shl32, UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32]
  simp only [show (8 : UInt32).toNat % 32 = 8 from rfl, show (16 : UInt32).toNat % 32 = 16 from rfl,
    show (24 : UInt32).toNat % 32 = 24 from rfl, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega : (mem.get! (a.toNat + 1)).toNat * 2 ^ 8 < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : (mem.get! (a.toNat + 2)).toNat * 2 ^ 16 < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : (mem.get! (a.toNat + 3)).toNat * 2 ^ 24 < 2 ^ 32)]
  rw [or_high' _ _ 8 (by omega), or_high' _ _ 16 (by omega), or_high' _ _ 24 (by omega)]
  omega

/-- Equal words have equal bytes. -/
theorem bytes_of_word {m1 m2 : ByteArray} {a : UInt32} (h1 : a.toNat + 4 ≤ m1.size) (h2 : a.toNat + 4 ≤ m2.size)
    (htop : m1.size ≤ ramTop) (e : rdBytes m1 a 4 = rdBytes m2 a 4) (j : Nat) (hj : j < 4) :
    memByte m1 (a + j.toUInt32) = memByte m2 (a + j.toUInt32) := by
  have ea := congrArg UInt32.toNat e
  rw [rd4_toNat h1, rd4_toNat h2] at ea
  have hb : (a + j.toUInt32).toNat = a.toNat + j := by
    rw [UInt32.toNat_add, Nat.toUInt32, UInt32.toNat_ofNat']; unfold ramTop at htop; omega
  rw [memByte_def (by rw [hb]; omega), memByte_def (by rw [hb]; omega), hb]
  have c0 := (m1.get! a.toNat).toNat_lt; have c1 := (m1.get! (a.toNat + 1)).toNat_lt
  have c2 := (m1.get! (a.toNat + 2)).toNat_lt; have c3 := (m1.get! (a.toNat + 3)).toNat_lt
  have d0 := (m2.get! a.toNat).toNat_lt; have d1 := (m2.get! (a.toNat + 1)).toNat_lt
  have d2 := (m2.get! (a.toNat + 2)).toNat_lt; have d3 := (m2.get! (a.toNat + 3)).toNat_lt
  apply UInt8.toNat_inj.1
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> (try simp only [Nat.add_zero]) <;>
    omega

/-- The argument area of a call is unchanged when its words are. -/
theorem arg_bytes {c : Caller} {args : List UInt32} (hc : Calls img c stackBound args) {N : PMem}
    (hs : N.get.size = c.mem.size)
    (hw : ∀ i, i < args.length + 1 → rdRaw N.get (UInt32.add (stk c) (256 + 4 * i).toUInt32) 4 =
      rdRaw c.mem (UInt32.add (stk c) (256 + 4 * i).toUInt32) 4) :
    ∀ a : UInt32, c.sp.toNat ≤ a.toNat → a.toNat < c.sp.toNat + 4 * (args.length + 1) →
      memByte N.get a = memByte c.mem a := by
  intro a h1 h2
  have hf := calls_facts hc
  have hst := stk_toNat hf.2.2.1
  obtain ⟨i, j, hi, hj, ha⟩ : ∃ i j, i < args.length + 1 ∧ j < 4 ∧ a.toNat = c.sp.toNat + 4 * i + j :=
    ⟨(a.toNat - c.sp.toNat) / 4, (a.toNat - c.sp.toNat) % 4, by omega, by omega, by omega⟩
  have hb : (UInt32.add (stk c) (256 + 4 * i).toUInt32).toNat = c.sp.toNat + 4 * i := by
    rw [toNat_uadd, hst]; simp only [Nat.toUInt32, UInt32.toNat_ofNat']; unfold ramTop at hf
    rw [Nat.mod_eq_of_lt (a := 256 + 4 * i) (by omega)]; omega
  have e : a = UInt32.add (stk c) (256 + 4 * i).toUInt32 + j.toUInt32 := by
    apply UInt32.toNat_inj.1
    rw [UInt32.toNat_add, hb, Nat.toUInt32, UInt32.toNat_ofNat']; unfold ramTop at hf; omega
  rw [e]
  exact bytes_of_word (by rw [hs, hb]; omega) (by rw [hb]; omega) (by rw [hs]; exact hf.1) (hw i hi) j hj

/-- A run of a call to its return address, with the callee-saved registers, the memory described by
`MemOK` and the argument area unchanged, is the harness's `Returns`. -/
theorem returns_of {c : Caller} {args : List UInt32} (hc : Calls img c stackBound args) (fn : UInt32)
    {N : PMem} {lU lC : List (Nat × UInt32)} {C : UInt32} {nC mC : Nat} {P : Nat → Prop}
    {W : UInt32 → Prop} {Q : Machine → Prop}
    (hM : MemOK (pmem hc) N (stk c) (256 + 4 * (args.length + 1)) lU C nC mC lC P)
    (hP : ∀ a : UInt32, ¬ W a → (a.toNat < c.sp.toNat - 256 ∨ c.sp.toNat + 4 * (args.length + 1) ≤ a.toNat) →
      P a.toNat)
    (hArg : ∀ a : UInt32, c.sp.toNat ≤ a.toNat → a.toNat < c.sp.toNat + 4 * (args.length + 1) →
      memByte N.get a = memByte c.mem a)
    {eax ecx edx gf : UInt32} {ic : UInt64}
    (hR : Run img (c.enter fn) (St.m ⟨N.get, eax, ecx, edx, c.regs.ebx, UInt32.add (stk c) 260, c.regs.ebp,
      c.regs.esi, c.regs.edi, Image.sym_halt, efl gf, ic⟩))
    (hQ : Q (St.m ⟨N.get, eax, ecx, edx, c.regs.ebx, UInt32.add (stk c) 260, c.regs.ebp,
      c.regs.esi, c.regs.edi, Image.sym_halt, efl gf, ic⟩)) :
    Returns img (c.enter fn) stackBound W Q := by
  have hf := calls_facts hc
  have hst := stk_toNat hf.2.2.1
  refine Returns.intro hR ⟨?_, ?_, efl_DF gf⟩ ⟨rfl, rfl, rfl, rfl⟩ ⟨hM.size, ?_⟩ hQ
  · rfl
  · show UInt32.add (stk c) 260 = c.sp + 4
    apply UInt32.toNat_inj.1
    rw [toNat_uadd, hst, UInt32.toNat_add]; unfold ramTop at hf; simp; omega
  · intro a ha hW hS
    show memByte N.get a = memByte c.mem a
    have hS' : ¬ (c.sp.toNat - 256 ≤ a.toNat ∧ a.toNat < c.sp.toNat - 256 + 256) := by
      intro h; apply hS
      show (c.sp - (256 : Nat).toUInt32) ≤ a ∧ a.toNat < (c.sp - (256 : Nat).toUInt32).toNat + 256
      have := stk_toNat (c := c) hf.2.2.1
      unfold stk at this
      rw [UInt32.le_iff_toNat_le, show ((256 : Nat).toUInt32) = 256 from rfl, this]; omega
    by_cases hin : c.sp.toNat ≤ a.toNat ∧ a.toNat < c.sp.toNat + 4 * (args.length + 1)
    · exact hArg a hin.1 hin.2
    · exact hM.pres.2 a ha (hP a hW (by omega))

end Solutions.OpensslPoly1305
