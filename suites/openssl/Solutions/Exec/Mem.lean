import Solutions.Logic.Mem
import Solutions.Exec.Simprocs
/-!
# Data accesses of a flat machine

For a machine whose paging, nested paging and breakpoints are off and whose devices are where the
harness puts them (`FlatM`), a linear read or write of 1, 2 or 4 bytes inside memory and below the
I/O APIC page is a plain `rdBytes`/`wrBytes` of `mem`, whether or not it crosses a page boundary
(`linRd_flat`, `linWr_flat`). `rdMem_flat`/`wrMem_flat` add the segment checks of a flat data
segment at CPL 0.

`ramTop` is the address of the I/O APIC page (`X86.ioApicBase`): every address below it is RAM in
the model. It is the harness's `Ssl.ramLimit`.
-/
namespace Solutions.Exec
open X86 Solutions.Logic

/-- Below this address every access reaches `Machine.mem`: the I/O APIC page starts here. -/
def ramTop : Nat := 0xFEC00000

/-- The parts of a machine that a data access looks at, as the harness sets them. -/
def FlatM (m : Machine) : Prop :=
  m.cpu.cr0 &&& CR0.PG = 0 ∧ m.cpu.npOn = false ∧ m.cpu.bpOn = false ∧ m.tso = none ∧
  m.apic.mmio = 0xFEE00000 ∧ m.watch = #[]

theorem bind_ok {α β : Type} {x : M α} {f : α → M β} {m m' : Machine} {a : α} (h : x m = .ok a m') :
    EStateM.bind x f m = f a m' := by
  simp only [EStateM.bind, h]

theorem dbData_flat {m : Machine} (h : m.cpu.bpOn = false) (lin n : UInt32) (w : Bool) :
    dbData lin n w m = .ok () m := by
  simp [dbData, h]

theorem translate_flat {m : Machine} (h : FlatM m) (lin : UInt32) (w u f i : Bool) :
    translate lin w u f i m = .ok lin.toUInt64 m := by
  obtain ⟨hpg, hnp, -⟩ := h
  simp [translate, hpg, hnp]

theorem notMmio_of_lt {m : Machine} (h : FlatM m) {a : UInt32} (ha : a.toNat < ramTop) :
    isMmio m a = false := by
  obtain ⟨-, -, -, -, hap, -⟩ := h
  simp only [isMmio, isApic, hap, ioApicBase, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  have hle : (a &&& 0xFFFFF000).toNat ≤ a.toNat := by
    rw [UInt32.toNat_and]; exact Nat.and_le_left
  constructor <;> intro he <;> rw [he] at hle <;> simp [ramTop] at hle ha <;> omega

theorem physRd_flat {m : Machine} (h : FlatM m) {a : UInt32} (ha : a.toNat < ramTop) (n : UInt32) :
    physRd a.toUInt64 n m = .ok (rdBytes m.mem a n) m := by
  have hm := notMmio_of_lt h ha
  obtain ⟨-, -, -, ht, -⟩ := h
  have h32 : ShiftRight.shiftRight a.toUInt64 32 = 0 := by
    have h := UInt64.toNat_shiftRight a.toUInt64 32
    apply UInt64.toNat_inj.1
    refine h.trans ?_
    have := a.toNat_lt
    simp only [UInt32.toNat_toUInt64, UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    rw [Nat.div_eq_of_lt (by omega)]
  simp [physRd, h32, hm, ht]

/-- An address is its page plus its offset in the page. -/
theorem page_add_off (a : UInt32) :
    (a &&& 0xFFFFF000).toNat + (a &&& 0xFFF).toNat = a.toNat := by
  have hbv : (a &&& 0xFFFFF000) + (a &&& 0xFFF) = a := by
    apply UInt32.toBitVec_inj.1
    simp only [UInt32.toBitVec_add, UInt32.toBitVec_and]
    rw [BitVec.add_eq_or_of_and_eq_zero]
    · rw [← BitVec.and_or_distrib_left]
      have : (0xFFFFF000 : UInt32).toBitVec ||| (0xFFF : UInt32).toBitVec = BitVec.allOnes 32 := by decide
      rw [this, BitVec.and_allOnes]
    · have : (0xFFFFF000 : UInt32).toBitVec &&& (0xFFF : UInt32).toBitVec = 0#32 := by decide
      rw [show a.toBitVec &&& (0xFFFFF000 : UInt32).toBitVec &&& (a.toBitVec &&& (0xFFF : UInt32).toBitVec) =
          a.toBitVec &&& ((0xFFFFF000 : UInt32).toBitVec &&& (0xFFF : UInt32).toBitVec) by ac_rfl, this]
      simp
  have h1 : (a &&& 0xFFFFF000).toNat ≤ 0xFFFFF000 := by
    rw [UInt32.toNat_and]; exact Nat.and_le_right
  have h2 : (a &&& 0xFFF).toNat ≤ 0xFFF := by
    rw [UInt32.toNat_and]; exact Nat.and_le_right
  have := congrArg UInt32.toNat hbv
  rw [UInt32.toNat_add] at this
  rw [Nat.mod_eq_of_lt (by omega)] at this
  exact this

/-- The physical address `linRd`/`linWr` compute for the byte `lin + k` of a page-crossing access
is `lin + k` (no paging). -/
theorem crossAddr {lin k : UInt32} {n : UInt32} (hk : lin.toNat + k.toNat < 2 ^ 32) :
    (if (lin + k &&& 0xFFFFF000 == (lin + n - 1) &&& 0xFFFFF000) = true then
        ((lin + n - 1) &&& 0xFFFFF000).toUInt64 + (lin + k &&& 0xFFF).toUInt64
      else lin.toUInt64 + (lin + k - lin).toUInt64) = (lin + k).toUInt64 := by
  split
  · rename_i hc
    have hc := eq_of_beq hc
    rw [← hc]
    apply UInt64.toNat_inj.1
    have := page_add_off (lin + k)
    have := (lin + k &&& 4294963200).toNat_lt
    have := (lin + k &&& 4095).toNat_lt
    simp only [UInt64.toNat_add, UInt32.toNat_toUInt64]
    omega
  · apply UInt64.toNat_inj.1
    have hk' : (lin + k).toNat = lin.toNat + k.toNat := by
      rw [UInt32.toNat_add, Nat.mod_eq_of_lt hk]
    have : (lin + k - lin) = k := by
      apply UInt32.toNat_inj.1
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega), hk']; omega
    rw [this]
    simp only [UInt64.toNat_add, UInt32.toNat_toUInt64, hk']
    omega

theorem rdLoop2 {m : Machine} {P : Nat → UInt64} {B : Nat → UInt32}
    (h0 : physRd (P 0) 1 m = .ok (B 0) m) (h1 : physRd (P 1) 1 m = .ok (B 1) m) :
    EStateM.bind (forIn [:UInt32.toNat 2] (0 : UInt32) fun k s =>
        EStateM.bind (physRd (P k) 1) fun b => pure (ForInStep.yield (s ||| ShiftLeft.shiftLeft b (k.toUInt32 * 8))))
      (fun s => pure s) m = .ok (ShiftLeft.shiftLeft (B 0) 0 ||| ShiftLeft.shiftLeft (B 1) 8) m := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp [List.range', List.forIn_cons, List.forIn_nil, Std.Legacy.Range.size]
  simp only [bind, EStateM.bind, pure, EStateM.pure, h0, h1]

theorem rdLoop4 {m : Machine} {P : Nat → UInt64} {B : Nat → UInt32}
    (h0 : physRd (P 0) 1 m = .ok (B 0) m) (h1 : physRd (P 1) 1 m = .ok (B 1) m)
    (h2 : physRd (P 2) 1 m = .ok (B 2) m) (h3 : physRd (P 3) 1 m = .ok (B 3) m) :
    EStateM.bind (forIn [:UInt32.toNat 4] (0 : UInt32) fun k s =>
        EStateM.bind (physRd (P k) 1) fun b => pure (ForInStep.yield (s ||| ShiftLeft.shiftLeft b (k.toUInt32 * 8))))
      (fun s => pure s) m = .ok (ShiftLeft.shiftLeft (B 0) 0 ||| ShiftLeft.shiftLeft (B 1) 8 ||| ShiftLeft.shiftLeft (B 2) 16 |||
        ShiftLeft.shiftLeft (B 3) 24) m := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp [List.range', List.forIn_cons, List.forIn_nil, Std.Legacy.Range.size]
  simp only [bind, EStateM.bind, pure, EStateM.pure, h0, h1, h2, h3]

theorem shl0 (x : UInt32) : ShiftLeft.shiftLeft x (0 : UInt32) = x := UInt32.shiftLeft_zero

theorem rdBytes1_get {mem : ByteArray} {a : UInt32} (h : a.toNat < mem.size) :
    rdBytes mem a 1 = (mem.get! a.toNat).toUInt32 := by
  unfold rdBytes
  rw [if_pos (c := _) (by simp; omega)]
  rfl

theorem toNat_add_k {a : UInt32} {k : Nat} (hk : k < 2 ^ 32) (h : a.toNat + k < 2 ^ 32) :
    (a + k.toUInt32).toNat = a.toNat + k := by
  rw [UInt32.toNat_add]
  simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']
  rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt h]

/-- The byte reads of a page-crossing 2-byte load assemble the 2-byte load. -/
theorem rd2_join {mem : ByteArray} {a : UInt32} (h : a.toNat + 2 ≤ mem.size) (hs : mem.size ≤ ramTop) :
    ShiftLeft.shiftLeft (rdBytes mem (a + (0 : Nat).toUInt32) 1) 0 |||
      ShiftLeft.shiftLeft (rdBytes mem (a + (1 : Nat).toUInt32) 1) 8 = rdBytes mem a 2 := by
  have h0 := toNat_add_k (a := a) (k := 0) (by decide) (by simp [ramTop] at *; omega)
  have h1 := toNat_add_k (a := a) (k := 1) (by decide) (by simp [ramTop] at *; omega)
  rw [rdBytes1_get (by omega), rdBytes1_get (by omega), h0, h1]
  unfold rdBytes
  rw [if_pos (c := _) (by simp; omega)]
  simp only [Nat.add_zero, shl0]
  rfl

/-- The byte reads of a page-crossing 4-byte load assemble the 4-byte load. -/
theorem rd4_join {mem : ByteArray} {a : UInt32} (h : a.toNat + 4 ≤ mem.size) (hs : mem.size ≤ ramTop) :
    ShiftLeft.shiftLeft (rdBytes mem (a + (0 : Nat).toUInt32) 1) 0 |||
      ShiftLeft.shiftLeft (rdBytes mem (a + (1 : Nat).toUInt32) 1) 8 |||
      ShiftLeft.shiftLeft (rdBytes mem (a + (2 : Nat).toUInt32) 1) 16 |||
      ShiftLeft.shiftLeft (rdBytes mem (a + (3 : Nat).toUInt32) 1) 24 = rdBytes mem a 4 := by
  have h0 := toNat_add_k (a := a) (k := 0) (by decide) (by simp [ramTop] at *; omega)
  have h1 := toNat_add_k (a := a) (k := 1) (by decide) (by simp [ramTop] at *; omega)
  have h2 := toNat_add_k (a := a) (k := 2) (by decide) (by simp [ramTop] at *; omega)
  have h3 := toNat_add_k (a := a) (k := 3) (by decide) (by simp [ramTop] at *; omega)
  rw [rdBytes1_get (by omega), rdBytes1_get (by omega), rdBytes1_get (by omega), rdBytes1_get (by omega),
    h0, h1, h2, h3]
  unfold rdBytes
  rw [if_pos (c := _) (by simp; omega)]
  simp only [Nat.add_zero, shl0]
  rfl

theorem physRd_cross {m : Machine} (h : FlatM m) {lin n : UInt32} (k : Nat) (hk : k < n.toNat)
    (hr : lin.toNat + n.toNat ≤ m.mem.size) (hm : m.mem.size ≤ ramTop) :
    physRd (if (lin + k.toUInt32 &&& 0xFFFFF000 == (lin + n - 1) &&& 0xFFFFF000) = true then
        ((lin + n - 1) &&& 0xFFFFF000).toUInt64 + (lin + k.toUInt32 &&& 0xFFF).toUInt64
      else lin.toUInt64 + (lin + k.toUInt32 - lin).toUInt64) 1 m =
      .ok (rdBytes m.mem (lin + k.toUInt32) 1) m := by
  have hk32 : k < 2 ^ 32 := by have := n.toNat_lt; omega
  have hkk : (k.toUInt32).toNat = k := by simp; omega
  rw [crossAddr (by simp [ramTop] at hm; omega)]
  apply physRd_flat h
  rw [toNat_add_k hk32 (by simp [ramTop] at hm; omega)]
  omega

theorem linRdCross2 {m : Machine} (h : FlatM m) {lin : UInt32}
    (hr : lin.toNat + UInt32.toNat 2 ≤ m.mem.size) (hm : m.mem.size ≤ ramTop) :
    EStateM.bind (forIn [:UInt32.toNat 2] (0 : UInt32) fun k s =>
        EStateM.bind (physRd (if (lin + k.toUInt32 &&& 4294963200 == lin + 2 - 1 &&& 4294963200) = true then
      (lin + 2 - 1 &&& 4294963200).toUInt64 + (lin + k.toUInt32 &&& 4095).toUInt64
    else lin.toUInt64 + (lin + k.toUInt32 - lin).toUInt64) 1) fun b =>
          pure (ForInStep.yield (s ||| ShiftLeft.shiftLeft b (k.toUInt32 * 8))))
      (fun s => pure s) m = .ok (rdBytes m.mem lin 2) m := by
  have := rdLoop2 (m := m) (P := fun k => if (lin + k.toUInt32 &&& 4294963200 == lin + 2 - 1 &&& 4294963200) = true then
      (lin + 2 - 1 &&& 4294963200).toUInt64 + (lin + k.toUInt32 &&& 4095).toUInt64
    else lin.toUInt64 + (lin + k.toUInt32 - lin).toUInt64)
    (B := fun k => rdBytes m.mem (lin + k.toUInt32) 1) (physRd_cross (n := 2) h 0 (by decide) hr hm) (physRd_cross (n := 2) h 1 (by decide) hr hm)
  rw [rd2_join hr hm] at this
  exact this

theorem linRdCross4 {m : Machine} (h : FlatM m) {lin : UInt32}
    (hr : lin.toNat + UInt32.toNat 4 ≤ m.mem.size) (hm : m.mem.size ≤ ramTop) :
    EStateM.bind (forIn [:UInt32.toNat 4] (0 : UInt32) fun k s =>
        EStateM.bind (physRd (if (lin + k.toUInt32 &&& 4294963200 == lin + 4 - 1 &&& 4294963200) = true then
      (lin + 4 - 1 &&& 4294963200).toUInt64 + (lin + k.toUInt32 &&& 4095).toUInt64
    else lin.toUInt64 + (lin + k.toUInt32 - lin).toUInt64) 1) fun b =>
          pure (ForInStep.yield (s ||| ShiftLeft.shiftLeft b (k.toUInt32 * 8))))
      (fun s => pure s) m = .ok (rdBytes m.mem lin 4) m := by
  have := rdLoop4 (m := m) (P := fun k => if (lin + k.toUInt32 &&& 4294963200 == lin + 4 - 1 &&& 4294963200) = true then
      (lin + 4 - 1 &&& 4294963200).toUInt64 + (lin + k.toUInt32 &&& 4095).toUInt64
    else lin.toUInt64 + (lin + k.toUInt32 - lin).toUInt64)
    (B := fun k => rdBytes m.mem (lin + k.toUInt32) 1) (physRd_cross (n := 4) h 0 (by decide) hr hm) (physRd_cross (n := 4) h 1 (by decide) hr hm) (physRd_cross (n := 4) h 2 (by decide) hr hm) (physRd_cross (n := 4) h 3 (by decide) hr hm)
  rw [rd4_join hr hm] at this
  exact this

theorem linRd_flat {m : Machine} (h : FlatM m) {lin n : UInt32} (hn : n = 1 ∨ n = 2 ∨ n = 4)
    (hr : lin.toNat + n.toNat ≤ m.mem.size) (hm : m.mem.size ≤ ramTop) (u w i : Bool) :
    linRd lin n u w i m = .ok (rdBytes m.mem lin n) m := by
  have hbp := h.2.2.1
  have hn1 : 1 ≤ n.toNat := by rcases hn with rfl | rfl | rfl <;> decide
  unfold linRd
  simp only [bind, EStateM.bind, dbData_flat hbp]
  split
  · rw [bind_ok (translate_flat h _ _ _ _ _)]
    exact physRd_flat h (by omega) n
  · rename_i hc
    rcases hn with rfl | rfl | rfl
    · exfalso; apply hc
      have : lin.toNat &&& 4095 ≤ 4095 := Nat.and_le_right
      rw [UInt32.le_iff_toNat_le, UInt32.toNat_add, Nat.mod_eq_of_lt (by simp; omega)]
      simp; omega
    · rw [bind_ok (translate_flat h _ _ _ _ _), bind_ok (translate_flat h _ _ _ _ _)]
      exact linRdCross2 h hr hm
    · rw [bind_ok (translate_flat h _ _ _ _ _), bind_ok (translate_flat h _ _ _ _ _)]
      exact linRdCross4 h hr hm

theorem physWr_flat {m : Machine} (h : FlatM m) {a : UInt32} (ha : a.toNat < ramTop) (n v : UInt32) :
    physWr a.toUInt64 n v m = .ok () { m with mem := wrBytes m.mem a n v } := by
  have hm := notMmio_of_lt h ha
  obtain ⟨-, -, -, ht, -, hw⟩ := h
  have h32 : ShiftRight.shiftRight a.toUInt64 32 = 0 := by
    have h := UInt64.toNat_shiftRight a.toUInt64 32
    apply UInt64.toNat_inj.1
    refine h.trans ?_
    have := a.toNat_lt
    simp only [UInt32.toNat_toUInt64, UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    rw [Nat.div_eq_of_lt (by omega)]
  simp [physWr, h32, hm, ht, hw]

theorem FlatM.mem_iter {m : Machine} (h : FlatM m) {mem : ByteArray} : FlatM { m with mem := mem } := h

/-- `wrBytes` keeps the size of memory. -/
theorem size_wrBytes (mem : ByteArray) (a n v : UInt32) : (wrBytes mem a n v).size = mem.size := by
  unfold wrBytes
  simp only
  split
  · split
    · exact Solutions.Logic.ByteArray.size_set! _ _ _
    · split
      · simp [Solutions.Logic.ByteArray.size_set!]
      · simp [Solutions.Logic.ByteArray.size_set!]
  · suffices ∀ k (b : ByteArray), (wrBytes.go v a.toNat k b).size = b.size from this _ _
    intro k
    induction k with
    | zero => intro b; rfl
    | succ k ih =>
      intro b
      simp only [wrBytes.go]
      rw [ih]
      split <;> simp [Solutions.Logic.ByteArray.size_set!]

theorem physWr_cross {m : Machine} (h : FlatM m) {lin n : UInt32} (k : Nat) (hk : k < n.toNat)
    (hr : lin.toNat + n.toNat ≤ m.mem.size) (hm : m.mem.size ≤ ramTop) (x : UInt32) :
    physWr (if (lin + k.toUInt32 &&& 0xFFFFF000 == (lin + n - 1) &&& 0xFFFFF000) = true then
        ((lin + n - 1) &&& 0xFFFFF000).toUInt64 + (lin + k.toUInt32 &&& 0xFFF).toUInt64
      else lin.toUInt64 + (lin + k.toUInt32 - lin).toUInt64) 1 x m =
      .ok () { m with mem := wrBytes m.mem (lin + k.toUInt32) 1 x } := by
  have hk32 : k < 2 ^ 32 := by have := n.toNat_lt; omega
  have hkk : (k.toUInt32).toNat = k := by simp; omega
  rw [crossAddr (by simp [ramTop] at hm; omega)]
  apply physWr_flat h
  rw [toNat_add_k hk32 (by simp [ramTop] at hm; omega)]
  omega

theorem wrLoop2 {m m1 m2 : Machine} {P : Nat → UInt64} {v : UInt32}
    (h0 : physWr (P 0) 1 (ShiftRight.shiftRight v 0) m = .ok () m1)
    (h1 : physWr (P 1) 1 (ShiftRight.shiftRight v 8) m1 = .ok () m2) :
    EStateM.bind (forIn [:UInt32.toNat 2] PUnit.unit fun k _ =>
        EStateM.bind (physWr (P k) 1 (ShiftRight.shiftRight v (k.toUInt32 * 8))) fun _ =>
          pure (ForInStep.yield PUnit.unit))
      (fun _ => pure ()) m = .ok () m2 := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp [List.range', List.forIn_cons, List.forIn_nil, Std.Legacy.Range.size]
  simp only [bind, EStateM.bind, pure, EStateM.pure, h0, h1]

theorem wrLoop4 {m m1 m2 m3 m4 : Machine} {P : Nat → UInt64} {v : UInt32}
    (h0 : physWr (P 0) 1 (ShiftRight.shiftRight v 0) m = .ok () m1)
    (h1 : physWr (P 1) 1 (ShiftRight.shiftRight v 8) m1 = .ok () m2)
    (h2 : physWr (P 2) 1 (ShiftRight.shiftRight v 16) m2 = .ok () m3)
    (h3 : physWr (P 3) 1 (ShiftRight.shiftRight v 24) m3 = .ok () m4) :
    EStateM.bind (forIn [:UInt32.toNat 4] PUnit.unit fun k _ =>
        EStateM.bind (physWr (P k) 1 (ShiftRight.shiftRight v (k.toUInt32 * 8))) fun _ =>
          pure (ForInStep.yield PUnit.unit))
      (fun _ => pure ()) m = .ok () m4 := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp [List.range', List.forIn_cons, List.forIn_nil, Std.Legacy.Range.size]
  simp only [bind, EStateM.bind, pure, EStateM.pure, h0, h1, h2, h3]

theorem wrBytes1_set {mem : ByteArray} {a : UInt32} (h : a.toNat < mem.size) (x : UInt32) :
    wrBytes mem a 1 x = mem.set! a.toNat x.toUInt8 := by
  unfold wrBytes
  rw [if_pos (c := _) (by simp; omega)]
  rfl

theorem shr0 (x : UInt32) : ShiftRight.shiftRight x 0 = x := UInt32.shiftRight_zero

theorem wr2_join {mem : ByteArray} {a : UInt32} (h : a.toNat + 2 ≤ mem.size) (hs : mem.size ≤ ramTop) (v : UInt32) :
    wrBytes (wrBytes mem (a + (0 : Nat).toUInt32) 1 (ShiftRight.shiftRight v 0))
      (a + (1 : Nat).toUInt32) 1 (ShiftRight.shiftRight v 8) = wrBytes mem a 2 v := by
  have h0 := toNat_add_k (a := a) (k := 0) (by decide) (by simp [ramTop] at *; omega)
  have h1 := toNat_add_k (a := a) (k := 1) (by decide) (by simp [ramTop] at *; omega)
  rw [wrBytes1_set (by rw [size_wrBytes, h1]; omega), wrBytes1_set (by rw [h0]; omega), h0, h1, shr0]
  unfold wrBytes
  rw [if_pos (c := _) (by simp; omega)]
  rfl

theorem wr4_join {mem : ByteArray} {a : UInt32} (h : a.toNat + 4 ≤ mem.size) (hs : mem.size ≤ ramTop) (v : UInt32) :
    wrBytes (wrBytes (wrBytes (wrBytes mem (a + (0 : Nat).toUInt32) 1 (ShiftRight.shiftRight v 0))
      (a + (1 : Nat).toUInt32) 1 (ShiftRight.shiftRight v 8))
      (a + (2 : Nat).toUInt32) 1 (ShiftRight.shiftRight v 16))
      (a + (3 : Nat).toUInt32) 1 (ShiftRight.shiftRight v 24) = wrBytes mem a 4 v := by
  have h0 := toNat_add_k (a := a) (k := 0) (by decide) (by simp [ramTop] at *; omega)
  have h1 := toNat_add_k (a := a) (k := 1) (by decide) (by simp [ramTop] at *; omega)
  have h2 := toNat_add_k (a := a) (k := 2) (by decide) (by simp [ramTop] at *; omega)
  have h3 := toNat_add_k (a := a) (k := 3) (by decide) (by simp [ramTop] at *; omega)
  rw [wrBytes1_set (by rw [size_wrBytes, size_wrBytes, size_wrBytes, h3]; omega),
    wrBytes1_set (by rw [size_wrBytes, size_wrBytes, h2]; omega),
    wrBytes1_set (by rw [size_wrBytes, h1]; omega), wrBytes1_set (by rw [h0]; omega), h0, h1, h2, h3, shr0]
  unfold wrBytes
  rw [if_pos (c := _) (by simp; omega)]
  rfl

theorem linWrCross2 {m : Machine} (h : FlatM m) {lin : UInt32}
    (hr : lin.toNat + UInt32.toNat 2 ≤ m.mem.size) (hm : m.mem.size ≤ ramTop) (v : UInt32) :
    EStateM.bind (forIn [:UInt32.toNat 2] PUnit.unit fun k _ =>
        EStateM.bind (physWr (if (lin + k.toUInt32 &&& 4294963200 == lin + 2 - 1 &&& 4294963200) = true then
              (lin + 2 - 1 &&& 4294963200).toUInt64 + (lin + k.toUInt32 &&& 4095).toUInt64
            else lin.toUInt64 + (lin + k.toUInt32 - lin).toUInt64) 1 (ShiftRight.shiftRight v (k.toUInt32 * 8))) fun _ =>
          pure (ForInStep.yield PUnit.unit))
      (fun _ => pure ()) m = .ok () { m with mem := wrBytes m.mem lin 2 v } := by
  have := wrLoop2 (P := fun k => (if (lin + k.toUInt32 &&& 4294963200 == lin + 2 - 1 &&& 4294963200) = true then
              (lin + 2 - 1 &&& 4294963200).toUInt64 + (lin + k.toUInt32 &&& 4095).toUInt64
            else lin.toUInt64 + (lin + k.toUInt32 - lin).toUInt64)) (physWr_cross (n := 2) (m := m) (FlatM.mem_iter h) 0 (by decide) (by first | exact hr | simp only [size_wrBytes]; exact hr) (by first | exact hm | simp only [size_wrBytes]; exact hm) _) (physWr_cross (n := 2) (m := { m with mem := wrBytes m.mem (lin + (0 : Nat).toUInt32) 1 (ShiftRight.shiftRight v 0) }) (FlatM.mem_iter h) 1 (by decide) (by first | exact hr | simp only [size_wrBytes]; exact hr) (by first | exact hm | simp only [size_wrBytes]; exact hm) _)
  simp only [wr2_join hr hm] at this
  exact this

theorem linWrCross4 {m : Machine} (h : FlatM m) {lin : UInt32}
    (hr : lin.toNat + UInt32.toNat 4 ≤ m.mem.size) (hm : m.mem.size ≤ ramTop) (v : UInt32) :
    EStateM.bind (forIn [:UInt32.toNat 4] PUnit.unit fun k _ =>
        EStateM.bind (physWr (if (lin + k.toUInt32 &&& 4294963200 == lin + 4 - 1 &&& 4294963200) = true then
              (lin + 4 - 1 &&& 4294963200).toUInt64 + (lin + k.toUInt32 &&& 4095).toUInt64
            else lin.toUInt64 + (lin + k.toUInt32 - lin).toUInt64) 1 (ShiftRight.shiftRight v (k.toUInt32 * 8))) fun _ =>
          pure (ForInStep.yield PUnit.unit))
      (fun _ => pure ()) m = .ok () { m with mem := wrBytes m.mem lin 4 v } := by
  have := wrLoop4 (P := fun k => (if (lin + k.toUInt32 &&& 4294963200 == lin + 4 - 1 &&& 4294963200) = true then
              (lin + 4 - 1 &&& 4294963200).toUInt64 + (lin + k.toUInt32 &&& 4095).toUInt64
            else lin.toUInt64 + (lin + k.toUInt32 - lin).toUInt64)) (physWr_cross (n := 4) (m := m) (FlatM.mem_iter h) 0 (by decide) (by first | exact hr | simp only [size_wrBytes]; exact hr) (by first | exact hm | simp only [size_wrBytes]; exact hm) _) (physWr_cross (n := 4) (m := { m with mem := wrBytes m.mem (lin + (0 : Nat).toUInt32) 1 (ShiftRight.shiftRight v 0) }) (FlatM.mem_iter h) 1 (by decide) (by first | exact hr | simp only [size_wrBytes]; exact hr) (by first | exact hm | simp only [size_wrBytes]; exact hm) _) (physWr_cross (n := 4) (m := { { m with mem := wrBytes m.mem (lin + (0 : Nat).toUInt32) 1 (ShiftRight.shiftRight v 0) } with mem := wrBytes { m with mem := wrBytes m.mem (lin + (0 : Nat).toUInt32) 1 (ShiftRight.shiftRight v 0) }.mem (lin + (1 : Nat).toUInt32) 1 (ShiftRight.shiftRight v 8) }) (FlatM.mem_iter h) 2 (by decide) (by first | exact hr | simp only [size_wrBytes]; exact hr) (by first | exact hm | simp only [size_wrBytes]; exact hm) _) (physWr_cross (n := 4) (m := { { { m with mem := wrBytes m.mem (lin + (0 : Nat).toUInt32) 1 (ShiftRight.shiftRight v 0) } with mem := wrBytes { m with mem := wrBytes m.mem (lin + (0 : Nat).toUInt32) 1 (ShiftRight.shiftRight v 0) }.mem (lin + (1 : Nat).toUInt32) 1 (ShiftRight.shiftRight v 8) } with mem := wrBytes { { m with mem := wrBytes m.mem (lin + (0 : Nat).toUInt32) 1 (ShiftRight.shiftRight v 0) } with mem := wrBytes { m with mem := wrBytes m.mem (lin + (0 : Nat).toUInt32) 1 (ShiftRight.shiftRight v 0) }.mem (lin + (1 : Nat).toUInt32) 1 (ShiftRight.shiftRight v 8) }.mem (lin + (2 : Nat).toUInt32) 1 (ShiftRight.shiftRight v 16) }) (FlatM.mem_iter h) 3 (by decide) (by first | exact hr | simp only [size_wrBytes]; exact hr) (by first | exact hm | simp only [size_wrBytes]; exact hm) _)
  simp only [wr4_join hr hm] at this
  exact this

theorem linWr_flat {m : Machine} (h : FlatM m) {lin n : UInt32} (hn : n = 1 ∨ n = 2 ∨ n = 4)
    (hr : lin.toNat + n.toNat ≤ m.mem.size) (hm : m.mem.size ≤ ramTop) (v : UInt32) (u i : Bool) :
    linWr lin n v u i m = .ok () { m with mem := wrBytes m.mem lin n v } := by
  have hbp := h.2.2.1
  have hn1 : 1 ≤ n.toNat := by rcases hn with rfl | rfl | rfl <;> decide
  unfold linWr
  simp only [bind, EStateM.bind, dbData_flat hbp]
  split
  · rw [bind_ok (translate_flat h _ _ _ _ _)]
    exact physWr_flat h (by omega) n v
  · rename_i hc
    rcases hn with rfl | rfl | rfl
    · exfalso; apply hc
      have : lin.toNat &&& 4095 ≤ 4095 := Nat.and_le_right
      rw [UInt32.le_iff_toNat_le, UInt32.toNat_add, Nat.mod_eq_of_lt (by simp; omega)]
      simp; omega
    · rw [bind_ok (translate_flat h _ _ _ _ _), bind_ok (translate_flat h _ _ _ _ _)]
      exact linWrCross2 h hr hm v
    · rw [bind_ok (translate_flat h _ _ _ _ _), bind_ok (translate_flat h _ _ _ _ _)]
      exact linWrCross4 h hr hm v

/-- A flat, present, writable, expand-up data segment covering the whole address space. -/
def FlatSeg (sr : SegReg) : Prop := sr.base = 0 ∧ sr.limit = 0xFFFFFFFF ∧ sr.attr = 0xC093

theorem segAddr_flat {m : Machine} {s : UInt8} (hs : FlatSeg (m.cpu.getSeg s)) {off n : UInt32}
    (hn : 1 ≤ n.toNat) (hr : off.toNat + n.toNat ≤ 2 ^ 32) (w : Bool) :
    segAddr s off n w m = .ok off m := by
  obtain ⟨hb, hl, ha⟩ := hs
  have hlast : off.toUInt64 + n.toUInt64 - 1 ≤ (0xFFFFFFFF : UInt32).toUInt64 := by
    rw [UInt64.le_iff_toNat_le]
    have : (off.toUInt64 + n.toUInt64).toNat = off.toNat + n.toNat := by
      simp only [UInt64.toNat_add, UInt32.toNat_toUInt64]; omega
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, this]; simp; omega), this]
    simp; omega
  simp only [reduceU32toU64] at hlast
  simp only [segAddr, segAllowed, ha, hl, hb]
  simp [hlast, reduceAndU]

theorem rdMem_flat {m : Machine} (h : FlatM m) (hcpl : m.cpu.cpl = 0) {s : UInt8}
    (hs : FlatSeg (m.cpu.getSeg s)) {off n : UInt32} (hn : n = 1 ∨ n = 2 ∨ n = 4)
    (hr : off.toNat + n.toNat ≤ m.mem.size) (hm : m.mem.size ≤ ramTop) (w : Bool) (al : UInt32) :
    rdMem s off n w al m = .ok (rdBytes m.mem off n) m := by
  have hn1 : 1 ≤ n.toNat := by rcases hn with rfl | rfl | rfl <;> decide
  simp only [rdMem, bind, EStateM.bind]
  rw [segAddr_flat hs hn1 (by simp [ramTop] at hm; omega)]
  simp only [isUser, hcpl, acChk]
  exact linRd_flat h hn hr hm _ _ _

theorem wrMem_flat {m : Machine} (h : FlatM m) (hcpl : m.cpu.cpl = 0) {s : UInt8}
    (hs : FlatSeg (m.cpu.getSeg s)) {off n : UInt32} (hn : n = 1 ∨ n = 2 ∨ n = 4)
    (hr : off.toNat + n.toNat ≤ m.mem.size) (hm : m.mem.size ≤ ramTop) (v al : UInt32) :
    wrMem s off n v al m = .ok () { m with mem := wrBytes m.mem off n v } := by
  have hn1 : 1 ≤ n.toNat := by rcases hn with rfl | rfl | rfl <;> decide
  simp only [wrMem, bind, EStateM.bind]
  rw [segAddr_flat hs hn1 (by simp [ramTop] at hm; omega)]
  simp only [isUser, hcpl, acChk]
  exact linWr_flat h hn hr hm _ _ _

end Solutions.Exec
