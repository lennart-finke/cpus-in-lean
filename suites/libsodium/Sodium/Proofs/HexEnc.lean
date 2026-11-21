import Sodium.Proofs.HexEncLoop
/-!
# `bin2hex_correct` and `bin2hex_constant_time`

The run of `sodium_bin2hex`: the prologue (`HexEncPre`), `n` iterations of the loop
(`HexEncLoop`), the epilogue. It follows a path of instruction addresses that depends only on the
length `n` (`path`); the bytes written are the digits of `hex x` and a NUL.
-/
namespace Sodium.Proofs.HexEnc
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Solutions.Logic.Cmp Sodium.Proofs Sodium.Utils Sodium.Spec
open Sodium.Proofs.Memzero (running_of_eip neHalt tf_efl u64_succ_toNat u64_lt_max toNat_toUInt32
  succ_toUInt32 u32_toNat_sub u32_toNat_add)
open Sodium.Proofs.Memcmp (pstep2 ic_chain)

/-! ## Paths -/

def seg1Path : List UInt32 := [1048576, 1048577, 1048578, 1048579, 1048580, 1048581]
def seg2aPath : List UInt32 := [1048585, 1048591, 1048593, 1048597, 1048601]
def seg2bPath : List UInt32 := [1048603, 1048607, 1048609, 1048611]
def seg3Path : List UInt32 := [1048614, 1048618, 1048620, 1048621, 1048622, 1048623]
def segz1Path : List UInt32 := [1048603, 1048607, 1048609, 1048695]
/-- From the terminating store to the return. -/
def tailPath : List UInt32 := [0x100079, 0x10007D, 0x100080, 0x100081, 0x100082, 0x100083, 0x100084]
/-- After the loop. -/
def exitPath : List UInt32 := [0x100072, 0x100075] ++ tailPath

/-- The instruction addresses of a call on `n` bytes. -/
def path (n : Nat) : List UInt32 :=
  if n = 0 then seg1Path ++ seg2aPath ++ segz1Path ++ tailPath
  else seg1Path ++ seg2aPath ++ seg2bPath ++ seg3Path ++ (List.replicate (n - 1) iterPath).flatten ++ iterPath ++
    exitPath

/-! ## The frame -/

theorem get!_wr4_out {mem : ByteArray} {a v : UInt32} (h : a.toNat + 4 ≤ mem.size) (j : Nat)
    (hd : j < a.toNat ∨ a.toNat + 4 ≤ j) : (wrBytes mem a 4 v).get! j = mem.get! j := by
  rw [get!_wrBytes4 h, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

section frame
variable (G : SMem) (t ebp ebx edi esi eax : UInt32)
  (ok1 : StoreOk Image.base Image.size G.mem (t.add 16))
  (ok2 : StoreOk Image.base Image.size (CodeMem.wr4 G (t.add 16) ebp ok1).mem (t.add 12))
  (ok3 : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 G (t.add 16) ebp ok1) (t.add 12) ebx ok2).mem (t.add 8))
  (ok4 : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 (CodeMem.wr4 G (t.add 16) ebp ok1) (t.add 12) ebx ok2)
    (t.add 8) edi ok3).mem (t.add 4))
  (ok5 : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 (CodeMem.wr4 (CodeMem.wr4 G (t.add 16) ebp ok1)
    (t.add 12) ebx ok2) (t.add 8) edi ok3) (t.add 4) esi ok4).mem t)
  (hsz : G.get.size ≤ 4273995776) (hst : t.toNat + 40 ≤ G.get.size)

theorem fr_size : (Fr G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5).get.size = G.get.size := by
  unfold Fr; simp only [wr4_get_size]

include hsz hst in
/-- The bytes outside `[t, t + 20)` are those of `G`. -/
theorem fr_get (j : Nat) (hd : j < t.toNat ∨ t.toNat + 20 ≤ j) :
    (Fr G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5).get.get! j = G.get.get! j := by
  have h4 : (t.add 4).toNat = t.toNat + 4 := u32_toNat_add (by simp; omega)
  have h8 : (t.add 8).toNat = t.toNat + 8 := u32_toNat_add (by simp; omega)
  have h12 : (t.add 12).toNat = t.toNat + 12 := u32_toNat_add (by simp; omega)
  have h16 : (t.add 16).toNat = t.toNat + 16 := u32_toNat_add (by simp; omega)
  unfold Fr; simp only [wr4_get]
  rw [get!_wr4_out, get!_wr4_out, get!_wr4_out, get!_wr4_out, get!_wr4_out] <;>
    first | (simp only [size_wrBytes]; omega) | omega

include hsz hst in
/-- The saved registers and the return address. -/
theorem fr_reads :
    rdRaw (Fr G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5).get (t.add 4) 4 = esi ∧
    rdRaw (Fr G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5).get (t.add 8) 4 = edi ∧
    rdRaw (Fr G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5).get (t.add 12) 4 = ebx ∧
    rdRaw (Fr G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5).get (t.add 16) 4 = ebp ∧
    rdRaw (Fr G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5).get (t.add 20) 4 = rdRaw G.get (t.add 20) 4 := by
  have h4 : (t.add 4).toNat = t.toNat + 4 := u32_toNat_add (by simp; omega)
  have h8 : (t.add 8).toNat = t.toNat + 8 := u32_toNat_add (by simp; omega)
  have h12 : (t.add 12).toNat = t.toNat + 12 := u32_toNat_add (by simp; omega)
  have h16 : (t.add 16).toNat = t.toNat + 16 := u32_toNat_add (by simp; omega)
  have h20 : (t.add 20).toNat = t.toNat + 20 := u32_toNat_add (by simp; omega)
  unfold Fr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [rdRaw_wr4_other4, rdRaw_wr4_same] <;> first | (simp only [wr4_get_size]; omega) | omega
  · rw [rdRaw_wr4_other4, rdRaw_wr4_other4, rdRaw_wr4_same] <;>
      first | (simp only [wr4_get_size]; omega) | omega
  · rw [rdRaw_wr4_other4, rdRaw_wr4_other4, rdRaw_wr4_other4, rdRaw_wr4_same] <;>
      first | (simp only [wr4_get_size]; omega) | omega
  · rw [rdRaw_wr4_other4, rdRaw_wr4_other4, rdRaw_wr4_other4, rdRaw_wr4_other4, rdRaw_wr4_same] <;>
      first | (simp only [wr4_get_size]; omega) | omega
  · rw [rdRaw_wr4_other4, rdRaw_wr4_other4, rdRaw_wr4_other4, rdRaw_wr4_other4, rdRaw_wr4_other4] <;>
      first | (simp only [wr4_get_size]; omega) | omega

include hsz hst in
set_option maxHeartbeats 0 in
/-- The terminating store and the return, from any memory that still holds the saved registers. -/
theorem tail (hap : StackApart t) (H : SMem) (P C d b N B i F : UInt32) (ic : UInt64)
    (hHs : H.get.size = G.get.size)
    (hag : ∀ j, t.toNat + 4 ≤ j → j < t.toNat + 24 →
      H.get.get! j = (Fr G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5).get.get! j)
    (hPC : P.toNat + C.toNat < G.get.size) (hPi : P.toNat + C.toNat < 0x100000 ∨ 0x100000 + 3560 ≤ P.toNat)
    (hPt : P.toNat + C.toNat < t.toNat + 4 ∨ t.toNat + 24 ≤ P.toNat + C.toNat)
    (hic : ic.toNat + 8 < 2 ^ 64) :
    ∃ (Mf : SMem) (ic' : UInt64), PRun img tailPath (St.m ⟨H.get, P, C, d, b, t, N, B, i, 0x100079, efl F, ic⟩)
      (St.m ⟨Mf.get, P, C, d, ebx, t.add 24, ebp, esi, edi, rdRaw G.get (t.add 20) 4, efl (addF 4 t 4 0).2, ic'⟩) ∧
      Mf.get = wrBytes H.get (P.add C) 1 0 := by
  have hpc : (P.add C).toNat = P.toNat + C.toNat := u32_toNat_add (by omega)
  have hsz' : H.get.size ≤ 4273995776 := by rw [hHs]; exact hsz
  have hst' : t.toNat + 40 ≤ H.get.size := by rw [hHs]; exact hst
  have ok : StoreOk1 Image.base Image.size H.mem (P.add C) := by
    refine ⟨by show _ < H.get.size; rw [hpc, hHs]; omega, ?_⟩
    rw [hpc]; simp only [Image.base, Image.size, UInt32.reduceToNat]; omega
  have q3 := pst (e3 H P C d b t N B i F ic hsz' hst' hap (by rw [hHs]; exact hPC) hPi ok) (by omega) (tf_efl _)
    (neHalt _ (by decide))
  obtain ⟨Mf, hMf⟩ : ∃ Mf, Mf = CodeMem.wr1 H (P.add C) 0 ok := ⟨_, rfl⟩
  rw [← hMf] at q3
  have hMg : Mf.get = wrBytes H.get (P.add C) 1 0 := by rw [hMf]; rfl
  have hMs : Mf.get.size = G.get.size := by rw [hMg, size_wrBytes, hHs]
  have hszf : Mf.get.size ≤ 4273995776 := by rw [hMs]; exact hsz
  have hstf : t.toNat + 40 ≤ Mf.get.size := by rw [hMs]; exact hst
  have rd : ∀ k : UInt32, (t.add k).toNat = t.toNat + k.toNat → 4 ≤ k.toNat → k.toNat ≤ 20 →
      rdRaw Mf.get (t.add k) 4 = rdRaw (Fr G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5).get (t.add k) 4 := by
    intro k hk h4 h20
    show rdBytes Mf.get (t.add k) 4 = rdBytes (Fr G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5).get (t.add k) 4
    apply rdBytes4_congr (by rw [hk, hMs]; omega) (by rw [hk, fr_size]; omega)
    intro j hj
    rw [hMg, get!_wrBytes1 (by rw [hpc, hHs]; omega), if_neg (by rw [hpc, hk]; omega), hag _ (by omega) (by omega)]
  have h4 : (t.add 4).toNat = t.toNat + 4 := u32_toNat_add (by simp; omega)
  have h8 : (t.add 8).toNat = t.toNat + 8 := u32_toNat_add (by simp; omega)
  have h12 : (t.add 12).toNat = t.toNat + 12 := u32_toNat_add (by simp; omega)
  have h16 : (t.add 16).toNat = t.toNat + 16 := u32_toNat_add (by simp; omega)
  have h20 : (t.add 20).toNat = t.toNat + 20 := u32_toNat_add (by simp; omega)
  obtain ⟨f4, f8, f12, f16, f20⟩ := fr_reads G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5 hsz hst
  have r4 := (rd 4 h4 (by decide) (by decide)).trans f4
  have r8 := (rd 8 h8 (by decide) (by decide)).trans f8
  have r12 := (rd 12 h12 (by decide) (by decide)).trans f12
  have r16 := (rd 16 h16 (by decide) (by decide)).trans f16
  have r20 := (rd 20 h20 (by decide) (by decide)).trans f20
  have q4 := pst (e4 Mf P C d b t N B i F (ic + 1) hszf hstf hap) (icb 1 (by omega)) (tf_efl _) (neHalt _ (by decide))
  have q5 := pst (e5 Mf P C d b t N B i (addF 4 t 4 0).2 (ic + 1 + 1) hszf hstf hap) (icb 2 (by omega)) (tf_efl _)
    (neHalt _ (by decide))
  rw [r4] at q5
  have q6 := pst (e6 Mf P C d b t N esi i (addF 4 t 4 0).2 (ic + 1 + 1 + 1) hszf hstf hap) (icb 3 (by omega))
    (tf_efl _) (neHalt _ (by decide))
  rw [r8] at q6
  have q7 := pst (e7 Mf P C d b t N esi edi (addF 4 t 4 0).2 (ic + 1 + 1 + 1 + 1) hszf hstf hap) (icb 4 (by omega))
    (tf_efl _) (neHalt _ (by decide))
  rw [r12] at q7
  have q8 := pst (e8 Mf P C d ebx t N esi edi (addF 4 t 4 0).2 (ic + 1 + 1 + 1 + 1 + 1) hszf hstf hap)
    (icb 5 (by omega)) (tf_efl _) (neHalt _ (by decide))
  rw [r16] at q8
  have q9 := pst (e9 Mf P C d ebx t ebp esi edi (addF 4 t 4 0).2 (ic + 1 + 1 + 1 + 1 + 1 + 1) hszf hstf hap)
    (icb 6 (by omega)) (tf_efl _) (neHalt _ (by decide))
  rw [r20] at q9
  exact ⟨Mf, _, (q3.append (q4.append (q5.append (q6.append (q7.append (q8.append q9)))))).cast rfl, hMg⟩

end frame

/-! ## The call -/

theorem hi_ne {a b : UInt32} (h : a.toNat ≠ b.toNat) : a ≠ b := fun e => h (congrArg UInt32.toNat e)

set_option maxHeartbeats 0 in
/-- A call: its path of instruction addresses, its return, and the bytes it writes. -/
theorem run (c : Caller) (hexp binp : UInt32) (cap : Nat) (x : List UInt8)
    (h : EncodePre c (bin2hexArgs hexp binp cap x) hexp binp cap (2 * x.length) x) :
    ∃ r, PRun img (path x.length) (c.enter Image.sym_sodium_bin2hex) r ∧
      Returned img (c.enter Image.sym_sodium_bin2hex) r ∧ CalleeSaved (c.enter Image.sym_sodium_bin2hex) r ∧
      Preserved (c.enter Image.sym_sodium_bin2hex) r stackBound (InRange hexp (2 * x.length + 1)) ∧
      r.cpu.eax = hexp ∧ bytesAt r hexp (2 * x.length + 1) = hex x ++ [0] := by
  obtain ⟨hc, hbP, hbB, hPB, hmx, hcap⟩ := h
  have hsz : c.mem.size ≤ 4273995776 := hc.1
  have hsp : 128 ≤ c.sp.toNat := hc.2.2.2.2.1
  have hsp20 : c.sp.toNat + 20 ≤ c.mem.size := by
    have := hc.2.2.2.2.2.1; simpa [bin2hexArgs] using this
  have hlo : (c.stackLo stackBound).toNat = c.sp.toNat - 128 := u32_toNat_sub hsp (by decide)
  have hbase : (Image.base).toNat = 0x100000 := rfl
  have hap0 : c.sp.toNat - 128 + 148 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ c.sp.toNat - 128 := by
    have h := hc.2.2.2.2.2.2
    unfold Apart at h
    rw [hlo, Memzero.img_size, Memzero.img_base] at h
    simp only [stackSize, bin2hexArgs, List.length_cons, List.length_nil, stackBound] at h
    omega
  -- the buffers
  have hcapM : cap ≤ maxObject := hbP.2.1
  have hcap31 : cap < 2 ^ 32 := by unfold maxObject at hcapM; omega
  have hn : x.length < 1073741824 := by unfold maxObject at hcapM; omega
  have hPfit : hexp.toNat + cap ≤ c.mem.size := by
    rcases hbP.1 with h0 | h0
    · omega
    · exact h0
  have hPimg : hexp.toNat + cap ≤ 0x100000 ∨ 0x100000 + 3560 ≤ hexp.toNat := by
    have h := hbP.2.2.1; unfold Apart at h; rw [Memzero.img_size, Memzero.img_base] at h; omega
  have hPstk : hexp.toNat + cap ≤ c.sp.toNat - 128 ∨ c.sp.toNat + 20 ≤ hexp.toNat := by
    have h := hbP.2.2.2; unfold Apart at h; rw [hlo] at h
    simp only [stackSize, bin2hexArgs, List.length_cons, List.length_nil, stackBound] at h; omega
  -- the stack
  let t : UInt32 := c.sp - (20 : Nat).toUInt32
  have ht : t.toNat = c.sp.toNat - 20 := u32_toNat_sub (by omega) (by decide)
  have hspt : c.sp = t.add 20 := by
    apply UInt32.toNat_inj.1; rw [u32_toNat_add (by simp; omega)]; simp; omega
  let G : SMem := codeMem c hc
  have hG : G.get = c.mem := rfl
  have hszG : G.get.size ≤ 4273995776 := hsz
  have hGs : G.get.size = c.mem.size := rfl
  have hst : t.toNat + 40 ≤ G.get.size := by rw [hG]; omega
  have hap : StackApart t := by unfold StackApart; omega
  have h4 : (t.add 4).toNat = t.toNat + 4 := u32_toNat_add (by simp; omega)
  have h8 : (t.add 8).toNat = t.toNat + 8 := u32_toNat_add (by simp; omega)
  have h12 : (t.add 12).toNat = t.toNat + 12 := u32_toNat_add (by simp; omega)
  have h16 : (t.add 16).toNat = t.toNat + 16 := u32_toNat_add (by simp; omega)
  have hk : ∀ k : Nat, k < 4 → t.add (24 + 4 * k).toUInt32 = c.sp + 4 * (k + 1).toUInt32 := by
    intro k hk4
    apply UInt32.toNat_inj.1
    rw [u32_toNat_add (by simp; omega), UInt32.toNat_add]; simp; omega
  have hP' : rdRaw G.get (t.add 24) 4 = hexp := by
    have := hk 0 (by decide); simp at this; rw [this]; exact calls_arg hc 0 (by simp [bin2hexArgs])
  have hC' : rdRaw G.get (t.add 28) 4 = cap.toUInt32 := by
    have := hk 1 (by decide); simp at this; rw [this]; exact calls_arg hc 1 (by simp [bin2hexArgs])
  have hB' : rdRaw G.get (t.add 32) 4 = binp := by
    have := hk 2 (by decide); simp at this; rw [this]; exact calls_arg hc 2 (by simp [bin2hexArgs])
  have hN' : rdRaw G.get (t.add 36) 4 = x.length.toUInt32 := by
    have := hk 3 (by decide); simp at this; rw [this]; exact calls_arg hc 3 (by simp [bin2hexArgs])
  have hret : rdRaw G.get (t.add 20) 4 = Image.sym_halt := by rw [← hspt]; exact calls_ret hc
  have hNN : x.length.toUInt32.toNat = x.length := toNat_toUInt32 (by omega)
  have hcN : cap.toUInt32.toNat = cap := toNat_toUInt32 hcap31
  -- the pushes
  have ok1 : StoreOk Image.base Image.size G.mem (t.add 16) := by
    refine ⟨by show _ ≤ G.get.size; omega, ?_⟩
    simp only [Image.size, hbase, h16]; omega
  have ok2 : StoreOk Image.base Image.size (CodeMem.wr4 G (t.add 16) c.regs.ebp ok1).mem (t.add 12) := by
    refine ⟨by show _ ≤ (CodeMem.wr4 G _ _ ok1).get.size; rw [wr4_get_size]; omega, ?_⟩
    simp only [Image.size, hbase, h12]; omega
  have ok3 : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 G (t.add 16) c.regs.ebp ok1) (t.add 12)
      c.regs.ebx ok2).mem (t.add 8) := by
    refine ⟨by show _ ≤ (CodeMem.wr4 (CodeMem.wr4 G _ _ ok1) _ _ ok2).get.size; rw [wr4_get_size, wr4_get_size]; omega, ?_⟩
    simp only [Image.size, hbase, h8]; omega
  have ok4 : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 (CodeMem.wr4 G (t.add 16) c.regs.ebp ok1)
      (t.add 12) c.regs.ebx ok2) (t.add 8) c.regs.edi ok3).mem (t.add 4) := by
    refine ⟨by rw [mem_eq_get]; simp only [wr4_get_size]; omega, ?_⟩
    simp only [Image.size, hbase, h4]; omega
  have ok5 : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 (CodeMem.wr4 (CodeMem.wr4 G (t.add 16)
      c.regs.ebp ok1) (t.add 12) c.regs.ebx ok2) (t.add 8) c.regs.edi ok3) (t.add 4) c.regs.esi ok4).mem t := by
    refine ⟨by rw [mem_eq_get]; simp only [wr4_get_size]; omega, ?_⟩
    simp only [Image.size, hbase]; omega
  have hFs := fr_size G t c.regs.ebp c.regs.ebx c.regs.edi c.regs.esi c.regs.eax ok1 ok2 ok3 ok4 ok5
  have ok6 : StoreOk Image.base Image.size
      (Fr G t c.regs.ebp c.regs.ebx c.regs.edi c.regs.esi c.regs.eax ok1 ok2 ok3 ok4 ok5).mem t := by
    refine ⟨by show _ ≤ (Fr G t _ _ _ _ _ ok1 ok2 ok3 ok4 ok5).get.size; rw [hFs]; omega, ?_⟩
    simp only [Image.size, hbase]; omega
  have hFg := fr_get G t c.regs.ebp c.regs.ebx c.regs.edi c.regs.esi c.regs.eax ok1 ok2 ok3 ok4 ok5 hszG hst
  have e0 : c.enter Image.sym_sodium_bin2hex =
      St.m ⟨G.get, c.regs.eax, c.regs.ecx, c.regs.edx, c.regs.ebx, t.add 20, c.regs.ebp, c.regs.esi,
        c.regs.edi, 0x100000, efl c.regs.flags, 0⟩ := by
    rw [← hspt]; rfl
  have hesp : (t.add 20) + 4 = t.add 24 := by
    apply UInt32.toNat_inj.1
    rw [UInt32.toNat_add, u32_toNat_add (by simp; omega), u32_toNat_add (by simp; omega)]; simp; omega
  have hstack : ∀ a : UInt32, ¬ InRange (t.add 20 - (stackBound : Nat).toUInt32) stackBound a →
      a.toNat < t.toNat ∨ t.toNat + 20 ≤ a.toNat := by
    intro a ha
    rw [inRange_iff, u32_toNat_sub (by rw [u32_toNat_add (by simp; omega)]; simp [stackBound]; omega) (by decide),
      u32_toNat_add (by simp; omega)] at ha
    simp [stackBound] at ha; omega
  have p1 := prun_of_runOkP (seg1 (G := G) (eax := c.regs.eax) (ecx := c.regs.ecx) (edx := c.regs.edx)
    (ebx := c.regs.ebx) (t := t) (ebp := c.regs.ebp) (esi := c.regs.esi) (edi := c.regs.edi) (f := c.regs.flags)
    (ok1 := ok1) (ok2 := ok2) (ok3 := ok3) (ok4 := ok4) (ok5 := ok5) (hsz := hszG) (hst := hst) (hap := hap))
  have p2 := prun_of_runOkP (seg2a (G := G) (eax := c.regs.eax) (ecx := c.regs.ecx) (edx := c.regs.edx)
    (ebx := c.regs.ebx) (t := t) (ebp := c.regs.ebp) (esi := c.regs.esi) (edi := c.regs.edi) (f := c.regs.flags)
    (ok1 := ok1) (ok2 := ok2) (ok3 := ok3) (ok4 := ok4) (ok5 := ok5) (hsz := hszG) (hst := hst) (hap := hap)
    (hn := by rw [hN', hNN]; exact hn) (hcap := by rw [hN', hC', hNN, hcN]; omega))
  rw [e0]
  rcases Nat.eq_zero_or_pos x.length with hn0 | hn0
  · -- an empty input
    have hz : (rdRaw G.get (t.add 36) 4).toNat = 0 := by rw [hN', hNN, hn0]
    have pz := prun_of_runOkP (segz1 (G := G) (eax := c.regs.eax) (edx := c.regs.edx)
      (ebx := c.regs.ebx) (t := t) (ebp := c.regs.ebp) (esi := c.regs.esi) (edi := c.regs.edi)
      (f := (subF 4 (rdRaw G.get (t.add 28) 4) ((rdRaw G.get (t.add 36) 4).add (rdRaw G.get (t.add 36) 4)) 0).2)
      (ok1 := ok1) (ok2 := ok2) (ok3 := ok3) (ok4 := ok4) (ok5 := ok5) (hsz := hszG) (hst := hst) (hap := hap)
      (hz := hz))
    obtain ⟨Mf, ic', pt, hMg⟩ := tail G t c.regs.ebp c.regs.ebx c.regs.edi c.regs.esi c.regs.eax ok1 ok2 ok3 ok4 ok5
      hszG hst hap _ (rdRaw G.get (t.add 24) 4) 0 c.regs.edx c.regs.ebx (rdRaw G.get (t.add 36) 4) c.regs.esi
      c.regs.edi (logicF 4 0).2 15 hFs (fun _ _ _ => rfl) (by rw [hP']; simp; omega) (by rw [hP']; simp; omega)
      (by rw [hP']; simp; omega) (by decide)
    have pr := p1.append (p2.append (pz.append pt))
    rw [hret, hP'] at pr
    rw [hP'] at hMg
    have hp0 : (hexp.add 0).toNat = hexp.toNat := by rw [u32_toNat_add (by simp; omega)]; rfl
    refine ⟨_, pr.cast ?_, ⟨rfl, hesp.symm, efl_DF _⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨?_, ?_⟩, rfl, ?_⟩
    · rw [path, if_pos hn0]; simp only [seg1Path, seg2aPath, segz1Path, List.append_assoc]
    · show Mf.get.size = c.mem.size
      rw [hMg, size_wrBytes, hFs, hGs]
    · intro a ha hW hs
      have ha' : a.toNat < c.mem.size := ha
      have hd := hstack a hs
      have hW' : ¬(hexp.toNat ≤ a.toNat ∧ a.toNat < hexp.toNat + (2 * x.length + 1)) := fun h => hW (inRange_iff.2 h)
      show memByte Mf.get a = memByte c.mem a
      rw [hMg, memByte_wrBytes1 (by rw [hp0, hFs]; omega) (by rw [hFs]; exact ha),
        if_neg (hi_ne (by rw [hp0]; omega)), memByte_def (by rw [hFs]; exact ha), memByte_def ha', hFg _ hd]
      rfl
    · have hx0 : x = [] := List.eq_nil_of_length_eq_zero hn0
      show memBytes Mf.get hexp (2 * x.length + 1) = hex x ++ [0]
      rw [hx0]
      apply memBytes_eq_iff.2
      refine ⟨rfl, fun i hi => ?_⟩
      have hi0 : i = 0 := by simp [hex_nil] at hi; omega
      subst hi0
      rw [hMg, memByte_wrBytes1 (by rw [hp0, hFs]; omega) (by simp; rw [hFs]; omega),
        if_pos (UInt32.toNat_inj.1 (by rw [hp0]; simp))]
      rfl
  · -- the loop
    have hz : 0 < (rdRaw G.get (t.add 36) 4).toNat := by rw [hN', hNN]; exact hn0
    have p3 := prun_of_runOkP (seg2b (G := G) (eax := c.regs.eax) (edx := c.regs.edx)
      (ebx := c.regs.ebx) (t := t) (ebp := c.regs.ebp) (esi := c.regs.esi) (edi := c.regs.edi)
      (f := (subF 4 (rdRaw G.get (t.add 28) 4) ((rdRaw G.get (t.add 36) 4).add (rdRaw G.get (t.add 36) 4)) 0).2)
      (ok1 := ok1) (ok2 := ok2) (ok3 := ok3) (ok4 := ok4) (ok5 := ok5) (ok6 := ok6) (hsz := hszG) (hst := hst)
      (hap := hap) (hn := by rw [hN', hNN]; exact hn) (hz := hz))
    have p4 := prun_of_runOkP (seg3 (G := G) (eax := c.regs.eax) (edx := c.regs.edx)
      (ebx := c.regs.ebx) (t := t) (ebp := c.regs.ebp) (esi := c.regs.esi) (edi := c.regs.edi)
      (f := (logicF 4 (rdRaw G.get (t.add 36) 4)).2)
      (ok1 := ok1) (ok2 := ok2) (ok3 := ok3) (ok4 := ok4) (ok5 := ok5) (ok6 := ok6) (hsz := hszG) (hst := hst)
      (hap := hap) (P := rdRaw G.get (t.add 24) 4) (c := (rdRaw G.get (t.add 36) 4).add (rdRaw G.get (t.add 36) 4)))
    have hpre := p1.append (p2.append (p3.append p4))
    obtain ⟨M6, hM6⟩ : ∃ M6, M6 = CodeMem.wr4 (Fr G t c.regs.ebp c.regs.ebx c.regs.edi c.regs.esi c.regs.eax
        ok1 ok2 ok3 ok4 ok5) t ((rdRaw G.get (t.add 36) 4).add (rdRaw G.get (t.add 36) 4)) ok6 := ⟨_, rfl⟩
    have hM6s : M6.get.size = c.mem.size := by rw [hM6, wr4_get_size, hFs, hGs]
    have hM6g : ∀ j, j < t.toNat ∨ t.toNat + 20 ≤ j → M6.get.get! j = c.mem.get! j := by
      intro j hj
      rw [hM6, wr4_get, get!_wr4_out, hFg j hj]
      · rfl
      · rw [hFs]; omega
      · omega
    have hM6f : ∀ j, t.toNat + 4 ≤ j →
        M6.get.get! j = (Fr G t c.regs.ebp c.regs.ebx c.regs.edi c.regs.esi c.regs.eax ok1 ok2 ok3 ok4 ok5).get.get! j := by
      intro j hj
      rw [hM6, wr4_get, get!_wr4_out]
      · rw [hFs]; omega
      · omega
    have hM6t : rdRaw M6.get t 4 = x.length.toUInt32.add x.length.toUInt32 := by
      rw [hM6, rdRaw_wr4_same _ _ _ _ _ rfl, hN']
    rw [← hM6] at hpre
    rw [hN', hP', hB'] at hpre
    have hF : Facts M6.get hexp binp x.length x := by
      have hBfit := hbB.1
      have hBimg := hbB.2.2.1
      have hBstk := hbB.2.2.2
      unfold Fits at hBfit
      unfold Apart at hBimg hBstk hPB
      rw [Memzero.img_size, Memzero.img_base] at hBimg
      rw [hlo] at hBstk
      simp only [stackSize, bin2hexArgs, List.length_cons, List.length_nil, stackBound] at hBstk
      refine ⟨by rw [hM6s]; exact hsz, hn, rfl, by rw [hM6s]; omega, by omega, by rw [hM6s]; omega, by omega,
        by omega, fun k hk => ?_⟩
      have hbk : (binp + k.toUInt32).toNat = binp.toNat + k := toNat_add_of_lt (by omega)
      rw [hM6g _ (by omega), ← hbk, ← memByte_def (by rw [hbk]; omega),
        ← memBytes_getElem c.mem binp x.length k (by rw [memBytes_length]; exact hk)]
      simp only [hmx]
      simp [hk]
    have hI0 : Inv M6.get hexp t x.length.toUInt32 binp x 0
        (St.m ⟨M6.get, hexp, x.length.toUInt32.add x.length.toUInt32, c.regs.edx, c.regs.ebx, t, x.length.toUInt32,
          binp, 0, 0x100030, efl (logicF 4 0).2, 21⟩) :=
      ⟨M6, _, _, _, _, 21, rfl, by decide, rfl, fun j hj => by rw [if_neg (by omega)]⟩
    obtain ⟨m1, hL, hI1⟩ := PRun.loop (img := img) iterPath
      (fun i m => Inv M6.get hexp t x.length.toUInt32 binp x i m) (x.length - 1)
      (fun i m hi hI => loop_step M6.get hexp t binp x.length x hF i m (by omega) hI) hI0
    obtain ⟨H, c1, d1, b1, ic, hE, hic, hH⟩ := loop_last M6.get hexp t binp x.length x hF m1 hn0 hI1
    have hszH : H.get.size ≤ 4273995776 := by rw [hH.1, hM6s]; exact hsz
    have hstH : t.toNat + 40 ≤ H.get.size := by rw [hH.1, hM6s]; omega
    have hNN2 : (x.length.toUInt32.add x.length.toUInt32).toNat = 2 * x.length := by
      rw [u32_toNat_add (by rw [hNN]; omega), hNN]; omega
    have hHt : rdRaw H.get t 4 = x.length.toUInt32.add x.length.toUInt32 := by
      rw [← hM6t]
      show rdBytes H.get t 4 = rdBytes M6.get t 4
      exact rdBytes4_congr (by omega) (by rw [hM6s]; omega)
        (fun k hk => by rw [hH.2 _ (by rw [hM6s]; omega), if_neg (by omega)])
    have q1 := pst (e1 H hexp c1 d1 b1 t x.length.toUInt32 binp x.length.toUInt32
      (subF 4 x.length.toUInt32 x.length.toUInt32 0).2 ic hszH hstH hap) (by omega) (tf_efl _) (neHalt _ (by decide))
    rw [hHt] at q1
    have q2 := pst (e2 H hexp (x.length.toUInt32.add x.length.toUInt32) d1 b1 t x.length.toUInt32 binp
      x.length.toUInt32 (subF 4 x.length.toUInt32 x.length.toUInt32 0).2 (ic + 1) hszH hstH hap)
      (icb 1 (by omega)) (tf_efl _) (neHalt _ (by decide))
    have e2 : (ic + 1 + 1).toNat = ic.toNat + 2 := ic_chain 2 (by omega)
    obtain ⟨Mf, ic', pt, hMg⟩ := tail G t c.regs.ebp c.regs.ebx c.regs.edi c.regs.esi c.regs.eax ok1 ok2 ok3 ok4 ok5
      hszG hst hap H hexp (x.length.toUInt32.add x.length.toUInt32) d1 b1 x.length.toUInt32 binp x.length.toUInt32
      (subF 4 x.length.toUInt32 x.length.toUInt32 0).2 (ic + 1 + 1) (by rw [hH.1, hM6s, hGs])
      (fun j h1 h2 => by rw [hH.2 j (by rw [hM6s]; omega), if_neg (by omega), hM6f j h1])
      (by rw [hNN2]; omega) (by rw [hNN2]; omega) (by rw [hNN2]; omega) (by omega)
    have pr := hpre.append (hL.append (hE.append (q1.append (q2.append pt))))
    rw [hret] at pr
    have hpc : (hexp.add (x.length.toUInt32.add x.length.toUInt32)).toNat = hexp.toNat + 2 * x.length := by
      rw [u32_toNat_add (by rw [hNN2]; omega), hNN2]
    refine ⟨_, pr.cast ?_, ⟨rfl, hesp.symm, efl_DF _⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨?_, ?_⟩, rfl, ?_⟩
    · rw [path, if_neg (by omega)]
      simp only [seg1Path, seg2aPath, seg2bPath, seg3Path, exitPath, List.append_assoc, List.cons_append,
        List.nil_append]
    · show Mf.get.size = c.mem.size
      rw [hMg, size_wrBytes, hH.1, hM6s]
    · intro a ha hW hs
      have ha' : a.toNat < c.mem.size := ha
      have hd := hstack a hs
      have hW' : ¬(hexp.toNat ≤ a.toNat ∧ a.toNat < hexp.toNat + (2 * x.length + 1)) := fun h => hW (inRange_iff.2 h)
      show memByte Mf.get a = memByte c.mem a
      rw [hMg, memByte_wrBytes1 (by rw [hpc, hH.1, hM6s]; omega) (by rw [hH.1, hM6s]; exact ha'),
        if_neg (hi_ne (by rw [hpc]; omega)), memByte_def (by rw [hH.1, hM6s]; exact ha'), memByte_def ha',
        hH.2 _ (by rw [hM6s]; exact ha'), if_neg (by omega), hM6g _ hd]
    · show memBytes Mf.get hexp (2 * x.length + 1) = hex x ++ [0]
      apply memBytes_eq_iff.2
      refine ⟨by simp [hex_length], fun i hi => ?_⟩
      have hi' : i < 2 * x.length + 1 := by simp [hex_length] at hi; omega
      have hpi : (hexp + i.toUInt32).toNat = hexp.toNat + i := toNat_add_of_lt (by omega)
      rw [hMg, memByte_wrBytes1 (by rw [hpc, hH.1, hM6s]; omega) (by rw [hpi, hH.1, hM6s]; omega)]
      by_cases hi2 : i = 2 * x.length
      · rw [if_pos (UInt32.toNat_inj.1 (by rw [hpi, hpc]; omega)),
          List.getElem_append_right (by rw [hex_length]; omega)]
        simp [hex_length, hi2]
      · rw [if_neg (hi_ne (by rw [hpi, hpc]; omega)), memByte_def (by rw [hpi, hH.1, hM6s]; omega),
          hH.2 _ (by rw [hpi, hM6s]; omega), hpi, if_pos (by omega),
          List.getElem_append_left (by rw [hex_length]; omega), show hexp.toNat + i - hexp.toNat = i by omega,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hex_length]; omega)]
        rfl

theorem _root_.Sodium.Proofs.bin2hex_correct : Sodium.Utils.bin2hex_correct := by
  intro c hexp binp cap x h
  obtain ⟨r, hp, hR, hC, hP, hQ⟩ := run c hexp binp cap x h
  exact Returns.intro hp.run hR hC hP hQ

theorem _root_.Sodium.Proofs.bin2hex_constant_time : Sodium.Utils.bin2hex_constant_time := by
  intro c c' hexp binp cap x x' hl h h'
  obtain ⟨r, hp, hR, -⟩ := run c hexp binp cap x h
  obtain ⟨r', hp', hR', -⟩ := run c' hexp binp cap x' h'
  rw [hl] at hp
  exact SameTraceG.of_prun hp hp' hR.1 hR'.1

end Sodium.Proofs.HexEnc
