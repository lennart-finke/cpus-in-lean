import Solutions.OpensslX25519.AddSubRun
import Solutions.OpensslX25519.AddSubMath
import Solutions.OpensslX25519.Peel
import Solutions.Exec.Alu
/-!
# `fe_add` and `fe_sub` are correct

The run of each function is put together from the pieces of `AddSubRun` (prologue, ten limbs,
epilogue); the memory after the run is the chain of its eleven stores over the caller's memory.
Loads through the chain (`peel`) give the limbs the function read and wrote, and
`fe_add_math`/`fe_sub_math` do the arithmetic.
-/
namespace Solutions.OpensslX25519
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

theorem rdRaw_def (mem : ByteArray) (a n : UInt32) : rdRaw mem a n = rdBytes mem a n := rfl

/- Loads stay folded when goals are matched against the states of a run. -/
attribute [local irreducible] rdRaw

theorem inRange_nat {lo : UInt32} {n : Nat} {a : UInt32} (h : ¬ InRange lo n a) :
    a.toNat < lo.toNat ∨ lo.toNat + n ≤ a.toNat := by
  unfold InRange at h
  rw [UInt32.le_iff_toNat_le] at h
  omega

theorem sp_sub_toNat {sp : UInt32} (h : 2048 ≤ sp.toNat) : (sp - (2048 : Nat).toUInt32).toNat = sp.toNat - 2048 := by
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
  simp

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem fe_add_ok : fe_add_correct := by
  intro c h f g fv gv hc hfin hgin
  have hF0 := fieldFacts hc
  obtain ⟨hcall, hecx, hedx, -, -, -, -, -, hfm, hgm⟩ := hc
  let G : XMem := xmem hcall
  have hS : G.get.size = c.mem.size := rfl
  have F0 : FieldFacts G.get.size c.sp.toNat h.toNat f.toNat g.toNat := hF0
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ := id F0
  have hargE : rdRaw G.get (UInt32.add (UInt32.sub c.sp 4) 8) 4 = g := by
    have := calls_arg hcall 0 (by simp)
    rw [show UInt32.add (UInt32.sub c.sp 4) 8 = c.sp + 4 * (0 + 1 : Nat).toUInt32 by
      apply UInt32.toNat_inj.1
      have := c.sp.toNat_lt
      simp only [toNat_uadd, toNat_usub, UInt32.toNat_add, UInt32.toNat_mul]; simp; omega]
    rw [rdRaw_def]; exact this
  have hret : rdRaw G.get (UInt32.add (UInt32.sub c.sp 4) 4) 4 = Image.sym_halt := by
    rw [show UInt32.add (UInt32.sub c.sp 4) 4 = c.sp by
      apply UInt32.toNat_inj.1
      have := c.sp.toNat_lt
      simp only [toNat_uadd, toNat_usub]; simp; omega]
    rw [rdRaw_def]; exact calls_ret hcall
  have e0 : c.enter Image.sym_fe_add = St.m ⟨G.get, c.regs.eax, h, f, c.regs.ebx, c.sp, c.regs.ebp,
      c.regs.esi, c.regs.edi, Image.sym_fe_add, efl c.regs.flags, 0⟩ := by
    rw [← hecx, ← hedx]; rfl
  rw [e0]
  have ok0 := storeOk_sp G F0
  let N1 := CodeMem.wr4 G (UInt32.sub c.sp 4) c.regs.esi ok0
  have s1 : N1.get.size = G.get.size := wr4_size _ _ _ _
  have p := add_pro G c.regs.eax c.regs.ebx c.sp c.regs.ebp c.regs.esi c.regs.edi c.regs.flags h f g
    (⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok0
  rw [hargE] at p
  have ok1 := storeOk_h0 N1 rfl (FieldFacts.size_eq s1 F0)
  let r0 := addF 4 (rdRaw N1.get g 4) (rdRaw N1.get f 4) 0
  let N2 := CodeMem.wr4 N1 h r0.1 ok1
  have s2 : N2.get.size = G.get.size := (wr4_size _ _ _ _).trans s1

  have ok2 := storeOk_h N2 rfl (FieldFacts.size_eq s2 F0) 4 (by decide)
  let r1 := addF 4 (rdRaw N2.get (UInt32.add g 4) 4) (rdRaw N2.get (UInt32.add f 4) 4) 0
  let N3 := CodeMem.wr4 N2 (UInt32.add h 4) r1.1 ok2
  have s3 : N3.get.size = G.get.size := (wr4_size _ _ _ _).trans s2

  have ok3 := storeOk_h N3 rfl (FieldFacts.size_eq s3 F0) 8 (by decide)
  let r2 := addF 4 (rdRaw N3.get (UInt32.add g 8) 4) (rdRaw N3.get (UInt32.add f 8) 4) 0
  let N4 := CodeMem.wr4 N3 (UInt32.add h 8) r2.1 ok3
  have s4 : N4.get.size = G.get.size := (wr4_size _ _ _ _).trans s3

  have ok4 := storeOk_h N4 rfl (FieldFacts.size_eq s4 F0) 12 (by decide)
  let r3 := addF 4 (rdRaw N4.get (UInt32.add g 12) 4) (rdRaw N4.get (UInt32.add f 12) 4) 0
  let N5 := CodeMem.wr4 N4 (UInt32.add h 12) r3.1 ok4
  have s5 : N5.get.size = G.get.size := (wr4_size _ _ _ _).trans s4

  have ok5 := storeOk_h N5 rfl (FieldFacts.size_eq s5 F0) 16 (by decide)
  let r4 := addF 4 (rdRaw N5.get (UInt32.add g 16) 4) (rdRaw N5.get (UInt32.add f 16) 4) 0
  let N6 := CodeMem.wr4 N5 (UInt32.add h 16) r4.1 ok5
  have s6 : N6.get.size = G.get.size := (wr4_size _ _ _ _).trans s5

  have ok6 := storeOk_h N6 rfl (FieldFacts.size_eq s6 F0) 20 (by decide)
  let r5 := addF 4 (rdRaw N6.get (UInt32.add g 20) 4) (rdRaw N6.get (UInt32.add f 20) 4) 0
  let N7 := CodeMem.wr4 N6 (UInt32.add h 20) r5.1 ok6
  have s7 : N7.get.size = G.get.size := (wr4_size _ _ _ _).trans s6

  have ok7 := storeOk_h N7 rfl (FieldFacts.size_eq s7 F0) 24 (by decide)
  let r6 := addF 4 (rdRaw N7.get (UInt32.add g 24) 4) (rdRaw N7.get (UInt32.add f 24) 4) 0
  let N8 := CodeMem.wr4 N7 (UInt32.add h 24) r6.1 ok7
  have s8 : N8.get.size = G.get.size := (wr4_size _ _ _ _).trans s7

  have ok8 := storeOk_h N8 rfl (FieldFacts.size_eq s8 F0) 28 (by decide)
  let r7 := addF 4 (rdRaw N8.get (UInt32.add g 28) 4) (rdRaw N8.get (UInt32.add f 28) 4) 0
  let N9 := CodeMem.wr4 N8 (UInt32.add h 28) r7.1 ok8
  have s9 : N9.get.size = G.get.size := (wr4_size _ _ _ _).trans s8

  have ok9 := storeOk_h N9 rfl (FieldFacts.size_eq s9 F0) 32 (by decide)
  let r8 := addF 4 (rdRaw N9.get (UInt32.add g 32) 4) (rdRaw N9.get (UInt32.add f 32) 4) 0
  let N10 := CodeMem.wr4 N9 (UInt32.add h 32) r8.1 ok9
  have s10 : N10.get.size = G.get.size := (wr4_size _ _ _ _).trans s9

  have ok10 := storeOk_h N10 rfl (FieldFacts.size_eq s10 F0) 36 (by decide)
  let r9 := addF 4 (rdRaw N10.get (UInt32.add g 36) 4) (rdRaw N10.get (UInt32.add f 36) 4) 0
  let N11 := CodeMem.wr4 N10 (UInt32.add h 36) r9.1 ok10
  have s11 : N11.get.size = G.get.size := (wr4_size _ _ _ _).trans s10

  refine Returns.intro (Run.trans (run_of_runOk p) (Run.trans (run_of_runOk (add_limb0 N1 c.regs.ebx c.sp c.regs.ebp c.regs.esi c.regs.edi c.regs.flags h f g
    (FieldFacts.size_eq s1 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok1))
    (Run.trans (run_of_runOk (add_limb1 N2 c.regs.ebx c.sp c.regs.ebp r0.1 c.regs.edi r0.2 h f g
    (FieldFacts.size_eq s2 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok2))
    (Run.trans (run_of_runOk (add_limb2 N3 c.regs.ebx c.sp c.regs.ebp r1.1 c.regs.edi r1.2 h f g
    (FieldFacts.size_eq s3 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok3))
    (Run.trans (run_of_runOk (add_limb3 N4 c.regs.ebx c.sp c.regs.ebp r2.1 c.regs.edi r2.2 h f g
    (FieldFacts.size_eq s4 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok4))
    (Run.trans (run_of_runOk (add_limb4 N5 c.regs.ebx c.sp c.regs.ebp r3.1 c.regs.edi r3.2 h f g
    (FieldFacts.size_eq s5 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok5))
    (Run.trans (run_of_runOk (add_limb5 N6 c.regs.ebx c.sp c.regs.ebp r4.1 c.regs.edi r4.2 h f g
    (FieldFacts.size_eq s6 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok6))
    (Run.trans (run_of_runOk (add_limb6 N7 c.regs.ebx c.sp c.regs.ebp r5.1 c.regs.edi r5.2 h f g
    (FieldFacts.size_eq s7 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok7))
    (Run.trans (run_of_runOk (add_limb7 N8 c.regs.ebx c.sp c.regs.ebp r6.1 c.regs.edi r6.2 h f g
    (FieldFacts.size_eq s8 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok8))
    (Run.trans (run_of_runOk (add_limb8 N9 c.regs.ebx c.sp c.regs.ebp r7.1 c.regs.edi r7.2 h f g
    (FieldFacts.size_eq s9 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok9))
    (Run.trans (run_of_runOk (add_limb9 N10 c.regs.ebx c.sp c.regs.ebp r8.1 c.regs.edi r8.2 h f g
    (FieldFacts.size_eq s10 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok10))
    (run_of_runOk (add_epi N11 r9.1 c.regs.ebx f c.sp c.regs.ebp r8.1 c.regs.edi r9.2 h f g (FieldFacts.size_eq s11 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩)))))))))))))) ?_ ?_ ?_ ?_
  all_goals clear p
  · refine ⟨?_, ?_, ?_⟩
    · show (rdRaw N11.get (UInt32.add (UInt32.sub c.sp 4) 4) 4 == Image.sym_halt && _ && _) = true
      rw [rd_sb N10 s10 (sp := c.sp.toNat) (t := 4) (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at_s4 f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N9 s9 (sp := c.sp.toNat) (t := 4) (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_s4 f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N8 s8 (sp := c.sp.toNat) (t := 4) (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_s4 f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N7 s7 (sp := c.sp.toNat) (t := 4) (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_s4 f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N6 s6 (sp := c.sp.toNat) (t := 4) (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_s4 f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N5 s5 (sp := c.sp.toNat) (t := 4) (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_s4 f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N4 s4 (sp := c.sp.toNat) (t := 4) (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_s4 f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N3 s3 (sp := c.sp.toNat) (t := 4) (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_s4 f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N2 s2 (sp := c.sp.toNat) (t := 4) (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_s4 f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N1 s1 (sp := c.sp.toNat) (t := 4) (at0 h) (at_s4 f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_ss G rfl (at_s f3) (at_s4 f3) f3 f4]
      rw [hret]; rfl
    · exact esp_ret f3
    · exact efl_DF _
  · refine ⟨rfl, ?_, rfl, rfl⟩
    show rdRaw N11.get (UInt32.sub c.sp 4) 4 = c.regs.esi
    rw [rd_sb N10 s10 (sp := c.sp.toNat) (t := 0) (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at_s f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N9 s9 (sp := c.sp.toNat) (t := 0) (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_s f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N8 s8 (sp := c.sp.toNat) (t := 0) (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_s f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N7 s7 (sp := c.sp.toNat) (t := 0) (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_s f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N6 s6 (sp := c.sp.toNat) (t := 0) (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_s f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N5 s5 (sp := c.sp.toNat) (t := 0) (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_s f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N4 s4 (sp := c.sp.toNat) (t := 0) (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_s f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N3 s3 (sp := c.sp.toNat) (t := 0) (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_s f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N2 s2 (sp := c.sp.toNat) (t := 0) (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_s f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N1 s1 (sp := c.sp.toNat) (t := 0) (at0 h) (at_s f3) (by decide) (by decide) F0.h_stk f3 f4,
        rdRaw_wr4_same _ _ _ _ rfl]
  · refine ⟨?_, fun x hx hW hS => ?_⟩
    · dsimp only [St.m]; exact s11
    dsimp only [St.m] at hx hS ⊢
    have hW' := not_inRange_h hW
    have hS' := not_inRange_stack f3 hS
    rw [mb_b N10 s10 (at_b rfl F0.h_mem F0.ram 36 (by decide)) (by decide) hx hW',
        mb_b N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (by decide) hx hW',
        mb_b N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (by decide) hx hW',
        mb_b N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (by decide) hx hW',
        mb_b N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (by decide) hx hW',
        mb_b N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (by decide) hx hW',
        mb_b N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (by decide) hx hW',
        mb_b N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (by decide) hx hW',
        mb_b N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (by decide) hx hW',
        mb_b N1 s1 (at0 h) (by decide) hx hW',
        mb_s G rfl (at_s f3) hx f3 hS']
  · dsimp only [St.m, wordsAt]
    have w0 : rdRaw N11.get h 4 = rdRaw G.get g 4 + rdRaw G.get f 4 := by
      rw [rd_bb N10 s10 (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at0 h) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at0 h) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at0 h) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at0 h) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at0 h) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at0 h) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at0 h) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at0 h) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at0 h) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rdRaw_wr4_same _ _ _ _ rfl]
      rw [addF_fst]
      rw [rd_bs G rfl (at_s f3) (at0 g) F0.g_mem F0.g_stk f3 (by decide),
          rd_bs G rfl (at_s f3) (at0 f) F0.f_mem F0.f_stk f3 (by decide)]
    have w1 : rdRaw N11.get (UInt32.add h 4) 4 = rdRaw G.get (UInt32.add g 4) 4 + rdRaw G.get (UInt32.add f 4) 4 := by
      rw [rd_bb N10 s10 (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at_b rfl F0.h_mem F0.ram 4 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_b rfl F0.h_mem F0.ram 4 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_b rfl F0.h_mem F0.ram 4 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.h_mem F0.ram 4 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.h_mem F0.ram 4 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.h_mem F0.ram 4 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.h_mem F0.ram 4 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.h_mem F0.ram 4 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rdRaw_wr4_same _ _ _ _ rfl]
      rw [addF_fst]
      rw [rd_bb N1 s1 (at0 h) (at_b rfl F0.g_mem F0.ram 4 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.g_mem F0.ram 4 (by decide)) F0.g_mem F0.g_stk f3 (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.f_mem F0.ram 4 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.f_mem F0.ram 4 (by decide)) F0.f_mem F0.f_stk f3 (by decide)]
    have w2 : rdRaw N11.get (UInt32.add h 8) 4 = rdRaw G.get (UInt32.add g 8) 4 + rdRaw G.get (UInt32.add f 8) 4 := by
      rw [rd_bb N10 s10 (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at_b rfl F0.h_mem F0.ram 8 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_b rfl F0.h_mem F0.ram 8 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_b rfl F0.h_mem F0.ram 8 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.h_mem F0.ram 8 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.h_mem F0.ram 8 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.h_mem F0.ram 8 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.h_mem F0.ram 8 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rdRaw_wr4_same _ _ _ _ rfl]
      rw [addF_fst]
      rw [rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.g_mem F0.ram 8 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.g_mem F0.ram 8 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.g_mem F0.ram 8 (by decide)) F0.g_mem F0.g_stk f3 (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.f_mem F0.ram 8 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.f_mem F0.ram 8 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.f_mem F0.ram 8 (by decide)) F0.f_mem F0.f_stk f3 (by decide)]
    have w3 : rdRaw N11.get (UInt32.add h 12) 4 = rdRaw G.get (UInt32.add g 12) 4 + rdRaw G.get (UInt32.add f 12) 4 := by
      rw [rd_bb N10 s10 (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at_b rfl F0.h_mem F0.ram 12 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_b rfl F0.h_mem F0.ram 12 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_b rfl F0.h_mem F0.ram 12 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.h_mem F0.ram 12 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.h_mem F0.ram 12 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.h_mem F0.ram 12 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rdRaw_wr4_same _ _ _ _ rfl]
      rw [addF_fst]
      rw [rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.g_mem F0.ram 12 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.g_mem F0.ram 12 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.g_mem F0.ram 12 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.g_mem F0.ram 12 (by decide)) F0.g_mem F0.g_stk f3 (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.f_mem F0.ram 12 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.f_mem F0.ram 12 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.f_mem F0.ram 12 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.f_mem F0.ram 12 (by decide)) F0.f_mem F0.f_stk f3 (by decide)]
    have w4 : rdRaw N11.get (UInt32.add h 16) 4 = rdRaw G.get (UInt32.add g 16) 4 + rdRaw G.get (UInt32.add f 16) 4 := by
      rw [rd_bb N10 s10 (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at_b rfl F0.h_mem F0.ram 16 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_b rfl F0.h_mem F0.ram 16 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_b rfl F0.h_mem F0.ram 16 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.h_mem F0.ram 16 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.h_mem F0.ram 16 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rdRaw_wr4_same _ _ _ _ rfl]
      rw [addF_fst]
      rw [rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.g_mem F0.ram 16 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.g_mem F0.ram 16 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.g_mem F0.ram 16 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.g_mem F0.ram 16 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.g_mem F0.ram 16 (by decide)) F0.g_mem F0.g_stk f3 (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.f_mem F0.ram 16 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.f_mem F0.ram 16 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.f_mem F0.ram 16 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.f_mem F0.ram 16 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.f_mem F0.ram 16 (by decide)) F0.f_mem F0.f_stk f3 (by decide)]
    have w5 : rdRaw N11.get (UInt32.add h 20) 4 = rdRaw G.get (UInt32.add g 20) 4 + rdRaw G.get (UInt32.add f 20) 4 := by
      rw [rd_bb N10 s10 (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at_b rfl F0.h_mem F0.ram 20 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_b rfl F0.h_mem F0.ram 20 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_b rfl F0.h_mem F0.ram 20 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.h_mem F0.ram 20 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rdRaw_wr4_same _ _ _ _ rfl]
      rw [addF_fst]
      rw [rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.g_mem F0.ram 20 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.g_mem F0.ram 20 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.g_mem F0.ram 20 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.g_mem F0.ram 20 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.g_mem F0.ram 20 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.g_mem F0.ram 20 (by decide)) F0.g_mem F0.g_stk f3 (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.f_mem F0.ram 20 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.f_mem F0.ram 20 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.f_mem F0.ram 20 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.f_mem F0.ram 20 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.f_mem F0.ram 20 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.f_mem F0.ram 20 (by decide)) F0.f_mem F0.f_stk f3 (by decide)]
    have w6 : rdRaw N11.get (UInt32.add h 24) 4 = rdRaw G.get (UInt32.add g 24) 4 + rdRaw G.get (UInt32.add f 24) 4 := by
      rw [rd_bb N10 s10 (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at_b rfl F0.h_mem F0.ram 24 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_b rfl F0.h_mem F0.ram 24 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_b rfl F0.h_mem F0.ram 24 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rdRaw_wr4_same _ _ _ _ rfl]
      rw [addF_fst]
      rw [rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.g_mem F0.ram 24 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.g_mem F0.ram 24 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.g_mem F0.ram 24 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.g_mem F0.ram 24 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.g_mem F0.ram 24 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.g_mem F0.ram 24 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.g_mem F0.ram 24 (by decide)) F0.g_mem F0.g_stk f3 (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.f_mem F0.ram 24 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.f_mem F0.ram 24 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.f_mem F0.ram 24 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.f_mem F0.ram 24 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.f_mem F0.ram 24 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.f_mem F0.ram 24 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.f_mem F0.ram 24 (by decide)) F0.f_mem F0.f_stk f3 (by decide)]
    have w7 : rdRaw N11.get (UInt32.add h 28) 4 = rdRaw G.get (UInt32.add g 28) 4 + rdRaw G.get (UInt32.add f 28) 4 := by
      rw [rd_bb N10 s10 (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at_b rfl F0.h_mem F0.ram 28 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_b rfl F0.h_mem F0.ram 28 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rdRaw_wr4_same _ _ _ _ rfl]
      rw [addF_fst]
      rw [rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.g_mem F0.ram 28 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.g_mem F0.ram 28 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.g_mem F0.ram 28 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.g_mem F0.ram 28 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.g_mem F0.ram 28 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.g_mem F0.ram 28 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.g_mem F0.ram 28 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.g_mem F0.ram 28 (by decide)) F0.g_mem F0.g_stk f3 (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.f_mem F0.ram 28 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.f_mem F0.ram 28 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.f_mem F0.ram 28 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.f_mem F0.ram 28 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.f_mem F0.ram 28 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.f_mem F0.ram 28 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.f_mem F0.ram 28 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.f_mem F0.ram 28 (by decide)) F0.f_mem F0.f_stk f3 (by decide)]
    have w8 : rdRaw N11.get (UInt32.add h 32) 4 = rdRaw G.get (UInt32.add g 32) 4 + rdRaw G.get (UInt32.add f 32) 4 := by
      rw [rd_bb N10 s10 (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at_b rfl F0.h_mem F0.ram 32 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rdRaw_wr4_same _ _ _ _ rfl]
      rw [addF_fst]
      rw [rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_b rfl F0.g_mem F0.ram 32 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.g_mem F0.ram 32 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.g_mem F0.ram 32 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.g_mem F0.ram 32 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.g_mem F0.ram 32 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.g_mem F0.ram 32 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.g_mem F0.ram 32 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.g_mem F0.ram 32 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.g_mem F0.ram 32 (by decide)) F0.g_mem F0.g_stk f3 (by decide),
          rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_b rfl F0.f_mem F0.ram 32 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.f_mem F0.ram 32 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.f_mem F0.ram 32 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.f_mem F0.ram 32 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.f_mem F0.ram 32 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.f_mem F0.ram 32 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.f_mem F0.ram 32 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.f_mem F0.ram 32 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.f_mem F0.ram 32 (by decide)) F0.f_mem F0.f_stk f3 (by decide)]
    have w9 : rdRaw N11.get (UInt32.add h 36) 4 = rdRaw G.get (UInt32.add g 36) 4 + rdRaw G.get (UInt32.add f 36) 4 := by
      rw [rdRaw_wr4_same _ _ _ _ rfl]
      rw [addF_fst]
      rw [rd_bb N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_b rfl F0.g_mem F0.ram 36 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_b rfl F0.g_mem F0.ram 36 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.g_mem F0.ram 36 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.g_mem F0.ram 36 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.g_mem F0.ram 36 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.g_mem F0.ram 36 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.g_mem F0.ram 36 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.g_mem F0.ram 36 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.g_mem F0.ram 36 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.g_mem F0.ram 36 (by decide)) F0.g_mem F0.g_stk f3 (by decide),
          rd_bb N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_b rfl F0.f_mem F0.ram 36 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_b rfl F0.f_mem F0.ram 36 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.f_mem F0.ram 36 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.f_mem F0.ram 36 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.f_mem F0.ram 36 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.f_mem F0.ram 36 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.f_mem F0.ram 36 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.f_mem F0.ram 36 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.f_mem F0.ram 36 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.f_mem F0.ram 36 (by decide)) F0.f_mem F0.f_stk f3 (by decide)]
    have hwi : ∀ i, i < 10 → (memWords N11.get h 10)[i]! = gv[i]! + fv[i]! := by
      intro i hi
      rw [← hfm, ← hgm, memWords_getElem! _ _ _ _ hi, memWords_getElem! _ _ _ _ hi,
        memWords_getElem! _ _ _ _ hi]
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · simp only [Nat.toUInt32_eq, UInt32.reduceOfNat, UInt32.reduceMul, UInt32.add_zero]
        first | exact w0 | exact w1 | exact w2 | exact w3 | exact w4 | exact w5 | exact w6 | exact w7 | exact w8 | exact w9
    exact fe_add_math fv gv _ hfin hgin (by simp [memWords]) hwi

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem fe_sub_ok : fe_sub_correct := by
  intro c h f g fv gv hc hfin hgin
  have hF0 := fieldFacts hc
  obtain ⟨hcall, hecx, hedx, -, -, -, -, -, hfm, hgm⟩ := hc
  let G : XMem := xmem hcall
  have hS : G.get.size = c.mem.size := rfl
  have F0 : FieldFacts G.get.size c.sp.toNat h.toNat f.toNat g.toNat := hF0
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ := id F0
  have hargE : rdRaw G.get (UInt32.add (UInt32.sub c.sp 4) 8) 4 = g := by
    have := calls_arg hcall 0 (by simp)
    rw [show UInt32.add (UInt32.sub c.sp 4) 8 = c.sp + 4 * (0 + 1 : Nat).toUInt32 by
      apply UInt32.toNat_inj.1
      have := c.sp.toNat_lt
      simp only [toNat_uadd, toNat_usub, UInt32.toNat_add, UInt32.toNat_mul]; simp; omega]
    rw [rdRaw_def]; exact this
  have hret : rdRaw G.get (UInt32.add (UInt32.sub c.sp 4) 4) 4 = Image.sym_halt := by
    rw [show UInt32.add (UInt32.sub c.sp 4) 4 = c.sp by
      apply UInt32.toNat_inj.1
      have := c.sp.toNat_lt
      simp only [toNat_uadd, toNat_usub]; simp; omega]
    rw [rdRaw_def]; exact calls_ret hcall
  have e0 : c.enter Image.sym_fe_sub = St.m ⟨G.get, c.regs.eax, h, f, c.regs.ebx, c.sp, c.regs.ebp,
      c.regs.esi, c.regs.edi, Image.sym_fe_sub, efl c.regs.flags, 0⟩ := by
    rw [← hecx, ← hedx]; rfl
  rw [e0]
  have ok0 := storeOk_sp G F0
  let N1 := CodeMem.wr4 G (UInt32.sub c.sp 4) c.regs.esi ok0
  have s1 : N1.get.size = G.get.size := wr4_size _ _ _ _
  have p := sub_pro G c.regs.eax c.regs.ebx c.sp c.regs.ebp c.regs.esi c.regs.edi c.regs.flags h f g
    (⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok0
  rw [hargE] at p
  have ok1 := storeOk_h0 N1 rfl (FieldFacts.size_eq s1 F0)
  let r0 := subF 4 (rdRaw N1.get f 4) (rdRaw N1.get g 4) 0
  let N2 := CodeMem.wr4 N1 h r0.1 ok1
  have s2 : N2.get.size = G.get.size := (wr4_size _ _ _ _).trans s1

  have ok2 := storeOk_h N2 rfl (FieldFacts.size_eq s2 F0) 4 (by decide)
  let r1 := subF 4 (rdRaw N2.get (UInt32.add f 4) 4) (rdRaw N2.get (UInt32.add g 4) 4) 0
  let N3 := CodeMem.wr4 N2 (UInt32.add h 4) r1.1 ok2
  have s3 : N3.get.size = G.get.size := (wr4_size _ _ _ _).trans s2

  have ok3 := storeOk_h N3 rfl (FieldFacts.size_eq s3 F0) 8 (by decide)
  let r2 := subF 4 (rdRaw N3.get (UInt32.add f 8) 4) (rdRaw N3.get (UInt32.add g 8) 4) 0
  let N4 := CodeMem.wr4 N3 (UInt32.add h 8) r2.1 ok3
  have s4 : N4.get.size = G.get.size := (wr4_size _ _ _ _).trans s3

  have ok4 := storeOk_h N4 rfl (FieldFacts.size_eq s4 F0) 12 (by decide)
  let r3 := subF 4 (rdRaw N4.get (UInt32.add f 12) 4) (rdRaw N4.get (UInt32.add g 12) 4) 0
  let N5 := CodeMem.wr4 N4 (UInt32.add h 12) r3.1 ok4
  have s5 : N5.get.size = G.get.size := (wr4_size _ _ _ _).trans s4

  have ok5 := storeOk_h N5 rfl (FieldFacts.size_eq s5 F0) 16 (by decide)
  let r4 := subF 4 (rdRaw N5.get (UInt32.add f 16) 4) (rdRaw N5.get (UInt32.add g 16) 4) 0
  let N6 := CodeMem.wr4 N5 (UInt32.add h 16) r4.1 ok5
  have s6 : N6.get.size = G.get.size := (wr4_size _ _ _ _).trans s5

  have ok6 := storeOk_h N6 rfl (FieldFacts.size_eq s6 F0) 20 (by decide)
  let r5 := subF 4 (rdRaw N6.get (UInt32.add f 20) 4) (rdRaw N6.get (UInt32.add g 20) 4) 0
  let N7 := CodeMem.wr4 N6 (UInt32.add h 20) r5.1 ok6
  have s7 : N7.get.size = G.get.size := (wr4_size _ _ _ _).trans s6

  have ok7 := storeOk_h N7 rfl (FieldFacts.size_eq s7 F0) 24 (by decide)
  let r6 := subF 4 (rdRaw N7.get (UInt32.add f 24) 4) (rdRaw N7.get (UInt32.add g 24) 4) 0
  let N8 := CodeMem.wr4 N7 (UInt32.add h 24) r6.1 ok7
  have s8 : N8.get.size = G.get.size := (wr4_size _ _ _ _).trans s7

  have ok8 := storeOk_h N8 rfl (FieldFacts.size_eq s8 F0) 28 (by decide)
  let r7 := subF 4 (rdRaw N8.get (UInt32.add f 28) 4) (rdRaw N8.get (UInt32.add g 28) 4) 0
  let N9 := CodeMem.wr4 N8 (UInt32.add h 28) r7.1 ok8
  have s9 : N9.get.size = G.get.size := (wr4_size _ _ _ _).trans s8

  have ok9 := storeOk_h N9 rfl (FieldFacts.size_eq s9 F0) 32 (by decide)
  let r8 := subF 4 (rdRaw N9.get (UInt32.add f 32) 4) (rdRaw N9.get (UInt32.add g 32) 4) 0
  let N10 := CodeMem.wr4 N9 (UInt32.add h 32) r8.1 ok9
  have s10 : N10.get.size = G.get.size := (wr4_size _ _ _ _).trans s9

  have ok10 := storeOk_h N10 rfl (FieldFacts.size_eq s10 F0) 36 (by decide)
  let r9 := subF 4 (rdRaw N10.get (UInt32.add f 36) 4) (rdRaw N10.get (UInt32.add g 36) 4) 0
  let N11 := CodeMem.wr4 N10 (UInt32.add h 36) r9.1 ok10
  have s11 : N11.get.size = G.get.size := (wr4_size _ _ _ _).trans s10

  refine Returns.intro (Run.trans (run_of_runOk p) (Run.trans (run_of_runOk (sub_limb0 N1 c.regs.ebx c.sp c.regs.ebp c.regs.esi c.regs.edi c.regs.flags h f g
    (FieldFacts.size_eq s1 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok1))
    (Run.trans (run_of_runOk (sub_limb1 N2 c.regs.ebx c.sp c.regs.ebp r0.1 c.regs.edi r0.2 h f g
    (FieldFacts.size_eq s2 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok2))
    (Run.trans (run_of_runOk (sub_limb2 N3 c.regs.ebx c.sp c.regs.ebp r1.1 c.regs.edi r1.2 h f g
    (FieldFacts.size_eq s3 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok3))
    (Run.trans (run_of_runOk (sub_limb3 N4 c.regs.ebx c.sp c.regs.ebp r2.1 c.regs.edi r2.2 h f g
    (FieldFacts.size_eq s4 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok4))
    (Run.trans (run_of_runOk (sub_limb4 N5 c.regs.ebx c.sp c.regs.ebp r3.1 c.regs.edi r3.2 h f g
    (FieldFacts.size_eq s5 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok5))
    (Run.trans (run_of_runOk (sub_limb5 N6 c.regs.ebx c.sp c.regs.ebp r4.1 c.regs.edi r4.2 h f g
    (FieldFacts.size_eq s6 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok6))
    (Run.trans (run_of_runOk (sub_limb6 N7 c.regs.ebx c.sp c.regs.ebp r5.1 c.regs.edi r5.2 h f g
    (FieldFacts.size_eq s7 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok7))
    (Run.trans (run_of_runOk (sub_limb7 N8 c.regs.ebx c.sp c.regs.ebp r6.1 c.regs.edi r6.2 h f g
    (FieldFacts.size_eq s8 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok8))
    (Run.trans (run_of_runOk (sub_limb8 N9 c.regs.ebx c.sp c.regs.ebp r7.1 c.regs.edi r7.2 h f g
    (FieldFacts.size_eq s9 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok9))
    (Run.trans (run_of_runOk (sub_limb9 N10 c.regs.ebx c.sp c.regs.ebp r8.1 c.regs.edi r8.2 h f g
    (FieldFacts.size_eq s10 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩) ok10))
    (run_of_runOk (sub_epi N11 g c.regs.ebx r9.1 c.sp c.regs.ebp r8.1 c.regs.edi r9.2 h f g (FieldFacts.size_eq s11 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩)))))))))))))) ?_ ?_ ?_ ?_
  all_goals clear p
  · refine ⟨?_, ?_, ?_⟩
    · show (rdRaw N11.get (UInt32.add (UInt32.sub c.sp 4) 4) 4 == Image.sym_halt && _ && _) = true
      rw [rd_sb N10 s10 (sp := c.sp.toNat) (t := 4) (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at_s4 f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N9 s9 (sp := c.sp.toNat) (t := 4) (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_s4 f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N8 s8 (sp := c.sp.toNat) (t := 4) (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_s4 f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N7 s7 (sp := c.sp.toNat) (t := 4) (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_s4 f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N6 s6 (sp := c.sp.toNat) (t := 4) (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_s4 f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N5 s5 (sp := c.sp.toNat) (t := 4) (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_s4 f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N4 s4 (sp := c.sp.toNat) (t := 4) (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_s4 f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N3 s3 (sp := c.sp.toNat) (t := 4) (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_s4 f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N2 s2 (sp := c.sp.toNat) (t := 4) (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_s4 f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N1 s1 (sp := c.sp.toNat) (t := 4) (at0 h) (at_s4 f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_ss G rfl (at_s f3) (at_s4 f3) f3 f4]
      rw [hret]; rfl
    · exact esp_ret f3
    · exact efl_DF _
  · refine ⟨rfl, ?_, rfl, rfl⟩
    show rdRaw N11.get (UInt32.sub c.sp 4) 4 = c.regs.esi
    rw [rd_sb N10 s10 (sp := c.sp.toNat) (t := 0) (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at_s f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N9 s9 (sp := c.sp.toNat) (t := 0) (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_s f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N8 s8 (sp := c.sp.toNat) (t := 0) (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_s f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N7 s7 (sp := c.sp.toNat) (t := 0) (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_s f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N6 s6 (sp := c.sp.toNat) (t := 0) (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_s f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N5 s5 (sp := c.sp.toNat) (t := 0) (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_s f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N4 s4 (sp := c.sp.toNat) (t := 0) (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_s f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N3 s3 (sp := c.sp.toNat) (t := 0) (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_s f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N2 s2 (sp := c.sp.toNat) (t := 0) (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_s f3) (by decide) (by decide) F0.h_stk f3 f4,
        rd_sb N1 s1 (sp := c.sp.toNat) (t := 0) (at0 h) (at_s f3) (by decide) (by decide) F0.h_stk f3 f4,
        rdRaw_wr4_same _ _ _ _ rfl]
  · refine ⟨?_, fun x hx hW hS => ?_⟩
    · dsimp only [St.m]; exact s11
    dsimp only [St.m] at hx hS ⊢
    have hW' := not_inRange_h hW
    have hS' := not_inRange_stack f3 hS
    rw [mb_b N10 s10 (at_b rfl F0.h_mem F0.ram 36 (by decide)) (by decide) hx hW',
        mb_b N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (by decide) hx hW',
        mb_b N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (by decide) hx hW',
        mb_b N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (by decide) hx hW',
        mb_b N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (by decide) hx hW',
        mb_b N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (by decide) hx hW',
        mb_b N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (by decide) hx hW',
        mb_b N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (by decide) hx hW',
        mb_b N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (by decide) hx hW',
        mb_b N1 s1 (at0 h) (by decide) hx hW',
        mb_s G rfl (at_s f3) hx f3 hS']
  · dsimp only [St.m, wordsAt]
    have w0 : rdRaw N11.get h 4 = rdRaw G.get f 4 - rdRaw G.get g 4 := by
      rw [rd_bb N10 s10 (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at0 h) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at0 h) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at0 h) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at0 h) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at0 h) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at0 h) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at0 h) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at0 h) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at0 h) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rdRaw_wr4_same _ _ _ _ rfl]
      rw [subF_fst]
      rw [rd_bs G rfl (at_s f3) (at0 f) F0.f_mem F0.f_stk f3 (by decide),
          rd_bs G rfl (at_s f3) (at0 g) F0.g_mem F0.g_stk f3 (by decide)]
    have w1 : rdRaw N11.get (UInt32.add h 4) 4 = rdRaw G.get (UInt32.add f 4) 4 - rdRaw G.get (UInt32.add g 4) 4 := by
      rw [rd_bb N10 s10 (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at_b rfl F0.h_mem F0.ram 4 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_b rfl F0.h_mem F0.ram 4 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_b rfl F0.h_mem F0.ram 4 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.h_mem F0.ram 4 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.h_mem F0.ram 4 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.h_mem F0.ram 4 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.h_mem F0.ram 4 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.h_mem F0.ram 4 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rdRaw_wr4_same _ _ _ _ rfl]
      rw [subF_fst]
      rw [rd_bb N1 s1 (at0 h) (at_b rfl F0.f_mem F0.ram 4 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.f_mem F0.ram 4 (by decide)) F0.f_mem F0.f_stk f3 (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.g_mem F0.ram 4 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.g_mem F0.ram 4 (by decide)) F0.g_mem F0.g_stk f3 (by decide)]
    have w2 : rdRaw N11.get (UInt32.add h 8) 4 = rdRaw G.get (UInt32.add f 8) 4 - rdRaw G.get (UInt32.add g 8) 4 := by
      rw [rd_bb N10 s10 (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at_b rfl F0.h_mem F0.ram 8 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_b rfl F0.h_mem F0.ram 8 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_b rfl F0.h_mem F0.ram 8 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.h_mem F0.ram 8 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.h_mem F0.ram 8 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.h_mem F0.ram 8 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.h_mem F0.ram 8 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rdRaw_wr4_same _ _ _ _ rfl]
      rw [subF_fst]
      rw [rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.f_mem F0.ram 8 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.f_mem F0.ram 8 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.f_mem F0.ram 8 (by decide)) F0.f_mem F0.f_stk f3 (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.g_mem F0.ram 8 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.g_mem F0.ram 8 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.g_mem F0.ram 8 (by decide)) F0.g_mem F0.g_stk f3 (by decide)]
    have w3 : rdRaw N11.get (UInt32.add h 12) 4 = rdRaw G.get (UInt32.add f 12) 4 - rdRaw G.get (UInt32.add g 12) 4 := by
      rw [rd_bb N10 s10 (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at_b rfl F0.h_mem F0.ram 12 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_b rfl F0.h_mem F0.ram 12 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_b rfl F0.h_mem F0.ram 12 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.h_mem F0.ram 12 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.h_mem F0.ram 12 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.h_mem F0.ram 12 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rdRaw_wr4_same _ _ _ _ rfl]
      rw [subF_fst]
      rw [rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.f_mem F0.ram 12 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.f_mem F0.ram 12 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.f_mem F0.ram 12 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.f_mem F0.ram 12 (by decide)) F0.f_mem F0.f_stk f3 (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.g_mem F0.ram 12 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.g_mem F0.ram 12 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.g_mem F0.ram 12 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.g_mem F0.ram 12 (by decide)) F0.g_mem F0.g_stk f3 (by decide)]
    have w4 : rdRaw N11.get (UInt32.add h 16) 4 = rdRaw G.get (UInt32.add f 16) 4 - rdRaw G.get (UInt32.add g 16) 4 := by
      rw [rd_bb N10 s10 (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at_b rfl F0.h_mem F0.ram 16 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_b rfl F0.h_mem F0.ram 16 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_b rfl F0.h_mem F0.ram 16 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.h_mem F0.ram 16 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.h_mem F0.ram 16 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rdRaw_wr4_same _ _ _ _ rfl]
      rw [subF_fst]
      rw [rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.f_mem F0.ram 16 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.f_mem F0.ram 16 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.f_mem F0.ram 16 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.f_mem F0.ram 16 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.f_mem F0.ram 16 (by decide)) F0.f_mem F0.f_stk f3 (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.g_mem F0.ram 16 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.g_mem F0.ram 16 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.g_mem F0.ram 16 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.g_mem F0.ram 16 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.g_mem F0.ram 16 (by decide)) F0.g_mem F0.g_stk f3 (by decide)]
    have w5 : rdRaw N11.get (UInt32.add h 20) 4 = rdRaw G.get (UInt32.add f 20) 4 - rdRaw G.get (UInt32.add g 20) 4 := by
      rw [rd_bb N10 s10 (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at_b rfl F0.h_mem F0.ram 20 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_b rfl F0.h_mem F0.ram 20 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_b rfl F0.h_mem F0.ram 20 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.h_mem F0.ram 20 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rdRaw_wr4_same _ _ _ _ rfl]
      rw [subF_fst]
      rw [rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.f_mem F0.ram 20 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.f_mem F0.ram 20 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.f_mem F0.ram 20 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.f_mem F0.ram 20 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.f_mem F0.ram 20 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.f_mem F0.ram 20 (by decide)) F0.f_mem F0.f_stk f3 (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.g_mem F0.ram 20 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.g_mem F0.ram 20 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.g_mem F0.ram 20 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.g_mem F0.ram 20 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.g_mem F0.ram 20 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.g_mem F0.ram 20 (by decide)) F0.g_mem F0.g_stk f3 (by decide)]
    have w6 : rdRaw N11.get (UInt32.add h 24) 4 = rdRaw G.get (UInt32.add f 24) 4 - rdRaw G.get (UInt32.add g 24) 4 := by
      rw [rd_bb N10 s10 (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at_b rfl F0.h_mem F0.ram 24 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_b rfl F0.h_mem F0.ram 24 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_b rfl F0.h_mem F0.ram 24 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rdRaw_wr4_same _ _ _ _ rfl]
      rw [subF_fst]
      rw [rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.f_mem F0.ram 24 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.f_mem F0.ram 24 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.f_mem F0.ram 24 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.f_mem F0.ram 24 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.f_mem F0.ram 24 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.f_mem F0.ram 24 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.f_mem F0.ram 24 (by decide)) F0.f_mem F0.f_stk f3 (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.g_mem F0.ram 24 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.g_mem F0.ram 24 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.g_mem F0.ram 24 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.g_mem F0.ram 24 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.g_mem F0.ram 24 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.g_mem F0.ram 24 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.g_mem F0.ram 24 (by decide)) F0.g_mem F0.g_stk f3 (by decide)]
    have w7 : rdRaw N11.get (UInt32.add h 28) 4 = rdRaw G.get (UInt32.add f 28) 4 - rdRaw G.get (UInt32.add g 28) 4 := by
      rw [rd_bb N10 s10 (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at_b rfl F0.h_mem F0.ram 28 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rd_bb N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_b rfl F0.h_mem F0.ram 28 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rdRaw_wr4_same _ _ _ _ rfl]
      rw [subF_fst]
      rw [rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.f_mem F0.ram 28 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.f_mem F0.ram 28 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.f_mem F0.ram 28 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.f_mem F0.ram 28 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.f_mem F0.ram 28 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.f_mem F0.ram 28 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.f_mem F0.ram 28 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.f_mem F0.ram 28 (by decide)) F0.f_mem F0.f_stk f3 (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.g_mem F0.ram 28 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.g_mem F0.ram 28 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.g_mem F0.ram 28 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.g_mem F0.ram 28 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.g_mem F0.ram 28 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.g_mem F0.ram 28 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.g_mem F0.ram 28 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.g_mem F0.ram 28 (by decide)) F0.g_mem F0.g_stk f3 (by decide)]
    have w8 : rdRaw N11.get (UInt32.add h 32) 4 = rdRaw G.get (UInt32.add f 32) 4 - rdRaw G.get (UInt32.add g 32) 4 := by
      rw [rd_bb N10 s10 (at_b rfl F0.h_mem F0.ram 36 (by decide)) (at_b rfl F0.h_mem F0.ram 32 (by decide)) F0.h_mem (Or.inl rfl) (by decide) (by decide) (by decide),
          rdRaw_wr4_same _ _ _ _ rfl]
      rw [subF_fst]
      rw [rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_b rfl F0.f_mem F0.ram 32 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.f_mem F0.ram 32 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.f_mem F0.ram 32 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.f_mem F0.ram 32 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.f_mem F0.ram 32 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.f_mem F0.ram 32 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.f_mem F0.ram 32 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.f_mem F0.ram 32 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.f_mem F0.ram 32 (by decide)) F0.f_mem F0.f_stk f3 (by decide),
          rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_b rfl F0.g_mem F0.ram 32 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.g_mem F0.ram 32 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.g_mem F0.ram 32 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.g_mem F0.ram 32 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.g_mem F0.ram 32 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.g_mem F0.ram 32 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.g_mem F0.ram 32 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.g_mem F0.ram 32 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.g_mem F0.ram 32 (by decide)) F0.g_mem F0.g_stk f3 (by decide)]
    have w9 : rdRaw N11.get (UInt32.add h 36) 4 = rdRaw G.get (UInt32.add f 36) 4 - rdRaw G.get (UInt32.add g 36) 4 := by
      rw [rdRaw_wr4_same _ _ _ _ rfl]
      rw [subF_fst]
      rw [rd_bb N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_b rfl F0.f_mem F0.ram 36 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_b rfl F0.f_mem F0.ram 36 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.f_mem F0.ram 36 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.f_mem F0.ram 36 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.f_mem F0.ram 36 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.f_mem F0.ram 36 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.f_mem F0.ram 36 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.f_mem F0.ram 36 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.f_mem F0.ram 36 (by decide)) F0.f_mem F0.hf (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.f_mem F0.ram 36 (by decide)) F0.f_mem F0.f_stk f3 (by decide),
          rd_bb N9 s9 (at_b rfl F0.h_mem F0.ram 32 (by decide)) (at_b rfl F0.g_mem F0.ram 36 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N8 s8 (at_b rfl F0.h_mem F0.ram 28 (by decide)) (at_b rfl F0.g_mem F0.ram 36 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N7 s7 (at_b rfl F0.h_mem F0.ram 24 (by decide)) (at_b rfl F0.g_mem F0.ram 36 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N6 s6 (at_b rfl F0.h_mem F0.ram 20 (by decide)) (at_b rfl F0.g_mem F0.ram 36 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N5 s5 (at_b rfl F0.h_mem F0.ram 16 (by decide)) (at_b rfl F0.g_mem F0.ram 36 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N4 s4 (at_b rfl F0.h_mem F0.ram 12 (by decide)) (at_b rfl F0.g_mem F0.ram 36 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N3 s3 (at_b rfl F0.h_mem F0.ram 8 (by decide)) (at_b rfl F0.g_mem F0.ram 36 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N2 s2 (at_b rfl F0.h_mem F0.ram 4 (by decide)) (at_b rfl F0.g_mem F0.ram 36 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bb N1 s1 (at0 h) (at_b rfl F0.g_mem F0.ram 36 (by decide)) F0.g_mem F0.hg (by decide) (by decide) (by decide),
          rd_bs G rfl (at_s f3) (at_b rfl F0.g_mem F0.ram 36 (by decide)) F0.g_mem F0.g_stk f3 (by decide)]
    have hwi : ∀ i, i < 10 → (memWords N11.get h 10)[i]! = fv[i]! - gv[i]! := by
      intro i hi
      rw [← hfm, ← hgm, memWords_getElem! _ _ _ _ hi, memWords_getElem! _ _ _ _ hi,
        memWords_getElem! _ _ _ _ hi]
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · simp only [Nat.toUInt32_eq, UInt32.reduceOfNat, UInt32.reduceMul, UInt32.add_zero]
        first | exact w0 | exact w1 | exact w2 | exact w3 | exact w4 | exact w5 | exact w6 | exact w7 | exact w8 | exact w9
    exact fe_sub_math fv gv _ hfin hgin (by simp [memWords]) hwi

end Solutions.OpensslX25519
