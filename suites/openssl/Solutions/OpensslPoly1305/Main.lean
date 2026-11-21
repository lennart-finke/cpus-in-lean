import Solutions.OpensslPoly1305.FinOk
import Solutions.OpensslPoly1305.UpdOk
/-!
# OpenSSL Poly1305: the task theorems

`final_ok : FinSpec` (`Poly1305_Final` from its entry, both paths), and with `update_ok : UpdSpec`
the streaming statement `Poly1305_correct` and its one-shot instance `Poly1305_oneshot`.
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305 Ssl.Spec.Poly1305

set_option autoImplicit false

set_option maxHeartbeats 4000000 in
/-- `Poly1305_Final` from a good context writes the tag of its message and wipes the context. -/
theorem final_ok : FinSpec := by
  intro key msg st c ctx mac hk hg hpre
  obtain ⟨hc, hbc, hbm, hap, hst⟩ := hpre
  have hf := calls_facts hc
  have bc := buffer_facts hc hbc (by decide)
  have bm := buffer_facts hc hbm (by decide)
  have hsp := stk_toNat hf.2.2.1
  have ham := apart_nat hap (by decide) (by decide)
  simp only [List.length, ctxSize] at hf bc bm hst ham
  let P : Nat → Prop := fun x => OutF (stk c) 268 x ∧ OutF ctx 236 x
  have hl : Frame (pmem hc) (stk c) 268 [(256, Image.sym_halt), (260, ctx), (264, mac)] :=
    frame_cons (frame_cons (frame_cons (Frame.nil (pmem hc) (stk c) 268) 264 mac 264 rfl rfl (by decide)
      (word_arg hc 1 (by simp) 264 rfl)) 260 ctx 260 rfl rfl (by decide) (word_arg hc 0 (by simp) 260 rfl))
      256 _ 256 rfl rfl (by decide) (word_ret hc)
  have hM0 := entry_memok hc ctx 236 236 bc.1 bc.2.1 (by simp only [List.length]; omega) _ hl P
    (fun x h => h.1) (fun x h => h.2)
  have hM : MemOK (pmem hc) (pmem hc) (stk c) 268 [(256, Image.sym_halt), (260, ctx), (264, mac)] ctx 236 236
      (lC0 (pmem hc) ctx) P :=
    ⟨hM0.fU, hM0.fC, hM0.dUC, hM0.wU, frame_lC0 _ _, hM0.pres, hM0.pU, hM0.pC⟩
  have hg' : GoodB key msg (memBytes (pmem hc).get ctx 236) := by rw [pmem_get, hst]; exact hg
  have hP : ∀ x, PT (stk c) ctx mac x → P x := fun x h => ⟨h.1, h.2.1⟩
  have hlU : LK [(256, Image.sym_halt), (260, ctx), (264, mac)] [(256, Image.sym_halt), (260, ctx), (264, mac)] :=
    ⟨lk_here, lk_skip lk_here rfl, lk_skip (lk_skip lk_here rfl) rfl, trivial⟩
  have hmf : mac.toNat + 16 ≤ (pmem hc).get.size := by rw [pmem_get]; exact bm.1
  have hmU : mac.toNat + 16 ≤ (stk c).toNat ∨ (stk c).toNat + 268 ≤ mac.toNat := by rw [hsp]; omega
  obtain ⟨N', lU', lC', eax, ecx, edx, gf, ic, R, M, LU, htag, hz⟩ :
      ∃ (N' : PMem) (lU' lC' : List (Nat × UInt32)) (eax ecx edx gf : UInt32) (ic : UInt64),
        Run img (St.m ⟨(pmem hc).get, c.regs.eax, c.regs.ecx, c.regs.edx, c.regs.ebx, UInt32.add (stk c) 256,
            c.regs.ebp, c.regs.esi, c.regs.edi, 0x100460, efl c.regs.flags, icAdd 0 0⟩)
          (St.m ⟨N'.get, eax, ecx, edx, c.regs.ebx, UInt32.add (stk c) 260, c.regs.ebp, c.regs.esi, c.regs.edi,
            Image.sym_halt, efl gf, ic⟩) ∧
        MemOK (pmem hc) N' (stk c) 268 lU' mac 16 16 lC' (PT (stk c) ctx mac) ∧
        LK lU' [(256, Image.sym_halt), (260, ctx), (264, mac)] ∧
        memBytes N'.get mac 16 = poly1305 key msg ∧ ∀ j, j < 236 → memByte N'.get (ctx + j.toUInt32) = 0 := by
    by_cases h0 : msg.length % 16 = 0
    · exact fin_p0 key msg (pmem hc) (stk c) ctx mac _ P hM hg' hP hmf bm.2.1 hmU (by omega) Image.sym_halt
        c.regs.eax c.regs.ecx c.regs.edx c.regs.ebx c.regs.ebp c.regs.esi c.regs.edi c.regs.flags hlU h0
    · exact fin_p1 key msg (pmem hc) (stk c) ctx mac _ P hM hg' hP hmf bm.2.1 hmU (by omega) Image.sym_halt
        c.regs.eax c.regs.ecx c.regs.edx c.regs.ebx c.regs.ebp c.regs.esi c.regs.edi c.regs.flags hlU h0
  have hsz : N'.get.size = c.mem.size := M.size
  have R' : Run img (c.enter Image.sym_Poly1305_Final) (St.m ⟨N'.get, eax, ecx, edx, c.regs.ebx,
      UInt32.add (stk c) 260, c.regs.ebp, c.regs.esi, c.regs.edi, Image.sym_halt, efl gf, ic⟩) := by
    rw [enter_eq c _ hf.2.2.1]; exact R
  refine returns_of hc _ M ?_ ?_ R' ⟨htag, ?_⟩
  · intro a hW ha
    simp only [InRange, ctxSize, UInt32.le_iff_toNat_le, not_or, not_and, Nat.not_lt] at hW
    refine ⟨by unfold OutF; rw [hsp]; simp only [List.length] at ha; omega, ?_, ?_⟩
    · unfold OutF
      by_cases h1 : ctx.toNat ≤ a.toNat
      · exact Or.inr (hW.1 h1)
      · exact Or.inl (by omega)
    · unfold OutF
      by_cases h1 : mac.toNat ≤ a.toNat
      · exact Or.inr (hW.2 h1)
      · exact Or.inl (by omega)
  · refine arg_bytes hc hsz (fun i hi => ?_)
    simp only [List.length] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact (M.rdU (k := 256) LU.1 _ rfl).trans (word_ret hc).symm
    · exact (M.rdU (k := 260) LU.2.1 _ rfl).trans (word_arg hc 0 (by simp) _ rfl).symm
    · exact (M.rdU (k := 264) LU.2.2.1 _ rfl).trans (word_arg hc 1 (by simp) _ rfl).symm
  · show memBytes N'.get ctx 236 = List.replicate 236 0
    apply list_ext! (by rw [memBytes_length, List.length_replicate])
    intro j hj
    simp only [memBytes_length] at hj
    rw [getElem!_memBytes hj, hz j hj]
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_replicate, if_pos hj]; rfl

/-- `Poly1305_Init`, `Poly1305_Update`s over any chunks, `Poly1305_Final`: the RFC 8439 tag, the
context wiped. -/
theorem Poly1305_correct_ok : Ssl.OpensslPoly1305.Poly1305_correct := correct_of update_ok final_ok

/-- The one-shot instance. -/
theorem Poly1305_oneshot_ok : Ssl.OpensslPoly1305.Poly1305_oneshot := oneshot_of update_ok final_ok

end Solutions.OpensslPoly1305
