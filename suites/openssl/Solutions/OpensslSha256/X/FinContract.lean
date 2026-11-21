import Solutions.OpensslSha256.X.FinCore
import Solutions.OpensslSha256.X.F224Run
/-!
# The contracts of `SHA256_Final` and `SHA224_Final`

From a context `Good` after `msg`, `Final` returns 1, writes only the context and the digest, puts
the first `olen / 4` hash words of `msg` big-endian at `md`, and leaves the buffer and `num` zero.
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256
open Solutions.OpensslSha256 (Good hOf tailOf)

set_option maxHeartbeats 4000000 in
/-- A call that reaches the first instruction of `SHA256_Final` with nothing changed but the
instruction count. -/
theorem fin_ok (H0 : Array UInt32) (mdN : Nat) (msg st : List UInt8) (hG : Good H0 mdN msg st) (olen : Nat)
    (holen : (olen = 32 ∧ mdN = 32) ∨ (olen = 28 ∧ mdN = 28)) (c : Caller) (out ctx : UInt32)
    (hpre : FinalPre olen c out ctx st) (fn : UInt32) (H : CMem) (hH : H.get = c.mem) (f0 : UInt32) (ic0 : UInt64)
    (hic0 : ic0.toNat ≤ 2 ^ 40)
    (hr0 : Run img (c.enter fn) (St.m ⟨H.get, c.regs.eax, c.regs.ecx, c.regs.edx, c.regs.ebx, (c.sp - 36).add 36,
      c.regs.ebp, c.regs.esi, c.regs.edi, 0x1001b0, efl f0, ic0⟩)) :
    Returns img (c.enter fn) stackBound (fun a => InRange ctx ctxSize a ∨ InRange out olen a) fun m3 =>
      m3.cpu.eax = 1 ∧
      bytesAt m3 out olen = (List.range (olen / 4)).flatMap (fun i => be32 (Spec.Sha256.hashWords H0 msg)[i]!) ∧
      bytesAt m3 (ctx + dataOff) 68 = List.replicate 68 0 := by
  obtain ⟨hC, hBc, hBo, hAp, hst⟩ := hpre
  have hol0 : olen ≠ 0 := by omega
  have hS := spOk_of hC
  simp only [List.length_cons, List.length_nil] at hS
  have hX := bufOk_of hBc (by decide) hS.lo
  have hY := bufOk_of hBo hol0 hS.lo
  have hlo := hS.lo; have hhi := hS.hi; have himg := hS.img; have hsz := hS.sz
  have xf := hX.fit; have xi := hX.img; have xs := hX.stk
  have yf := hY.fit; have yi := hY.img; have ys := hY.stk
  unfold ctxSize at xf xi xs hst ⊢
  unfold Apart ctxSize at hAp
  have hHs : H.get.size = c.mem.size := by rw [hH]
  have tV : (c.sp - 36).toNat = c.sp.toNat - 36 := frame_tN 36 36 rfl (by omega)
  have hF : FF H.get (c.sp - 36) ctx out olen :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have a1 := calls_arg hC 0 (by simp)
  have a2 := calls_arg hC 1 (by simp)
  have rd : ∀ (d : UInt32) (v : UInt32), rdBytes c.mem (c.sp + d) 4 = v → rdRaw H.get ((c.sp - 36).add (36 + d)) 4 = v :=
    fun d v h => by rw [sp_frame, hH]; exact h
  rw [← hst] at hG
  have hG' : Good H0 mdN msg (memBytes H.get ctx 112) := by rw [hH]; exact hG
  have hCk := ctxOk_of_good (by omega) (by omega) hG'
  obtain ⟨H', ecx', edx', f', ic', hrun, hA, hw, hz⟩ := fin_core H (c.sp - 36) ctx out Image.sym_halt c.regs.eax
    c.regs.ecx c.regs.edx c.regs.ebx c.regs.ebp c.regs.esi c.regs.edi f0 ic0 olen H0 mdN msg hF
    (frame_ret hC H hH 36) (rd 4 _ (by simpa using a1)) (rd 8 _ (by simpa using a2)) hCk hG'.lt holen hic0
  have e40 : (c.sp - 36).add 40 = c.sp + 4 := sp_frame c.sp 36 4
  rw [e40] at hrun
  have hS' : H'.get.size = c.mem.size := by rw [hA.1, hH]
  refine returns_of_run c _ _ _ H'.get 1 ecx' edx' f' ic'
    (fun a => (c.sp - 36).toNat - 168 ≤ a ∧ a < (c.sp - 36).toNat + 36 ∨ ctx.toNat ≤ a ∧ a < ctx.toNat + 112 ∨
      out.toNat ≤ a ∧ a < out.toNat + olen) (hr0.trans hrun) (by rw [← hH]; exact hA) ?_ ⟨rfl, ?_, ?_⟩
  · intro a ha
    rw [inRange_iff, inRange_iff, inRange_iff, stack_lo c hlo]
    omega
  · show memBytes H'.get out olen = _
    have h4 : olen = 4 * (olen / 4) := by omega
    conv => lhs; rw [h4]
    exact digest_of_words H'.get out _ (olen / 4) (by omega) (by omega) hw
  · show memBytes H'.get (ctx + 40) 68 = _
    have e : (ctx + 40).toNat = ctx.toNat + 40 := by rw [UInt32.toNat_add]; simp; omega
    exact zeros_of H'.get (ctx + 40) 68 (by omega) (by omega) (fun i hi => by rw [e]; exact hz i hi)

theorem fin256_ok (H0 : Array UInt32) (msg st : List UInt8) (hG : Good H0 32 msg st) (c : Caller) (out ctx : UInt32)
    (hpre : FinalPre 32 c out ctx st) :
    Returns img (c.enter Image.sym_SHA256_Final) stackBound (fun a => InRange ctx ctxSize a ∨ InRange out 32 a)
      fun m3 => m3.cpu.eax = 1 ∧
        bytesAt m3 out 32 = (List.range 8).flatMap (fun i => be32 (Spec.Sha256.hashWords H0 msg)[i]!) ∧
        bytesAt m3 (ctx + dataOff) 68 = List.replicate 68 0 := by
  obtain ⟨H, hH⟩ : ∃ H : CMem, H.get = c.mem := ⟨cmemOf hpre.1, rfl⟩
  exact fin_ok H0 32 msg st hG 32 (Or.inl ⟨rfl, rfl⟩) c out ctx hpre _ H hH c.regs.flags 0 (by decide)
    (by rw [enter_frame c H hH 36]; exact Run.refl _ _)

theorem fin224_ok (H0 : Array UInt32) (msg st : List UInt8) (hG : Good H0 28 msg st) (c : Caller) (out ctx : UInt32)
    (hpre : FinalPre 28 c out ctx st) :
    Returns img (c.enter Image.sym_SHA224_Final) stackBound (fun a => InRange ctx ctxSize a ∨ InRange out 28 a)
      fun m3 => m3.cpu.eax = 1 ∧
        bytesAt m3 out 28 = (List.range 7).flatMap (fun i => be32 (Spec.Sha256.hashWords H0 msg)[i]!) ∧
        bytesAt m3 (ctx + dataOff) 68 = List.replicate 68 0 := by
  obtain ⟨H, hH⟩ : ∃ H : CMem, H.get = c.mem := ⟨cmemOf hpre.1, rfl⟩
  have hsz : H.get.size ≤ 4273995776 := by rw [hH]; exact hpre.1.1
  obtain ⟨f1, e1⟩ := fin224_jmp H ((c.sp - 36).add 36) c.regs.eax c.regs.ecx c.regs.edx c.regs.ebx c.regs.ebp
    c.regs.esi c.regs.edi c.regs.flags 0 hsz
  have r1 := exN_run (img := img) 1 _ _ e1 (by show (0 : UInt64).toNat + 1 < 2 ^ 64; decide)
  exact fin_ok H0 28 msg st hG 28 (Or.inr ⟨rfl, rfl⟩) c out ctx hpre _ H hH f1 (0 + 1) (by decide)
    (by rw [enter_frame c H hH 36]; exact r1)

end Solutions.ShaX
