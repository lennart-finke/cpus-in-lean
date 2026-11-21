import Solutions.OpensslSha256.X.UpdOk
import Solutions.OpensslSha256.X.U224Run
/-!
# The contracts of `SHA256_Update` and `SHA224_Update`

From a context `Good` after the bytes `msg`, an `Update` with `chunk` returns 1, writes only the
context, and leaves it `Good` after `msg ++ chunk` (`upd256_ok`, `upd224_ok`).
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256
open Solutions.OpensslSha256 (Good hOf tailOf tailOf_length)

/-- What the precondition of an `Update` gives, for the frame `U` with `U + k = c.sp`. -/
theorem upd_facts (c : Caller) (ctx msgp : UInt32) (st chunk : List UInt8) (hpre : UpdatePre c ctx msgp st chunk)
    (U : UInt32) (k : Nat) (hk : 40 ≤ k ∧ k ≤ 56) (hU : U.toNat + k = c.sp.toNat) (H : CMem) (hH : H.get = c.mem) :
    UF H.get U ctx ∧ chunk.length < 2 ^ 31 ∧ (0 < chunk.length → MF H.get U ctx msgp chunk.length) ∧
      (∀ i, i < chunk.length → H.get.get! (msgp.toNat + i) = chunk[i]!) ∧
      memBytes H.get ctx 112 = st ∧ 512 ≤ c.sp.toNat ∧ c.sp.toNat + 16 ≤ H.get.size ∧
      (c.sp.toNat + 16 ≤ 1048576 ∨ 1048576 + 4944 + 512 ≤ c.sp.toNat) ∧
      (ctx.toNat + 112 ≤ c.sp.toNat - 512 ∨ c.sp.toNat + 16 ≤ ctx.toNat) ∧
      (0 < chunk.length → msgp.toNat + chunk.length ≤ c.sp.toNat - 512 ∨ c.sp.toNat + 16 ≤ msgp.toNat) := by
  obtain ⟨hC, hBc, hBm, hAp, hst, hch⟩ := hpre
  have hS := spOk_of hC
  simp only [List.length_cons, List.length_nil] at hS
  have hX := bufOk_of hBc (by decide) hS.lo
  have hlo := hS.lo; have hhi := hS.hi; have himg := hS.img; have hsz := hS.sz
  have xf := hX.fit; have xi := hX.img; have xs := hX.stk
  have hmax : chunk.length ≤ 0x7FFFFFFF := hBm.2.1
  rw [hH]
  unfold ctxSize at xf xi xs hst
  refine ⟨⟨hsz, by omega, by omega, by omega, xf, by omega, by omega⟩, by omega, fun h0 => ?_, fun i hi => ?_, hst,
    hlo, by omega, by omega, by omega, fun h0 => ?_⟩
  · have hY := bufOk_of hBm (by omega) hS.lo
    have yf := hY.fit; have yi := hY.img; have ys := hY.stk
    unfold Apart at hAp
    exact ⟨yf, by omega, by omega, by unfold ctxSize at hAp; omega⟩
  · have hY := bufOk_of hBm (by omega) hS.lo
    have := memBytes_get (M := c.mem) (a := msgp) (n := chunk.length) (i := i) hi hY.fit (by omega)
    rw [hch] at this; exact this.symm
  · have hY := bufOk_of hBm (by omega) hS.lo
    exact hY.stk

theorem good_of_upd (H0 : Array UInt32) (md : Nat) (msg chunk : List UInt8) (M : ByteArray) (ctx : UInt32)
    (hfit : ctx.toNat + 112 ≤ M.size) (hM : M.size < 2 ^ 32) (hlt : (msg ++ chunk).length < Spec.Sha256.lenBound)
    (nl' nh' : UInt32)
    (hnl : NlOk (8 * msg.length).toUInt32 nl' chunk.length.toUInt32.toNat)
    (hnh : NhOk (8 * msg.length).toUInt32 (8 * msg.length / 2 ^ 32).toUInt32 nh' chunk.length.toUInt32.toNat)
    (hl : chunk.length.toUInt32.toNat = chunk.length)
    (hC : CtxOk M ctx (updH (hOf H0 msg) (tailOf msg) chunk) nl' nh'
      (((tailOf msg).length + chunk.length.toUInt32.toNat) % 64).toUInt32 md.toUInt32 (updB (tailOf msg) chunk)) :
    Good H0 md (msg ++ chunk) (memBytes M ctx 112) := by
  unfold NlOk at hnl
  unfold NhOk at hnh
  rw [hl, toUInt32_toNat_mod] at hnl hnh
  rw [toUInt32_toNat_mod] at hnh
  rw [hl, tailOf_length] at hC
  refine good_upd hfit hM hlt nl' nh' _ hnl hnh ?_ hC
  rw [toUInt32_toNat_mod]; omega

set_option maxHeartbeats 4000000 in
theorem upd256_ok (H0 : Array UInt32) (md : Nat) (msg st chunk : List UInt8) (hG : Good H0 md msg st)
    (hlt : (msg ++ chunk).length < Spec.Sha256.lenBound) (c : Caller) (ctx msgp : UInt32)
    (hpre : UpdatePre c ctx msgp st chunk) :
    Returns img (c.enter Image.sym_SHA256_Update) stackBound (InRange ctx ctxSize) fun m =>
      m.cpu.eax = 1 ∧ Good H0 md (msg ++ chunk) (bytesAt m ctx ctxSize) := by
  have hC := hpre.1
  obtain ⟨H, hH⟩ : ∃ H : CMem, H.get = c.mem := ⟨cmemOf hC, rfl⟩
  have hsp512 : 512 ≤ c.sp.toNat := (spOk_of hC).lo
  have tU : (c.sp - 40).toNat = c.sp.toNat - 40 := frame_tN 40 40 rfl (by omega)
  obtain ⟨hF, hLl, hM, hb, hst, hlo, hhi, himg, -, -⟩ :=
    upd_facts c ctx msgp st chunk hpre (c.sp - 40) 40 (by omega) (by omega) H hH
  have hcf := hF.cfit; have hsz := hF.sz
  have hl : chunk.length.toUInt32.toNat = chunk.length := toUInt32_lt (by omega)
  rw [← hst] at hG
  have hC0 := ctxOk_of_good hcf (by omega) hG
  have hTl := tailOf_length msg
  have hC1 : CtxOk H.get ctx (hOf H0 msg) (8 * msg.length).toUInt32 (8 * msg.length / 2 ^ 32).toUInt32
      (tailOf msg).length.toUInt32 md.toUInt32 (tailOf msg) := by rw [hTl]; exact hC0
  have a1 := calls_arg hC 0 (by simp)
  have a2 := calls_arg hC 1 (by simp)
  have a3 := calls_arg hC 2 (by simp)
  have rd : ∀ (d : UInt32) (v : UInt32), rdBytes c.mem (c.sp + d) 4 = v → rdRaw H.get ((c.sp - 40).add (40 + d)) 4 = v :=
    fun d v h => by rw [sp_frame, hH]; exact h
  obtain ⟨H', ecx', edx', f', ic', -, hrun, hA, nl', nh', hnl, hnh, hC2⟩ := upd_core H (c.sp - 40) ctx msgp
    chunk.length.toUInt32 Image.sym_halt c.regs.eax c.regs.ecx c.regs.edx c.regs.ebx c.regs.ebp c.regs.esi c.regs.edi
    c.regs.flags chunk (tailOf msg) (hOf H0 msg) (8 * msg.length).toUInt32 (8 * msg.length / 2 ^ 32).toUInt32
    md.toUInt32 hF hl.symm (by omega) (by rw [hl]; exact hM) (by rw [hl]; exact hb) (frame_ret hC H hH 40)
    (rd 4 _ (by simpa using a1)) (rd 8 _ (by simpa using a2)) (rd 12 _ (by simpa using a3))
    (by rw [hTl]; omega) hC1 0 (by decide)
  have e44 : (c.sp - 40).add 44 = c.sp + 4 := sp_frame c.sp 40 4
  have hS' : H'.get.size = c.mem.size := by rw [hA.1, hH]
  have hHs : H.get.size = c.mem.size := by rw [hH]
  refine returns_of_run c _ _ _ H'.get 1 ecx' edx' f' ic' (RU (c.sp - 40) ctx)
    (by rw [enter_frame c H hH 40]; unfold SR at hrun; rw [e44] at hrun; exact hrun) (by rw [← hH]; exact hA) ?_
    ⟨rfl, ?_⟩
  · intro a ha
    unfold RU at ha
    rw [inRange_iff, inRange_iff, stack_lo c hsp512]
    unfold ctxSize
    omega
  · show Good _ _ _ (memBytes H'.get ctx 112)
    exact good_of_upd H0 md msg chunk H'.get ctx (by omega) (by omega) hlt nl' nh' hnl hnh hl hC2

set_option maxHeartbeats 4000000 in
theorem upd224_ok (H0 : Array UInt32) (md : Nat) (msg st chunk : List UInt8) (hG : Good H0 md msg st)
    (hlt : (msg ++ chunk).length < Spec.Sha256.lenBound) (c : Caller) (ctx msgp : UInt32)
    (hpre : UpdatePre c ctx msgp st chunk) :
    Returns img (c.enter Image.sym_SHA224_Update) stackBound (InRange ctx ctxSize) fun m =>
      m.cpu.eax = 1 ∧ Good H0 md (msg ++ chunk) (bytesAt m ctx ctxSize) := by
  have hC := hpre.1
  obtain ⟨H, hH⟩ : ∃ H : CMem, H.get = c.mem := ⟨cmemOf hC, rfl⟩
  have hHs : H.get.size = c.mem.size := by rw [hH]
  have hsp512 : 512 ≤ c.sp.toNat := (spOk_of hC).lo
  have tU : (c.sp - 56).toNat = c.sp.toNat - 56 := frame_tN 56 56 rfl (by omega)
  obtain ⟨hF, hLl, hM, hb, hst, hlo, hhi, himg, hcs, hms⟩ :=
    upd_facts c ctx msgp st chunk hpre (c.sp - 56) 56 (by omega) (by omega) H hH
  have hcf := hF.cfit; have hsz := hF.sz
  have hl : chunk.length.toUInt32.toNat = chunk.length := toUInt32_lt (by omega)
  rw [← hst] at hG
  have hC0 := ctxOk_of_good hcf (by omega) hG
  have hTl := tailOf_length msg
  have hC1 : CtxOk H.get ctx (hOf H0 msg) (8 * msg.length).toUInt32 (8 * msg.length / 2 ^ 32).toUInt32
      (tailOf msg).length.toUInt32 md.toUInt32 (tailOf msg) := by rw [hTl]; exact hC0
  have a1 := calls_arg hC 0 (by simp)
  have a2 := calls_arg hC 1 (by simp)
  have a3 := calls_arg hC 2 (by simp)
  have rd : ∀ (d : UInt32) (v : UInt32), rdBytes c.mem (c.sp + d) 4 = v → rdRaw H.get ((c.sp - 56).add (56 + d)) 4 = v :=
    fun d v h => by rw [sp_frame, hH]; exact h
  obtain ⟨H1, f1, e1, hm1⟩ := u224_a H (c.sp - 56) ctx msgp chunk.length.toUInt32 c.regs.eax c.regs.ecx c.regs.edx
    c.regs.ebx c.regs.ebp c.regs.esi c.regs.edi c.regs.flags 0 hsz (by omega) (by omega)
    (rd 4 _ (by simpa using a1)) (rd 8 _ (by simpa using a2)) (rd 12 _ (by simpa using a3))
  have r1 := exN_run (img := img) 4 _ _ e1 (by show (0 : UInt64).toNat + 4 < 2 ^ 64; decide)
  have hS1 : H1.get.size = H.get.size := by rw [hm1]; simp only [Solutions.Exec.size_wrBytes]
  have a1' : AgreeOn (fun a => (c.sp - 56).toNat + 40 ≤ a ∧ a < (c.sp - 56).toNat + 56) H.get H1.get := by
    rw [hm1]; agw
  have hM1 : 0 < chunk.length.toUInt32.toNat → MF H1.get (c.sp - 56) ctx msgp chunk.length.toUInt32.toNat :=
    fun h => by rw [hl] at h ⊢; exact (hM h).size hS1
  have hb1 : ∀ i, i < chunk.length.toUInt32.toNat → H1.get.get! (msgp.toNat + i) = chunk[i]! := by
    intro i hi
    rw [hl] at hi
    have mf := (hM (by omega)).fit; have ms := hms (by omega)
    rw [a1'.2 _ (by omega) (by omega)]; exact hb i hi
  have hC1' := CtxOk.agree a1' (fun a h1 h2 h3 => by omega) hcf hsz (by rw [hTl]; omega) hC1
  obtain ⟨H2, ecx2, edx2, f2, ic2, hic2, hrun, hA, nl', nh', hnl, hnh, hC2⟩ := upd_core H1 (c.sp - 56) ctx msgp
    chunk.length.toUInt32 0x1000d1 c.regs.eax c.regs.ecx c.regs.edx c.regs.ebx c.regs.ebp c.regs.esi c.regs.edi
    f1 chunk (tailOf msg) (hOf H0 msg) (8 * msg.length).toUInt32 (8 * msg.length / 2 ^ 32).toUInt32
    md.toUInt32 (hF.size hS1) hl.symm (by omega) hM1 hb1 (by rw [hm1]; rdv) (by rw [hm1]; rdv)
    (by rw [hm1]; rdv) (by rw [hm1]; rdv) (by rw [hTl]; omega) hC1' (0 + 4) (by decide)
  have hS2 : H2.get.size = c.mem.size := by rw [hA.1, hS1, hH]
  have hra2 : rdRaw H2.get ((c.sp - 56).add 56) 4 = Image.sym_halt := by
    have c56 : ((c.sp - 56).add 56).toNat = (c.sp - 56).toNat + 56 := by ao
    rw [rdRaw4_agree hA (by omega) (fun k hk => by unfold RU; omega), rdRaw4_agree a1' (by omega) (fun k hk => by omega)]
    exact frame_ret hC H hH 56
  obtain ⟨f3, e3⟩ := u224_b H2 (c.sp - 56) Image.sym_halt 1 ecx2 edx2 c.regs.ebx c.regs.ebp c.regs.esi c.regs.edi f2
    ic2 (by omega) (by omega) (by omega) hra2
  have i4 : ((0 : UInt64) + 4).toNat = 4 := rfl
  have r3 := exN_run (img := img) 3 _ _ e3 (by show ic2.toNat + 3 < 2 ^ 64; omega)
  have e60 : (c.sp - 56).add 60 = c.sp + 4 := sp_frame c.sp 56 4
  rw [e60] at r3
  unfold SR at hrun
  refine returns_of_run c _ _ _ H2.get 1 ecx2 edx2 f3 (ic2 + 3)
    (fun a => (c.sp - 56).toNat - 168 ≤ a ∧ a < (c.sp - 56).toNat + 56 ∨ ctx.toNat ≤ a ∧ a < ctx.toNat + 108)
    (by rw [enter_frame c H hH 56]; exact r1.trans (hrun.trans r3))
    (by rw [← hH]; exact (a1'.mono fun a h => by omega).trans (hA.mono fun a h => by unfold RU at h; omega)) ?_
    ⟨rfl, ?_⟩
  · intro a ha
    rw [inRange_iff, inRange_iff, stack_lo c hsp512]
    unfold ctxSize
    omega
  · show Good _ _ _ (memBytes H2.get ctx 112)
    exact good_of_upd H0 md msg chunk H2.get ctx (by omega) (by omega) hlt nl' nh' hnl hnh hl hC2

end Solutions.ShaX
