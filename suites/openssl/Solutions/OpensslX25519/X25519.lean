import Solutions.OpensslX25519.I.OssCall
import Solutions.OpensslX25519.Call
import Solutions.OpensslX25519.Peel
/-!
# `ossl_x25519` (Statement B)

`ossl_x25519_ok : Ssl.OpensslX25519.ossl_x25519_correct`, from the run `I.ossl_run` (prover R): the caller's frame
gives `Lb = sp - 388`, `L = sp - 356`; everything the call writes lies in `[sp - 1368, sp)` and the 32 bytes at
`out`.
-/
namespace Solutions.OpensslX25519
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.OpensslX25519.I

theorem buf32 {c : Caller} {p : UInt32} (hs : 2048 ≤ c.sp.toNat) (hb : Buffer img c stackBound 3 p 32) :
    p.toNat + 32 ≤ c.mem.size ∧ (p.toNat + 32 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ p.toNat) ∧
      (p.toNat + 32 ≤ c.sp.toNat - 2048 ∨ c.sp.toNat + 16 ≤ p.toNat) := by
  obtain ⟨hfit, -, hai, has⟩ := hb
  have hlo := stackLo_toNat (c := c) (stack := stackBound) hs
  refine ⟨by rcases hfit with h | h <;> omega, ?_, ?_⟩
  · have := apart_nat hai (by decide) (by rw [img_size]; decide)
    rw [img_size, img_base] at this
    exact this
  · have := apart_nat has (by decide) (by simp [stackSize])
    rw [hlo] at this
    simp only [stackSize, stackBound] at this
    omega

theorem not_inRange32 {o x : UInt32} (h : ¬ InRange o 32 x) : x.toNat < o.toNat ∨ o.toNat + 32 ≤ x.toNat := by
  unfold InRange at h
  rw [UInt32.le_iff_toNat_le] at h
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ossl_x25519_ok : ossl_x25519_correct := by
  intro c out kp up k u hpre
  obtain ⟨hcall, -, -, hbo, hbk, hbu, -, -, hk, hu⟩ := hpre
  let G : XMem := xmem hcall
  have hTop : G.get.size ≤ ramTop := ramTop_of_calls hcall
  have hs : 2048 ≤ c.sp.toNat := hcall.2.2.2.2.1
  have hsp : c.sp.toNat + 4 * ([out, kp, up].length + 1) ≤ c.mem.size := hcall.2.2.2.2.2.1
  simp only [List.length] at hsp
  have hlo := stackLo_toNat (c := c) (stack := stackBound) hs
  have himgS := apart_nat hcall.2.2.2.2.2.2 (by simp [stackSize]) (by rw [img_size]; decide)
  rw [hlo, img_size, img_base] at himgS
  simp only [stackSize, stackBound, List.length] at himgS
  have hfit := hcall.2.1
  rw [img_size, img_base] at hfit
  have bo := buf32 hs hbo
  have bk := buf32 hs hbk
  have bu := buf32 hs hbu
  have hsz : G.get.size = c.mem.size := rfl
  obtain ⟨Lb, hLb⟩ := below_L (L := c.sp) (d := 388) (by omega)
  obtain ⟨L, hL⟩ := below_L (L := c.sp) (d := 356) (by omega)
  have hspLb : UInt32.add Lb 388 = c.sp := by
    apply UInt32.toNat_inj.1; rw [toNat_uadd]; simp only [UInt32.reduceToNat]; have := c.sp.toNat_lt; omega
  have ea0 : c.sp + 4 * (0 + 1).toUInt32 = UInt32.add Lb 392 := by
    rw [← hspLb]; show Lb + 388 + 4 * (0 + 1).toUInt32 = Lb + 392; rw [UInt32.add_assoc]; rfl
  have ea1 : c.sp + 4 * (1 + 1).toUInt32 = UInt32.add Lb 396 := by
    rw [← hspLb]; show Lb + 388 + 4 * (1 + 1).toUInt32 = Lb + 396; rw [UInt32.add_assoc]; rfl
  have ea2 : c.sp + 4 * (2 + 1).toUInt32 = UInt32.add Lb 400 := by
    rw [← hspLb]; show Lb + 388 + 4 * (2 + 1).toUInt32 = Lb + 400; rw [UInt32.add_assoc]; rfl
  have hret : rdRaw G.get (UInt32.add Lb 388) 4 = Image.sym_halt := by
    rw [hspLb]; unfold rdRaw; exact calls_ret hcall
  have hout : rdRaw G.get (UInt32.add Lb 392) 4 = out := by
    have := calls_arg hcall 0 (by simp)
    rw [ea0] at this
    unfold rdRaw; exact this
  have hkp : rdRaw G.get (UInt32.add Lb 396) 4 = kp := by
    have := calls_arg hcall 1 (by simp)
    rw [ea1] at this
    unfold rdRaw; exact this
  have hup : rdRaw G.get (UInt32.add Lb 400) 4 = up := by
    have := calls_arg hcall 2 (by simp)
    rw [ea2] at this
    unfold rdRaw; exact this
  have e0 : c.enter Image.sym_ossl_x25519 = St.m ⟨G.get, c.regs.eax, c.regs.ecx, c.regs.edx, c.regs.ebx,
      UInt32.add Lb 388, c.regs.ebp, c.regs.esi, c.regs.edi, 0x100420, efl c.regs.flags, 0⟩ := by
    rw [hspLb]; rfl
  obtain ⟨N, ecx, edx, fl, R, P, V⟩ := ossl_run G Lb L out kp up Image.sym_halt c.regs.esi k u
    ⟨hTop, by rw [hsz]; omega, by omega⟩ (by rw [hsz]; omega) (by omega) (by omega) (by omega) hret hout hkp hup
    (by rw [hsz]; exact bk.1) bk.2.1 (by omega) hk (by rw [hsz]; exact bu.1) bu.2.1 (by omega) hu
    (by rw [hsz]; exact bo.1) bo.2.1 (by omega) c.regs.eax c.regs.ecx c.regs.edx c.regs.ebx c.regs.ebp c.regs.edi
    c.regs.flags 0 (by simp)
  rw [e0]
  refine Returns.intro R ?_ ⟨rfl, rfl, rfl, rfl⟩ ?_ ⟨V, rfl⟩
  · refine ⟨rfl, ?_, efl_DF _⟩
    show UInt32.add Lb 392 = UInt32.add Lb 388 + 4
    apply UInt32.toNat_inj.1
    rw [toNat_uadd, UInt32.toNat_add, toNat_uadd]
    simp only [UInt32.reduceToNat]
    omega
  · refine ⟨P.1, fun x hx hW hSt => P.2 x hx ⟨?_, not_inRange32 hW⟩⟩
    have := not_inRange_stack (sp := UInt32.add Lb 388) (by rw [hspLb]; exact hs) hSt
    rw [hspLb] at this
    omega

end Solutions.OpensslX25519
