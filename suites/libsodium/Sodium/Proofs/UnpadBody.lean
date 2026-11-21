import Sodium.Proofs.UnpadSteps
/-! # `sodium_unpad`: the loop body back to the loop head (`UnpadSteps`) -/
namespace Sodium.Proofs.Unpad
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Sodium.Proofs Sodium.Utils Sodium.Proofs.PadLib
  Sodium.Proofs.PadRun
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000
set_option Elab.async false

theorem body (M : SMem) (v ecx edx i t acc esi edi f : UInt32) (ic : UInt64)
    (hsz : M.get.size ≤ 0xFEC00000) (hst : t.toNat + 44 ≤ M.get.size)
    (hap : t.toNat + 44 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat)
    (hed : edi.toNat < M.get.size) (hbuf : edi.toNat < 0x100000 ∨ 0x100000 + 3560 ≤ edi.toNat)
    (hic : ic.toNat + 31 < 2 ^ 64)
    (hi : i.toNat + 1 < (rdRaw M.get (t.add 40) 4).toNat) :
    ∃ (M' : SMem) (ecx' edx' esi' F : UInt32),
      M'.get = wrBytes M.get t 4 (upl (rdRaw M.get edi 1) (rdRaw M.get t 4) acc i) ∧
      PRun img Lbody (St.m ⟨M.get, v, ecx, edx, i, t, acc, esi, edi, 0x100D70, efl f, ic⟩)
        (St.m ⟨M'.get, v.lor (ubit (rdRaw M.get edi 1) (rdRaw M.get t 4) acc), ecx', edx', i.add 1, t,
          acc.lor (rdRaw M.get edi 1), esi', edi.add 4294967295, 0x100D70, efl F, ic + Nat.toUInt64 20⟩) := by
  run_chain h : 20 from ⟨M.get, v, ecx, edx, i, t, acc, esi, edi, 0x100D70, efl f, ic⟩
  refine ⟨_, _, _, _, _, ?_, h⟩
  simp only [wr4_get] <;> rfl

end Sodium.Proofs.Unpad
