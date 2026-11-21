import Sodium.Proofs.UnpadSteps
/-! # `sodium_unpad`: the prologue (`UnpadSteps`) -/
namespace Sodium.Proofs.Unpad
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Sodium.Proofs Sodium.Utils Sodium.Proofs.PadLib
  Sodium.Proofs.PadRun
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000
set_option Elab.async false

theorem pre (G : SMem) (eax ecx edx ebx t ebp esi edi f : UInt32)
    (hsz : G.get.size ≤ 0xFEC00000) (hst : t.toNat + 44 ≤ G.get.size)
    (hap : t.toNat + 44 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat)
    (hblk : 0 < (rdRaw G.get (t.add 40) 4).toNat)
    (hlen : (rdRaw G.get (t.add 40) 4).toNat ≤ (rdRaw G.get (t.add 36) 4).toNat) :
    ∃ (P : SMem) (ecx' esi' F : UInt32),
      P.get = wrBytes (wrBytes (wrBytes (wrBytes (wrBytes (wrBytes G.get (t.add 20) 4 ebp) (t.add 16) 4 ebx)
        (t.add 12) 4 edi) (t.add 8) 4 esi) t 4 0) (t.add 4) 4 ((rdRaw G.get (t.add 36) 4).add 4294967295) ∧
      PRun img Lpre (St.m ⟨G.get, eax, ecx, edx, ebx, t.add 24, ebp, esi, edi, 0x100D30, efl f, 0⟩)
        (St.m ⟨P.get, 0, ecx', edx, 0, t, 0, esi',
          ((rdRaw G.get (t.add 32) 4).add (rdRaw G.get (t.add 36) 4)).add 4294967295, 0x100D70, efl F,
          0 + Nat.toUInt64 30⟩) := by
  run_chain h : 30 from ⟨G.get, eax, ecx, edx, ebx, t.add 24, ebp, esi, edi, 0x100D30, efl f, 0⟩
  refine ⟨_, _, _, _, ?_, h⟩
  simp only [wr4_get] <;> rfl

end Sodium.Proofs.Unpad
