import Sodium.Proofs.UnpadSteps
/-! # `sodium_unpad`: the last iteration and the epilogue (`UnpadSteps`) -/
namespace Sodium.Proofs.Unpad
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Sodium.Proofs Sodium.Utils Sodium.Proofs.PadLib
  Sodium.Proofs.PadRun
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000
set_option Elab.async false

theorem exit (M : SMem) (v ecx edx i t acc esi edi f : UInt32) (ic : UInt64)
    (hsz : M.get.size ≤ 0xFEC00000) (hst : t.toNat + 44 ≤ M.get.size)
    (hap : t.toNat + 44 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat)
    (hed : edi.toNat < M.get.size) (hbuf : edi.toNat < 0x100000 ∨ 0x100000 + 3560 ≤ edi.toNat)
    (hic : ic.toNat + 31 < 2 ^ 64)
    (hlp : (rdRaw M.get (t.add 28) 4).toNat + 4 ≤ M.get.size)
    (hlp2 : (rdRaw M.get (t.add 28) 4).toNat + 4 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ (rdRaw M.get (t.add 28) 4).toNat)
    (hlp3 : (rdRaw M.get (t.add 28) 4).toNat + 4 ≤ t.toNat ∨ t.toNat + 44 ≤ (rdRaw M.get (t.add 28) 4).toNat)
    (hi : i.toNat + 1 = (rdRaw M.get (t.add 40) 4).toNat) (hB : (rdRaw M.get (t.add 40) 4).toNat < 2 ^ 31) :
    ∃ (M' : SMem) (ecx' F : UInt32),
      M'.get = wrBytes (wrBytes M.get t 4 (upl (rdRaw M.get edi 1) (rdRaw M.get t 4) acc i))
        (rdRaw M.get (t.add 28) 4) 4
        ((rdRaw M.get (t.add 4) 4).sub (upl (rdRaw M.get edi 1) (rdRaw M.get t 4) acc i)) ∧
      PRun img Lexit (St.m ⟨M.get, v, ecx, edx, i, t, acc, esi, edi, 0x100D70, efl f, ic⟩)
        (St.m ⟨M'.get, (v.lor (ubit (rdRaw M.get edi 1) (rdRaw M.get t 4) acc)).add 4294967295, ecx',
          rdRaw M.get (t.add 28) 4, rdRaw M.get (t.add 16) 4, t.add 28, rdRaw M.get (t.add 20) 4,
          rdRaw M.get (t.add 8) 4, rdRaw M.get (t.add 12) 4, rdRaw M.get (t.add 24) 4, efl F,
          ic + Nat.toUInt64 31⟩) := by
  run_chain h : 31 from ⟨M.get, v, ecx, edx, i, t, acc, esi, edi, 0x100D70, efl f, ic⟩
  refine ⟨_, _, _, ?_, h⟩
  simp only [wr4_get] <;> rfl

end Sodium.Proofs.Unpad
