import Solutions.OpensslSha256.Fam.FX
import Solutions.Logic.Flags
/-! The loop branch of the block function taken: `jne 0x100390` at `0x101190` after `decl %esi` with
a count other than 1. -/
namespace Solutions.OpensslSha256
open X86 Solutions.Logic Solutions.Exec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000
set_option Elab.async false
attribute [local cbv_eval] execOp0F_x185 efl_mix_zf

theorem famJNE_T (G : CodeMem 0x101190 6 (codeOf [0x0f, 0x85, 0xfa, 0xf1, 0xff, 0xff])) (r : R) (fl c : UInt32)
    (ic : UInt64) (hc : c.toNat ≠ 1) (hp : (0x101190 : UInt32).toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r (mixF fl (subF 4 c 1 0).2 2260) 0x101190 ic)) =
      some (conc G.get r (mixF fl (subF 4 c 1 0).2 2260) 0x100390 ic) := by
  cbv

end Solutions.OpensslSha256
