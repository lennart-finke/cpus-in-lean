import Sodium.Proofs.HexEncPre
import Solutions.Logic.Shb
/-!
# `sodium_hex2bin`: after the loop: the checks, the stored length, the return

One instruction each, at any instruction count, over any code-keeping memory `M`. The stack pointer
after the prologue is `t`; the entry stack pointer `t + 28`, the arguments at `t + 32 …`.
-/
namespace Sodium.Proofs.HexDec
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Solutions.Logic.Bytes Solutions.Logic.Cmp Solutions.Logic.Shb Sodium.Proofs Sodium.Utils
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr
attribute [-cbv_eval] Solutions.Logic.rdBytes_codeMem
attribute [-cbvSimprocAttr] Solutions.Logic.cbvZF

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000

/-- `mov 0x2c(%esp),%edx`. -/
theorem x305 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100305, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, rdRaw M.get (t.add 44) 4, b, t, p, s, i, 0x100309, efl F, ic⟩) := by
  cbv

/-- `mov 0x38(%esp),%ecx`. -/
theorem x309 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100309, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, rdRaw M.get (t.add 56) 4, d, b, t, p, s, i, 0x10030D, efl F, ic⟩) := by
  cbv

/-- `test %al,%al (al = 0)`. -/
theorem x30d (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, 0, c, d, b, t, p, s, i, 0x10030D, efl F, ic⟩)) =
      some (St.m ⟨M.get, 0, c, d, b, t, p, s, i, 0x10030F, efl (logicF 1 0).2, ic⟩) := by
  cbv

/-- `jne (not taken)`. -/
theorem x30f (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, 0, c, d, b, t, p, s, i, 0x10030F, efl (logicF 1 0).2, ic⟩)) =
      some (St.m ⟨M.get, 0, c, d, b, t, p, s, i, 0x100311, efl (logicF 1 0).2, ic⟩) := by
  cbv

/-- `mov (%esp),%eax`. -/
theorem x311 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100311, efl F, ic⟩)) =
      some (St.m ⟨M.get, rdRaw M.get t 4, c, d, b, t, p, s, i, 0x100314, efl F, ic⟩) := by
  cbv

/-- `movzbl %al,%esi`. -/
theorem x314 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100314, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, a.land 255, i, 0x100317, efl F, ic⟩) := by
  cbv

/-- `dec %esi (esi = 1)`. -/
theorem x317 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, 1, i, 0x100317, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, 0, i, 0x100318, efl (mixF F (subF 4 1 1 0).2 2260), ic⟩) := by
  cbv

/-- `xor %edi,%edi`. -/
theorem x318 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100318, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, 0, 0x10031A, efl (logicF 4 0).2, ic⟩) := by
  cbv

/-- `test %al,%al`. -/
theorem x31a (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10031A, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10031C, efl (logicF 1 (a.land 255)).2, ic⟩) := by
  cbv

/-- `cmove %edi,%ebx (not taken)`. -/
theorem x31c (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10031C, efl (logicF 1 1).2, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10031F, efl (logicF 1 1).2, ic⟩) := by
  cbv

/-- `mov 0x34(%esp),%eax`. -/
theorem x31f (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10031F, efl F, ic⟩)) =
      some (St.m ⟨M.get, rdRaw M.get (t.add 52) 4, c, d, b, t, p, s, i, 0x100323, efl F, ic⟩) := by
  cbv

/-- `mov 0x28(%esp),%ebp`. -/
theorem x323 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100323, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, rdRaw M.get (t.add 40) 4, s, i, 0x100327, efl F, ic⟩) := by
  cbv

/-- `jmp`. -/
theorem x327 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100327, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10038B, efl F, ic⟩) := by
  cbv

/-- `test %ecx,%ecx`. -/
theorem x38b (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10038B, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10038D, efl (logicF 4 c).2, ic⟩) := by
  cbv

/-- `je (taken)`. -/
theorem x38d (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, 0, d, b, t, p, s, i, 0x10038D, efl (logicF 4 0).2, ic⟩)) =
      some (St.m ⟨M.get, a, 0, d, b, t, p, s, i, 0x1003A3, efl (logicF 4 0).2, ic⟩) := by
  cbv

/-- `cmp 0x2c(%esp),%edx`. -/
theorem x3a3 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1003A3, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1003A7, efl (subF 4 d (rdRaw M.get (t.add 44) 4) 0).2, ic⟩) := by
  cbv

/-- `je (taken)`. -/
theorem x3a7 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) (q : UInt32) (h : d.toNat = q.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1003A7, efl (subF 4 d q 0).2, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100393, efl (subF 4 d q 0).2, ic⟩) := by
  cbv

/-- `test %eax,%eax`. -/
theorem x393 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100393, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100395, efl (logicF 4 a).2, ic⟩) := by
  cbv

/-- `je (not taken)`. -/
theorem x395 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) (h : a.toNat ≠ 0) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100395, efl (logicF 4 a).2, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100397, efl (logicF 4 a).2, ic⟩) := by
  cbv

/-- `mov %ebx,(%eax)`. -/
theorem x397 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat)
    (ha1 : a.toNat + 4 ≤ M.get.size) (ha2 : a.toNat + 4 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ a.toNat)
    (ok : StoreOk Image.base Image.size M.mem a) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100397, efl F, ic⟩)) =
      some (St.m ⟨(CodeMem.wr4 M a b ok).get, a, c, d, b, t, p, s, i, 0x100399, efl F, ic⟩) := by
  cbv

/-- `mov %esi,%eax`. -/
theorem x399 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100399, efl F, ic⟩)) =
      some (St.m ⟨M.get, s, c, d, b, t, p, s, i, 0x10039B, efl F, ic⟩) := by
  cbv

/-- `add $0xc,%esp`. -/
theorem x39b (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10039B, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t.add 12, p, s, i, 0x10039E, efl (addF 4 t 12 0).2, ic⟩) := by
  cbv

/-- `pop %esi`. -/
theorem x39e (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t.add 12, p, s, i, 0x10039E, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t.add 16, p, rdRaw M.get (t.add 12) 4, i, 0x10039F, efl F, ic⟩) := by
  cbv

/-- `pop %edi`. -/
theorem x39f (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t.add 16, p, s, i, 0x10039F, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t.add 20, p, s, rdRaw M.get (t.add 16) 4, 0x1003A0, efl F, ic⟩) := by
  cbv

/-- `pop %ebx`. -/
theorem x3a0 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t.add 20, p, s, i, 0x1003A0, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, rdRaw M.get (t.add 20) 4, t.add 24, p, s, i, 0x1003A1, efl F, ic⟩) := by
  cbv

/-- `pop %ebp`. -/
theorem x3a1 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t.add 24, p, s, i, 0x1003A1, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t.add 28, rdRaw M.get (t.add 24) 4, s, i, 0x1003A2, efl F, ic⟩) := by
  cbv

/-- `ret`. -/
theorem x3a2 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t.add 28, p, s, i, 0x1003A2, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t.add 32, p, s, i, rdRaw M.get (t.add 28) 4, efl F, ic⟩) := by
  cbv

end Sodium.Proofs.HexDec
