import Sodium.Proofs.HexEncPre
import Solutions.Logic.Shb
/-!
# `sodium_hex2bin`: the instructions of the loop without an `ignore` set, one each, at any instruction count

The loop, from the load of a character to the branch on the state (0x10026d … 0x1002c2).

The memory `M` is any code-keeping memory. The stack pointer is `t` (after the prologue); the
arguments are at `t + 32 …`. Removes `Solutions.Logic.cbvZF` for `Solutions.Logic.Shb.cbvZFs` (the zero
flag of byte operations).
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

/-- `mov %ebx,%ebp`. -/
theorem s26d (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10026D, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, b, s, i, 0x10026F, efl F, ic⟩) := by
  cbv

/-- `mov 0x28(%esp),%ecx`. -/
theorem s26f (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10026F, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, rdRaw M.get (t.add 40) 4, d, b, t, p, s, i, 0x100273, efl F, ic⟩) := by
  cbv

/-- `mov %edx,4(%esp)`. -/
theorem s273 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) (ok : StoreOk Image.base Image.size M.mem (t.add 4)) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100273, efl F, ic⟩)) =
      some (St.m ⟨(CodeMem.wr4 M (t.add 4) d ok).get, a, c, d, b, t, p, s, i, 0x100277, efl F, ic⟩) := by
  cbv

/-- `movzbl (%ecx,%edx),%ecx`. -/
theorem s277 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat)
    (hT : (c.add d).toNat < M.get.size) (hTi : (c.add d).toNat < 0x100000 ∨ 0x100000 + 3560 ≤ (c.add d).toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100277, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, rdRaw M.get (c.add d) 1, d, b, t, p, s, i, 0x10027B, efl F, ic⟩) := by
  cbv

/-- `mov %ecx,%esi`. -/
theorem s27b (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10027B, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, c, i, 0x10027D, efl F, ic⟩) := by
  cbv

/-- `xor $0x30,%esi`. -/
theorem s27d (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10027D, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s.xor 48, i, 0x100280, efl (logicF 4 (s.xor 48)).2, ic⟩) := by
  cbv

/-- `lea -10(%esi),%edx`. -/
theorem s280 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100280, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, s.add 65526, b, t, p, s, i, 0x100286, efl F, ic⟩) := by
  cbv

/-- `shr $8,%edx`. -/
theorem s286 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100286, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d.shiftRight 8, b, t, p, s, i, 0x100289, efl (shFl 5 d 8), ic⟩) := by
  cbv

/-- `and $0xdf,%cl`. -/
theorem s289 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100289, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, (c.land 4294967040).lor (((c.land 255).land 223).land 255), d, b, t, p, s, i, 0x10028C, efl (logicF 1 ((c.land 255).land 223)).2, ic⟩) := by
  cbv

/-- `add $0xc9,%cl`. -/
theorem s28c (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10028C, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, (c.land 4294967040).lor ((addF 1 (c.land 255) 201 0).1.land 255), d, b, t, p, s, i, 0x10028F, efl (addF 1 (c.land 255) 201 0).2, ic⟩) := by
  cbv

/-- `movzbl %cl,%edi`. -/
theorem s28f (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10028F, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, c.land 255, 0x100292, efl F, ic⟩) := by
  cbv

/-- `lea -10(%edi),%ecx`. -/
theorem s292 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100292, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, i.add 65526, d, b, t, p, s, i, 0x100298, efl F, ic⟩) := by
  cbv

/-- `lea -16(%edi),%ebx`. -/
theorem s298 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100298, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, i.add 65520, t, p, s, i, 0x10029E, efl F, ic⟩) := by
  cbv

/-- `xor %ebx,%ecx`. -/
theorem s29e (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10029E, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c.xor b, d, b, t, p, s, i, 0x1002A0, efl (logicF 4 (c.xor b)).2, ic⟩) := by
  cbv

/-- `shr $8,%ecx`. -/
theorem s2a0 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1002A0, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c.shiftRight 8, d, b, t, p, s, i, 0x1002A3, efl (shFl 5 c 8), ic⟩) := by
  cbv

/-- `mov %edx,%ebx`. -/
theorem s2a3 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1002A3, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, d, t, p, s, i, 0x1002A5, efl F, ic⟩) := by
  cbv

/-- `or %cl,%bl`. -/
theorem s2a5 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1002A5, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, (b.land 4294967040).lor (((b.land 255).lor (c.land 255)).land 255), t, p, s, i, 0x1002A7, efl (logicF 1 ((b.land 255).lor (c.land 255))).2, ic⟩) := by
  cbv

/-- `mov $1,%bl`. -/
theorem s2a7 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1002A7, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, (b.land 4294967040).lor 1, t, p, s, i, 0x1002A9, efl F, ic⟩) := by
  cbv

/-- `mov %ebx,(%esp)`. -/
theorem s2a9 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) (ok : StoreOk Image.base Image.size M.mem t) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1002A9, efl F, ic⟩)) =
      some (St.m ⟨(CodeMem.wr4 M t b ok).get, a, c, d, b, t, p, s, i, 0x1002AC, efl F, ic⟩) := by
  cbv

/-- `je (not taken)`. -/
theorem s2ac (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) (r : UInt32) (hr : r.toNat ≠ 0) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1002AC, efl (logicF 1 r).2, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1002AE, efl (logicF 1 r).2, ic⟩) := by
  cbv

/-- `mov %ebp,%ebx`. -/
theorem s2ae (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1002AE, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, p, t, p, s, i, 0x1002B0, efl F, ic⟩) := by
  cbv

/-- `cmp 0x24(%esp),%ebp`. -/
theorem s2b0 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1002B0, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1002B4, efl (subF 4 p (rdRaw M.get (t.add 36) 4) 0).2, ic⟩) := by
  cbv

/-- `jae (not taken)`. -/
theorem s2b4 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) (q : UInt32) (h : p.toNat < q.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1002B4, efl (subF 4 p q 0).2, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1002BA, efl (subF 4 p q 0).2, ic⟩) := by
  cbv

/-- `and %edi,%ecx`. -/
theorem s2ba (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1002BA, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c.land i, d, b, t, p, s, i, 0x1002BC, efl (logicF 4 (c.land i)).2, ic⟩) := by
  cbv

/-- `and %esi,%edx`. -/
theorem s2bc (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1002BC, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d.land s, b, t, p, s, i, 0x1002BE, efl (logicF 4 (d.land s)).2, ic⟩) := by
  cbv

/-- `or %ecx,%edx`. -/
theorem s2be (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1002BE, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d.lor c, b, t, p, s, i, 0x1002C0, efl (logicF 4 (d.lor c)).2, ic⟩) := by
  cbv

/-- `test %al,%al (al = 0)`. -/
theorem s2c0z (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, 0, c, d, b, t, p, s, i, 0x1002C0, efl F, ic⟩)) =
      some (St.m ⟨M.get, 0, c, d, b, t, p, s, i, 0x1002C2, efl (logicF 1 0).2, ic⟩) := by
  cbv

/-- `test %al,%al (al = 0xff)`. -/
theorem s2c0f (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, 255, c, d, b, t, p, s, i, 0x1002C0, efl F, ic⟩)) =
      some (St.m ⟨M.get, 255, c, d, b, t, p, s, i, 0x1002C2, efl (logicF 1 255).2, ic⟩) := by
  cbv

/-- `jne (not taken)`. -/
theorem s2c2z (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, 0, c, d, b, t, p, s, i, 0x1002C2, efl (logicF 1 0).2, ic⟩)) =
      some (St.m ⟨M.get, 0, c, d, b, t, p, s, i, 0x1002C4, efl (logicF 1 0).2, ic⟩) := by
  cbv

/-- `jne (taken)`. -/
theorem s2c2f (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, 255, c, d, b, t, p, s, i, 0x1002C2, efl (logicF 1 255).2, ic⟩)) =
      some (St.m ⟨M.get, 255, c, d, b, t, p, s, i, 0x100250, efl (logicF 1 255).2, ic⟩) := by
  cbv

end Sodium.Proofs.HexDec
