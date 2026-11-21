import Sodium.Proofs.HexEncPre
import Solutions.Logic.Shb
/-!
# `sodium_hex2bin`: the instructions of the loop without an `ignore` set, one each, at any instruction count

The loop, from the branch on the state on (0x1002c4 … 0x100267, 0x100250 … 0x10025b).

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

/-- `shl $4,%dl`. -/
theorem s2c4 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1002C4, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, (d.land 4294967040).lor ((((d.land 255).shiftLeft 4).land 255).land 255), b, t, p, s, i, 0x1002C7, efl (shFl1 4 (d.land 255) 4), ic⟩) := by
  cbv

/-- `mov %edx,8(%esp)`. -/
theorem s2c7 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) (ok : StoreOk Image.base Image.size M.mem (t.add 8)) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1002C7, efl F, ic⟩)) =
      some (St.m ⟨(CodeMem.wr4 M (t.add 8) d ok).get, a, c, d, b, t, p, s, i, 0x1002CB, efl F, ic⟩) := by
  cbv

/-- `jmp`. -/
theorem s2cb (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1002CB, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10025C, efl F, ic⟩) := by
  cbv

/-- `not %al (al = 0)`. -/
theorem s25cz (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, 0, c, d, b, t, p, s, i, 0x10025C, efl F, ic⟩)) =
      some (St.m ⟨M.get, 255, c, d, b, t, p, s, i, 0x10025E, efl F, ic⟩) := by
  cbv

/-- `not %al (al = 0xff)`. -/
theorem s25cf (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, 255, c, d, b, t, p, s, i, 0x10025C, efl F, ic⟩)) =
      some (St.m ⟨M.get, 0, c, d, b, t, p, s, i, 0x10025E, efl F, ic⟩) := by
  cbv

/-- `mov 4(%esp),%edx`. -/
theorem s25e (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10025E, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, rdRaw M.get (t.add 4) 4, b, t, p, s, i, 0x100262, efl F, ic⟩) := by
  cbv

/-- `inc %edx`. -/
theorem s262 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100262, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d.add 1, b, t, p, s, i, 0x100263, efl (mixF F (addF 4 d 1 0).2 2260), ic⟩) := by
  cbv

/-- `cmp %edx,0x2c(%esp)`. -/
theorem s263 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100263, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100267, efl (subF 4 (rdRaw M.get (t.add 44) 4) d 0).2, ic⟩) := by
  cbv

/-- `je (not taken)`. -/
theorem s267b (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) (q : UInt32) (h : q.toNat ≠ d.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100267, efl (subF 4 q d 0).2, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10026D, efl (subF 4 q d 0).2, ic⟩) := by
  cbv

/-- `je (taken)`. -/
theorem s267x (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) (q : UInt32) (h : q.toNat = d.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100267, efl (subF 4 q d 0).2, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100305, efl (subF 4 q d 0).2, ic⟩) := by
  cbv

/-- `or 8(%esp),%dl`. -/
theorem s250 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100250, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, (d.land 4294967040).lor (((d.land 255).lor (rdRaw M.get (t.add 8) 1)).land 255), b, t, p, s, i, 0x100254, efl (logicF 1 ((d.land 255).lor (rdRaw M.get (t.add 8) 1))).2, ic⟩) := by
  cbv

/-- `mov 0x20(%esp),%ecx`. -/
theorem s254 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100254, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, rdRaw M.get (t.add 32) 4, d, b, t, p, s, i, 0x100258, efl F, ic⟩) := by
  cbv

/-- `movb %dl,(%ecx,%ebx)`. -/
theorem s258 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat)
    (hB : (c.add b).toNat < M.get.size) (hBi : (c.add b).toNat < 0x100000 ∨ 0x100000 + 3560 ≤ (c.add b).toNat)
    (ok : StoreOk1 Image.base Image.size M.mem (c.add b)) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100258, efl F, ic⟩)) =
      some (St.m ⟨(CodeMem.wr1 M (c.add b) (d.land 255) ok).get, a, c, d, b, t, p, s, i, 0x10025B, efl F, ic⟩) := by
  cbv

/-- `inc %ebx`. -/
theorem s25b (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10025B, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b.add 1, t, p, s, i, 0x10025C, efl (mixF F (addF 4 b 1 0).2 2260), ic⟩) := by
  cbv

end Sodium.Proofs.HexDec
