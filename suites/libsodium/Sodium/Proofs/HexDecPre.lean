import Sodium.Proofs.HexEncPre
import Solutions.Logic.Shb
/-!
# `sodium_hex2bin`: the prologue and the call on an empty text

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

/-- `push %ebp`. -/
theorem q090 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) (ok : StoreOk Image.base Image.size M.mem (t.add 24)) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t.add 28, p, s, i, 0x100090, efl F, ic⟩)) =
      some (St.m ⟨(CodeMem.wr4 M (t.add 24) p ok).get, a, c, d, b, t.add 24, p, s, i, 0x100091, efl F, ic⟩) := by
  cbv

/-- `push %ebx`. -/
theorem q091 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) (ok : StoreOk Image.base Image.size M.mem (t.add 20)) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t.add 24, p, s, i, 0x100091, efl F, ic⟩)) =
      some (St.m ⟨(CodeMem.wr4 M (t.add 20) b ok).get, a, c, d, b, t.add 20, p, s, i, 0x100092, efl F, ic⟩) := by
  cbv

/-- `push %edi`. -/
theorem q092 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) (ok : StoreOk Image.base Image.size M.mem (t.add 16)) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t.add 20, p, s, i, 0x100092, efl F, ic⟩)) =
      some (St.m ⟨(CodeMem.wr4 M (t.add 16) i ok).get, a, c, d, b, t.add 16, p, s, i, 0x100093, efl F, ic⟩) := by
  cbv

/-- `push %esi`. -/
theorem q093 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) (ok : StoreOk Image.base Image.size M.mem (t.add 12)) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t.add 16, p, s, i, 0x100093, efl F, ic⟩)) =
      some (St.m ⟨(CodeMem.wr4 M (t.add 12) s ok).get, a, c, d, b, t.add 12, p, s, i, 0x100094, efl F, ic⟩) := by
  cbv

/-- `sub $0xc,%esp`. -/
theorem q094 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t.add 12, p, s, i, 0x100094, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100097, efl (subF 4 (t.add 12) 12 0).2, ic⟩) := by
  cbv

/-- `mov 0x38(%esp),%ecx`. -/
theorem q097 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100097, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, rdRaw M.get (t.add 56) 4, d, b, t, p, s, i, 0x10009B, efl F, ic⟩) := by
  cbv

/-- `mov 0x34(%esp),%eax`. -/
theorem q09b (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10009B, efl F, ic⟩)) =
      some (St.m ⟨M.get, rdRaw M.get (t.add 52) 4, c, d, b, t, p, s, i, 0x10009F, efl F, ic⟩) := by
  cbv

/-- `mov 0x28(%esp),%ebp`. -/
theorem q09f (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10009F, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, rdRaw M.get (t.add 40) 4, s, i, 0x1000A3, efl F, ic⟩) := by
  cbv

/-- `cmpl $0,0x2c(%esp)`. -/
theorem q0a3 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1000A3, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1000A8, efl (subF 4 (rdRaw M.get (t.add 44) 4) 0 0).2, ic⟩) := by
  cbv

/-- `je (not taken)`. -/
theorem q0a8n (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) (q : UInt32) (h : q.toNat ≠ 0) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1000A8, efl (subF 4 q 0 0).2, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1000AE, efl (subF 4 q 0 0).2, ic⟩) := by
  cbv

/-- `je (taken)`. -/
theorem q0a8t (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) (q : UInt32) (h : q.toNat = 0) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1000A8, efl (subF 4 q 0 0).2, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10022A, efl (subF 4 q 0 0).2, ic⟩) := by
  cbv

/-- `xor %eax,%eax`. -/
theorem q0ae (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1000AE, efl F, ic⟩)) =
      some (St.m ⟨M.get, 0, c, d, b, t, p, s, i, 0x1000B0, efl (logicF 4 0).2, ic⟩) := by
  cbv

/-- `xor %ebx,%ebx`. -/
theorem q0b0 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1000B0, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, 0, t, p, s, i, 0x1000B2, efl (logicF 4 0).2, ic⟩) := by
  cbv

/-- `xor %edx,%edx`. -/
theorem q0b2 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1000B2, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, 0, b, t, p, s, i, 0x1000B4, efl (logicF 4 0).2, ic⟩) := by
  cbv

/-- `cmpl $0,0x30(%esp)`. -/
theorem q0b4 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1000B4, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1000B9, efl (subF 4 (rdRaw M.get (t.add 48) 4) 0 0).2, ic⟩) := by
  cbv

/-- `je (taken)`. -/
theorem q0b9 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) (q : UInt32) (h : q.toNat = 0) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x1000B9, efl (subF 4 q 0 0).2, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100243, efl (subF 4 q 0 0).2, ic⟩) := by
  cbv

/-- `movl $0,8(%esp)`. -/
theorem q243 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) (ok : StoreOk Image.base Image.size M.mem (t.add 8)) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100243, efl F, ic⟩)) =
      some (St.m ⟨(CodeMem.wr4 M (t.add 8) 0 ok).get, a, c, d, b, t, p, s, i, 0x10024B, efl F, ic⟩) := by
  cbv

/-- `jmp`. -/
theorem q24b (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10024B, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10026D, efl F, ic⟩) := by
  cbv

/-- `xor %ebx,%ebx`. -/
theorem z22a (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10022A, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, 0, t, p, s, i, 0x10022C, efl (logicF 4 0).2, ic⟩) := by
  cbv

/-- `test %ecx,%ecx`. -/
theorem z22c (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10022C, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10022E, efl (logicF 4 c).2, ic⟩) := by
  cbv

/-- `mov $0,%esi`. -/
theorem z22e (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10022E, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, 0, i, 0x100233, efl F, ic⟩) := by
  cbv

/-- `mov $0,%edx`. -/
theorem z233 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100233, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, 0, b, t, p, s, i, 0x100238, efl F, ic⟩) := by
  cbv

/-- `jne (not taken)`. -/
theorem z238 (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, 0, d, b, t, p, s, i, 0x100238, efl (logicF 4 0).2, ic⟩)) =
      some (St.m ⟨M.get, a, 0, d, b, t, p, s, i, 0x10023E, efl (logicF 4 0).2, ic⟩) := by
  cbv

/-- `jmp`. -/
theorem z23e (M : SMem) (a c d b t p s i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 64 ≤ M.get.size) (hap : t.toNat + 64 ≤ 0x100000 ∨ 0x100000 + 3560 ≤ t.toNat) :
    okState (execInstr (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x10023E, efl F, ic⟩)) =
      some (St.m ⟨M.get, a, c, d, b, t, p, s, i, 0x100393, efl F, ic⟩) := by
  cbv

end Sodium.Proofs.HexDec
