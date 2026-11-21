import Solutions.Logic.Cbx
import Solutions.Exec.Dispatch
import Solutions.Exec.Call
import Solutions.Logic.MemRules
import Solutions.Logic.Path
import Sodium.Proofs.Code
import Solutions.Logic.Cmp
/-!
# `sodium_bin2hex`: the prologue and the call on an empty input, in short segments

```
100000 push %ebp; push %ebx; push %edi; push %esi; push %eax
100005 mov 0x24(%esp),%ebp          (n)
100009 cmp $0x7ffffffe,%ebp; ja misuse
100011 lea (%ebp,%ebp),%ecx; cmp %ecx,0x1c(%esp); jbe misuse   (2n < cap)
10001b mov 0x18(%esp),%eax          (hex)
10001f test %ebp,%ebp; je 100077
100023 mov %ecx,(%esp); mov 0x20(%esp),%esi; xor %edi,%edi; nop × 4
100030 … loop (`HexEncSteps`) …
100077 xor %ecx,%ecx
100079 movb $0,(%eax,%ecx); add $4,%esp; pop %esi; pop %edi; pop %ebx; pop %ebp; ret
```

The stack pointer after the pushes is `t`; the entry stack pointer is `t + 20`.
-/
namespace Sodium.Proofs.HexEnc
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Solutions.Logic.Bytes Solutions.Logic.Cmp Sodium.Proofs Sodium.Utils
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr
attribute [-cbv_eval] Solutions.Logic.rdBytes_codeMem

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000

/-- The image lies apart from the stack words `[t - 108, t + 40)`. -/
def StackApart (t : UInt32) : Prop := t.toNat + 40 ≤ 0x100000 ∨ 0x100000 + 3560 + 108 ≤ t.toNat

/-- The saved registers. -/
def Fr (G : SMem) (t a b c d e : UInt32) (ok1 : StoreOk Image.base Image.size G.mem (t.add 16))
    (ok2 : StoreOk Image.base Image.size (CodeMem.wr4 G (t.add 16) a ok1).mem (t.add 12))
    (ok3 : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 G (t.add 16) a ok1) (t.add 12) b ok2).mem (t.add 8))
    (ok4 : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 (CodeMem.wr4 G (t.add 16) a ok1) (t.add 12) b ok2)
      (t.add 8) c ok3).mem (t.add 4))
    (ok5 : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 (CodeMem.wr4 (CodeMem.wr4 G (t.add 16) a ok1)
      (t.add 12) b ok2) (t.add 8) c ok3) (t.add 4) d ok4).mem t) : SMem :=
  CodeMem.wr4 (CodeMem.wr4 (CodeMem.wr4 (CodeMem.wr4 (CodeMem.wr4 G (t.add 16) a ok1) (t.add 12) b ok2) (t.add 8) c ok3)
    (t.add 4) d ok4) t e ok5


section seg
variable (G : SMem) (eax ecx edx ebx t ebp esi edi f : UInt32)
  (ok1 : StoreOk Image.base Image.size G.mem (t.add 16))
  (ok2 : StoreOk Image.base Image.size (CodeMem.wr4 G (t.add 16) ebp ok1).mem (t.add 12))
  (ok3 : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 G (t.add 16) ebp ok1) (t.add 12) ebx ok2).mem (t.add 8))
  (ok4 : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 (CodeMem.wr4 G (t.add 16) ebp ok1) (t.add 12) ebx ok2)
    (t.add 8) edi ok3).mem (t.add 4))
  (ok5 : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 (CodeMem.wr4 (CodeMem.wr4 G (t.add 16) ebp ok1)
    (t.add 12) ebx ok2) (t.add 8) edi ok3) (t.add 4) esi ok4).mem t)
  (ok6 : StoreOk Image.base Image.size (Fr G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5).mem t)
  (hsz : G.get.size ≤ 4273995776) (hst : t.toNat + 40 ≤ G.get.size) (hap : StackApart t)
  (hn : (rdRaw G.get (t.add 36) 4).toNat < 1073741824)
  (hcap : 2 * (rdRaw G.get (t.add 36) 4).toNat < (rdRaw G.get (t.add 28) 4).toNat)

include hsz hst hap in
/-- The pushes and the length load. -/
theorem seg1 :
    runOkP img 6 (St.m ⟨G.get, eax, ecx, edx, ebx, t.add 20, ebp, esi, edi, 0x100000, efl f, 0⟩) =
      some (St.m ⟨(Fr G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5).get, eax, ecx, edx, ebx, t, rdRaw G.get (t.add 36) 4, esi, edi, 0x100009, efl f, 6⟩,
        [1048576, 1048577, 1048578, 1048579, 1048580, 1048581]) := by
  unfold StackApart at hap; cbv

include hsz hst hap hn hcap in
/-- The two argument checks (both pass). -/
theorem seg2a :
    runOkP img 5 (St.m ⟨(Fr G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5).get, eax, ecx, edx, ebx, t, rdRaw G.get (t.add 36) 4, esi, edi, 0x100009, efl f, 6⟩) =
      some (St.m ⟨(Fr G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5).get, eax, (rdRaw G.get (t.add 36) 4).add (rdRaw G.get (t.add 36) 4), edx, ebx, t, rdRaw G.get (t.add 36) 4, esi, edi, 0x10001B,
        efl (subF 4 (rdRaw G.get (t.add 28) 4) ((rdRaw G.get (t.add 36) 4).add (rdRaw G.get (t.add 36) 4)) 0).2, 11⟩,
        [1048585, 1048591, 1048593, 1048597, 1048601]) := by
  unfold StackApart at hap; cbv

include hsz hst hap hn in
/-- A non-empty input: the output pointer, `2n` kept on the stack. -/
theorem seg2b (hz : 0 < (rdRaw G.get (t.add 36) 4).toNat) :
    runOkP img 4 (St.m ⟨(Fr G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5).get, eax, (rdRaw G.get (t.add 36) 4).add (rdRaw G.get (t.add 36) 4), edx, ebx, t, rdRaw G.get (t.add 36) 4, esi, edi, 0x10001B, efl f, 11⟩) =
      some (St.m ⟨(CodeMem.wr4 (Fr G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5) t ((rdRaw G.get (t.add 36) 4).add (rdRaw G.get (t.add 36) 4)) ok6).get, rdRaw G.get (t.add 24) 4,
        (rdRaw G.get (t.add 36) 4).add (rdRaw G.get (t.add 36) 4), edx, ebx, t, rdRaw G.get (t.add 36) 4, esi, edi, 0x100026, efl (logicF 4 (rdRaw G.get (t.add 36) 4)).2, 15⟩,
        [1048603, 1048607, 1048609, 1048611]) := by
  unfold StackApart at hap; cbv

include hsz hst hap in
/-- The input pointer, the index, the padding. -/
theorem seg3 (P c : UInt32) :
    runOkP img 6 (St.m ⟨(CodeMem.wr4 (Fr G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5) t c ok6).get, P, c, edx, ebx, t, rdRaw G.get (t.add 36) 4, esi, edi, 0x100026, efl f, 15⟩) =
      some (St.m ⟨(CodeMem.wr4 (Fr G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5) t c ok6).get, P, c, edx, ebx, t, rdRaw G.get (t.add 36) 4, rdRaw G.get (t.add 32) 4, 0, 0x100030,
        efl (logicF 4 0).2, 21⟩, [1048614, 1048618, 1048620, 1048621, 1048622, 1048623]) := by
  unfold StackApart at hap; cbv

include hsz hst hap in
/-- An empty input: to the terminating store. -/
theorem segz1 (hz : (rdRaw G.get (t.add 36) 4).toNat = 0) :
    runOkP img 4 (St.m ⟨(Fr G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5).get, eax, (rdRaw G.get (t.add 36) 4).add (rdRaw G.get (t.add 36) 4), edx, ebx, t, rdRaw G.get (t.add 36) 4, esi, edi, 0x10001B, efl f, 11⟩) =
      some (St.m ⟨(Fr G t ebp ebx edi esi eax ok1 ok2 ok3 ok4 ok5).get, rdRaw G.get (t.add 24) 4, 0, edx, ebx, t, rdRaw G.get (t.add 36) 4, esi, edi, 0x100079,
        efl (logicF 4 0).2, 15⟩, [1048603, 1048607, 1048609, 1048695]) := by
  unfold StackApart at hap; cbv

end seg

end Sodium.Proofs.HexEnc
