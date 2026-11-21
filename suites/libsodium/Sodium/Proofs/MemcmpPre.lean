import Solutions.Logic.Cbx
import Solutions.Exec.Dispatch
import Solutions.Exec.Call
import Solutions.Logic.MemRules
import Solutions.Logic.Path
import Sodium.Proofs.Code
/-!
# `sodium_memcmp`: the prologue, in short segments

```
100c30 push %esi                   100c4d test %eax,%eax
100c31 sub $0xc,%esp               100c4f je 100c78
100c34 mov 0x1c(%esp),%eax         100c51 xor %ecx,%ecx
100c38 mov 0x18(%esp),%ecx         100c53 … 100c5f nop × 13
100c3c mov 0x14(%esp),%edx
100c40 mov %edx,0x8(%esp)          100c78 movzbl 0x3(%esp),%ecx; dec %ecx; xor %eax,%eax
100c44 mov %ecx,0x4(%esp)          100c80 bt $0x8,%ecx; adc $-1,%eax
100c48 movb $0x0,0x3(%esp)         100c87 add $0xc,%esp; pop %esi; ret
```

The stack pointer after the prologue is `t`; the entry stack pointer is `t + 16`. The frame `Fr`
holds the saved `esi` at `t + 12`, the two pointers at `t + 8` and `t + 4`; the accumulator byte is
at `t + 3`, stored on top of the frame (`CodeMem.wr1`). Each segment is a separate `cbv` proof of a
few steps (to keep each kernel check small); `runOkP_split` joins them.
-/
namespace Sodium.Proofs.Memcmp
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Solutions.Logic.Bytes Sodium.Proofs Sodium.Utils
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr
attribute [-cbv_eval] Solutions.Logic.rdBytes_codeMem

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000

/-- The image lies apart from the stack words `[t - 112, t + 32)`. -/
def StackApart (t : UInt32) : Prop := t.toNat + 32 ≤ 0x100000 ∨ 0x100000 + 3560 + 112 ≤ t.toNat

/-- The frame: the saved `esi` and the two buffer pointers. -/
def Fr (G : SMem) (t e A B : UInt32) (ok0 : StoreOk Image.base Image.size G.mem (t.add 12))
    (okA : StoreOk Image.base Image.size (CodeMem.wr4 G (t.add 12) e ok0).mem (t.add 8))
    (okB : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 G (t.add 12) e ok0) (t.add 8) A okA).mem
      (t.add 4)) : SMem :=
  CodeMem.wr4 (CodeMem.wr4 (CodeMem.wr4 G (t.add 12) e ok0) (t.add 8) A okA) (t.add 4) B okB

/-- The addresses of the prologue. -/
def prePath : List UInt32 :=
  [1051696, 1051697, 1051700, 1051704, 1051708, 1051712, 1051716, 1051720, 1051725, 1051727, 1051729, 1051731,
   1051732, 1051733, 1051734, 1051735, 1051736, 1051737, 1051738, 1051739, 1051740, 1051741, 1051742, 1051743]

/-- The result the epilogue computes from the accumulator `x`. -/
noncomputable def eaxZ (x : UInt32) : UInt32 :=
  (addF 4 0 4294967295
    (if Bool.rec true false (decide ((if Bool.rec true false (decide (((UInt32.add x 4294967295).shiftRight 8).land 1
        = 0)) = true then Flag.CF else 0).land 1 = 0)) = true then 1 else 0)).1

/-- The addresses of a call on an empty buffer. -/
def zeroPath : List UInt32 :=
  [1051696, 1051697, 1051700, 1051704, 1051708, 1051712, 1051716, 1051720, 1051725, 1051727, 1051768, 1051773,
   1051774, 1051776, 1051780, 1051783, 1051786, 1051787]

section seg
variable (G : SMem) (eax ecx edx ebx t ebp esi edi f : UInt32)
  (hsz : G.get.size ≤ 4273995776) (hst : t.toNat + 32 ≤ G.get.size) (hap : StackApart t)
  (ok0 : StoreOk Image.base Image.size G.mem (t.add 12))
  (okA : StoreOk Image.base Image.size (CodeMem.wr4 G (t.add 12) esi ok0).mem (t.add 8))
  (okB : StoreOk Image.base Image.size
    (CodeMem.wr4 (CodeMem.wr4 G (t.add 12) esi ok0) (t.add 8) (rdRaw G.get (t.add 20) 4) okA).mem (t.add 4))
  (ok3 : StoreOk1 Image.base Image.size
    (Fr G t esi (rdRaw G.get (t.add 20) 4) (rdRaw G.get (t.add 24) 4) ok0 okA okB).mem (t.add 3))

include hsz hst hap in
/-- `push %esi; sub $0xc,%esp`. -/
theorem seg1 :
    runOkP img 2 (St.m ⟨G.get, eax, ecx, edx, ebx, t.add 16, ebp, esi, edi, 0x100C30, efl f, 0⟩) =
      some (St.m ⟨(CodeMem.wr4 G (t.add 12) esi ok0).get, eax, ecx, edx, ebx, t, ebp, esi, edi, 0x100C34,
        efl (subF 4 (t.add 12) 12 0).2, 2⟩, [1051696, 1051697]) := by
  unfold StackApart at hap
  cbv

include hsz hst hap in
/-- The three argument loads. -/
theorem seg2 :
    runOkP img 3 (St.m ⟨(CodeMem.wr4 G (t.add 12) esi ok0).get, eax, ecx, edx, ebx, t, ebp, esi, edi, 0x100C34,
        efl f, 2⟩) =
      some (St.m ⟨(CodeMem.wr4 G (t.add 12) esi ok0).get, rdRaw G.get (t.add 28) 4, rdRaw G.get (t.add 24) 4,
        rdRaw G.get (t.add 20) 4, ebx, t, ebp, esi, edi, 0x100C40, efl f, 5⟩, [1051700, 1051704, 1051708]) := by
  unfold StackApart at hap
  cbv

include hsz hst hap in
/-- The two pointer stores and the accumulator store. -/
theorem seg3 :
    runOkP img 3 (St.m ⟨(CodeMem.wr4 G (t.add 12) esi ok0).get, eax, rdRaw G.get (t.add 24) 4,
        rdRaw G.get (t.add 20) 4, ebx, t, ebp, esi, edi, 0x100C40, efl f, 5⟩) =
      some (St.m ⟨(CodeMem.wr1 (Fr G t esi (rdRaw G.get (t.add 20) 4) (rdRaw G.get (t.add 24) 4) ok0 okA okB)
          (t.add 3) 0 ok3).get, eax, rdRaw G.get (t.add 24) 4, rdRaw G.get (t.add 20) 4, ebx, t, ebp, esi, edi,
          0x100C4D, efl f, 8⟩, [1051712, 1051716, 1051720]) := by
  unfold StackApart at hap
  cbv

include hsz hst hap in
/-- `test %eax,%eax; je` (not taken); `xor %ecx,%ecx`. -/
theorem seg4 (hn : 0 < (rdRaw G.get (t.add 28) 4).toNat) :
    runOkP img 3 (St.m ⟨(CodeMem.wr1 (Fr G t esi (rdRaw G.get (t.add 20) 4) (rdRaw G.get (t.add 24) 4) ok0 okA okB)
          (t.add 3) 0 ok3).get, rdRaw G.get (t.add 28) 4, rdRaw G.get (t.add 24) 4, rdRaw G.get (t.add 20) 4, ebx,
          t, ebp, esi, edi, 0x100C4D, efl f, 8⟩) =
      some (St.m ⟨(CodeMem.wr1 (Fr G t esi (rdRaw G.get (t.add 20) 4) (rdRaw G.get (t.add 24) 4) ok0 okA okB)
          (t.add 3) 0 ok3).get, rdRaw G.get (t.add 28) 4, 0, rdRaw G.get (t.add 20) 4, ebx, t, ebp, esi, edi,
          0x100C53, efl (logicF 4 0).2, 11⟩, [1051725, 1051727, 1051729]) := by
  unfold StackApart at hap
  cbv

include hsz hst hap in
/-- `test %eax,%eax; je` (taken). -/
theorem segz1 (hn : (rdRaw G.get (t.add 28) 4).toNat = 0) :
    runOkP img 2 (St.m ⟨(CodeMem.wr1 (Fr G t esi (rdRaw G.get (t.add 20) 4) (rdRaw G.get (t.add 24) 4) ok0 okA okB)
          (t.add 3) 0 ok3).get, rdRaw G.get (t.add 28) 4, rdRaw G.get (t.add 24) 4, rdRaw G.get (t.add 20) 4, ebx,
          t, ebp, esi, edi, 0x100C4D, efl f, 8⟩) =
      some (St.m ⟨(CodeMem.wr1 (Fr G t esi (rdRaw G.get (t.add 20) 4) (rdRaw G.get (t.add 24) 4) ok0 okA okB)
          (t.add 3) 0 ok3).get, rdRaw G.get (t.add 28) 4, rdRaw G.get (t.add 24) 4, rdRaw G.get (t.add 20) 4, ebx,
          t, ebp, esi, edi, 0x100C78, efl (logicF 4 (rdRaw G.get (t.add 28) 4)).2, 10⟩, [1051725, 1051727]) := by
  unfold StackApart at hap
  cbv

include hsz hst hap in
/-- `movzbl 0x3(%esp),%ecx; dec %ecx; xor %eax,%eax` on the zero accumulator. -/
theorem segz2 :
    runOkP img 3 (St.m ⟨(CodeMem.wr1 (Fr G t esi (rdRaw G.get (t.add 20) 4) (rdRaw G.get (t.add 24) 4) ok0 okA okB)
          (t.add 3) 0 ok3).get, eax, ecx, edx, ebx, t, ebp, esi, edi, 0x100C78, efl f, 10⟩) =
      some (St.m ⟨(CodeMem.wr1 (Fr G t esi (rdRaw G.get (t.add 20) 4) (rdRaw G.get (t.add 24) 4) ok0 okA okB)
          (t.add 3) 0 ok3).get, 0, UInt32.add 0 4294967295, edx, ebx, t, ebp, esi, edi, 0x100C80,
          efl (logicF 4 0).2, 13⟩, [1051768, 1051773, 1051774]) := by
  unfold StackApart at hap
  cbv

include hsz hst hap in
/-- `bt; adc; add $0xc,%esp; pop %esi; ret` on the zero accumulator. -/
theorem segz3 :
    runOkP img 5 (St.m ⟨(CodeMem.wr1 (Fr G t esi (rdRaw G.get (t.add 20) 4) (rdRaw G.get (t.add 24) 4) ok0 okA okB)
          (t.add 3) 0 ok3).get, 0, UInt32.add 0 4294967295, edx, ebx, t, ebp, esi, edi, 0x100C80,
          efl (logicF 4 0).2, 13⟩) =
      some (St.m ⟨(CodeMem.wr1 (Fr G t esi (rdRaw G.get (t.add 20) 4) (rdRaw G.get (t.add 24) 4) ok0 okA okB)
          (t.add 3) 0 ok3).get, eaxZ 0, UInt32.add 0 4294967295, edx, ebx, t.add 20, ebp, esi,
          edi, rdRaw G.get (t.add 16) 4, efl (addF 4 t 12 0).2, 18⟩, [1051776, 1051780, 1051783, 1051786, 1051787]) := by
  unfold StackApart at hap
  cbv
  -- the two sides differ only in `Decidable` instances inside the result; fix the conditions
  congr
  have hc1 : @Bool.rec (fun _ => Bool) true false
      (decide (((UInt32.add 0 4294967295).shiftRight 8).land 1 = 0)) = true := by decide
  have hc2 : @Bool.rec (fun _ => Bool) true false (decide ((Flag.CF).land 1 = 0)) = true := by decide
  simp only [if_pos hc1, if_pos hc2]

end seg

/-- Seven `nop`s. -/
theorem nops7 (M : SMem) (eax ecx edx ebx t ebp esi edi f : UInt32) (hsz : M.get.size ≤ 4273995776) :
    runOkP img 7 (St.m ⟨M.get, eax, ecx, edx, ebx, t, ebp, esi, edi, 0x100C53, efl f, 11⟩) =
      some (St.m ⟨M.get, eax, ecx, edx, ebx, t, ebp, esi, edi, 0x100C5A, efl f, 18⟩,
        [1051731, 1051732, 1051733, 1051734, 1051735, 1051736, 1051737]) := by
  cbv

/-- Six `nop`s. -/
theorem nops6 (M : SMem) (eax ecx edx ebx t ebp esi edi f : UInt32) (hsz : M.get.size ≤ 4273995776) :
    runOkP img 6 (St.m ⟨M.get, eax, ecx, edx, ebx, t, ebp, esi, edi, 0x100C5A, efl f, 18⟩) =
      some (St.m ⟨M.get, eax, ecx, edx, ebx, t, ebp, esi, edi, 0x100C60, efl f, 24⟩,
        [1051738, 1051739, 1051740, 1051741, 1051742, 1051743]) := by
  cbv

/-- From the entry to the loop head, for a non-empty buffer. -/
theorem run_pre (G : SMem) (eax ecx edx ebx t ebp esi edi f : UInt32)
    (hsz : G.get.size ≤ 4273995776) (hst : t.toNat + 32 ≤ G.get.size) (hap : StackApart t)
    (hn : 0 < (rdRaw G.get (t.add 28) 4).toNat)
    (ok0 : StoreOk Image.base Image.size G.mem (t.add 12))
    (okA : StoreOk Image.base Image.size (CodeMem.wr4 G (t.add 12) esi ok0).mem (t.add 8))
    (okB : StoreOk Image.base Image.size
      (CodeMem.wr4 (CodeMem.wr4 G (t.add 12) esi ok0) (t.add 8) (rdRaw G.get (t.add 20) 4) okA).mem (t.add 4))
    (ok3 : StoreOk1 Image.base Image.size
      (Fr G t esi (rdRaw G.get (t.add 20) 4) (rdRaw G.get (t.add 24) 4) ok0 okA okB).mem (t.add 3)) :
    runOkP img 24 (St.m ⟨G.get, eax, ecx, edx, ebx, t.add 16, ebp, esi, edi, 0x100C30, efl f, 0⟩) =
      some (St.m ⟨(CodeMem.wr1 (Fr G t esi (rdRaw G.get (t.add 20) 4) (rdRaw G.get (t.add 24) 4) ok0 okA okB)
          (t.add 3) 0 ok3).get, rdRaw G.get (t.add 28) 4, 0, rdRaw G.get (t.add 20) 4, ebx, t, ebp, esi, edi,
          0x100C60, efl (logicF 4 0).2, 24⟩, prePath) := by
  have hM : (CodeMem.wr1 (Fr G t esi (rdRaw G.get (t.add 20) 4) (rdRaw G.get (t.add 24) 4) ok0 okA okB)
      (t.add 3) 0 ok3).get.size ≤ 4273995776 := by
    rw [wr1_get_size]; unfold Fr; rw [wr4_get_size, wr4_get_size, wr4_get_size]; exact hsz
  have s1 := seg1 (G := G) (eax := eax) (ecx := ecx) (edx := edx) (ebx := ebx) (t := t) (ebp := ebp)
    (esi := esi) (edi := edi) (f := f) (ok0 := ok0) (hsz := hsz) (hst := hst) (hap := hap)
  have s2 := seg2 (G := G) (eax := eax) (ecx := ecx) (edx := edx) (ebx := ebx) (t := t) (ebp := ebp)
    (esi := esi) (edi := edi) (f := (subF 4 (t.add 12) 12 0).2) (ok0 := ok0) (hsz := hsz) (hst := hst)
    (hap := hap)
  have s3 := seg3 (G := G) (eax := rdRaw G.get (t.add 28) 4) (ebx := ebx) (t := t) (ebp := ebp)
    (esi := esi) (edi := edi) (f := (subF 4 (t.add 12) 12 0).2) (ok0 := ok0) (okA := okA) (okB := okB)
    (ok3 := ok3) (hsz := hsz) (hst := hst) (hap := hap)
  have s4 := seg4 (G := G) (ebx := ebx) (t := t) (ebp := ebp) (esi := esi) (edi := edi)
    (f := (subF 4 (t.add 12) 12 0).2) (ok0 := ok0) (okA := okA) (okB := okB) (ok3 := ok3) (hsz := hsz)
    (hst := hst) (hap := hap) hn
  have s5 := nops7 _ (rdRaw G.get (t.add 28) 4) 0 (rdRaw G.get (t.add 20) 4) ebx t ebp esi edi (logicF 4 0).2 hM
  have s6 := nops6 _ (rdRaw G.get (t.add 28) 4) 0 (rdRaw G.get (t.add 20) 4) ebx t ebp esi edi (logicF 4 0).2 hM
  exact runOkP_split (runOkP_split (runOkP_split (runOkP_split (runOkP_split s1 s2) s3) s4) s5) s6

/-- From the entry to the return, for an empty buffer. -/
theorem run_zero (G : SMem) (eax ecx edx ebx t ebp esi edi f : UInt32)
    (hsz : G.get.size ≤ 4273995776) (hst : t.toNat + 32 ≤ G.get.size) (hap : StackApart t)
    (hn : (rdRaw G.get (t.add 28) 4).toNat = 0)
    (ok0 : StoreOk Image.base Image.size G.mem (t.add 12))
    (okA : StoreOk Image.base Image.size (CodeMem.wr4 G (t.add 12) esi ok0).mem (t.add 8))
    (okB : StoreOk Image.base Image.size
      (CodeMem.wr4 (CodeMem.wr4 G (t.add 12) esi ok0) (t.add 8) (rdRaw G.get (t.add 20) 4) okA).mem (t.add 4))
    (ok3 : StoreOk1 Image.base Image.size
      (Fr G t esi (rdRaw G.get (t.add 20) 4) (rdRaw G.get (t.add 24) 4) ok0 okA okB).mem (t.add 3)) :
    runOkP img 18 (St.m ⟨G.get, eax, ecx, edx, ebx, t.add 16, ebp, esi, edi, 0x100C30, efl f, 0⟩) =
      some (St.m ⟨(CodeMem.wr1 (Fr G t esi (rdRaw G.get (t.add 20) 4) (rdRaw G.get (t.add 24) 4) ok0 okA okB)
          (t.add 3) 0 ok3).get, eaxZ 0, UInt32.add 0 4294967295, rdRaw G.get (t.add 20) 4, ebx, t.add 20, ebp, esi,
          edi, rdRaw G.get (t.add 16) 4, efl (addF 4 t 12 0).2, 18⟩, zeroPath) := by
  have s1 := seg1 (G := G) (eax := eax) (ecx := ecx) (edx := edx) (ebx := ebx) (t := t) (ebp := ebp)
    (esi := esi) (edi := edi) (f := f) (ok0 := ok0) (hsz := hsz) (hst := hst) (hap := hap)
  have s2 := seg2 (G := G) (eax := eax) (ecx := ecx) (edx := edx) (ebx := ebx) (t := t) (ebp := ebp)
    (esi := esi) (edi := edi) (f := (subF 4 (t.add 12) 12 0).2) (ok0 := ok0) (hsz := hsz) (hst := hst)
    (hap := hap)
  have s3 := seg3 (G := G) (eax := rdRaw G.get (t.add 28) 4) (ebx := ebx) (t := t) (ebp := ebp)
    (esi := esi) (edi := edi) (f := (subF 4 (t.add 12) 12 0).2) (ok0 := ok0) (okA := okA) (okB := okB)
    (ok3 := ok3) (hsz := hsz) (hst := hst) (hap := hap)
  have s4 := segz1 (G := G) (ebx := ebx) (t := t) (ebp := ebp) (esi := esi) (edi := edi)
    (f := (subF 4 (t.add 12) 12 0).2) (ok0 := ok0) (okA := okA) (okB := okB) (ok3 := ok3) (hsz := hsz)
    (hst := hst) (hap := hap) hn
  have s5 := segz2 (G := G) (eax := rdRaw G.get (t.add 28) 4) (ecx := rdRaw G.get (t.add 24) 4)
    (edx := rdRaw G.get (t.add 20) 4) (ebx := ebx) (t := t) (ebp := ebp) (esi := esi) (edi := edi)
    (f := (logicF 4 (rdRaw G.get (t.add 28) 4)).2) (ok0 := ok0) (okA := okA) (okB := okB) (ok3 := ok3)
    (hsz := hsz) (hst := hst) (hap := hap)
  have s6 := segz3 (G := G) (edx := rdRaw G.get (t.add 20) 4) (ebx := ebx) (t := t) (ebp := ebp)
    (esi := esi) (edi := edi) (ok0 := ok0) (okA := okA) (okB := okB) (ok3 := ok3)
    (hsz := hsz) (hst := hst) (hap := hap)
  exact runOkP_split (runOkP_split (runOkP_split (runOkP_split (runOkP_split s1 s2) s3) s4) s5) s6

end Sodium.Proofs.Memcmp
