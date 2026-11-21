import Solutions.Logic.Cbx
import Solutions.Exec.Dispatch
import Solutions.Exec.Call
import Solutions.Logic.MemRules
import Solutions.Logic.Path
import Sodium.Proofs.Code
import Sodium.Proofs.MemcmpPre
/-!
# `sodium_memcmp`, instruction by instruction

```
100c30 push %esi                   100c60 mov 0x8(%esp),%edx
100c31 sub $0xc,%esp               100c64 movzbl (%edx,%ecx),%edx
100c34 mov 0x1c(%esp),%eax         100c68 mov 0x4(%esp),%esi
100c38 mov 0x18(%esp),%ecx         100c6c xor (%esi,%ecx),%dl
100c3c mov 0x14(%esp),%edx         100c6f or %dl,0x3(%esp)
100c40 mov %edx,0x8(%esp)          100c73 inc %ecx
100c44 mov %ecx,0x4(%esp)          100c74 cmp %ecx,%eax
100c48 movb $0x0,0x3(%esp)         100c76 jne 100c60
100c4d test %eax,%eax              100c78 movzbl 0x3(%esp),%ecx
100c4f je 100c78                   100c7d dec %ecx
100c51 xor %ecx,%ecx               100c7e xor %eax,%eax
100c53 … 100c5f nop × 13           100c80 bt $0x8,%ecx
                                   100c84 adc $-1,%eax
                                   100c87 add $0xc,%esp; 100c8a pop %esi; 100c8b ret
```

The loop and the epilogue, one instruction each, at any instruction count (the prologue is in
`Sodium.Proofs.MemcmpPre`).
-/
namespace Sodium.Proofs.Memcmp
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Solutions.Logic.Bytes Sodium.Proofs Sodium.Utils
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr
attribute [-cbv_eval] Solutions.Logic.rdBytes_codeMem

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000

section loop
variable (G : SMem) (e A B w N i a d ebx edx esi ebp edi F t : UInt32) (ic : UInt64)
  (ok0 : StoreOk Image.base Image.size G.mem (t.add 12))
  (okA : StoreOk Image.base Image.size (CodeMem.wr4 G (t.add 12) e ok0).mem (t.add 8))
  (okB : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 G (t.add 12) e ok0) (t.add 8) A okA).mem (t.add 4))
  (ok : StoreOk1 Image.base Image.size (Fr G t e A B ok0 okA okB).mem (t.add 3))
  (hsz : G.get.size ≤ 4273995776) (hst : t.toNat + 32 ≤ G.get.size) (hap : StackApart t)

include hsz hst hap in
/-- `mov 0x8(%esp),%edx`. -/
theorem ex_ldA :
    okState (execInstr (St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).get, N, i, edx, ebx, t, ebp,
      esi, edi, 0x100C60, efl F, ic⟩)) =
    some (St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).get, N, i, A, ebx, t, ebp,
      esi, edi, 0x100C64, efl F, ic⟩) := by
  unfold Fr StackApart at *; cbv

include hsz hst hap in
/-- `movzbl (%edx,%ecx),%edx`. -/
theorem ex_ldbyteA (hi : i.toNat < N.toNat) (hAs : A.toNat + N.toNat ≤ G.get.size)
    (hAa : A.toNat + N.toNat ≤ t.toNat ∨ t.toNat + 32 ≤ A.toNat)
    (hAi : A.toNat + N.toNat ≤ 0x100000 ∨ 0x100000 + 3560 ≤ A.toNat) :
    okState (execInstr (St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).get, N, i, A, ebx, t, ebp,
      esi, edi, 0x100C64, efl F, ic⟩)) =
    some (St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).get, N, i, rdRaw G.get (A.add i) 1, ebx, t,
      ebp, esi, edi, 0x100C68, efl F, ic⟩) := by
  unfold Fr StackApart at *; cbv

include hsz hst hap in
/-- `mov 0x4(%esp),%esi`. -/
theorem ex_ldB :
    okState (execInstr (St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).get, N, i, a, ebx, t, ebp,
      esi, edi, 0x100C68, efl F, ic⟩)) =
    some (St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).get, N, i, a, ebx, t, ebp,
      B, edi, 0x100C6C, efl F, ic⟩) := by
  unfold Fr StackApart at *; cbv

include hsz hst hap in
/-- `xor (%esi,%ecx),%dl`. -/
theorem ex_xorB (hi : i.toNat < N.toNat) (hBs : B.toNat + N.toNat ≤ G.get.size)
    (hBa : B.toNat + N.toNat ≤ t.toNat ∨ t.toNat + 32 ≤ B.toNat)
    (hBi : B.toNat + N.toNat ≤ 0x100000 ∨ 0x100000 + 3560 ≤ B.toNat) :
    okState (execInstr (St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).get, N, i, a, ebx, t, ebp,
      B, edi, 0x100C6C, efl F, ic⟩)) =
    some (St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).get, N, i,
      (a.land 4294967040).lor (((a.land 255).xor (rdRaw G.get (B.add i) 1)).land 255), ebx, t, ebp,
      B, edi, 0x100C6F, efl (logicF 1 ((a.land 255).xor (rdRaw G.get (B.add i) 1))).2, ic⟩) := by
  unfold Fr StackApart at *; cbv

include hsz hst hap in
/-- `or %dl,0x3(%esp)`: the accumulator byte, stored again. -/
theorem ex_or (ok' : StoreOk1 Image.base Image.size (CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).mem
      (t.add 3)) :
    okState (execInstr (St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).get, N, i, d, ebx, t, ebp,
      B, edi, 0x100C6F, efl F, ic⟩)) =
    some (St.m ⟨(CodeMem.wr1 (CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok) (t.add 3)
      (w.toUInt8.toUInt32.lor (d.land 255)) ok').get, N, i, d, ebx, t, ebp,
      B, edi, 0x100C73, efl (logicF 1 (w.toUInt8.toUInt32.lor (d.land 255))).2, ic⟩) := by
  unfold Fr StackApart at *; cbv

end loop

section plain
variable (M : SMem) (N i d ebx t ebp esi edi F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)

include hsz in
/-- `inc %ecx`. -/
theorem ex_inc :
    okState (execInstr (St.m ⟨M.get, N, i, d, ebx, t, ebp, esi, edi, 0x100C73, efl F, ic⟩)) =
      some (St.m ⟨M.get, N, i.add 1, d, ebx, t, ebp, esi, edi, 0x100C74, efl (mixF F (addF 4 i 1 0).2 2260), ic⟩) := by
  cbv

include hsz in
/-- `cmp %ecx,%eax`. -/
theorem ex_cmp :
    okState (execInstr (St.m ⟨M.get, N, i, d, ebx, t, ebp, esi, edi, 0x100C74, efl F, ic⟩)) =
      some (St.m ⟨M.get, N, i, d, ebx, t, ebp, esi, edi, 0x100C76, efl (subF 4 N i 0).2, ic⟩) := by
  cbv

include hsz in
/-- `jne`, taken. -/
theorem ex_jne_back (hne : N.toNat ≠ i.toNat) :
    okState (execInstr (St.m ⟨M.get, N, i, d, ebx, t, ebp, esi, edi, 0x100C76, efl (subF 4 N i 0).2, ic⟩)) =
      some (St.m ⟨M.get, N, i, d, ebx, t, ebp, esi, edi, 0x100C60, efl (subF 4 N i 0).2, ic⟩) := by
  cbv

include hsz in
/-- `jne`, not taken. -/
theorem ex_jne_out (heq : N.toNat = i.toNat) :
    okState (execInstr (St.m ⟨M.get, N, i, d, ebx, t, ebp, esi, edi, 0x100C76, efl (subF 4 N i 0).2, ic⟩)) =
      some (St.m ⟨M.get, N, i, d, ebx, t, ebp, esi, edi, 0x100C78, efl (subF 4 N i 0).2, ic⟩) := by
  cbv

include hsz in
/-- `dec %ecx`. -/
theorem ex_dec :
    okState (execInstr (St.m ⟨M.get, N, i, d, ebx, t, ebp, esi, edi, 0x100C7D, efl F, ic⟩)) =
      some (St.m ⟨M.get, N, i.add 4294967295, d, ebx, t, ebp, esi, edi, 0x100C7E,
        efl (mixF F (subF 4 i 1 0).2 2260), ic⟩) := by
  cbv

include hsz in
/-- `xor %eax,%eax`. -/
theorem ex_xor :
    okState (execInstr (St.m ⟨M.get, N, i, d, ebx, t, ebp, esi, edi, 0x100C7E, efl F, ic⟩)) =
      some (St.m ⟨M.get, 0, i, d, ebx, t, ebp, esi, edi, 0x100C80, efl (logicF 4 0).2, ic⟩) := by
  cbv

include hsz in
/-- `bt $0x8,%ecx`. -/
theorem ex_bt :
    okState (execInstr (St.m ⟨M.get, N, i, d, ebx, t, ebp, esi, edi, 0x100C80, efl F, ic⟩)) =
      some (St.m ⟨M.get, N, i, d, ebx, t, ebp, esi, edi, 0x100C84,
        efl (mixF F (if Bool.rec true false (decide ((i.shiftRight 8).land 1 = 0)) = true then Flag.CF else 0) 1),
        ic⟩) := by
  cbv
  -- the two sides differ only in the `Decidable` instance of the condition
  split <;> rfl

include hsz in
/-- `adc $-1,%eax`. -/
theorem ex_adc :
    okState (execInstr (St.m ⟨M.get, N, i, d, ebx, t, ebp, esi, edi, 0x100C84, efl F, ic⟩)) =
      some (St.m ⟨M.get, (addF 4 N 4294967295 (if Bool.rec true false (decide (F.land 1 = 0)) = true then 1 else 0)).1,
        i, d, ebx, t, ebp, esi, edi, 0x100C87,
        efl (addF 4 N 4294967295 (if Bool.rec true false (decide (F.land 1 = 0)) = true then 1 else 0)).2, ic⟩) := by
  cbv

end plain

section exit
variable (G : SMem) (e A B w N i a d ebx edx esi ebp edi F t : UInt32) (ic : UInt64)
  (ok0 : StoreOk Image.base Image.size G.mem (t.add 12))
  (okA : StoreOk Image.base Image.size (CodeMem.wr4 G (t.add 12) e ok0).mem (t.add 8))
  (okB : StoreOk Image.base Image.size (CodeMem.wr4 (CodeMem.wr4 G (t.add 12) e ok0) (t.add 8) A okA).mem (t.add 4))
  (ok : StoreOk1 Image.base Image.size (Fr G t e A B ok0 okA okB).mem (t.add 3))
  (hsz : G.get.size ≤ 4273995776) (hst : t.toNat + 32 ≤ G.get.size) (hap : StackApart t)

include hsz hst hap in
/-- `movzbl 0x3(%esp),%ecx`: the accumulator. -/
theorem ex_ldacc :
    okState (execInstr (St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).get, N, i, d, ebx, t, ebp,
      esi, edi, 0x100C78, efl F, ic⟩)) =
    some (St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).get, N, w.toUInt8.toUInt32, d, ebx, t, ebp,
      esi, edi, 0x100C7D, efl F, ic⟩) := by
  unfold Fr StackApart at *; cbv

include hsz hst hap in
/-- `add $0xc,%esp`. -/
theorem ex_add :
    okState (execInstr (St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).get, N, i, d, ebx, t, ebp,
      esi, edi, 0x100C87, efl F, ic⟩)) =
    some (St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).get, N, i, d, ebx, t.add 12, ebp,
      esi, edi, 0x100C8A, efl (addF 4 t 12 0).2, ic⟩) := by
  unfold Fr StackApart at *; cbv

include hsz hst hap in
/-- `pop %esi`. -/
theorem ex_pop :
    okState (execInstr (St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).get, N, i, d, ebx, t.add 12,
      ebp, esi, edi, 0x100C8A, efl F, ic⟩)) =
    some (St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).get, N, i, d, ebx, t.add 16, ebp,
      e, edi, 0x100C8B, efl F, ic⟩) := by
  unfold Fr StackApart at *; cbv

include hsz hst hap in
/-- `ret`. -/
theorem ex_ret :
    okState (execInstr (St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).get, N, i, d, ebx, t.add 16,
      ebp, esi, edi, 0x100C8B, efl F, ic⟩)) =
    some (St.m ⟨(CodeMem.wr1 (Fr G t e A B ok0 okA okB) (t.add 3) w ok).get, N, i, d, ebx, t.add 20, ebp,
      esi, edi, rdRaw G.get (t.add 16) 4, efl F, ic⟩) := by
  unfold Fr StackApart at *; cbv

end exit

end Sodium.Proofs.Memcmp
