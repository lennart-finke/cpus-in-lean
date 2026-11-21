import Solutions.Logic.Cbx
import Solutions.Exec.Dispatch
import Solutions.Exec.Call
import Solutions.Logic.MemRules
import Solutions.Logic.Path
import Sodium.Proofs.HexEncPre
import Solutions.Logic.Cmp
/-!
# `sodium_bin2hex`: the loop and the epilogue, one instruction each, at any instruction count

```
100030 movzbl (%esi,%edi),%ebx      100058 shr $8,%edx
100034 mov %ebx,%ecx                10005b and $0xd9,%edx
100036 and $0xf,%ecx                100061 add %ebx,%edx
100039 shr $4,%ebx                  100063 addb $0x57,%dl
10003c lea -10(%ecx),%edx           100066 movb %dl,(%eax,%edi,2)
100042 shl $8,%ecx                  100069 movb %ch,1(%eax,%edi,2)
100045 and $0xd900,%edx             10006d inc %edi
10004b lea 0x5700(%ecx,%edx),%ecx   10006e cmp %edi,%ebp
100052 lea -10(%ebx),%edx           100070 jne 100030
100072 mov (%esp),%ecx; jmp 100079; movb $0,(%eax,%ecx); add $4,%esp; pop × 4; ret
```

The memory `M` is any code-keeping memory (the loop invariant says what it holds).
-/
namespace Sodium.Proofs.HexEnc
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Solutions.Logic.Bytes Solutions.Logic.Cmp Sodium.Proofs Sodium.Utils
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr
attribute [-cbv_eval] Solutions.Logic.rdBytes_codeMem

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000


/-- `movzbl (%esi,%edi),%ebx`. -/
theorem l01 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hi : i.toNat < N.toNat) (hBs : B.toNat + N.toNat ≤ M.get.size)
    (hBi : B.toNat + N.toNat ≤ 0x100000 ∨ 0x100000 + 3560 ≤ B.toNat) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100030, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, c, d, rdRaw M.get (B.add i) 1, t, N, B, i, 0x100034, efl F, ic⟩) := by
  cbv

/-- `mov %ebx,%ecx`. -/
theorem l02 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100034, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, b, d, b, t, N, B, i, 0x100036, efl F, ic⟩) := by
  cbv

/-- `and $0xf,%ecx`. -/
theorem l03 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100036, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, c.land 15, d, b, t, N, B, i, 0x100039, efl (logicF 4 (c.land 15)).2, ic⟩) := by
  cbv

/-- `shr $4,%ebx`. -/
theorem l04 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100039, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, c, d, b.shiftRight 4, t, N, B, i, 0x10003C, efl (shFl 5 b 4), ic⟩) := by
  cbv

/-- `lea -10(%ecx),%edx`. -/
theorem l05 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x10003C, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, c, c.add 65526, b, t, N, B, i, 0x100042, efl F, ic⟩) := by
  cbv

/-- `shl $8,%ecx`. -/
theorem l06 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100042, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, c.shiftLeft 8, d, b, t, N, B, i, 0x100045, efl (shFl 4 c 8), ic⟩) := by
  cbv

/-- `and $0xd900,%edx`. -/
theorem l07 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100045, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, c, d.land 55552, b, t, N, B, i, 0x10004B, efl (logicF 4 (d.land 55552)).2, ic⟩) := by
  cbv

/-- `lea 0x5700(%ecx,%edx),%ecx`. -/
theorem l08 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x10004B, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, (c.add d).add 22272, d, b, t, N, B, i, 0x100052, efl F, ic⟩) := by
  cbv

/-- `lea -10(%ebx),%edx`. -/
theorem l09 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100052, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, c, b.add 65526, b, t, N, B, i, 0x100058, efl F, ic⟩) := by
  cbv

/-- `shr $8,%edx`. -/
theorem l10 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100058, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, c, d.shiftRight 8, b, t, N, B, i, 0x10005B, efl (shFl 5 d 8), ic⟩) := by
  cbv

/-- `and $0xd9,%edx`. -/
theorem l11 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x10005B, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, c, d.land 217, b, t, N, B, i, 0x100061, efl (logicF 4 (d.land 217)).2, ic⟩) := by
  cbv

/-- `add %ebx,%edx`. -/
theorem l12 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100061, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, c, d.add b, b, t, N, B, i, 0x100063, efl (addF 4 d b 0).2, ic⟩) := by
  cbv

/-- `addb $0x57,%dl`. -/
theorem l13 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100063, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, c, (d.land 4294967040).lor ((addF 1 (d.land 255) 87 0).1.land 255), b, t, N, B, i, 0x100066, efl (addF 1 (d.land 255) 87 0).2, ic⟩) := by
  cbv

/-- `movb %dl,(%eax,%edi,2)`. -/
theorem l14 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hi : i.toNat < N.toNat) (hN : N.toNat < 1073741824) (hPs : P.toNat + 2 * N.toNat < M.get.size)
    (hPi : P.toNat + 2 * N.toNat < 0x100000 ∨ 0x100000 + 3560 ≤ P.toNat)
    (ok : StoreOk1 Image.base Image.size M.mem (P.add (i.add i))) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100066, efl F, ic⟩)) =
      some (St.m ⟨(CodeMem.wr1 M (P.add (i.add i)) (d.land 255) ok).get, P, c, d, b, t, N, B, i, 0x100069, efl F, ic⟩) := by
  cbv

/-- `movb %ch,1(%eax,%edi,2)`. -/
theorem l15 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hi : i.toNat < N.toNat) (hN : N.toNat < 1073741824) (hPs : P.toNat + 2 * N.toNat < M.get.size)
    (hPi : P.toNat + 2 * N.toNat < 0x100000 ∨ 0x100000 + 3560 ≤ P.toNat)
    (ok : StoreOk1 Image.base Image.size M.mem ((P.add (i.add i)).add 1)) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100069, efl F, ic⟩)) =
      some (St.m ⟨(CodeMem.wr1 M ((P.add (i.add i)).add 1) ((c.shiftRight 8).land 255) ok).get, P, c, d, b, t, N, B, i, 0x10006D, efl F, ic⟩) := by
  cbv

/-- `inc %edi`. -/
theorem l16 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x10006D, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, c, d, b, t, N, B, i.add 1, 0x10006E, efl (mixF F (addF 4 i 1 0).2 2260), ic⟩) := by
  cbv

/-- `cmp %edi,%ebp`. -/
theorem l17 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x10006E, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100070, efl (subF 4 N i 0).2, ic⟩) := by
  cbv

/-- `jne`, taken. -/
theorem l18b (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hne : N.toNat ≠ i.toNat) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100070, efl (subF 4 N i 0).2, ic⟩)) =
      some (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100030, efl (subF 4 N i 0).2, ic⟩) := by
  cbv

/-- `jne`, not taken. -/
theorem l18o (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (heq : N.toNat = i.toNat) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100070, efl (subF 4 N i 0).2, ic⟩)) =
      some (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100072, efl (subF 4 N i 0).2, ic⟩) := by
  cbv

/-- `mov (%esp),%ecx`. -/
theorem e1 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 40 ≤ M.get.size) (hap : StackApart t) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100072, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, rdRaw M.get t 4, d, b, t, N, B, i, 0x100075, efl F, ic⟩) := by
  unfold StackApart at hap; cbv

/-- `jmp`. -/
theorem e2 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 40 ≤ M.get.size) (hap : StackApart t) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100075, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100079, efl F, ic⟩) := by
  unfold StackApart at hap; cbv

/-- `movb $0,(%eax,%ecx)`. -/
theorem e3 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 40 ≤ M.get.size) (hap : StackApart t)
    (hPs : P.toNat + c.toNat < M.get.size) (hPi : P.toNat + c.toNat < 0x100000 ∨ 0x100000 + 3560 ≤ P.toNat)
    (ok : StoreOk1 Image.base Image.size M.mem (P.add c)) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x100079, efl F, ic⟩)) =
      some (St.m ⟨(CodeMem.wr1 M (P.add c) 0 ok).get, P, c, d, b, t, N, B, i, 0x10007D, efl F, ic⟩) := by
  unfold StackApart at hap; cbv

/-- `add $4,%esp`. -/
theorem e4 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 40 ≤ M.get.size) (hap : StackApart t) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t, N, B, i, 0x10007D, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, c, d, b, t.add 4, N, B, i, 0x100080, efl (addF 4 t 4 0).2, ic⟩) := by
  unfold StackApart at hap; cbv

/-- `pop %esi`. -/
theorem e5 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 40 ≤ M.get.size) (hap : StackApart t) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t.add 4, N, B, i, 0x100080, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, c, d, b, t.add 8, N, rdRaw M.get (t.add 4) 4, i, 0x100081, efl F, ic⟩) := by
  unfold StackApart at hap; cbv

/-- `pop %edi`. -/
theorem e6 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 40 ≤ M.get.size) (hap : StackApart t) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t.add 8, N, B, i, 0x100081, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, c, d, b, t.add 12, N, B, rdRaw M.get (t.add 8) 4, 0x100082, efl F, ic⟩) := by
  unfold StackApart at hap; cbv

/-- `pop %ebx`. -/
theorem e7 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 40 ≤ M.get.size) (hap : StackApart t) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t.add 12, N, B, i, 0x100082, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, c, d, rdRaw M.get (t.add 12) 4, t.add 16, N, B, i, 0x100083, efl F, ic⟩) := by
  unfold StackApart at hap; cbv

/-- `pop %ebp`. -/
theorem e8 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 40 ≤ M.get.size) (hap : StackApart t) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t.add 16, N, B, i, 0x100083, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, c, d, b, t.add 20, rdRaw M.get (t.add 16) 4, B, i, 0x100084, efl F, ic⟩) := by
  unfold StackApart at hap; cbv

/-- `ret`. -/
theorem e9 (M : SMem) (P c d b t N B i F : UInt32) (ic : UInt64) (hsz : M.get.size ≤ 4273995776)
    (hst : t.toNat + 40 ≤ M.get.size) (hap : StackApart t) :
    okState (execInstr (St.m ⟨M.get, P, c, d, b, t.add 20, N, B, i, 0x100084, efl F, ic⟩)) =
      some (St.m ⟨M.get, P, c, d, b, t.add 24, N, B, i, rdRaw M.get (t.add 20) 4, efl F, ic⟩) := by
  unfold StackApart at hap; cbv

end Sodium.Proofs.HexEnc
