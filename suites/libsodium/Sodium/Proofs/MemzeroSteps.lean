import Solutions.Logic.Cbx
import Solutions.Exec.Dispatch
import Solutions.Exec.Call
import Solutions.Logic.MemRules
import Solutions.Logic.Step
import Solutions.Logic.Path
import Sodium.Proofs.Code
/-!
# `sodium_memzero`, instruction by instruction

```
100c00 push %eax                   100c20 mov (%esp),%edx
100c01 mov 0xc(%esp),%eax          100c23 movb $0x0,(%edx,%ecx)
100c05 mov 0x8(%esp),%ecx          100c27 inc %ecx
100c09 mov %ecx,(%esp)             100c28 cmp %ecx,%eax
100c0c test %eax,%eax              100c2a jne 100c20
100c0e je 100c2c                   100c2c pop %eax
100c10 xor %ecx,%ecx               100c2d ret
100c12 … 100c1f nop × 14
```

The stack pointer at entry is `t + 4`: `t` is the slot of the pushed `eax`, which the function
overwrites with the buffer pointer and reloads in every iteration. The facts about addresses are
hypotheses in `toNat` form; `cbv` discharges the side conditions of the memory accesses from them by
`omega`.
-/
namespace Sodium.Proofs.Memzero
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Sodium.Proofs Sodium.Utils
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000

/-- The image lies apart from the stack words `[t - 124, t + 16)`. -/
def StackApart (t : UInt32) : Prop := t.toNat + 16 ≤ 0x100000 ∨ 0x100000 + 3560 + 124 ≤ t.toNat

/-! The prefix in short segments (each a small `cbv` proof). -/

theorem pre_a (G : SMem) (eax ecx edx ebx t ebp esi edi f : UInt32)
    (hsz : G.get.size ≤ ramTop) (hst : t.toNat + 16 ≤ G.get.size) (hap : StackApart t)
    (ok0 : StoreOk Image.base Image.size G.mem t)
    (ok1 : StoreOk Image.base Image.size (CodeMem.wr4 G t eax ok0).mem t) :
    runOk img 4 (St.m ⟨G.get, eax, ecx, edx, ebx, t.add 4, ebp, esi, edi, 0x100C00, efl f, 0⟩) =
      some (St.m ⟨(CodeMem.wr4 (CodeMem.wr4 G t eax ok0) t (rdRaw G.get (t.add 8) 4) ok1).get,
        rdRaw G.get (t.add 12) 4, rdRaw G.get (t.add 8) 4, edx, ebx, t, ebp, esi, edi, 0x100C0C, efl f, 4⟩) := by
  unfold StackApart at hap
  cbv
theorem pre_b (G : SMem) (eax ecx edx ebx t ebp esi edi f : UInt32)
    (hsz : G.get.size ≤ ramTop) (hst : t.toNat + 16 ≤ G.get.size) (hap : StackApart t)
    (hn : 0 < (rdRaw G.get (t.add 12) 4).toNat)
    (ok0 : StoreOk Image.base Image.size G.mem t)
    (ok1 : StoreOk Image.base Image.size (CodeMem.wr4 G t eax ok0).mem t) :
    runOk img 3 (St.m ⟨(CodeMem.wr4 (CodeMem.wr4 G t eax ok0) t (rdRaw G.get (t.add 8) 4) ok1).get,
        rdRaw G.get (t.add 12) 4, rdRaw G.get (t.add 8) 4, edx, ebx, t, ebp, esi, edi, 0x100C0C, efl f, 4⟩) =
      some (St.m ⟨(CodeMem.wr4 (CodeMem.wr4 G t eax ok0) t (rdRaw G.get (t.add 8) 4) ok1).get,
        rdRaw G.get (t.add 12) 4, 0, edx, ebx, t, ebp, esi, edi, 0x100C12, efl (logicF 4 0).2, 7⟩) := by
  unfold StackApart at hap
  cbv

theorem pre_c (M : SMem) (eax ecx edx ebx t ebp esi edi f : UInt32)
    (hsz : M.get.size ≤ ramTop) :
    runOk img 7 (St.m ⟨M.get, eax, ecx, edx, ebx, t, ebp, esi, edi, 0x100C12, efl f, 7⟩) =
      some (St.m ⟨M.get, eax, ecx, edx, ebx, t, ebp, esi, edi, 0x100C19, efl f, 14⟩) := by
  cbv

theorem pre_d (M : SMem) (eax ecx edx ebx t ebp esi edi f : UInt32)
    (hsz : M.get.size ≤ ramTop) :
    runOk img 7 (St.m ⟨M.get, eax, ecx, edx, ebx, t, ebp, esi, edi, 0x100C19, efl f, 14⟩) =
      some (St.m ⟨M.get, eax, ecx, edx, ebx, t, ebp, esi, edi, 0x100C20, efl f, 21⟩) := by
  cbv

theorem zero_b (G : SMem) (eax ecx edx ebx t ebp esi edi f : UInt32)
    (hsz : G.get.size ≤ ramTop) (hst : t.toNat + 16 ≤ G.get.size) (hap : StackApart t)
    (hn : (rdRaw G.get (t.add 12) 4).toNat = 0)
    (ok0 : StoreOk Image.base Image.size G.mem t)
    (ok1 : StoreOk Image.base Image.size (CodeMem.wr4 G t eax ok0).mem t) :
    runOk img 4 (St.m ⟨(CodeMem.wr4 (CodeMem.wr4 G t eax ok0) t (rdRaw G.get (t.add 8) 4) ok1).get,
        rdRaw G.get (t.add 12) 4, rdRaw G.get (t.add 8) 4, edx, ebx, t, ebp, esi, edi, 0x100C0C, efl f, 4⟩) =
      some (St.m ⟨(CodeMem.wr4 (CodeMem.wr4 G t eax ok0) t (rdRaw G.get (t.add 8) 4) ok1).get,
        rdRaw G.get (t.add 8) 4, rdRaw G.get (t.add 8) 4, edx, ebx, t.add 8, ebp, esi, edi,
        rdRaw G.get (t.add 4) 4, efl (logicF 4 (rdRaw G.get (t.add 12) 4)).2, 8⟩) := by
  unfold StackApart at hap
  cbv

/-- From the entry to the loop, for a non-empty buffer. -/
theorem run_pre (G : SMem) (eax ecx edx ebx t ebp esi edi f : UInt32)
    (hsz : G.get.size ≤ ramTop) (hst : t.toNat + 16 ≤ G.get.size) (hap : StackApart t)
    (hn : 0 < (rdRaw G.get (t.add 12) 4).toNat)
    (ok0 : StoreOk Image.base Image.size G.mem t)
    (ok1 : StoreOk Image.base Image.size (CodeMem.wr4 G t eax ok0).mem t) :
    runOk img 21 (St.m ⟨G.get, eax, ecx, edx, ebx, t.add 4, ebp, esi, edi, 0x100C00, efl f, 0⟩) =
      some (St.m ⟨(CodeMem.wr4 (CodeMem.wr4 G t eax ok0) t (rdRaw G.get (t.add 8) 4) ok1).get,
        rdRaw G.get (t.add 12) 4, 0, edx, ebx, t, ebp, esi, edi, 0x100C20, efl (logicF 4 0).2, 21⟩) :=
  runOk_split (runOk_split (runOk_split (pre_a G eax ecx edx ebx t ebp esi edi f hsz hst hap ok0 ok1)
    (pre_b G eax ecx edx ebx t ebp esi edi f hsz hst hap hn ok0 ok1)) (pre_c _ _ _ _ _ _ _ _ _ _ (by
      rw [wr4_get_size, wr4_get_size]; exact hsz))) (pre_d _ _ _ _ _ _ _ _ _ _ (by
      rw [wr4_get_size, wr4_get_size]; exact hsz))

/-- From the entry to the return, for an empty buffer. -/
theorem run_zero (G : SMem) (eax ecx edx ebx t ebp esi edi f : UInt32)
    (hsz : G.get.size ≤ ramTop) (hst : t.toNat + 16 ≤ G.get.size) (hap : StackApart t)
    (hn : (rdRaw G.get (t.add 12) 4).toNat = 0)
    (ok0 : StoreOk Image.base Image.size G.mem t)
    (ok1 : StoreOk Image.base Image.size (CodeMem.wr4 G t eax ok0).mem t) :
    runOk img 8 (St.m ⟨G.get, eax, ecx, edx, ebx, t.add 4, ebp, esi, edi, 0x100C00, efl f, 0⟩) =
      some (St.m ⟨(CodeMem.wr4 (CodeMem.wr4 G t eax ok0) t (rdRaw G.get (t.add 8) 4) ok1).get,
        rdRaw G.get (t.add 8) 4, rdRaw G.get (t.add 8) 4, edx, ebx, t.add 8, ebp, esi, edi,
        rdRaw G.get (t.add 4) 4, efl (logicF 4 (rdRaw G.get (t.add 12) 4)).2, 8⟩) :=
  runOk_split (pre_a G eax ecx edx ebx t ebp esi edi f hsz hst hap ok0 ok1)
    (zero_b G eax ecx edx ebx t ebp esi edi f hsz hst hap hn ok0 ok1)

/-- `mov (%esp),%edx`: the buffer pointer from the stack slot. -/
theorem ex_load (H : SMem) (P N i edx ebx t ebp esi edi f : UInt32) (ic : UInt64)
    (okH : StoreOk Image.base Image.size H.mem t)
    (hsz : H.get.size ≤ ramTop) (hst : t.toNat + 16 ≤ H.get.size) :
    okState (execInstr (St.m ⟨(CodeMem.wr4 H t P okH).get, N, i, edx, ebx, t, ebp, esi, edi, 0x100C20, efl f, ic⟩)) =
      some (St.m ⟨(CodeMem.wr4 H t P okH).get, N, i, P, ebx, t, ebp, esi, edi, 0x100C23, efl f, ic⟩) := by
  cbv

/-- `movb $0,(%edx,%ecx)`: the byte store. -/
theorem ex_store (H : SMem) (P N i ebx t ebp esi edi f : UInt32) (ic : UInt64) (n : Nat)
    (okH : StoreOk Image.base Image.size H.mem t)
    (hsz : H.get.size ≤ ramTop) (hst : t.toNat + 16 ≤ H.get.size) (hap : StackApart t)
    (hi : i.toNat < n) (hP : P.toNat + n ≤ H.get.size)
    (hPi : P.toNat + n ≤ 0x100000 ∨ 0x100000 + 3560 ≤ P.toNat)
    (hPs : P.toNat + n ≤ t.toNat - 124 ∨ t.toNat + 16 ≤ P.toNat)
    (ok1 : StoreOk1 Image.base Image.size (CodeMem.wr4 H t P okH).mem (P.add i)) :
    okState (execInstr (St.m ⟨(CodeMem.wr4 H t P okH).get, N, i, P, ebx, t, ebp, esi, edi, 0x100C23, efl f, ic⟩)) =
      some (St.m ⟨(CodeMem.wr1 (CodeMem.wr4 H t P okH) (P.add i) 0 ok1).get, N, i, P, ebx, t, ebp, esi, edi,
        0x100C27, efl f, ic⟩) := by
  unfold StackApart at hap
  cbv

/-- `inc %ecx`. -/
theorem ex_inc (M : SMem) (P N i ebx t ebp esi edi f : UInt32) (ic : UInt64) (hsz : M.get.size ≤ ramTop) :
    okState (execInstr (St.m ⟨M.get, N, i, P, ebx, t, ebp, esi, edi, 0x100C27, efl f, ic⟩)) =
      some (St.m ⟨M.get, N, i.add 1, P, ebx, t, ebp, esi, edi, 0x100C28, efl (mixF f (addF 4 i 1 0).2 2260), ic⟩) := by
  cbv

/-- `cmp %ecx,%eax`. -/
theorem ex_cmp (M : SMem) (P N j ebx t ebp esi edi f : UInt32) (ic : UInt64) (hsz : M.get.size ≤ ramTop) :
    okState (execInstr (St.m ⟨M.get, N, j, P, ebx, t, ebp, esi, edi, 0x100C28, efl f, ic⟩)) =
      some (St.m ⟨M.get, N, j, P, ebx, t, ebp, esi, edi, 0x100C2A, efl (subF 4 N j 0).2, ic⟩) := by
  cbv

/-- `jne`, taken. -/
theorem ex_jne_back (M : SMem) (P N j ebx t ebp esi edi : UInt32) (ic : UInt64) (hsz : M.get.size ≤ ramTop)
    (hne : N.toNat ≠ j.toNat) :
    okState (execInstr (St.m ⟨M.get, N, j, P, ebx, t, ebp, esi, edi, 0x100C2A, efl (subF 4 N j 0).2, ic⟩)) =
      some (St.m ⟨M.get, N, j, P, ebx, t, ebp, esi, edi, 0x100C20, efl (subF 4 N j 0).2, ic⟩) := by
  cbv

/-- `jne`, not taken. -/
theorem ex_jne_out (M : SMem) (P N j ebx t ebp esi edi : UInt32) (ic : UInt64) (hsz : M.get.size ≤ ramTop)
    (heq : N.toNat = j.toNat) :
    okState (execInstr (St.m ⟨M.get, N, j, P, ebx, t, ebp, esi, edi, 0x100C2A, efl (subF 4 N j 0).2, ic⟩)) =
      some (St.m ⟨M.get, N, j, P, ebx, t, ebp, esi, edi, 0x100C2C, efl (subF 4 N j 0).2, ic⟩) := by
  cbv

/-- `pop %eax`. -/
theorem ex_pop (H : SMem) (P N j edx ebx t ebp esi edi f : UInt32) (ic : UInt64)
    (okH : StoreOk Image.base Image.size H.mem t)
    (hsz : H.get.size ≤ ramTop) (hst : t.toNat + 16 ≤ H.get.size) :
    okState (execInstr (St.m ⟨(CodeMem.wr4 H t P okH).get, N, j, edx, ebx, t, ebp, esi, edi, 0x100C2C, efl f, ic⟩)) =
      some (St.m ⟨(CodeMem.wr4 H t P okH).get, P, j, edx, ebx, t.add 4, ebp, esi, edi, 0x100C2D, efl f, ic⟩) := by
  cbv

/-- `ret`. -/
theorem ex_ret (H : SMem) (P N j edx ebx t ebp esi edi f : UInt32) (ic : UInt64)
    (okH : StoreOk Image.base Image.size H.mem t)
    (hsz : H.get.size ≤ ramTop) (hst : t.toNat + 16 ≤ H.get.size) :
    okState (execInstr (St.m ⟨(CodeMem.wr4 H t P okH).get, N, j, edx, ebx, t.add 4, ebp, esi, edi, 0x100C2D, efl f, ic⟩)) =
      some (St.m ⟨(CodeMem.wr4 H t P okH).get, N, j, edx, ebx, t.add 8, ebp, esi, edi, rdRaw H.get (t.add 4) 4,
        efl f, ic⟩) := by
  cbv

end Sodium.Proofs.Memzero
