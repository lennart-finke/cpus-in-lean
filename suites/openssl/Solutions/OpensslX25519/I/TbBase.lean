import Solutions.OpensslX25519.Frame
import Solutions.OpensslX25519.I.Base
import Solutions.OpensslX25519.I.MemCall
import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.ShapesMul1
import Solutions.OpensslX25519.ShapesMul2
import Solutions.OpensslX25519.I.ShapesM121
import Solutions.OpensslX25519.I.ShapesX1
import Solutions.OpensslX25519.I.ShapesX2
import Solutions.OpensslX25519.I.ShapesX3
import Solutions.OpensslX25519.I.ShapesX4
import Solutions.Exec.Mul
import Solutions.Exec.Alu
import Solutions.Exec.Branch
import Solutions.Exec.Byte
import Solutions.Exec.Shift
/-!
# `fe_tobytes` (`0x101c30`): the ends of its run

The frame is `L = sp - 40` (`FB L 44`): the four pushes put `ebp`, `ebx`, `edi`, `esi` at `L + 36 … L + 24`,
`subl $0x18` sets `esp = L`; at the end `addl $0x18`, the pops and `retl` (return address at `L + 40`).
A 2-byte store (`movw`) into the output is two `CodeMem.wr1` (`wr1_wr1_eq`). Prover Q.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

/-- A 2-byte store as two byte stores. -/
theorem wr1_wr1_eq (N : XMem) (a a1 v : UInt32) (ok : StoreOk1 Image.base Image.size N.mem a)
    (ok' : StoreOk1 Image.base Image.size (CodeMem.wr1 N a v ok).mem a1) (h1 : a1.toNat = a.toNat + 1)
    (hs : N.get.size ≤ ramTop) :
    (CodeMem.wr1 (CodeMem.wr1 N a v ok) a1 (UInt32.shiftRight v 8) ok').get = wrBytes N.get a 2 v := by
  rw [wr1_get, wr1_get]
  have hsz : a.toNat + 2 ≤ N.get.size := by
    have := ok'.1
    have e : (CodeMem.wr1 N a v ok).mem.size = N.get.size := wr1_get_size N a v ok
    omega
  have e1 : a1 = a + (1 : Nat).toUInt32 := UInt32.toNat_inj.1 (by
    rw [h1, UInt32.toNat_add]; unfold ramTop at hs; simp only [Nat.toUInt32, UInt32.toNat_ofNat']; omega)
  have e0 : a + (0 : Nat).toUInt32 = a := by simp
  rw [← wr2_join hsz hs v, e0, shr0, e1]
  rfl

set_option exec.addrSub true in
/-- `pushl %ebp ; pushl %ebx ; pushl %edi ; pushl %esi` -/
theorem tb_pro (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (G : XMem) (L : UInt32) (hS : FB G.get.size L 44)
    (l : List (Nat × UInt32)) (hF : Frame G L 44 l) (eax ecx edx ebx ebp esi edi f : UInt32) :
    ∃ N' : XMem, Run img (St.m ⟨G.get, eax, ecx, edx, ebx, UInt32.add L 40, ebp, esi, edi, 0x101c30, efl f, icAdd ic0 0⟩)
      (St.m ⟨N'.get, eax, ecx, edx, ebx, UInt32.add L 24, ebp, esi, edi, 0x101c34, efl f, icAdd ic0 4⟩) ∧
      Frame N' L 44 ((24, esi) :: (28, edi) :: (32, ebx) :: (36, ebp) :: l) ∧
      Pres G N' (OutF L 40) := by
  refine ⟨stF (stF (stF (stF G L 44 36 ebp hS (by decide)) L 44 32 ebx stF_FB (by decide))
    L 44 28 edi stF_FB (by decide)) L 44 24 esi stF_FB (by decide), run_of_runI (k := 4) ?_ (icB hic (by decide)),
    (((hF.wrF 36 rfl rfl).wrF 32 rfl rfl).wrF 28 rfl rfl).wrF 24 rfl rfl,
    ((((Pres.refl G _).wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide)⟩
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF
  cbv

theorem tb_esp_sub (L : UInt32) : (subF 4 (UInt32.add L 24) 24 0).1 = L := by
  rw [subF_fst]; show L + 24 - 24 = L; exact UInt32.add_sub_cancel _ _

/-- `subl $0x18, %esp` -/
theorem tb_sub (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 44)
    (eax ecx edx ebx ebp esi edi f : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 24, ebp, esi, edi, 0x101c34, efl f, icAdd ic0 4⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, L, ebp, esi, edi, 0x101c37, efl (subF 4 (UInt32.add L 24) 24 0).2,
        icAdd ic0 5⟩) := by
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  have h : runI img 1 (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 24, ebp, esi, edi, 0x101c34, efl f, icAdd ic0 4⟩) =
      some (St.m ⟨N.get, eax, ecx, edx, ebx, (subF 4 (UInt32.add L 24) 24 0).1, ebp, esi, edi, 0x101c37,
        efl (subF 4 (UInt32.add L 24) 24 0).2, icAdd ic0 5⟩) := by
    cbv
  rw [tb_esp_sub] at h
  exact run_of_runI h (icB hic (by decide))

theorem tb_esp_add (L : UInt32) : (addF 4 L 24 0).1 = UInt32.add L 24 := addF_fst _ _

/-- `addl $0x18, %esp` -/
theorem tb_add (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 44)
    (eax ecx edx ebx ebp esi edi f : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, L, ebp, esi, edi, 0x101df1, efl f, icAdd ic0 157⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 24, ebp, esi, edi, 0x101df4, efl (addF 4 L 24 0).2,
        icAdd ic0 158⟩) := by
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  have h : runI img 1 (St.m ⟨N.get, eax, ecx, edx, ebx, L, ebp, esi, edi, 0x101df1, efl f, icAdd ic0 157⟩) =
      some (St.m ⟨N.get, eax, ecx, edx, ebx, (addF 4 L 24 0).1, ebp, esi, edi, 0x101df4,
        efl (addF 4 L 24 0).2, icAdd ic0 158⟩) := by
    cbv
  rw [tb_esp_add] at h
  exact run_of_runI h (icB hic (by decide))

/-- `popl %esi ; popl %edi ; popl %ebx ; popl %ebp ; retl` -/
theorem tb_epi (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 44)
    (eax ecx edx ebx ebp esi edi f esi0 edi0 ebx0 ebp0 ret : UInt32)
    (l1 : rdRaw N.get (UInt32.add L 24) 4 = esi0) (l2 : rdRaw N.get (UInt32.add L 28) 4 = edi0)
    (l3 : rdRaw N.get (UInt32.add L 32) 4 = ebx0) (l4 : rdRaw N.get (UInt32.add L 36) 4 = ebp0)
    (l5 : rdRaw N.get (UInt32.add L 40) 4 = ret) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 24, ebp, esi, edi, 0x101df4, efl f, icAdd ic0 158⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx0, UInt32.add L 44, ebp0, esi0, edi0, ret, efl f, icAdd ic0 163⟩) := by
  subst l1 l2 l3 l4 l5
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  refine run_of_runI (k := 5) ?_ (icB hic (by decide))
  cbv

end Solutions.OpensslX25519.I
