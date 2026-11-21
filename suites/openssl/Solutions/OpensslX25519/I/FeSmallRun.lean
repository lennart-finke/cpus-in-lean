import Solutions.OpensslX25519.Frame
import Solutions.OpensslX25519.I.Base
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
/-!
# The instructions of `fe_0` (`0x1021e0`), `fe_1` (`0x1021f0`) and `fe_copy` (`0x102280`)

Around their calls of `memset`/`memmove`: the argument pushes and the call, the release of the
arguments, the store of the limb `1` (`fe_1`), the return. Frames from `L`: `fe_0` 24 bytes
(`L = sp - 20`), `fe_1` and `fe_copy` 28 bytes (`L = sp - 24`), so that the callee's frame starts at `L`.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast Solutions.Exec.Branch
  Solutions.Exec.Byte

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

set_option exec.addrSub true in
/-- `fe_0`: `pushl $0x28 ; pushl $0x0 ; pushl %ecx ; calll memset` -/
theorem f0_a (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 24)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 20, ebp, esi, edi, 0x1021e0, efl fl, icAdd ic0 0⟩)
      (St.m ⟨(stF (stF (stF (stF N L 24 16 40 hS (by decide)) L 24 12 0 stF_FB (by decide)) L 24 8 ecx stF_FB
        (by decide)) L 24 4 0x1021ea stF_FB (by decide)).get, eax, ecx, edx, ebx, UInt32.add L 4, ebp, esi, edi,
        0x103f60, efl fl, icAdd ic0 4⟩) := by
  refine run_of_runI (k := 4) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `addl $0xc, %esp` (after the call of `memset` in `fe_0`) -/
theorem f0_b (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 24)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x1021ea, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 20, ebp, esi, edi, 0x1021ed,
        efl (addF 4 (UInt32.add L 8) 12 0).2, icAdd ic 1⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `retl` (of `fe_0`) -/
theorem f0_c (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 24)
    (eax ecx edx ebx ebp esi edi fl ret : UInt32) (lr : rdRaw N.get (UInt32.add L 20) 4 = ret) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 20, ebp, esi, edi, 0x1021ed, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 24, ebp, esi, edi, ret, efl fl, icAdd ic 1⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  subst lr
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

set_option exec.addrSub true in
/-- `fe_1`: `pushl %esi ; movl %ecx, %esi ; pushl $0x28` -/
theorem f1_a (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 28)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 24, ebp, esi, edi, 0x1021f0, efl fl, icAdd ic0 0⟩)
      (St.m ⟨(stF (stF N L 28 20 esi hS (by decide)) L 28 16 40 stF_FB (by decide)).get, eax, ecx, edx, ebx,
        UInt32.add L 16, ebp, ecx, edi, 0x1021f5, efl fl, icAdd ic0 3⟩) := by
  refine run_of_runI (k := 3) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

set_option exec.addrSub true in
/-- `fe_1`: `pushl $0x0 ; pushl %ecx ; calll memset` -/
theorem f1_b (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 28)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 16, ebp, esi, edi, 0x1021f5, efl fl, icAdd ic 0⟩)
      (St.m ⟨(stF (stF (stF N L 28 12 0 hS (by decide)) L 28 8 ecx stF_FB (by decide)) L 28 4 0x1021fd stF_FB
        (by decide)).get, eax, ecx, edx, ebx, UInt32.add L 4, ebp, esi, edi, 0x103f60, efl fl, icAdd ic 3⟩) := by
  refine run_of_runI (k := 3) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `addl $0xc, %esp` (in `fe_1`) -/
theorem f1_c (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 28)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x1021fd, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 20, ebp, esi, edi, 0x102200,
        efl (addF 4 (UInt32.add L 8) 12 0).2, icAdd ic 1⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `movl $0x1, (%esi) ; popl %esi ; retl` (end of `fe_1`) -/
theorem f1_d (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L hp : UInt32) (hS : FB N.get.size L 28)
    (hH : FB N.get.size hp 40) (hd : hp.toNat + 40 ≤ L.toNat ∨ L.toNat + 28 ≤ hp.toNat)
    (eax ecx edx ebx ebp edi fl s0 ret : UInt32) (l0 : rdRaw N.get (UInt32.add L 20) 4 = s0)
    (lr : rdRaw N.get (UInt32.add L 24) 4 = ret) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 20, ebp, hp, edi, 0x102200, efl fl, icAdd ic 0⟩)
      (St.m ⟨(stF0 N hp 40 1 hH (by decide)).get, eax, ecx, edx, ebx, UInt32.add L 28, ebp, s0, edi, ret, efl fl,
        icAdd ic 3⟩) := by
  refine run_of_runI (k := 3) ?_ (icB hic (by decide))
  subst l0 lr
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img; have h4 := hH.fit; have h5 := hH.img
  cbv

set_option exec.addrSub true in
/-- `fe_copy`: `pushl $0x28 ; pushl %edx ; pushl %ecx ; calll memmove` -/
theorem fc_a (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 28)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 24, ebp, esi, edi, 0x102280, efl fl, icAdd ic0 0⟩)
      (St.m ⟨(stF (stF (stF (stF N L 28 20 40 hS (by decide)) L 28 16 edx stF_FB (by decide)) L 28 12 ecx stF_FB
        (by decide)) L 28 8 0x102289 stF_FB (by decide)).get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi,
        0x103f10, efl fl, icAdd ic0 4⟩) := by
  refine run_of_runI (k := 4) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `addl $0xc, %esp` (in `fe_copy`) -/
theorem fc_b (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 28)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 12, ebp, esi, edi, 0x102289, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 24, ebp, esi, edi, 0x10228c,
        efl (addF 4 (UInt32.add L 12) 12 0).2, icAdd ic 1⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `retl` (of `fe_copy`) -/
theorem fc_c (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 28)
    (eax ecx edx ebx ebp esi edi fl ret : UInt32) (lr : rdRaw N.get (UInt32.add L 24) 4 = ret) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 24, ebp, esi, edi, 0x10228c, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 28, ebp, esi, edi, ret, efl fl, icAdd ic 1⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  subst lr
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

end Solutions.OpensslX25519.I
