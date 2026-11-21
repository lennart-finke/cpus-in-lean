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
# The instructions of `memcpy` (`0x103ee0`)

The pieces of `memmove`'s forward copy (`I/MemRun`) with `memcpy`'s registers (`eax` = dst, `ecx` = n,
`edx` = src, `esi` = index, `ebx` = the byte). The frame is the 24 bytes from `L = sp - 8` (saved `esi`,
`ebx`, the return address, `dst`, `src`, `n`). Prover P.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast Solutions.Exec.Branch
  Solutions.Exec.Byte

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

set_option exec.addrSub true in

set_option exec.addrSub true in
/-- `memcpy`: `pushl %ebx ; pushl %esi ; movl 0x14(%esp), %ecx ; movl 0xc(%esp), %eax` -/
theorem mc_a (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 24)
    (eax ecx edx ebx ebp esi edi fl dst n : UInt32) (ld : rdRaw N.get (UInt32.add L 12) 4 = dst)
    (ln : rdRaw N.get (UInt32.add L 20) 4 = n) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x103ee0, efl fl, icAdd ic0 0⟩)
      (St.m ⟨(stF0 (stF N L 24 4 ebx hS (by decide)) L 24 esi stF_FB (by decide)).get, dst, n, edx, ebx, L, ebp,
        esi, edi, 0x103eea, efl fl, icAdd ic0 4⟩) := by
  refine run_of_runI (k := 4) ?_ (icB hic (by decide))
  subst ld ln
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `testl %ecx, %ecx ; je` (not taken) `; movl 0x10(%esp), %edx ; xorl %esi, %esi ; nop × 12` -/
theorem mc_b (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 24)
    (eax n edx ebx ebp esi edi fl src : UInt32) (hn : n.toNat ≠ 0) (ls : rdRaw N.get (UInt32.add L 16) 4 = src) :
    Run img (St.m ⟨N.get, eax, n, edx, ebx, L, ebp, esi, edi, 0x103eea, efl fl, icAdd ic0 0⟩)
      (St.m ⟨N.get, eax, n, src, ebx, L, ebp, 0, edi, 0x103f00, efl (logicF 4 0).2, icAdd ic0 16⟩) := by
  refine run_of_runI (k := 16) ?_ (icB hic (by decide))
  subst ls
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- One byte: `movzbl (%edx,%esi), %ebx ; movb %bl, (%eax,%esi) ; incl %esi ; cmpl %esi, %ecx ; jne` (taken). -/
theorem mc_iter (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (dst src i n b : UInt32)
    (ok : StoreOk1 Image.base Image.size N.mem (UInt32.add dst i)) (htop : N.get.size ≤ ramTop)
    (hsrc : (UInt32.add src i).toNat < N.get.size) (lb : rdRaw N.get (UInt32.add src i) 1 = b)
    (hsrc2 : (UInt32.add src i).toNat < 1048576 ∨ 1048576 + 47024 ≤ (UInt32.add src i).toNat)
    (ebx ebp edi fl L : UInt32) (hx : n.toNat ≠ (UInt32.add i 1).toNat) :
    Run img (St.m ⟨N.get, dst, n, src, ebx, L, ebp, i, edi, 0x103f00, efl fl, icAdd ic 0⟩)
      (St.m ⟨(CodeMem.wr1 N (UInt32.add dst i) (UInt32.land b 255) ok).get, dst, n, src, b, L, ebp,
        UInt32.add i 1, edi, 0x103f00, efl (subF 4 n (UInt32.add i 1) 0).2, icAdd ic 5⟩) := by
  refine run_of_runI (k := 5) ?_ (icB hic (by decide))
  subst lb
  have h1 : (UInt32.add dst i).toNat < N.get.size := ok.1
  have h2 := ok.2
  have hb : Image.base.toNat = 0x100000 := rfl
  have hs : Image.size = 47024 := rfl
  rw [hb, hs] at h2
  cbv

/-- The last byte (`jne` not taken). -/
theorem mc_last (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (dst src i n b : UInt32)
    (ok : StoreOk1 Image.base Image.size N.mem (UInt32.add dst i)) (htop : N.get.size ≤ ramTop)
    (hsrc : (UInt32.add src i).toNat < N.get.size) (lb : rdRaw N.get (UInt32.add src i) 1 = b)
    (hsrc2 : (UInt32.add src i).toNat < 1048576 ∨ 1048576 + 47024 ≤ (UInt32.add src i).toNat)
    (ebx ebp edi fl L : UInt32) (hx : n.toNat = (UInt32.add i 1).toNat) :
    Run img (St.m ⟨N.get, dst, n, src, ebx, L, ebp, i, edi, 0x103f00, efl fl, icAdd ic 0⟩)
      (St.m ⟨(CodeMem.wr1 N (UInt32.add dst i) (UInt32.land b 255) ok).get, dst, n, src, b, L, ebp,
        UInt32.add i 1, edi, 0x103f0c, efl (subF 4 n (UInt32.add i 1) 0).2, icAdd ic 5⟩) := by
  refine run_of_runI (k := 5) ?_ (icB hic (by decide))
  subst lb
  have h1 : (UInt32.add dst i).toNat < N.get.size := ok.1
  have h2 := ok.2
  have hb : Image.base.toNat = 0x100000 := rfl
  have hs : Image.size = 47024 := rfl
  rw [hb, hs] at h2
  cbv

/-- `popl %esi ; popl %ebx ; retl` -/
theorem mc_tail (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 24)
    (eax ecx edx ebx ebp esi edi fl s0 b0 ret : UInt32) (l0 : rdRaw N.get L 4 = s0)
    (l1 : rdRaw N.get (UInt32.add L 4) 4 = b0) (l2 : rdRaw N.get (UInt32.add L 8) 4 = ret) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, L, ebp, esi, edi, 0x103f0c, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, b0, UInt32.add L 12, ebp, s0, edi, ret, efl fl, icAdd ic 3⟩) := by
  refine run_of_runI (k := 3) ?_ (icB hic (by decide))
  subst l0 l1 l2
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

end Solutions.OpensslX25519.I
