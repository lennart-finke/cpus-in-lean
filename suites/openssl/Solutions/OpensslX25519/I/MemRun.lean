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
# The instructions of `memset` (`0x103f60`) and of the forward copy of `memmove` (`0x103f10`)

Pieces of at most a few instructions, run by `cbv` from a memory `N` given by the words it reads.
The frame of `memset` is the 20 bytes from `L = sp - 4` (saved `esi`, the return address, `dst`,
`c`, `n`); that of `memmove` the 24 bytes from `L = sp - 8` (saved `esi`, `ebx`, the return address,
`dst`, `src`, `n`). Conditional jumps on the counters are decided by `Solutions.Exec.Branch` from
the hypotheses on the counters; byte stores are `CodeMem.wr1` (`Solutions.Exec.Byte`).
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast Solutions.Exec.Branch
  Solutions.Exec.Byte

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

set_option exec.addrSub true in
/-- `pushl %esi ; movl 0x10(%esp), %ecx ; movl 0x8(%esp), %eax ; testl %ecx, %ecx` -/
theorem ms_a (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 20)
    (eax ecx edx ebx ebp esi edi fl dst n : UInt32) (ld : rdRaw N.get (UInt32.add L 8) 4 = dst)
    (ln : rdRaw N.get (UInt32.add L 16) 4 = n) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 4, ebp, esi, edi, 0x103f60, efl fl, icAdd ic0 0⟩)
      (St.m ⟨(stF0 N L 20 esi hS (by decide)).get, dst, n, edx, ebx, L, ebp, esi, edi, 0x103f6b,
        efl (logicF 4 (UInt32.land n n)).2, icAdd ic0 4⟩) := by
  refine run_of_runI (k := 4) ?_ (icB hic (by decide))
  subst ld ln
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `je` (not taken) `; movl 0xc(%esp), %edx ; movl %eax, %esi ; nop × 13` -/
theorem ms_b (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 20)
    (eax ecx edx ebx ebp esi edi g c : UInt32) (hg : UInt32.land (efl g) 64 = 0)
    (lc : rdRaw N.get (UInt32.add L 12) 4 = c) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, L, ebp, esi, edi, 0x103f6b, efl g, icAdd ic0 4⟩)
      (St.m ⟨N.get, eax, ecx, c, ebx, L, ebp, eax, edi, 0x103f80, efl g, icAdd ic0 20⟩) := by
  refine run_of_runI (k := 16) ?_ (icB hic (by decide))
  subst lc
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- One byte: `movb %dl, (%esi) ; incl %esi ; decl %ecx ; jne` (taken). -/
theorem ms_iter (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (p : UInt32)
    (ok : StoreOk1 Image.base Image.size N.mem p) (htop : N.get.size ≤ ramTop)
    (eax ecx edx ebx ebp edi fl L : UInt32) (hx : ecx.toNat ≠ 1) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, L, ebp, p, edi, 0x103f80, efl fl, icAdd ic 0⟩)
      (St.m ⟨(CodeMem.wr1 N p (UInt32.land edx 255) ok).get, eax, (subF 4 ecx 1 0).1, edx, ebx, L, ebp,
        UInt32.add p 1, edi, 0x103f80, efl (mixF (mixF fl (addF 4 p 1 0).2 2260) (subF 4 ecx 1 0).2 2260),
        icAdd ic 4⟩) := by
  refine run_of_runI (k := 4) ?_ (icB hic (by decide))
  have h1 : p.toNat < N.get.size := ok.1
  have h2 := ok.2
  have hb : Image.base.toNat = 0x100000 := rfl
  have hs : Image.size = 47024 := rfl
  rw [hb, hs] at h2
  cbv

/-- The last byte: `movb %dl, (%esi) ; incl %esi ; decl %ecx ; jne` (not taken). -/
theorem ms_last (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (p : UInt32)
    (ok : StoreOk1 Image.base Image.size N.mem p) (htop : N.get.size ≤ ramTop)
    (eax ecx edx ebx ebp edi fl L : UInt32) (hx : ecx.toNat = 1) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, L, ebp, p, edi, 0x103f80, efl fl, icAdd ic 0⟩)
      (St.m ⟨(CodeMem.wr1 N p (UInt32.land edx 255) ok).get, eax, (subF 4 ecx 1 0).1, edx, ebx, L, ebp,
        UInt32.add p 1, edi, 0x103f86, efl (mixF (mixF fl (addF 4 p 1 0).2 2260) (subF 4 ecx 1 0).2 2260),
        icAdd ic 4⟩) := by
  refine run_of_runI (k := 4) ?_ (icB hic (by decide))
  have h1 : p.toNat < N.get.size := ok.1
  have h2 := ok.2
  have hb : Image.base.toNat = 0x100000 := rfl
  have hs : Image.size = 47024 := rfl
  rw [hb, hs] at h2
  cbv

/-- `je` (taken, `n = 0`). -/
theorem ms_zero (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 20)
    (eax ecx edx ebx ebp esi edi g : UInt32) (hg : UInt32.land (efl g) 64 = 64) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, L, ebp, esi, edi, 0x103f6b, efl g, icAdd ic0 4⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, L, ebp, esi, edi, 0x103f86, efl g, icAdd ic0 5⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `popl %esi ; retl` -/
theorem ms_tail (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 20)
    (eax ecx edx ebx ebp esi edi fl s0 ret : UInt32) (l0 : rdRaw N.get L 4 = s0)
    (l1 : rdRaw N.get (UInt32.add L 4) 4 = ret) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, L, ebp, esi, edi, 0x103f86, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, s0, edi, ret, efl fl, icAdd ic 2⟩) := by
  refine run_of_runI (k := 2) ?_ (icB hic (by decide))
  subst l0 l1
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

set_option exec.addrSub true in
/-- `memmove`: `pushl %ebx ; pushl %esi ; movl 0x14(%esp), %edx ; movl 0x10(%esp), %ecx ;
movl 0xc(%esp), %eax ; cmpl %ecx, %eax ; jbe` (taken: `dst < src`) -/
theorem mm_a (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 24)
    (eax ecx edx ebx ebp esi edi fl dst src n : UInt32) (ld : rdRaw N.get (UInt32.add L 12) 4 = dst)
    (ls : rdRaw N.get (UInt32.add L 16) 4 = src) (ln : rdRaw N.get (UInt32.add L 20) 4 = n)
    (hds : dst.toNat < src.toNat) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x103f10, efl fl, icAdd ic0 0⟩)
      (St.m ⟨(stF0 (stF N L 24 4 ebx hS (by decide)) L 24 esi stF_FB (by decide)).get, dst, src, n, ebx, L, ebp,
        esi, edi, 0x103f40, efl (subF 4 dst src 0).2, icAdd ic0 7⟩) := by
  refine run_of_runI (k := 7) ?_ (icB hic (by decide))
  subst ld ls ln
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `testl %edx, %edx ; je` (not taken) `; xorl %esi, %esi ; nop × 10` -/
theorem mm_b (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 24)
    (eax ecx n ebx ebp esi edi fl : UInt32) (hn : n.toNat ≠ 0) :
    Run img (St.m ⟨N.get, eax, ecx, n, ebx, L, ebp, esi, edi, 0x103f40, efl fl, icAdd ic0 7⟩)
      (St.m ⟨N.get, eax, ecx, n, ebx, L, ebp, 0, edi, 0x103f50, efl (logicF 4 0).2, icAdd ic0 20⟩) := by
  refine run_of_runI (k := 13) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- One byte: `movzbl (%ecx,%esi), %ebx ; movb %bl, (%eax,%esi) ; incl %esi ; cmpl %esi, %edx ; jne` (taken). -/
theorem mm_iter (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (dst src i n b : UInt32)
    (ok : StoreOk1 Image.base Image.size N.mem (UInt32.add dst i)) (htop : N.get.size ≤ ramTop)
    (hsrc : (UInt32.add src i).toNat < N.get.size) (lb : rdRaw N.get (UInt32.add src i) 1 = b)
    (hsrc2 : (UInt32.add src i).toNat < 1048576 ∨ 1048576 + 47024 ≤ (UInt32.add src i).toNat)
    (ebx ebp edi fl L : UInt32) (hx : n.toNat ≠ (UInt32.add i 1).toNat) :
    Run img (St.m ⟨N.get, dst, src, n, ebx, L, ebp, i, edi, 0x103f50, efl fl, icAdd ic 0⟩)
      (St.m ⟨(CodeMem.wr1 N (UInt32.add dst i) (UInt32.land b 255) ok).get, dst, src, n, b, L, ebp,
        UInt32.add i 1, edi, 0x103f50, efl (subF 4 n (UInt32.add i 1) 0).2, icAdd ic 5⟩) := by
  refine run_of_runI (k := 5) ?_ (icB hic (by decide))
  subst lb
  have h1 : (UInt32.add dst i).toNat < N.get.size := ok.1
  have h2 := ok.2
  have hb : Image.base.toNat = 0x100000 := rfl
  have hs : Image.size = 47024 := rfl
  rw [hb, hs] at h2
  cbv

/-- The last byte (`jne` not taken). -/
theorem mm_last (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (dst src i n b : UInt32)
    (ok : StoreOk1 Image.base Image.size N.mem (UInt32.add dst i)) (htop : N.get.size ≤ ramTop)
    (hsrc : (UInt32.add src i).toNat < N.get.size) (lb : rdRaw N.get (UInt32.add src i) 1 = b)
    (hsrc2 : (UInt32.add src i).toNat < 1048576 ∨ 1048576 + 47024 ≤ (UInt32.add src i).toNat)
    (ebx ebp edi fl L : UInt32) (hx : n.toNat = (UInt32.add i 1).toNat) :
    Run img (St.m ⟨N.get, dst, src, n, ebx, L, ebp, i, edi, 0x103f50, efl fl, icAdd ic 0⟩)
      (St.m ⟨(CodeMem.wr1 N (UInt32.add dst i) (UInt32.land b 255) ok).get, dst, src, n, b, L, ebp,
        UInt32.add i 1, edi, 0x103f5c, efl (subF 4 n (UInt32.add i 1) 0).2, icAdd ic 5⟩) := by
  refine run_of_runI (k := 5) ?_ (icB hic (by decide))
  subst lb
  have h1 : (UInt32.add dst i).toNat < N.get.size := ok.1
  have h2 := ok.2
  have hb : Image.base.toNat = 0x100000 := rfl
  have hs : Image.size = 47024 := rfl
  rw [hb, hs] at h2
  cbv

/-- `popl %esi ; popl %ebx ; retl` -/
theorem mm_tail (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 24)
    (eax ecx edx ebx ebp esi edi fl s0 b0 ret : UInt32) (l0 : rdRaw N.get L 4 = s0)
    (l1 : rdRaw N.get (UInt32.add L 4) 4 = b0) (l2 : rdRaw N.get (UInt32.add L 8) 4 = ret) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, L, ebp, esi, edi, 0x103f5c, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, b0, UInt32.add L 12, ebp, s0, edi, ret, efl fl, icAdd ic 3⟩) := by
  refine run_of_runI (k := 3) ?_ (icB hic (by decide))
  subst l0 l1 l2
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

end Solutions.OpensslX25519.I
