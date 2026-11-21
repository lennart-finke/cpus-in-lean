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
# The instructions of `CRYPTO_memcmp` (`0x103ea0`)

The frame is the 28 bytes from `L = sp - 12` (saved `esi`, `edi`, `ebx`, the return address, `a`, `b`,
`len`); the loop at `0x103ec0` has `eax` = the accumulated `or` of `a[i] ^ b[i]`, `ecx` = len, `edx` = b,
`esi` = a, `edi` = i. Prover P.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast Solutions.Exec.Branch
  Solutions.Exec.Byte

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000


set_option exec.addrSub true in
/-- `pushl %ebx ; pushl %edi ; pushl %esi ; movl 0x18(%esp), %ecx ; testl %ecx, %ecx` -/
theorem cm_a (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 28)
    (eax ecx edx ebx ebp esi edi fl n : UInt32) (ln : rdRaw N.get (UInt32.add L 24) 4 = n) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 12, ebp, esi, edi, 0x103ea0, efl fl, icAdd ic0 0⟩)
      (St.m ⟨(stF0 (stF (stF N L 28 8 ebx hS (by decide)) L 28 4 edi stF_FB (by decide)) L 28 esi stF_FB
        (by decide)).get, eax, n, edx, ebx, L, ebp, esi, edi, 0x103ea9, efl (logicF 4 (UInt32.land n n)).2,
        icAdd ic0 5⟩) := by
  refine run_of_runI (k := 5) ?_ (icB hic (by decide))
  subst ln
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `je` (not taken) `; movl 0x14(%esp), %edx ; movl 0x10(%esp), %esi ; xorl %eax, %eax ; xorl %edi, %edi ;
nop × 9` -/
theorem cm_b (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 28)
    (eax n edx ebx ebp esi edi a b : UInt32) (hn : n.toNat ≠ 0) (la : rdRaw N.get (UInt32.add L 16) 4 = a)
    (lb : rdRaw N.get (UInt32.add L 20) 4 = b) :
    Run img (St.m ⟨N.get, eax, n, edx, ebx, L, ebp, esi, edi, 0x103ea9, efl (logicF 4 (UInt32.land n n)).2,
        icAdd ic0 0⟩)
      (St.m ⟨N.get, 0, n, b, ebx, L, ebp, a, 0, 0x103ec0, efl (logicF 4 0).2, icAdd ic0 14⟩) := by
  refine run_of_runI (k := 14) ?_ (icB hic (by decide))
  subst la lb
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- One byte: `movzbl (%esi,%edi), %ebx ; xorb (%edx,%edi), %bl ; movzbl %bl, %ebx ; orl %ebx, %eax ; incl %edi ;
cmpl %edi, %ecx ; jne` (taken) -/
theorem cm_iter (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L a b n i acc ebx ebp fl ya yb : UInt32)
    (htop : N.get.size ≤ ramTop) (ha : (UInt32.add a i).toNat < N.get.size) (hb : (UInt32.add b i).toNat < N.get.size)
    (ha2 : (UInt32.add a i).toNat < 1048576 ∨ 1048576 + 47024 ≤ (UInt32.add a i).toNat)
    (hb2 : (UInt32.add b i).toNat < 1048576 ∨ 1048576 + 47024 ≤ (UInt32.add b i).toNat)
    (la : rdRaw N.get (UInt32.add a i) 1 = ya) (lb : rdRaw N.get (UInt32.add b i) 1 = yb)
    (hx : n.toNat ≠ (UInt32.add i 1).toNat) :
    Run img (St.m ⟨N.get, acc, n, b, ebx, L, ebp, a, i, 0x103ec0, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, (logicF 4 (acc.lor ((((ya.land 4294967040).lor ((logicF 1 ((ya.land 255).xor yb)).1.land 255)).land 255)))).1, n, b, ((((ya.land 4294967040).lor ((logicF 1 ((ya.land 255).xor yb)).1.land 255)).land 255)), L, ebp, a, UInt32.add i 1, 0x103ec0,
        efl (subF 4 n (UInt32.add i 1) 0).2, icAdd ic 7⟩) := by
  refine run_of_runI (k := 7) ?_ (icB hic (by decide))
  subst la lb
  cbv

/-- The last byte (`jne` not taken). -/
theorem cm_last (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L a b n i acc ebx ebp fl ya yb : UInt32)
    (htop : N.get.size ≤ ramTop) (ha : (UInt32.add a i).toNat < N.get.size) (hb : (UInt32.add b i).toNat < N.get.size)
    (ha2 : (UInt32.add a i).toNat < 1048576 ∨ 1048576 + 47024 ≤ (UInt32.add a i).toNat)
    (hb2 : (UInt32.add b i).toNat < 1048576 ∨ 1048576 + 47024 ≤ (UInt32.add b i).toNat)
    (la : rdRaw N.get (UInt32.add a i) 1 = ya) (lb : rdRaw N.get (UInt32.add b i) 1 = yb)
    (hx : n.toNat = (UInt32.add i 1).toNat) :
    Run img (St.m ⟨N.get, acc, n, b, ebx, L, ebp, a, i, 0x103ec0, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, (logicF 4 (acc.lor ((((ya.land 4294967040).lor ((logicF 1 ((ya.land 255).xor yb)).1.land 255)).land 255)))).1, n, b, ((((ya.land 4294967040).lor ((logicF 1 ((ya.land 255).xor yb)).1.land 255)).land 255)), L, ebp, a, UInt32.add i 1, 0x103ed1,
        efl (subF 4 n (UInt32.add i 1) 0).2, icAdd ic 7⟩) := by
  refine run_of_runI (k := 7) ?_ (icB hic (by decide))
  subst la lb
  cbv

/-- `popl %esi ; popl %edi ; popl %ebx ; retl` -/
theorem cm_tail (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 28)
    (eax ecx edx ebx ebp esi edi fl s0 d0 b0 ret : UInt32) (l0 : rdRaw N.get L 4 = s0)
    (l1 : rdRaw N.get (UInt32.add L 4) 4 = d0) (l2 : rdRaw N.get (UInt32.add L 8) 4 = b0)
    (l3 : rdRaw N.get (UInt32.add L 12) 4 = ret) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, L, ebp, esi, edi, 0x103ed1, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, b0, UInt32.add L 16, ebp, s0, d0, ret, efl fl, icAdd ic 4⟩) := by
  refine run_of_runI (k := 4) ?_ (icB hic (by decide))
  subst l0 l1 l2 l3
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

end Solutions.OpensslX25519.I
