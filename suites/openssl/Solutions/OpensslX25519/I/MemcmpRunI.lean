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
import Solutions.Exec.CodeRd
import Solutions.OpensslX25519.I.MemcmpRun
/-!
# `CRYPTO_memcmp`'s loop with the first buffer inside the image

The loop pieces of `I/MemcmpRun` without the hypotheses that the buffers are outside the image (the first
argument of the call in `ossl_x25519` is `kZeros`, inside it): data reads through
`Solutions.Exec.CodeRd.cbvRdAny`. Prover P.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast Solutions.Exec.Branch
  Solutions.Exec.Byte Solutions.Exec.CodeRd

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000


attribute [-cbvSimprocAttr] Solutions.Exec.Byte.cbvRdOut

/-- One byte: `movzbl (%esi,%edi), %ebx ; xorb (%edx,%edi), %bl ; movzbl %bl, %ebx ; orl %ebx, %eax ; incl %edi ;
cmpl %edi, %ecx ; jne` (taken) -/
theorem cm_iterI (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L a b n i acc ebx ebp fl ya yb : UInt32)
    (htop : N.get.size ≤ ramTop) (ha : (UInt32.add a i).toNat < N.get.size) (hb : (UInt32.add b i).toNat < N.get.size)
    (la : rdRaw N.get (UInt32.add a i) 1 = ya) (lb : rdRaw N.get (UInt32.add b i) 1 = yb)
    (hx : n.toNat ≠ (UInt32.add i 1).toNat) :
    Run img (St.m ⟨N.get, acc, n, b, ebx, L, ebp, a, i, 0x103ec0, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, (logicF 4 (acc.lor ((((ya.land 4294967040).lor ((logicF 1 ((ya.land 255).xor yb)).1.land 255)).land 255)))).1, n, b, ((((ya.land 4294967040).lor ((logicF 1 ((ya.land 255).xor yb)).1.land 255)).land 255)), L, ebp, a, UInt32.add i 1, 0x103ec0,
        efl (subF 4 n (UInt32.add i 1) 0).2, icAdd ic 7⟩) := by
  refine run_of_runI (k := 7) ?_ (icB hic (by decide))
  subst la lb
  cbv

/-- The last byte (`jne` not taken). -/
theorem cm_lastI (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L a b n i acc ebx ebp fl ya yb : UInt32)
    (htop : N.get.size ≤ ramTop) (ha : (UInt32.add a i).toNat < N.get.size) (hb : (UInt32.add b i).toNat < N.get.size)
    (la : rdRaw N.get (UInt32.add a i) 1 = ya) (lb : rdRaw N.get (UInt32.add b i) 1 = yb)
    (hx : n.toNat = (UInt32.add i 1).toNat) :
    Run img (St.m ⟨N.get, acc, n, b, ebx, L, ebp, a, i, 0x103ec0, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, (logicF 4 (acc.lor ((((ya.land 4294967040).lor ((logicF 1 ((ya.land 255).xor yb)).1.land 255)).land 255)))).1, n, b, ((((ya.land 4294967040).lor ((logicF 1 ((ya.land 255).xor yb)).1.land 255)).land 255)), L, ebp, a, UInt32.add i 1, 0x103ed1,
        efl (subF 4 n (UInt32.add i 1) 0).2, icAdd ic 7⟩) := by
  refine run_of_runI (k := 7) ?_ (icB hic (by decide))
  subst la lb
  cbv

end Solutions.OpensslX25519.I
