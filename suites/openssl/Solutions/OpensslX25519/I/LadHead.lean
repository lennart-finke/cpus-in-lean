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
import Solutions.Exec.Shift
/-!
# The head of the ladder loop of `x25519_scalar_mult_generic`

The load of the scalar byte at position `esi >> 3` and the bit index `esi & 7`:
`movl %esi, %eax ; shrl $3, %eax` (`lh1`), `movzbl 0x8(%esp,%eax), %eax ; movl %esi, %ecx ; andl $7, %ecx`
(`lh2`). (The rest of the head, `btl … setb …`, is not done yet: see NOTES-X25519.md.)
The frame is `[L, L + 344)` with `esp = L + 8`; flags of the immediate operations are passed on as variables.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast
  Solutions.Exec.Branch Solutions.Exec.Byte Solutions.Exec.Shift

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

/-- `movl %esi, %eax ; shrl $3, %eax` -/
theorem lh1 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 344)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x103990, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, Shift.shrR esi 3, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x103995, efl (Shift.shrF esi 3),
        icAdd ic 2⟩) := by
  refine run_of_runI (k := 2) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `movzbl 0x8(%esp,%eax), %eax ; movl %esi, %ecx ; andl $7, %ecx` -/
theorem lh2 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 344)
    (q ecx edx ebx ebp esi edi fl y : UInt32) (hq : q.toNat < 32)
    (ly : rdRaw N.get (UInt32.add (UInt32.add (UInt32.add L 8) q) 8) 1 = y) :
    Run img (St.m ⟨N.get, q, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x103995, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, y, (logicF 4 (esi.land 7)).1, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x10399f,
        efl (logicF 4 (esi.land 7)).2, icAdd ic 3⟩) := by
  refine run_of_runI (k := 3) ?_ (icB hic (by decide))
  subst ly
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

end Solutions.OpensslX25519.I
