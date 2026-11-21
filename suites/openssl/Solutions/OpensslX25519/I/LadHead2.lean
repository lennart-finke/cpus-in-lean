import Solutions.OpensslX25519.I.LadHead
import Solutions.Exec.Bit
/-!
# The ladder loop of `x25519_scalar_mult_generic`: the rest of the head, and the loop control

`btl %ecx, %eax ; movl $0, %eax ; setb %al` (`lh3`: the bit, as `setbV`, through the opaque `bitU` of
`Solutions.Exec.Bit`), `movl %eax, 0x4(%esp) ; xorl %eax, %edi ; leal 0x50(%esp), %ecx ;
leal 0x78(%esp), %edx ; pushl %edi ; calll fe_cswap` (`lp1`), and `addl $-1, %esi` (`lc1`),
`movl 0x4(%esp), %edi ; jb` (`lc2t` taken, `lc2x` not taken; the carry as a hypothesis on the flags
variable). The frame is `[L, L + 344)` with `esp = L + 8`.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast
  Solutions.Exec.Branch Solutions.Exec.Byte Solutions.Exec.Shift Solutions.Exec.Bit

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

/-- The bit that `bt %ecx, %eax` tests (`(y >> (r & 31)) & 1 ≠ 0`). -/
def btV (y r : UInt32) : Bool := !decide (UInt32.land (y.shiftRight (r.land 31)) 1 = 0)
/-- `eax` after `movl $0, %eax ; setb %al`. -/
def setbV (fl y r : UInt32) : UInt32 := UInt32.lor 0 (UInt32.land (bitU (cfB (mixF fl (bitU (btV y r)) 1))) 255)

/-- `btl %ecx, %eax ; movl $0, %eax ; setb %al` -/
theorem lh3 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 344)
    (y r edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, y, r, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x10399f, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, setbV fl y r, r, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x1039aa,
        efl (mixF fl (bitU (btV y r)) 1), icAdd ic 3⟩) := by
  refine run_of_runI (k := 3) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv
  simp only [ite_bitU, ite_bitU_cf]

set_option exec.addrSub true in
/-- `movl %eax, 0x4(%esp) ; xorl %eax, %edi ; leal 0x50(%esp), %ecx ; leal 0x78(%esp), %edx ; pushl %edi ;
calll fe_cswap` -/
theorem lp1 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 344)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x1039aa, efl fl, icAdd ic 0⟩)
      (St.m ⟨(stF0 (stF (stF N L 344 12 eax hS (by decide)) L 344 4 (edi.xor eax) stF_FB (by decide)) L 344 0x1039be
        stF_FB (by decide)).get, eax, UInt32.add L 88, UInt32.add L 128, ebx, L, ebp, esi, edi.xor eax, 0x103b40,
        efl (logicF 4 (edi.xor eax)).2, icAdd ic 6⟩) := by
  refine run_of_runI (k := 6) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `addl $-1, %esi` -/
theorem lc1 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 344)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x103af0, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, UInt32.add esi 4294967295, edi, 0x103af3,
        efl (addF 4 esi 4294967295 0).2, icAdd ic 1⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `movl 0x4(%esp), %edi ; jb` (taken) -/
theorem lc2t (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 344)
    (eax ecx edx ebx ebp esi edi g b : UInt32) (hc : Mul.cfB g = true) (lb : rdRaw N.get (UInt32.add L 12) 4 = b) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x103af3, efl g, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, b, 0x103990, efl g, icAdd ic 2⟩) := by
  refine run_of_runI (k := 2) ?_ (icB hic (by decide))
  subst lb
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `movl 0x4(%esp), %edi ; jb` (not taken) -/
theorem lc2x (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 344)
    (eax ecx edx ebx ebp esi edi g b : UInt32) (hc : Mul.cfB g = false) (lb : rdRaw N.get (UInt32.add L 12) 4 = b) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x103af3, efl g, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, b, 0x103afd, efl g, icAdd ic 2⟩) := by
  refine run_of_runI (k := 2) ?_ (icB hic (by decide))
  subst lb
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

end Solutions.OpensslX25519.I
