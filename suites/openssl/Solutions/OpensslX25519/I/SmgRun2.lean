import Solutions.OpensslX25519.I.TbBase
import Solutions.OpensslX25519.I.LadRun1
/-!
# `x25519_scalar_mult_generic` (`0x103910`): the calls outside the ladder loop

Frame `[L, L + 344)` (the `CSt` region), esp `L + 8`: the instructions that load the arguments of the calls of
`fe_frombytes`, `fe_1`, `fe_0`, `fe_copy`, `fe_1`, the loop entry (`movl $0xfe, %esi ; xorl %edi, %edi ; nop`s),
and after the loop the calls of `fe_invert`, `fe_mul`, `fe_tobytes`. Written by `gen/gensmg.py` (prover R) from
`gen/smgrun2.lean.in` and `genlad.piece_thm`.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast
  Solutions.Exec.Branch Solutions.Exec.Byte

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

set_option exec.addrSub true in
/-- `leal 0xf0(%esp), %edi ; movl %edi, %ecx ; movl %esi, %edx ; calll 0x1036f0` -/
theorem smg_b1 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 344)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x103946, efl fl, icAdd ic 0⟩)
      (St.m ⟨(stF N L 344 4 0x103956 hS (by decide)).get, eax, UInt32.add L 248, esi, ebx, UInt32.add L 4, ebp, esi, UInt32.add L 248, 0x1036f0, efl fl, icAdd ic 4⟩) := by
  refine run_of_runI (k := 4) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

set_option exec.addrSub true in
/-- `leal 0x50(%esp), %ecx ; calll 0x1021f0` -/
theorem smg_b2 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 344)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x103956, efl fl, icAdd ic 0⟩)
      (St.m ⟨(stF N L 344 4 0x10395f hS (by decide)).get, eax, UInt32.add L 88, edx, ebx, UInt32.add L 4, ebp, esi, edi, 0x1021f0, efl fl, icAdd ic 2⟩) := by
  refine run_of_runI (k := 2) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

set_option exec.addrSub true in
/-- `leal 0xc8(%esp), %ecx ; calll 0x1021e0` -/
theorem smg_b3 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 344)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x10395f, efl fl, icAdd ic 0⟩)
      (St.m ⟨(stF N L 344 4 0x10396b hS (by decide)).get, eax, UInt32.add L 208, edx, ebx, UInt32.add L 4, ebp, esi, edi, 0x1021e0, efl fl, icAdd ic 2⟩) := by
  refine run_of_runI (k := 2) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

set_option exec.addrSub true in
/-- `leal 0x78(%esp), %ecx ; movl %edi, %edx ; calll 0x102280` -/
theorem smg_b4 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 344)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x10396b, efl fl, icAdd ic 0⟩)
      (St.m ⟨(stF N L 344 4 0x103976 hS (by decide)).get, eax, UInt32.add L 128, edi, ebx, UInt32.add L 4, ebp, esi, edi, 0x102280, efl fl, icAdd ic 3⟩) := by
  refine run_of_runI (k := 3) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

set_option exec.addrSub true in
/-- `leal 0x28(%esp), %ecx ; calll 0x1021f0` -/
theorem smg_b5 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 344)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x103976, efl fl, icAdd ic 0⟩)
      (St.m ⟨(stF N L 344 4 0x10397f hS (by decide)).get, eax, UInt32.add L 48, edx, ebx, UInt32.add L 4, ebp, esi, edi, 0x1021f0, efl fl, icAdd ic 2⟩) := by
  refine run_of_runI (k := 2) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

set_option exec.addrSub true in
/-- `leal 0xc8(%esp), %edi ; movl %edi, %ecx ; movl %edi, %edx ; calll 0x1005d0` -/
theorem smg_b7 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 344)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x103afd, efl fl, icAdd ic 0⟩)
      (St.m ⟨(stF N L 344 4 0x103b0d hS (by decide)).get, eax, UInt32.add L 208, UInt32.add L 208, ebx, UInt32.add L 4, ebp, esi, UInt32.add L 208, 0x1005d0, efl fl, icAdd ic 4⟩) := by
  refine run_of_runI (k := 4) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

set_option exec.addrSub true in
/-- `leal 0x50(%esp), %esi ; movl %esi, %ecx ; movl %esi, %edx ; pushl %edi ; calll 0x100c20` -/
theorem smg_b8 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 344)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x103b0d, efl fl, icAdd ic 0⟩)
      (St.m ⟨(stF0 (stF N L 344 4 edi hS (by decide)) L 344 0x103b1b stF_FB (by decide)).get, eax, UInt32.add L 88, UInt32.add L 88, ebx, L, ebp, UInt32.add L 88, edi, 0x100c20, efl fl, icAdd ic 5⟩) := by
  refine run_of_runI (k := 5) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `addl $0x4, %esp` -/
theorem smg_a9 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 344)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 4, ebp, esi, edi, 0x103b1b, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x103b1e,
        efl (addF 4 (UInt32.add L 4) 4 0).2, icAdd ic 1⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv


/-- `movl $0xfe, %esi ; xorl %edi, %edi ; nop` ×10 (to the loop head) -/
theorem smg_b6 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 344)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x10397f, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, 254, (logicF 4 0).1, 0x103990, efl (logicF 4 0).2,
        icAdd ic 12⟩) := by
  refine run_of_runI (k := 12) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

set_option exec.addrSub true in
/-- `movl (%esp), %ecx ; movl %esi, %edx ; calll fe_tobytes` -/
theorem smg_b10 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L out : UInt32) (hS : FB N.get.size L 344)
    (eax ecx edx ebx ebp esi edi fl : UInt32) (ho : rdRaw N.get (UInt32.add L 8) 4 = out) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x103b1e, efl fl, icAdd ic 0⟩)
      (St.m ⟨(stF N L 344 4 0x103b28 hS (by decide)).get, eax, out, esi, ebx, UInt32.add L 4, ebp, esi, edi,
        0x101c30, efl fl, icAdd ic 3⟩) := by
  subst ho
  refine run_of_runI (k := 3) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

end Solutions.OpensslX25519.I
