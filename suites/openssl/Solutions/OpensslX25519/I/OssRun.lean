import Solutions.OpensslX25519.I.TbBase
import Solutions.OpensslX25519.I.LadRun1
/-!
# `ossl_x25519` (`0x100420`): its instructions around the two calls

Frame base `Lb = sp - 388` with `FB Lb 404` (`[sp - 388, sp + 16)`): entry esp `Lb + 388` (the sentinel return
address), the arguments `out`, `kp`, `up` at `Lb + 392 … Lb + 400`; `pushl %esi` to `Lb + 384`; the call of
`x25519_scalar_mult` (a `jmp` to `x25519_scalar_mult_generic`) with `up` at `Lb + 380` and its return address at
`Lb + 376`; `CRYPTO_memcmp(kZeros, out, 32)` with its arguments at `Lb + 372 … Lb + 380` and return address at
`Lb + 368`; the result `setne` in two cases (the zero flag of `testl %eax, %eax` as a hypothesis, for
`Solutions.Exec.Branch`). Prover R; the forms were read off `cbv`.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast
  Solutions.Exec.Byte Solutions.Exec.Shift Solutions.Exec.Branch

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

set_option exec.addrSub true in
/-- `pushl %esi ; movl 0x8(%esp), %esi ; movl 0xc(%esp), %edx ; movl %esi, %ecx ; pushl 0x10(%esp) ;
calll x25519_scalar_mult ; jmp x25519_scalar_mult_generic` -/
theorem oss_o1 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (Lb : UInt32) (hS : FB N.get.size Lb 404)
    (eax ecx edx ebx ebp esi edi fl out kp up : UInt32) (h1 : rdRaw N.get (UInt32.add Lb 392) 4 = out)
    (h2 : rdRaw N.get (UInt32.add Lb 396) 4 = kp) (h3 : rdRaw N.get (UInt32.add Lb 400) 4 = up) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 388, ebp, esi, edi, 0x100420, efl fl, icAdd ic 0⟩)
      (St.m ⟨(stF (stF (stF N Lb 404 384 esi hS (by decide)) Lb 404 380 up stF_FB (by decide)) Lb 404 376 0x100434
          stF_FB (by decide)).get, eax, out, kp, ebx, UInt32.add Lb 376, ebp, out, edi, 0x103910, efl fl,
        icAdd ic 7⟩) := by
  subst h1 h2 h3
  refine run_of_runI (k := 7) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `addl $0x4, %esp` -/
theorem oss_o2 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (Lb : UInt32) (hS : FB N.get.size Lb 404)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 380, ebp, esi, edi, 0x100434, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 384, ebp, esi, edi, 0x100437,
        efl (addF 4 (UInt32.add Lb 380) 4 0).2, icAdd ic 1⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

set_option exec.addrSub true in
/-- `pushl $0x20 ; pushl %esi ; pushl $0x103f8c ; calll CRYPTO_memcmp` -/
theorem oss_o3 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (Lb : UInt32) (hS : FB N.get.size Lb 404)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 384, ebp, esi, edi, 0x100437, efl fl, icAdd ic 0⟩)
      (St.m ⟨(stF (stF (stF (stF N Lb 404 380 32 hS (by decide)) Lb 404 376 esi stF_FB (by decide)) Lb 404 372
          0x103f8c stF_FB (by decide)) Lb 404 368 0x100444 stF_FB (by decide)).get, eax, ecx, edx, ebx,
        UInt32.add Lb 368, ebp, esi, edi, 0x103ea0, efl fl, icAdd ic 4⟩) := by
  refine run_of_runI (k := 4) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `addl $0xc, %esp` -/
theorem oss_o4 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (Lb : UInt32) (hS : FB N.get.size Lb 404)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 372, ebp, esi, edi, 0x100444, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 384, ebp, esi, edi, 0x100447,
        efl (addF 4 (UInt32.add Lb 372) 12 0).2, icAdd ic 1⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `xorl %ecx, %ecx ; testl %eax, %eax ; setne %cl ; movl %ecx, %eax ; popl %esi ; retl`, `eax ≠ 0` -/
theorem oss_o5n (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (Lb : UInt32) (hS : FB N.get.size Lb 404)
    (eax ecx edx ebx ebp esi edi fl esi0 ret : UInt32)
    (hz : UInt32.land (efl (logicF 4 (UInt32.land eax eax)).2) 64 = 0)
    (l1 : rdRaw N.get (UInt32.add Lb 384) 4 = esi0) (l2 : rdRaw N.get (UInt32.add Lb 388) 4 = ret) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 384, ebp, esi, edi, 0x100447, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, UInt32.lor (UInt32.land (logicF 4 0).1 4294967040) 1,
        UInt32.lor (UInt32.land (logicF 4 0).1 4294967040) 1, edx, ebx, UInt32.add Lb 392, ebp, esi0, edi, ret,
        efl (logicF 4 (UInt32.land eax eax)).2, icAdd ic 6⟩) := by
  subst l1 l2
  refine run_of_runI (k := 6) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- As `oss_o5n`, `eax = 0` -/
theorem oss_o5z (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (Lb : UInt32) (hS : FB N.get.size Lb 404)
    (eax ecx edx ebx ebp esi edi fl esi0 ret : UInt32)
    (hz : UInt32.land (efl (logicF 4 (UInt32.land eax eax)).2) 64 = 64)
    (l1 : rdRaw N.get (UInt32.add Lb 384) 4 = esi0) (l2 : rdRaw N.get (UInt32.add Lb 388) 4 = ret) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 384, ebp, esi, edi, 0x100447, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, UInt32.lor (UInt32.land (logicF 4 0).1 4294967040) 0,
        UInt32.lor (UInt32.land (logicF 4 0).1 4294967040) 0, edx, ebx, UInt32.add Lb 392, ebp, esi0, edi, ret,
        efl (logicF 4 (UInt32.land eax eax)).2, icAdd ic 6⟩) := by
  subst l1 l2
  refine run_of_runI (k := 6) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

end Solutions.OpensslX25519.I
