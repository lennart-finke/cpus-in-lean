import Solutions.OpensslX25519.I.TbBase
import Solutions.OpensslX25519.I.LadRun1
/-!
# `x25519_scalar_mult_generic` (`0x103910`): prologue, clamp, cleanse call, epilogue

Frame base `Lb = L - 32` with `FB Lb 384` (`[L - 32, L + 352)`, where `[L, L + 344)` is the `CSt` region of the
ladder): entry esp `Lb + 376` (return address there, the u pointer at `Lb + 380`); the pushes put `ebp`, `ebx`,
`edi`, `esi` at `Lb + 372 … Lb + 360`; `subl $0x140` sets esp to `Lb + 40 = L + 8`. Written from
`gen/smgrun1.lean.in` by `gen/gensmg.py` (prover R); the forms of the byte instructions were read off `cbv`.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast
  Solutions.Exec.Byte Solutions.Exec.Shift

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

set_option exec.addrSub true in
/-- `pushl %ebp ; pushl %ebx ; pushl %edi ; pushl %esi` -/
theorem smg_pro (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (G : XMem) (Lb : UInt32) (hS : FB G.get.size Lb 384)
    (l : List (Nat × UInt32)) (hF : Frame G Lb 384 l) (eax ecx edx ebx ebp esi edi f : UInt32) :
    ∃ N' : XMem, Run img (St.m ⟨G.get, eax, ecx, edx, ebx, UInt32.add Lb 376, ebp, esi, edi, 0x103910, efl f,
        icAdd ic 0⟩)
      (St.m ⟨N'.get, eax, ecx, edx, ebx, UInt32.add Lb 360, ebp, esi, edi, 0x103914, efl f, icAdd ic 4⟩) ∧
      Frame N' Lb 384 ((360, esi) :: (364, edi) :: (368, ebx) :: (372, ebp) :: l) ∧
      Pres G N' (OutF Lb 376) := by
  refine ⟨stF (stF (stF (stF G Lb 384 372 ebp hS (by decide)) Lb 384 368 ebx stF_FB (by decide))
    Lb 384 364 edi stF_FB (by decide)) Lb 384 360 esi stF_FB (by decide), run_of_runI (k := 4) ?_ (icB hic (by decide)),
    (((hF.wrF 372 rfl rfl).wrF 368 rfl rfl).wrF 364 rfl rfl).wrF 360 rfl rfl,
    ((((Pres.refl G _).wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide)⟩
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF
  cbv

theorem smg_esp_sub (Lb : UInt32) : (subF 4 (UInt32.add Lb 360) 320 0).1 = UInt32.add Lb 40 := by
  rw [subF_fst]
  show Lb + 360 - 320 = Lb + 40
  rw [show (360 : UInt32) = 40 + 320 from rfl, ← UInt32.add_assoc, UInt32.add_sub_cancel]

/-- `subl $0x140, %esp` -/
theorem smg_sub (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (Lb : UInt32) (hS : FB N.get.size Lb 384)
    (eax ecx edx ebx ebp esi edi f : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 360, ebp, esi, edi, 0x103914, efl f, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 40, ebp, esi, edi, 0x10391a,
        efl (subF 4 (UInt32.add Lb 360) 320 0).2, icAdd ic 1⟩) := by
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  have h : runI img 1 (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 360, ebp, esi, edi, 0x103914, efl f,
      icAdd ic 0⟩) =
      some (St.m ⟨N.get, eax, ecx, edx, ebx, (subF 4 (UInt32.add Lb 360) 320 0).1, ebp, esi, edi, 0x10391a,
        efl (subF 4 (UInt32.add Lb 360) 320 0).2, icAdd ic 1⟩) := by
    cbv
  rw [smg_esp_sub] at h
  exact run_of_runI h (icB hic (by decide))

/-- `movl %ecx, (%esp)` (the output pointer to `L + 8`) -/
theorem smg_st (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (Lb : UInt32) (hS : FB N.get.size Lb 384)
    (eax ecx edx ebx ebp esi edi f : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 40, ebp, esi, edi, 0x10391a, efl f, icAdd ic 0⟩)
      (St.m ⟨(stF N Lb 384 40 ecx hS (by decide)).get, eax, ecx, edx, ebx, UInt32.add Lb 40, ebp, esi, edi,
        0x10391d, efl f, icAdd ic 1⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

set_option exec.addrSub true in
/-- `movl 0x154(%esp), %esi ; leal 0x8(%esp), %eax ; pushl $0x20 ; pushl %edx ; pushl %eax ; calll memcpy` -/
theorem smg_mc (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (Lb up : UInt32) (hS : FB N.get.size Lb 384)
    (eax ecx edx ebx ebp esi edi f : UInt32) (hu : rdRaw N.get (UInt32.add Lb 380) 4 = up) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 40, ebp, esi, edi, 0x10391d, efl f, icAdd ic 0⟩)
      (St.m ⟨(stF (stF (stF (stF N Lb 384 36 32 hS (by decide)) Lb 384 32 edx stF_FB (by decide)) Lb 384 28
          (UInt32.add Lb 48) stF_FB (by decide)) Lb 384 24 0x103931 stF_FB (by decide)).get,
        UInt32.add Lb 48, ecx, edx, ebx, UInt32.add Lb 24, ebp, up, edi, 0x103ee0, efl f, icAdd ic 6⟩) := by
  subst hu
  refine run_of_runI (k := 6) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `addl $0xc, %esp` -/
theorem smg_add (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (Lb : UInt32) (hS : FB N.get.size Lb 384)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 28, ebp, esi, edi, 0x103931, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 40, ebp, esi, edi, 0x103934,
        efl (addF 4 (UInt32.add Lb 28) 12 0).2, icAdd ic 1⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `andb $-0x8, 0x8(%esp)` (clamp byte 0 of the scalar copy at `L + 16`) -/
theorem smg_c1 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (Lb : UInt32) (hS : FB N.get.size Lb 384)
    (eax ecx edx ebx ebp esi edi fl : UInt32) (ok : StoreOk1 Image.base Image.size N.mem (UInt32.add Lb 48)) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 40, ebp, esi, edi, 0x103934, efl fl, icAdd ic 0⟩)
      (St.m ⟨(CodeMem.wr1 N (UInt32.add Lb 48) (logicF 1 (UInt32.land (rdRaw N.get (UInt32.add Lb 48) 1) 248)).1
          ok).get, eax, ecx, edx, ebx, UInt32.add Lb 40, ebp, esi, edi, 0x103939,
        efl (logicF 1 (UInt32.land (rdRaw N.get (UInt32.add Lb 48) 1) 248)).2, icAdd ic 1⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `movzbl 0x27(%esp), %eax ; andb $0x3f, %al` (byte 31) -/
theorem smg_c2 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (Lb : UInt32) (hS : FB N.get.size Lb 384)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 40, ebp, esi, edi, 0x103939, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, UInt32.lor (UInt32.land (rdRaw N.get (UInt32.add Lb 79) 1) 4294967040)
          (UInt32.land (logicF 1 (UInt32.land (UInt32.land (rdRaw N.get (UInt32.add Lb 79) 1) 255) 63)).1 255),
        ecx, edx, ebx, UInt32.add Lb 40, ebp, esi, edi, 0x103940,
        efl (logicF 1 (UInt32.land (UInt32.land (rdRaw N.get (UInt32.add Lb 79) 1) 255) 63)).2, icAdd ic 2⟩) := by
  refine run_of_runI (k := 2) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `orb $0x40, %al` -/
theorem smg_c3 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (Lb : UInt32) (hS : FB N.get.size Lb 384)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 40, ebp, esi, edi, 0x103940, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, UInt32.lor (UInt32.land eax 4294967040) (UInt32.land (logicF 1 (UInt32.lor (UInt32.land eax 255) 64)).1 255),
        ecx, edx, ebx, UInt32.add Lb 40, ebp, esi, edi, 0x103942,
        efl (logicF 1 (UInt32.lor (UInt32.land eax 255) 64)).2, icAdd ic 1⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `movb %al, 0x27(%esp)` -/
theorem smg_c4 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (Lb : UInt32) (hS : FB N.get.size Lb 384)
    (eax ecx edx ebx ebp esi edi fl : UInt32) (ok : StoreOk1 Image.base Image.size N.mem (UInt32.add Lb 79)) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 40, ebp, esi, edi, 0x103942, efl fl, icAdd ic 0⟩)
      (St.m ⟨(CodeMem.wr1 N (UInt32.add Lb 79) (UInt32.land eax 255) ok).get, eax, ecx, edx, ebx, UInt32.add Lb 40,
        ebp, esi, edi, 0x103946, efl fl, icAdd ic 1⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

set_option exec.addrSub true in
/-- `pushl $0x20 ; leal 0xc(%esp), %eax ; pushl %eax ; calll OPENSSL_cleanse` -/
theorem smg_cl (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (Lb : UInt32) (hS : FB N.get.size Lb 384)
    (eax ecx edx ebx ebp esi edi f : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 40, ebp, esi, edi, 0x103b28, efl f, icAdd ic 0⟩)
      (St.m ⟨(stF (stF (stF N Lb 384 36 32 hS (by decide)) Lb 384 32 (UInt32.add Lb 48) stF_FB (by decide)) Lb 384 28
          0x103b34 stF_FB (by decide)).get,
        UInt32.add Lb 48, ecx, edx, ebx, UInt32.add Lb 28, ebp, esi, edi, 0x103e80, efl f, icAdd ic 4⟩) := by
  refine run_of_runI (k := 4) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `addl $0x148, %esp` -/
theorem smg_add2 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (Lb : UInt32) (hS : FB N.get.size Lb 384)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 32, ebp, esi, edi, 0x103b34, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 360, ebp, esi, edi, 0x103b3a,
        efl (addF 4 (UInt32.add Lb 32) 328 0).2, icAdd ic 1⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `popl %esi ; popl %edi ; popl %ebx ; popl %ebp ; retl` -/
theorem smg_epi (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (Lb : UInt32) (hS : FB N.get.size Lb 384)
    (eax ecx edx ebx ebp esi edi f esi0 edi0 ebx0 ebp0 ret : UInt32)
    (l1 : rdRaw N.get (UInt32.add Lb 360) 4 = esi0) (l2 : rdRaw N.get (UInt32.add Lb 364) 4 = edi0)
    (l3 : rdRaw N.get (UInt32.add Lb 368) 4 = ebx0) (l4 : rdRaw N.get (UInt32.add Lb 372) 4 = ebp0)
    (l5 : rdRaw N.get (UInt32.add Lb 376) 4 = ret) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add Lb 360, ebp, esi, edi, 0x103b3a, efl f, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx0, UInt32.add Lb 380, ebp0, esi0, edi0, ret, efl f, icAdd ic 5⟩) := by
  subst l1 l2 l3 l4 l5
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  refine run_of_runI (k := 5) ?_ (icB hic (by decide))
  cbv

end Solutions.OpensslX25519.I
