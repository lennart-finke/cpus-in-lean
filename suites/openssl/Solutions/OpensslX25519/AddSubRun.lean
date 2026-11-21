import Solutions.Exec.Step
import Solutions.Exec.Dispatch
import Solutions.OpensslX25519.Call
/-!
# The runs of `fe_add` and `fe_sub`, in pieces

Each piece is a few instructions run by `cbv` from a machine whose memory is an arbitrary `XMem`
(so that loads stay `rdRaw N.get a 4`, with no earlier stores to look through): the prologue
(`push %esi; movl 8(%esp), %eax`), one piece per limb (load, add or subtract, store) and the
epilogue (`pop %esi; ret`). The statements are generated from the disassembly; every piece is
proved by `cbv`.
-/
namespace Solutions.OpensslX25519
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

attribute [local cbv_opaque] Image.bytes


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem add_pro (N : XMem) (eax ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem (UInt32.sub sp 4)) :
    runOk img 2 (St.m ⟨N.get, eax, h, fp, ebx, sp, ebp, esi, edi, 0x100510, efl f, 0⟩) =
      some (St.m ⟨(CodeMem.wr4 N (UInt32.sub sp 4) esi ok).get,
        rdRaw N.get (UInt32.add (UInt32.sub sp 4) 8) 4, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi,
        0x100515, efl f, 2⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem add_limb0 (N : XMem) (ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem h) :
    runOk img 3 (St.m ⟨N.get, gp, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x100515, efl f, 2⟩) =
      some (St.m ⟨(CodeMem.wr4 N h (addF 4 (rdRaw N.get gp 4) (rdRaw N.get fp 4) 0).1 ok).get,
        gp, h, fp, ebx, UInt32.sub sp 4, ebp, (addF 4 (rdRaw N.get gp 4) (rdRaw N.get fp 4) 0).1, edi, 0x10051b, efl (addF 4 (rdRaw N.get gp 4) (rdRaw N.get fp 4) 0).2, 5⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem add_limb1 (N : XMem) (ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem (UInt32.add h 4)) :
    runOk img 3 (St.m ⟨N.get, gp, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x10051b, efl f, 5⟩) =
      some (St.m ⟨(CodeMem.wr4 N (UInt32.add h 4) (addF 4 (rdRaw N.get (UInt32.add gp 4) 4) (rdRaw N.get (UInt32.add fp 4) 4) 0).1 ok).get,
        gp, h, fp, ebx, UInt32.sub sp 4, ebp, (addF 4 (rdRaw N.get (UInt32.add gp 4) 4) (rdRaw N.get (UInt32.add fp 4) 4) 0).1, edi, 0x100524, efl (addF 4 (rdRaw N.get (UInt32.add gp 4) 4) (rdRaw N.get (UInt32.add fp 4) 4) 0).2, 8⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem add_limb2 (N : XMem) (ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem (UInt32.add h 8)) :
    runOk img 3 (St.m ⟨N.get, gp, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x100524, efl f, 8⟩) =
      some (St.m ⟨(CodeMem.wr4 N (UInt32.add h 8) (addF 4 (rdRaw N.get (UInt32.add gp 8) 4) (rdRaw N.get (UInt32.add fp 8) 4) 0).1 ok).get,
        gp, h, fp, ebx, UInt32.sub sp 4, ebp, (addF 4 (rdRaw N.get (UInt32.add gp 8) 4) (rdRaw N.get (UInt32.add fp 8) 4) 0).1, edi, 0x10052d, efl (addF 4 (rdRaw N.get (UInt32.add gp 8) 4) (rdRaw N.get (UInt32.add fp 8) 4) 0).2, 11⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem add_limb3 (N : XMem) (ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem (UInt32.add h 12)) :
    runOk img 3 (St.m ⟨N.get, gp, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x10052d, efl f, 11⟩) =
      some (St.m ⟨(CodeMem.wr4 N (UInt32.add h 12) (addF 4 (rdRaw N.get (UInt32.add gp 12) 4) (rdRaw N.get (UInt32.add fp 12) 4) 0).1 ok).get,
        gp, h, fp, ebx, UInt32.sub sp 4, ebp, (addF 4 (rdRaw N.get (UInt32.add gp 12) 4) (rdRaw N.get (UInt32.add fp 12) 4) 0).1, edi, 0x100536, efl (addF 4 (rdRaw N.get (UInt32.add gp 12) 4) (rdRaw N.get (UInt32.add fp 12) 4) 0).2, 14⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem add_limb4 (N : XMem) (ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem (UInt32.add h 16)) :
    runOk img 3 (St.m ⟨N.get, gp, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x100536, efl f, 14⟩) =
      some (St.m ⟨(CodeMem.wr4 N (UInt32.add h 16) (addF 4 (rdRaw N.get (UInt32.add gp 16) 4) (rdRaw N.get (UInt32.add fp 16) 4) 0).1 ok).get,
        gp, h, fp, ebx, UInt32.sub sp 4, ebp, (addF 4 (rdRaw N.get (UInt32.add gp 16) 4) (rdRaw N.get (UInt32.add fp 16) 4) 0).1, edi, 0x10053f, efl (addF 4 (rdRaw N.get (UInt32.add gp 16) 4) (rdRaw N.get (UInt32.add fp 16) 4) 0).2, 17⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem add_limb5 (N : XMem) (ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem (UInt32.add h 20)) :
    runOk img 3 (St.m ⟨N.get, gp, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x10053f, efl f, 17⟩) =
      some (St.m ⟨(CodeMem.wr4 N (UInt32.add h 20) (addF 4 (rdRaw N.get (UInt32.add gp 20) 4) (rdRaw N.get (UInt32.add fp 20) 4) 0).1 ok).get,
        gp, h, fp, ebx, UInt32.sub sp 4, ebp, (addF 4 (rdRaw N.get (UInt32.add gp 20) 4) (rdRaw N.get (UInt32.add fp 20) 4) 0).1, edi, 0x100548, efl (addF 4 (rdRaw N.get (UInt32.add gp 20) 4) (rdRaw N.get (UInt32.add fp 20) 4) 0).2, 20⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem add_limb6 (N : XMem) (ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem (UInt32.add h 24)) :
    runOk img 3 (St.m ⟨N.get, gp, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x100548, efl f, 20⟩) =
      some (St.m ⟨(CodeMem.wr4 N (UInt32.add h 24) (addF 4 (rdRaw N.get (UInt32.add gp 24) 4) (rdRaw N.get (UInt32.add fp 24) 4) 0).1 ok).get,
        gp, h, fp, ebx, UInt32.sub sp 4, ebp, (addF 4 (rdRaw N.get (UInt32.add gp 24) 4) (rdRaw N.get (UInt32.add fp 24) 4) 0).1, edi, 0x100551, efl (addF 4 (rdRaw N.get (UInt32.add gp 24) 4) (rdRaw N.get (UInt32.add fp 24) 4) 0).2, 23⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem add_limb7 (N : XMem) (ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem (UInt32.add h 28)) :
    runOk img 3 (St.m ⟨N.get, gp, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x100551, efl f, 23⟩) =
      some (St.m ⟨(CodeMem.wr4 N (UInt32.add h 28) (addF 4 (rdRaw N.get (UInt32.add gp 28) 4) (rdRaw N.get (UInt32.add fp 28) 4) 0).1 ok).get,
        gp, h, fp, ebx, UInt32.sub sp 4, ebp, (addF 4 (rdRaw N.get (UInt32.add gp 28) 4) (rdRaw N.get (UInt32.add fp 28) 4) 0).1, edi, 0x10055a, efl (addF 4 (rdRaw N.get (UInt32.add gp 28) 4) (rdRaw N.get (UInt32.add fp 28) 4) 0).2, 26⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem add_limb8 (N : XMem) (ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem (UInt32.add h 32)) :
    runOk img 3 (St.m ⟨N.get, gp, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x10055a, efl f, 26⟩) =
      some (St.m ⟨(CodeMem.wr4 N (UInt32.add h 32) (addF 4 (rdRaw N.get (UInt32.add gp 32) 4) (rdRaw N.get (UInt32.add fp 32) 4) 0).1 ok).get,
        gp, h, fp, ebx, UInt32.sub sp 4, ebp, (addF 4 (rdRaw N.get (UInt32.add gp 32) 4) (rdRaw N.get (UInt32.add fp 32) 4) 0).1, edi, 0x100563, efl (addF 4 (rdRaw N.get (UInt32.add gp 32) 4) (rdRaw N.get (UInt32.add fp 32) 4) 0).2, 29⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem add_limb9 (N : XMem) (ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem (UInt32.add h 36)) :
    runOk img 3 (St.m ⟨N.get, gp, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x100563, efl f, 29⟩) =
      some (St.m ⟨(CodeMem.wr4 N (UInt32.add h 36) (addF 4 (rdRaw N.get (UInt32.add gp 36) 4) (rdRaw N.get (UInt32.add fp 36) 4) 0).1 ok).get,
        (addF 4 (rdRaw N.get (UInt32.add gp 36) 4) (rdRaw N.get (UInt32.add fp 36) 4) 0).1, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x10056c, efl (addF 4 (rdRaw N.get (UInt32.add gp 36) 4) (rdRaw N.get (UInt32.add fp 36) 4) 0).2, 32⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem add_epi (N : XMem) (eax ebx edx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat) :
    runOk img 2 (St.m ⟨N.get, eax, h, edx, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x10056c, efl f, 32⟩) =
      some (St.m ⟨N.get, eax, h, edx, ebx, UInt32.add (UInt32.sub sp 4) 8, ebp,
        rdRaw N.get (UInt32.sub sp 4) 4, edi, rdRaw N.get (UInt32.add (UInt32.sub sp 4) 4) 4, efl f, 34⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem sub_pro (N : XMem) (eax ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem (UInt32.sub sp 4)) :
    runOk img 2 (St.m ⟨N.get, eax, h, fp, ebx, sp, ebp, esi, edi, 0x100570, efl f, 0⟩) =
      some (St.m ⟨(CodeMem.wr4 N (UInt32.sub sp 4) esi ok).get,
        rdRaw N.get (UInt32.add (UInt32.sub sp 4) 8) 4, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi,
        0x100575, efl f, 2⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem sub_limb0 (N : XMem) (ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem h) :
    runOk img 3 (St.m ⟨N.get, gp, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x100575, efl f, 2⟩) =
      some (St.m ⟨(CodeMem.wr4 N h (subF 4 (rdRaw N.get fp 4) (rdRaw N.get gp 4) 0).1 ok).get,
        gp, h, fp, ebx, UInt32.sub sp 4, ebp, (subF 4 (rdRaw N.get fp 4) (rdRaw N.get gp 4) 0).1, edi, 0x10057b, efl (subF 4 (rdRaw N.get fp 4) (rdRaw N.get gp 4) 0).2, 5⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem sub_limb1 (N : XMem) (ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem (UInt32.add h 4)) :
    runOk img 3 (St.m ⟨N.get, gp, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x10057b, efl f, 5⟩) =
      some (St.m ⟨(CodeMem.wr4 N (UInt32.add h 4) (subF 4 (rdRaw N.get (UInt32.add fp 4) 4) (rdRaw N.get (UInt32.add gp 4) 4) 0).1 ok).get,
        gp, h, fp, ebx, UInt32.sub sp 4, ebp, (subF 4 (rdRaw N.get (UInt32.add fp 4) 4) (rdRaw N.get (UInt32.add gp 4) 4) 0).1, edi, 0x100584, efl (subF 4 (rdRaw N.get (UInt32.add fp 4) 4) (rdRaw N.get (UInt32.add gp 4) 4) 0).2, 8⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem sub_limb2 (N : XMem) (ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem (UInt32.add h 8)) :
    runOk img 3 (St.m ⟨N.get, gp, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x100584, efl f, 8⟩) =
      some (St.m ⟨(CodeMem.wr4 N (UInt32.add h 8) (subF 4 (rdRaw N.get (UInt32.add fp 8) 4) (rdRaw N.get (UInt32.add gp 8) 4) 0).1 ok).get,
        gp, h, fp, ebx, UInt32.sub sp 4, ebp, (subF 4 (rdRaw N.get (UInt32.add fp 8) 4) (rdRaw N.get (UInt32.add gp 8) 4) 0).1, edi, 0x10058d, efl (subF 4 (rdRaw N.get (UInt32.add fp 8) 4) (rdRaw N.get (UInt32.add gp 8) 4) 0).2, 11⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem sub_limb3 (N : XMem) (ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem (UInt32.add h 12)) :
    runOk img 3 (St.m ⟨N.get, gp, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x10058d, efl f, 11⟩) =
      some (St.m ⟨(CodeMem.wr4 N (UInt32.add h 12) (subF 4 (rdRaw N.get (UInt32.add fp 12) 4) (rdRaw N.get (UInt32.add gp 12) 4) 0).1 ok).get,
        gp, h, fp, ebx, UInt32.sub sp 4, ebp, (subF 4 (rdRaw N.get (UInt32.add fp 12) 4) (rdRaw N.get (UInt32.add gp 12) 4) 0).1, edi, 0x100596, efl (subF 4 (rdRaw N.get (UInt32.add fp 12) 4) (rdRaw N.get (UInt32.add gp 12) 4) 0).2, 14⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem sub_limb4 (N : XMem) (ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem (UInt32.add h 16)) :
    runOk img 3 (St.m ⟨N.get, gp, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x100596, efl f, 14⟩) =
      some (St.m ⟨(CodeMem.wr4 N (UInt32.add h 16) (subF 4 (rdRaw N.get (UInt32.add fp 16) 4) (rdRaw N.get (UInt32.add gp 16) 4) 0).1 ok).get,
        gp, h, fp, ebx, UInt32.sub sp 4, ebp, (subF 4 (rdRaw N.get (UInt32.add fp 16) 4) (rdRaw N.get (UInt32.add gp 16) 4) 0).1, edi, 0x10059f, efl (subF 4 (rdRaw N.get (UInt32.add fp 16) 4) (rdRaw N.get (UInt32.add gp 16) 4) 0).2, 17⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem sub_limb5 (N : XMem) (ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem (UInt32.add h 20)) :
    runOk img 3 (St.m ⟨N.get, gp, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x10059f, efl f, 17⟩) =
      some (St.m ⟨(CodeMem.wr4 N (UInt32.add h 20) (subF 4 (rdRaw N.get (UInt32.add fp 20) 4) (rdRaw N.get (UInt32.add gp 20) 4) 0).1 ok).get,
        gp, h, fp, ebx, UInt32.sub sp 4, ebp, (subF 4 (rdRaw N.get (UInt32.add fp 20) 4) (rdRaw N.get (UInt32.add gp 20) 4) 0).1, edi, 0x1005a8, efl (subF 4 (rdRaw N.get (UInt32.add fp 20) 4) (rdRaw N.get (UInt32.add gp 20) 4) 0).2, 20⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem sub_limb6 (N : XMem) (ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem (UInt32.add h 24)) :
    runOk img 3 (St.m ⟨N.get, gp, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x1005a8, efl f, 20⟩) =
      some (St.m ⟨(CodeMem.wr4 N (UInt32.add h 24) (subF 4 (rdRaw N.get (UInt32.add fp 24) 4) (rdRaw N.get (UInt32.add gp 24) 4) 0).1 ok).get,
        gp, h, fp, ebx, UInt32.sub sp 4, ebp, (subF 4 (rdRaw N.get (UInt32.add fp 24) 4) (rdRaw N.get (UInt32.add gp 24) 4) 0).1, edi, 0x1005b1, efl (subF 4 (rdRaw N.get (UInt32.add fp 24) 4) (rdRaw N.get (UInt32.add gp 24) 4) 0).2, 23⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem sub_limb7 (N : XMem) (ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem (UInt32.add h 28)) :
    runOk img 3 (St.m ⟨N.get, gp, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x1005b1, efl f, 23⟩) =
      some (St.m ⟨(CodeMem.wr4 N (UInt32.add h 28) (subF 4 (rdRaw N.get (UInt32.add fp 28) 4) (rdRaw N.get (UInt32.add gp 28) 4) 0).1 ok).get,
        gp, h, fp, ebx, UInt32.sub sp 4, ebp, (subF 4 (rdRaw N.get (UInt32.add fp 28) 4) (rdRaw N.get (UInt32.add gp 28) 4) 0).1, edi, 0x1005ba, efl (subF 4 (rdRaw N.get (UInt32.add fp 28) 4) (rdRaw N.get (UInt32.add gp 28) 4) 0).2, 26⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem sub_limb8 (N : XMem) (ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem (UInt32.add h 32)) :
    runOk img 3 (St.m ⟨N.get, gp, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x1005ba, efl f, 26⟩) =
      some (St.m ⟨(CodeMem.wr4 N (UInt32.add h 32) (subF 4 (rdRaw N.get (UInt32.add fp 32) 4) (rdRaw N.get (UInt32.add gp 32) 4) 0).1 ok).get,
        gp, h, fp, ebx, UInt32.sub sp 4, ebp, (subF 4 (rdRaw N.get (UInt32.add fp 32) 4) (rdRaw N.get (UInt32.add gp 32) 4) 0).1, edi, 0x1005c3, efl (subF 4 (rdRaw N.get (UInt32.add fp 32) 4) (rdRaw N.get (UInt32.add gp 32) 4) 0).2, 29⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem sub_limb9 (N : XMem) (ebx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat)
    (ok : StoreOk Image.base Image.size N.mem (UInt32.add h 36)) :
    runOk img 3 (St.m ⟨N.get, gp, h, fp, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x1005c3, efl f, 29⟩) =
      some (St.m ⟨(CodeMem.wr4 N (UInt32.add h 36) (subF 4 (rdRaw N.get (UInt32.add fp 36) 4) (rdRaw N.get (UInt32.add gp 36) 4) 0).1 ok).get,
        gp, h, (subF 4 (rdRaw N.get (UInt32.add fp 36) 4) (rdRaw N.get (UInt32.add gp 36) 4) 0).1, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x1005cc, efl (subF 4 (rdRaw N.get (UInt32.add fp 36) 4) (rdRaw N.get (UInt32.add gp 36) 4) 0).2, 32⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option cbv.maxSteps 50000000 in
theorem sub_epi (N : XMem) (eax ebx edx sp ebp esi edi f h fp gp : UInt32) (hF : FieldFacts N.get.size sp.toNat h.toNat fp.toNat gp.toNat) :
    runOk img 2 (St.m ⟨N.get, eax, h, edx, ebx, UInt32.sub sp 4, ebp, esi, edi, 0x1005cc, efl f, 32⟩) =
      some (St.m ⟨N.get, eax, h, edx, ebx, UInt32.add (UInt32.sub sp 4) 8, ebp,
        rdRaw N.get (UInt32.sub sp 4) 4, edi, rdRaw N.get (UInt32.add (UInt32.sub sp 4) 4) 4, efl f, 34⟩) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hF
  cbv

end Solutions.OpensslX25519
