import Solutions.OpensslChacha20.Hyp
/-!
# The two byte loops: `memcpy` and the keystream xor

One iteration each, continuing (`_cont`) or leaving the loop (`_exit`).

`memcpy` (`0x100420`): `movzbl (%edx,%esi),%ebx; movb %bl,(%eax,%esi); incl %esi; cmpl %esi,%ecx; jne`.

The xor loop of `ChaCha20_ctr32` (`0x1000d0`): `movzbl 0x40(%esp,%eax),%ecx; xorb (%ebp,%eax),%cl;
movb %cl,(%esi,%eax); incl %eax; cmpl %eax,%edi; jne`.
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

/-- The address facts of a byte loop over `[a, a + n)`: inside memory and outside the code. -/
def ByteRegion (size : Nat) (a : UInt32) (n : Nat) : Prop :=
  a.toNat + n ≤ size ∧ (1049648 ≤ a.toNat ∨ a.toNat + n ≤ 1048576)

theorem memcpy_cont (H : CMem) (u dst src i ebx ebp edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hd : ByteRegion H.get.size dst 64) (hs : ByteRegion H.get.size src 64)
    (hi : i.toNat + 1 < 64) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, dst, 64, src, ebx, u, ebp, i, edi, 0x100420, efl f, ic⟩ =
        some ⟨H'.get, dst, 64, src, rdRaw H.get (src.add i) 1, u, ebp, i.add 1, edi, 0x100420, efl f', ic + 5⟩ ∧
      H'.get = wrBytes H.get (dst.add i) 1 (UInt32.land (rdRaw H.get (src.add i) 1) 255) := by
  obtain ⟨hd1, hd2⟩ := hd
  obtain ⟨hs1, hs2⟩ := hs
  ex_run
  exact ⟨_, _, rfl, rfl⟩

theorem memcpy_exit (H : CMem) (u dst src i ebx ebp edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hd : ByteRegion H.get.size dst 64) (hs : ByteRegion H.get.size src 64)
    (hi : i.toNat = 63) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, dst, 64, src, ebx, u, ebp, i, edi, 0x100420, efl f, ic⟩ =
        some ⟨H'.get, dst, 64, src, rdRaw H.get (src.add i) 1, u, ebp, i.add 1, edi, 0x10042c, efl f', ic + 5⟩ ∧
      H'.get = wrBytes H.get (dst.add i) 1 (UInt32.land (rdRaw H.get (src.add i) 1) 255) := by
  obtain ⟨hd1, hd2⟩ := hd
  obtain ⟨hs1, hs2⟩ := hs
  ex_run
  exact ⟨_, _, rfl, rfl⟩

/-- ECX after `xorb`, from the keystream byte `k` and the input byte `b` (as loaded). -/
def xorReg (k b : UInt32) : UInt32 :=
  UInt32.lor (UInt32.land k 4294967040) (UInt32.land (UInt32.xor (UInt32.land k 255) b) 255)

theorem xorReg_toUInt8 (k b : UInt32) : (UInt32.land (xorReg k b) 255).toUInt8 = k.toUInt8 ^^^ b.toUInt8 := by
  apply UInt8.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  show (((k &&& 4294967040) ||| (((k &&& 255) ^^^ b) &&& 255)) &&& 255).toUInt8.toBitVec.getLsbD i = _
  simp only [UInt32.toBitVec_toUInt8, UInt8.toBitVec_xor, BitVec.getLsbD_setWidth, BitVec.getLsbD_xor,
    UInt32.toBitVec_and, UInt32.toBitVec_or, UInt32.toBitVec_xor, BitVec.getLsbD_and, BitVec.getLsbD_or, hi,
    decide_true, Bool.true_and]
  have h1 : ∀ j, j < 8 → (UInt32.toBitVec 4294967040).getLsbD j = false := by decide
  have h2 : ∀ j, j < 8 → (UInt32.toBitVec 255).getLsbD j = true := by decide
  rw [h1 i hi, h2 i hi]
  simp

theorem xor_cont (H : CMem) (T i ecx edx ebx inp out n f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hT : ByteRegion H.get.size (T.add 64) 64) (hTn : T.toNat + 128 < 2 ^ 32)
    (hin : ByteRegion H.get.size inp n.toNat) (hout : ByteRegion H.get.size out n.toNat)
    (hn : n.toNat ≤ 64) (hi : i.toNat + 1 < n.toNat) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 ⟨H.get, i, ecx, edx, ebx, T, inp, out, n, 0x1000d0, efl f, ic⟩ =
        some ⟨H'.get, i.add 1, xorReg (rdRaw H.get ((T.add i).add 64) 1) (rdRaw H.get (inp.add i) 1), edx, ebx,
          T, inp, out, n, 0x1000d0, efl f', ic + 6⟩ ∧
      H'.get = wrBytes H.get (out.add i) 1
        (UInt32.land (xorReg (rdRaw H.get ((T.add i).add 64) 1) (rdRaw H.get (inp.add i) 1)) 255) := by
  obtain ⟨hT1, hT2⟩ := hT
  obtain ⟨hi1, hi2⟩ := hin
  obtain ⟨ho1, ho2⟩ := hout
  ex_run
  exact ⟨_, _, rfl, rfl⟩

theorem xor_exit (H : CMem) (T i ecx edx ebx inp out n f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hT : ByteRegion H.get.size (T.add 64) 64) (hTn : T.toNat + 128 < 2 ^ 32)
    (hin : ByteRegion H.get.size inp n.toNat) (hout : ByteRegion H.get.size out n.toNat)
    (hn : n.toNat ≤ 64) (hi : i.toNat + 1 = n.toNat) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 ⟨H.get, i, ecx, edx, ebx, T, inp, out, n, 0x1000d0, efl f, ic⟩ =
        some ⟨H'.get, i.add 1, xorReg (rdRaw H.get ((T.add i).add 64) 1) (rdRaw H.get (inp.add i) 1), edx, ebx,
          T, inp, out, n, 0x1000e1, efl f', ic + 6⟩ ∧
      H'.get = wrBytes H.get (out.add i) 1
        (UInt32.land (xorReg (rdRaw H.get ((T.add i).add 64) 1) (rdRaw H.get (inp.add i) 1)) 255) := by
  obtain ⟨hT1, hT2⟩ := hT
  obtain ⟨hi1, hi2⟩ := hin
  obtain ⟨ho1, ho2⟩ := hout
  ex_run
  exact ⟨_, _, rfl, rfl⟩

end Solutions.OpensslChacha20
