import Solutions.OpensslChacha20.Hyp
/-!
# The state of `chacha20_core`'s round loop

`RS`: the seven general registers other than ESP and the thirteen stack slots the loop uses, at
offsets `0, 4, …, 0x38` from the frame `t` (the loop counter is at `0x28`, `0x2c` and `0x38` are
scratch). `stRS M t r eip fl ic` is the machine state, `Corr M t r` says the slots of `M` hold the
slot values of `r`.
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec

structure RS where
  eax : UInt32
  ecx : UInt32
  edx : UInt32
  ebx : UInt32
  ebp : UInt32
  esi : UInt32
  edi : UInt32
  s0 : UInt32
  s4 : UInt32
  s8 : UInt32
  sc : UInt32
  s10 : UInt32
  s14 : UInt32
  s18 : UInt32
  s1c : UInt32
  s20 : UInt32
  s24 : UInt32
  s28 : UInt32
  s2c : UInt32
  s30 : UInt32
  s34 : UInt32
  s38 : UInt32

/-- The machine state with registers from `r` and stack pointer `t`. -/
def stRS (M : ByteArray) (t : UInt32) (r : RS) (eip fl : UInt32) (ic : UInt64) : St :=
  ⟨M, r.eax, r.ecx, r.edx, r.ebx, t, r.ebp, r.esi, r.edi, eip, fl, ic⟩

/-- The slots of the frame at `t` hold the slot values of `r`. -/
def Corr (M : ByteArray) (t : UInt32) (r : RS) : Prop :=
  rdRaw M t 4 = r.s0 ∧ rdRaw M (t.add 4) 4 = r.s4 ∧ rdRaw M (t.add 8) 4 = r.s8 ∧
  rdRaw M (t.add 12) 4 = r.sc ∧ rdRaw M (t.add 16) 4 = r.s10 ∧ rdRaw M (t.add 20) 4 = r.s14 ∧ rdRaw M (t.add 24) 4 = r.s18 ∧
  rdRaw M (t.add 28) 4 = r.s1c ∧ rdRaw M (t.add 32) 4 = r.s20 ∧ rdRaw M (t.add 36) 4 = r.s24 ∧ rdRaw M (t.add 40) 4 = r.s28 ∧
  rdRaw M (t.add 44) 4 = r.s2c ∧ rdRaw M (t.add 48) 4 = r.s30 ∧ rdRaw M (t.add 52) 4 = r.s34 ∧
  rdRaw M (t.add 56) 4 = r.s38

end Solutions.OpensslChacha20
