import Ssl.Harness
/-!
# The machine of a call in progress

`St` is the part of the machine a flat ring-0 call changes: memory, the general registers, EIP,
EFLAGS and the instruction count. `St.m` is the machine with everything else as `Ssl.entry` sets it,
and `Ssl.entry` is `St.m` of the caller's state (`entry_eq`).
-/
namespace Solutions.Logic
open X86 Ssl

structure St where
  mem : ByteArray
  eax : UInt32
  ecx : UInt32
  edx : UInt32
  ebx : UInt32
  esp : UInt32
  ebp : UInt32
  esi : UInt32
  edi : UInt32
  eip : UInt32
  fl : UInt32
  ic : UInt64

def St.m (s : St) : Machine :=
  { mem := s.mem, icount := s.ic
    cpu := { eip := s.eip, esp := s.esp, cs := flatSeg 0x08 0xC09B, ds := flatSeg 0x10 0xC093,
             es := flatSeg 0x10 0xC093, ss := flatSeg 0x10 0xC093, fs := flatSeg 0x10 0xC093,
             gs := flatSeg 0x10 0xC093
             eax := s.eax, ecx := s.ecx, edx := s.edx, ebx := s.ebx
             esi := s.esi, edi := s.edi, ebp := s.ebp
             cr0 := CR0.PE ||| CR0.ET, eflags := s.fl } }

theorem entry_eq (mem : ByteArray) (r : Ssl.Regs) (eip esp : UInt32) :
    entry mem r eip esp = St.m ⟨mem, r.eax, r.ecx, r.edx, r.ebx, esp, r.ebp, r.esi, r.edi, eip,
      2 ||| (r.flags &&& Flag.arith), 0⟩ := rfl

end Solutions.Logic
