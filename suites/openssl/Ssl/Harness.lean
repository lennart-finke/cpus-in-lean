import X86
import Ssl.Bytes
/-!
# OpenSSL task call harness

Every task is a contract about one call of a function of a linked i386 image, executed by the
unchanged `X86.step` in an 8 MiB flat machine. The contracts are stated for an arbitrary caller:

* **Caller state** (`Caller`): arbitrary memory contents, arbitrary general registers, arbitrary
  arithmetic status flags and an arbitrary stack pointer. The remaining machine state is fixed by
  `entry`: ring 0, flat 4 GiB segments, protected mode without paging, interrupts disabled, the
  direction flag clear (as the calling convention requires), devices idle.
* **Well-formed call** (`Calls`): the image bytes are in memory at their link address, the return
  address (the image's `halt` sentinel) and the stack arguments are at the stack pointer, and the
  `stack` bytes below the stack pointer are available to the callee and do not overlap the image.
* **Buffers** (`Buffer`): every pointer argument designates a region inside memory that overlaps
  neither the image nor the call's stack. Which buffers may alias is stated per task with `Apart`.
* **Outcome** (`Returns`): the run reaches the sentinel without an earlier fault or halt, with the
  return address popped, the direction flag clear and the callee-saved registers restored; every
  byte of memory outside the stated writable set and outside the `stack` bytes below the entry
  stack pointer is unchanged. In particular the image itself (code, tables, data) is unchanged, so
  a contract can be applied to the memory another call left behind.

A proof of a task therefore also bounds the function's stack use by `stack`.
-/
namespace Ssl
open X86

/-- A linked image: bytes placed at `base`, and the address of the `halt` sentinel. -/
structure Img where
  base : UInt32
  bytes : ByteArray
  halt : UInt32

def memSize : Nat := 0x800000

/-! ## Reading memory -/

/-- The byte at `addr`. -/
def memByte (mem : ByteArray) (addr : UInt32) : UInt8 := (rdBytes mem addr 1).toUInt8
/-- The `n` bytes from `addr`. -/
def memBytes (mem : ByteArray) (addr : UInt32) (n : Nat) : List UInt8 :=
  (List.range n).map fun i => memByte mem (addr + i.toUInt32)
/-- The 32-bit little-endian word at `addr`. -/
def memWord (mem : ByteArray) (addr : UInt32) : UInt32 := rdBytes mem addr 4
/-- The `n` consecutive 32-bit little-endian words from `addr`. -/
def memWords (mem : ByteArray) (addr : UInt32) (n : Nat) : Array UInt32 :=
  Array.ofFn (n := n) fun i => memWord mem (addr + 4 * i.val.toUInt32)

def byteAt (m : X86.Machine) (addr : UInt32) : UInt8 := memByte m.mem addr
def bytesAt (m : X86.Machine) (addr : UInt32) (n : Nat) : List UInt8 := memBytes m.mem addr n
def wordAt (m : X86.Machine) (addr : UInt32) : UInt32 := memWord m.mem addr
def wordsAt (m : X86.Machine) (addr : UInt32) (n : Nat) : Array UInt32 := memWords m.mem addr n

/-! ## Regions -/

/-- `a ∈ [lo, lo + n)`. -/
def InRange (lo : UInt32) (n : Nat) (a : UInt32) : Prop := lo ≤ a ∧ a.toNat < lo.toNat + n

instance (lo : UInt32) (n : Nat) : DecidablePred (InRange lo n) := fun a =>
  inferInstanceAs (Decidable (lo ≤ a ∧ a.toNat < lo.toNat + n))

def NoWrites (_ : UInt32) : Prop := False

/-- `[lo, lo + n)` lies inside memory (an empty region is nowhere, so any pointer will do). -/
def Fits (lo : UInt32) (n : Nat) : Prop := n = 0 ∨ lo.toNat + n ≤ memSize

/-- `[a, a + n)` and `[b, b + k)` do not overlap (an empty region overlaps nothing). -/
def Apart (a : UInt32) (n : Nat) (b : UInt32) (k : Nat) : Prop :=
  n = 0 ∨ k = 0 ∨ a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat

instance (lo : UInt32) (n : Nat) : Decidable (Fits lo n) := by unfold Fits; infer_instance
instance (a : UInt32) (n : Nat) (b : UInt32) (k : Nat) : Decidable (Apart a n b k) := by
  unfold Apart; infer_instance

/-! ## The caller -/

/-- The general registers and status flags a caller may leave in any state. -/
structure Regs where
  eax : UInt32
  ecx : UInt32
  edx : UInt32
  ebx : UInt32
  esi : UInt32
  edi : UInt32
  ebp : UInt32
  /-- Only the six arithmetic status flags (CF, PF, AF, ZF, SF, OF) of this word are used. -/
  flags : UInt32

/-- The state a caller is in when it calls: any memory, registers, status flags and stack pointer. -/
structure Caller where
  mem : ByteArray
  regs : Regs
  sp : UInt32

/-- The machine about to execute its first instruction at `eip`: flat ring-0 protected mode without
paging, interrupts disabled, direction flag clear; memory, general registers, status flags and the
stack pointer are the caller's. -/
def entry (mem : ByteArray) (r : Regs) (eip esp : UInt32) : X86.Machine :=
  let cs := flatSeg 0x08 0xC09B
  let ds := flatSeg 0x10 0xC093
  { mem
    cpu := { eip, esp, cs, ds, es := ds, ss := ds, fs := ds, gs := ds
             eax := r.eax, ecx := r.ecx, edx := r.edx, ebx := r.ebx
             esi := r.esi, edi := r.edi, ebp := r.ebp
             cr0 := CR0.PE ||| CR0.ET, eflags := 2 ||| (r.flags &&& Flag.arith) } }

/-- The machine at the first instruction of the function at `fn`, called by `c`. -/
def Caller.enter (c : Caller) (fn : UInt32) : X86.Machine := entry c.mem c.regs fn c.sp

/-- The lowest address of the `stack` bytes below the caller's stack pointer. -/
def Caller.stackLo (c : Caller) (stack : Nat) : UInt32 := c.sp - stack.toUInt32

/-- The size of the call's stack region: `stack` bytes for the callee, then the return address and
`nargs` argument words. It starts at `c.stackLo stack`. -/
def stackSize (stack nargs : Nat) : Nat := stack + 4 * (nargs + 1)

/-- A well-formed call of a function of `img` with stack arguments `args`, for which the callee may
use `stack` bytes below the stack pointer: memory has the model's size and holds the image at its
link address; the sentinel return address and the arguments are at the stack pointer; the stack
region is inside memory and does not overlap the image. -/
def Calls (img : Img) (c : Caller) (stack : Nat) (args : List UInt32) : Prop :=
  c.mem.size = memSize ∧
  img.base.toNat + img.bytes.size ≤ memSize ∧
  memBytes c.mem img.base img.bytes.size = img.bytes.data.toList ∧
  memWords c.mem c.sp (args.length + 1) = (img.halt :: args).toArray ∧
  stack ≤ c.sp.toNat ∧
  c.sp.toNat + 4 * (args.length + 1) ≤ memSize ∧
  Apart (c.stackLo stack) (stackSize stack args.length) img.base img.bytes.size

/-- `[lo, lo + n)` is a buffer of the caller: inside memory, overlapping neither the image nor the
stack region of a call with `nargs` stack arguments. -/
def Buffer (img : Img) (c : Caller) (stack nargs : Nat) (lo : UInt32) (n : Nat) : Prop :=
  Fits lo n ∧ Apart lo n img.base img.bytes.size ∧ Apart lo n (c.stackLo stack) (stackSize stack nargs)

instance (img : Img) (c : Caller) (stack : Nat) (args : List UInt32) : Decidable (Calls img c stack args) := by
  unfold Calls; infer_instance
instance (img : Img) (c : Caller) (stack nargs : Nat) (lo : UInt32) (n : Nat) :
    Decidable (Buffer img c stack nargs lo n) := by
  unfold Buffer; infer_instance

/-! ## Running -/

/-- A return is recognized before executing the sentinel HLT. -/
def returned (img : Img) (m : X86.Machine) : Bool :=
  m.cpu.eip == img.halt && m.fatal.isNone && !m.cpu.halted

def steps : Nat → X86.Machine → X86.Machine
  | 0, m => m
  | n + 1, m => steps n (X86.step m)

def Running (img : Img) (m : X86.Machine) : Prop :=
  (returned img m || m.fatal.isSome || m.cpu.halted) = false

def Trace (img : Img) (n : Nat) (m : X86.Machine) : Prop := ∀ i, i < n → Running img (steps i m)

/-- Some number of architectural steps reaches `P` without an earlier return, fault or halt. -/
def Reaches (img : Img) (m : X86.Machine) (P : X86.Machine → Prop) : Prop :=
  ∃ k, Trace img k m ∧ P (steps k m)

/-- The call returned to the sentinel, popped its return address and left the direction flag clear. -/
def Returned (img : Img) (m0 m1 : X86.Machine) : Prop :=
  returned img m1 = true ∧ m1.cpu.esp = m0.cpu.esp + 4 ∧ m1.cpu.eflags &&& Flag.DF = 0

/-- Callee-saved registers restored. -/
def CalleeSaved (m0 m1 : X86.Machine) : Prop :=
  m1.cpu.ebx = m0.cpu.ebx ∧ m1.cpu.esi = m0.cpu.esi ∧ m1.cpu.edi = m0.cpu.edi ∧ m1.cpu.ebp = m0.cpu.ebp

/-- Every byte of memory is unchanged, except those in the writable set `W` and the `stack` bytes
below the entry stack pointer. -/
def Preserved (m0 m1 : X86.Machine) (stack : Nat) (W : UInt32 → Prop) : Prop :=
  ∀ a : UInt32, a.toNat < memSize → ¬ W a → ¬ InRange (m0.cpu.esp - stack.toUInt32) stack a →
    memByte m1.mem a = memByte m0.mem a

/-- The call entered at `m0` returns, restores the callee-saved registers, changes no memory outside
`W` and its `stack` bytes, and the state at the return satisfies `Q`. -/
def Returns (img : Img) (m0 : X86.Machine) (stack : Nat) (W : UInt32 → Prop)
    (Q : X86.Machine → Prop) : Prop :=
  Reaches img m0 fun m1 =>
    Returned img m0 m1 ∧ CalleeSaved m0 m1 ∧ Preserved m0 m1 stack W ∧ Q m1

/-- Total, fuel-bounded run of the architectural step function (for executable checkers). -/
def runSteps (img : Img) : Nat → X86.Machine → X86.Machine
  | 0, m => m
  | n + 1, m =>
    if returned img m || m.fatal.isSome || m.cpu.halted then m
    else runSteps img n (X86.step m)

end Ssl
