import X86.Step
/-!
# Multiprocessor machine with the x86-TSO memory model

Several CPUs share physical memory. Each CPU has a FIFO store buffer (x86-TSO, Owens, Sarkar and
Sewell, "A better x86 memory model: x86-TSO", 2009):

* a CPU executes one whole instruction per step (`X86.step`) against its *view*: shared memory
  overlaid with its own buffered stores, so a load sees the newest own buffered store to each byte,
  otherwise memory;
* the stores of the step (logged by `physWr`, see `Machine.tso`) are appended to its buffer;
* a separate step commits the oldest buffered store of some CPU to memory;
* a locked instruction (LOCK prefix, XCHG with memory) or a serializing instruction can only
  execute with an empty buffer and writes memory directly, in the same atomic step.

`TStep` is the nondeterministic step relation; `successors` enumerates it for testing.

## Soundness of the modelling choices

A theorem about all `TStep` executions is about real hardware only if the model allows every
behaviour the hardware has. Where an instruction step is stronger than the hardware, the CPU is
stopped with `Fault.unsupported` instead (statements must exclude stopped CPUs), and where the SDM
leaves room, the weaker choice is taken:

* A store is one buffer entry (committed atomically) only if it lies in one aligned 8-byte block;
  other stores are split into byte stores. Two 4-byte halves of a quadword store are two entries.
* A step reads all its data at one instant. That is only as strong as the hardware for a single
  load that is single-copy atomic, so a step whose data reads (the logged reads minus the fetch of
  the instruction bytes) do not all lie in one aligned 8-byte block stops, unless the instruction is
  locked (atomic on the bus) and completed without a fault. This stops e.g. CMPS, POPA, IRET, split
  loads and exception delivery (descriptor-table reads). A REP string instruction does one iteration
  per step.
* Interrupt and exception delivery do not drain the buffer.
* Store-to-load forwarding is byte-granular for overlapping stores of different sizes.
* Out of scope (the CPU stops): paging (the walk updates page tables directly), I/O instructions
  and devices (each CPU has its own copy of the device state; a CPU must start with `intr = false`
  and no timer).
* MFENCE drains the store buffer. LFENCE and SFENCE need no additional ordering for the ordinary
  write-back accesses supported here. Non-temporal and masked stores (and CLZERO, weakly ordered
  like them, APM CLZERO), APIC MMIO and SMM stop. CLFLUSH, CLFLUSHOPT, CLWB and the prefetches
  have no memory effect in the model (no caches). MONITOR/MONITORX and MWAIT/MWAITX stop: a store
  by another CPU to the monitored line would end the wait, which the single-CPU step does not see.
* Instruction fetch reads the view like data; code is assumed not to be modified concurrently.
-/
namespace X86

namespace Tso

/-- Commit one store to memory. -/
def commit (mem : ByteArray) (s : Store) : ByteArray := wrBytes mem s.addr s.n s.val

/-- Memory as seen through a store buffer (oldest store first). -/
def overlay (mem : ByteArray) (buf : Array Store) : ByteArray := buf.foldl commit mem

/-- A store as buffer entries: one entry inside an aligned 8-byte block, else one per byte. -/
def splitStore (s : Store) : Array Store :=
  if (s.addr &&& 7) + s.n ≤ 8 then #[s]
  else (Array.range s.n.toNat).map fun k =>
    { addr := s.addr + k.toUInt32, n := 1, val := s.val >>> (k.toUInt32 * 8) }

/-- Locked read-modify-write: a valid LOCK prefix, or XCHG with a memory operand (implicitly
locked). (An invalid LOCK prefix raises #UD.) -/
def locked (i : Inst) : Bool := (i.lock && lockOk i) || ((i.op == 0x86 || i.op == 0x87) && i.isMem)

/-- Serializing instructions (SDM Vol. 3A "Serializing Instructions") that the model decodes:
IRET, CPUID, MOV to CR/DR, INVD, WBINVD, WRMSR, LLDT, LTR, LGDT, LIDT, INVLPG. -/
def serializing (i : Inst) : Bool :=
  i.op == 0xCF || i.op == 0x1A2 || i.op == 0x122 || i.op == 0x123 || i.op == 0x108 ||
  i.op == 0x109 || i.op == 0x130 || (i.op == 0x100 && (i.reg == 2 || i.reg == 3)) ||
  (i.op == 0x101 && (i.reg == 2 || i.reg == 3 || i.reg == 7))

/-- Instructions that need an empty store buffer and write memory directly. -/
def drains (i : Inst) : Bool := locked i || serializing i ||
  (i.op == 0x1AE && !i.isMem && i.reg == 6) -- MFENCE

/-- Non-temporal and masked stores use ordering outside this write-back TSO model. -/
def isWeakStore (i : Inst) : Bool :=
  i.op == 0x12B || i.op == 0x1C3 || i.op == 0x1E7 || i.op == 0x1F7 ||
  (!i.vex && i.op == 0x101 && i.modrm == 0xFC)   -- CLZERO

/-- MONITOR, MWAIT, MONITORX, MWAITX (0F 01 C8, C9, FA without F3, FB). -/
def isMonitorWait (i : Inst) : Bool :=
  !i.vex && i.op == 0x101 && (i.modrm == 0xC8 || i.modrm == 0xC9 || i.modrm == 0xFB ||
    (i.modrm == 0xFA && i.rep != 0xF3))

/-- IN, OUT, INS, OUTS. -/
def isIO (i : Inst) : Bool :=
  (0x6C ≤ i.op && i.op ≤ 0x6F) || (0xE4 ≤ i.op && i.op ≤ 0xE7) || (0xEC ≤ i.op && i.op ≤ 0xEF)

/-- All reads lie in one aligned 8-byte block (so that one atomic snapshot is no stronger than the
hardware). -/
def oneBlock (rs : Array (UInt32 × UInt32)) : Bool :=
  match rs[0]? with
  | none => true
  | some (p, _) => rs.all fun (a, n) => a &&& ~~~7 == p &&& ~~~7 && (a &&& 7) + n ≤ 8

/-- The data reads of a step: the logged reads without the fetch of the instruction bytes. The
fetch is recognized only as exactly the first `len` reads, one byte each at `cs.base + eip + k`;
otherwise every read counts as a data read. -/
def dataReads (c : Cpu) (i : Option Inst) (rs : Array (UInt32 × UInt32)) : Array (UInt32 × UInt32) :=
  match i with
  | none => rs
  | some i =>
    let n := i.len.toNat
    let isFetch := n ≤ rs.size &&
      (List.range n).all fun k => rs[k]! == (c.cs.base + c.eip + k.toUInt32, 1)
    if isFetch then rs.extract n rs.size else rs

end Tso

/-- One CPU of the multiprocessor: its machine state (`mem` unused, `tso = none` between steps) and
its store buffer, oldest store first. -/
structure Core where
  m : Machine
  sb : Array Store := #[]
  deriving Inhabited

/-- The multiprocessor: shared physical memory and the CPUs. -/
structure TMachine where
  mem : ByteArray
  cores : Array Core
  deriving Inhabited

namespace TMachine
open Tso

/-- The multiprocessor with the given CPUs (their `mem` is dropped) and empty store buffers. -/
def init (mem : ByteArray) (cpus : List Machine) : TMachine :=
  { mem, cores := (cpus.map fun m => { m := { m with mem := .empty, tso := none } }).toArray }

/-- CPU `k`'s view of memory. -/
def view (t : TMachine) (c : Core) : Machine := { c.m with mem := overlay t.mem c.sb }

/-- CPU `k` executes one step (`X86.step` on its view), or `none` if it cannot: no such CPU, the CPU
has stopped (`fatal`), or the instruction drains the buffer and the buffer is not empty. A step the
model cannot represent soundly stops the CPU in its state before the step. -/
def exec (t : TMachine) (k : Nat) : Option TMachine := do
  let c ← t.cores[k]?
  if c.m.fatal.isSome then none
  let v := t.view c
  let inst := match decode v with
    | .ok i _ => some i
    | .error _ _ => none
  let drain := inst.any drains
  if drain && !c.sb.isEmpty then none
  let stop (why : String) : TMachine :=
    { t with cores := t.cores.set! k { c with m := { c.m with fatal := some (.unsupported why) } } }
  if v.cpu.cr0 &&& CR0.PG != 0 then return stop "TSO: paging"
  if v.intr || v.timerAt != maxU64 then return stop "TSO: devices"
  if inst.any isIO then return stop "TSO: I/O instruction"
  if v.smiPending || v.cpu.smm then return stop "TSO: SMM"
  if inst.any isWeakStore then return stop "TSO: non-temporal or masked store"
  if inst.any isMonitorWait then return stop "TSO: MONITOR/MWAIT"
  let v' := step { v with tso := some {} }
  let log := v'.tso.getD {}
  -- A locked instruction is atomic only if it completed: lockable instructions never branch, so
  -- completion is EIP advancing by the length (a fault delivers an exception in the same step).
  let atomic := inst.any fun i => locked i && v'.cpu.eip == v.cpu.eip + i.len && v'.fatal.isNone
  if !atomic && !oneBlock (dataReads v.cpu inst log.reads) then
    return stop "TSO: non-atomic loads in one step"
  let m' := { v' with mem := .empty, tso := none }
  if drain then
    return { mem := log.writes.foldl commit t.mem, cores := t.cores.set! k { m := m', sb := c.sb } }
  else
    return { t with cores := t.cores.set! k { m := m', sb := c.sb ++ log.writes.flatMap splitStore } }

/-- Commit the oldest buffered store of CPU `k`, or `none` if its buffer is empty. -/
def flush (t : TMachine) (k : Nat) : Option TMachine := do
  let c ← t.cores[k]?
  let s ← c.sb[0]?
  return { mem := commit t.mem s, cores := t.cores.set! k { c with sb := c.sb.extract 1 c.sb.size } }

/-- All successors of `t` (`exec` of every CPU, then `flush` of every CPU). -/
def successors (t : TMachine) : List TMachine :=
  (List.range t.cores.size).filterMap t.exec ++ (List.range t.cores.size).filterMap t.flush

end TMachine

/-- One step of the multiprocessor: some CPU executes a step or commits its oldest buffered store. -/
inductive TStep : TMachine → TMachine → Prop
  | exec (k : Nat) (h : t.exec k = some t') : TStep t t'
  | flush (k : Nat) (h : t.flush k = some t') : TStep t t'

end X86
