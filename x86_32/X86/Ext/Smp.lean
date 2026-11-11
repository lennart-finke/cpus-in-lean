import X86.Exec
/-!
# Multiprocessor platform

Owner: the SMP workstream (I/O APIC, x2APIC, IPIs, several CPUs). The local APIC and the I/O APIC
are in `X86/Dev.lean`, interrupt messages and the device pages in `X86/Machine.lean`, IRQ routing
and IA32_APIC_BASE in `X86/Io.lean`, INIT/STARTUP/NMI at instruction boundaries in `X86/Step.lean`
(`smpEvent?`), the N-CPU machine and its scheduler in `X86/Mp.lean`, the MP tables in
`X86/Boot.lean`, the topology leaves in `X86/Cpuid.lean` (`Cpuid.topo`).

Hook (called by `X86/Dispatch.lean`; `none` = not handled here):

* `msr?`: x2APIC registers (0x800..0x8FF).

## x2APIC register interface (AMD APM vol. 2, 16.11–16.15)

MSR 800h + (MMIO offset >> 4), table 16-6. Outside x2APIC mode every one of them is #GP(0) (16.11),
as are the unimplemented ones (80Ch remote read and 80Eh DFR, which x2APIC mode eliminates, 831h, and
every address the table does not list). RDMSR of the write-only EOI (80Bh) and SELF IPI (83Fh) is
#GP(0); WRMSR of a read-only register (ID, version, APR, PPR, LDR, ISR/TMR/IRR, current count, the
extended feature register) is #GP(0). WRMSR checks reserved bits (16.11.3): bits 63:32 of every
register but the ICR, the register's must-be-zero bits as in xAPIC mode (TPR 31:8, SVR 31:10, LVT
entries outside their fields and read-only bits, divide configuration, extended control 31:3, SEOI
31:8, extended LVTs), a non-zero EOI or ESR value, the ICR's bits 31:20, 17:16 (remote read status)
and 13:12 (delivery status) and its eliminated message types 1 (lowest priority), 3 (remote read)
and 7 (ExtINT) (16.13), and SELF IPI bits 31:8 (16.15). The IER registers are not checked (their
reset value sets the "reserved" bits 15:0 of 848h). The ID is the 32-bit x2APIC ID, the LDR the
derived logical ID (cluster ID[19:4], bit ID[3:0]); the 64-bit ICR names a 32-bit destination
(FFFF_FFFFh: broadcast; logical: cluster mode only, 16.14); SELF IPI sends a fixed, edge-triggered
IPI with shorthand self without changing the ICR.
-/
namespace X86
namespace Smp

/-- The xAPIC register offset of x2APIC MSR `n`. -/
@[inline] def x2Off (n : UInt32) : UInt32 := (n - 0x800) <<< 4

/-- Read-only x2APIC registers. -/
def x2ReadOnly (n : UInt32) : Bool :=
  n == 0x802 || n == 0x803 || n == 0x809 || n == 0x80A || n == 0x80D ||
  (0x810 ≤ n && n ≤ 0x827) || n == 0x839 || n == 0x840

/-- Implemented x2APIC registers (APM table 16-6). -/
def x2Implemented (n : UInt32) : Bool :=
  x2ReadOnly n || n == 0x808 || n == 0x80B || n == 0x80F || n == 0x828 || n == 0x830 ||
  (0x832 ≤ n && n ≤ 0x838) || n == 0x83E || n == 0x83F || n == 0x841 || n == 0x842 ||
  (0x848 ≤ n && n ≤ 0x84F) || (0x850 ≤ n && n ≤ 0x853)

/-- Must-be-zero bits of a write to x2APIC register `n` (bits 31:0; bits 63:32 are reserved for all
but the ICR). -/
def x2Reserved (n : UInt32) : UInt32 :=
  match n with
  | 0x808 => 0xFFFFFF00
  | 0x80F => 0xFFFFFC00
  | 0x83E => ~~~0xB
  | 0x841 => ~~~7
  | 0x842 => 0xFFFFFF00
  | 0x83F => 0xFFFFFF00
  | 0x80B | 0x828 => 0xFFFFFFFF
  | _ =>
    if 0x832 ≤ n && n ≤ 0x837 then ~~~(Apic.lvtMask[(n - 0x832).toNat]! ||| 0x5000)
    else if 0x850 ≤ n && n ≤ 0x853 then ~~~(Apic.xlvtMask ||| 0x1000)
    else 0

/-- RDMSR of x2APIC register `n`. -/
def x2Read (n : UInt32) : M UInt64 := do
  let m ← getM
  let a := m.apic
  if !a.x2 || !x2Implemented n || n == 0x80B || n == 0x83F then gp 0
  if n == 0x802 then return a.id.toUInt64
  if n == 0x830 then return (a.icrHi.toUInt64 <<< 32) ||| a.icrLo.toUInt64
  match a.read (x2Off n) m.icount with
  | some v => return v.toUInt64
  | none => gp 0

/-- WRMSR of x2APIC register `n`. -/
def x2Write (n : UInt32) (v : UInt64) : M Unit := do
  let m ← getM
  let a := m.apic
  if !a.x2 || !x2Implemented n || x2ReadOnly n then gp 0
  let lo := v.toUInt32
  if n == 0x830 then
    let mt := (lo >>> 8) &&& 7
    if lo &&& 0xFFF33000 != 0 || mt == 1 || mt == 3 || mt == 7 then gp 0
    set ({ m with apic := { a with icrLo := lo, icrHi := (v >>> 32).toUInt32 } }.sendIcr.syncApic)
    return
  if v >>> 32 != 0 || lo &&& x2Reserved n != 0 then gp 0
  if n == 0x83F then
    -- SELF IPI: fixed, edge, shorthand self (APM 16.15)
    let m := if lo < 16 then { m with apic := m.apic.error Esr.SIV } else m
    set (m.deliver { mode := 0, vec := lo, sh := 1, x2 := true, src := some m.cur }).1.syncApic
    return
  set (m.apicWrite (x2Off n) lo)

def msr? (n : UInt32) : Option MsrImpl :=
  if 0x800 ≤ n && n ≤ 0x8FF then some { rd := x2Read n, wr := x2Write n } else none

end Smp
end X86
