import X86.Word
/-!
# Platform devices

Minimal, deterministic models of the PC devices Linux needs:

* `Pic`  — Intel 8259A programmable interrupt controller (master + slave pair)
* `Pit`  — Intel 8254 programmable interval timer (channels 0 and 2)
* `Uart` — NS16550A serial port (COM1)
* CMOS RTC (fixed clock)
* `Apic` — the local APIC (memory-mapped or x2APIC MSRs; see `Machine.physRd`, `X86/Ext/Smp.lean`)
* `IoApic` — the I/O APIC (82093AA)

Time is virtual: the PIT input clock is derived from the retired instruction count
(`instrHz` instructions per virtual second), so runs are reproducible.
-/
namespace X86

/-! ## 8259A PIC -/

structure Pic where
  irr : UInt8 := 0
  isr : UInt8 := 0
  imr : UInt8 := 0xFF
  /-- Input line levels, for edge detection. -/
  lines : UInt8 := 0
  vecBase : UInt8 := 8
  /-- 0 = operational, otherwise the number of the next expected ICW. -/
  icwStep : UInt8 := 0
  single : Bool := false
  needIcw4 : Bool := false
  autoEoi : Bool := false
  readIsr : Bool := false
  elcr : UInt8 := 0
  deriving Repr, Inhabited

namespace Pic

def setLine (p : Pic) (irq : UInt8) (level : Bool) : Pic :=
  let b : UInt8 := 1 <<< irq
  if p.elcr &&& b != 0 then
    -- level triggered: IRR follows the line
    if level then { p with lines := p.lines ||| b, irr := p.irr ||| b }
    else { p with lines := p.lines &&& ~~~b, irr := p.irr &&& ~~~b }
  else if level then
    if p.lines &&& b == 0 then { p with lines := p.lines ||| b, irr := p.irr ||| b } else p
  else { p with lines := p.lines &&& ~~~b }

/-- Highest-priority request that is not masked and not blocked by an in-service
interrupt of higher or equal priority (fixed priority, IR0 highest). `extra` adds request bits
(used for the cascade input). -/
def highest (p : Pic) (extra : UInt8 := 0) : Option UInt8 :=
  let req := (p.irr ||| extra) &&& ~~~p.imr
  let rec go (i : Nat) : Option UInt8 :=
    match i with
    | 0 => none
    | n+1 =>
      let k : UInt8 := (8 - (n+1)).toUInt8
      let b : UInt8 := 1 <<< k
      if p.isr &&& b != 0 then none
      else if req &&& b != 0 then some k
      else go n
  go 8

/-- Interrupt acknowledge for input `k`. -/
def ack (p : Pic) (k : UInt8) : Pic :=
  let b : UInt8 := 1 <<< k
  let p := if p.elcr &&& b == 0 then { p with irr := p.irr &&& ~~~b } else p
  if p.autoEoi then p else { p with isr := p.isr ||| b }

/-- Highest priority bit set in `x`, if any. -/
def lowestBit (x : UInt8) : Option UInt8 :=
  let rec go (i : Nat) : Option UInt8 :=
    match i with
    | 0 => none
    | n+1 => let k := (8 - (n+1)).toUInt8; if x &&& (1 <<< k) != 0 then some k else go n
  go 8

def write (p : Pic) (a0 : Bool) (v : UInt8) : Pic :=
  if !a0 then
    if v &&& 0x10 != 0 then
      -- ICW1
      { p with icwStep := 2, single := v &&& 2 != 0, needIcw4 := v &&& 1 != 0,
               imr := 0, isr := 0, irr := 0, autoEoi := false, readIsr := false }
    else if v &&& 0x08 != 0 then
      -- OCW3
      if v &&& 2 != 0 then { p with readIsr := v &&& 1 != 0 } else p
    else
      -- OCW2
      let cmd := v >>> 5
      if cmd == 1 || cmd == 5 then
        match lowestBit p.isr with
        | some k => { p with isr := p.isr &&& ~~~((1 : UInt8) <<< k) }
        | none => p
      else if cmd == 3 || cmd == 7 then
        { p with isr := p.isr &&& ~~~((1 : UInt8) <<< (v &&& 7)) }
      else p
  else
    match p.icwStep with
    | 2 => { p with vecBase := v &&& 0xF8,
                    icwStep := if !p.single then 3 else if p.needIcw4 then 4 else 0 }
    | 3 => { p with icwStep := if p.needIcw4 then 4 else 0 }
    | 4 => { p with autoEoi := v &&& 2 != 0, icwStep := 0 }
    | _ => { p with imr := v }

def read (p : Pic) (a0 : Bool) : UInt8 :=
  if a0 then p.imr else if p.readIsr then p.isr else p.irr

end Pic

/-! ## 8254 PIT -/

/-- Virtual instruction rate: instructions per virtual second. -/
def instrHz : UInt64 := 100000000
def pitHz : UInt64 := 1193182

@[inline] def pitTick (icount : UInt64) : UInt64 := icount * pitHz / instrHz
/-- First instruction count at which the PIT tick counter reaches `t`. -/
@[inline] def tickToIcount (t : UInt64) : UInt64 := (t * instrHz + pitHz - 1) / pitHz

structure PitCh where
  mode : UInt8 := 0
  access : UInt8 := 3
  /-- Reload value, 1..65536. -/
  reload : UInt64 := 0x10000
  /-- PIT tick at which the current count was loaded. -/
  start : UInt64 := 0
  armed : Bool := false
  writeHi : Bool := false
  pendLo : UInt8 := 0
  readHi : Bool := false
  latched : Bool := false
  latch : UInt16 := 0
  /-- Tick of the next rising edge of OUT (IRQ for channel 0); `none` if none scheduled. -/
  nextFire : Option UInt64 := none
  deriving Repr, Inhabited

namespace PitCh

def count (c : PitCh) (t : UInt64) : UInt16 :=
  if !c.armed then 0 else
  let el := t - c.start
  let n := c.reload
  match c.mode with
  | 2 => (n - el % n).toUInt16
  | 3 => (n - (2 * el) % n).toUInt16
  | _ => (n - el).toUInt16  -- wraps modulo 2^16 after terminal count

def out (c : PitCh) (t : UInt64) : Bool :=
  if !c.armed then true else
  let el := t - c.start
  match c.mode with
  | 0 => el ≥ c.reload
  | 2 => el % c.reload != c.reload - 1
  | 3 => el % c.reload < (c.reload + 1) / 2
  | _ => true

def load (c : PitCh) (n : UInt64) (t : UInt64) : PitCh :=
  let n := if n == 0 then 0x10000 else n
  { c with reload := n, start := t, armed := true, nextFire := some (t + n) }

def writeCount (c : PitCh) (v : UInt8) (t : UInt64) : PitCh :=
  match c.access with
  | 1 => c.load v.toUInt64 t
  | 2 => c.load (v.toUInt64 <<< 8) t
  | _ =>
    if !c.writeHi then { c with writeHi := true, pendLo := v, armed := if c.mode == 0 then false else c.armed,
                                nextFire := if c.mode == 0 then none else c.nextFire }
    else { c.load (c.pendLo.toUInt64 ||| (v.toUInt64 <<< 8)) t with writeHi := false }

def readCount (c : PitCh) (t : UInt64) : UInt8 × PitCh :=
  let v := if c.latched then c.latch else c.count t
  match c.access with
  | 1 => (v.toUInt8, { c with latched := false })
  | 2 => ((v >>> 8).toUInt8, { c with latched := false })
  | _ =>
    if !c.readHi then (v.toUInt8, { c with readHi := true })
    else ((v >>> 8).toUInt8, { c with readHi := false, latched := false })

def control (c : PitCh) (v : UInt8) (t : UInt64) : PitCh :=
  let acc := (v >>> 4) &&& 3
  if acc == 0 then
    if c.latched then c else { c with latched := true, latch := c.count t }
  else
    let mode := (v >>> 1) &&& 7
    let mode := if mode ≥ 6 then mode - 4 else mode
    { c with access := acc, mode := mode, writeHi := false, readHi := false, latched := false,
             armed := false, nextFire := none }

/-- Called when the tick counter reaches `nextFire`. -/
def fired (c : PitCh) : PitCh :=
  match c.nextFire, c.mode with
  | some f, 2 => { c with nextFire := some (f + c.reload) }
  | some f, 3 => { c with nextFire := some (f + c.reload) }
  | _, _ => { c with nextFire := none }

end PitCh

structure Pit where
  ch0 : PitCh := {}
  ch1 : PitCh := {}
  ch2 : PitCh := {}
  /-- Port 0x61 bits 0..1 (channel 2 gate, speaker enable). -/
  p61 : UInt8 := 0
  deriving Repr, Inhabited

/-! ## 16550A UART -/

structure Uart where
  ier : UInt8 := 0
  lcr : UInt8 := 0
  mcr : UInt8 := 0
  scr : UInt8 := 0
  dll : UInt8 := 0x0C
  dlm : UInt8 := 0
  fcr : UInt8 := 0
  /-- THR-empty interrupt pending. -/
  thri : Bool := false
  rx : ByteArray := .empty
  rxPos : Nat := 0
  /-- Transmitted bytes not yet collected by the host. -/
  tx : ByteArray := .empty
  deriving Inhabited

namespace Uart

@[inline] def rxAvail (u : Uart) : Bool := u.rxPos < u.rx.size

def irq (u : Uart) : Bool :=
  u.mcr &&& 0x08 != 0 &&
  ((u.ier &&& 1 != 0 && u.rxAvail) || (u.ier &&& 2 != 0 && u.thri))

def iir (u : Uart) : UInt8 :=
  let fifo : UInt8 := if u.fcr &&& 1 != 0 then 0xC0 else 0
  if u.ier &&& 1 != 0 && u.rxAvail then 0x04 ||| fifo
  else if u.ier &&& 2 != 0 && u.thri then 0x02 ||| fifo
  else 0x01 ||| fifo

def pushRx (u : Uart) (b : ByteArray) : Uart :=
  if u.rxPos ≥ u.rx.size then { u with rx := b, rxPos := 0 } else { u with rx := u.rx ++ b }

def read (u : Uart) (r : UInt32) : UInt8 × Uart :=
  let dlab := u.lcr &&& 0x80 != 0
  match r with
  | 0 => if dlab then (u.dll, u) else
      if u.rxAvail then (u.rx.get! u.rxPos, { u with rxPos := u.rxPos + 1 }) else (0, u)
  | 1 => if dlab then (u.dlm, u) else (u.ier, u)
  | 2 => let v := u.iir; (v, if v &&& 0x0F == 0x02 then { u with thri := false } else u)
  | 3 => (u.lcr, u)
  | 4 => (u.mcr, u)
  | 5 => ((0x60 : UInt8) ||| (if u.rxAvail then 1 else 0), u)
  | 6 =>
    if u.mcr &&& 0x10 != 0 then
      let m := u.mcr
      (((m &&& 0x0C) <<< 4) ||| ((m &&& 1) <<< 5) ||| ((m &&& 2) <<< 3), u)
    else (0xB0, u)
  | _ => (u.scr, u)

def write (u : Uart) (r : UInt32) (v : UInt8) : Uart :=
  let dlab := u.lcr &&& 0x80 != 0
  match r with
  | 0 => if dlab then { u with dll := v } else
      if u.mcr &&& 0x10 != 0 then { u.pushRx (ByteArray.mk #[v]) with thri := true }
      else { u with tx := u.tx.push v, thri := true }
  | 1 => if dlab then { u with dlm := v } else
      let nv := v &&& 0x0F
      let u' := { u with ier := nv }
      if nv &&& 2 != 0 && u.ier &&& 2 == 0 then { u' with thri := true } else u'
  | 2 => let u := { u with fcr := v }
         if v &&& 2 != 0 then { u with rx := .empty, rxPos := 0 } else u
  | 3 => { u with lcr := v }
  | 4 => { u with mcr := v &&& 0x1F }
  | 7 => { u with scr := v }
  | _ => u

end Uart

/-! ## CMOS / RTC -/

def bcd (n : Nat) : UInt8 := ((n / 10) * 16 + n % 10).toUInt8

/-- CMOS RAM with a fixed time of 2026-10-02 12:00:00 (BCD, 24h). -/
def cmosInit : ByteArray := Id.run do
  let mut a := ByteArray.mk (Array.replicate 128 0)
  a := a.set! 0x00 (bcd 0)
  a := a.set! 0x02 (bcd 0)
  a := a.set! 0x04 (bcd 12)
  a := a.set! 0x06 (bcd 5)
  a := a.set! 0x07 (bcd 2)
  a := a.set! 0x08 (bcd 10)
  a := a.set! 0x09 (bcd 26)
  a := a.set! 0x0A 0x26
  a := a.set! 0x0B 0x02
  a := a.set! 0x0D 0x80
  a := a.set! 0x32 (bcd 20)
  return a

/-! ## Local APIC (AMD APM vol. 2, chapter 16)

One local APIC per CPU: `Machine.apic` for the running CPU, `Machine.peers` for the others. In xAPIC
mode the registers are memory-mapped at the APIC base (`IA32_APIC_BASE`, reset 0xFEE00000; the page
actually decoded is cached in `mmio`); in x2APIC mode they are MSRs 800h–8FFh (`X86/Ext/Smp.lean`)
and the page is not decoded (APM 16.11: the MMIO interface is disabled).

Implemented (APM table 16-2): ID, version (80050010h: EAS, six LVT entries, version 10h), TPR, APR
(AMD definition, 16.6.2), PPR, EOI, remote read (RRR and ICR.RRS), LDR, DFR (flat and cluster
models), SVR (vector, ASE, FCC), ISR/TMR/IRR, ESR (SAE, SIV, RIV, IRA; latched by a write, 16.4.6),
ICR with every message type, destination mode and shorthand (`Machine.sendIcr`), the six LVT entries
with their message types (fixed, SMI, NMI, ExtINT; trigger mode and remote IRR for LINT0/LINT1), the
timer (one-shot and periodic: Zen 2 has no TSC-deadline mode, LVT bit 18 is reserved), the divide
configuration, and the extended space (APM 16.3.5–16.3.6, 16.7): extended feature register
00040007h (four extended LVTs, SEOI, IER, 8-bit IDs), extended control (IERN, SN, XAIDN), SEOI, IER
(reset all ones; masks IRR in the priority selection while IERN = 1) and the extended LVTs
500h–530h (IBS, thresholding, ...: storage; the model has no source that raises them, nor thermal or
performance-counter interrupts).

Choices where the APM is open or inconsistent (also in `x86_32/README.md`):
* SVR.FCC: 16.4.7 says both "set to 1 disables focus checking" and "clearing to 0 disables it";
  16.6.2 (bit 9 = 0: enabled) and Intel agree on the first, which the model follows.
* XAIDN = 0 is described as selecting 4-bit APIC IDs; the model always matches 8-bit IDs (the
  bit is storage only), as firmware of the 128-thread 7742 has to enable 8-bit IDs.
* IER writes take effect only while IERN = 1 ("enables writes", 16.3.6).
* An APIC that is globally disabled (AE = 0) accepts no messages; a software-disabled one (ASE = 0)
  accepts SMI, NMI, INIT, STARTUP and remote reads, and ExtINT IPIs ("can be delivered even if the
  APIC is disabled", 16.5), but no fixed or lowest-priority interrupts.
* Illegal vectors (0..15) of fixed and lowest-priority messages: the sender records SIV, the
  message is sent, and receivers drop it recording RIV (as for an LVT entry with an illegal vector).
  SAE is recorded when no APIC matches the destination of an IPI; RAE is never recorded.
* The divide value is sampled when the initial count is written.
* Message delivery is instantaneous, so delivery-status bits read 0.

The PIC reaches the processor through LINT0 in ExtINT mode (virtual wire, the state the firmware
leaves the boot processor's LINT0 in) or directly while the APIC is globally disabled; LINT0 in fixed,
SMI or NMI mode sees the PIC's INTR output as its input pin. LINT1 (the NMI line) has no source. -/

namespace Esr
/-- Sent accept error, receive accept error, sent/received illegal vector, illegal register address. -/
def SAE : UInt32 := 0x04
def RAE : UInt32 := 0x08
def SIV : UInt32 := 0x20
def RIV : UInt32 := 0x40
def IRA : UInt32 := 0x80
end Esr

structure Apic where
  /-- IA32_APIC_BASE: base address bits 31:12 and 47:32 (MAXPHYADDR 48), AE (bit 11), EXTD (bit 10,
  x2APIC mode), BSC (bit 8, read-only). -/
  base : UInt32 := 0xFEE00000
  baseHi : UInt32 := 0
  enabled : Bool := true
  x2 : Bool := false
  bsp : Bool := true
  /-- The physical page the xAPIC registers occupy: `base` while AE = 1, EXTD = 0 and the base is
  below 4 GiB; otherwise 1 (matches no page). See `withMmio`. -/
  mmio : UInt32 := 0xFEE00000
  /-- Initial APIC ID (assigned by hardware: the CPU index) and the APIC ID: bits 31:24 of register
  20h in xAPIC mode (writable), the 32-bit x2APIC ID in x2APIC mode. -/
  initId : UInt32 := 0
  id : UInt32 := 0
  tpr : UInt32 := 0
  /-- LDR: bits 31:24 in xAPIC mode, the 32-bit logical x2APIC ID in x2APIC mode. -/
  ldr : UInt32 := 0
  dfr : UInt32 := 0xFFFFFFFF
  svr : UInt32 := 0xFF
  isr : Array UInt32 := Array.replicate 8 0
  tmr : Array UInt32 := Array.replicate 8 0
  irr : Array UInt32 := Array.replicate 8 0
  icrLo : UInt32 := 0
  icrHi : UInt32 := 0
  /-- LVT timer, thermal, performance counter, LINT0, LINT1, error. -/
  lvt : Array UInt32 := #[0x10000, 0x10000, 0x10000, 0x700, 0x10000, 0x10000]
  initCount : UInt32 := 0
  divCfg : UInt32 := 0
  /-- Instruction count at which the current count was loaded, divider of the run, next expiry. -/
  timerStart : UInt64 := 0
  timerDiv : UInt64 := 2
  timerNext : UInt64 := 0xFFFFFFFFFFFFFFFF
  /-- ESR as last latched by a write, and the errors detected since (APM 16.4.6). -/
  esr : UInt32 := 0
  errs : UInt32 := 0
  /-- Remote read register (C0h). -/
  rrr : UInt32 := 0
  /-- Extended APIC control (410h), IER (480h–4F0h), extended LVTs (500h–530h). SEOI (420h) is
  write-only in the model (reads 0). -/
  extCtl : UInt32 := 0
  ier : Array UInt32 := Array.replicate 8 0xFFFFFFFF
  xlvt : Array UInt32 := Array.replicate 4 0
  /-- Messages the APIC passes directly to the CPU core (APM 16.2: SMI, NMI, INIT, STARTUP and the
  external interrupt): taken at the next instruction boundary of this CPU. -/
  smi : Bool := false
  nmi : Bool := false
  init : Bool := false
  sipi : Option UInt32 := none
  extInt : Bool := false
  /-- LINT0 input level last seen (edge detection when LINT0 is not in ExtINT mode). -/
  lint0In : Bool := false
  deriving Repr, Inhabited

namespace Apic

def never : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- APIC version register: EAS (extended space present), MLE = 5 (six LVT entries), version 10h
(APM 16.3.4: "1Xh"; 10h is what AMD processors report, UNCONFIRMED for the 7742). -/
def version : UInt32 := 0x80050010
/-- Extended APIC feature register: XLC = 4, XAIDC, SNIC, INC (APM table 16-2 reset value). -/
def extFeature : UInt32 := 0x00040007

@[inline] def swEnabled (a : Apic) : Bool := a.enabled && a.svr &&& 0x100 != 0

/-- Recompute the decoded MMIO page after a change of the base, AE or EXTD. -/
@[inline] def withMmio (a : Apic) : Apic :=
  { a with mmio := if a.enabled && !a.x2 && a.baseHi == 0 then a.base else 1 }

/-- The APIC ID used to match physical destinations and to break lowest-priority ties. -/
@[inline] def physId (a : Apic) : UInt32 := a.id

@[inline] def getBit (v : Array UInt32) (n : UInt32) : Bool := (v[(n >>> 5).toNat]! >>> (n &&& 31)) &&& 1 != 0
@[inline] def setBit (v : Array UInt32) (n : UInt32) (b : Bool) : Array UInt32 :=
  let k := (n >>> 5).toNat
  let m : UInt32 := 1 <<< (n &&& 31)
  v.set! k (if b then v[k]! ||| m else v[k]! &&& ~~~m)

/-- Highest set vector of a 256-bit register. -/
def highest (v : Array UInt32) : Option UInt32 := Id.run do
  for j in [0:8] do
    let k := 7 - j
    let w := v[k]!
    if w != 0 then return some (k.toUInt32 * 32 + w.toNat.log2.toUInt32)
  return none

/-- Processor priority: the TPR, or the class of the highest in-service vector if that is higher. -/
def ppr (a : Apic) : UInt32 :=
  let isrv := (highest a.isr).getD 0
  if (a.tpr >>> 4) ≥ (isrv >>> 4) then a.tpr &&& 0xFF else isrv &&& 0xF0

/-- Arbitration priority (APM 16.6.2): the highest of the task priority and the classes of the
highest ISR and IRR vectors; the sub-class is the TPR's if the TPR wins, else 0. -/
def apr (a : Apic) : UInt32 :=
  let c := max (((highest a.isr).getD 0) >>> 4) (((highest a.irr).getD 0) >>> 4)
  if (a.tpr >>> 4) ≥ c then a.tpr &&& 0xFF else c <<< 4

/-- The requests that take part in the priority selection: IRR, masked by IER while IERN = 1. -/
@[inline] def reqs (a : Apic) : Array UInt32 :=
  if a.extCtl &&& 1 == 0 then a.irr else (Array.range 8).map fun k => a.irr[k]! &&& a.ier[k]!

/-- The fixed interrupt the APIC presents to the processor: the highest requested vector whose
priority class is above the processor priority. -/
def pending (a : Apic) : Option UInt32 :=
  if !a.swEnabled then none else
  match highest a.reqs with
  | some v => if (v >>> 4) > (a.ppr >>> 4) then some v else none
  | none => none

/-- Whether the PIC's INTR reaches the processor (LINT0 unmasked in ExtINT mode, or APIC off). -/
@[inline] def picPasses (a : Apic) : Bool :=
  !a.enabled || (a.lvt[3]! &&& 0x10000 == 0 && (a.lvt[3]! >>> 8) &&& 7 == 7)

/-- LINT0 is unmasked in a mode other than ExtINT: its input is watched for edges (`lint0Sync`). -/
@[inline] def lint0Live (a : Apic) : Bool :=
  a.enabled && a.lvt[3]! &&& 0x10000 == 0 && (a.lvt[3]! >>> 8) &&& 7 != 7

/-- LVT entry `k`: 0..5 the standard entries, 6..9 the extended ones. -/
@[inline] def lvtAt (a : Apic) (k : Nat) : UInt32 := if k < 6 then a.lvt[k]! else a.xlvt[k - 6]!

/-- Enter a legal fixed vector into IRR (and TMR) unless the APIC is software-disabled. -/
@[inline] def rawAccept (a : Apic) (v : UInt32) (level : Bool) : Apic :=
  if !a.swEnabled then a else { a with irr := setBit a.irr v true, tmr := setBit a.tmr v level }

/-- A local interrupt through LVT entry `k` (APM 16.4): nothing if masked; a fixed vector is
accepted (an illegal one only records RIV here, see `localInt`); SMI, NMI and ExtINT go to the core;
other message types are reserved and deliver nothing. `level`: a level-triggered LINT0/LINT1. -/
def lvtFire (a : Apic) (k : Nat) (level : Bool := false) : Apic :=
  let e := a.lvtAt k
  if !a.enabled || e &&& 0x10000 != 0 then a else
  match (e >>> 8) &&& 7 with
  | 0 =>
    let v := e &&& 0xFF
    if v < 16 then { a with errs := a.errs ||| Esr.RIV } else a.rawAccept v level
  | 2 => { a with smi := true }
  | 4 => { a with nmi := true }
  | 7 => { a with extInt := true }
  | _ => a

/-- Record an APIC error and raise the error interrupt (LVT error entry). -/
def error (a : Apic) (bits : UInt32) : Apic := { a with errs := a.errs ||| bits }.lvtFire 5

/-- A local interrupt through LVT entry `k`: an illegal fixed vector is an error (RIV, APM 16.4). -/
def localInt (a : Apic) (k : Nat) (level : Bool := false) : Apic :=
  let e := a.lvtAt k
  if k != 5 && a.enabled && e &&& 0x10700 == 0 && e &&& 0xFF < 16 then a.error Esr.RIV
  else a.lvtFire k level

/-- Accept a fixed (or lowest-priority) interrupt message: dropped by a software-disabled APIC;
vectors 0..15 are illegal (RIV). -/
def acceptFixed (a : Apic) (v : UInt32) (level : Bool := false) : Apic :=
  if !a.swEnabled then a else if v < 16 then a.error Esr.RIV else a.rawAccept v level

/-- Interrupt acknowledge: the vector moves from IRR to ISR. -/
def ack (a : Apic) (v : UInt32) : Apic := { a with irr := setBit a.irr v false, isr := setBit a.isr v true }

/-- End of interrupt for in-service vector `v`: returns `v` if it was level-triggered (TMR), for the
EOI message to the I/O APIC, and clears the remote IRR of a level LINT0/LINT1 entry with vector `v`. -/
def eoiVec (a : Apic) (v : UInt32) : Apic × Option UInt32 :=
  if !getBit a.isr v then (a, none) else
  let lvl := getBit a.tmr v
  let a := { a with isr := setBit a.isr v false, tmr := setBit a.tmr v false }
  if !lvl then (a, none) else
  let clr := fun (e : UInt32) => if e &&& 0xFF == v then e &&& ~~~0x4000 else e
  ({ a with lvt := (a.lvt.set! 3 (clr a.lvt[3]!)).set! 4 (clr a.lvt[4]!) }, some v)

/-- EOI: retire the highest in-service vector (see `eoiVec`). -/
def eoi (a : Apic) : Apic × Option UInt32 :=
  match highest a.isr with
  | some v => a.eoiVec v
  | none => (a, none)

/-- Divide configuration register to divider: 2, 4, ..., 128, 1. -/
def divider (cfg : UInt32) : UInt64 :=
  let k := (cfg &&& 3) ||| ((cfg >>> 1) &&& 4)
  if k == 7 then 1 else (2 : UInt64) <<< k.toUInt64

@[inline] def periodic (a : Apic) : Bool := (a.lvt[0]! >>> 17) &&& 1 != 0

/-- Current count of the timer at instruction count `now`. -/
def currentCount (a : Apic) (now : UInt64) : UInt32 :=
  if a.initCount == 0 then 0 else
  let el := (now - a.timerStart) / a.timerDiv
  let n := a.initCount.toUInt64
  if a.periodic then (n - el % n).toUInt32 else if el ≥ n then 0 else (n - el).toUInt32

/-- The timer expired: raise its local interrupt (unless masked) and re-arm a periodic timer. -/
def timerFired (a : Apic) : Apic :=
  let a := a.localInt 0
  if a.periodic && a.initCount != 0 then
    { a with timerNext := a.timerNext + a.timerDiv * a.initCount.toUInt64 }
  else { a with timerNext := never }

/-- Register read at offset `off` (16-byte aligned) in xAPIC layout; `none` for an unimplemented
offset (illegal register address). EOI and SEOI are write-only and read 0. -/
def read (a : Apic) (off : UInt32) (now : UInt64) : Option UInt32 :=
  match off with
  | 0x20 => some (a.id <<< 24)
  | 0x30 => some version
  | 0x80 => some a.tpr
  | 0x90 => some a.apr
  | 0xA0 => some a.ppr
  | 0xB0 => some 0
  | 0xC0 => some a.rrr
  | 0xD0 => some a.ldr
  | 0xE0 => some a.dfr
  | 0xF0 => some a.svr
  | 0x280 => some a.esr
  | 0x300 => some a.icrLo
  | 0x310 => some a.icrHi
  | 0x380 => some a.initCount
  | 0x390 => some (a.currentCount now)
  | 0x3E0 => some a.divCfg
  | 0x400 => some extFeature
  | 0x410 => some a.extCtl
  | 0x420 => some 0
  | _ =>
    if 0x100 ≤ off && off < 0x180 then some a.isr[((off - 0x100) >>> 4).toNat]!
    else if 0x180 ≤ off && off < 0x200 then some a.tmr[((off - 0x180) >>> 4).toNat]!
    else if 0x200 ≤ off && off < 0x280 then some a.irr[((off - 0x200) >>> 4).toNat]!
    else if 0x320 ≤ off && off < 0x380 then some a.lvt[((off - 0x320) >>> 4).toNat]!
    else if 0x480 ≤ off && off < 0x500 then some a.ier[((off - 0x480) >>> 4).toNat]!
    else if 0x500 ≤ off && off < 0x540 then some a.xlvt[((off - 0x500) >>> 4).toNat]!
    else none

/-- Writable bits of the LVT entries (APM figures 16-8, 16-12 to 16-15: the error, thermal and
performance-counter entries have a message type; LINT0/1 also polarity and trigger mode). The
read-only remote IRR (bit 14) and delivery status (bit 12) are not written. -/
def lvtMask : Array UInt32 := #[0x300FF, 0x107FF, 0x107FF, 0x1A7FF, 0x1A7FF, 0x107FF]
/-- Writable bits of the extended LVT entries (vector, message type, mask). -/
def xlvtMask : UInt32 := 0x107FF

/-- Register writes that only change this APIC's state, at offset `off` (16-byte aligned, xAPIC
layout) at instruction count `now`; `none` for an unimplemented offset. EOI (B0h), ICR low (300h) and
SEOI (420h) have effects beyond the APIC and are handled by `Machine.apicWrite`; writes to read-only
registers are ignored. -/
def write (a : Apic) (off v : UInt32) (now : UInt64) : Option Apic :=
  match off with
  | 0x20 => some { a with id := v >>> 24 }
  | 0x80 => some { a with tpr := v &&& 0xFF }
  | 0xD0 => some { a with ldr := v &&& 0xFF000000 }
  | 0xE0 => some { a with dfr := v ||| 0x0FFFFFFF }
  | 0xF0 =>
    let a := { a with svr := v &&& 0x3FF }
    -- software disable masks every LVT entry (APM 16.3.1)
    some (if v &&& 0x100 == 0 then
      { a with lvt := a.lvt.map (· ||| 0x10000), xlvt := a.xlvt.map (· ||| 0x10000) } else a)
  -- ESR: a write records the errors detected since the last write and clears them (APM 16.4.6)
  | 0x280 => some { a with esr := a.errs, errs := 0 }
  | 0x310 => some { a with icrHi := v &&& 0xFF000000 }
  | 0x380 =>
    let d := divider a.divCfg
    some { a with initCount := v, timerStart := now, timerDiv := d,
                  timerNext := if v == 0 then never else now + d * v.toUInt64 }
  | 0x3E0 => some { a with divCfg := v &&& 0xB }
  | 0x410 => some { a with extCtl := v &&& 7 }
  | 0x30 | 0x90 | 0xA0 | 0xC0 | 0x390 | 0x400 => some a
  | _ =>
    if 0x100 ≤ off && off < 0x280 then some a   -- ISR, TMR, IRR: read-only
    else if 0x320 ≤ off && off < 0x380 then
      let k := ((off - 0x320) >>> 4).toNat
      let v := (v &&& lvtMask[k]!) ||| (a.lvt[k]! &&& 0x4000)
      some { a with lvt := a.lvt.set! k (if a.swEnabled then v else v ||| 0x10000) }
    else if 0x480 ≤ off && off < 0x500 then
      some (if a.extCtl &&& 1 == 0 then a else { a with ier := a.ier.set! ((off - 0x480) >>> 4).toNat v })
    else if 0x500 ≤ off && off < 0x540 then
      let v := v &&& xlvtMask
      some { a with xlvt := a.xlvt.set! ((off - 0x500) >>> 4).toNat (if a.swEnabled then v else v ||| 0x10000) }
    else none

/-- The APIC after RESET or INIT (APM table 16-2; 16.10): every register at its reset value except
the base address, AE, EXTD, BSC and the APIC ID. In x2APIC mode the LDR is the derived logical
x2APIC ID. The boot processor's LINT0 is left in ExtINT mode (virtual wire), as the firmware sets it
up: the model's initial state of the BSP (and its state after a global disable, as before). The
messages already passed to the core are kept: INIT holds SMI and NMI pending (APM 16.5). -/
def reset (a : Apic) : Apic :=
  let r : Apic := { base := a.base, baseHi := a.baseHi, enabled := a.enabled, x2 := a.x2, bsp := a.bsp,
                    initId := a.initId, id := a.id, smi := a.smi, nmi := a.nmi,
                    lvt := #[0x10000, 0x10000, 0x10000, if a.bsp then 0x700 else 0x10000, 0x10000, 0x10000] }
  let r := if a.x2 then { r with ldr := ((a.id >>> 4) <<< 16) ||| ((1 : UInt32) <<< (a.id &&& 0xF)) } else r
  r.withMmio

/-- The APIC of CPU `k` at power-up (APM table 16-2): initial ID `k`, AE = 1, BSC for CPU 0. -/
def powerUp (k : Nat) : Apic :=
  ({ bsp := k == 0, initId := k.toUInt32, id := k.toUInt32 } : Apic).reset

end Apic

/-! ## Interrupt messages

A message on the APIC bus (APM 16.2, 16.5): sent by a local APIC (ICR, `src` = the sending CPU) or
the I/O APIC (`src = none`). -/

structure Msg where
  /-- Message type: 0 fixed, 1 lowest priority, 2 SMI, 4 NMI, 5 INIT, 6 STARTUP, 7 ExtINT. -/
  mode : UInt32
  vec : UInt32 := 0
  /-- Trigger mode (level) and level (assert) bits. -/
  level : Bool := false
  assert : Bool := true
  /-- Destination ID: 8 bits, or 32 bits for an x2APIC ICR (`x2`). -/
  dest : UInt32 := 0
  logical : Bool := false
  /-- Destination shorthand: 0 none, 1 self, 2 all including self, 3 all excluding self. -/
  sh : UInt32 := 0
  x2 : Bool := false
  src : Option Nat := none
  deriving Repr, Inhabited

/-- Whether APIC `a` (CPU `k`) is a destination of `msg` (APM 16.6.1, 16.14). -/
def Msg.targets (msg : Msg) (k : Nat) (a : Apic) : Bool :=
  a.enabled &&
  match msg.sh with
  | 1 => msg.src == some k
  | 2 => true
  | 3 => msg.src != some k
  | _ =>
    if a.x2 then
      let d := if msg.x2 then msg.dest else if msg.dest &&& 0xFF == 0xFF then 0xFFFFFFFF else msg.dest
      d == 0xFFFFFFFF ||
      (if msg.logical then d >>> 16 == a.ldr >>> 16 && d &&& a.ldr &&& 0xFFFF != 0 else d == a.id)
    else
      let d := msg.dest &&& 0xFF
      d == 0xFF ||
      (if !msg.logical then d == a.id &&& 0xFF
       else if a.dfr >>> 28 == 0xF then (a.ldr >>> 24) &&& d != 0
       else (a.ldr >>> 28) == (d >>> 4) && (a.ldr >>> 24) &&& d &&& 0xF != 0)

/-! ## I/O APIC (Intel 82093AA)

At 0xFEC00000 (`ioApicBase`): IOREGSEL at offset 00h, IOWIN at 10h (the page is decoded modulo
100h, as QEMU does). Registers: ID (index 0, bits 27:24), version (1: 00170011h, 24 entries, the
82093AA's version 11h; QEMU's default is 20h), arbitration ID (2, read-only, = ID) and 24 redirection
entries (10h + 2n: bits 31:0, 11h + 2n: bits 63:32) with vector, delivery mode (fixed, lowest
priority, SMI, NMI, INIT, ExtINT), destination mode, delivery status (always 0: messages are
delivered at once), polarity, remote IRR, trigger mode, mask and destination (bits 63:56).

Inputs (`Machine.setIrq`): ISA IRQ n drives pin n, except IRQ 0 (PIT channel 0), which drives pin 2
(the usual override, also QEMU's wiring); the UART is IRQ 4, the RTC IRQ 8 (the model's RTC raises no
interrupts). Pin 0 is not connected. A pin is asserted when its level differs from the polarity bit
(1 = active low). Edge-triggered entries send a message on each assertion while unmasked (masked
edges are lost); level-triggered entries send one while asserted, unmasked and remote IRR is clear,
then set remote IRR, which an EOI for its vector from a local APIC clears (`Machine.ioapicEoi`).
Writing an entry with edge trigger mode clears its remote IRR (as QEMU, and as Linux relies on for
the 82093AA, which has no EOI register). -/

def ioApicBase : UInt32 := 0xFEC00000

structure IoApic where
  id : UInt32 := 0
  sel : UInt32 := 0
  redir : Array UInt64 := Array.replicate 24 0x10000
  /-- Input pin levels (bit n: pin n). -/
  lines : UInt32 := 0
  deriving Repr, Inhabited

namespace IoApic

def pins : Nat := 24
def version : UInt32 := 0x00170011
/-- Writable bits of a redirection entry: vector, delivery mode, destination mode, polarity, trigger
mode, mask, destination. -/
def rwMask : UInt64 := 0xFF0000000001AFFF

@[inline] def entry (s : IoApic) (p : Nat) : UInt64 := s.redir[p]!

/-- Pin `p` is asserted: its level differs from the polarity bit (bit 13, 1 = active low). -/
@[inline] def asserted (s : IoApic) (p : Nat) : Bool :=
  ((s.lines >>> p.toUInt32) &&& 1 != 0) != ((s.entry p >>> 13) &&& 1 != 0)

/-- IOWIN read of the selected register. -/
def readWin (s : IoApic) : UInt32 :=
  match s.sel with
  | 0 | 2 => (s.id &&& 0xF) <<< 24
  | 1 => version
  | r =>
    if 0x10 ≤ r && r < 0x40 then
      let e := s.entry ((r - 0x10) >>> 1).toNat
      if r &&& 1 == 0 then e.toUInt32 else (e >>> 32).toUInt32
    else 0

/-- IOWIN write of the selected register; returns the redirection entry written, if any. -/
def writeWin (s : IoApic) (v : UInt32) : IoApic × Option Nat :=
  match s.sel with
  | 0 => ({ s with id := (v >>> 24) &&& 0xF }, none)
  | r =>
    if 0x10 ≤ r && r < 0x40 then
      let p := ((r - 0x10) >>> 1).toNat
      let e := s.entry p
      let e := if r &&& 1 == 0 then (e &&& 0xFFFFFFFF00000000) ||| v.toUInt64
               else (e &&& 0xFFFFFFFF) ||| (v.toUInt64 <<< 32)
      let e := (e &&& rwMask) ||| (s.entry p &&& 0x5000)
      -- edge trigger mode: no remote IRR
      let e := if e &&& 0x8000 == 0 then e &&& ~~~0x4000 else e
      ({ s with redir := s.redir.set! p e }, some p)
    else (s, none)

/-- The message entry `p` sends (8-bit destination, APM 16.6.1). -/
def msg (s : IoApic) (p : Nat) : Msg :=
  let e := s.entry p
  { mode := ((e >>> 8) &&& 7).toUInt32, vec := (e &&& 0xFF).toUInt32, level := e &&& 0x8000 != 0,
    dest := (e >>> 56).toUInt32, logical := e &&& 0x800 != 0 }

end IoApic


end X86
