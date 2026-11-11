import X86.Word
/-!
# Platform devices

Minimal, deterministic models of the PC devices Linux needs:

* `Pic`  — Intel 8259A programmable interrupt controller (master + slave pair)
* `Pit`  — Intel 8254 programmable interval timer (channels 0 and 2)
* `Uart` — NS16550A serial port (COM1)
* CMOS RTC (fixed clock)
* `Apic` — the local APIC (memory-mapped; see `Machine.physRd`)

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

/-! ## Local APIC (xAPIC, single processor)

Memory-mapped at `IA32_APIC_BASE` (default 0xFEE00000). Implemented: ID, version, TPR, PPR, EOI,
LDR, DFR, SVR, ISR/TMR/IRR, ESR, ICR (fixed and lowest-priority IPIs to this processor), the six
LVT entries and the timer (one-shot and periodic, counting at one tick per instruction before the
divider). The PIC reaches the processor through LINT0 in ExtINT mode (virtual wire, the reset state
of the boot processor as set up by firmware), or directly while the APIC is globally disabled.
Not modelled: NMI/SMI/INIT/SIPI delivery modes, TSC-deadline mode, thermal and performance
interrupts, APIC error conditions (ESR stays 0) and x2APIC. -/

structure Apic where
  /-- IA32_APIC_BASE: base address (bits 31:12) and global enable (bit 11). -/
  base : UInt32 := 0xFEE00000
  enabled : Bool := true
  id : UInt32 := 0
  tpr : UInt32 := 0
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
  deriving Repr, Inhabited

namespace Apic

def never : UInt64 := 0xFFFFFFFFFFFFFFFF

@[inline] def swEnabled (a : Apic) : Bool := a.enabled && a.svr &&& 0x100 != 0

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

/-- The fixed interrupt the APIC presents to the processor: the highest requested vector whose
priority class is above the processor priority. -/
def pending (a : Apic) : Option UInt32 :=
  if !a.swEnabled then none else
  match highest a.irr with
  | some v => if (v >>> 4) > (a.ppr >>> 4) then some v else none
  | none => none

/-- Whether the PIC's INTR reaches the processor (LINT0 unmasked in ExtINT mode, or APIC off). -/
@[inline] def picPasses (a : Apic) : Bool :=
  !a.enabled || (a.lvt[3]! &&& 0x10000 == 0 && (a.lvt[3]! >>> 8) &&& 7 == 7)

/-- Accept a fixed interrupt (vectors 0..15 are illegal and dropped). -/
def accept (a : Apic) (v : UInt32) (level : Bool := false) : Apic :=
  if v < 16 || !a.swEnabled then a else { a with irr := setBit a.irr v true, tmr := setBit a.tmr v level }

/-- Interrupt acknowledge: the vector moves from IRR to ISR. -/
def ack (a : Apic) (v : UInt32) : Apic := { a with irr := setBit a.irr v false, isr := setBit a.isr v true }

/-- EOI: retire the highest in-service vector. -/
def eoi (a : Apic) : Apic :=
  match highest a.isr with
  | some v => { a with isr := setBit a.isr v false, tmr := setBit a.tmr v false }
  | none => a

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

/-- The timer expired: request its vector (unless masked) and re-arm a periodic timer. -/
def timerFired (a : Apic) : Apic :=
  let t := a.lvt[0]!
  let a := if t &&& 0x10000 == 0 then a.accept (t &&& 0xFF) else a
  if a.periodic && a.initCount != 0 then
    { a with timerNext := a.timerNext + a.timerDiv * a.initCount.toUInt64 }
  else { a with timerNext := never }

/-- Register read at offset `off` (16-byte aligned). -/
def read (a : Apic) (off : UInt32) (now : UInt64) : UInt32 :=
  match off with
  | 0x20 => a.id
  | 0x30 => 0x00050014
  | 0x80 => a.tpr
  | 0xA0 => a.ppr
  | 0xD0 => a.ldr
  | 0xE0 => a.dfr
  | 0xF0 => a.svr
  | 0x280 => 0
  | 0x300 => a.icrLo
  | 0x310 => a.icrHi
  | 0x380 => a.initCount
  | 0x390 => a.currentCount now
  | 0x3E0 => a.divCfg
  | _ =>
    if 0x100 ≤ off && off < 0x180 then a.isr[((off - 0x100) >>> 4).toNat]!
    else if 0x180 ≤ off && off < 0x200 then a.tmr[((off - 0x180) >>> 4).toNat]!
    else if 0x200 ≤ off && off < 0x280 then a.irr[((off - 0x200) >>> 4).toNat]!
    else if 0x320 ≤ off && off < 0x380 then a.lvt[((off - 0x320) >>> 4).toNat]!
    else 0

/-- Writable bits of the LVT entries. -/
def lvtMask : Array UInt32 := #[0x300FF, 0x107FF, 0x107FF, 0x1A7FF, 0x1A7FF, 0x100FF]

/-- The ICR was written: deliver the IPI if it targets this processor. -/
def sendIpi (a : Apic) : Apic :=
  let lo := a.icrLo
  let dest := a.icrHi >>> 24
  let toSelf := match (lo >>> 18) &&& 3 with
    | 1 | 2 => true
    | 3 => false
    | _ =>
      if lo &&& 0x800 == 0 then dest == 0xFF || dest == (a.id >>> 24)
      else if a.dfr >>> 28 == 0xF then (a.ldr >>> 24) &&& dest != 0
      else (a.ldr >>> 28) == (dest >>> 4) && (a.ldr >>> 24) &&& dest &&& 0xF != 0
  let mode := (lo >>> 8) &&& 7
  if toSelf && (mode == 0 || mode == 1) then a.accept (lo &&& 0xFF) (lo &&& 0x8000 != 0) else a

/-- Register write at offset `off` (16-byte aligned) at instruction count `now`. -/
def write (a : Apic) (off v : UInt32) (now : UInt64) : Apic :=
  match off with
  | 0x20 => { a with id := v &&& 0xFF000000 }
  | 0x80 => { a with tpr := v &&& 0xFF }
  | 0xB0 => a.eoi
  | 0xD0 => { a with ldr := v &&& 0xFF000000 }
  | 0xE0 => { a with dfr := v ||| 0x0FFFFFFF }
  | 0xF0 =>
    let a := { a with svr := v &&& 0x3FF }
    -- software disable masks every LVT entry
    if v &&& 0x100 == 0 then { a with lvt := a.lvt.map (· ||| 0x10000) } else a
  | 0x300 => { a with icrLo := v &&& 0xCCFFF }.sendIpi
  | 0x310 => { a with icrHi := v &&& 0xFF000000 }
  | 0x380 =>
    let d := divider a.divCfg
    { a with initCount := v, timerStart := now, timerDiv := d,
             timerNext := if v == 0 then never else now + d * v.toUInt64 }
  | 0x3E0 => { a with divCfg := v &&& 0xB }
  | _ =>
    if 0x320 ≤ off && off < 0x380 then
      let k := ((off - 0x320) >>> 4).toNat
      let v := v &&& lvtMask[k]!
      { a with lvt := a.lvt.set! k (if a.swEnabled then v else v ||| 0x10000) }
    else a

end Apic

end X86
