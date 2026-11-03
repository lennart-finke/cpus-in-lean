import X86.Word
/-!
# Platform devices

Minimal, deterministic models of the PC devices Linux needs:

* `Pic`  — Intel 8259A programmable interrupt controller (master + slave pair)
* `Pit`  — Intel 8254 programmable interval timer (channels 0 and 2)
* `Uart` — NS16550A serial port (COM1)
* CMOS RTC (fixed clock)

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

end X86
