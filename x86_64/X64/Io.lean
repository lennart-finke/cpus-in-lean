import X64.Machine
/-!
# I/O port bus

Routes `IN`/`OUT` to the device models and keeps the cached interrupt state
(`Machine.intr`, `Machine.timerAt`) consistent with the devices.
-/
namespace X64

namespace Machine

/-- Highest-priority request of the master PIC, including the cascade input. -/
def masterHighest (m : Machine) : Option UInt8 :=
  m.pic0.highest (if (m.pic1.highest).isSome then 4 else 0)

/-- Recompute the cached INTR line (the slave's INT output drives master input 2). -/
def syncIntr (m : Machine) : Machine :=
  { m with intr := m.masterHighest.isSome }

/-- Propagate the UART interrupt output to IRQ4. -/
def syncUart (m : Machine) : Machine :=
  { m with pic0 := m.pic0.setLine 4 m.uart.irq }.syncIntr

def syncTimer (m : Machine) : Machine :=
  { m with timerAt := match m.pit.ch0.nextFire with
                      | some t => tickToIcount t
                      | none => 0xFFFFFFFFFFFFFFFF }

/-- PIT channel 0 output rose: pulse IRQ0 and schedule the next edge. -/
def timerFire (m : Machine) : Machine :=
  let pic0 := (m.pic0.setLine 0 true).setLine 0 false
  { m with pic0, pit := { m.pit with ch0 := m.pit.ch0.fired } }.syncTimer.syncIntr

/-- Interrupt acknowledge cycle: returns the vector supplied by the PICs. -/
def intAck (m : Machine) : UInt8 × Machine :=
  match m.masterHighest with
  | some 2 =>
    match m.pic1.highest with
    | some k =>
      let m := { m with pic0 := m.pic0.ack 2, pic1 := m.pic1.ack k }
      (m.pic1.vecBase + k, m.syncIntr)
    | none => (m.pic1.vecBase + 7, m.syncIntr)
  | some k =>
    let m := { m with pic0 := m.pic0.ack k }
    (m.pic0.vecBase + k, m.syncIntr)
  | none => (m.pic0.vecBase + 7, m)

def in8 (m : Machine) (port : UInt32) : UInt8 × Machine :=
  let t := pitTick m.icount
  match port with
  | 0x20 => (m.pic0.read false, m)
  | 0x21 => (m.pic0.read true, m)
  | 0xA0 => (m.pic1.read false, m)
  | 0xA1 => (m.pic1.read true, m)
  | 0x40 => let (v, c) := m.pit.ch0.readCount t; (v, { m with pit := { m.pit with ch0 := c } })
  | 0x41 => let (v, c) := m.pit.ch1.readCount t; (v, { m with pit := { m.pit with ch1 := c } })
  | 0x42 => let (v, c) := m.pit.ch2.readCount t; (v, { m with pit := { m.pit with ch2 := c } })
  | 0x61 =>
    let out2 : UInt8 := if m.pit.p61 &&& 1 != 0 && m.pit.ch2.out t then 0x20 else 0
    let refresh : UInt8 := if (t / 18) % 2 == 1 then 0x10 else 0
    (m.pit.p61 ||| out2 ||| refresh, m)
  | 0x70 => (m.cmosIdx, m)
  | 0x71 =>
    let i := (m.cmosIdx &&& 0x7F).toNat
    let v := m.cmos.get! i
    (v, if i == 0x0C then { m with cmos := m.cmos.set! i 0 } else m)
  | 0x4D0 => (m.pic0.elcr, m)
  | 0x4D1 => (m.pic1.elcr, m)
  | _ =>
    if 0x3F8 ≤ port && port ≤ 0x3FF then
      let (v, u) := m.uart.read (port - 0x3F8)
      (v, { m with uart := u }.syncUart)
    else (0xFF, m)

def out8 (m : Machine) (port : UInt32) (v : UInt8) : Machine :=
  let t := pitTick m.icount
  match port with
  | 0x20 => { m with pic0 := m.pic0.write false v }.syncIntr
  | 0x21 => { m with pic0 := m.pic0.write true v }.syncIntr
  | 0xA0 => { m with pic1 := m.pic1.write false v }.syncIntr
  | 0xA1 => { m with pic1 := m.pic1.write true v }.syncIntr
  | 0x40 => { m with pit := { m.pit with ch0 := m.pit.ch0.writeCount v t } }.syncTimer
  | 0x41 => { m with pit := { m.pit with ch1 := m.pit.ch1.writeCount v t } }
  | 0x42 => { m with pit := { m.pit with ch2 := m.pit.ch2.writeCount v t } }
  | 0x43 =>
    let ch := v >>> 6
    if ch == 0 then { m with pit := { m.pit with ch0 := m.pit.ch0.control v t } }.syncTimer
    else if ch == 1 then { m with pit := { m.pit with ch1 := m.pit.ch1.control v t } }
    else if ch == 2 then { m with pit := { m.pit with ch2 := m.pit.ch2.control v t } }
    else m -- read-back command not modelled
  | 0x61 => { m with pit := { m.pit with p61 := v &&& 3 } }
  | 0x70 => { m with cmosIdx := v }
  | 0x71 => let i := (m.cmosIdx &&& 0x7F).toNat
            if i ≥ 0x0E then { m with cmos := m.cmos.set! i v } else m
  | 0x4D0 => { m with pic0 := { m.pic0 with elcr := v &&& 0xF8 } }.syncIntr
  | 0x4D1 => { m with pic1 := { m.pic1 with elcr := v &&& 0xDE } }.syncIntr
  | _ =>
    if 0x3F8 ≤ port && port ≤ 0x3FF then
      { m with uart := m.uart.write (port - 0x3F8) v }.syncUart
    else m

end Machine

def portIn (port : UInt32) (sz : Sz) : M UInt64 := fun m =>
  let (b0, m) := m.in8 port
  if sz == 1 then .ok b0.toUInt64 m else
  let (b1, m) := m.in8 (port + 1)
  if sz == 2 then .ok (b0.toUInt64 ||| (b1.toUInt64 <<< 8)) m else
  let (b2, m) := m.in8 (port + 2)
  let (b3, m) := m.in8 (port + 3)
  .ok (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24)) m

def portOut (port : UInt32) (sz : Sz) (v : UInt64) : M Unit := fun m =>
  let m := m.out8 port v.toUInt8
  if sz == 1 then .ok () m else
  let m := m.out8 (port + 1) (v >>> 8).toUInt8
  if sz == 2 then .ok () m else
  let m := m.out8 (port + 2) (v >>> 16).toUInt8
  .ok () (m.out8 (port + 3) (v >>> 24).toUInt8)

end X64
