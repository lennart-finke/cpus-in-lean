import X86.Machine
import X86.Cpuid
/-!
# I/O port bus

Routes `IN`/`OUT` to the device models and keeps the cached interrupt state
(`Machine.intr`, `Machine.timerAt`) consistent with the devices.
-/
namespace X86

namespace Machine

/-- Propagate the UART interrupt output to IRQ4 (PIC and I/O APIC). -/
def syncUart (m : Machine) : Machine :=
  (m.setIrq 4 m.uart.irq).syncIntr

/-- A timer event is due: PIT channel 0 output rose (pulse IRQ0 and schedule the next edge),
and/or the APIC timer expired. -/
def timerFire (m : Machine) : Machine :=
  let m := match m.pit.ch0.nextFire with
    | some t =>
      if tickToIcount t ≤ m.icount then
        let m := (m.setIrq 0 true).setIrq 0 false
        { m with pit := { m.pit with ch0 := m.pit.ch0.fired } }
      else m
    | none => m
  let m := if m.apic.timerNext ≤ m.icount then { m with apic := m.apic.timerFired } else m
  m.syncTimer.syncApic

/-- Interrupt acknowledge cycle: returns the vector supplied by the local APIC (fixed interrupt)
or, through LINT0 or an external-interrupt message (ExtINT), by the PICs. -/
def intAck (m : Machine) : UInt8 × Machine :=
  match m.apic.pending with
  | some v => (v.toUInt8, { m with apic := m.apic.ack v }.syncIntr)
  | none =>
  let m := if m.apic.extInt then { m with apic := { m.apic with extInt := false } }.syncIntr else m
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
  | 0xB2 => (m.apmCnt, m)
  | 0xB3 => (m.apmSts, m)
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
  -- APM control port: an SMI to the CPU that executes the OUT. Which CPUs a chipset signals is the
  -- chipset's choice and not settled by a source for the 7742's FCH (open question): QEMU's PIIX4
  -- raises it on the first CPU, its ICH9 on the writing CPU unless firmware negotiated broadcast SMIs.
  | 0xB2 => { m with apmCnt := v, smiPending := true }
  | 0xB3 => { m with apmSts := v }
  | 0x4D0 => { m with pic0 := { m.pic0 with elcr := v &&& 0xF8 } }.syncIntr
  | 0x4D1 => { m with pic1 := { m.pic1 with elcr := v &&& 0xDE } }.syncIntr
  | _ =>
    if 0x3F8 ≤ port && port ≤ 0x3FF then
      { m with uart := m.uart.write (port - 0x3F8) v }.syncUart
    else m

/-! ## IA32_APIC_BASE (MSR 1Bh; AMD APM vol. 2, 16.3.1, 16.9) -/

/-- The register as RDMSR reads it: base address bits 47:12, AE (bit 11), EXTD (bit 10), BSC (bit 8). -/
def apicBaseRd (m : Machine) : UInt64 :=
  let a := m.apic
  (a.baseHi.toUInt64 <<< 32) ||| a.base.toUInt64 ||| (if a.enabled then 0x800 else 0) |||
    (if a.x2 then 0x400 else 0) ||| (if a.bsp then 0x100 else 0)

/-- WRMSR to IA32_APIC_BASE; `none` is #GP(0). Reserved: bits 63:48 (above MAXPHYADDR 48), 9 and 7:0,
and EXTD without CPUID x2APIC; BSC is read-only (written values are ignored). Mode transitions (APM
table 16-5, figure 16-32, 16.9.1): AE = 0 with EXTD = 1 is invalid, x2APIC mode can only be left to
the disabled state, and the disabled state can only be left to xAPIC mode. A global disable resets
the APIC (`Apic.reset`, keeping base, BSC and ID); entering x2APIC mode derives the logical x2APIC
ID (LDR = cluster ID[19:4] << 16 | 1 << ID[3:0], APM 16.14), does not preserve ICR high, and makes the
APIC ID written in xAPIC mode the x2APIC ID (APM 16.9.1). The mode is mirrored into
`Cpu.smpx.apicMode` (CPUID 8000_001E:EAX). -/
def apicBaseWr (m : Machine) (v : UInt64) : Option Machine :=
  let a := m.apic
  let ae := v &&& 0x800 != 0
  let ex := v &&& 0x400 != 0
  if v &&& 0xFFFF0000000002FF != 0 || (ex && !implemented .x2apic) then none
  else if !ae && ex then none
  else if a.x2 && ae && !ex then none
  else if !a.enabled && ae && ex then none
  else
    let wasEn := a.enabled
    let wasX2 := a.x2
    let a := { a with base := v.toUInt32 &&& 0xFFFFF000, baseHi := (v >>> 32).toUInt32 &&& 0xFFFF }
    let a := if !ae then ({ a with enabled := false, x2 := false } : Apic).reset
      else if !wasEn then { a with enabled := true }
      else if ex && !wasX2 then
        { a with x2 := true, icrHi := 0, ldr := ((a.id >>> 4) <<< 16) ||| ((1 : UInt32) <<< (a.id &&& 0xF)) }
      else a
    let mode : UInt8 := if !ae then 0 else if ex then 2 else 1
    some ({ m with apic := a.withMmio, cpu := { m.cpu with smpx := { m.cpu.smpx with apicMode := mode } } }
      |>.syncTimer |>.syncApic)

end Machine

/-- Read `sz` bytes from consecutive ports. -/
def portInRaw (port : UInt32) (sz : Sz) : M UInt32 := fun m =>
  let (b0, m) := m.in8 port
  if sz == 1 then .ok b0.toUInt32 m else
  let (b1, m) := m.in8 (port + 1)
  if sz == 2 then .ok (b0.toUInt32 ||| (b1.toUInt32 <<< 8)) m else
  let (b2, m) := m.in8 (port + 2)
  let (b3, m) := m.in8 (port + 3)
  .ok (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)) m

/-- Write `sz` bytes to consecutive ports. -/
def portOutRaw (port : UInt32) (sz : Sz) (v : UInt32) : M Unit := fun m =>
  let m := m.out8 port v.toUInt8
  if sz == 1 then .ok () m else
  let m := m.out8 (port + 1) (v >>> 8).toUInt8
  if sz == 2 then .ok () m else
  let m := m.out8 (port + 2) (v >>> 16).toUInt8
  .ok () (m.out8 (port + 3) (v >>> 24).toUInt8)

/-- IN: port read, recording I/O breakpoints. -/
def portIn (port : UInt32) (sz : Sz) : M UInt32 := do
  dbIo port sz.toUInt32
  portInRaw port sz

/-- OUT: port write, recording I/O breakpoints. -/
def portOut (port : UInt32) (sz : Sz) (v : UInt32) : M Unit := do
  dbIo port sz.toUInt32
  portOutRaw port sz v

end X86
