import X86.Ext.Vex
/-!
# General-purpose instruction extensions of Zen 2

Owner: the GPR-extension workstream. Sources: AMD64 APM vol. 3 rev. 3.33 (general-purpose and
system instruction reference, appendix E for CPUID), vol. 2 (MSRs), Intel SDM vol. 2 where the APM
is silent (said so at the place). State: `GprState` (`X86/State.lean`).

| instructions | encoding | CPUID feature |
|---|---|---|
| POPCNT | F3 0F B8 | `popcnt` |
| LZCNT | F3 0F BD | `abm` (otherwise BSR) |
| TZCNT | F3 0F BC | `bmi1` (otherwise BSF) |
| ANDN, BEXTR, BLSI, BLSMSK, BLSR | VEX.0F38 F2, F7, F3 /3 /2 /1 | `bmi1` |
| BZHI, PDEP, PEXT, MULX, SHLX, SARX, SHRX, RORX | VEX.0F38 F5, F6, F7, VEX.0F3A F0 | `bmi2` |
| ADCX, ADOX | 66 / F3 0F 38 F6 | `adx` |
| MOVBE | 0F 38 F0, F1 (memory) | `movbe` |
| CRC32 | F2 0F 38 F0, F1 | `sse42` (see below) |
| RDRAND, RDSEED, RDPID | 0F C7 /6, /7 (register), F3 0F C7 /7 | `rdrand`, `rdseed`, `rdpid` |
| RDTSCP, RDPRU, RDPMC | 0F 01 F9, 0F 01 FD, 0F 33 | `rdtscp`, `rdpru`, core |
| CLFLUSH, CLFLUSHOPT, CLWB, CLZERO | 0F AE /7, 66 0F AE /7, 66 0F AE /6 (memory), 0F 01 FC | `clfsh`, `clflushopt`, `clwb`, `clzero` |
| WBNOINVD | F3 0F 09 | `wbnoinvd` (otherwise WBINVD) |
| PREFETCH, PREFETCHW | 0F 0D /0../7 (memory) | `prefetchw` |
| MONITOR, MWAIT, MONITORX, MWAITX | 0F 01 C8, C9, FA, FB | `monitor`, `mwaitx` |
| MCOMMIT | F3 0F 01 FA | `mcommit` |

Every hook returns `none` for a form whose feature is not `implemented`, so that the fallback of
`X86/Dispatch.lean` (#UD, BSF/BSR, WBINVD, the core NOP of 0F 0D) runs as on a CPU without it.

## Modelling decisions

* **Undefined flags.** LZCNT/TZCNT (OF, SF, AF, PF), ANDN/BLSx/BZHI (AF, PF) and BEXTR (SF, AF, PF)
  leave flags undefined (APM rFLAGS tables). The model writes OF = AF = 0, SF = the result's top bit
  and PF = the parity of the result's low byte, as TCG does; what Zen 2 hardware writes is not known
  (the native campaign records them; the differential tests mask them).
* **BZHI with index ≥ 32** copies the source unchanged and sets CF: the pseudo-code of the SDM.
  The APM's prose ("index is set to op_size − 1") would also clear bit 31; it is read as the same
  saturation and not as a cleared top bit (UNCONFIRMED on hardware).
* **RORX with VEX.vvvv ≠ 1111b** executes: the APM lists no #UD for it (the SDM does); TCG executes
  it too. UNCONFIRMED on hardware (a native campaign family checks it).
* **CRC32** is gated on nothing: the instruction belongs to SSE4.2, whose CPUID bit the SSE
  workstream reports; until then CRC32 executes although CPUID does not advertise SSE4.2.
* **RDRAND/RDSEED** draw from a deterministic entropy source that is machine state: SplitMix64
  (Steele, Lea, Flood 2014; `GprState.rng`, reset 0) advanced once per instruction; the destination
  receives the low 16 or 32 bits of the output. They never fail: CF = 1, OF = SF = ZF = AF = PF = 0
  (APM RDRAND, RDSEED).
* **TSC** for RDTSCP is `Machine.icount`, as for the core's RDTSC (`Exec`, 0F 31). MPERF and APERF
  (RDPRU, MSRs E7h/E8h) count at the same rate (`icount` plus an offset set by WRMSR); the model has
  no P-states, and unlike hardware they also count while halted (HLT/MWAIT skip virtual time).
* **Performance counters** PerfCtr0..3 (MSRs C001_0004h..7, aliased to C001_0201h/3/5/7) and
  PerfCtr4..5 (C001_0209h/B, with `perfCtrExtCore`) hold what WRMSR writes (48 bits) but never
  count: no events are modelled. RDPMC reads them (APM RDPMC); NB and L2/L3 counters are absent
  (#GP). PerfEvtSel writes keep only the defined bits.
* **CLFLUSH/CLFLUSHOPT/CLWB** perform the segment and paging checks of a one-byte read (also on
  execute-only segments) and set the accessed bit like a load (APM); there is no cache, so nothing
  else happens. They do not trigger data breakpoints (not stated by the APM; UNCONFIRMED).
* **PREFETCH/PREFETCHW/PREFETCHlevel** never fault and have no effect (APM: a memory fault makes
  them NOPs); their register forms are #UD for 0F 0D (APM PREFETCH) and NOPs for 0F 18 (APM
  PREFETCHlevel lists no exception; core).
* **CLZERO** writes zeros to the 64-byte aligned *linear* line containing DS:rAX (rAX by the address
  size), checking the line like a 64-byte store (APM CLZERO: "all the segmentation and paging checks
  that a store of the specified cache line would perform"); whether the alignment applies to the
  offset or to the linear address is not documented (they agree for 64-byte aligned segment bases).
* **MONITOR/MONITORX** check DS:rAX like a one-byte read (no data breakpoint) and arm the monitor
  on its 64-byte physical line, remembering the line's contents. **MWAIT/MWAITX** do nothing unless
  the monitor is armed and the line still holds those contents (SDM MWAIT: no optimized state
  without a successful MONITOR; a store with a different value is how this single-CPU model sees a
  store to the line, silent stores are missed, and far control transfers between MONITOR and MWAIT
  do not disarm the monitor). Otherwise they disarm it and wait for the next wake-up event, the
  model's only one being an interrupt: with EFLAGS.IF = 1 this is HLT (`Cpu.halted`; `step` wakes on
  the interrupt and delivers it); with IF = 0 and ECX[0] = 1 (interrupts wake even when masked,
  CPUID 5:ECX.IBE) the wait ends at the next timer event without delivering it (immediately if an
  interrupt is already pending); with IF = 0 and ECX[0] = 0 it is HLT. MWAITX with ECX[1] = 1 and
  EBX ≠ 0 ends at the latest after EBX TSC ticks; this timed wait is computed by advancing
  `Machine.icount` (to the deadline, or to an earlier timer event when interrupts can wake it; a
  masked timer interrupt then ends the wait early, which the APM permits as an exit without stated
  reason only implicitly). MONITOR/MWAIT are #UD at CPL > 0 unless HWCR.MonMwaitUserEn (MSR
  C001_0015h bit 10); MONITORX/MWAITX run at any CPL.
* **HWCR** (C001_0015h) models only MonMwaitUserEn (bit 10, writable) and TscFreqSel (bit 24, reads
  1); writes to its other bits are ignored.
* **MCOMMIT** needs EFER.MCOMMIT (bit 17, else #UD); the model has no memory with delayed error
  reporting, so it always sets CF = 1 and clears OF, SF, ZF, AF, PF (APM MCOMMIT).
* **RDPRU** returns MPERF (ECX = 0) or APERF (ECX = 1) with CF = 1, and 0 with CF = 0 for any other
  ECX (APM: "Any unsupported ECX values return zero"; the APM marks CF as modified without saying
  how, so its value is UNCONFIRMED); OF, SF, ZF, AF, PF = 0. #UD at CPL > 0 with CR4.TSD.

## Hooks (called by `X86/Dispatch.lean`; `none` = not handled here, see `EXTENDING.md`)

* `op0F?`: F3 0F B8 / BC / BD, 0F 0D, 0F 18 (none: core NOP), 0F 33, F3 0F 09; the 0F 01 register
  forms C8, C9, F9, FA (MONITORX; F3: MCOMMIT), FB, FC, FD; 0F AE memory /7 (CLFLUSH), 66 /6 (CLWB),
  66 /7 (CLFLUSHOPT); 0F C7 register /6 (RDRAND), /7 (RDSEED), F3 /7 (RDPID).
* `map2?` (legacy 0F 38): F0/F1 (MOVBE; F2: CRC32), F6 (66: ADCX, F3: ADOX).
* `vex?`: VEX.0F38 F2, F3, F5, F6, F7 and VEX.0F3A F0 (all their forms, undefined ones #UD).
* `msr?`: TSC_AUX (C000_0103h), HWCR (C001_0015h), MPERF/APERF (E7h/E8h), PerfEvtSel/PerfCtr
  (C001_0000h..7, C001_0200h..B).
-/
namespace X86
namespace Gpr
open Flag

/-! ## Pure operations (used by the semantics and by the theorems in `Proofs/ExtGpr.lean`) -/

/-- Number of set bits (SWAR). -/
def popcount32 (x : UInt32) : UInt32 :=
  let x := x - ((x >>> 1) &&& 0x55555555)
  let x := (x &&& 0x33333333) + ((x >>> 2) &&& 0x33333333)
  let x := (x + (x >>> 4)) &&& 0x0F0F0F0F
  (x * 0x01010101) >>> 24

/-- Number of trailing zero bits of the low `bits` (16 or 32) bits; `bits` for zero. -/
def tzcnt (bits x : UInt32) : UInt32 :=
  let x := if bits == 16 then x &&& 0xFFFF else x
  if x == 0 then bits else popcount32 ((x &&& (0 - x)) - 1)

/-- Number of leading zero bits of a `bits`-bit (16 or 32) value; `bits` for zero. -/
def lzcnt (bits x : UInt32) : UInt32 :=
  let x := if bits == 16 then x &&& 0xFFFF else x
  let s := x ||| (x >>> 1)
  let s := s ||| (s >>> 2)
  let s := s ||| (s >>> 4)
  let s := s ||| (s >>> 8)
  let s := s ||| (s >>> 16)
  bits - popcount32 s

/-- The flags of LZCNT/TZCNT/BLSR/BLSMSK/...: CF and OF as given, ZF/SF/PF from the result, AF = 0. -/
@[inline] def bmiFlags (sz : Sz) (r : UInt32) (cf : Bool) : UInt32 :=
  szp sz r ||| (if cf then CF else 0)

/-- PDEP: deposit the low bits of `src` at the positions of the set bits of `mask`. -/
def pdep (src mask : UInt32) : UInt32 := Id.run do
  let mut r : UInt32 := 0
  let mut k : UInt32 := 0
  for i in [0:32] do
    let b : UInt32 := (1 : UInt32) <<< i.toUInt32
    if mask &&& b != 0 then
      if (src >>> k) &&& 1 != 0 then r := r ||| b
      k := k + 1
  return r

/-- PEXT: gather the bits of `src` at the set bits of `mask` into the low bits. -/
def pext (src mask : UInt32) : UInt32 := Id.run do
  let mut r : UInt32 := 0
  let mut k : UInt32 := 0
  for i in [0:32] do
    let b : UInt32 := (1 : UInt32) <<< i.toUInt32
    if mask &&& b != 0 then
      if src &&& b != 0 then r := r ||| ((1 : UInt32) <<< k)
      k := k + 1
  return r

/-- BEXTR: the field of `len` (`ctl[15:8]`) bits at `start` (`ctl[7:0]`), zeros beyond bit 31. -/
def bextr (src ctl : UInt32) : UInt32 :=
  let start := ctl &&& 0xFF
  let len := (ctl >>> 8) &&& 0xFF
  let v := if start ≥ 32 then 0 else src >>> start
  if len ≥ 32 then v else v &&& (((1 : UInt32) <<< len) - 1)

/-- BZHI: clear the bits at positions ≥ `idx[7:0]`; unchanged if that is ≥ 32. -/
def bzhi (src idx : UInt32) : UInt32 :=
  let n := idx &&& 0xFF
  if n ≥ 32 then src else src &&& (((1 : UInt32) <<< n) - 1)

/-- One step of CRC-32C (polynomial 11EDC6F41h, bit-reflected 82F63B78h) over the low `n` bytes of
`v`, least significant byte first; no pre/post inversion (as the CRC32 instruction). -/
def crc32c (crc v : UInt32) (n : Nat) : UInt32 := Id.run do
  let mut c := crc
  for k in [0:n] do
    c := c ^^^ ((v >>> (8 * k.toUInt32)) &&& 0xFF)
    for _ in [0:8] do
      c := if c &&& 1 != 0 then (c >>> 1) ^^^ 0x82F63B78 else c >>> 1
  return c

/-- SplitMix64: the next state and the output. -/
def splitmix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (s, z ^^^ (z >>> 31))

/-- 32-bit byte swap. -/
@[inline] def bswap32 (v : UInt32) : UInt32 :=
  (v <<< 24) ||| ((v &&& 0xFF00) <<< 8) ||| ((v >>> 8) &&& 0xFF00) ||| (v >>> 24)

/-! ## State access -/

@[inline] def gst : M GprState := fun m => .ok m.cpu.gprx m
@[inline] def modG (f : GprState → GprState) : M Unit := modCpu fun c => { c with gprx := f c.gprx }

/-- The time-stamp counter, as the core's RDTSC reads it (`Exec`, 0F 31). -/
@[inline] def tsc : M UInt64 := fun m => .ok m.icount m

/-- Set the arithmetic flags to `v` (only bits of `Flag.arith`). -/
@[inline] def setArith (v : UInt32) : M Unit := setFlags arith v

/-! ## Memory-operand checks -/

/-- Linear address of a one-byte read at `seg:off` with the segment checks of a read, except
that execute-only code segments are allowed (CLFLUSH, CLFLUSHOPT, CLWB). -/
def flushAddr (seg : UInt8) (off : UInt32) : M UInt32 := do
  let sr := (← cpu).getSeg seg
  let sr' := if sr.isCode then { sr with attr := sr.attr ||| 2 } else sr
  if !segAllowed sr' off 1 false then
    if seg == SegN.SS then exc Vec.SS (some 0) else gp 0
  return sr.base + off

/-- CLFLUSH/CLFLUSHOPT/CLWB of the ModRM operand: the checks of a one-byte load (A bit, no D bit). -/
def cacheFlush (i : Inst) : M Unit := do
  let lin ← flushAddr i.seg (← eaOff i)
  let _ ← translate lin false (← isUser)

/-- The implicit DS:rAX operand (segment override allowed) of MONITOR/MONITORX/CLZERO. -/
@[inline] def raxOff (i : Inst) : M UInt32 := do
  let a ← getReg 0
  return if i.adsz == 2 then a &&& 0xFFFF else a
@[inline] def raxSeg (i : Inst) : UInt8 := if i.segOvr != 0xFF then i.segOvr else SegN.DS

/-- The 16 dwords of the 64-byte physical line at `p` (all ones outside RAM). -/
def lineData (p : UInt64) : M (Array UInt32) := fun m =>
  .ok ((List.range 16).toArray.map fun k =>
    if p >>> 32 != 0 then 0xFFFFFFFF else rdBytes m.mem (p.toUInt32 + 4 * k.toUInt32) 4) m

/-! ## Instructions -/

/-- POPCNT/LZCNT/TZCNT r, r/m (`kind` 0, 1, 2) at the operand size. -/
def bitCount (i : Inst) (kind : Nat) : M Unit := do
  let sz := i.opsz
  let v ← rdE i sz
  let bits := sz.bits
  match kind with
  | 0 =>
    let r := popcount32 v
    wrReg sz i.reg r
    setArith (if v == 0 then ZF else 0)
  | 1 =>
    let r := lzcnt bits v
    wrReg sz i.reg r
    setArith (bmiFlags sz r (v == 0))
  | _ =>
    let r := tzcnt bits v
    wrReg sz i.reg r
    setArith (bmiFlags sz r (v &&& sz.mask == 0))

/-- MONITOR (`x = false`) / MONITORX: ECX must be 0 (#GP(0)); DS:rAX is checked like a one-byte
read and its physical 64-byte line armed. -/
def monitor (i : Inst) (x : Bool) : M Unit := do
  let c ← cpu
  if !x && c.cpl != 0 && !c.gprx.monMwaitUserEn then ud
  if c.ecx != 0 then gp 0
  let lin ← segAddr (raxSeg i) (← raxOff i) 1 false
  let p ← translate lin false (← isUser)
  let line := p &&& ~~~63
  let d ← lineData line
  modG fun g => { g with monLine := some line, monData := d }

/-- MWAIT (`x = false`) / MWAITX (see the module documentation). -/
def mwait (x : Bool) : M Unit := do
  let c ← cpu
  if !x && c.cpl != 0 && !c.gprx.monMwaitUserEn then ud
  -- ECX[0]: interrupts wake even if masked (CPUID 5:ECX.IBE = 1); MWAITX also ECX[1]: timer
  if c.ecx &&& ~~~(if x then 3 else 1) != 0 then gp 0
  let g := c.gprx
  modG fun g => { g with monLine := none, monData := #[] }
  let some line := g.monLine | return
  if (← lineData line) != g.monData then return
  let ibe := c.ecx &&& 1 != 0
  let iflag := c.eflags &&& IF != 0
  let m ← getM
  let timed := x && c.ecx &&& 2 != 0 && c.ebx != 0
  if !timed then
    if iflag || !ibe then modCpu fun c => { c with halted := true }
    else if m.intr then return
    else if m.timerAt == 0xFFFFFFFFFFFFFFFF then modCpu fun c => { c with halted := true }
    else modM fun m => { m with icount := max m.icount m.timerAt }
  else
    let deadline := m.icount + c.ebx.toUInt64
    if iflag || ibe then
      if m.intr then return
      modM fun m => { m with icount := max m.icount (min deadline m.timerAt) }
    else modM fun m => { m with icount := deadline }

/-- CLZERO: zero the 64-byte linear line containing DS:rAX. -/
def clzero (i : Inst) : M Unit := do
  let seg := raxSeg i
  let off ← raxOff i
  let sr := (← cpu).getSeg seg
  let lin := (sr.base + off) &&& ~~~63
  let _ ← segAddr seg (lin - sr.base) 64 true
  dbData lin 64 true
  let p ← translate lin true (← isUser)
  for k in [0:16] do physWr (p + (4 * k).toUInt64) 4 0

/-- RDPMC: counter ECX (0..3, 0..5 with PerfCtrExtCore) into EDX:EAX. -/
def rdpmc : M Unit := do
  let c ← cpu
  if c.cr4 &&& CR4.PCE == 0 && c.cpl != 0 then gp 0
  let n := c.ecx
  if n ≥ (if implemented .perfCtrExtCore then 6 else 4) then gp 0
  let v := c.gprx.perfCtr[n.toNat]!
  setReg 0 v.toUInt32
  setReg 2 (v >>> 32).toUInt32

/-- RDPRU: MPERF (ECX = 0), APERF (ECX = 1). -/
def rdpru : M Unit := do
  let c ← cpu
  if c.cpl != 0 && c.cr4 &&& CR4.TSD != 0 then ud
  let t ← tsc
  let (v, ok) : UInt64 × Bool :=
    if c.ecx == 0 then (t + c.gprx.mperfOff, true)
    else if c.ecx == 1 then (t + c.gprx.aperfOff, true) else (0, false)
  setReg 0 v.toUInt32
  setReg 2 (v >>> 32).toUInt32
  setArith (if ok then CF else 0)

/-- RDRAND/RDSEED r16/r32: the next SplitMix64 output; CF = 1, OF = SF = ZF = AF = PF = 0. -/
def rdrand (i : Inst) : M Unit := do
  let (s, z) := splitmix (← gst).rng
  modG fun g => { g with rng := s }
  wrReg i.opsz i.rm z.toUInt32
  setArith CF

/-- The 0F-map hook (see the module documentation). -/
def op0F? (i : Inst) : Option (M Unit) :=
  match i.op with
  | 0x1B8 => if i.pp == 2 && implemented .popcnt then some (bitCount i 0) else none
  | 0x1BD => if implemented .abm then some (bitCount i 1) else none
  | 0x1BC => if implemented .bmi1 then some (bitCount i 2) else none
  -- PREFETCH (/0), PREFETCHW (/1), reserved types (/2../7) as PREFETCH: no effect; register #UD
  | 0x10D => if implemented .prefetchw then some (if i.isMem then pure () else ud) else none
  | 0x133 => some rdpmc
  -- F3 0F 09: WBNOINVD (CPL 0; no cache to write back)
  | 0x109 => if implemented .wbnoinvd then some cplIs0 else none
  | 0x101 =>
    if i.isMem then none else
    match i.modrm with
    | 0xC8 => if implemented .monitor then some (monitor i false) else none
    | 0xC9 => if implemented .monitor then some (mwait false) else none
    | 0xF9 => if implemented .rdtscp then some (do
        let c ← cpu
        if c.cr4 &&& CR4.TSD != 0 && c.cpl != 0 then gp 0
        let t ← tsc
        setReg 0 t.toUInt32
        setReg 2 (t >>> 32).toUInt32
        setReg 1 c.gprx.tscAux) else none
    | 0xFA =>
      if i.rep == 0xF3 then
        if implemented .mcommit then some (do
          if (← cpu).efer &&& EFER.MCOMMIT == 0 then ud
          setArith CF) else none
      else if implemented .mwaitx then some (monitor i true) else none
    | 0xFB => if implemented .mwaitx then some (mwait true) else none
    | 0xFC => if implemented .clzero then some (clzero i) else none
    | 0xFD => if implemented .rdpru then some rdpru else none
    | _ => none
  | 0x1AE =>
    if !i.isMem then none
    else if i.pp == 0 && i.reg == 7 then (if implemented .clfsh then some (cacheFlush i) else none)
    else if i.pp == 1 && i.reg == 7 then (if implemented .clflushopt then some (cacheFlush i) else none)
    else if i.pp == 1 && i.reg == 6 then (if implemented .clwb then some (cacheFlush i) else none)
    else none
  | 0x1C7 =>
    if i.isMem then none
    -- RDRAND, RDSEED: #UD with F2/F3 (SDM RDRAND/RDSEED; the APM lists no prefix rule)
    else if i.reg == 6 then (if i.pp ≤ 1 && implemented .rdrand then some (rdrand i) else none)
    else if i.reg == 7 then
      if i.pp == 2 then
        -- RDPID r32: operand-size prefixes do not apply (APM RDPID); flags unaffected
        if implemented .rdpid then some (do setReg i.rm (← gst).tscAux) else none
      else if i.pp ≤ 1 && implemented .rdseed then some (rdrand i) else none
    else none
  | _ => none

/-- Legacy 0F 38 F0, F1, F6. -/
def map2? (i : Inst) : Option (M Unit) :=
  match i.byte with
  | 0xF0 | 0xF1 =>
    if i.pp == 3 then
      -- CRC32 r32, r/m8 (F0) or r/m16/32 (F1; operand size)
      some (do
        let sz : Sz := if i.byte == 0xF0 then 1 else i.opsz
        let v ← rdE i sz
        setReg i.reg (crc32c (← getReg i.reg) v sz.toNat))
    else if i.pp ≤ 1 && implemented .movbe then
      some (do
        needMem i
        let sz := i.opsz
        let sw := fun (v : UInt32) => if sz == 2 then ((v &&& 0xFF) <<< 8) ||| ((v >>> 8) &&& 0xFF) else bswap32 v
        if i.byte == 0xF0 then wrReg sz i.reg (sw (← rdE i sz))
        else wrE i sz (sw (← rdReg sz i.reg)))
    else none
  | 0xF6 =>
    if (i.pp == 1 || i.pp == 2) && implemented .adx then
      -- ADCX (66; CF) / ADOX (F3; OF): 32-bit regardless of the operand size
      some (do
        let b ← rdE i 4
        let a ← getReg i.reg
        let fl := if i.pp == 1 then CF else OF
        let cin : UInt64 := if (← getFlags) &&& fl != 0 then 1 else 0
        let s := a.toUInt64 + b.toUInt64 + cin
        setReg i.reg s.toUInt32
        setFlags fl (if s >>> 32 != 0 then fl else 0))
    else none
  | _ => none

/-- BMI1/BMI2 (VEX; real/virtual-8086 mode and legacy prefixes were rejected by `vexExec`).
Operand size 32 (VEX.W is ignored outside 64-bit mode); VEX.L = 1 is #UD (APM). -/
def vex? (i : Inst) : Option (M Unit) :=
  let run (f : Feature) (body : M Unit) : Option (M Unit) :=
    if !implemented f then none else some (do
      if i.vexL then ud
      body)
  let wr := fun (r : UInt8) (v : UInt32) => setReg r v
  if i.map == 2 then
    match i.byte, i.pp with
    | 0xF2, 0 => run .bmi1 do   -- ANDN r, vvvv, r/m
      let r := ~~~(← getReg i.vvvv) &&& (← rdE i 4)
      wr i.reg r
      setArith (bmiFlags 4 r false)
    | 0xF3, 0 =>                -- BLSR /1, BLSMSK /2, BLSI /3: vvvv, r/m
      if i.reg == 0 || i.reg > 3 then (if implemented .bmi1 then some ud else none) else
      run .bmi1 do
        let s ← rdE i 4
        let (r, cf) :=
          if i.reg == 1 then ((s - 1) &&& s, s == 0)
          else if i.reg == 2 then ((s - 1) ^^^ s, s == 0)
          else ((0 - s) &&& s, s != 0)
        wr i.vvvv r
        setArith (bmiFlags 4 r cf)
    | 0xF5, 0 => run .bmi2 do   -- BZHI r, r/m, vvvv
      let idx ← getReg i.vvvv
      let r := bzhi (← rdE i 4) idx
      wr i.reg r
      setArith (bmiFlags 4 r (idx &&& 0xFF ≥ 32))
    | 0xF5, 2 => run .bmi2 do   -- PEXT r, vvvv, r/m
      wr i.reg (pext (← getReg i.vvvv) (← rdE i 4))
    | 0xF5, 3 => run .bmi2 do   -- PDEP r, vvvv, r/m
      wr i.reg (pdep (← getReg i.vvvv) (← rdE i 4))
    | 0xF6, 3 => run .bmi2 do   -- MULX hi (reg), lo (vvvv), r/m × EDX
      let p := (← getReg 2).toUInt64 * (← rdE i 4).toUInt64
      wr i.vvvv p.toUInt32
      wr i.reg (p >>> 32).toUInt32
    | 0xF7, 0 => run .bmi1 do   -- BEXTR r, r/m, vvvv
      let r := bextr (← rdE i 4) (← getReg i.vvvv)
      wr i.reg r
      setArith (bmiFlags 4 r false)
    | 0xF7, pp => run .bmi2 do  -- SHLX (66), SARX (F3), SHRX (F2): r, r/m, vvvv
      let s ← rdE i 4
      let n := (← getReg i.vvvv) &&& 31
      wr i.reg (if pp == 1 then s <<< n
                else if pp == 2 then (if s &&& 0x80000000 != 0 then ~~~((~~~s) >>> n) else s >>> n)
                else s >>> n)
    | 0xF2, _ | 0xF3, _ | 0xF5, _ | 0xF6, _ =>
      if implemented .bmi1 || implemented .bmi2 then some ud else none
    | _, _ => none
  else if i.map == 3 && i.byte == 0xF0 then
    if i.pp != 3 then (if implemented .bmi2 then some ud else none) else
    run .bmi2 do               -- RORX r, r/m, imm8 (VEX.vvvv not checked, see above)
      let s ← rdE i 4
      let n := i.imm &&& 31
      wr i.reg (if n == 0 then s else (s >>> n) ||| (s <<< (32 - n)))
  else none

/-! ## MSRs -/

/-- PerfEvtSel bits that are defined (APM vol. 2, 13.2.1): EventSelect[7:0], UnitMask, Usr, Os,
Edge, Int, En, Inv, CntMask, EventSelect[11:8], HostGuestOnly. -/
def perfEvtSelMask : UInt64 := 0x0000030FFFD7FFFF

def perfMsr (k : Nat) (ctr : Bool) : MsrImpl where
  rd := do
    let g ← gst
    return if ctr then g.perfCtr[k]! else g.perfEvtSel[k]!
  wr v := modG fun g =>
    if ctr then { g with perfCtr := g.perfCtr.set! k (v &&& 0xFFFFFFFFFFFF) }
    else { g with perfEvtSel := g.perfEvtSel.set! k (v &&& perfEvtSelMask) }

def msr? (n : UInt32) : Option MsrImpl :=
  if n == 0xC0000103 then
    if implemented .rdtscp || implemented .rdpid then
      some { rd := do return (← gst).tscAux.toUInt64
             wr := fun v => do
               -- bits 63:32 reserved
               if v >>> 32 != 0 then gp 0
               modG fun g => { g with tscAux := v.toUInt32 } }
    else none
  else if n == 0xC0010015 then
    -- HWCR: TscFreqSel (bit 24) reads 1; only MonMwaitUserEn (bit 10) is modelled
    some { rd := do return (if (← gst).monMwaitUserEn then 0x400 else 0) ||| 0x01000000
           wr := fun v => modG fun g => { g with monMwaitUserEn := v &&& 0x400 != 0 } }
  else if (n == 0xE7 || n == 0xE8) && implemented .rdpru then
    some { rd := do
             let g ← gst
             return (← tsc) + (if n == 0xE7 then g.mperfOff else g.aperfOff)
           wr := fun v => do
             let t ← tsc
             modG fun g => if n == 0xE7 then { g with mperfOff := v - t } else { g with aperfOff := v - t } }
  else if 0xC0010000 ≤ n && n ≤ 0xC0010007 then
    some (perfMsr ((n - 0xC0010000).toNat % 4) (n ≥ 0xC0010004))
  else if 0xC0010200 ≤ n && n ≤ 0xC001020B && implemented .perfCtrExtCore then
    let k := (n - 0xC0010200).toNat
    some (perfMsr (k / 2) (k % 2 == 1))
  else none

end Gpr
end X86
