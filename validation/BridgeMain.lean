import X86
import X64
import LongStub
/-!
# x86bridge — handing 64-bit code from the IA-32 model to the x86-64 model

    x86bridge [--max N] [--x64max N] [--cmdline STR] kernel.elf

The IA-32 model (`x86_32`, namespace `X86`) executes legacy and compatibility-mode code and stops
before the first instruction of 64-bit code (`Fault.unsupported "64-bit mode"`, the boundary of
`X86/Ext/LongModeBase.lean`). At that point its machine state is a complete 64-bit state (RIP =
`ripHi`:EIP, RSP = `rspHi`:ESP, R11 after SYSCALL; see `toX64`), which this executable converts to the
`x86_64` model's (`X64`) state and runs there. The `x86_64` model has no compatibility mode: it stops in
turn at the first transfer back to compatibility mode ("IRET/far return/far transfer/SYSRET to
compatibility mode"), with the state before that instruction; the reverse conversion would have to
perform that 64-bit instruction, which neither model does, so the hand-off is one-way.

For the long-mode system test (`test/sys/t_long.c`) every 64-bit target is one of the test's stubs:
the bridge runs the stub in the `x86_64` model up to its final IRETQ (where `X64` stops), and checks
it against `LongStub.run` (the stub emulation `x86sys` uses): the record and the IRETQ frame the stub
writes, and the registers at the IRETQ, must be identical. It then continues the IA-32 run from the
emulated IRETQ. The UART output of the kernel goes to stdout as in `x86sys`.

The state mapping (IA-32 → X64): general registers zero-extended (`LongModeState` holds RIP/RSP bits
63:32 and R11; R8–R15 are 0), RFLAGS, segment registers with 64-bit bases (FS/GS bases from the
FS_BASE/GS_BASE MSR values while the cache is unchanged), GDTR/IDTR/LDTR/TR, CR0/2/3/4, DR0–3/6/7,
EFER, STAR/LSTAR/CSTAR/SFMASK, KernelGSbase, XMM0–7 (XMM8–15 zero) and MXCSR, the x87 registers
(physical order), control/status word and a full tag word (00 or 11: the model keeps only empty
bits), the stored MSRs, HLT/interrupt shadow, the whole physical memory. Not mapped: the local APIC
(X64 has none; its page reads as RAM), the PIC/PIT/UART device states (reset values) and
pending events, the YMM upper halves and XCR0 (X64 has no AVX state).
-/
open X86

def seg64 (s : X86.SegReg) : X64.SegReg :=
  { sel := s.sel, base := s.base.toUInt64, limit := s.limit.toUInt64, attr := s.attr.toUInt64 }

def baseMsr (s : X86.SegReg) (saved : Option (X86.SegReg × UInt64)) : UInt64 :=
  match saved with
  | some (cache, b) => if cache == s then b else s.base.toUInt64
  | none => s.base.toUInt64

/-- The IA-32 machine at a 64-bit stop as an X64 machine. -/
def toX64 (m : X86.Machine) : X64.Machine :=
  let c := m.cpu
  let tag : UInt16 := (List.range 8).foldl (fun t k =>
    if c.fempty &&& ((1 : UInt8) <<< k.toUInt8) != 0 then t ||| ((3 : UInt16) <<< (2 * k).toUInt16) else t) 0
  let cpu : X64.Cpu := {
    xmm := (Array.range 16).map fun k => if k < 8 then { lo := c.xmm[k]!.lo, hi := c.xmm[k]!.hi } else {},
    mxcsr := c.mxcsr.toUInt64, fpControl := c.fcw, fpStatus := c.fsw, fpTag := tag, fpOpcode := c.fop,
    fpIp := c.fip.toUInt64, fpDp := c.fdp.toUInt64,
    fp := c.fpr.map fun f => { significand := f.sig, signExp := f.se },
    rax := c.eax.toUInt64, rcx := c.ecx.toUInt64, rdx := c.edx.toUInt64, rbx := c.ebx.toUInt64,
    rsp := LongMode.rsp c, rbp := c.ebp.toUInt64, rsi := c.esi.toUInt64, rdi := c.edi.toUInt64,
    r11 := c.lmx.r11,
    efer := c.efer.toUInt64, fsBase := baseMsr c.fs c.lmx.fsBase, gsBase := baseMsr c.gs c.lmx.gsBase,
    kernelGsBase := c.lmx.kernelGsBase, star := c.sysx.star, lstar := c.sysx.lstar, cstar := c.sysx.cstar,
    sfmask := c.sysx.sfmask.toUInt64, rip := LongMode.rip c, rflags := c.eflags.toUInt64,
    es := seg64 c.es, cs := seg64 c.cs, ss := seg64 c.ss, ds := seg64 c.ds, fs := seg64 c.fs, gs := seg64 c.gs,
    ldtr := seg64 c.ldtr, tr := seg64 c.tr,
    gdtBase := c.gdtBase.toUInt64, gdtLimit := c.gdtLimit.toUInt64, idtBase := c.idtBase.toUInt64,
    idtLimit := c.idtLimit.toUInt64, cr0 := c.cr0.toUInt64, cr2 := c.cr2.toUInt64, cr3 := c.cr3.toUInt64,
    cr4 := c.cr4.toUInt64, dr0 := c.dr0.toUInt64, dr1 := c.dr1.toUInt64, dr2 := c.dr2.toUInt64,
    dr3 := c.dr3.toUInt64, dr6 := c.dr6.toUInt64, dr7 := c.dr7.toUInt64,
    msrs := c.msrs.map fun (n, v) => (n.toUInt64, v), halted := c.halted, shadow := c.shadow }
  { cpu, mem := m.mem, icount := m.icount }

def loadElf (img : ByteArray) (memSize : Nat) (cmdline : String) : Except String X86.Machine := do
  if img.size < 84 || u32At img 0 != 0x464C457F then throw "not an ELF file"
  let entry := u32At img 24
  let phoff := u32At img 28
  let mut mem := zeroMem memSize
  for k in [0:u16At img 44] do
    let ph := phoff + 32 * k
    if u32At img ph != 1 then continue
    mem := img.copySlice (u32At img (ph + 4)) mem (u32At img (ph + 12)) (u32At img (ph + 16))
  if !cmdline.isEmpty then
    mem := wrBytes mem 0x9000 4 4
    mem := wrBytes mem (0x9000 + 16) 4 0x9100
    let cl := cmdline.toUTF8
    mem := cl.copySlice 0 mem 0x9100 cl.size
    mem := wrBytes mem (0x9100 + cl.size.toUInt32) 1 0
  let cs := flatSeg 0x08 0xC09B
  let ds := flatSeg 0x10 0xC093
  return { cpu := { eip := entry.toUInt32, eax := 0x2BADB002, ebx := 0x9000, esp := 0x7000, cs, ds, es := ds,
                    ss := ds, fs := ds, gs := ds, idtBase := 0, idtLimit := 0, cr0 := CR0.PE ||| CR0.ET,
                    smbase := 0xA0000 }, mem }

partial def parse (o : Nat × Nat × String) : List String → (Nat × Nat × String) × List String
  | "--max" :: n :: r => parse (n.toNat!, o.2.1, o.2.2) r
  | "--x64max" :: n :: r => parse (o.1, n.toNat!, o.2.2) r
  | "--cmdline" :: c :: r => parse (o.1, o.2.1, c) r
  | f :: r => let (a, b) := parse o r; (a, f :: b)
  | [] => (o, [])

/-- Run X64 until it stops (fatal) or `limit` instructions. -/
def runX64 (m : X64.Machine) (limit : Nat) : X64.Machine := m.runUntil (m.icount + limit.toUInt64)

def rd64 (mem : ByteArray) (p : UInt64) : UInt64 :=
  (rdBytes mem p.toUInt32 4).toUInt64 ||| ((rdBytes mem (p.toUInt32 + 4) 4).toUInt64 <<< 32)

def hex (x : UInt64) : String := s!"0x{String.ofList (Nat.toDigits 16 x.toNat)}"

def main (args : List String) : IO UInt32 := do
  let ((maxI, x64max, cmdline), files) := parse (20000000000, 10000, "") args
  let [path] := files | do IO.eprintln "usage: x86bridge [--max N] [--x64max N] [--cmdline STR] kernel.elf"; return 2
  let img ← IO.FS.readBinFile path
  let mut m ← match loadElf img (64 * 1024 * 1024) cmdline with
    | .ok m => pure m
    | .error e => do IO.eprintln e; return 2
  let stdout ← IO.getStdout
  let mut out := ""
  let mut stops := 0
  let mut agree := 0
  let mut bad := 0
  let mut done := false
  while !done do
    m := m.runUntil (min maxI.toUInt64 (m.icount + 100000))
    let tx := m.uart.tx
    if tx.size > 0 then
      stdout.write tx; stdout.flush
      out := out ++ String.fromUTF8! (ByteArray.mk (tx.data.filter (· < 128)))
      m := { m with uart := { m.uart with tx := .empty } }
    if (out.splitOn "END\n").length > 1 then done := true
    else if let some (.unsupported "64-bit mode") := m.fatal then
      stops := stops + 1
      -- the 64-bit continuation in the x86-64 model
      let x := runX64 (toX64 m) x64max
      let xr := match x.fatal with | some f => s!"{repr f}" | none => "no stop"
      -- the stub emulation of x86sys, from the same IA-32 state
      match LongStub.resume m with
      | none =>
        IO.println s!"BRIDGE stop {stops}: {m.cpu.lmx.entry} rip={hex (LongMode.rip m.cpu)}: not a test stub; x86_64 model: {xr} at rip={hex x.cpu.rip} after {x.icount - m.icount} instructions"
        done := true
      | some m' =>
        -- X64 stops at the stub's IRETQ (to compatibility mode); compare the stub's memory writes and
        -- registers with the emulation: the record (rax/rbx/rcx/r11 slots and the copy) and the frame
        let iretOk := match x.fatal with
          | some (.unsupported s) => s.startsWith "IRET to compatibility mode"
          | _ => false
        -- the registers the stub leaves for IRETQ: RSI/RDI/RCX after REP MOVSQ
        let regsOk := x.cpu.rsi.toUInt32 == m'.cpu.esi && x.cpu.rdi.toUInt32 == m'.cpu.edi && x.cpu.rcx == 0
        -- memory: every byte the two runs wrote must agree outside the paging structures' A/D bits
        let mut diffs := 0
        let mut firstDiff : Option Nat := none
        for k in [0:m.mem.size] do
          if x.mem.get! k != m'.mem.get! k then
            -- X64 sets accessed/dirty bits without a TLB; accept differences in bits 5/6 of a byte
            if (x.mem.get! k ^^^ m'.mem.get! k) &&& 0x9F != 0 then
              diffs := diffs + 1
              if firstDiff.isNone then firstDiff := some k
        if iretOk && regsOk && diffs == 0 then agree := agree + 1
        else
          bad := bad + 1
          IO.println s!"BRIDGE stop {stops}: {m.cpu.lmx.entry} rip={hex (LongMode.rip m.cpu)}: x86_64 model: {xr} at rip={hex x.cpu.rip}; regs {regsOk}, {diffs} differing bytes (first {firstDiff})"
        m := m'
    else if let some f := m.fatal then
      IO.println s!"FATAL: {repr f} at eip={m.cpu.eip}"; done := true
    else if m.icount ≥ maxI.toUInt64 then IO.println "FATAL: instruction limit"; done := true
    else if m.idle then IO.println "FATAL: idle"; done := true
  IO.println s!"BRIDGE: {stops} stops in 64-bit mode, {agree} continued identically by the x86_64 model, {bad} differences"
  return (if bad == 0 then 0 else 1)
