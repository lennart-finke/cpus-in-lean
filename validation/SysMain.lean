import X86
import LongStub
/-!
# x86sys — runner for the system-level test kernel

    x86sys [--max N] [--mem MB] [--cmdline STR] systest.elf

Loads the multiboot ELF built by `test/sys/build.sh` (one PT_LOAD segment) and starts it in the
state a multiboot loader leaves: flat 32-bit protected mode, paging off, interrupts disabled,
`EAX = 0x2BADB002`, `EBX` pointing at a (zeroed) multiboot information block. COM1 output goes to
stdout; the run ends when the kernel prints `END`, on a fatal stop, or at the instruction limit.
`test/sys/run.sh` runs the same kernel under QEMU and compares the two transcripts.
-/
open X86

def loadElf (img : ByteArray) (memSize : Nat) (cmdline : String := "") : Except String Machine := do
  if img.size < 84 || u32At img 0 != 0x464C457F then throw "not an ELF file"
  let entry := u32At img 24
  let phoff := u32At img 28
  let phnum := u16At img 44
  let mut mem := zeroMem memSize
  for k in [0:phnum] do
    let ph := phoff + 32 * k
    if u32At img ph != 1 then continue
    let off := u32At img (ph + 4)
    let paddr := u32At img (ph + 12)
    let filesz := u32At img (ph + 16)
    if paddr + filesz > memSize then throw "segment beyond memory"
    mem := img.copySlice off mem paddr filesz
  -- multiboot information at 0x9000: flags bit 2 = command line (at 0x9100), as QEMU passes -append
  if !cmdline.isEmpty then
    mem := wrBytes mem 0x9000 4 4
    mem := wrBytes mem (0x9000 + 16) 4 0x9100
    let cl := cmdline.toUTF8
    mem := cl.copySlice 0 mem 0x9100 cl.size
    mem := wrBytes mem (0x9100 + cl.size.toUInt32) 1 0
  let cs := flatSeg 0x08 0xC09B
  let ds := flatSeg 0x10 0xC093
  let cpu : Cpu := { eip := entry.toUInt32, eax := 0x2BADB002, ebx := 0x9000, esp := 0x7000,
                     cs, ds, es := ds, ss := ds, fs := ds, gs := ds, idtBase := 0, idtLimit := 0,
                     cr0 := CR0.PE ||| CR0.ET,
                     -- firmware (SeaBIOS) relocates SMBASE to 0xA0000 before starting the kernel
                     smbase := 0xA0000,
                     -- model-only test hooks of system B (the NMI test MSR, `SysB.nmiHookMsr`)
                     sysbx := { testHooks := true } }
  return { cpu, mem }

partial def parse (maxI : UInt64) (mem : Nat) (cl : String) : List String → UInt64 × Nat × String × List String
  | "--max" :: n :: r => parse n.toNat!.toUInt64 mem cl r
  | "--mem" :: n :: r => parse maxI n.toNat! cl r
  | "--cmdline" :: c :: r => parse maxI mem c r
  | f :: r => let (a, b, c, d) := parse maxI mem cl r; (a, b, c, f :: d)
  | [] => (maxI, mem, cl, [])

def main (args : List String) : IO UInt32 := do
  let (maxI, memMB, cmdline, files) := parse 20000000000 64 "" args
  let [path] := files | do IO.eprintln "usage: x86sys [--max N] [--mem MB] [--cmdline STR] systest.elf"; return 2
  let img ← IO.FS.readBinFile path
  let mut m ← match loadElf img (memMB * 1024 * 1024) cmdline with
    | .ok m => pure m
    | .error e => do IO.eprintln e; return 2
  let stdout ← IO.getStdout
  let mut out : String := ""
  let mut done := false
  while !done do
    m := m.runUntil (min maxI (m.icount + 100000))
    -- the long-mode test's 64-bit stubs (test infrastructure, `LongStub.lean`)
    if let some m' := X86.LongStub.resume m then m := m'; continue
    let tx := m.uart.tx
    if tx.size > 0 then
      stdout.write tx
      stdout.flush
      out := out ++ String.fromUTF8! (ByteArray.mk (tx.data.filter (· < 128)))
      m := { m with uart := { m.uart with tx := .empty } }
    if (out.splitOn "END\n").length > 1 then done := true
    else if let some f := m.fatal then
      IO.println s!"FATAL: {repr f} at eip={m.cpu.eip}"
      done := true
    else if m.icount ≥ maxI then
      IO.println "FATAL: instruction limit"
      done := true
    else if m.idle then
      IO.println "FATAL: idle"
      done := true
  return 0
