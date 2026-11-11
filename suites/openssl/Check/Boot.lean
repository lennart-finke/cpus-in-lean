import Check.Support
/-! Run a multiboot ELF (a driver built by `tools/hw.py`) on the model the way QEMU's `-kernel`
does: flat 32-bit protected mode, paging off, interrupts disabled. COM1 output goes to stdout; the
run ends when the guest prints `END`. -/
namespace Check
open X86

def loadElf (img : ByteArray) (memSize : Nat) : Except String Machine := do
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
  let cs := flatSeg 0x08 0xC09B
  let ds := flatSeg 0x10 0xC093
  let cpu : Cpu := { eip := entry.toUInt32, eax := 0x2BADB002, ebx := 0x9000, esp := 0x7000,
                     cs, ds, es := ds, ss := ds, fs := ds, gs := ds, idtBase := 0, idtLimit := 0,
                     cr0 := CR0.PE ||| CR0.ET }
  return { cpu, mem }

def boot (path : String) : IO UInt32 := do
  let mut m ← match loadElf (← IO.FS.readBinFile path) (64 * 1024 * 1024) with
    | .ok m => pure m
    | .error e => do IO.eprintln e; return 2
  let stdout ← IO.getStdout
  let mut tail := ""
  for _ in [0:100000] do
    m := m.runUntil (m.icount + 100000)
    let tx := m.uart.tx
    if tx.size > 0 then
      stdout.write tx
      let cs := tail.toList ++ (tx.data.filter (· < 128)).toList.map fun b => Char.ofNat b.toNat
      tail := String.ofList (cs.drop (cs.length - 8))
      m := { m with uart := { m.uart with tx := .empty } }
    if tail.endsWith "END\n" then
      stdout.flush
      return 0
    if let some f := m.fatal then
      IO.eprintln s!"FATAL: {repr f} at eip={m.cpu.eip}"; return 1
    if m.idle then
      IO.eprintln "FATAL: the guest halted without printing END"; return 1
  IO.eprintln "FATAL: instruction limit"
  return 1

end Check
