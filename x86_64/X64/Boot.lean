import X64.Step
namespace X64

def bootParams : UInt64 := 0x10000
def cmdlineAddr : UInt64 := 0x20000
def flatSeg (sel : UInt16) (attr : UInt64) : SegReg :=
  { sel, base := 0, limit := 0xFFFFFFFF, attr }

def zeroMem (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n 0)

/-- Four-level identity map of the first GiB, using 2 MiB leaves. The tables and GDT
are loader data, not a shortcut for guest execution. -/
def identityMap (mem : ByteArray) : ByteArray := Id.run do
  let mut mem := wrBytes mem 0x3000 8 0x4003
  mem := wrBytes mem 0x4000 8 0x5003
  for k in [0:512] do
    mem := wrBytes mem (0x5000 + k.toUInt64 * 8) 8 (k.toUInt64 * 0x200000 ||| 0x83)
  return mem

/-- Linux's documented 64-bit boot entry, at code32_start + 0x200.
This loader requires a 64-bit bzImage and leaves decompression to guest instructions. -/
def loadLinux (memSize : Nat) (kernel initrd : ByteArray) (cmdline : String) : Except String Machine := do
  if memSize < 32 * 1024 * 1024 || memSize > 1024 * 1024 * 1024 then
    throw "boot memory must be between 32 MiB and 1 GiB"
  if kernel.size < 0x270 then throw "kernel image too small"
  let rd := fun (off n : UInt64) => (rdBytes kernel off n).toNat
  if rd 0x202 4 != 0x53726448 || rd 0x1FE 2 != 0xAA55 then throw "not a bzImage"
  if rd 0x206 2 < 0x20C || rd 0x236 2 % 2 != 1 then throw "requires a 64-bit bzImage with boot protocol >= 2.12"
  let sectors := rd 0x1F1 1
  let payload := ((if sectors == 0 then 4 else sectors) + 1) * 512
  if payload + 0x200 ≥ kernel.size then throw "truncated kernel payload"
  let load := rd 0x214 4
  let size := kernel.size - payload
  let reserved := max size (rd 0x260 4)
  if load < 0x100000 || load + reserved > memSize then throw "kernel does not fit in RAM"
  let hdrEnd := 0x202 + rd 0x201 1
  if hdrEnd > kernel.size || hdrEnd > 4096 then throw "invalid setup header length"
  let cl := cmdline.toUTF8
  if cl.size + 1 > min 65536 (rd 0x238 4) then throw "kernel command line too long"
  if initrd.size > memSize then throw "initramfs exceeds RAM"
  let top := min memSize (rd 0x22C 4 + 1)
  if initrd.size > top then throw "initramfs exceeds address limit"
  let initAddr := (top - initrd.size) / 4096 * 4096
  if initrd.size > 0 && initAddr < load + reserved then throw "kernel/initramfs overlap"
  let mut mem := identityMap (zeroMem memSize)
  mem := kernel.copySlice payload mem load size
  mem := kernel.copySlice 0x1F1 mem (bootParams.toNat + 0x1F1) (hdrEnd - 0x1F1)
  mem := wrBytes mem (bootParams + 0x210) 1 0xFF
  mem := wrBytes mem (bootParams + 0x211) 1 ((rd 0x211 1).toUInt64 ||| 1)
  mem := wrBytes mem (bootParams + 0x228) 4 cmdlineAddr
  mem := cl.copySlice 0 mem cmdlineAddr.toNat cl.size
  if initrd.size > 0 then
    mem := initrd.copySlice 0 mem initAddr initrd.size
    mem := wrBytes mem (bootParams + 0x218) 4 initAddr.toUInt64
    mem := wrBytes mem (bootParams + 0x21C) 4 initrd.size.toUInt64
  let e820 : List (Nat × Nat × Nat) :=
    [(0, 0x9FC00, 1), (0x9FC00, 0x400, 2), (0xF0000, 0x10000, 2), (0x100000, memSize - 0x100000, 1)]
  let mut k : UInt64 := 0
  for (base, size, typ) in e820 do
    let addr := bootParams + 0x2D0 + k * 20
    mem := wrBytes mem addr 8 base.toUInt64
    mem := wrBytes mem (addr + 8) 8 size.toUInt64
    mem := wrBytes mem (addr + 16) 4 typ.toUInt64
    k := k + 1
  mem := wrBytes mem (bootParams + 0x1E8) 1 k
  mem := wrBytes mem (bootParams + 0x1E0) 4 (memSize / 1024 - 1024).toUInt64
  mem := wrBytes mem 0x9010 8 0x00AF9B000000FFFF
  mem := wrBytes mem 0x9018 8 0x00CF93000000FFFF
  let cs := flatSeg 0x10 0xA09B
  let ds := flatSeg 0x18 0xC093
  let cpu : Cpu := {
    rip := load.toUInt64 + 0x200, rsi := bootParams, rsp := 0x9F000,
    cs, ds, es := ds, ss := ds, fs := ds, gs := ds,
    gdtBase := 0x9000, gdtLimit := 0x1F, idtLimit := 0,
    cr0 := 0x80000011, cr3 := 0x3000, cr4 := 0x20, efer := 0x500 }
  return { cpu, mem }

end X64
