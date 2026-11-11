import X86.Step
/-!
# Linux boot protocol loader

Implements the 32-bit entry of the Linux/x86 boot protocol (Documentation/arch/x86/boot.rst):
the protected-mode kernel is placed at `code32_start`, a `boot_params` zero page with an
e820 memory map, command line and initrd is built, and the CPU starts in flat 32-bit
protected mode with `ESI` pointing to `boot_params`. No firmware and no real mode are involved.
-/
namespace X86

def bootParams : UInt32 := 0x10000
def cmdlineAddr : UInt32 := 0x20000
def gdtAddr : UInt32 := 0x9000

def u8At (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat
def u16At (b : ByteArray) (i : Nat) : Nat := u8At b i + 256 * u8At b (i+1)
def u32At (b : ByteArray) (i : Nat) : Nat := u16At b i + 65536 * u16At b (i+2)

def wr64 (mem : ByteArray) (a : UInt32) (v : Nat) : ByteArray :=
  wrBytes (wrBytes mem a 4 (v % 2^32).toUInt32) (a + 4) 4 (v / 2^32).toUInt32

def zeroMem (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n 0)

def flatSeg (sel : UInt16) (attr : UInt32) : SegReg :=
  { sel, base := 0, limit := 0xFFFFFFFF, attr }

def loadLinux (memSize : Nat) (kernel initrd : ByteArray) (cmdline : String) : Except String Machine := do
  if kernel.size < 0x300 then throw "kernel image too small"
  if u32At kernel 0x202 != 0x53726448 then throw "not a bzImage (missing HdrS)"
  let version := u16At kernel 0x206
  if version < 0x0206 then throw s!"boot protocol {version} too old"
  let setupSects := match u8At kernel 0x1F1 with | 0 => 4 | n => n
  let pmOff := (setupSects + 1) * 512
  let code32 := u32At kernel 0x214
  let pmSize := kernel.size - pmOff
  if code32 + pmSize > memSize then throw "not enough memory for the kernel"
  let mut mem := zeroMem memSize
  mem := kernel.copySlice pmOff mem code32 pmSize
  -- boot_params: copy the setup header
  let hdrEnd := 0x202 + u8At kernel 0x201
  mem := kernel.copySlice 0x1F1 mem (bootParams.toNat + 0x1F1) (hdrEnd - 0x1F1)
  let bp := bootParams
  mem := wrBytes mem (bp + 0x210) 1 0xFF                          -- type_of_loader
  mem := wrBytes mem (bp + 0x211) 1 ((u8At kernel 0x211).toUInt32 ||| 1) -- LOADED_HIGH
  mem := wrBytes mem (bp + 0x228) 4 cmdlineAddr                   -- cmd_line_ptr
  let cl := cmdline.toUTF8
  mem := cl.copySlice 0 mem cmdlineAddr.toNat cl.size
  mem := wrBytes mem (cmdlineAddr + cl.size.toUInt32) 1 0
  -- initrd near the top of memory, below initrd_addr_max
  if initrd.size > 0 then
    let maxAddr := min (u32At kernel 0x22C + 1) memSize
    let addr := (maxAddr - initrd.size) / 4096 * 4096
    if addr < code32 + pmSize then throw "not enough memory for the initrd"
    mem := initrd.copySlice 0 mem addr initrd.size
    mem := wrBytes mem (bp + 0x218) 4 addr.toUInt32
    mem := wrBytes mem (bp + 0x21C) 4 initrd.size.toUInt32
  -- e820 map
  let e820 : List (Nat × Nat × Nat) :=
    [(0, 0x9FC00, 1), (0x9FC00, 0x400, 2), (0xF0000, 0x10000, 2), (0x100000, memSize - 0x100000, 1)]
  let mut k : UInt32 := 0
  for (a, s, t) in e820 do
    let e := bp + 0x2D0 + k * 20
    mem := wr64 mem e a
    mem := wr64 mem (e + 8) s
    mem := wrBytes mem (e + 16) 4 t.toUInt32
    k := k + 1
  mem := wrBytes mem (bp + 0x1E8) 1 k
  mem := wrBytes mem (bp + 0x1E0) 4 (memSize / 1024 - 1024).toUInt32 -- alt_mem_k
  -- GDT with __BOOT_CS = 0x10 and __BOOT_DS = 0x18
  mem := wr64 mem (gdtAddr + 0x10) 0x00CF9B000000FFFF
  mem := wr64 mem (gdtAddr + 0x18) 0x00CF93000000FFFF
  let cs := flatSeg 0x10 0xC09B
  let ds := flatSeg 0x18 0xC093
  let cpu : Cpu := {
    eip := code32.toUInt32, esi := bp, esp := 0x9F000,
    cs, ds, es := ds, ss := ds, fs := ds, gs := ds,
    gdtBase := gdtAddr, gdtLimit := 0x1F, idtBase := 0, idtLimit := 0,
    cr0 := CR0.PE ||| CR0.ET }
  return { cpu, mem }

end X86
