import X86.Mp
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

/-! ## MP tables (Intel MultiProcessor Specification 1.4, chapter 4)

The guest kernels have no ACPI, so the CPUs and the I/O APIC are described by an MP floating pointer
structure (at `mpFloat`, in the BIOS area 0xF0000–0xFFFFF that Linux scans and the e820 map reserves)
and an MP configuration table (at `mpConfig`): one processor entry per CPU (APIC ID = CPU number,
local APIC version 10h, enabled, CPU 0 the boot processor, signature and feature flags from CPUID
leaf 1), an ISA bus, the I/O APIC (ID `ioApicId N`, version 11h, at 0xFEC00000), I/O interrupt entries for ISA
IRQs 0..15 except 2 with IRQ 0 on pin 2 (conforming polarity and trigger), and the local interrupt
entries ExtINT → LINT0 of the boot processor and NMI → LINT1 of every CPU: the layout SeaBIOS
generates for QEMU. Feature byte 2 bit 7 (IMCRP) = 0: virtual-wire mode, no IMCR. -/

/-- The I/O APIC's ID for `n` CPUs (local APIC IDs 0..n−1): `n` while that fits the 82093AA's 4-bit ID
register below the serial-bus broadcast ID 15 (n ≤ 14: an ID no local APIC has), otherwise 0. With n ≥ 15 no 4-bit ID is free;
on xAPIC systems (the system bus of the 7742) I/O APIC and local APIC IDs are separate name spaces, and
QEMU/SeaBIOS give the I/O APIC ID 0 for any number of CPUs. The MP table and the ID register always
agree. Supported: 1 ≤ n ≤ 128 (the threads of one 7742 package, `Cpuid.topo`; xAPIC IDs < 255). Linux
checks the IDs for uniqueness only on Intel CPUs without xAPIC (`setup_ioapic_ids_from_mpc`): with the
AMD identity it boots with 16, 32 and 64 CPUs (guest/build.sh bigsmp); the former Intel identity
needed n ≤ 14. -/
def ioApicId (n : Nat) : UInt32 := if n ≤ 14 then n.toUInt32 else 0

/-- The largest number of CPUs `MpMachine` supports (one EPYC 7742 package). -/
def maxCpus : Nat := 128

def mpFloat : UInt32 := 0xF0000
def mpConfig : UInt32 := 0xF0010

/-- `n` little-endian bytes of `v`. -/
def leBytes (n v : Nat) : List UInt8 := (List.range n).map fun i => (v / 256 ^ i % 256).toUInt8

/-- Set byte `i` to the value that makes the byte sum 0 mod 256. -/
def withChecksum (b : List UInt8) (i : Nat) : List UInt8 :=
  b.set i (0 - b.foldl (· + ·) 0)

/-- The MP configuration table for `n` CPUs (`c`: the boot processor, for CPUID leaf 1). -/
def mpConfigTable (c : Cpu) (n : Nat) : List UInt8 :=
  let (sig, _, _, feat) := cpuid c 1 0
  let procs := (List.range n).flatMap fun k =>
    [0, k.toUInt8, 0x10, if k == 0 then 3 else 1] ++ leBytes 4 sig.toNat ++ leBytes 4 feat.toNat ++ leBytes 8 0
  let bus := [1, 0] ++ "ISA   ".toUTF8.toList
  let ioapic := [2, (ioApicId n).toUInt8, 0x11, 1] ++ leBytes 4 0xFEC00000
  let ints := ((List.range 16).filter (· != 2)).flatMap fun irq =>
    [3, 0, 0, 0, 0, irq.toUInt8, (ioApicId n).toUInt8, (if irq == 0 then 2 else irq).toUInt8]
  let locals := [4, 3, 0, 0, 0, 0, 0, 0] ++ [4, 1, 0, 0, 0, 0, 0xFF, 1]
  let body := procs ++ bus ++ ioapic ++ ints ++ locals
  let count := n + 1 + 1 + 15 + 2
  let hdr := "PCMP".toUTF8.toList ++ leBytes 2 (44 + body.length) ++ [4, 0] ++ "LEANX86 ".toUTF8.toList ++
    "EPYC 7742   ".toUTF8.toList ++ leBytes 4 0 ++ leBytes 2 0 ++ leBytes 2 count ++ leBytes 4 0xFEE00000 ++
    leBytes 2 0 ++ [0, 0]
  withChecksum (hdr ++ body) 7

/-- The MP floating pointer structure (16 bytes) pointing at `mpConfig`. -/
def mpFloatingPointer : List UInt8 :=
  withChecksum ("_MP_".toUTF8.toList ++ leBytes 4 mpConfig.toNat ++ [1, 4, 0, 0, 0, 0, 0, 0]) 10

/-- Write the MP tables for `n` CPUs into memory. -/
def placeMpTables (mem : ByteArray) (c : Cpu) (n : Nat) : ByteArray :=
  let put := fun (mem : ByteArray) (a : UInt32) (b : List UInt8) =>
    (b.zip (List.range b.length)).foldl (fun mem (x, i) => wrBytes mem (a + i.toUInt32) 1 x.toUInt32) mem
  put (put mem mpFloat mpFloatingPointer) mpConfig (mpConfigTable c n)

/-- Load a Linux bzImage. With `smp = n > 0` the MP tables for `n` CPUs are placed and the I/O APIC
gets ID `ioApicId n` (as firmware assigns it); the CPUs themselves are added by `MpMachine.ofMachine`. -/
def loadLinux (memSize : Nat) (kernel initrd : ByteArray) (cmdline : String) (smp : Nat := 0) :
    Except String Machine := do
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
  if smp == 0 then return { cpu, mem }
  let cpu := { cpu with smpx := { cpu.smpx with ncpu := smp.toUInt32 } }
  return { cpu, mem := placeMpTables mem cpu smp, ioapic := { id := ioApicId smp } }

end X86
