import Ssl
import Std.Data.HashMap
/-! Support for the executable checks: pseudo-random callers, buffer placements, and a runner that
checks every clause of `Ssl.Returns`. Test code; nothing here is part of a statement. -/
namespace Check
open X86 Ssl

def ensure (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- `n` pseudo-random bytes. -/
def bytes (n seed : Nat) : List UInt8 := Id.run do
  let mut s := lcg (seed.toUInt64 + 0x9E3779B97F4A7C15)
  let mut out := []
  for _ in [0:n] do
    s := lcg s
    out := (s >>> 33).toUInt8 :: out
  return out

/-- `n` pseudo-random 32-bit words. -/
def words (n seed : Nat) : Array UInt32 := Id.run do
  let mut s := lcg (seed.toUInt64 + 0x243F6A8885A308D3)
  let mut out := #[]
  for _ in [0:n] do
    s := lcg s
    out := out.push (s >>> 29).toUInt32
  return out

def wordBytes (ws : Array UInt32) : List UInt8 := ws.toList.flatMap le32

/-- The memory size of the ordinary placements. -/
def baseSize : Nat := 0x800000

/-- `baseSize` pseudo-random bytes. -/
def garbage (seed : UInt64) : ByteArray := Id.run do
  let mut s := seed
  let mut a := ByteArray.emptyWithCapacity baseSize
  for _ in [0:baseSize / 8] do
    s := lcg s
    let v := s ^^^ (s >>> 29)
    for k in [0:8] do
      a := a.push (v >>> (8 * k.toUInt64)).toUInt8
  return a

def put (mem : ByteArray) (addr : UInt32) (b : List UInt8) : ByteArray :=
  (ByteArray.mk b.toArray).copySlice 0 mem addr.toNat b.length

/-- `n` zero bytes, built by doubling (a byte array of gigabytes must not go through `Array`). -/
def zeros (n : Nat) : ByteArray := Id.run do
  let mut a := ByteArray.mk (Array.replicate 4096 0)
  while a.size < n do a := a ++ a
  return a.extract 0 n

/-- How large the caller's memory is, and where a check puts the stack and its (small) buffers. -/
structure Layout where
  size : Nat := baseSize
  sp : UInt32
  slots : Array UInt32
  deriving Inhabited

def Layout.slot (l : Layout) (i : Nat) : UInt32 := l.slots[i]!

/-- Four placements: the stack below the buffers; unaligned buffers below the image with the
stack at the top of memory; the stack directly above the image with buffers up to the last
bytes of memory; and a memory that ends with the last byte of the image, with the stack directly
below the image. -/
def layouts (img : Img) (stack : Nat) : List Layout :=
  [{ sp := 0x180000, slots := #[0x200000, 0x400000, 0x600000, 0x700000] },
   { sp := 0x7FFFE0, slots := #[0x1001, 0x3003, 0x5005, 0x7007] },
   { sp := ((img.base.toNat + img.bytes.size + stack + 3) / 4 * 4).toUInt32,
     slots := #[0x700001, 0x710002, 0x720003, 0x7FFF00] },
   { size := img.base.toNat + img.bytes.size, sp := img.base - 32,
     slots := #[0x1001, 0x3003, 0x5005, 0x7007] }]

/-- A memory of more than 2 GiB: the first buffer straddles address 2^31, the others and the stack
(at the top of memory) lie above it, so every pointer of the call has its top bit set. -/
def highLayouts : List Layout :=
  [{ size := 0x80200000, sp := 0x801FFFE0, slots := #[0x7FFFFFF0, 0x80001001, 0x80003003, 0x80100005] }]

/-- The class an executed instruction is counted under when comparing with the instruction fuzzer:
opcode, the ModRM `reg` field for group opcodes, memory or register operand, operand size, REP. -/
def groupOps : List UInt32 :=
  [0x80, 0x81, 0x82, 0x83, 0x8F, 0xC0, 0xC1, 0xC6, 0xC7, 0xD0, 0xD1, 0xD2, 0xD3, 0xF6, 0xF7, 0xFE, 0xFF,
   0x100, 0x101, 0x1AE, 0x1BA, 0x1C7]

def hex (v : UInt32) : String := String.ofList (Nat.toDigits 16 v.toNat)

def encKey (i : Inst) : String :=
  let grp := if groupOps.contains i.op then s!"/{i.reg}" else "/-"
  s!"op={hex i.op} {grp} {if i.isMem then "mem" else "reg"} opsz={i.opsz.toUInt32}{if i.rep != 0 then " rep" else ""}"

structure T where
  /-- Run the checks in the placements of `highLayouts` instead of `layouts`, on fewer cases. -/
  high : Bool
  base : ByteArray
  seed : IO.Ref UInt64
  /-- Deepest stack use seen per target. -/
  depth : IO.Ref (List (String × Nat))
  calls : IO.Ref Nat
  /-- Executed instruction classes, when recording. -/
  encs : Option (IO.Ref (Std.HashMap String Nat))

def T.new (record : Bool := false) (high : Bool := false) : IO T := do
  let encs ← if record then some <$> IO.mkRef {} else pure none
  return { high, base := garbage 0x5EED, seed := ← IO.mkRef 1, depth := ← IO.mkRef [], calls := ← IO.mkRef 0, encs }

def T.layouts (t : T) (img : Img) (stack : Nat) : List Layout :=
  if t.high then highLayouts else Check.layouts img stack

/-- A caller with pseudo-random registers and flags and a memory of the placement's size
(pseudo-random up to `baseSize`, zero beyond); the image, the given buffers and the call frame are
placed in its memory. -/
def T.caller (t : T) (img : Img) (L : Layout) (args : List UInt32) (bufs : List (UInt32 × List UInt8))
    (ecx edx : Option UInt32 := none) : IO Caller := do
  let s0 ← t.seed.modifyGet fun s => (s, lcg s)
  let r (k : Nat) : UInt32 := ((lcg (s0 + k.toUInt64)) >>> 24).toUInt32
  let sp := L.sp
  let mem := if L.size ≤ t.base.size then t.base.extract 0 L.size
             else t.base ++ zeros (L.size - t.base.size)
  let mem := img.bytes.copySlice 0 mem img.base.toNat img.bytes.size
  let mem := bufs.foldl (fun m (a, b) => put m a b) mem
  let mem := put mem sp ((img.halt :: args).flatMap le32)
  let regs : Regs :=
    { eax := r 0
      ecx := ecx.getD (r 1)
      edx := edx.getD (r 2)
      ebx := r 3
      esi := r 4
      edi := r 5
      ebp := r 6
      flags := r 7 }
  return { mem, sp, regs }

/-- First address whose byte differs between `a` and `b` (of equal size), outside the `allowed`
regions. Memories of gigabytes are first compared by hash, with the allowed regions of `b` replaced
by those of `a`; only a mismatch is then located byte by byte. -/
def firstChange (a b : ByteArray) (allowed : List (Nat × Nat)) : Option Nat := Id.run do
  if a.size > 4 * baseSize then
    let b' := allowed.foldl (fun b' (lo, n) => a.copySlice lo b' lo (min n (a.size - lo))) b
    if hash a == hash b' then return none
  for i in [0:a.size] do
    if a.get! i != b.get! i then
      if !(allowed.any fun (lo, n) => lo ≤ i && i < lo + n) then return some i
  return none

/-- Run the call and check every clause of `Returns img (c.enter fn) stack W`; `W` is given as
regions. Returns the final machine for the task-specific checks. -/
def T.call (t : T) (target : String) (img : Img) (c : Caller) (fn : UInt32) (stack : Nat)
    (W : List (UInt32 × Nat)) : IO Machine := do
  let m0 := c.enter fn
  let mut m := m0
  let mut lo := c.sp
  let mut fuel := 60000000
  while fuel > 0 && !(returned img m || m.fatal.isSome || m.cpu.halted) do
    if let some encs := t.encs then
      if let .ok i _ := decode m then encs.modify fun h => h.insert (encKey i) (h.getD (encKey i) 0 + 1)
    m := X86.step m
    if m.cpu.esp < lo then lo := m.cpu.esp
    fuel := fuel - 1
  ensure s!"{target}: did not return (eip={m.cpu.eip}, fatal={reprStr m.fatal})"
    (returned img m && m.cpu.esp == c.sp + 4 && m.cpu.eflags &&& Flag.DF == 0)
  ensure s!"{target}: callee-saved registers"
    (m.cpu.ebx == c.regs.ebx && m.cpu.esi == c.regs.esi && m.cpu.edi == c.regs.edi && m.cpu.ebp == c.regs.ebp)
  let used := c.sp.toNat - lo.toNat
  ensure s!"{target}: used {used} bytes of stack, more than the stated {stack}" (used ≤ stack)
  ensure s!"{target}: memory size" (m.mem.size == c.mem.size)
  let allowed := (c.sp.toNat - stack, stack) :: W.map fun (a, n) => (a.toNat, n)
  if let some a := firstChange c.mem m.mem allowed then
    throw (IO.userError s!"{target}: byte at {a} changed outside the writable set and the stack")
  t.depth.modify fun d =>
    match d.lookup target with
    | some old => if used > old then (target, used) :: d.filter (·.1 != target) else d
    | none => (target, used) :: d
  t.calls.modify (· + 1)
  return m

def T.report (t : T) (bounds : List (String × Nat)) : IO Unit := do
  let d ← t.depth.get
  for (target, bound) in bounds do
    IO.println s!"stack: {target} used at most {(d.lookup target).getD 0} of the stated {bound} bytes"
  IO.println s!"{← t.calls.get} calls checked against their contracts"

def T.printEncodings (t : T) : IO Unit := do
  if let some encs := t.encs then
    for (k, n) in (← encs.get).toArray.qsort (fun a b => a.1 < b.1) do
      IO.println s!"{k} {n}"

end Check
