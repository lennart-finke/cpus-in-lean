import X64
open X64

def hex (v : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 v.toNat)
  "".pushn '0' (16 - s.length) ++ s

def random32 (s : UInt32) : UInt32 :=
  let x := s ^^^ (s <<< 13)
  let x := x ^^^ (x >>> 17)
  x ^^^ (x <<< 5)

def makeState (bytes : ByteArray) (offset : Nat) (nativeMemory : Bool := false) : Machine := Id.run do
  let rd := fun (k n : Nat) => rdBytes bytes (offset+k).toUInt64 n.toUInt64
  let mut c : Cpu := {
    rip := 0x20100, rflags := rd 144 8,
    cs := flatSeg 0x1B 0xA0FB, ss := flatSeg 0x23 0xC0F3,
    ds := flatSeg 0x23 0xC0F3, es := flatSeg 0x23 0xC0F3,
    gdtBase := 0x22000, gdtLimit := 55,
    cr0 := 0x80000011 ||| (if rd 156 4 &&& 1 != 0 then 0x10000 else 0),
    cr3 := 0x3000, cr4 := 0x620, efer := 0xD00, mxcsr := rd 432 4 }
  for k in [0:16] do c := c.setReg k.toUInt8 (rd (16+k*8) 8)
  for k in [0:16] do c := { c with xmm := c.xmm.set! k { lo := rd (176+k*16) 8, hi := rd (184+k*16) 8 } }
  let mut mem := zeroMem 0x40000
  mem := wrBytes mem 0x3000 8 0x4027
  mem := wrBytes mem 0x4000 8 0x5027
  mem := wrBytes mem 0x5000 8 0x6027
  for k in [0:64] do mem := wrBytes mem (0x6000+k.toUInt64*8) 8 (k.toUInt64*4096 ||| 0x67)
  mem := wrBytes mem 0x6040 8 (0x8000 ||| rd 160 8)
  mem := wrBytes mem 0x6048 8 (0x9000 ||| rd 168 8)
  if nativeMemory then
    mem := wrBytes mem 0x6080 8 (0x8000 ||| rd 160 8)
    mem := wrBytes mem 0x6088 8 (0x9000 ||| rd 168 8)
  for (k,v) in [(1,0x00AF9B000000FFFF),(2,0x00CF93000000FFFF),(3,0x00AFFB000000FFFF),(4,0x00CFF3000000FFFF),(5,0x8B0000000067)] do
    mem := wrBytes mem (0x22000+k*8) 8 v
  let mut seed := (rd 152 4).toUInt32
  for k in [0:2048] do
    seed := random32 seed
    mem := wrBytes mem (0x8000+k.toUInt64*4) 4 seed.toUInt64
  if rd 156 4 &&& 2 != 0 then mem := wrBytes mem 0x8800 8 0x20180
  for k in [0:512] do mem := mem.set! (0x20000+k) 0xCC
  for k in [0:15] do mem := mem.set! (0x20100+k) (bytes.get! (offset+1+k))
  return { cpu := c, mem }

def hashMem (mem : ByteArray) : UInt32 := Id.run do
  let mut h : UInt32 := 2166136261
  for k in [0:8192] do h := (h ^^^ (mem.get! (0x8000+k)).toUInt32) * 16777619
  return h

def hashPage (mem : ByteArray) (page : Nat) : UInt64 := Id.run do
  let mut h : UInt64 := 14695981039346656037
  for k in [0:4096] do h := (h ^^^ (mem.get! (0x8000+page*4096+k)).toUInt64) * 1099511628211
  return h

/-- Complete one instruction, including REP iterations, or stop at the first TF trap.
Each iteration still uses the public model instruction function. -/
def testInstruction (m : Machine) : Except Fault (Machine × UInt64 × UInt64 × UInt64) := Id.run do
  let mut current := m
  for _ in [0:1024] do
    match instruction current with
    | .ok i m' =>
      current := m'
      if m.cpu.flag Flag.TF || i.rep == 0 || m'.cpu.rip != m.cpu.rip then
        return .ok (m', if m.cpu.flag Flag.TF && !(i.op == 0x8E && i.group == SegN.SS) then 1 else 3, 0, 0)
    | .error (.exc v e addr) m' => return .ok (m', v.toUInt64, e.getD 0, if v == Vec.PF then addr else 0)
    | .error f _ => return .error f
  return .error (.unsupported "test instruction exceeded REP iteration limit")

def main (args : List String) : IO UInt32 := do
  let nativeMemory := args.head? == some "--native-memory"
  let [path] := (if nativeMemory then args.drop 1 else args) | IO.eprintln "usage: x64test [--native-memory] vectors.bin"; return 2
  let bytes ← IO.FS.readBinFile path
  if bytes.size % 440 != 0 then IO.eprintln "invalid vector size"; return 2
  let out ← IO.getStdout
  out.putStrLn s!"BEGIN {hex (bytes.size / 440).toUInt64}"
  for k in [0:bytes.size / 440] do
    let m := makeState bytes (k*440) nativeMemory
    if let .ok i _ := decode m then
      if i.len.toNat != (bytes.get! (k*440)).toNat then
        IO.eprintln s!"vector {k}: declared instruction length disagrees with decoded length {i.len}"
        return 1
    let (m, vector, error, cr2) ← match testInstruction m with
      | .ok result => pure result
      | .error f => IO.eprintln s!"vector {k}: {repr f}"; return 1
    let mut values := [k.toUInt64, vector, error, m.cpu.rip]
    for r in [0:16] do values := values ++ [m.cpu.getReg r.toUInt8]
    values := values ++ [m.cpu.rflags, cr2, (hashMem m.mem).toUInt64,
      rdBytes m.mem 0x6040 8, rdBytes m.mem 0x6048 8]
    for r in [0:16] do values := values ++ [m.cpu.xmm[r]!.lo, m.cpu.xmm[r]!.hi]
    values := values ++ [m.cpu.mxcsr]
    if nativeMemory then values := values ++ [hashPage m.mem 0, hashPage m.mem 1]
    out.putStrLn (String.intercalate " " (values.map hex))
  out.putStrLn "END"
  return 0
