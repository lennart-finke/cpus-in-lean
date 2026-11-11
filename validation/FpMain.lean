import X86

/-! Single-instruction IA-32 floating-point hardware replay. Input: an eight-byte count,
followed by 648-byte native records (440-byte GPR/SSE record, 144-byte x87 state,
64-byte memory patch). Format v2 (bit 63 of the count) appends YMM0..7 bits 255:128
(128 bytes) to each record and their final values (16 fields) to each output row.
No native result is an input to this executable. -/
open X86

def rdQ (v : ByteArray) (o : Nat) : UInt64 :=
  (u32At v o).toUInt64 ||| ((u32At v (o + 4)).toUInt64 <<< 32)

def memoryByte (mem : ByteArray) (kind i : Nat) : UInt8 :=
  if kind == 1 && i < 512 &&
      !(i < 5 || (24 ≤ i && i < 28) || (32 ≤ i && i < 160 && (i-32)%16 < 10) ||
        (160 ≤ i && i < 288) || 464 ≤ i) then 0
  else if (kind == 2 || kind == 3) && i < 28 &&
      !(i < 2 || (4 ≤ i && i < 6) || (8 ≤ i && i < 10)) then 0
  else mem.get! (0x10000 + i)

def fpVector (v : ByteArray) (o : Nat) (v2 : Bool := false) : Except String (List UInt64) := do
  let len := u8At v o
  if len == 0 || len > 15 then throw "invalid instruction length"
  let mut mem := zeroMem 0x40000
  let mut seed := (u32At v (o + 152)).toUInt32
  for k in [0:2048] do
    seed := seed ^^^ (seed <<< 13)
    seed := seed ^^^ (seed >>> 17)
    seed := seed ^^^ (seed <<< 5)
    mem := wrBytes mem (0x10000 + k.toUInt32 * 4) 4 seed
  for k in [0:64] do mem := mem.set! (0x10000 + k) (v.get! (o + 584 + k))
  for k in [0:len] do mem := mem.set! (0x20100 + k) (v.get! (o + 1 + k))
  -- Identity paging permits genuine not-present/read-only operand tests.
  mem := wrBytes mem 0x3000 4 0x4027
  for k in [0:64] do
    mem := wrBytes mem (0x4000 + k.toUInt32 * 4) 4 (k.toUInt32 * 4096 ||| 0x67)
  for k in [0:2] do
    mem := wrBytes mem (0x4040 + k.toUInt32 * 4) 4
      ((0x10000 + k.toUInt32 * 4096) ||| (rdQ v (o + 160 + 8*k)).toUInt32)
  let seg : SegReg := { sel := 0x2B, limit := 0xFFFFFFFF, attr := 0xC0F3 }
  let mut c : Cpu := {
    cs := { seg with sel := 0x23, attr := 0xC0FB },
    ds := seg, es := seg, ss := seg, fs := seg, gs := seg,
    -- CR0 as Linux sets it: PG, AM (alignment checking for EFLAGS.AC = 1), WP, NE, ET, MP, PE
    cr0 := 0x80050033, cr3 := 0x3000, cr4 := 0x600, eip := 0x20100,
    eflags := (rdQ v (o + 144)).toUInt32,
    fcw := (u16At v (o + 440)).toUInt16, fsw := (u16At v (o + 442)).toUInt16,
    fempty := ~~~(u16At v (o + 444)).toUInt8 }
  for k in [0:8] do
    c := c.setReg k.toUInt8 (rdQ v (o + 16 + 8*k)).toUInt32
    let f : F80 := {
      sig := rdQ v (o + 456 + 16*k), se := (u16At v (o + 464 + 16*k)).toUInt16 }
    c := { c with fpr := c.fpr.set! (c.stIdx k) f }
  let xmm := (List.range 8).map fun k =>
    ({ lo := rdQ v (o + 176 + 16*k), hi := rdQ v (o + 184 + 16*k) } : V128)
  let ymmh := if v2 then (List.range 8).toArray.map fun k =>
      ({ lo := rdQ v (o + 648 + 16*k), hi := rdQ v (o + 656 + 16*k) } : V128)
    else Array.replicate 8 {}
  c := { c with sse := { xmm := xmm.toArray, mxcsr := (u32At v (o + 432)).toUInt32, ymmh } }
  let m : Machine := { cpu := c, mem }
  let (m, vec, err) ← match execInstr m with
    | .ok _ m' => pure (m', (3 : UInt64), (0 : UInt64))
    | .error (.exc vv e _) m' => pure (m', vv.toUInt64, (e.getD 0).toUInt64)
    | .error f _ => throw s!"unsupported outcome: {repr f}"
  c := m.cpu
  let mut fields := [vec, err, c.eip.toUInt64, c.eflags.toUInt64]
  fields := fields ++ (List.range 8).map (fun k => (c.getReg k.toUInt8).toUInt64)
  for k in [0:8] do fields := fields ++ [c.xmm[k]!.lo, c.xmm[k]!.hi]
  fields := fields ++ [c.mxcsr.toUInt64, c.fcw.toUInt64, c.fsw.toUInt64,
    (~~~c.fempty).toUInt64, c.fop.toUInt64, c.fip.toUInt64, c.fdp.toUInt64]
  for k in [0:8] do fields := fields ++ [(c.st k).sig, (c.st k).se.toUInt64]
  let mut hash : UInt32 := 2166136261
  let mut pages : List UInt64 := []
  for page in [0:2] do
    let mut h : UInt64 := 14695981039346656037
    for k in [0:4096] do
      let b := memoryByte m.mem (u32At v (o + 436)) (4096*page + k)
      hash := (hash ^^^ b.toUInt32) * 16777619
      h := (h ^^^ b.toUInt64) * 1099511628211
    pages := pages ++ [h]
  let ymm := if v2 then (c.ymmh.toList.map fun x => [x.lo, x.hi]).flatten else []
  return fields ++ [hash.toUInt64] ++ pages ++ ymm

def main (args : List String) : IO UInt32 := do
  let [path] := args | do IO.eprintln "usage: x86fp native.bin"; return 2
  let v ← IO.FS.readBinFile path
  let v2 := rdQ v 0 >>> 63 == 1
  let n := (rdQ v 0 &&& 0x7FFFFFFFFFFFFFFF).toNat
  let size := if v2 then 776 else 648
  if v.size < 8 || n == 0 || n > 1000000 || v.size != 8 + n*size then
    IO.eprintln "invalid vector file"; return 2
  let hx := fun (x : UInt64) =>
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    "".pushn '0' (16 - s.length) ++ s
  IO.println s!"BEGIN {hx n.toUInt64}"
  for i in [0:n] do
    match fpVector v (8 + i*size) v2 with
    | .error e => IO.eprintln s!"vector {i}: {e}"; return 1
    | .ok fields => IO.println (String.intercalate " " ((i.toUInt64 :: fields).map hx))
  IO.println "END"
  return 0
