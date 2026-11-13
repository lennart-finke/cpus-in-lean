import X86

/-! Single-instruction IA-32 floating-point hardware replay. Input: an eight-byte count,
followed by 648-byte native records (440-byte GPR/SSE record, 144-byte x87 state,
64-byte memory patch). Format v2 (bit 63 of the count) appends YMM0..7 bits 255:128
(128 bytes) to each record and their final values (16 fields) to each output row.
Format v3 (bits 63 and 62) appends a further 128-byte extension (below) to each v2 record and
11 fields to each output row. No native result is an input to this executable.

`x86fp --compat` runs each case as the native oracle really runs it: in compatibility mode under a
64-bit Linux (EFER.LME/LMA/NXE/SCE set, 4-level paging, CR4 = 0035_0EF0h as Linux sets it on a 7742
(PAE, PSE, PGE, MCE, OSFXSR, OSXMMEXCPT, OSXSAVE, UMIP, FSGSBASE, SMEP, SMAP), a 32-bit DPL-3 code
segment with L = 0, the user selectors 0x23/0x2B of Linux's __USER32_CS/__USER_DS; FS and GS hold
0x2B too, as the oracle loads them). (Linux emulates SGDT/SIDT/SMSW that UMIP makes #GP for 32-bit
processes; the model reports the #GP.) Without the flag the case runs in legacy protected mode
(32-bit paging).

IN/OUT/INS/OUTS find no I/O permission bitmap (#GP(0)), as in a Linux process without ioperm.

The address space is the oracle process's below 4 GiB (native/signal_oracle.c): the two data pages
at 0x10000 with the record's PTEs (0 unmapped, 0x65 read-only, 0x67 writable), the code page at
0x20000 present, user and read-only (the oracle maps it PROT_READ|PROT_EXEC) and filled with 0xCC
outside the instruction at 0x20100, and nothing else (every other page of the identity-mapped
256 KiB is not present, so a stray access is a #PF with its CR2 here as on the processor; the oracle's
own image at 1 MiB is outside the model's memory). A single-step trap (EFLAGS.TF = 1 in the input)
is reported as vector 1 after an instruction that completes, as the processor's #DB (`stepInstr`); a
REP string instruction interrupted by the model's iteration chunk (`Exec.repChunk`) is continued
until it completes (the processor runs it to completion between the two signals; with TF = 1 one
iteration, as the processor's trap after each iteration).

v3 extension (record offset 776, 128 bytes): +0 flags (bit 0: the x87 FIP/FDP/FOP below are the
input's; bit 1: dump the 64 arena bytes at the offset below), +4 FOP (u16), +6 dump offset (u16,
within the 8 KiB arena), +8 FIP (u64, the 64-bit layout of the signal frame), +16 FDP (u64), +24 the
number (0..8) of dword patches of the arena at +32 (8 bytes each: offset u16, dword count u16 (0 = 1),
value u32: the value stored count times from the offset; applied in order after the 64-byte patch), +28 the mode (0: the 32-bit code segment; 1: a 16-bit code
segment, CS 07h based at 20000h with IP 0100h, DS = ES = 0Fh based at the arena, as the oracle's LDT); the
rest is reserved (0). Extra output fields: FIP and FDP as 64-bit values, CR2 of a #PF (else 0), and the
dumped bytes as eight little-endian quadwords (zeros without bit 1).

`x86fp [--compat] --probe FILE` prints, for every case, `index status vector error eip cr2 length
op modrm vex` (status 0, or 1 when the model cannot run the case, which the normal mode reports as an
error) instead of the comparison row: the native campaign's generators use it to select fuzz cases
(test/native_filter.py). -/
open X86

def rdQ (v : ByteArray) (o : Nat) : UInt64 :=
  (u32At v o).toUInt64 ||| ((u32At v (o + 4)).toUInt64 <<< 32)

def memoryByte (mem : ByteArray) (kind i : Nat) : UInt8 :=
  if kind == 1 && i < 512 &&
      !(i < 5 || (24 ≤ i && i < 28) || (32 ≤ i && i < 160 && (i-32)%16 < 10) ||
        (160 ≤ i && i < 288) || 464 ≤ i) then 0
  else if (kind == 2 || kind == 3) && i < 28 &&
      !(i < 2 || (4 ≤ i && i < 6) || (8 ≤ i && i < 10)) then 0
  -- XSAVE images (test/native_xsave.py): reserved bytes 5, 14..15, 22..23, MXCSR_MASK, the
  -- padding of the x87 register slots and bytes 288..463 of the legacy region are not compared
  else if kind == 4 && i < 512 &&
      (i == 5 || i == 14 || i == 15 || i == 22 || i == 23 || (28 ≤ i && i < 32) ||
       (32 ≤ i && i < 160 && (i-32)%16 ≥ 10) || (288 ≤ i && i < 464)) then 0
  else mem.get! (0x10000 + i)

/-- The PTE of page `k` of the low 256 KiB: the data pages from the record, the read-only code page,
nothing else (the oracle process maps nothing else there). -/
def pte (v : ByteArray) (o k : Nat) : UInt64 :=
  if k == 16 || k == 17 then (0x10000 + (k.toUInt64 - 16) * 4096) ||| rdQ v (o + 160 + 8*(k - 16))
  else if k == 32 then 0x20000 ||| 0x65
  else 0

/-- A REP string instruction (INS/OUTS/MOVS/CMPS/STOS/LODS/SCAS with a REP prefix). -/
def repString (i : Inst) : Bool :=
  !i.vex && i.rep != 0 &&
    ((0x6C ≤ i.op && i.op ≤ 0x6F) || (0xA4 ≤ i.op && i.op ≤ 0xA7) || (0xAA ≤ i.op && i.op ≤ 0xAF))

structure Outcome where
  m : Machine
  vec : UInt64
  err : UInt64
  cr2 : UInt64
  inst : Option Inst
  unsupported : Option String := none

def fpCase (v : ByteArray) (o : Nat) (v2 v3 compat : Bool) : Except String (Machine × Outcome) := do
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
  -- v3: up to eight further dword patches of the arena
  if v3 then
    for k in [0:min 8 (u8At v (o + 800))] do
      let off := u16At v (o + 808 + 8*k)
      let n := max 1 (u16At v (o + 810 + 8*k))
      if off + 4 * n ≤ 8192 then
        for i in [0:n] do
          mem := wrBytes mem (0x10000 + (off + 4*i).toUInt32) 4 (u32At v (o + 812 + 8*k)).toUInt32
  -- the oracle's code page: INT3 everywhere but the instruction
  for k in [0:4096] do mem := mem.set! (0x20000 + k) 0xCC
  for k in [0:len] do mem := mem.set! (0x20100 + k) (v.get! (o + 1 + k))
  -- legacy mode: 32-bit paging, PD 0x3000 -> PT 0x4000
  mem := wrBytes mem 0x3000 4 0x4027
  for k in [0:64] do
    mem := wrBytes mem (0x4000 + k.toUInt32 * 4) 4 (pte v o k).toUInt32
  -- compatibility mode: PML4 0x5000 -> PDPT 0x6000 -> PD 0x7000 -> PT 0x8000 (64-bit entries)
  if compat then
    mem := wrBytes mem 0x5000 4 0x6027
    mem := wrBytes mem 0x6000 4 0x7027
    mem := wrBytes mem 0x7000 4 0x8027
    for k in [0:64] do
      let e := pte v o k
      mem := wrBytes mem (0x8000 + k.toUInt32 * 8) 4 e.toUInt32
      mem := wrBytes mem (0x8000 + k.toUInt32 * 8 + 4) 4 (e >>> 32).toUInt32
  let seg : SegReg := { sel := 0x2B, limit := 0xFFFFFFFF, attr := 0xC0F3 }
  let mut c : Cpu := {
    cs := { seg with sel := 0x23, attr := 0xC0FB },
    ds := seg, es := seg, ss := seg, fs := seg, gs := seg,
    -- Linux's TSS has no I/O permission bitmap for the oracle (no ioperm: the bitmap offset is invalid),
    -- so IN/OUT/INS/OUTS at CPL 3 are #GP(0); a TSS limit below 67h gives that without memory reads
    -- (`Exec.ioCheck`); the model's default TR would read an I/O map base at linear 66h
    tr := { sel := 0x40, base := 0, limit := 0x66, attr := 0x8B },
    -- CR0 as Linux sets it: PG, AM (alignment checking for EFLAGS.AC = 1), WP, NE, ET, MP, PE
    cr0 := 0x80050033, cr3 := 0x3000, eip := 0x20100,
    -- as Linux on the target: CR4.OSFXSR, OSXMMEXCPT, OSXSAVE; XCR0 = 7; the x87, SSE and AVX
    -- state loaded from the signal frame by XRSTOR with XSTATE_BV[2:0] = 111b (XINUSE = 7)
    cr4 := 0x40600, xcr0 := 7, xsx := { inuse := 7 },
    eflags := (rdQ v (o + 144)).toUInt32,
    -- the oracle loads the x87 state from the signal frame with XRSTOR, which sets B = ES (`fswLoad`)
    -- and loads the control word's reserved bits as every x87 load does (`fcwLoad`)
    fcw := fcwLoad (u16At v (o + 440)).toUInt32,
    fsw := fswLoad (u16At v (o + 442)).toUInt16 (u16At v (o + 440)).toUInt16,
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
  -- v3: the x87 error pointers and opcode the oracle installs in the signal frame (64-bit layout:
  -- no FCS/FDS, which stay 0)
  if v3 && u32At v (o + 776) &&& 1 != 0 then
    c := { c with fop := ((u16At v (o + 780)) &&& 0x7FF).toUInt16, fip := (rdQ v (o + 784)).toUInt32,
                  fdp := (rdQ v (o + 792)).toUInt32 }
  -- v3 mode 1: a 16-bit code segment (the oracle's LDT entries, modify_ldt): CS 07h with base 20000h and
  -- limit FFFh (byte granular, D = 0), DS = ES = 0Fh (16-bit data, base 10000h = the arena, limit 1FFFh);
  -- SS, FS and GS stay flat 32-bit; IP 0100h
  if v3 && u8At v (o + 804) == 1 then
    c := { c with cs := { sel := 0x07, base := 0x20000, limit := 0xFFF, attr := 0x00FB },
                  ds := { sel := 0x0F, base := 0x10000, limit := 0x1FFF, attr := 0x00F3 },
                  es := { sel := 0x0F, base := 0x10000, limit := 0x1FFF, attr := 0x00F3 }, eip := 0x100 }
  if compat then
    -- CR4 as 64-bit Linux 6.x sets it on an EPYC 7742 (CPUID 7:EBX FSGSBASE/SMEP/SMAP, 7:ECX UMIP; no
    -- PCID, PKU, LA57): PSE, PAE, MCE, PGE (head_64.S, mm/init.c), OSFXSR, OSXMMEXCPT (fpu/init.c),
    -- OSXSAVE (fpu/xstate.c), SMEP, SMAP, UMIP (setup_smep/setup_smap/setup_umip, CONFIG_X86_UMIP=y),
    -- FSGSBASE (identify_cpu) = 0035_0EF0h; DE, TSD, PCE, VME, PVI clear (cpu_init, per task/mm)
    c := { c with cr3 := 0x5000, cr4 := 0x350EF0,
                  efer := EFER.SCE ||| EFER.LME ||| EFER.LMA ||| EFER.NXE }
  let m : Machine := { cpu := c, mem }
  let tf := c.eflags &&& Flag.TF != 0
  let start := c.eip
  -- a REP string instruction is continued until it completes (bounded: the arena is 8 KiB)
  let mut cur := m
  let mut out : Option Outcome := none
  for _ in [0:1024] do
    match execInstr cur with
    | .ok i m' =>
      if !tf && repString i && m'.cpu.eip == start then
        cur := m'
      else
        let vec : UInt64 := if tf && !noStepTrap i then 1 else 3
        out := some { m := m', vec, err := 0, cr2 := 0, inst := some i }
        break
    | .error (.exc vv e a) m' =>
      out := some { m := m', vec := vv.toUInt64, err := (e.getD 0).toUInt64,
                    cr2 := if vv == 14 then a.toUInt64 else 0, inst := none }
      break
    | .error f m' =>
      out := some { m := m', vec := 0, err := 0, cr2 := 0, inst := none, unsupported := some s!"{repr f}" }
      break
  match out with
  | some r => return (m, r)
  | none => throw "REP string instruction did not complete"

def fpVector (v : ByteArray) (o : Nat) (v2 : Bool := false) (compat : Bool := false) (v3 : Bool := false) :
    Except String (List UInt64) := do
  let (_, r) ← fpCase v o v2 v3 compat
  if let some f := r.unsupported then throw s!"unsupported outcome: {f}"
  let m := r.m
  let c := m.cpu
  let mut fields := [r.vec, r.err, c.eip.toUInt64, c.eflags.toUInt64]
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
  let ext ← if !v3 then pure [] else do
    let flags := u32At v (o + 776)
    let off := u16At v (o + 782)
    if off + 64 > 8192 then throw "dump window outside the arena"
    let dump := (List.range 8).map fun q =>
      if flags &&& 2 == 0 then (0 : UInt64)
      else (List.range 8).foldl (fun acc b => acc ||| ((m.mem.get! (0x10000 + off + 8*q + b)).toUInt64 <<< (8*b).toUInt64)) 0
    pure ([c.fip.toUInt64, c.fdp.toUInt64, r.cr2] ++ dump)
  return fields ++ [hash.toUInt64] ++ pages ++ ymm ++ ext

/-- `--probe`: what the case selection of the generators needs (test/native_filter.py). -/
def fpProbe (v : ByteArray) (o : Nat) (v2 v3 compat : Bool) : Except String (List UInt64) := do
  let (m0, r) ← fpCase v o v2 v3 compat
  let (len, op, modrm, vex) := match decode m0 with
    | .ok i _ => (i.len.toUInt64, i.op.toUInt64, i.modrm.toUInt64,
                  (if i.vex then 1 else 0) ||| (i.pp.toUInt64 <<< 1) ||| ((if i.vexL then 1 else 0) <<< 3) |||
                  ((if i.vexW then 1 else 0) <<< 4) ||| ((if i.isMem then 1 else 0) <<< 5) |||
                  (i.rep.toUInt64 <<< 8) ||| ((if i.p66 then 1 else 0) <<< 16) ||| (i.adsz.toUInt64 <<< 20) |||
                  (i.opsz.toUInt64 <<< 24) ||| ((if i.lock then 1 else 0) <<< 28))
    | .error _ _ => (0, 0, 0, 0)
  let status : UInt64 := if r.unsupported.isSome then 1 else 0
  return [status, r.vec, r.err, r.m.cpu.eip.toUInt64, r.cr2, len, op, modrm, vex]

def main (args : List String) : IO UInt32 := do
  let (compat, args) := if args.head? == some "--compat" then (true, args.drop 1) else (false, args)
  let (probe, args) := if args.head? == some "--probe" then (true, args.drop 1) else (false, args)
  let [path] := args | do IO.eprintln "usage: x86fp [--compat] [--probe] native.bin"; return 2
  let v ← IO.FS.readBinFile path
  let v2 := rdQ v 0 >>> 63 == 1
  let v3 := v2 && (rdQ v 0 >>> 62) &&& 1 == 1
  let n := (rdQ v 0 &&& 0x3FFFFFFFFFFFFFFF).toNat
  let size := if v3 then 904 else if v2 then 776 else 648
  if v.size < 8 || n == 0 || n > 1000000 || v.size != 8 + n*size then
    IO.eprintln "invalid vector file"; return 2
  let hx := fun (x : UInt64) =>
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    "".pushn '0' (16 - s.length) ++ s
  IO.println s!"BEGIN {hx n.toUInt64}"
  for i in [0:n] do
    match (if probe then fpProbe v (8 + i*size) v2 v3 compat else fpVector v (8 + i*size) v2 compat v3) with
    | .error e => IO.eprintln s!"vector {i}: {e}"; return 1
    | .ok fields => IO.println (String.intercalate " " ((i.toUInt64 :: fields).map hx))
  IO.println "END"
  return 0
