import X86
import X86.Tso
/-!
# x86test — differential testing of the model against QEMU

    x86test vectors.bin vectors.metaLines qemu.out

Rebuilds, for every vector, the machine state the QEMU harness (test/harness) sets up:
ring 3, flat user segments, GDT at 0x1000, TSS at 0x1800, IDT base 0x2000, optional paging
(page directory 0x3000, identity page table 0x4000, per-vector PTEs for the data pages 8 and 9,
CR0.WP), data area at 0x8000 (8 KiB) filled by xorshift32, code buffer at 0x20000 filled with
INT3. Executes exactly one instruction with the model and compares the outcome (exception vector,
error code and CR2, or EIP, GPRs, defined EFLAGS, segment selectors, a hash of the data area and
the two PTEs including accessed/dirty bits) with QEMU's.

Record format v2 (a 16-byte header `X86VEC\0\2`, record size, 0; see `test/gen.py`) adds MXCSR and
vector flags to each vector: CR4.OSFXSR/OSXMMEXCPT are set (with flag bit 0 also CR4.OSXSAVE and
XCR0 = 7), XMM0-7 and YMM0-7[255:128] start from `vecPattern`, and MXCSR, XMM0-7 and the YMM upper
halves (zero without flag bit 0) are compared too. Version 1 (88 bytes, no header) is unchanged.
-/
open X86

def DATA : UInt32 := 0x8000
def CODE : UInt32 := 0x20000

def xorshift (s : UInt32) : UInt32 :=
  let x := s ^^^ (s <<< 13)
  let x := x ^^^ (x >>> 17)
  x ^^^ (x <<< 5)

def segDesc (base limit typ flags : UInt32) : Nat :=
  let lo : Nat := ((limit &&& 0xFFFF) ||| ((base &&& 0xFFFF) <<< 16)).toNat
  let hi : Nat := (((base >>> 16) &&& 0xFF) ||| (typ <<< 8) ||| (limit &&& 0xF0000) |||
                   (flags <<< 20) ||| (base &&& 0xFF000000)).toNat
  lo + hi * 2^32

def gdt : List Nat := [0,
  segDesc 0 0xfffff 0x9b 0xc, segDesc 0 0xfffff 0x93 0xc, segDesc 0 0xfffff 0xfb 0xc,
  segDesc 0 0xfffff 0xf3 0xc, segDesc 0x8000 0xfff 0xf3 0x4, segDesc 0 0x7fff 0xf7 0x4,
  segDesc 0 0xfffff 0xf1 0xc, segDesc 0x1800 0x67 0x8b 0x0, segDesc 0 0xfffff 0x93 0xc,
  segDesc 0 0xfffff 0x73 0xc, segDesc 0 0xffff 0xfb 0x0, segDesc 0 0xffff 0xf3 0x0,
  segDesc 0 0xfffff 0xf9 0xc]

def fnv (mem : ByteArray) : UInt32 := Id.run do
  let mut h : UInt32 := 2166136261
  for i in [0:8192] do
    h := (h ^^^ (mem.get! (DATA.toNat + i)).toUInt32) * 16777619
  return h

structure Outcome where
  vec : UInt32
  err : UInt32
  eip : UInt32
  regs : Array UInt32   -- eax ecx edx ebx esp ebp esi edi
  eflags : UInt32
  segs : Array UInt32   -- ds es fs gs ss
  hash : UInt32
  cr2 : UInt32
  pte8 : UInt32
  pte9 : UInt32
  pageHashes : List UInt32 := []
  /-- v2: MXCSR, XMM0-7 and YMM0-7[255:128] as 32-bit words (low word first). -/
  vecs : List UInt32 := []
  deriving BEq, Repr

def v2Magic : List UInt8 := [0x58, 0x38, 0x36, 0x56, 0x45, 0x43, 0, 2]

/-- Header size and record size of a vector file (v1: no header, 88-byte records). -/
def vecFormat (v : ByteArray) : Nat × Nat :=
  if v.size ≥ 16 && (List.range 8).all (fun k => v.get! k == v2Magic[k]!) then
    (16, u32At v 8)
  else (0, 88)

/-- Initial XMM0-7 and YMM0-7[255:128] words of a v2 vector (as `vec_pattern` in test/gen.py). -/
def vecPattern (seed : UInt32) : Array UInt32 := Id.run do
  let mut s := seed ^^^ 0xA5A5A5A5
  let mut out := #[]
  for _ in [0:64] do
    s := xorshift s
    out := out.push s
  return out

def v128Of (w : Array UInt32) (k : Nat) : V128 :=
  { lo := w[4*k]!.toUInt64 ||| (w[4*k+1]!.toUInt64 <<< 32),
    hi := w[4*k+2]!.toUInt64 ||| (w[4*k+3]!.toUInt64 <<< 32) }

def v128Words (x : V128) : List UInt32 :=
  [x.lo.toUInt32, (x.lo >>> 32).toUInt32, x.hi.toUInt32, (x.hi >>> 32).toUInt32]

def baseMachine : Machine := Id.run do
  let mut mem := ByteArray.mk (Array.replicate 0x40000 0)
  let mut k : UInt32 := 0
  for d in gdt do
    mem := wr64 mem (0x1000 + k * 8) d
    k := k + 1
  mem := wrBytes mem (0x1800 + 0x64) 4 (0x68 <<< 16)
  mem := wrBytes mem 0x3000 4 (0x4000 ||| 0x27)
  for i in [0:1024] do
    mem := wrBytes mem (0x4000 + 4 * i.toUInt32) 4 ((i.toUInt32 <<< 12) ||| 0x67)
  let user (sel : UInt16) (attr : UInt32) : SegReg := { sel, base := 0, limit := 0xFFFFFFFF, attr }
  let cpu : Cpu := {
    cs := user 0x1B 0xC0FB, ss := user 0x23 0xC0F3, ds := user 0x23 0xC0F3,
    es := user 0x23 0xC0F3, fs := user 0x23 0xC0F3, gs := user 0x23 0xC0F3,
    gdtBase := 0x1000, gdtLimit := 14 * 8 - 1, idtBase := 0x2000, idtLimit := 20 * 8 - 1,
    tr := { sel := 0x40, base := 0x1800, limit := 0x67, attr := 0x8B },
    ldtr := { sel := 0, base := 0, limit := 0, attr := 0 },
    cr0 := 0x31 }
  return { cpu, mem }

/-- Read-modify-write instructions with a memory destination: the model, like the CPU of the
2026-10-22 hardware campaign, translates the destination with write intent on the first access
(`rmwE`, XADD, CMPXCHG, CMPXCHG8B, BTS/BTR/BTC); QEMU's TCG reads it first and writes afterwards. -/
def rmwDest (i : Inst) : Bool :=
  lockOk i || (i.isMem &&
    (i.op == 0xC0 || i.op == 0xC1 || (0xD0 ≤ i.op && i.op ≤ 0xD3) ||          -- shifts, rotates
     i.op == 0x1A4 || i.op == 0x1A5 || i.op == 0x1AC || i.op == 0x1AD ||      -- SHLD, SHRD
     i.op == 0x63))                                                           -- ARPL

/-- (Avx) VEX encodings that are #UD on the CPU (and in the model) but that TCG (QEMU 11.1.2)
executes:
* the MMX-register forms with a VEX prefix (VEX.pp = 00 of the 0F-map MMX instructions, of the SSSE3
  0F 38 00..0B, 1C..1E and of PALIGNR 0F 3A 0F): VEX encodes only the XMM/YMM forms (SDM vol. 2,
  appendix A, tables A-3..A-5: the "v" forms are the 66/F2/F3 columns; AMD APM vol. 4 lists no VEX form
  of an MMX instruction);
* legacy-only SSE forms without a VEX encoding: SSE4.1 PBLENDVB/BLENDVPS/BLENDVPD with the implicit
  XMM0 (66 0F 38 10, 14, 15; their VEX forms are 0F 3A 4C, 4A, 4B), SSE4a MOVNTSS/MOVNTSD (F3/F2 0F 2B),
  VEX.66/F3/F2.0F 77 (VZEROUPPER/VZEROALL exist only with VEX.pp = 00, APM: "X.1111.L.00");
* VEX.L = 1 of VEX.128-only forms (APM vol. 4 exception tables "VEX.L = 1"): VMOVD r/m32, xmm
  (66 0F 7E), VMOVLPS/PD and VMOVHPS/PD stores (0F 13, 17);
* the register forms of memory-only forms (APM "ModRM.mod = 11b" / SDM "#UD if ... register"):
  VMOVLPD, VMOVHPD (66 0F 12, 16), VMOVNTDQ (66 0F E7), VMOVNTPS/PD (0F 2B). -/
def tcgVexUd (i : Inst) : Bool :=
  i.vex && (
    (i.pp == 0 && ((i.map == 1 && (isPint i.byte || [0x6E, 0x6F, 0x70, 0x71, 0x72, 0x73, 0x7E, 0x7F, 0xC4,
        0xC5, 0xD7, 0xE7, 0xF7].contains i.byte)) ||
      (i.map == 2 && (i.byte ≤ 0x0B || (0x1C ≤ i.byte && i.byte ≤ 0x1E))) || (i.map == 3 && i.byte == 0x0F))) ||
    (i.map == 2 && i.pp == 1 && [0x10, 0x14, 0x15].contains i.byte) ||
    (i.map == 1 && i.pp ≥ 2 && i.byte == 0x2B) ||
    (i.map == 1 && i.pp != 0 && i.byte == 0x77) ||
    (i.vexL && i.map == 1 && ((i.pp == 1 && i.byte == 0x7E) || (i.pp ≤ 1 && (i.byte == 0x13 || i.byte == 0x17)))) ||
    (!i.isMem && i.map == 1 && ((i.pp == 1 && [0x12, 0x16, 0xE7].contains i.byte) ||
      (i.pp ≤ 1 && i.byte == 0x2B))))

/-- QEMU (TCG) behaviours that differ from the hardware the model was checked against (README):
* RMW destinations: TCG reads first, so a #PF on the destination has the W bit clear; its read
  translation sets only A where the write-intent translation sets A and D (or faults before setting
  A); and for an operand crossing into the next page, a readable but read-only first page lets TCG's
  read reach the second page and fault there. The CPU reports a write fault from the first access, at
  the operand start when the first page is not writable (hardware campaign, README).
* PUSHA: TCG probes the whole push range first and faults at its start with nothing written; the CPU
  pushes in order, keeps completed pushes and faults at the first failing push.
* SYSRET with EFER.SCE = 0 at CPL 3 (system A): the APM checks SCE first (#UD), then protected mode
  and CPL (#GP(0)) (AMD APM vol. 3, SYSRET, SYSRET_START); TCG checks the CPL first and raises #GP(0).
`qemuAsHardware i qo lo init` rewrites exactly those fields of QEMU's outcome `qo` to the model's
`lo` when they show the TCG signature; every other field is still compared. -/
def qemuAsHardware (i : Inst) (qo lo : Outcome) (initHash : UInt32) : Outcome := Id.run do
  if i.op == 0x107 && !i.vex && qo.vec == 13 && qo.err == 0 && lo.vec == 6 then
    return { qo with vec := 6, err := lo.err }
  -- (Crypto) SHA1NEXTE..SHA256MSG2 (0F 38 C8..CD) and SHA1RNDS4 (0F 3A CC) are "NP" instructions:
  -- with a 66, F2 or F3 prefix they are #UD (SDM vol. 2, 3.1.1.1 and the instruction pages; Bochs
  -- decodes them only without prefix). TCG decodes them with any prefix and runs them.
  if !i.vex && i.pp != 0 && ((0x2C8 ≤ i.op && i.op ≤ 0x2CD) || i.op == 0x3CC) && lo.vec == 6 then
    return lo
  -- (Avx) VEX encodings TCG executes although they are #UD (QEMU's completion or fault, or the
  -- accessed bits its memory access set before its #UD, are replaced by the model's #UD; see
  -- `tcgVexUd`)
  if lo.vec == 6 && tcgVexUd i then return lo
  -- (Avx, Avx2) Masked stores (VMASKMOVPS/PD, VEX.66.0F38 2E/2F; VPMASKMOVD/Q, VEX.66.0F38 8E;
  -- VMASKMOVDQU, VEX.66.0F F7): a faulting instruction leaves memory unchanged (faults are restartable: "the state ... prior to the
  -- execution of the faulting instruction", SDM vol. 3, 6.5; the model checks every selected element
  -- before writing any); TCG stores the selected elements one by one and faults in the middle. With
  -- the same #PF on both sides, only QEMU's data-area hash and the accessed/dirty bits its stores set
  -- are replaced.
  if i.vex && qo.vec == 14 && lo.vec == 14 && qo.cr2 == lo.cr2 && qo.err == lo.err &&
     ((i.map == 2 && i.pp == 1 && (i.byte == 0x2E || i.byte == 0x2F || i.byte == 0x8E)) ||
      (i.map == 1 && i.pp == 1 && i.byte == 0xF7)) then
    let ad (q l : UInt32) : UInt32 := if (q ^^^ l) &&& ~~~0x60 == 0 then l else q
    return { qo with hash := lo.hash, pte8 := ad qo.pte8 lo.pte8, pte9 := ad qo.pte9 lo.pte9 }
  -- (Avx) VCVTDQ2PD ymm1, xmm2/m128 and VCVTPS2PD ymm1, xmm2/m128 read 16 bytes (SDM vol. 2 and AMD
  -- APM vol. 4 instruction pages: "mem128"); TCG loads 32, so an operand ending right before a
  -- not-present page faults at that page's first byte. Only that #PF is replaced.
  if i.vex && i.vexL && i.isMem && i.map == 1 && ((i.pp == 2 && i.byte == 0xE6) || (i.pp == 0 && i.byte == 0x5A)) &&
     qo.vec == 14 && qo.cr2 &&& 0xFFF == 0 && lo.vec != 14 then return lo
  -- (Avx) VEX-encoded scalar instructions with F3/F2 (VSQRTSS .. VMAXSD, VCMPSS/SD,
  -- VCVTSS2SD/VCVTSD2SS) ignore VEX.L ("VEX.LIG", SDM vol. 2 instruction pages; AMD APM vol. 4
  -- encodings "X.src.X.10"); TCG raises #UD for VEX.L = 1 (its X86_VEX_REPScalar rule). Only that #UD
  -- is replaced; the model's outcome must not be #UD.
  if i.vex && i.vexL && i.map == 1 && i.pp ≥ 2 && qo.vec == 6 && lo.vec != 6 &&
     [0x51, 0x52, 0x53, 0x58, 0x59, 0x5A, 0x5C, 0x5D, 0x5E, 0x5F, 0xC2].contains i.byte then
    return lo
  -- (Avx2) TCG loads 16 bytes for the m32/m64 operand of the scalar FMA forms (VFMADD/VFMSUB/VFNMADD/
  -- VFNMSUB 132/213/231 SS/SD, VEX.66.0F38 99, 9B, 9D, 9F, A9, AB, AD, AF, B9, BB, BD, BF: "xmm3/m32",
  -- "xmm3/m64" in the SDM and AMD APM vol. 4) and 32 bytes for the m128 count of the VEX.256 shifts by
  -- an XMM count (VPSLLW/D/Q, VPSRLW/D/Q, VPSRAW/D ymm, ymm, xmm3/m128: VEX.66.0F D1..D3, E1, E2, F1..F3).
  -- An operand ending right before the next page therefore makes TCG fault at that page's first byte
  -- (that #PF is replaced by the model's outcome) or set that page's accessed bit (only the A bit of
  -- its PTE is replaced).
  let tcgWide := i.vex && i.isMem &&
    ((i.map == 2 && i.pp == 1 && i.byte &&& 0x0F ≥ 9 && i.byte &&& 1 == 1 && 0x99 ≤ i.byte && i.byte ≤ 0xBF) ||
     (i.vexL && i.map == 1 && i.pp == 1 && [0xD1, 0xD2, 0xD3, 0xE1, 0xE2, 0xF1, 0xF2, 0xF3].contains i.byte))
  if tcgWide && qo.vec == 14 && qo.cr2 &&& 0xFFF == 0 && lo.vec != 14 then return lo
  if tcgWide && qo.vec == lo.vec then
    let a (q l : UInt32) : UInt32 := if q ^^^ l == 0x20 then l else q
    if qo.vec != 14 then return { qo with pte8 := a qo.pte8 lo.pte8, pte9 := a qo.pte9 lo.pte9 }
  if qo.vec != 14 || lo.vec != 14 then return qo
  let mut q := qo
  if rmwDest i then
    if q.err &&& 2 == 0 && lo.err &&& 2 != 0 && lo.cr2 < q.cr2 && q.cr2 &&& 0xFFF == 0 && q.cr2 - lo.cr2 < 8 then
      q := { q with err := lo.err, cr2 := lo.cr2 }
    if q.err &&& 2 == 0 && lo.err == q.err ||| 2 then q := { q with err := lo.err }
    let readVsWrite (qp lp : UInt32) : Bool :=
      (qp &&& 0x20 != 0 && lp == qp &&& ~~~0x20) || lp == qp ||| 0x40 || lp == qp ||| 0x60
    if readVsWrite q.pte8 lo.pte8 then q := { q with pte8 := lo.pte8 }
    if readVsWrite q.pte9 lo.pte9 then q := { q with pte9 := lo.pte9 }
  if i.op == 0x60 then
    let esp := lo.regs[4]!
    let start := esp - 8 * i.opsz.toUInt32
    if q.cr2 == start && start ≤ lo.cr2 && lo.cr2 < esp then q := { q with cr2 := lo.cr2 }
    if q.hash == initHash then q := { q with hash := lo.hash, pte8 := lo.pte8, pte9 := lo.pte9 }
  return q

/-- The machine state of vector `o`, before its instruction. -/
def vectorMachine (v : ByteArray) (o : Nat) (nativeMemory : Bool := false) (v2 : Bool := false) :
    Except String Machine := do
  let len := u8At v o
  let rd32 (i : Nat) : UInt32 := (u32At v (o + i)).toUInt32
  let regs := (List.range 8).map fun r => rd32 (16 + 4 * r)
  let eflags := rd32 48
  let seed := rd32 52
  let sels := (List.range 4).map fun s => (u16At v (o + 56 + 2 * s)).toUInt16
  let poff := (List.range 2).map fun k => u16At v (o + 64 + 2 * k)
  let pval := (List.range 2).map fun k => rd32 (68 + 4 * k)
  let mode := rd32 76
  let pte8 := rd32 80
  let pte9 := rd32 84
  let mut m := baseMachine
  let mut mem := m.mem
  let mut s := seed
  for i in [0:2048] do
    s := xorshift s
    mem := wrBytes mem (DATA + (4 * i).toUInt32) 4 s
  for (po, pv) in poff.zip pval do
    if po != 0xFFFF then mem := wrBytes mem (DATA + po.toUInt32) 4 pv
  for i in [0:512] do mem := mem.set! (CODE.toNat + i) 0xCC
  for i in [0:len] do mem := mem.set! (CODE.toNat + 256 + i) (v.get! (o + 1 + i))
  let mut c := m.cpu
  for r in [0:8] do c := c.setReg r.toUInt8 regs[r]!
  c := { c with eflags, eip := CODE + 256, cr3 := 0x3000 }
  mem := wrBytes mem (0x4000 + 8 * 4) 4 (0x8000 ||| (pte8 &&& 0xFFF))
  mem := wrBytes mem (0x4000 + 9 * 4) 4 (0x9000 ||| (pte9 &&& 0xFFF))
  if nativeMemory then
    mem := wrBytes mem (0x4000 + 16 * 4) 4 (0x8000 ||| (pte8 &&& 0xFFF))
    mem := wrBytes mem (0x4000 + 17 * 4) 4 (0x9000 ||| (pte9 &&& 0xFFF))
  if mode &&& 1 != 0 then
    c := { c with cr0 := 0x80000031 ||| (if mode &&& 2 != 0 then 0x10000 else 0) }
  if v2 then
    let mxcsr := rd32 88
    let ymm := rd32 92 &&& 1 != 0
    let pat := vecPattern seed
    c := { c with cr4 := CR4.OSFXSR ||| CR4.OSXMMEXCPT ||| (if ymm then CR4.OSXSAVE else 0),
                  xcr0 := if ymm then 7 else 1,
                  sse := { mxcsr, xmm := (List.range 8).toArray.map (v128Of pat),
                           ymmh := if ymm then (List.range 8).toArray.map (fun k => v128Of pat (k + 8))
                                   else Array.replicate 8 {} } }
  m := { m with mem, cpu := c }
  -- data segment registers through the descriptor-load path
  for (si, sel) in [SegN.DS, SegN.ES, SegN.FS, SegN.GS].zip sels do
    match (loadSeg si sel) m with
    | .ok _ m' => m := m'
    | .error _ _ => throw s!"bad initial selector {sel}"
  return m

def runVector (v : ByteArray) (o : Nat) (nativeMemory : Bool := false) (v2 : Bool := false) :
    Except String (Outcome × Option Inst × UInt32) := do
  let mut m ← vectorMachine v o nativeMemory v2
  let start := m.cpu.eip
  let inst := match decode m with | .ok i _ => some i | .error _ _ => none
  let initHash := fnv m.mem
  let tf := m.cpu.eflags &&& Flag.TF != 0
  let mut res : Option Fault := none
  let mut trapped := false
  let mut steps := 0
  let mut go := true
  while go do
    match execInstr { m with cpu := { m.cpu with shadow := false } } with
    | .ok i m' => m := m'; if tf && !noStepTrap i then trapped := true
    | .error f m' => m := m'; res := some f
    steps := steps + 1
    -- a REP string instruction that stopped early is re-executed, as the CPU would
    go := res.isNone && !trapped && m.cpu.eip == start && steps < 1000 && (u8At v (o+1) ≠ 0xEB)
  let fc := m.cpu
  let (vec, err, cr2) := match res with
    | none => if trapped then (1, 0, 0) else (3, 0, 0)
    | some (.exc vv e a) => (vv.toUInt32, e.getD 0, if vv == Vec.PF then a else 0)
    | some (.shutdown _) => (0xFFFF, 0, 0)
    | some (.unsupported _) => (0xFFFE, 0, 0)
  let mut pageHashes : List UInt32 := []
  if nativeMemory then
    for page in [0:2] do
      let mut h : UInt64 := 14695981039346656037
      for k in [0:4096] do h := (h ^^^ (m.mem.get! (0x8000+page*4096+k)).toUInt64) * 1099511628211
      pageHashes := pageHashes ++ [h.toUInt32, (h >>> 32).toUInt32]
  return ({ vec, err, eip := fc.eip,
            regs := #[fc.eax, fc.ecx, fc.edx, fc.ebx, fc.esp, fc.ebp, fc.esi, fc.edi],
            eflags := fc.eflags, segs := #[fc.ds.sel.toUInt32, fc.es.sel.toUInt32, fc.fs.sel.toUInt32,
              fc.gs.sel.toUInt32, fc.ss.sel.toUInt32], hash := fnv m.mem, cr2,
            pte8 := rdBytes m.mem (0x4000 + 32) 4, pte9 := rdBytes m.mem (0x4000 + 36) 4, pageHashes,
            vecs := if !v2 then [] else
              let ymm := (u32At v (o + 92)).toUInt32 &&& 1 != 0
              [fc.mxcsr] ++ (fc.xmm.toList.map v128Words).flatten ++
              (if ymm then (fc.ymmh.toList.map v128Words).flatten else List.replicate 32 0) },
          inst, initHash)

def parseHex (s : String) : UInt32 :=
  s.foldl (fun a ch => a * 16 + (if ch.isDigit then ch.toNat - 48 else ch.toLower.toNat - 87).toUInt32) 0

/-- The TSO access log (`Machine.tso`, used by `X86.Tso`) is complete and inert, for one vector
with paging off: one `step` with the log on leaves memory equal to the logged stores replayed on the
initial memory, and agrees with the plain `step` (CPU state and memory) unless the instruction is
a REP string instruction (one iteration per step under the log). `none` if the vector is skipped. -/
def tsoLogCheck (v : ByteArray) (o : Nat) : Except String (Option String) := do
  let m ← vectorMachine v o
  if m.cpu.cr0 &&& CR0.PG != 0 then return none
  let m1 := step m
  let m2 := step { m with tso := some {} }
  let log := m2.tso.getD {}
  if (Tso.overlay m.mem log.writes).data != m2.mem.data then
    return some s!"memory differs from the replayed log ({log.writes.size} stores)"
  let rep := match decode m with
    | .ok i _ => i.rep != 0 && ((0xA4 ≤ i.op && i.op ≤ 0xAF) || (0x6C ≤ i.op && i.op ≤ 0x6F))
    | .error _ _ => false
  if !rep && (m1.mem.data != m2.mem.data || reprStr m1.cpu != reprStr m2.cpu || reprStr m1.fatal != reprStr m2.fatal) then
    return some "logged step differs from the plain step"
  return some ""

def main (args : List String) : IO UInt32 := do
  if let ["--tso-log", vf] := args then
    let v ← IO.FS.readBinFile vf
    let mut bad := 0
    let mut checked := 0
    for idx in [0:v.size / 88] do
      match tsoLogCheck v (idx * 88) with
      | .error e => IO.println s!"#{idx}: {e}"; bad := bad + 1
      | .ok none => pure ()
      | .ok (some "") => checked := checked + 1
      | .ok (some e) => IO.println s!"#{idx}: {e}"; bad := bad + 1; checked := checked + 1
    IO.println s!"{checked} vectors (paging off) checked, {bad} failures"
    return (if bad == 0 then 0 else 1)
  let nativeMemory := args.head? == some "--native-memory"
  let dumpArgs := if nativeMemory then ["--dump"] ++ args.drop 1 else args
  if let ["--dump", vf] := dumpArgs then
    let v ← IO.FS.readBinFile vf
    if v.size == 0 || v.size % 88 != 0 then IO.eprintln "invalid vector size"; return 2
    let hx := fun (x : UInt32) =>
      let s := String.ofList (Nat.toDigits 16 x.toNat)
      "".pushn '0' (8 - s.length) ++ s
    IO.println s!"BEGIN {hx (v.size / 88).toUInt32}"
    for idx in [0:v.size / 88] do
      match runVector v (idx * 88) nativeMemory with
      | .error e => IO.eprintln s!"vector {idx}: {e}"; return 1
      | .ok (o, _, _) =>
        if o.vec >= 0xFFFE then IO.eprintln s!"vector {idx}: unsupported model outcome"; return 1
        let fields := [idx.toUInt32, o.vec, o.err, o.eip] ++ o.regs.toList ++
          [o.eflags] ++ o.segs.toList ++ [o.hash, o.cr2, o.pte8, o.pte9] ++ o.pageHashes
        IO.println (String.intercalate " " (fields.map hx))
    IO.println "END"
    return 0
  let [vf, mf, qf] := args | do IO.eprintln "usage: x86test vectors.bin vectors.metaLines qemu.out"; return 2
  let v ← IO.FS.readBinFile vf
  let (hdr, rsz) := vecFormat v
  -- a corrupt or stale header must not turn into "0 vectors compared, 0 mismatches"
  if rsz == 0 then IO.eprintln "invalid vector file: record size 0"; return 2
  let v2 := hdr != 0
  let metaLines := (← IO.FS.lines mf)
  let qlines := (← IO.FS.lines qf).filter fun l => l.length > 150 && (l.get 0).isAlphanum
  let n := (v.size - hdr) / rsz
  let mut bad := 0
  let mut tcg := 0
  let mut lenRule := 0
  let mut checked := 0
  let mut q := 0
  for l in qlines do
    let f := (l.splitOn " ").filter (· ≠ "") |>.map parseHex |>.toArray
    if f.size < (if v2 then 87 else 22) then continue
    let idx := f[0]!.toNat
    if idx ≥ n then continue
    let fm := parseHex ((metaLines[idx]!.splitOn " ")[0]!)
    let desc := (metaLines[idx]!.splitOn " ")[1]!
    let qo : Outcome := { vec := f[1]!, err := f[2]!, eip := f[3]!, regs := f.extract 4 12,
                          eflags := f[12]!, segs := f.extract 13 18, hash := f[18]!,
                          cr2 := f[19]!, pte8 := f[20]!, pte9 := f[21]!,
                          vecs := if v2 then (f.extract 22 87).toList else [] }
    -- 16-byte encodings without an instruction (`len16-` vectors of test/gen.py): TCG raises #UD
    -- for such an opcode before fetching its remaining ModRM/immediate bytes, so it never reaches
    -- the 15-byte limit. The model decodes the whole instruction and raises #GP(0), as the SDM's
    -- exception priorities list the length limit with the decode faults (vol. 3, table 6-2);
    -- QEMU's #UD is rewritten to #GP(0) (counted separately; all other fields still compared).
    let len16 := desc.startsWith "len16-" && qo.vec == 6
    let qo := if len16 then { qo with vec := 13 } else qo
    if len16 then lenRule := lenRule + 1
    match runVector v (hdr + idx * rsz) (v2 := v2) with
    | .error e => IO.println s!"#{idx} {desc}: {e}"; bad := bad + 1
    | .ok (lo, inst, initHash) =>
      -- the instruction completed (INT3 terminator or single-step trap): undefined flags masked
      let mask := if qo.vec == 3 || qo.vec == 1 then fm else 0xFFFEFFFF
      -- CMPS reads two memory operands in an unspecified order: CR2 is not compared
      let cmps := desc.endsWith "a6" || desc.endsWith "a7"
      let flt := qo.vec != 3 && qo.vec != 1
      let norm := fun (x : Outcome) => { x with eflags := x.eflags &&& mask,
                                                cr2 := if cmps then 0 else x.cr2,
                                                err := if cmps && x.vec == 14 then 0 else x.err,
                                                pte8 := if cmps && flt then x.pte8 &&& ~~~0x20 else x.pte8,
                                                pte9 := if cmps && flt then x.pte9 &&& ~~~0x20 else x.pte9 }
      checked := checked + 1
      let qh := match inst with | some i => qemuAsHardware i qo lo initHash | none => qo
      if norm lo != norm qo && norm lo == norm qh then
        tcg := tcg + 1
      else if norm lo != norm qo then
        bad := bad + 1
        IO.println s!"MISMATCH #{idx} insn {desc} (flag mask {(Nat.toDigits 16 mask.toNat).asString})"
        IO.println s!"  qemu: {repr (norm qo)}"
        IO.println s!"  lean: {repr (norm lo)}"
    q := q + 1
  let lenNote := if lenRule == 0 then "" else s!", {lenRule} 16-byte #UD encodings checked as #GP(0)"
  IO.println s!"{checked} vectors compared, {bad} mismatches ({tcg} known QEMU deviations accepted{lenNote})"
  -- every vector must have been compared: QEMU rows that are short (a harness with another record
  -- format), missing or out of range would otherwise be skipped silently
  if checked != n then
    IO.println s!"FAIL: only {checked} of {n} vectors compared (missing, short or out-of-range QEMU rows)"
    return 1
  return (if bad == 0 then 0 else 1)
