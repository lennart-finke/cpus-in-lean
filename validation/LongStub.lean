import X86
/-!
# The 64-bit stubs of the long-mode system test (`test/sys/t_long.c`)

Test infrastructure, not part of the model. The IA-32 model stops before the first instruction of
64-bit code (`Fault.unsupported "64-bit mode"`, see `X86/Ext/LongModeBase.lean`). The long-mode
system test sends every transfer into 64-bit code to tiny stubs whose exact bytes `t_long.c`
assembles (`build_stubs`):

    entry:  [6A 00]           push 0               (vectors without an error code, and far targets)
            68 imm32          push entry number
            E9 rel32          jmp common
    common: 48 89 04 25 d32   mov [d32], rax
            48 89 1C 25 d32   mov [d32], rbx
            48 89 0C 25 d32   mov [d32], rcx
            4C 89 1C 25 d32   mov [d32], r11
            48 89 E6          mov rsi, rsp
            BF d32            mov edi, rec
            B9 n32            mov ecx, n
            F3 48 A5          rep movsq
            6A ss / 68 rsp32 / 6A fl / 6A cs / 68 rip32 / 48 CF     push ...; iretq

When `x86sys` stops at such an entry, `resume` performs exactly what these instructions do (the
pushes, the stores, the copy, and IRETQ to the compatibility-mode or legacy code segment it names,
with its descriptor checks reduced to loading the caches, or the #GP of an IRETQ to a more privileged
level, which the model then delivers) and lets the model continue. Anything else
at RIP is left as the fatal stop. QEMU executes the same bytes, so both transcripts continue
identically.
-/
namespace X86.LongStub

open X86

/-- The model's M actions used by the stub emulation. -/
def rd8 (lin : UInt64) : M UInt32 := linRd lin.toUInt32 1 false
def rd32 (lin : UInt64) : M UInt32 := linRd lin.toUInt32 4 false
def rd64 (lin : UInt64) : M UInt64 := do
  let lo ← rd32 lin
  let hi ← rd32 (lin + 4)
  return (hi.toUInt64 <<< 32) ||| lo.toUInt64

@[inline] def sx32 (v : UInt32) : UInt64 :=
  if v &&& 0x80000000 != 0 then v.toUInt64 ||| 0xFFFFFFFF00000000 else v.toUInt64

/-- Parse and run the stub at RIP; `none` if RIP does not hold one. -/
def run : M Bool := do
  let c ← cpu
  let rip := LongMode.rip c
  let mut p := rip
  let mut n0 := false
  if (← rd8 p) == 0x6A then
    if (← rd8 (p + 1)) != 0 then return false
    n0 := true
    p := p + 2
  if (← rd8 p) != 0x68 then return false
  let vec := sx32 (← rd32 (p + 1))
  if (← rd8 (p + 5)) != 0xE9 then return false
  let common := p + 10 + sx32 (← rd32 (p + 6))
  -- the common part
  let expect (off : UInt64) (bs : List UInt32) : M Bool := do
    let mut ok := true
    let mut k : UInt64 := 0
    for x in bs do
      if (← rd8 (common + off + k)) != x then ok := false
      k := k + 1
    return ok
  let okAll :=
    (← expect 0 [0x48, 0x89, 0x04, 0x25]) && (← expect 8 [0x48, 0x89, 0x1C, 0x25]) &&
    (← expect 16 [0x48, 0x89, 0x0C, 0x25]) && (← expect 24 [0x4C, 0x89, 0x1C, 0x25]) &&
    (← expect 32 [0x48, 0x89, 0xE6, 0xBF]) && (← expect 40 [0xB9]) && (← expect 45 [0xF3, 0x48, 0xA5, 0x6A]) &&
    (← expect 50 [0x68]) && (← expect 55 [0x6A]) && (← expect 57 [0x6A]) && (← expect 59 [0x68]) &&
    (← expect 64 [0x48, 0xCF])
  if !okAll then return false
  let aRax := sx32 (← rd32 (common + 4))
  let aRbx := sx32 (← rd32 (common + 12))
  let aRcx := sx32 (← rd32 (common + 20))
  let aR11 := sx32 (← rd32 (common + 28))
  let recA := (← rd32 (common + 36)).toUInt64
  let n := (← rd32 (common + 41)).toUInt64
  let sx8 := fun (b : UInt32) => if b &&& 0x80 != 0 then b.toUInt64 ||| 0xFFFFFFFFFFFFFF00 else b.toUInt64
  let ssSel := sx8 (← rd8 (common + 49))
  let rspImm := sx32 (← rd32 (common + 51))
  let flImm := sx8 (← rd8 (common + 56))
  let csSel := sx8 (← rd8 (common + 58))
  let ripImm := sx32 (← rd32 (common + 60))
  let user := c.cpl == 3
  -- push 0 (if present), push the entry number
  let mut sp := LongMode.rsp c
  if n0 then sp ← LongMode.push64 sp 0 user
  sp ← LongMode.push64 sp vec user
  -- the register stores
  LongMode.wr64 aRax c.eax.toUInt64 user
  LongMode.wr64 aRbx c.ebx.toUInt64 user
  LongMode.wr64 aRcx c.ecx.toUInt64 user
  LongMode.wr64 aR11 c.lmx.r11 user
  -- rep movsq
  for k in [0:n.toNat] do
    let v ← rd64 (sp + 8 * k.toUInt64)
    LongMode.wr64 (recA + 8 * k.toUInt64) v user
  -- the IRETQ frame
  let top := sp
  sp ← LongMode.push64 sp ssSel user
  sp ← LongMode.push64 sp rspImm user
  sp ← LongMode.push64 sp flImm user
  sp ← LongMode.push64 sp csSel user
  let _ ← LongMode.push64 sp ripImm user
  -- IRETQ to a more privileged level (a stub entered at CPL 1..3 returning to ring-0 code): #GP(CS
  -- selector) at the IRETQ (APM vol. 3 IRET: the return CPL must not be below CPL), delivered by the model
  if csSel.toUInt32 &&& 3 < c.cpl then
    let at_ := common + 64
    let bot := sp - 8
    let si := (top + 8 * n).toUInt32
    let di := (recA + 8 * n).toUInt32
    modCpu fun c =>
      { c with eip := at_.toUInt32, esp := bot.toUInt32, esi := si, edi := di, ecx := 0,
               lmx := { c.lmx with ripHi := (at_ >>> 32).toUInt32, rspHi := (bot >>> 32).toUInt32 } }
    modM fun m => handleFault { m with icount := m.icount + (if n0 then 15 else 14) }
      (.exc Vec.GP (some (csSel.toUInt32 &&& 0xFFFC)) 0)
    return true
  -- IRETQ to compatibility (or legacy) mode at the same privilege level: CS and SS descriptors
  let (clo, chi, caddr) ← LongMode.readSel csSel.toUInt16 0
  let chi ← LongMode.setA chi caddr
  let (slo, shi, saddr) ← LongMode.readSel ssSel.toUInt16 0
  let shi ← LongMode.setA shi saddr
  modCpu fun c => { c with
    cs := LongMode.toSeg csSel.toUInt16 clo chi, ss := LongMode.toSeg ssSel.toUInt16 slo shi,
    eip := ripImm.toUInt32, esp := rspImm.toUInt32, eflags := (flImm.toUInt32 &&& Flag.valid) ||| 2,
    esi := (top + 8 * n).toUInt32, edi := (recA + 8 * n).toUInt32, ecx := 0,
    lmx := { c.lmx with ripHi := 0, rspHi := 0 } }
  modM fun m => { m with icount := m.icount + (if n0 then 16 else 15) }
  return true

/-- At a stop in 64-bit mode: run the stub at RIP and clear the stop; `none` if there is none. -/
def resume (m : Machine) : Option Machine :=
  match m.fatal with
  | some (.unsupported "64-bit mode") =>
    match run { m with fatal := none } with
    | .ok true m' => some m'
    | _ => none
  | _ => none

end X86.LongStub
