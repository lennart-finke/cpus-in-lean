import X64.Exec
namespace X64

def maxU64 : UInt64 := 0xFFFFFFFFFFFFFFFF

def lockOk (i : Inst) : Bool :=
  i.isMem &&
  ((i.op < 0x40 && i.op &&& 7 < 2 && i.op &&& 0x38 != 0x38) ||
   ((i.op == 0x80 || i.op == 0x81 || i.op == 0x83) && i.group != 7) ||
   i.op == 0x86 || i.op == 0x87 ||
   ((i.op == 0xF6 || i.op == 0xF7) && (i.group == 2 || i.group == 3)) ||
   ((i.op == 0xFE || i.op == 0xFF) && i.group < 2) ||
   i.op == 0x1AB || i.op == 0x1B3 || i.op == 0x1BB ||
   (i.op == 0x1BA && i.group ≥ 5) || (i.op == 0x1C7 && i.group == 1) ||
   i.op == 0x1B0 || i.op == 0x1B1 || i.op == 0x1C0 || i.op == 0x1C1)

/-- Decode/execute without exception delivery. Useful for instruction differential tests;
CPU registers roll back on faults, while page-table A/D effects are retained. -/
def instruction (m : Machine) : EStateM.Result Fault Machine Inst :=
  let result := (do
    if !((← cpu).long) then unsupported "execution outside 64-bit mode"
    let i ← decode
    if i.lock && !lockOk i then ud
    modCpu fun c => { c with rip := c.rip + i.len, shadow := false }
    exec i
    pure i) m
  match result with
  | .ok i m' => .ok i { m' with icount := m.icount + 1 }
  | .error f m' =>
    -- SIMD exceptions set sticky status even though destinations roll back.
    let c := match f with
      | .exc 19 _ _ => { m.cpu with mxcsr := m'.cpu.mxcsr }
      | .exc 1 _ _ => { m.cpu with dr6 := m'.cpu.dr6, dr7 := m'.cpu.dr7 }
      | _ => m.cpu
    .error f { m' with cpu := c, icount := m.icount + 1 }

def raiseExc (m : Machine) (vec : UInt8) (err : Option UInt64) (ext : Bool) : Machine :=
  match deliver vec err false ext m with
  | .ok _ m' => m'
  | .error f m' =>
    match f with
    | .unsupported _ => { m' with fatal := some f }
    | _ =>
      if vec == Vec.DF then { m' with fatal := some (.shutdown "triple fault") }
      else match deliver Vec.DF (some 0) false false { m' with cpu := m.cpu } with
        | .ok _ m'' => m''
        | .error f m'' => { m'' with fatal := some (.shutdown s!"double-fault delivery failed: {repr f}") }

def handleFault (m : Machine) (f : Fault) : Machine :=
  match f with
  | .exc vec err addr =>
    let m := if vec == Vec.PF then { m with cpu := { m.cpu with cr2 := addr } } else m
    raiseExc m vec err false
  | _ => { m with fatal := some f }

def step (m : Machine) : Machine :=
  let m := if m.icount ≥ m.timerAt then m.timerFire else m
  if m.intr && m.cpu.flag Flag.IF && !m.cpu.shadow then
    let (v, m) := m.intAck
    raiseExc { m with cpu := { m.cpu with halted := false } } v none true
  else if m.cpu.halted then
    { m with icount := if m.timerAt == maxU64 then m.icount else max (m.icount + 1) m.timerAt }
  else
    match instruction m with
    | .error f m' => handleFault m' f
    | .ok i m' =>
      if m.cpu.flag Flag.TF && i.op != 0xCC && i.op != 0xCD && i.op != 0xCF &&
         !(i.op == 0x8E && i.group == SegN.SS) then
        raiseExc { m' with cpu := { m'.cpu with dr6 := m'.cpu.dr6 ||| 0x4000 } } Vec.DB none false
      else m'

def Machine.idle (m : Machine) : Bool :=
  m.cpu.halted && m.timerAt == maxU64 && !(m.intr && m.cpu.flag Flag.IF)

partial def Machine.runUntil (m : Machine) (limit : UInt64) : Machine :=
  if m.icount ≥ limit || m.fatal.isSome || m.idle then m else (step m).runUntil limit

end X64
