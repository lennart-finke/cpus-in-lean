import X86.Tso
import X86.Boot
import Std.Data.HashSet
/-!
# `x86litmus`: all final states of a litmus test on the x86-TSO multiprocessor (`X86.Tso`)

Input (a file, produced by `litmus/litmus.py` from a herd `.litmus` test):

    thread <k> <hex code bytes>           code of thread k (ends in HLT)
    mem <addr> <value>                    initial 32-bit memory word
    reg <k> <regnum> <value>              initial register of thread k
    obsreg <k> <name> <regnum>            observed register (printed as `k:name=v`)
    obsmem <name> <addr>                  observed memory word (printed as `name=v`)

Every interleaving of instruction steps and store-buffer commits is explored (depth first, states
deduplicated). A final state has every CPU halted and every buffer empty; its observed values are
printed in herd's `States` format. A CPU stopped by the model (`Fault.unsupported`) or a fault is
printed as `STOP <thread> <reason>`.
-/
open X86

namespace Litmus

def memSize : Nat := 0x4000
def codeBase (k : Nat) : UInt32 := 0x1000 + 0x200 * k.toUInt32
def stackTop (k : Nat) : UInt32 := 0x3F00 - 0x100 * k.toUInt32
/-- Data lives in 0x2000..0x2FFF. -/
def dataLo : Nat := 0x2000
def dataHi : Nat := 0x3000

structure Test where
  threads : Array ByteArray := #[]
  mem : List (UInt32 × UInt32) := []
  regs : List (Nat × UInt8 × UInt32) := []
  obsRegs : List (Nat × String × UInt8) := []
  obsMems : List (String × UInt32) := []

def parseNum (s : String) : Option Nat :=
  if s.startsWith "0x" then
    (s.drop 2).foldl (fun acc c => acc.bind fun a =>
      if c.isDigit then some (16 * a + (c.toNat - '0'.toNat))
      else if 'a' ≤ c && c ≤ 'f' then some (16 * a + (c.toNat - 'a'.toNat + 10))
      else if 'A' ≤ c && c ≤ 'F' then some (16 * a + (c.toNat - 'A'.toNat + 10))
      else none) (some 0)
  else if s.startsWith "-" then (s.drop 1).toNat?.map fun n => (2 ^ 32 - n) % 2 ^ 32
  else s.toNat?

def parseHex (s : String) : Option ByteArray := do
  let cs := s.toList
  if cs.length % 2 != 0 then none
  let mut out := ByteArray.empty
  for i in [0:cs.length / 2] do
    out := out.push (← parseNum s!"0x{cs[2*i]!}{cs[2*i+1]!}").toUInt8
  return out

def parse (src : String) : Except String Test := do
  let mut t : Test := {}
  for line in src.splitOn "\n" do
    let ws := (line.splitOn " ").filter (· ≠ "")
    let num (s : String) : Except String Nat := match parseNum s with
      | some n => pure n | none => throw s!"bad number {s} in: {line}"
    match ws with
    | [] => pure ()
    | ["thread", k, hex] =>
      let k ← num k
      let some b := parseHex hex | throw s!"bad hex in: {line}"
      if k != t.threads.size then throw "threads out of order"
      t := { t with threads := t.threads.push b }
    | ["mem", a, v] => t := { t with mem := t.mem ++ [((← num a).toUInt32, (← num v).toUInt32)] }
    | ["reg", k, r, v] => t := { t with regs := t.regs ++ [(← num k, (← num r).toUInt8, (← num v).toUInt32)] }
    | ["obsreg", k, name, r] => t := { t with obsRegs := t.obsRegs ++ [(← num k, name, (← num r).toUInt8)] }
    | ["obsmem", name, a] => t := { t with obsMems := t.obsMems ++ [(name, (← num a).toUInt32)] }
    | _ => throw s!"bad line: {line}"
  return t

/-- Flat protected mode (the contract's call machine), paging off, at the thread's code. -/
def cpuFor (t : Test) (k : Nat) : Machine := Id.run do
  let cs := flatSeg 0x08 0xC09B
  let ds := flatSeg 0x10 0xC093
  let mut c : Cpu := { eip := codeBase k, esp := stackTop k, cs, ds, es := ds, ss := ds, fs := ds, gs := ds,
                       cr0 := CR0.PE ||| CR0.ET, eflags := 2 }
  for (j, r, v) in t.regs do
    if j == k then c := c.setReg r v
  return { mem := .empty, cpu := c }

def initial (t : Test) : TMachine := Id.run do
  let mut mem := zeroMem memSize
  for k in [0:t.threads.size] do
    mem := t.threads[k]!.copySlice 0 mem (codeBase k).toNat t.threads[k]!.size
  for (a, v) in t.mem do
    mem := wrBytes mem a 4 v
  return TMachine.init mem ((List.range t.threads.size).map (cpuFor t))

/-- Everything that can influence the future of a state (code is never written). -/
def key (s : TMachine) : String := Id.run do
  let mut out := ""
  for c in s.cores do
    let p := c.m.cpu
    out := out ++ s!"{p.eip},{p.eax},{p.ecx},{p.edx},{p.ebx},{p.esp},{p.ebp},{p.esi},{p.edi},{p.eflags},{p.halted},{c.m.fatal.isSome}|"
    for st in c.sb do out := out ++ s!"{st.addr}:{st.n}:{st.val};"
    out := out ++ "#"
  for i in [dataLo:dataHi] do
    let b := s.mem.get! i
    if b != 0 then out := out ++ s!"{i}={b};"
  return out

/-- Successors used by the explorer: halted CPUs are not stepped (their steps only advance the
instruction count). -/
def next (s : TMachine) : List TMachine :=
  let n := s.cores.size
  (List.range n).filterMap (fun k => if s.cores[k]!.m.cpu.halted then none else s.exec k) ++
  (List.range n).filterMap s.flush

def outcome (t : Test) (s : TMachine) : String := Id.run do
  for k in [0:s.cores.size] do
    if let some f := s.cores[k]!.m.fatal then
      return s!"STOP {k} {repr f}"
  let regs := t.obsRegs.map fun (k, name, r) => s!"{k}:{name}={s.cores[k]!.m.cpu.getReg r};"
  let mems := t.obsMems.map fun (name, a) => s!"{name}={rdBytes s.mem a 4};"
  return " ".intercalate (regs ++ mems)

partial def explore (t : Test) (s : TMachine) (seen : Std.HashSet String) (outs : Std.HashSet String)
    (budget : Nat) : Std.HashSet String × Std.HashSet String × Nat :=
  if budget == 0 then (seen, outs, 0) else
  let k := key s
  if seen.contains k then (seen, outs, budget) else
  let seen := seen.insert k
  let succ := next s
  let stopped := s.cores.any (·.m.fatal.isSome)
  if succ.isEmpty || stopped then (seen, outs.insert (outcome t s), budget - 1) else
  succ.foldl (fun (seen, outs, b) s' => explore t s' seen outs b) (seen, outs, budget - 1)

end Litmus

/-- `--trace`: run CPU 0 alone (exec, else flush) and print every state. -/
def trace (t : Litmus.Test) : IO Unit := do
  let mut s := Litmus.initial t
  IO.println s!"code {t.threads[0]!.toList} mem {(List.range 16).map fun i => s.mem.get! (0x1000 + i)}"
  for _ in [0:40] do
    let c := s.cores[0]!
    IO.println s!"eip={c.m.cpu.eip} eax={c.m.cpu.eax} halted={c.m.cpu.halted} fatal={repr c.m.fatal} sb={c.sb.size}"
    match (if c.m.cpu.halted then none else s.exec 0) <|> s.flush 0 with
    | some s' => s := s'
    | none => IO.println "final"; return

def main (args : List String) : IO UInt32 := do
  let (tr, args) := if args.head? == some "--trace" then (true, args.tail) else (false, args)
  let [file] := args | IO.eprintln "usage: x86litmus [--trace] TEST.lit"; return 2
  match Litmus.parse (← IO.FS.readFile file) with
  | .error e => IO.eprintln e; return 2
  | .ok t =>
    if tr then trace t; return 0
    let (seen, outs, budget) := Litmus.explore t (Litmus.initial t) {} {} 5000000
    if budget == 0 then IO.eprintln "state budget exhausted"; return 1
    let outs := outs.toList.toArray.qsort (· < ·)
    IO.println s!"States {outs.size}"
    for o in outs do IO.println o
    IO.eprintln s!"explored {seen.size} states"
    return 0
