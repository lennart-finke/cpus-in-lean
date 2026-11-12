import X86
/-!
# x86run — host driver

Boots a Linux bzImage on the Lean x86 model. COM1 is connected to the terminal
(raw mode when stdin is a TTY; exit with Ctrl-A x). The host loop is outside the formal
model: it only moves bytes between the terminal and the UART model, and paces idle time.

    x86run [--mem MB] [--max N] [--smp N] [--quantum Q] [--expect PAT --send TEXT]...
           [--trace-from N --trace-count K] bzImage [initrd] [cmdline]
    x86run --cpuid [--smp N]

`--cpuid` prints what CPUID reports to CPU 0 of N CPUs (default 1) with CR4.OSXSAVE = 1 and XCR0 = 7
(the state the 7742 dump was taken in): every leaf and subleaf in range and the first leaf beyond, as
`cpuid LEAF SUB EAX EBX ECX EDX`, and every feature bit of `X86.Cpuid` as
`feature NAME LEAF SUB REG MASK implemented|masked` (read by `test/cpuid_table.py`).

`--smp N` boots N logical CPUs (`X86.MpMachine`, MP tables for the kernel); without it the machine
is the single-CPU one exactly as before.

`--expect PAT --send TEXT` pairs are processed in order: when the console output contains PAT,
TEXT is typed (`\n` is a newline); TEXT `@exit` ends the run.
-/
open X86

structure Opts where
  memMB : Nat := 128
  maxInstr : UInt64 := 0xFFFFFFFFFFFFFFFF
  script : List (String × String) := []
  traceFrom : UInt64 := 0xFFFFFFFFFFFFFFFF
  traceCount : Nat := 0
  quiet : Bool := false
  smp : Nat := 0
  quantum : Nat := 1000
  cpuid : Bool := false
  files : List String := []

partial def parseArgs (o : Opts) : List String → Except String Opts
  | "--mem" :: n :: r => parseArgs { o with memMB := n.toNat! } r
  | "--max" :: n :: r => parseArgs { o with maxInstr := n.toNat!.toUInt64 } r
  | "--expect" :: p :: "--send" :: t :: r =>
    parseArgs { o with script := o.script ++ [(p, t.replace "\\n" "\n")] } r
  | "--trace-from" :: n :: r => parseArgs { o with traceFrom := n.toNat!.toUInt64 } r
  | "--trace-count" :: n :: r => parseArgs { o with traceCount := n.toNat! } r
  | "--quiet" :: r => parseArgs { o with quiet := true } r
  | "--smp" :: n :: r => parseArgs { o with smp := n.toNat! } r
  | "--quantum" :: n :: r => parseArgs { o with quantum := n.toNat! } r
  | "--cpuid" :: r => parseArgs { o with cpuid := true } r
  | f :: r => if f.startsWith "--" then .error s!"unknown option {f}" else parseArgs { o with files := o.files ++ [f] } r
  | [] => .ok o

def hex (v : UInt32) : String :=
  let s := (Nat.toDigits 16 v.toNat).asString
  "".pushn '0' (8 - s.length) ++ s

def dumpCpu (c : Cpu) : String :=
  s!"EAX={hex c.eax} EBX={hex c.ebx} ECX={hex c.ecx} EDX={hex c.edx} ESI={hex c.esi} EDI={hex c.edi} EBP={hex c.ebp} ESP={hex c.esp}\n" ++
  s!"EIP={hex c.eip} EFL={hex c.eflags} CS={hex c.cs.sel.toUInt32} SS={hex c.ss.sel.toUInt32} DS={hex c.ds.sel.toUInt32} CR0={hex c.cr0} CR2={hex c.cr2} CR3={hex c.cr3} CR4={hex c.cr4} CPL={c.cpl}\n" ++
  s!"GDT={hex c.gdtBase}/{hex c.gdtLimit} IDT={hex c.idtBase}/{hex c.idtLimit} TR={hex c.tr.sel.toUInt32} CS.base={hex c.cs.base} CS.lim={hex c.cs.limit} CS.attr={hex c.cs.attr}"

/-- Step with a per-instruction trace to stderr. -/
partial def traceRun (s : MpMachine) (n : Nat) (err : IO.FS.Stream) : IO MpMachine := do
  let m := s.m
  if n == 0 || m.fatal.isSome then return s
  let c := m.cpu
  err.putStrLn s!"{m.icount} cpu{m.cur} {hex c.eip} eax={hex c.eax} ebx={hex c.ebx} ecx={hex c.ecx} edx={hex c.edx} esi={hex c.esi} edi={hex c.edi} ebp={hex c.ebp} esp={hex c.esp} fl={hex c.eflags}"
  traceRun s.step (n - 1) err

/-- `--cpuid`: the CPUID table and the feature list (see the module documentation). -/
def cpuidDump (n : Nat) : IO Unit := do
  let c : Cpu := { cr4 := CR4.OSXSAVE, xcr0 := 7, smpx := { ncpu := n.toUInt32, apicId := 0 } }
  let subs (l : UInt32) : List UInt32 :=
    if l == 7 || l == 0xB || l == 0xD || l == 0xF || l == 0x10 || l == 0x8000001D then
      (List.range 10).map (·.toUInt32) else [0]
  let (mb, me) := ((cpuid c 0 0).1, (cpuid c 0x80000000 0).1)
  let leaves := (List.range (mb.toNat + 2)).map (·.toUInt32) ++
    (List.range (me.toNat - 0x80000000 + 2)).map (fun i => (0x80000000 + i).toUInt32)
  for l in leaves do
    for sub in subs l do
      let r := cpuid c l sub
      IO.println s!"cpuid {hex l} {hex sub} {hex r.1} {hex r.2.1} {hex r.2.2.1} {hex r.2.2.2}"
  for f in Feature.all do
    let (l, sub, k, mask) := f.loc
    let name := (reprStr f).replace "X86.Feature." ""
    IO.println s!"feature {name} {hex l} {hex sub} {k} {hex mask} {if implemented f then "implemented" else "masked"}"

def main (args : List String) : IO UInt32 := do
  let o ← match parseArgs {} args with
    | .ok o => pure o
    | .error e => do IO.eprintln e; return 2
  if o.cpuid then
    if o.smp > maxCpus then IO.eprintln s!"--smp: at most {maxCpus} CPUs"; return 2
    cpuidDump (max 1 o.smp); return 0
  let some (kpath : String) := o.files[0]? | do IO.eprintln "usage: x86run [options] bzImage [initrd] [cmdline]"; return 2
  let kernel ← IO.FS.readBinFile kpath
  let initrd ← match o.files[1]? with
    | some (p : String) => IO.FS.readBinFile p
    | none => pure ByteArray.empty
  let cmdline := o.files[2]?.getD "console=ttyS0 earlyprintk=serial,ttyS0"
  if o.smp > maxCpus then IO.eprintln s!"--smp: at most {maxCpus} CPUs"; return 2
  let m0 ← match loadLinux (o.memMB * 1024 * 1024) kernel initrd cmdline o.smp with
    | .ok m => pure m
    | .error e => do IO.eprintln s!"boot: {e}"; return 1
  let mut s := MpMachine.ofMachine m0 (max 1 o.smp) o.quantum
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  let interactive := o.script.isEmpty && (← stdin.isTty)
  if interactive then
    let _ ← IO.Process.output { cmd := "sh", args := #["-c", "stty raw -echo < /dev/tty"] }
  let input ← IO.mkRef ByteArray.empty
  if interactive then
    let _ ← IO.asTask (prio := .dedicated) do
      repeat
        let b ← stdin.read 1
        if b.isEmpty then break
        input.modify (· ++ b)
  let t0 ← IO.monoNanosNow
  let mut script := o.script
  let mut outBuf : String := ""
  let mut ctrlA := false
  let mut quit := false
  let chunk : UInt64 := 2000000
  while !quit do
    if s.m.icount + chunk > o.traceFrom && o.traceCount > 0 && s.m.icount < o.traceFrom + o.traceCount.toUInt64 then
      if s.m.icount < o.traceFrom then s := s.runUntil o.traceFrom
      s ← traceRun s o.traceCount stderr
    else
      s := s.runUntil (min o.maxInstr (s.m.icount + chunk))
    -- console output
    let tx := s.m.uart.tx
    if tx.size > 0 then
      stdout.write tx
      stdout.flush
      s := { s with m := { s.m with uart := { s.m.uart with tx := .empty } } }
      if !script.isEmpty then
        outBuf := outBuf ++ String.fromUTF8! (ByteArray.mk (tx.data.filter (· < 128)))
    -- scripted input
    match script with
    | (pat, txt) :: rest =>
      if (outBuf.splitOn pat).length > 1 then
        if txt == "@exit" then quit := true
        else s := { s with m := { s.m with uart := s.m.uart.pushRx txt.toUTF8 }.syncUart }
        script := rest
        outBuf := ""
    | [] => pure ()
    -- terminal input
    if interactive then
      let inp ← input.modifyGet fun a => (a, ByteArray.empty)
      let mut fwd := ByteArray.empty
      for b in inp.data do
        if ctrlA then
          ctrlA := false
          if b == 'x'.toNat.toUInt8 then quit := true
          else fwd := fwd.push b
        else if b == 1 then ctrlA := true
        else fwd := fwd.push b
      if fwd.size > 0 then s := { s with m := { s.m with uart := s.m.uart.pushRx fwd }.syncUart }
    if let some f := s.m.fatal then
      stderr.putStrLn s!"\n[x86run] stopped: {repr f}\n{dumpCpu s.m.cpu}"
      quit := true
    if s.m.icount ≥ o.maxInstr then
      if !o.quiet then stderr.putStrLn s!"\n[x86run] instruction limit reached"
      quit := true
    if s.idle then
      if !interactive && script.isEmpty then
        stderr.putStrLn s!"\n[x86run] machine idle with no pending events\n{dumpCpu s.m.cpu}"
        quit := true
      else IO.sleep 10
    else if interactive && s.m.cpu.halted then IO.sleep 5
  if interactive then
    let _ ← IO.Process.output { cmd := "sh", args := #["-c", "stty sane < /dev/tty"] }
  let t1 ← IO.monoNanosNow
  let secs := (t1 - t0).toFloat / 1e9
  if !o.quiet then
    stderr.putStrLn s!"[x86run] {s.m.icount} instructions in {secs} s ({s.m.icount.toNat.toFloat / secs / 1e6} MIPS)"
    if o.smp > 1 then stderr.putStrLn s!"[x86run] per CPU: {s.retiredNow.toList}"
  return (if s.m.fatal.isSome then 1 else 0)
