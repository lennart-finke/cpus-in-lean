import X64
/-!
# x64run — host driver

Boots a Linux bzImage on the Lean x86 model. COM1 is connected to the terminal
(raw mode when stdin is a TTY; exit with Ctrl-A x). The host loop is outside the formal
model: it only moves bytes between the terminal and the UART model, and paces idle time.

    x64run [--mem MB] [--max N] [--expect PAT --send TEXT]... [--trace-from N --trace-count K]
           bzImage [initrd] [cmdline]

`--expect PAT --send TEXT` pairs are processed in order: when the console output contains PAT,
TEXT is typed (`\n` is a newline); TEXT `@exit` ends the run.
-/
open X64

structure Opts where
  memMB : Nat := 128
  maxInstr : UInt64 := 0xFFFFFFFFFFFFFFFF
  script : List (String × String) := []
  traceFrom : UInt64 := 0xFFFFFFFFFFFFFFFF
  traceCount : Nat := 0
  quiet : Bool := false
  files : List String := []

partial def parseArgs (o : Opts) : List String → Except String Opts
  | "--mem" :: n :: r => parseArgs { o with memMB := n.toNat! } r
  | "--max" :: n :: r => parseArgs { o with maxInstr := n.toNat!.toUInt64 } r
  | "--expect" :: p :: "--send" :: t :: r =>
    parseArgs { o with script := o.script ++ [(p, t.replace "\\n" "\n")] } r
  | "--trace-from" :: n :: r => parseArgs { o with traceFrom := n.toNat!.toUInt64 } r
  | "--trace-count" :: n :: r => parseArgs { o with traceCount := n.toNat! } r
  | "--quiet" :: r => parseArgs { o with quiet := true } r
  | f :: r => if f.startsWith "--" then .error s!"unknown option {f}" else parseArgs { o with files := o.files ++ [f] } r
  | [] => .ok o

def hex (v : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 v.toNat)
  "".pushn '0' (16 - s.length) ++ s

def dumpCpu (c : Cpu) : String :=
  s!"RIP={hex c.rip} RSP={hex c.rsp} RAX={hex c.rax} CR0={hex c.cr0} CR2={hex c.cr2} CR3={hex c.cr3} CR4={hex c.cr4} EFER={hex c.efer}"

/-- Step with a per-instruction trace to stderr. -/
partial def traceRun (m : Machine) (n : Nat) (err : IO.FS.Stream) : IO Machine := do
  if n == 0 || m.fatal.isSome then return m
  let c := m.cpu
  err.putStrLn s!"{m.icount} {hex c.rip} rax={hex c.rax} rbx={hex c.rbx} rcx={hex c.rcx} rdx={hex c.rdx} rsi={hex c.rsi} rdi={hex c.rdi} rbp={hex c.rbp} rsp={hex c.rsp} fl={hex c.rflags}"
  traceRun (step m) (n - 1) err

def main (args : List String) : IO UInt32 := do
  let o ← match parseArgs {} args with
    | .ok o => pure o
    | .error e => do IO.eprintln e; return 2
  let some (kpath : String) := o.files[0]? | do IO.eprintln "usage: x64run [options] bzImage [initrd] [cmdline]"; return 2
  let kernel ← IO.FS.readBinFile kpath
  let initrd ← match o.files[1]? with
    | some (p : String) => IO.FS.readBinFile p
    | none => pure ByteArray.empty
  let cmdline := o.files[2]?.getD "console=ttyS0 earlyprintk=serial,ttyS0"
  let mut m ← match loadLinux (o.memMB * 1024 * 1024) kernel initrd cmdline with
    | .ok m => pure m
    | .error e => do IO.eprintln s!"boot: {e}"; return 1
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
    if m.icount + chunk > o.traceFrom && o.traceCount > 0 && m.icount < o.traceFrom + o.traceCount.toUInt64 then
      if m.icount < o.traceFrom then m := m.runUntil o.traceFrom
      m ← traceRun m o.traceCount stderr
    else
      m := m.runUntil (min o.maxInstr (m.icount + chunk))
    -- console output
    let tx := m.uart.tx
    if tx.size > 0 then
      stdout.write tx
      stdout.flush
      m := { m with uart := { m.uart with tx := .empty } }
      if !script.isEmpty then
        outBuf := outBuf ++ String.fromUTF8! (ByteArray.mk (tx.data.filter (· < 128)))
    -- scripted input
    match script with
    | (pat, txt) :: rest =>
      if (outBuf.splitOn pat).length > 1 then
        if txt == "@exit" then quit := true
        else m := { m with uart := m.uart.pushRx txt.toUTF8 }.syncUart
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
      if fwd.size > 0 then m := { m with uart := m.uart.pushRx fwd }.syncUart
    if let some f := m.fatal then
      stderr.putStrLn s!"\n[x64run] stopped: {repr f}\n{dumpCpu m.cpu}"
      quit := true
    if m.icount ≥ o.maxInstr then
      if !o.quiet then stderr.putStrLn s!"\n[x64run] instruction limit reached"
      quit := true
    if m.idle then
      if !interactive && script.isEmpty then
        stderr.putStrLn s!"\n[x64run] machine idle with no pending events\n{dumpCpu m.cpu}"
        quit := true
      else IO.sleep 10
    else if interactive && m.cpu.halted then IO.sleep 5
  if interactive then
    let _ ← IO.Process.output { cmd := "sh", args := #["-c", "stty sane < /dev/tty"] }
  let t1 ← IO.monoNanosNow
  let secs := (t1 - t0).toFloat / 1e9
  if !o.quiet then
    stderr.putStrLn s!"[x64run] {m.icount} instructions in {secs} s ({m.icount.toNat.toFloat / secs / 1e6} MIPS)"
  return (if m.fatal.isSome then 1 else 0)
