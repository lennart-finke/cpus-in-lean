import X86
/-!
# doomrun — DOOM in a window

Boots `bzImage initrd` with `doomwin=1` (doom runs with `-win`) and starts `viewer` (a command
reading PPM frames on stdin and writing key events `1 k`/`2 k` on stdout). When the guest
prints `ESC _ DG <addr> ESC \`, the 320x200 xRGB framebuffer at that user address is read
through the current page tables (doom is blocked waiting for the ack) and sent to the
viewer; then the pending key events and a 0 ack go to the guest's UART. Other console output
goes to stdout. Like x86run's host loop, this is outside the formal model.

    doomrun bzImage initrd viewer [args]...
-/
open X86

/-- Copy `n` bytes at user linear address `lin`, page by page, without touching A/D bits. -/
def readLin (m : Machine) (lin n : Nat) : Option ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity n
  let mut a := lin
  while out.size < n do
    let len := min (n - out.size) (0x1000 - a % 0x1000)
    match walk a.toUInt32 false true m with
    | .ok p _ => out := m.mem.copySlice p.toNat out out.size len
    | .error _ _ => return none
    a := a + len
  return some out

def ppm (px : ByteArray) : ByteArray := Id.run do
  let mut o := "P6\n320 200\n255\n".toUTF8
  for i in [0:320*200] do
    o := ((o.push px[4*i+2]!).push px[4*i+1]!).push px[4*i]!
  return o

def marker := "\x1b_DG".toUTF8

/-- Index of `marker` in `b`, if any. -/
def findMarker (b : ByteArray) : Option Nat :=
  (List.range b.size).find? fun i => (List.range 4).all fun j => b[i+j]? == some marker[j]!

def main (args : List String) : IO UInt32 := do
  let k :: i :: vcmd :: vargs := args | do IO.eprintln "usage: doomrun bzImage initrd viewer [args]..."; return 2
  let some m0 := (loadLinux (128 * 1024 * 1024) (← IO.FS.readBinFile k) (← IO.FS.readBinFile i)
      "console=ttyS0 quiet doomwin=1").toOption | do IO.eprintln "boot failed"; return 1
  let mut m := m0
  let v ← IO.Process.spawn { cmd := vcmd, args := vargs.toArray, stdin := .piped, stdout := .piped }
  let keys ← IO.mkRef ByteArray.empty
  let closed ← IO.mkRef false
  let _ ← IO.asTask (prio := .dedicated) do
    repeat
      let b ← v.stdout.read 2  -- one event; larger reads block until full
      if b.isEmpty then break
      keys.modify (· ++ b)
    closed.set true
  let out ← IO.getStdout
  let mut acc := ByteArray.empty
  while !(← closed.get) && m.fatal.isNone do
    m := m.runUntil (m.icount + 2000000)
    acc := acc ++ m.uart.tx
    m := { m with uart := { m.uart with tx := .empty } }
    match findMarker acc with
    | some j =>
      if acc.size < j + 14 then continue
      out.write (acc.extract 0 j)
      let addr := (String.fromUTF8! (acc.extract (j+4) (j+12))).foldl (fun a c =>
        16 * a + (if c.isDigit then c.toNat - 48 else c.toNat - 87)) 0
      acc := acc.extract (j+14) acc.size
      if let some px := readLin m addr (320*200*4) then
        v.stdin.write (ppm px); v.stdin.flush
      let ks ← keys.modifyGet fun a => (a, .empty)
      m := { m with uart := m.uart.pushRx (ks.push 0) }.syncUart
    | none =>
      -- keep a possible marker prefix at the end
      let cut := match (List.range acc.size).reverse.find? (acc[·]! == 0x1b) with
        | some e => if acc.size - e < 4 then e else acc.size
        | none => acc.size
      out.write (acc.extract 0 cut); out.flush
      acc := acc.extract cut acc.size
      if m.idle then IO.sleep 5
  if let some f := m.fatal then IO.eprintln s!"[doomrun] stopped: {repr f}"
  return 0
