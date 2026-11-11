import Ssl
import Check.Support
import Check.SpecVectors
import Check.Encodings
import Check.Boot

/-! Executable checks of the pinned machine code against the specifications, on the CPU model.

Every run is an instance of a task: the caller state is built with pseudo-random memory, registers
and flags and one of several buffer placements, the task's precondition is evaluated on it (so the
preconditions are known to be satisfiable and the runs to be covered by the statements), and the
whole postcondition is checked, including the memory-preservation and stack-bound clauses.
These finite examples do not discharge the universally quantified tasks in `Statement.lean`.

    sslcheck                 the checks below
    sslcheck high            the slow checks: the SHA-256 bit count past 2^32 bits, then the checks
                             below in a memory of more than 2 GiB, with every buffer and the stack
                             at addresses from 2^31 (a few minutes and about 10 GiB of memory)
    sslcheck spec FILE [KIND…]  evaluate the specifications on reference vectors (tools/spec_vectors.py)
                             or on a hardware transcript (tools/hw.py); the KINDs must occur
    sslcheck boot ELF        run a multiboot driver of tools/hw.py on the model, printing its output
    sslcheck encodings       print the instruction classes the checks execute, with counts
    sslcheck classify FILE   print the instruction classes of the fuzzer's vectors (tools/encodings.py)
-/
open X86 Ssl Check

def shaChecks (t : T) : IO Unit := do
  let img := OpensslSha256.img
  let stack := OpensslSha256.stackBound
  let cases : List (List (List UInt8)) :=
    [[], [[0x61], [], [0x62, 0x63]], [bytes 65 1], [bytes 55 2, bytes 9 3, bytes 200 4], [bytes 64 5, bytes 64 6]]
  for short in [false, true] do
    let ini := if short then OpensslSha256.Image.sym_SHA224_Init else OpensslSha256.Image.sym_SHA256_Init
    let upd := if short then OpensslSha256.Image.sym_SHA224_Update else OpensslSha256.Image.sym_SHA256_Update
    let fin := if short then OpensslSha256.Image.sym_SHA224_Final else OpensslSha256.Image.sym_SHA256_Final
    let n := if short then 28 else 32
    for chunks in cases, L in t.layouts img stack do
      -- every call has its own caller; the context moves between calls
      let ctx := L.slot 0
      let c ← t.caller img L [ctx] []
      ensure "SHA init precondition" (decide (OpensslSha256.InitPre c ctx))
      let m ← t.call "sha256" img c ini stack [(ctx, 112)]
      ensure "SHA init return" (m.cpu.eax == 1)
      let mut st := bytesAt m ctx 112
      let mut k := 1
      for chunk in chunks do
        let ctx := L.slot (k % 3)
        -- an empty chunk may come with any pointer
        let msgp := if chunk.isEmpty then 0xFFFFFFF1 else L.slot 3
        let c ← t.caller img L [ctx, msgp, chunk.length.toUInt32] [(ctx, st), (msgp, chunk)]
        ensure "SHA update precondition" (decide (OpensslSha256.UpdatePre c ctx msgp st chunk))
        let m ← t.call "sha256" img c upd stack [(ctx, 112)]
        ensure "SHA update return" (m.cpu.eax == 1)
        st := bytesAt m ctx 112
        k := k + 1
      let ctx := L.slot (k % 3)
      let out := L.slot 3
      let c ← t.caller img L [out, ctx] [(ctx, st)]
      ensure "SHA final precondition" (decide (OpensslSha256.FinalPre n c out ctx st))
      let m ← t.call "sha256" img c fin stack [(ctx, 112), (out, n)]
      let want := if short then Spec.Sha256.sha224 chunks.flatten else Spec.Sha256.sha256 chunks.flatten
      ensure "SHA digest/return" (m.cpu.eax == 1 && bytesAt m out n == want)
      ensure "SHA buffer wipe" (bytesAt m (ctx + OpensslSha256.dataOff) 68 == List.replicate 68 0)
  for L in t.layouts img stack, seed in [1, 2, 3] do
    let block := bytes 64 seed
    let h : Array UInt32 := if seed == 1 then Spec.Sha256.H0_256 else words 8 (seed + 10)
    let ctx := L.slot 0
    let blockp := L.slot 1
    let c ← t.caller img L [ctx, blockp] [(ctx, wordBytes h), (blockp, block)]
    ensure "SHA transform precondition" (decide (OpensslSha256.TransformPre c ctx blockp h block))
    let m ← t.call "sha256" img c OpensslSha256.Image.sym_SHA256_Transform stack [(ctx, 32)]
    ensure "SHA compression" (wordsAt m ctx 8 == Spec.Sha256.compress h block)
  IO.println "PASS: SHA-256/SHA-224 streaming, padding, wiping and compression"

/-- The carry of the bit count from `Nl` into `Nh`, which a message reaches at 2^32 bits (512 MiB).
Hashing that much on the model is out of reach, so the 112 context bytes are set to what the
statement says they hold after 2^23 - 1 zero blocks (2^32 - 512 bits): the hash words are the
specification's compression function iterated over those blocks, `Nl` is the bit count, `Nh` and
`num` are 0. A real `SHA256_Update` with 100 more bytes then crosses 2^32 bits and a real
`SHA256_Final` encodes the 64-bit length; the digest must be the specification's for the whole
message (its padding is spelled out here, since the message itself is too long to build). -/
def shaCarryCheck (t : T) : IO Unit := do
  let img := OpensslSha256.img
  let stack := OpensslSha256.stackBound
  let L := (Check.layouts img stack)[0]!
  let nBlocks := 2 ^ 23 - 1
  let zeroBlock := List.replicate 64 (0 : UInt8)
  let mut h := Spec.Sha256.H0_256
  for _ in [0:nBlocks] do
    h := Spec.Sha256.compress h zeroBlock
  let tail := bytes 100 41
  let total := nBlocks * 64 + tail.length
  ensure "SHA carry: the message is within the standard's bound" (total < Spec.Sha256.lenBound)
  let (ctx, msgp, out) := (L.slot 0, L.slot 3, L.slot 1)
  let c ← t.caller img L [ctx] []
  let m ← t.call "sha256" img c OpensslSha256.Image.sym_SHA256_Init stack [(ctx, 112)]
  let st := wordBytes h ++ le32 (nBlocks * 512).toUInt32 ++ le32 0 ++ (bytesAt m ctx 112).drop 40
  ensure "SHA carry: context layout" (st.length == 112 && wordAt m (ctx + 104) == 0)
  let c ← t.caller img L [ctx, msgp, tail.length.toUInt32] [(ctx, st), (msgp, tail)]
  ensure "SHA carry: update precondition" (decide (OpensslSha256.UpdatePre c ctx msgp st tail))
  let m ← t.call "sha256" img c OpensslSha256.Image.sym_SHA256_Update stack [(ctx, 112)]
  ensure "SHA carry: Nl wrapped and Nh incremented"
    (wordAt m (ctx + 32) == (total * 8).toUInt32 && wordAt m (ctx + 36) == 1)
  let st := bytesAt m ctx 112
  let c ← t.caller img L [out, ctx] [(ctx, st)]
  ensure "SHA carry: final precondition" (decide (OpensslSha256.FinalPre 32 c out ctx st))
  let m ← t.call "sha256" img c OpensslSha256.Image.sym_SHA256_Final stack [(ctx, 112), (out, 32)]
  let padded := tail ++ [0x80] ++ List.replicate ((119 - total % 64) % 64) 0 ++ be64 (8 * total).toUInt64
  let want := (Spec.Sha256.blocks padded).foldl Spec.Sha256.compress h
  ensure "SHA carry: digest" (m.cpu.eax == 1 && bytesAt m out 32 == (List.range 8).flatMap fun i => be32 want[i]!)
  IO.println "PASS: SHA-256 bit count carried past 2^32 bits (from the specification's state after 2^23 - 1 blocks)"

def chachaChecks (t : T) : IO Unit := do
  let img := OpensslChacha20.img
  let stack := OpensslChacha20.stackBound
  let key := Spec.Chacha.rfcState.extract 4 12
  for counter in [1, 0xffffffff], L in t.layouts img stack do
    let ctr : Array UInt32 := #[counter, 0x09000000, 0x4a000000, 0]
    for n in [0, 1, 63, 64, 65, 129, 200], inPlace in [false, true] do
      let src := bytes n (n + 7)
      let (keyp, ctrp) := (L.slot 0, L.slot 0 + 32)
      -- with no data the pointers are never used
      let inp := if n == 0 then 0xFFFFFFF3 else L.slot 1
      let out := if n == 0 then 0xFFFFFFF7 else if inPlace then inp else L.slot 2
      let c ← t.caller img L (OpensslChacha20.args out inp keyp ctrp src)
        [(keyp, wordBytes key), (ctrp, wordBytes ctr), (inp, src)]
      ensure "ChaCha20 precondition" (decide (OpensslChacha20.Pre c out inp keyp ctrp key ctr src))
      let m ← t.call "chacha20" img c OpensslChacha20.Image.sym_ChaCha20_ctr32 stack [(out, n)]
      ensure "ChaCha20 ciphertext"
        (bytesAt m out n == Spec.Chacha.crypt 20 (OpensslChacha20.state key ctr) src)
  IO.println "PASS: ChaCha20 block boundaries, counter wrap and in-place encryption"

def polyChecks (t : T) : IO Unit := do
  let img := OpensslPoly1305.img
  let stack := OpensslPoly1305.stackBound
  let key : List UInt8 :=
    [0x85, 0xd6, 0xbe, 0x78, 0x57, 0x55, 0x6d, 0x33, 0x7f, 0x44, 0x52, 0xfe, 0x42, 0xd5, 0x06, 0xa8,
     0x01, 0x03, 0x80, 0x8a, 0xfb, 0x0d, 0xb2, 0xfd, 0x4a, 0xbf, 0xf6, 0xaf, 0x41, 0x49, 0xf5, 0x1b]
  let msg := "Cryptographic Forum Research Group".toUTF8.data.toList
  let long := bytes 150 9
  let cases := [[], [msg], [msg.take 16, [], (msg.drop 16).take 1, msg.drop 17],
                [long.take 5, (long.drop 5).take 40, long.drop 45]]
  for chunks in cases, L in t.layouts img stack, key in [key, bytes 32 21] do
    let (ctx, keyp) := (L.slot 0, L.slot 3)
    let c ← t.caller img L [ctx, keyp] [(keyp, key)]
    ensure "Poly1305 init precondition" (decide (OpensslPoly1305.InitPre c ctx keyp key))
    let m ← t.call "poly1305" img c OpensslPoly1305.Image.sym_Poly1305_Init stack [(ctx, 236)]
    let mut st := bytesAt m ctx 236
    let mut k := 1
    for chunk in chunks do
      let ctx := L.slot (k % 3)
      let msgp := if chunk.isEmpty then 0xFFFFFFF1 else L.slot 3
      let c ← t.caller img L [ctx, msgp, chunk.length.toUInt32] [(ctx, st), (msgp, chunk)]
      ensure "Poly1305 update precondition" (decide (OpensslPoly1305.UpdatePre c ctx msgp st chunk))
      let m ← t.call "poly1305" img c OpensslPoly1305.Image.sym_Poly1305_Update stack [(ctx, 236)]
      st := bytesAt m ctx 236
      k := k + 1
    let (ctx, mac) := (L.slot (k % 3), L.slot 3)
    let c ← t.caller img L [ctx, mac] [(ctx, st)]
    ensure "Poly1305 final precondition" (decide (OpensslPoly1305.FinalPre c ctx mac st))
    let m ← t.call "poly1305" img c OpensslPoly1305.Image.sym_Poly1305_Final stack [(ctx, 236), (mac, 16)]
    ensure "Poly1305 tag" (bytesAt m mac 16 == Spec.Poly1305.poly1305 key chunks.flatten)
    ensure "Poly1305 wipe" (bytesAt m ctx 236 == List.replicate 236 0)
  for L in t.layouts img stack do
    let c ← t.caller img L [] []
    ensure "Poly1305 ctx size precondition" (decide (Calls img c stack []))
    let m ← t.call "poly1305" img c OpensslPoly1305.Image.sym_Poly1305_ctx_size stack []
    ensure "Poly1305 ctx size" (m.cpu.eax == 236)
  IO.println "PASS: Poly1305 streaming, RFC vector, context size and wiping"

/-- A limb vector within `Bounded num e`: at the bound with the given signs, or pseudo-random inside it. -/
def limbs (num e : Nat) (extreme : Bool) (seed : UInt64) : Array UInt32 := Id.run do
  let mut s := seed
  let mut v := #[]
  for i in [0:10] do
    let bound := num * 2 ^ (e - i % 2) / 100
    s := lcg s
    let r := (s >>> 20).toNat
    let mag := if extreme then bound else r % (bound + 1)
    let x : Int := if (r >>> 40) % 2 == 1 then -(mag : Int) else mag
    v := v.push (Int32.ofInt x).toUInt32
  return v

def curveChecks (t : T) : IO Unit := do
  let img := OpensslX25519.img
  let stack := OpensslX25519.stackBound
  let Ls := t.layouts img stack
  -- field operations: limbs at and inside the documented bounds, every permitted aliasing
  let ops : List (String × UInt32 × Bool × Nat × Nat × Nat × Nat) :=
    [("fe_mul", OpensslX25519.Image.sym_fe_mul, true, 165, 26, 101, 25),
     ("fe_sq", OpensslX25519.Image.sym_fe_sq, false, 165, 26, 101, 25),
     ("fe_add", OpensslX25519.Image.sym_fe_add, true, 110, 25, 110, 26),
     ("fe_sub", OpensslX25519.Image.sym_fe_sub, true, 110, 25, 110, 26)]
  for (name, fn, two, inN, inE, outN, outE) in ops do
    for it in [0:if t.high then 12 else 72] do
      let L := Ls[it % Ls.length]!
      let alias := it % 6          -- 0,1: none; 2: h = f; 3: h = g; 4: f = g; 5: h = f = g
      let extreme := it < (if t.high then 6 else 24)
      let fv := limbs inN inE extreme (1000 + it).toUInt64
      let gv := if alias ≥ 4 then fv else limbs inN inE extreme (5000 + it).toUInt64
      let f := L.slot 0
      let g := if alias ≥ 4 then f else L.slot 1
      let h := if alias == 2 || alias == 5 then f else if alias == 3 then g else L.slot 2
      let (h, g, gv) := if two then (h, g, gv) else ((if alias % 2 == 0 then L.slot 2 else f), f, fv)
      let c ← t.caller img L (if two then [g] else []) [(f, wordBytes fv), (g, wordBytes gv)]
        (ecx := some h) (edx := some f)
      if two then
        ensure s!"{name} precondition" (decide (OpensslX25519.FieldCall2 c h f g fv gv) &&
          decide (OpensslX25519.Bounded inN inE fv) && decide (OpensslX25519.Bounded inN inE gv))
      else
        ensure s!"{name} precondition" (decide (OpensslX25519.FieldCall1 c h f fv) &&
          decide (OpensslX25519.Bounded inN inE fv))
      let m ← t.call "x25519" img c fn stack [(h, 40)]
      let r := wordsAt m h 10
      let (a, b) := (OpensslX25519.feValI fv, OpensslX25519.feValI gv)
      let want := match name with | "fe_mul" => a * b | "fe_sq" => a * a | "fe_add" => a + b | _ => a - b
      ensure s!"{name} output bounds" (decide (OpensslX25519.Bounded outN outE r))
      ensure s!"{name} value" (OpensslX25519.feValI r % OpensslX25519.pI == want % OpensslX25519.pI)
  let key := Spec.X25519.leBytes 32
    0x449a44ba44226a50185afcc10a4c1462dd5e46824b15163b9d7c52f06be346a0
  let u := Spec.X25519.leBytes 32
    0x4c1cabd0a603a9103b35b326ec2466727c5fb124a4c19435db3030586768dbe6
  let points := [u, List.replicate 32 0, List.replicate 32 0xff,
                 Spec.X25519.leBytes 32 (Spec.X25519.p + 1 + 2 ^ 255), bytes 32 77]
  let mut i := 0
  for point in points do
    let L := Ls[i % Ls.length]!
    let (kp, up) := (L.slot 0, L.slot 1)
    -- the output may be either input buffer
    let out := match i % 3 with | 0 => L.slot 2 | 1 => kp | _ => up
    let c ← t.caller img L [out, kp, up] [(kp, key), (up, point)]
    ensure "X25519 precondition" (decide (OpensslX25519.X25519Pre c out kp up key point))
    let m ← t.call "x25519" img c OpensslX25519.Image.sym_ossl_x25519 stack [(out, 32)]
    let want := Spec.X25519.x25519 key point
    ensure "X25519 result" (bytesAt m out 32 == want && m.cpu.eax == OpensslX25519.retVal want)
    i := i + 1
  for L in Ls, inPlace in [false, true], key in [key, bytes 32 31] do
    let kp := L.slot 0
    let out := if inPlace then kp else L.slot 2
    let c ← t.caller img L [out, kp] [(kp, key)]
    ensure "X25519 public key precondition" (decide (OpensslX25519.PublicPre c out kp key))
    let m ← t.call "x25519" img c OpensslX25519.Image.sym_ossl_x25519_public_from_private stack [(out, 32)]
    ensure "X25519 public key" (bytesAt m out 32 == Spec.X25519.x25519 key OpensslX25519.basePoint)
  IO.println "PASS: X25519 field operations at their bounds and aliased, RFC vector, low-order and non-canonical inputs, public key"

def smoke (t : T) : IO Unit := do
  shaChecks t
  chachaChecks t
  polyChecks t
  curveChecks t

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    let t ← T.new
    smoke t
    t.report [("sha256", OpensslSha256.stackBound), ("chacha20", OpensslChacha20.stackBound),
              ("poly1305", OpensslPoly1305.stackBound), ("x25519", OpensslX25519.stackBound)]
    return 0
  | ["high"] =>
    let t ← T.new
    shaCarryCheck t
    let t ← T.new (high := true)
    smoke t
    IO.println s!"{← t.calls.get} calls checked against their contracts above address 2^31"
    return 0
  | "spec" :: file :: required => specVectors file required
  | ["boot", elf] => boot elf
  | ["encodings"] =>
    let t ← T.new (record := true)
    smoke t
    t.printEncodings
    return 0
  | ["classify", vectors] =>
    for (k, n) in (← vectorClasses vectors).toArray.qsort (fun a b => a.1 < b.1) do
      IO.println s!"{k} {n}"
    return 0
  | _ => IO.eprintln "usage: sslcheck [high | spec FILE [KIND…] | boot ELF | encodings | classify FILE]"; return 2
