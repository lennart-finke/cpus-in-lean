import Solutions.OpensslPoly1305.FinRun
/-!
# The image word `OPENSSL_cleanse` calls through

`movl 0x1005fc, %eax` loads the address of `memset` (`0x1005d0`) from the image; every memory of a
run (`PMem`, a `CodeMem` of the image) holds it.
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305 Solutions.Exec.Mul Solutions.Exec.Fast

set_option autoImplicit false

theorem img_word (N : PMem) : rdRaw N.get 1050108 4 = 1050064 := by
  have hf : 1048576 + 1536 ≤ N.mem.size := N.fits
  have e0 : N.mem.get! 1050108 = Image.byte 1532 := N.ok 1532 (by decide)
  have e1 : N.mem.get! 1050109 = Image.byte 1533 := N.ok 1533 (by decide)
  have e2 : N.mem.get! 1050110 = Image.byte 1534 := N.ok 1534 (by decide)
  have e3 : N.mem.get! 1050111 = Image.byte 1535 := N.ok 1535 (by decide)
  show rdBytes N.mem 1050108 4 = 1050064
  rw [rdBytes4_eq (by simp only [UInt32.reduceToNat]; omega)]
  simp only [UInt32.reduceToNat, Nat.reduceAdd]
  rw [e0, e1, e2, e3]
  decide

/-- The tag words `poly1305_emit` computes from `h` and `s` (as `cbv` leaves them): `g = h + 5`, the
selection by `g4 >> 2`, then `+ s` with carries. -/
def emitW (h0 h1 h2 h3 h4 s0 s1 s2 s3 : UInt32) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let g0 := addF 4 h0 5 0
  let g1 := addF 4 h1 0 (cfBit g0.2)
  let g2 := addF 4 h2 0 (cfBit g1.2)
  let g3 := addF 4 h3 0 (cfBit g2.2)
  let g4 := addF 4 h4 0 (cfBit g3.2)
  let b := UInt32.shiftRight g4.1 2
  let nm := UInt32.add b 4294967295
  let m := UInt32.sub 0 b
  let t0 := (logicF 4 (UInt32.lor (UInt32.land h0 nm) (UInt32.land g0.1 m))).1
  let t1 := (logicF 4 (UInt32.lor (UInt32.land h1 nm) (UInt32.land g1.1 m))).1
  let t2 := (logicF 4 (UInt32.lor (UInt32.land h2 nm) (UInt32.land g2.1 m))).1
  let t3 := (logicF 4 (UInt32.lor (UInt32.land nm h3) (UInt32.land m g3.1))).1
  let o0 := addF 4 t0 s0 0
  let o1 := addF 4 t1 s1 (cfBit o0.2)
  let o2 := addF 4 t2 s2 (cfBit o1.2)
  let o3 := addF 4 t3 s3 (cfBit o2.2)
  (o0.1, o1.1, o2.1, o3.1)

end Solutions.OpensslPoly1305
