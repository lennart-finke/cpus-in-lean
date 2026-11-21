import Solutions.OpensslSha256.Frame
/-! Instruction families of `sha256_block_data_order` (generated): each lemma is one
encoding at a symbolic address, its effect proved by `cbv`. -/
namespace Solutions.OpensslSha256
open X86 Solutions.Logic Solutions.Exec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000
set_option Elab.async false

theorem fam_31f7 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xf7])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (r.edi ^^^ r.esi) } (logicF 4 (r.edi ^^^ r.esi)).2 (p.add 2) ic) := by
  cbv

theorem fam_01d7 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xd7])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (r.edi + r.edx) } (addF 4 r.edi r.edx 0).2 (p.add 2) ic) := by
  cbv

theorem fam_010424 (p : UInt32) (G : CodeMem p 3 (codeOf [0x01, 0x04, 0x24])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.esp.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get r.esp 4 ((rdRaw G.get r.esp 4) + r.eax)) r (addF 4 (rdRaw G.get r.esp 4) r.eax 0).2 (p.add 3) ic) := by
  cbv

theorem fam_01c7 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xc7])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (r.edi + r.eax) } (addF 4 r.edi r.eax 0).2 (p.add 2) ic) := by
  cbv

theorem fam_b810000000 (p : UInt32) (G : CodeMem p 5 (codeOf [0xb8, 0x10, 0x00, 0x00, 0x00])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := 16 } fl (p.add 5) ic) := by
  cbv

theorem fam_89bc2494000000 (p : UInt32) (G : CodeMem p 7 (codeOf [0x89, 0xbc, 0x24, 0x94, 0x00, 0x00, 0x00])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (UInt32.add r.esp 148).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.esp 148) 4 r.edi) r fl (p.add 7) ic) := by
  cbv

theorem fam_8d50dd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x8d, 0x50, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.eax + d.toUInt32) } fl (p.add 3) ic) := by
  cbv

theorem fam_83e209 (p : UInt32) (G : CodeMem p 3 (codeOf [0x83, 0xe2, 0x09])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx &&& 9) } (logicF 4 (r.edx &&& 9)).2 (p.add 3) ic) := by
  cbv

theorem fam_899424a4000000 (p : UInt32) (G : CodeMem p 7 (codeOf [0x89, 0x94, 0x24, 0xa4, 0x00, 0x00, 0x00])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (UInt32.add r.esp 164).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.esp 164) 4 r.edx) r fl (p.add 7) ic) := by
  cbv

theorem fam_8b6c94dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x8b, 0x6c, 0x94, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.edx 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.edx 2)) d.toUInt32) 4) } fl (p.add 4) ic) := by
  cbv

theorem fam_89c6 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xc6])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := r.eax } fl (p.add 2) ic) := by
  cbv

theorem fam_c1c019 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc0, 0x19])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (rolV r.eax 25) } (mixF fl (rolF (rolV r.eax 25)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_c1c30e (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc3, 0x0e])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (rolV r.ebx 14) } (mixF fl (rolF (rolV r.ebx 14)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_c1ed03 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xed, 0x03])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (shrV r.ebp 3) } (shrF r.ebp 3) (p.add 3) ic) := by
  cbv

theorem fam_8d46dd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x8d, 0x46, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.esi + d.toUInt32) } fl (p.add 3) ic) := by
  cbv

theorem fam_83e00e (p : UInt32) (G : CodeMem p 3 (codeOf [0x83, 0xe0, 0x0e])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax &&& 14) } (logicF 4 (r.eax &&& 14)).2 (p.add 3) ic) := by
  cbv

theorem fam_8b5484dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x8b, 0x54, 0x84, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32) 4) } fl (p.add 4) ic) := by
  cbv

theorem fam_c1c00f (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc0, 0x0f])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (rolV r.eax 15) } (mixF fl (rolF (rolV r.eax 15)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_c1c30d (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc3, 0x0d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (rolV r.ebx 13) } (mixF fl (rolF (rolV r.ebx 13)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_c1e80a (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xe8, 0x0a])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (shrV r.eax 10) } (shrF r.eax 10) (p.add 3) ic) := by
  cbv

theorem fam_31d8 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xd8])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax ^^^ r.ebx) } (logicF 4 (r.eax ^^^ r.ebx)).2 (p.add 2) ic) := by
  cbv

theorem fam_8d5edd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x8d, 0x5e, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.esi + d.toUInt32) } fl (p.add 3) ic) := by
  cbv

theorem fam_83e309 (p : UInt32) (G : CodeMem p 3 (codeOf [0x83, 0xe3, 0x09])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx &&& 9) } (logicF 4 (r.ebx &&& 9)).2 (p.add 3) ic) := by
  cbv

theorem fam_036c9cdd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x03, 0x6c, 0x9c, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.ebx 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp + (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.ebx 2)) d.toUInt32) 4)) } (addF 4 r.ebp (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.ebx 2)) d.toUInt32) 4) 0).2 (p.add 4) ic) := by
  cbv

theorem fam_83e208 (p : UInt32) (G : CodeMem p 3 (codeOf [0x83, 0xe2, 0x08])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx &&& 8) } (logicF 4 (r.edx &&& 8)).2 (p.add 3) ic) := by
  cbv

end Solutions.OpensslSha256
