import Solutions.OpensslSha256.Frame
/-! Instruction families of `sha256_block_data_order` (generated): each lemma is one
encoding at a symbolic address, its effect proved by `cbv`. -/
namespace Solutions.OpensslSha256
open X86 Solutions.Logic Solutions.Exec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000
set_option Elab.async false

theorem fam_c1eb0a (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xeb, 0x0a])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (shrV r.ebx 10) } (shrF r.ebx 10) (p.add 3) ic) := by
  cbv

theorem fam_8d41dd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x8d, 0x41, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.ecx + d.toUInt32) } fl (p.add 3) ic) := by
  cbv

theorem fam_83e00a (p : UInt32) (G : CodeMem p 3 (codeOf [0x83, 0xe0, 0x0a])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax &&& 10) } (logicF 4 (r.eax &&& 10)).2 (p.add 3) ic) := by
  cbv

theorem fam_035484dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x03, 0x54, 0x84, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx + (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32) 4)) } (addF 4 r.edx (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32) 4) 0).2 (p.add 4) ic) := by
  cbv

theorem fam_01da (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xda])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx + r.ebx) } (addF 4 r.edx r.ebx 0).2 (p.add 2) ic) := by
  cbv

theorem fam_8b8424a4000000 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8b, 0x84, 0x24, 0xa4, 0x00, 0x00, 0x00])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (UInt32.add r.esp 164).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (rdRaw G.get (UInt32.add r.esp 164) 4) } fl (p.add 7) ic) := by
  cbv

theorem fam_895484dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x89, 0x54, 0x84, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32) 4 r.edx) r fl (p.add 4) ic) := by
  cbv

theorem fam_8b9c2494000000 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8b, 0x9c, 0x24, 0x94, 0x00, 0x00, 0x00])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (UInt32.add r.esp 148).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (rdRaw G.get (UInt32.add r.esp 148) 4) } fl (p.add 7) ic) := by
  cbv

theorem fam_31cb (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xcb])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx ^^^ r.ecx) } (logicF 4 (r.ebx ^^^ r.ecx)).2 (p.add 2) ic) := by
  cbv

theorem fam_8b4484dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x8b, 0x44, 0x84, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32) 4) } fl (p.add 4) ic) := by
  cbv

theorem fam_c1c219 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc2, 0x19])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (rolV r.edx 25) } (mixF fl (rolF (rolV r.edx 25)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_c1c20f (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc2, 0x0f])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (rolV r.edx 15) } (mixF fl (rolF (rolV r.edx 15)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_c1ea0a (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xea, 0x0a])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (shrV r.edx 10) } (shrF r.edx 10) (p.add 3) ic) := by
  cbv

theorem fam_8d5fdd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x8d, 0x5f, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.edi + d.toUInt32) } fl (p.add 3) ic) := by
  cbv

theorem fam_83e30b (p : UInt32) (G : CodeMem p 3 (codeOf [0x83, 0xe3, 0x0b])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx &&& 11) } (logicF 4 (r.ebx &&& 11)).2 (p.add 3) ic) := by
  cbv

theorem fam_03549cdd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x03, 0x54, 0x9c, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.ebx 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx + (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.ebx 2)) d.toUInt32) 4)) } (addF 4 r.edx (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.ebx 2)) d.toUInt32) 4) 0).2 (p.add 4) ic) := by
  cbv

theorem fam_83e30a (p : UInt32) (G : CodeMem p 3 (codeOf [0x83, 0xe3, 0x0a])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx &&& 10) } (logicF 4 (r.ebx &&& 10)).2 (p.add 3) ic) := by
  cbv

theorem fam_89549cdd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x89, 0x54, 0x9c, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.ebx 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.ebx 2)) d.toUInt32) 4 r.edx) r fl (p.add 4) ic) := by
  cbv

theorem fam_8b0c24 (p : UInt32) (G : CodeMem p 3 (codeOf [0x8b, 0x0c, 0x24])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.esp.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (rdRaw G.get r.esp 4) } fl (p.add 3) ic) := by
  cbv

theorem fam_8bbc2494000000 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8b, 0xbc, 0x24, 0x94, 0x00, 0x00, 0x00])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (UInt32.add r.esp 148).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (rdRaw G.get (UInt32.add r.esp 148) 4) } fl (p.add 7) ic) := by
  cbv

theorem fam_8b548cdd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x8b, 0x54, 0x8c, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.ecx 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.ecx 2)) d.toUInt32) 4) } fl (p.add 4) ic) := by
  cbv

theorem fam_c1ea03 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xea, 0x03])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (shrV r.edx 3) } (shrF r.edx 3) (p.add 3) ic) := by
  cbv

theorem fam_8b448cdd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x8b, 0x44, 0x8c, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.ecx 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.ecx 2)) d.toUInt32) 4) } fl (p.add 4) ic) := by
  cbv

theorem fam_8d59dd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x8d, 0x59, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ecx + d.toUInt32) } fl (p.add 3) ic) := by
  cbv

theorem fam_83e30c (p : UInt32) (G : CodeMem p 3 (codeOf [0x83, 0xe3, 0x0c])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx &&& 12) } (logicF 4 (r.ebx &&& 12)).2 (p.add 3) ic) := by
  cbv

end Solutions.OpensslSha256
