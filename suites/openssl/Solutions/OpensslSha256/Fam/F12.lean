import Solutions.OpensslSha256.Frame
/-! Instruction families of `sha256_block_data_order` (generated): each lemma is one
encoding at a symbolic address, its effect proved by `cbv`. -/
namespace Solutions.OpensslSha256
open X86 Solutions.Logic Solutions.Exec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000
set_option Elab.async false

theorem fam_01d6 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xd6])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (r.esi + r.edx) } (addF 4 r.esi r.edx 0).2 (p.add 2) ic) := by
  cbv

theorem fam_01de (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xde])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (r.esi + r.ebx) } (addF 4 r.esi r.ebx 0).2 (p.add 2) ic) := by
  cbv

theorem fam_83e30d (p : UInt32) (G : CodeMem p 3 (codeOf [0x83, 0xe3, 0x0d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx &&& 13) } (logicF 4 (r.ebx &&& 13)).2 (p.add 3) ic) := by
  cbv

theorem fam_c1c515 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc5, 0x15])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (rolV r.ebp 21) } (mixF fl (rolF (rolV r.ebp 21)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_c1c313 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc3, 0x13])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (rolV r.ebx 19) } (mixF fl (rolF (rolV r.ebx 19)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_232c24 (p : UInt32) (G : CodeMem p 3 (codeOf [0x23, 0x2c, 0x24])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.esp.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp &&& (rdRaw G.get r.esp 4)) } (logicF 4 (r.ebp &&& (rdRaw G.get r.esp 4))).2 (p.add 3) ic) := by
  cbv

theorem fam_83e00d (p : UInt32) (G : CodeMem p 3 (codeOf [0x83, 0xe0, 0x0d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax &&& 13) } (logicF 4 (r.eax &&& 13)).2 (p.add 3) ic) := by
  cbv

theorem fam_035c84dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x03, 0x5c, 0x84, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx + (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32) 4)) } (addF 4 r.ebx (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32) 4) 0).2 (p.add 4) ic) := by
  cbv

theorem fam_01d3 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xd3])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx + r.edx) } (addF 4 r.ebx r.edx 0).2 (p.add 2) ic) := by
  cbv

theorem fam_895c84dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x89, 0x5c, 0x84, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32) 4 r.ebx) r fl (p.add 4) ic) := by
  cbv

theorem fam_c1c207 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc2, 0x07])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (rolV r.edx 7) } (mixF fl (rolF (rolV r.edx 7)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_21e8 (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xe8])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax &&& r.ebp) } (logicF 4 (r.eax &&& r.ebp)).2 (p.add 2) ic) := by
  cbv

theorem fam_89ce (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xce])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := r.ecx } fl (p.add 2) ic) := by
  cbv

theorem fam_234c24dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x23, 0x4c, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (r.ecx &&& (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4)) } (logicF 4 (r.ecx &&& (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4))).2 (p.add 4) ic) := by
  cbv

theorem fam_31d9 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xd9])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (r.ecx ^^^ r.ebx) } (logicF 4 (r.ecx ^^^ r.ebx)).2 (p.add 2) ic) := by
  cbv

theorem fam_034c84dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x03, 0x4c, 0x84, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (r.ecx + (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32) 4)) } (addF 4 r.ecx (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32) 4) 0).2 (p.add 4) ic) := by
  cbv

theorem fam_894c84dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x89, 0x4c, 0x84, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32) 4 r.ecx) r fl (p.add 4) ic) := by
  cbv

theorem fam_31f8 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xf8])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax ^^^ r.edi) } (logicF 4 (r.eax ^^^ r.edi)).2 (p.add 2) ic) := by
  cbv

theorem fam_83f008 (p : UInt32) (G : CodeMem p 3 (codeOf [0x83, 0xf0, 0x08])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax ^^^ 8) } (logicF 4 (r.eax ^^^ 8)).2 (p.add 3) ic) := by
  cbv

theorem fam_8b54acdd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x8b, 0x54, 0xac, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.ebp 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.ebp 2)) d.toUInt32) 4) } fl (p.add 4) ic) := by
  cbv

theorem fam_83c007 (p : UInt32) (G : CodeMem p 3 (codeOf [0x83, 0xc0, 0x07])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax + 7) } (addF 4 r.eax 7 0).2 (p.add 3) ic) := by
  cbv

theorem fam_83e00f (p : UInt32) (G : CodeMem p 3 (codeOf [0x83, 0xe0, 0x0f])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax &&& 15) } (logicF 4 (r.eax &&& 15)).2 (p.add 3) ic) := by
  cbv

theorem fam_036c84dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x03, 0x6c, 0x84, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp + (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32) 4)) } (addF 4 r.ebp (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32) 4) 0).2 (p.add 4) ic) := by
  cbv

theorem fam_896c84dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x89, 0x6c, 0x84, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.eax 2)) d.toUInt32) 4 r.ebp) r fl (p.add 4) ic) := by
  cbv

theorem fam_01ef (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xef])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (r.edi + r.ebp) } (addF 4 r.edi r.ebp 0).2 (p.add 2) ic) := by
  cbv

end Solutions.OpensslSha256
