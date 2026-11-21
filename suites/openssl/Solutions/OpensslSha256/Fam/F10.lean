import Solutions.OpensslSha256.Frame
/-! Instruction families of `sha256_block_data_order` (generated): each lemma is one
encoding at a symbolic address, its effect proved by `cbv`. -/
namespace Solutions.OpensslSha256
open X86 Solutions.Logic Solutions.Exec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000
set_option Elab.async false

theorem fam_036c94dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x03, 0x6c, 0x94, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.edx 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp + (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.edx 2)) d.toUInt32) 4)) } (addF 4 r.ebp (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.edx 2)) d.toUInt32) 4) 0).2 (p.add 4) ic) := by
  cbv

theorem fam_89f3 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xf3])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := r.esi } fl (p.add 2) ic) := by
  cbv

theorem fam_c1c315 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc3, 0x15])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (rolV r.ebx 21) } (mixF fl (rolF (rolV r.ebx 21)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_893424 (p : UInt32) (G : CodeMem p 3 (codeOf [0x89, 0x34, 0x24])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.esp.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get r.esp 4 r.esi) r fl (p.add 3) ic) := by
  cbv

theorem fam_89fb (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xfb])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := r.edi } fl (p.add 2) ic) := by
  cbv

theorem fam_c1c31e (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc3, 0x1e])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (rolV r.ebx 30) } (mixF fl (rolF (rolV r.ebx 30)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_89fd (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xfd])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := r.edi } fl (p.add 2) ic) := by
  cbv

theorem fam_c1c30a (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc3, 0x0a])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (rolV r.ebx 10) } (mixF fl (rolF (rolV r.ebx 10)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_31f5 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xf5])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp ^^^ r.esi) } (logicF 4 (r.ebp ^^^ r.esi)).2 (p.add 2) ic) := by
  cbv

theorem fam_21fd (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xfd])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp &&& r.edi) } (logicF 4 (r.ebp &&& r.edi)).2 (p.add 2) ic) := by
  cbv

theorem fam_21f7 (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xf7])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (r.edi &&& r.esi) } (logicF 4 (r.edi &&& r.esi)).2 (p.add 2) ic) := by
  cbv

theorem fam_01d8 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xd8])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax + r.ebx) } (addF 4 r.eax r.ebx 0).2 (p.add 2) ic) := by
  cbv

theorem fam_014424dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x01, 0x44, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.esp d.toUInt32) 4 ((rdRaw G.get (UInt32.add r.esp d.toUInt32) 4) + r.eax)) r (addF 4 (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4) r.eax 0).2 (p.add 4) ic) := by
  cbv

theorem fam_895c94dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x89, 0x5c, 0x94, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.edx 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.edx 2)) d.toUInt32) 4 r.ebx) r fl (p.add 4) ic) := by
  cbv

theorem fam_8b4494dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x8b, 0x44, 0x94, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.edx 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.edx 2)) d.toUInt32) 4) } fl (p.add 4) ic) := by
  cbv

theorem fam_c1c319 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc3, 0x19])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (rolV r.ebx 25) } (mixF fl (rolF (rolV r.ebx 25)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_c1c50e (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc5, 0x0e])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (rolV r.ebp 14) } (mixF fl (rolF (rolV r.ebp 14)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_c1e803 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xe8, 0x03])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (shrV r.eax 3) } (shrF r.eax 3) (p.add 3) ic) := by
  cbv

theorem fam_31e8 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xe8])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax ^^^ r.ebp) } (logicF 4 (r.eax ^^^ r.ebp)).2 (p.add 2) ic) := by
  cbv

theorem fam_8d59ff (p : UInt32) (G : CodeMem p 3 (codeOf [0x8d, 0x59, 0xff])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ecx + 4294967295) } fl (p.add 3) ic) := by
  cbv

theorem fam_83e30f (p : UInt32) (G : CodeMem p 3 (codeOf [0x83, 0xe3, 0x0f])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx &&& 15) } (logicF 4 (r.ebx &&& 15)).2 (p.add 3) ic) := by
  cbv

theorem fam_8b549cdd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x8b, 0x54, 0x9c, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.ebx 2)) d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (rdRaw G.get (UInt32.add (UInt32.add r.esp (UInt32.shiftLeft r.ebx 2)) d.toUInt32) 4) } fl (p.add 4) ic) := by
  cbv

theorem fam_c1c30f (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc3, 0x0f])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (rolV r.ebx 15) } (mixF fl (rolF (rolV r.ebx 15)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_89d5 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xd5])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := r.edx } fl (p.add 2) ic) := by
  cbv

theorem fam_c1c50d (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc5, 0x0d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (rolV r.ebp 13) } (mixF fl (rolF (rolV r.ebp 13)) 2049) (p.add 3) ic) := by
  cbv

end Solutions.OpensslSha256
