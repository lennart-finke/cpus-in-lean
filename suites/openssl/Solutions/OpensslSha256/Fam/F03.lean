import Solutions.OpensslSha256.Frame
/-! Instruction families of `sha256_block_data_order` (generated): each lemma is one
encoding at a symbolic address, its effect proved by `cbv`. -/
namespace Solutions.OpensslSha256
open X86 Solutions.Logic Solutions.Exec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000
set_option Elab.async false

theorem fam_8b47dd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x8b, 0x47, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.edi d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (rdRaw G.get (UInt32.add r.edi d.toUInt32) 4) } fl (p.add 3) ic) := by
  cbv

theorem fam_89d1 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xd1])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := r.edx } fl (p.add 2) ic) := by
  cbv

theorem fam_89d6 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xd6])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := r.edx } fl (p.add 2) ic) := by
  cbv

theorem fam_89d7 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xd7])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := r.edx } fl (p.add 2) ic) := by
  cbv

theorem fam_31d6 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xd6])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (r.esi ^^^ r.edx) } (logicF 4 (r.esi ^^^ r.edx)).2 (p.add 2) ic) := by
  cbv

theorem fam_21fe (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xfe])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (r.esi &&& r.edi) } (logicF 4 (r.esi &&& r.edi)).2 (p.add 2) ic) := by
  cbv

theorem fam_01e8 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xe8])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax + r.ebp) } (addF 4 r.eax r.ebp 0).2 (p.add 2) ic) := by
  cbv

theorem fam_8dac01cffbc0b5 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8d, 0xac, 0x01, 0xcf, 0xfb, 0xc0, 0xb5])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := ((r.ecx + (r.eax <<< 0)) + 3049323471) } fl (p.add 7) ic) := by
  cbv

theorem fam_8b3424 (p : UInt32) (G : CodeMem p 3 (codeOf [0x8b, 0x34, 0x24])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.esp.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (rdRaw G.get r.esp 4) } fl (p.add 3) ic) := by
  cbv

theorem fam_c1c113 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc1, 0x13])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (rolV r.ecx 19) } (mixF fl (rolF (rolV r.ecx 19)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_31c1 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xc1])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (r.ecx ^^^ r.eax) } (logicF 4 (r.ecx ^^^ r.eax)).2 (p.add 2) ic) := by
  cbv

theorem fam_c1c00a (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc0, 0x0a])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (rolV r.eax 10) } (mixF fl (rolF (rolV r.eax 10)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_31c8 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xc8])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax ^^^ r.ecx) } (logicF 4 (r.eax ^^^ r.ecx)).2 (p.add 2) ic) := by
  cbv

theorem fam_8b4c24dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x8b, 0x4c, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4) } fl (p.add 4) ic) := by
  cbv

theorem fam_89ca (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xca])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := r.ecx } fl (p.add 2) ic) := by
  cbv

theorem fam_89df (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xdf])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := r.ebx } fl (p.add 2) ic) := by
  cbv

theorem fam_21da (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xda])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx &&& r.ebx) } (logicF 4 (r.edx &&& r.ebx)).2 (p.add 2) ic) := by
  cbv

theorem fam_89cb (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xcb])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := r.ecx } fl (p.add 2) ic) := by
  cbv

theorem fam_31fb (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xfb])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx ^^^ r.edi) } (logicF 4 (r.ebx ^^^ r.edi)).2 (p.add 2) ic) := by
  cbv

theorem fam_21f3 (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xf3])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx &&& r.esi) } (logicF 4 (r.ebx &&& r.esi)).2 (p.add 2) ic) := by
  cbv

theorem fam_31d3 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xd3])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx ^^^ r.edx) } (logicF 4 (r.ebx ^^^ r.edx)).2 (p.add 2) ic) := by
  cbv

theorem fam_01c3 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xc3])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx + r.eax) } (addF 4 r.ebx r.eax 0).2 (p.add 2) ic) := by
  cbv

theorem fam_01eb (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xeb])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx + r.ebp) } (addF 4 r.ebx r.ebp 0).2 (p.add 2) ic) := by
  cbv

theorem fam_036c24dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x03, 0x6c, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp + (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4)) } (addF 4 r.ebp (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4) 0).2 (p.add 4) ic) := by
  cbv

theorem fam_89e8 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xe8])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := r.ebp } fl (p.add 2) ic) := by
  cbv

end Solutions.OpensslSha256
