import Solutions.OpensslSha256.Frame
/-! Instruction families of `sha256_block_data_order` (generated): each lemma is one
encoding at a symbolic address, its effect proved by `cbv`. -/
namespace Solutions.OpensslSha256
open X86 Solutions.Logic Solutions.Exec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000
set_option Elab.async false

theorem fam_31da (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xda])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx ^^^ r.ebx) } (logicF 4 (r.edx ^^^ r.ebx)).2 (p.add 2) ic) := by
  cbv

theorem fam_21ea (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xea])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx &&& r.ebp) } (logicF 4 (r.edx &&& r.ebp)).2 (p.add 2) ic) := by
  cbv

theorem fam_896c24dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x89, 0x6c, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.esp d.toUInt32) 4 r.ebp) r fl (p.add 4) ic) := by
  cbv

theorem fam_89bc249c000000 (p : UInt32) (G : CodeMem p 7 (codeOf [0x89, 0xbc, 0x24, 0x9c, 0x00, 0x00, 0x00])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (UInt32.add r.esp 156).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.esp 156) 4 r.edi) r fl (p.add 7) ic) := by
  cbv

theorem fam_01f9 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xf9])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (r.ecx + r.edi) } (addF 4 r.ecx r.edi 0).2 (p.add 2) ic) := by
  cbv

theorem fam_01d1 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xd1])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (r.ecx + r.edx) } (addF 4 r.ecx r.edx 0).2 (p.add 2) ic) := by
  cbv

theorem fam_8b7424dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x8b, 0x74, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4) } fl (p.add 4) ic) := by
  cbv

theorem fam_8d8408982f8a42 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8d, 0x84, 0x08, 0x98, 0x2f, 0x8a, 0x42])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := ((r.eax + (r.ecx <<< 0)) + 1116352408) } fl (p.add 7) ic) := by
  cbv

theorem fam_8b7c24dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x8b, 0x7c, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4) } fl (p.add 4) ic) := by
  cbv

theorem fam_89f8 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xf8])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := r.edi } fl (p.add 2) ic) := by
  cbv

theorem fam_c1c01e (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc0, 0x1e])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (rolV r.eax 30) } (mixF fl (rolF (rolV r.eax 30)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_89fa (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xfa])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := r.edi } fl (p.add 2) ic) := by
  cbv

theorem fam_c1c213 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc2, 0x13])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (rolV r.edx 19) } (mixF fl (rolF (rolV r.edx 19)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_31c2 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xc2])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx ^^^ r.eax) } (logicF 4 (r.edx ^^^ r.eax)).2 (p.add 2) ic) := by
  cbv

theorem fam_89f9 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xf9])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := r.edi } fl (p.add 2) ic) := by
  cbv

theorem fam_c1c10a (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc1, 0x0a])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (rolV r.ecx 10) } (mixF fl (rolF (rolV r.ecx 10)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_8b5c24dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x8b, 0x5c, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4) } fl (p.add 4) ic) := by
  cbv

theorem fam_89d8 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xd8])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := r.ebx } fl (p.add 2) ic) := by
  cbv

theorem fam_21f8 (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xf8])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax &&& r.edi) } (logicF 4 (r.eax &&& r.edi)).2 (p.add 2) ic) := by
  cbv

theorem fam_890424 (p : UInt32) (G : CodeMem p 3 (codeOf [0x89, 0x04, 0x24])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.esp.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get r.esp 4 r.eax) r fl (p.add 3) ic) := by
  cbv

theorem fam_897424dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x89, 0x74, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.esp d.toUInt32) 4 r.esi) r fl (p.add 4) ic) := by
  cbv

theorem fam_89f2 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xf2])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := r.esi } fl (p.add 2) ic) := by
  cbv

theorem fam_21fa (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xfa])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx &&& r.edi) } (logicF 4 (r.edx &&& r.edi)).2 (p.add 2) ic) := by
  cbv

theorem fam_89f0 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xf0])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := r.esi } fl (p.add 2) ic) := by
  cbv

theorem fam_21d8 (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xd8])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax &&& r.ebx) } (logicF 4 (r.eax &&& r.ebx)).2 (p.add 2) ic) := by
  cbv

end Solutions.OpensslSha256
