import Solutions.OpensslSha256.Frame
/-! Instruction families of `sha256_block_data_order` (generated): each lemma is one
encoding at a symbolic address, its effect proved by `cbv`. -/
namespace Solutions.OpensslSha256
open X86 Solutions.Logic Solutions.Exec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000
set_option Elab.async false

theorem fam_31fd (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xfd])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp ^^^ r.edi) } (logicF 4 (r.ebp ^^^ r.edi)).2 (p.add 2) ic) := by
  cbv

theorem fam_01df (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xdf])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (r.edi + r.ebx) } (addF 4 r.edi r.ebx 0).2 (p.add 2) ic) := by
  cbv

theorem fam_898c2488000000 (p : UInt32) (G : CodeMem p 7 (codeOf [0x89, 0x8c, 0x24, 0x88, 0x00, 0x00, 0x00])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (UInt32.add r.esp 136).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.esp 136) 4 r.ecx) r fl (p.add 7) ic) := by
  cbv

theorem fam_89f7 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xf7])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := r.esi } fl (p.add 2) ic) := by
  cbv

theorem fam_8d8408feb1de80 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8d, 0x84, 0x08, 0xfe, 0xb1, 0xde, 0x80])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := ((r.eax + (r.ecx <<< 0)) + 2162078206) } fl (p.add 7) ic) := by
  cbv

theorem fam_21eb (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xeb])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx &&& r.ebp) } (logicF 4 (r.ebx &&& r.ebp)).2 (p.add 2) ic) := by
  cbv

theorem fam_898c248c000000 (p : UInt32) (G : CodeMem p 7 (codeOf [0x89, 0x8c, 0x24, 0x8c, 0x00, 0x00, 0x00])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (UInt32.add r.esp 140).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.esp 140) 4 r.ecx) r fl (p.add 7) ic) := by
  cbv

theorem fam_8db408a706dc9b (p : UInt32) (G : CodeMem p 7 (codeOf [0x8d, 0xb4, 0x08, 0xa7, 0x06, 0xdc, 0x9b])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := ((r.eax + (r.ecx <<< 0)) + 2614888103) } fl (p.add 7) ic) := by
  cbv

theorem fam_c1c713 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc7, 0x13])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (rolV r.edi 19) } (mixF fl (rolF (rolV r.edi 19)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_31cf (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xcf])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (r.edi ^^^ r.ecx) } (logicF 4 (r.edi ^^^ r.ecx)).2 (p.add 2) ic) := by
  cbv

theorem fam_c1c20a (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc2, 0x0a])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (rolV r.edx 10) } (mixF fl (rolF (rolV r.edx 10)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_89ef (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xef])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := r.ebp } fl (p.add 2) ic) := by
  cbv

theorem fam_8b0424 (p : UInt32) (G : CodeMem p 3 (codeOf [0x8b, 0x04, 0x24])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.esp.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (rdRaw G.get r.esp 4) } fl (p.add 3) ic) := by
  cbv

theorem fam_21c7 (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xc7])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (r.edi &&& r.eax) } (logicF 4 (r.edi &&& r.eax)).2 (p.add 2) ic) := by
  cbv

theorem fam_01f5 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xf5])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp + r.esi) } (addF 4 r.ebp r.esi 0).2 (p.add 2) ic) := by
  cbv

theorem fam_01f1 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xf1])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (r.ecx + r.esi) } (addF 4 r.ecx r.esi 0).2 (p.add 2) ic) := by
  cbv

theorem fam_c1c607 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc6, 0x07])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (rolV r.esi 7) } (mixF fl (rolF (rolV r.esi 7)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_8b50dd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x8b, 0x50, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.eax d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (rdRaw G.get (UInt32.add r.eax d.toUInt32) 4) } fl (p.add 3) ic) := by
  cbv

theorem fam_89942490000000 (p : UInt32) (G : CodeMem p 7 (codeOf [0x89, 0x94, 0x24, 0x90, 0x00, 0x00, 0x00])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (UInt32.add r.esp 144).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.esp 144) 4 r.edx) r fl (p.add 7) ic) := by
  cbv

theorem fam_31c7 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xc7])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (r.edi ^^^ r.eax) } (logicF 4 (r.edi ^^^ r.eax)).2 (p.add 2) ic) := by
  cbv

theorem fam_01fa (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xfa])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx + r.edi) } (addF 4 r.edx r.edi 0).2 (p.add 2) ic) := by
  cbv

theorem fam_8d841674f19bc1 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8d, 0x84, 0x16, 0x74, 0xf1, 0x9b, 0xc1])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := ((r.esi + (r.edx <<< 0)) + 3248222580) } fl (p.add 7) ic) := by
  cbv

theorem fam_21ee (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xee])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (r.esi &&& r.ebp) } (logicF 4 (r.esi &&& r.ebp)).2 (p.add 2) ic) := by
  cbv

theorem fam_31ef (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xef])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (r.edi ^^^ r.ebp) } (logicF 4 (r.edi ^^^ r.ebp)).2 (p.add 2) ic) := by
  cbv

theorem fam_21cf (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xcf])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (r.edi &&& r.ecx) } (logicF 4 (r.edi &&& r.ecx)).2 (p.add 2) ic) := by
  cbv

end Solutions.OpensslSha256
