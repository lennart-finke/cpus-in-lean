import Solutions.OpensslSha256.Frame
/-! Instruction families of `sha256_block_data_order` (generated): each lemma is one
encoding at a symbolic address, its effect proved by `cbv`. -/
namespace Solutions.OpensslSha256
open X86 Solutions.Logic Solutions.Exec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000
set_option Elab.async false

theorem fam_31ea (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xea])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx ^^^ r.ebp) } (logicF 4 (r.edx ^^^ r.ebp)).2 (p.add 2) ic) := by
  cbv

theorem fam_01d0 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xd0])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax + r.edx) } (addF 4 r.eax r.edx 0).2 (p.add 2) ic) := by
  cbv

theorem fam_8dac075bc25639 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8d, 0xac, 0x07, 0x5b, 0xc2, 0x56, 0x39])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := ((r.edi + (r.eax <<< 0)) + 961987163) } fl (p.add 7) ic) := by
  cbv

theorem fam_8b1424 (p : UInt32) (G : CodeMem p 3 (codeOf [0x8b, 0x14, 0x24])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.esp.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (rdRaw G.get r.esp 4) } fl (p.add 3) ic) := by
  cbv

theorem fam_21d6 (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xd6])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (r.esi &&& r.edx) } (logicF 4 (r.esi &&& r.edx)).2 (p.add 2) ic) := by
  cbv

theorem fam_21cb (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xcb])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx &&& r.ecx) } (logicF 4 (r.ebx &&& r.ecx)).2 (p.add 2) ic) := by
  cbv

theorem fam_31f3 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xf3])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx ^^^ r.esi) } (logicF 4 (r.ebx ^^^ r.esi)).2 (p.add 2) ic) := by
  cbv

theorem fam_89dd (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xdd])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := r.ebx } fl (p.add 2) ic) := by
  cbv

theorem fam_89c3 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xc3])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := r.eax } fl (p.add 2) ic) := by
  cbv

theorem fam_31f2 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xf2])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx ^^^ r.esi) } (logicF 4 (r.edx ^^^ r.esi)).2 (p.add 2) ic) := by
  cbv

theorem fam_8d9c07f111f159 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8d, 0x9c, 0x07, 0xf1, 0x11, 0xf1, 0x59])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := ((r.edi + (r.eax <<< 0)) + 1508970993) } fl (p.add 7) ic) := by
  cbv

theorem fam_31f9 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xf9])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (r.ecx ^^^ r.edi) } (logicF 4 (r.ecx ^^^ r.edi)).2 (p.add 2) ic) := by
  cbv

theorem fam_21e9 (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xe9])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (r.ecx &&& r.ebp) } (logicF 4 (r.ecx &&& r.ebp)).2 (p.add 2) ic) := by
  cbv

theorem fam_01c1 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xc1])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (r.ecx + r.eax) } (addF 4 r.ecx r.eax 0).2 (p.add 2) ic) := by
  cbv

theorem fam_8b2c24 (p : UInt32) (G : CodeMem p 3 (codeOf [0x8b, 0x2c, 0x24])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.esp.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (rdRaw G.get r.esp 4) } fl (p.add 3) ic) := by
  cbv

theorem fam_01dd (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xdd])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp + r.ebx) } (addF 4 r.ebp r.ebx 0).2 (p.add 2) ic) := by
  cbv

theorem fam_01d9 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xd9])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (r.ecx + r.ebx) } (addF 4 r.ecx r.ebx 0).2 (p.add 2) ic) := by
  cbv

theorem fam_89eb (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xeb])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := r.ebp } fl (p.add 2) ic) := by
  cbv

theorem fam_892c24 (p : UInt32) (G : CodeMem p 3 (codeOf [0x89, 0x2c, 0x24])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.esp.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get r.esp 4 r.ebp) r fl (p.add 3) ic) := by
  cbv

theorem fam_c1c307 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc3, 0x07])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (rolV r.ebx 7) } (mixF fl (rolF (rolV r.ebx 7)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_8dac03a4823f92 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8d, 0xac, 0x03, 0xa4, 0x82, 0x3f, 0x92])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := ((r.ebx + (r.eax <<< 0)) + 2453635748) } fl (p.add 7) ic) := by
  cbv

theorem fam_89f5 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xf5])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := r.esi } fl (p.add 2) ic) := by
  cbv

theorem fam_c1c507 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc5, 0x07])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (rolV r.ebp 7) } (mixF fl (rolF (rolV r.ebp 7)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_31d5 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xd5])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp ^^^ r.edx) } (logicF 4 (r.ebp ^^^ r.edx)).2 (p.add 2) ic) := by
  cbv

theorem fam_8b43dd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x8b, 0x43, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.ebx d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (rdRaw G.get (UInt32.add r.ebx d.toUInt32) 4) } fl (p.add 3) ic) := by
  cbv

end Solutions.OpensslSha256
