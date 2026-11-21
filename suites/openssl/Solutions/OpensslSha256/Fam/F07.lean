import Solutions.OpensslSha256.Frame
/-! Instruction families of `sha256_block_data_order` (generated): each lemma is one
encoding at a symbolic address, its effect proved by `cbv`. -/
namespace Solutions.OpensslSha256
open X86 Solutions.Logic Solutions.Exec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000
set_option Elab.async false

theorem fam_21c3 (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xc3])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx &&& r.eax) } (logicF 4 (r.ebx &&& r.eax)).2 (p.add 2) ic) := by
  cbv

theorem fam_31eb (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xeb])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx ^^^ r.ebp) } (logicF 4 (r.ebx ^^^ r.ebp)).2 (p.add 2) ic) := by
  cbv

theorem fam_01cb (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xcb])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx + r.ecx) } (addF 4 r.ebx r.ecx 0).2 (p.add 2) ic) := by
  cbv

theorem fam_01f7 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xf7])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (r.edi + r.esi) } (addF 4 r.edi r.esi 0).2 (p.add 2) ic) := by
  cbv

theorem fam_01f3 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xf3])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx + r.esi) } (addF 4 r.ebx r.esi 0).2 (p.add 2) ic) := by
  cbv

theorem fam_8b51dd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x8b, 0x51, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.ecx d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (rdRaw G.get (UInt32.add r.ecx d.toUInt32) 4) } fl (p.add 3) ic) := by
  cbv

theorem fam_21f9 (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xf9])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (r.ecx &&& r.edi) } (logicF 4 (r.ecx &&& r.edi)).2 (p.add 2) ic) := by
  cbv

theorem fam_8dac10be853124 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8d, 0xac, 0x10, 0xbe, 0x85, 0x31, 0x24])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := ((r.eax + (r.edx <<< 0)) + 607225278) } fl (p.add 7) ic) := by
  cbv

theorem fam_89d9 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xd9])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := r.ebx } fl (p.add 2) ic) := by
  cbv

theorem fam_89d3 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xd3])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := r.edx } fl (p.add 2) ic) := by
  cbv

theorem fam_31c3 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xc3])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx ^^^ r.eax) } (logicF 4 (r.ebx ^^^ r.eax)).2 (p.add 2) ic) := by
  cbv

theorem fam_21fb (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xfb])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (r.ebx &&& r.edi) } (logicF 4 (r.ebx &&& r.edi)).2 (p.add 2) ic) := by
  cbv

theorem fam_01ea (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xea])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx + r.ebp) } (addF 4 r.edx r.ebp 0).2 (p.add 2) ic) := by
  cbv

theorem fam_c1c115 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc1, 0x15])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (rolV r.ecx 21) } (mixF fl (rolF (rolV r.ecx 21)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_8b49dd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x8b, 0x49, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.ecx d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (rdRaw G.get (UInt32.add r.ecx d.toUInt32) 4) } fl (p.add 3) ic) := by
  cbv

theorem fam_0fc9 (p : UInt32) (G : CodeMem p 2 (codeOf [0x0f, 0xc9])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := ((((r.ecx <<< 24) ||| ((r.ecx &&& 65280) <<< 8)) ||| ((r.ecx >>> 8) &&& 65280)) ||| (r.ecx >>> 24)) } fl (p.add 2) ic) := by
  cbv

theorem fam_898c2480000000 (p : UInt32) (G : CodeMem p 7 (codeOf [0x89, 0x8c, 0x24, 0x80, 0x00, 0x00, 0x00])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (UInt32.add r.esp 128).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.esp 128) 4 r.ecx) r fl (p.add 7) ic) := by
  cbv

theorem fam_034c24dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x03, 0x4c, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (r.ecx + (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4)) } (addF 4 r.ecx (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4) 0).2 (p.add 4) ic) := by
  cbv

theorem fam_8dbc08c37d0c55 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8d, 0xbc, 0x08, 0xc3, 0x7d, 0x0c, 0x55])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := ((r.eax + (r.ecx <<< 0)) + 1426881987) } fl (p.add 7) ic) := by
  cbv

theorem fam_31dd (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xdd])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp ^^^ r.ebx) } (logicF 4 (r.ebp ^^^ r.ebx)).2 (p.add 2) ic) := by
  cbv

theorem fam_21c5 (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xc5])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp &&& r.eax) } (logicF 4 (r.ebp &&& r.eax)).2 (p.add 2) ic) := by
  cbv

theorem fam_01cd (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xcd])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp + r.ecx) } (addF 4 r.ebp r.ecx 0).2 (p.add 2) ic) := by
  cbv

theorem fam_898c2484000000 (p : UInt32) (G : CodeMem p 7 (codeOf [0x89, 0x8c, 0x24, 0x84, 0x00, 0x00, 0x00])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (UInt32.add r.esp 132).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.esp 132) 4 r.ecx) r fl (p.add 7) ic) := by
  cbv

theorem fam_31fa (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xfa])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx ^^^ r.edi) } (logicF 4 (r.edx ^^^ r.edi)).2 (p.add 2) ic) := by
  cbv

theorem fam_8d9c08745dbe72 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8d, 0x9c, 0x08, 0x74, 0x5d, 0xbe, 0x72])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := ((r.eax + (r.ecx <<< 0)) + 1925078388) } fl (p.add 7) ic) := by
  cbv

end Solutions.OpensslSha256
