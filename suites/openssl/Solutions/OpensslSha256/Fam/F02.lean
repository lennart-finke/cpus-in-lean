import Solutions.OpensslSha256.Frame
/-! Instruction families of `sha256_block_data_order` (generated): each lemma is one
encoding at a symbolic address, its effect proved by `cbv`. -/
namespace Solutions.OpensslSha256
open X86 Solutions.Logic Solutions.Exec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000
set_option Elab.async false

theorem fam_31d0 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xd0])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax ^^^ r.edx) } (logicF 4 (r.eax ^^^ r.edx)).2 (p.add 2) ic) := by
  cbv

theorem fam_01c8 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xc8])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax + r.ecx) } (addF 4 r.eax r.ecx 0).2 (p.add 2) ic) := by
  cbv

theorem fam_01f0 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xf0])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax + r.esi) } (addF 4 r.eax r.esi 0).2 (p.add 2) ic) := by
  cbv

theorem fam_037424dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x03, 0x74, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (r.esi + (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4)) } (addF 4 r.esi (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4) 0).2 (p.add 4) ic) := by
  cbv

theorem fam_8b57dd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x8b, 0x57, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.edi d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (rdRaw G.get (UInt32.add r.edi d.toUInt32) 4) } fl (p.add 3) ic) := by
  cbv

theorem fam_0fca (p : UInt32) (G : CodeMem p 2 (codeOf [0x0f, 0xca])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := ((((r.edx <<< 24) ||| ((r.edx &&& 65280) <<< 8)) ||| ((r.edx >>> 8) &&& 65280)) ||| (r.edx >>> 24)) } fl (p.add 2) ic) := by
  cbv

theorem fam_89f1 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xf1])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := r.esi } fl (p.add 2) ic) := by
  cbv

theorem fam_c1c615 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc6, 0x15])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (rolV r.esi 21) } (mixF fl (rolF (rolV r.esi 21)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_31ce (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xce])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (r.esi ^^^ r.ecx) } (logicF 4 (r.esi ^^^ r.ecx)).2 (p.add 2) ic) := by
  cbv

theorem fam_31f1 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xf1])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (r.ecx ^^^ r.esi) } (logicF 4 (r.ecx ^^^ r.esi)).2 (p.add 2) ic) := by
  cbv

theorem fam_89ee (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xee])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := r.ebp } fl (p.add 2) ic) := by
  cbv

theorem fam_8b6c24dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x8b, 0x6c, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4) } fl (p.add 4) ic) := by
  cbv

theorem fam_31ee (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xee])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (r.esi ^^^ r.ebp) } (logicF 4 (r.esi ^^^ r.ebp)).2 (p.add 2) ic) := by
  cbv

theorem fam_21c6 (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xc6])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (r.esi &&& r.eax) } (logicF 4 (r.esi &&& r.eax)).2 (p.add 2) ic) := by
  cbv

theorem fam_01ce (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xce])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (r.esi + r.ecx) } (addF 4 r.esi r.ecx 0).2 (p.add 2) ic) := by
  cbv

theorem fam_8d843291443771 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8d, 0x84, 0x32, 0x91, 0x44, 0x37, 0x71])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := ((r.edx + (r.esi <<< 0)) + 1899447441) } fl (p.add 7) ic) := by
  cbv

theorem fam_c1c11e (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc1, 0x1e])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (rolV r.ecx 30) } (mixF fl (rolF (rolV r.ecx 30)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_89da (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xda])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := r.ebx } fl (p.add 2) ic) := by
  cbv

theorem fam_21f2 (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xf2])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx &&& r.esi) } (logicF 4 (r.edx &&& r.esi)).2 (p.add 2) ic) := by
  cbv

theorem fam_331424 (p : UInt32) (G : CodeMem p 3 (codeOf [0x33, 0x14, 0x24])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.esp.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx ^^^ (rdRaw G.get r.esp 4)) } (logicF 4 (r.edx ^^^ (rdRaw G.get r.esp 4))).2 (p.add 3) ic) := by
  cbv

theorem fam_01ca (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xca])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx + r.ecx) } (addF 4 r.edx r.ecx 0).2 (p.add 2) ic) := by
  cbv

theorem fam_01c2 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xc2])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx + r.eax) } (addF 4 r.edx r.eax 0).2 (p.add 2) ic) := by
  cbv

theorem fam_891424 (p : UInt32) (G : CodeMem p 3 (codeOf [0x89, 0x14, 0x24])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.esp.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get r.esp 4 r.edx) r fl (p.add 3) ic) := by
  cbv

theorem fam_89c2 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xc2])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := r.eax } fl (p.add 2) ic) := by
  cbv

theorem fam_035424dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x03, 0x54, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx + (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4)) } (addF 4 r.edx (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4) 0).2 (p.add 4) ic) := by
  cbv

end Solutions.OpensslSha256
