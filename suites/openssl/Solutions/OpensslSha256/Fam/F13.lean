import Solutions.OpensslSha256.Frame
/-! Instruction families of `sha256_block_data_order` (generated): each lemma is one
encoding at a symbolic address, its effect proved by `cbv`. -/
namespace Solutions.OpensslSha256
open X86 Solutions.Logic Solutions.Exec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000
set_option Elab.async false

theorem fam_31df (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xdf])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (r.edi ^^^ r.ebx) } (logicF 4 (r.edi ^^^ r.ebx)).2 (p.add 2) ic) := by
  cbv

theorem fam_8d40dd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x8d, 0x40, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax + d.toUInt32) } fl (p.add 3) ic) := by
  cbv

theorem fam_017c24dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x01, 0x7c, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.esp d.toUInt32) 4 ((rdRaw G.get (UInt32.add r.esp d.toUInt32) 4) + r.edi)) r (addF 4 (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4) r.edi 0).2 (p.add 4) ic) := by
  cbv

theorem fam_014c24dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x01, 0x4c, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.esp d.toUInt32) 4 ((rdRaw G.get (UInt32.add r.esp d.toUInt32) 4) + r.ecx)) r (addF 4 (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4) r.ecx 0).2 (p.add 4) ic) := by
  cbv

theorem fam_030c24 (p : UInt32) (G : CodeMem p 3 (codeOf [0x03, 0x0c, 0x24])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.esp.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (r.ecx + (rdRaw G.get r.esp 4)) } (addF 4 r.ecx (rdRaw G.get r.esp 4) 0).2 (p.add 3) ic) := by
  cbv

theorem fam_8bbc249c000000 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8b, 0xbc, 0x24, 0x9c, 0x00, 0x00, 0x00])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (UInt32.add r.esp 156).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (rdRaw G.get (UInt32.add r.esp 156) 4) } fl (p.add 7) ic) := by
  cbv

theorem fam_037c24dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x03, 0x7c, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (r.edi + (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4)) } (addF 4 r.edi (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4) 0).2 (p.add 4) ic) := by
  cbv

theorem fam_83c240 (p : UInt32) (G : CodeMem p 3 (codeOf [0x83, 0xc2, 0x40])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx + 64) } (addF 4 r.edx 64 0).2 (p.add 3) ic) := by
  cbv

theorem fam_8bb424a0000000 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8b, 0xb4, 0x24, 0xa0, 0x00, 0x00, 0x00])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (UInt32.add r.esp 160).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (rdRaw G.get (UInt32.add r.esp 160) 4) } fl (p.add 7) ic) := by
  cbv

theorem fam_8b842498000000 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8b, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (UInt32.add r.esp 152).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (rdRaw G.get (UInt32.add r.esp 152) 4) } fl (p.add 7) ic) := by
  cbv

theorem fam_8918 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0x18])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.eax.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get r.eax 4 r.ebx) r fl (p.add 2) ic) := by
  cbv

theorem fam_8958dd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x89, 0x58, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.eax d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.eax d.toUInt32) 4 r.ebx) r fl (p.add 3) ic) := by
  cbv

theorem fam_8948dd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x89, 0x48, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.eax d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.eax d.toUInt32) 4 r.ecx) r fl (p.add 3) ic) := by
  cbv

theorem fam_8968dd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x89, 0x68, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.eax d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.eax d.toUInt32) 4 r.ebp) r fl (p.add 3) ic) := by
  cbv

theorem fam_8978dd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x89, 0x78, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.eax d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.eax d.toUInt32) 4 r.edi) r fl (p.add 3) ic) := by
  cbv

theorem fam_81c4a8000000 (p : UInt32) (G : CodeMem p 6 (codeOf [0x81, 0xc4, 0xa8, 0x00, 0x00, 0x00])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esp := (r.esp + 168) } (addF 4 r.esp 168 0).2 (p.add 6) ic) := by
  cbv

theorem fam_83c404 (p : UInt32) (G : CodeMem p 3 (codeOf [0x83, 0xc4, 0x04])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esp := (r.esp + 4) } (addF 4 r.esp 4 0).2 (p.add 3) ic) := by
  cbv

end Solutions.OpensslSha256
