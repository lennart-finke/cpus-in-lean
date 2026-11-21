import Solutions.OpensslSha256.Frame
/-! Instruction families of `sha256_block_data_order` (generated): each lemma is one
encoding at a symbolic address, its effect proved by `cbv`. -/
namespace Solutions.OpensslSha256
open X86 Solutions.Logic Solutions.Exec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000
set_option Elab.async false

theorem fam_c1c01a (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc0, 0x1a])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (rolV r.eax 26) } (mixF fl (rolF (rolV r.eax 26)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_31c6 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xc6])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (r.esi ^^^ r.eax) } (logicF 4 (r.esi ^^^ r.eax)).2 (p.add 2) ic) := by
  cbv

theorem fam_c1c007 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc0, 0x07])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (rolV r.eax 7) } (mixF fl (rolF (rolV r.eax 7)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_31f0 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xf0])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax ^^^ r.esi) } (logicF 4 (r.eax ^^^ r.esi)).2 (p.add 2) ic) := by
  cbv

theorem fam_8b72dd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x8b, 0x72, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.edx d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (rdRaw G.get (UInt32.add r.edx d.toUInt32) 4) } fl (p.add 3) ic) := by
  cbv

theorem fam_0fce (p : UInt32) (G : CodeMem p 2 (codeOf [0x0f, 0xce])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := ((((r.esi <<< 24) ||| ((r.esi &&& 65280) <<< 8)) ||| ((r.esi >>> 8) &&& 65280)) ||| (r.esi >>> 24)) } fl (p.add 2) ic) := by
  cbv

theorem fam_31d7 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xd7])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (r.edi ^^^ r.edx) } (logicF 4 (r.edi ^^^ r.edx)).2 (p.add 2) ic) := by
  cbv

theorem fam_21ef (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xef])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (r.edi &&& r.ebp) } (logicF 4 (r.edi &&& r.ebp)).2 (p.add 2) ic) := by
  cbv

theorem fam_01fe (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xfe])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (r.esi + r.edi) } (addF 4 r.esi r.edi 0).2 (p.add 2) ic) := by
  cbv

theorem fam_8d0c06 (p : UInt32) (G : CodeMem p 3 (codeOf [0x8d, 0x0c, 0x06])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (r.esi + (r.eax <<< 0)) } fl (p.add 3) ic) := by
  cbv

theorem fam_894c24dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x89, 0x4c, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.esp d.toUInt32) 4 r.ecx) r fl (p.add 4) ic) := by
  cbv

theorem fam_8dac30a5dbb5e9 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8d, 0xac, 0x30, 0xa5, 0xdb, 0xb5, 0xe9])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := ((r.eax + (r.esi <<< 0)) + 3921009573) } fl (p.add 7) ic) := by
  cbv

theorem fam_89de (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xde])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := r.ebx } fl (p.add 2) ic) := by
  cbv

theorem fam_c1c613 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc6, 0x13])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (rolV r.esi 19) } (mixF fl (rolF (rolV r.esi 19)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_21ca (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xca])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx &&& r.ecx) } (logicF 4 (r.edx &&& r.ecx)).2 (p.add 2) ic) := by
  cbv

theorem fam_21de (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xde])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (r.esi &&& r.ebx) } (logicF 4 (r.esi &&& r.ebx)).2 (p.add 2) ic) := by
  cbv

theorem fam_01c6 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xc6])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (r.esi + r.eax) } (addF 4 r.esi r.eax 0).2 (p.add 2) ic) := by
  cbv

theorem fam_01ee (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xee])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (r.esi + r.ebp) } (addF 4 r.esi r.ebp 0).2 (p.add 2) ic) := by
  cbv

theorem fam_8b4424dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x8b, 0x44, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4) } fl (p.add 4) ic) := by
  cbv

theorem fam_8d8c08a5dbb5e9 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8d, 0x8c, 0x08, 0xa5, 0xdb, 0xb5, 0xe9])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := ((r.eax + (r.ecx <<< 0)) + 3921009573) } fl (p.add 7) ic) := by
  cbv

theorem fam_89c8 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xc8])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := r.ecx } fl (p.add 2) ic) := by
  cbv

theorem fam_89cf (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xcf])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := r.ecx } fl (p.add 2) ic) := by
  cbv

theorem fam_c1c707 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc7, 0x07])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (rolV r.edi 7) } (mixF fl (rolF (rolV r.edi 7)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_8b40dd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x8b, 0x40, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.eax d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (rdRaw G.get (UInt32.add r.eax d.toUInt32) 4) } fl (p.add 3) ic) := by
  cbv

theorem fam_034424dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x03, 0x44, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax + (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4)) } (addF 4 r.eax (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4) 0).2 (p.add 4) ic) := by
  cbv

end Solutions.OpensslSha256
