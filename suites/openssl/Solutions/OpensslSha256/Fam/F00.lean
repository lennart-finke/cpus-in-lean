import Solutions.OpensslSha256.Frame
/-! Instruction families of `sha256_block_data_order` (generated): each lemma is one
encoding at a symbolic address, its effect proved by `cbv`. -/
namespace Solutions.OpensslSha256
open X86 Solutions.Logic Solutions.Exec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000
set_option Elab.async false

theorem fam_81eca8000000 (p : UInt32) (G : CodeMem p 6 (codeOf [0x81, 0xec, 0xa8, 0x00, 0x00, 0x00])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esp := (r.esp - 168) } (subF 4 r.esp 168 0).2 (p.add 6) ic) := by
  cbv

theorem fam_8bb424bc000000 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8b, 0xb4, 0x24, 0xbc, 0x00, 0x00, 0x00])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (UInt32.add r.esp 188).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := (rdRaw G.get (UInt32.add r.esp 188) 4) } fl (p.add 7) ic) := by
  cbv

theorem fam_8b01 (p : UInt32) (G : CodeMem p 2 (codeOf [0x8b, 0x01])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.ecx.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (rdRaw G.get r.ecx 4) } fl (p.add 2) ic) := by
  cbv

theorem fam_894424dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x89, 0x44, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.esp d.toUInt32) 4 r.eax) r fl (p.add 4) ic) := by
  cbv

theorem fam_8b41dd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x8b, 0x41, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.ecx d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (rdRaw G.get (UInt32.add r.ecx d.toUInt32) 4) } fl (p.add 3) ic) := by
  cbv

theorem fam_8b79dd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x8b, 0x79, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.ecx d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := (rdRaw G.get (UInt32.add r.ecx d.toUInt32) 4) } fl (p.add 3) ic) := by
  cbv

theorem fam_897c24dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x89, 0x7c, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.esp d.toUInt32) 4 r.edi) r fl (p.add 4) ic) := by
  cbv

theorem fam_8b59dd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x8b, 0x59, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.ecx d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (rdRaw G.get (UInt32.add r.ecx d.toUInt32) 4) } fl (p.add 3) ic) := by
  cbv

theorem fam_898c2498000000 (p : UInt32) (G : CodeMem p 7 (codeOf [0x89, 0x8c, 0x24, 0x98, 0x00, 0x00, 0x00])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (UInt32.add r.esp 152).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.esp 152) 4 r.ecx) r fl (p.add 7) ic) := by
  cbv

theorem fam_89c1 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xc1])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := r.eax } fl (p.add 2) ic) := by
  cbv

theorem fam_90 (p : UInt32) (G : CodeMem p 1 (codeOf [0x90])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get r fl (p.add 1) ic) := by
  cbv

theorem fam_895424dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x89, 0x54, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.esp d.toUInt32) 4 r.edx) r fl (p.add 4) ic) := by
  cbv

theorem fam_895c24dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x89, 0x5c, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.esp d.toUInt32) 4 r.ebx) r fl (p.add 4) ic) := by
  cbv

theorem fam_89b424a0000000 (p : UInt32) (G : CodeMem p 7 (codeOf [0x89, 0xb4, 0x24, 0xa0, 0x00, 0x00, 0x00])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (UInt32.add r.esp 160).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (UInt32.add r.esp 160) 4 r.esi) r fl (p.add 7) ic) := by
  cbv

theorem fam_8b02 (p : UInt32) (G : CodeMem p 2 (codeOf [0x8b, 0x02])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.edx.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (rdRaw G.get r.edx 4) } fl (p.add 2) ic) := by
  cbv

theorem fam_0fc8 (p : UInt32) (G : CodeMem p 2 (codeOf [0x0f, 0xc8])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := ((((r.eax <<< 24) ||| ((r.eax &&& 65280) <<< 8)) ||| ((r.eax >>> 8) &&& 65280)) ||| (r.eax >>> 24)) } fl (p.add 2) ic) := by
  cbv

theorem fam_89cd (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xcd])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := r.ecx } fl (p.add 2) ic) := by
  cbv

theorem fam_c1c11a (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc1, 0x1a])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (rolV r.ecx 26) } (mixF fl (rolF (rolV r.ecx 26)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_89ea (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xea])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := r.ebp } fl (p.add 2) ic) := by
  cbv

theorem fam_c1c215 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc2, 0x15])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (rolV r.edx 21) } (mixF fl (rolF (rolV r.edx 21)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_31ca (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xca])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (r.edx ^^^ r.ecx) } (logicF 4 (r.edx ^^^ r.ecx)).2 (p.add 2) ic) := by
  cbv

theorem fam_89e9 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xe9])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := r.ebp } fl (p.add 2) ic) := by
  cbv

theorem fam_c1c107 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc1, 0x07])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (rolV r.ecx 7) } (mixF fl (rolF (rolV r.ecx 7)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_31d1 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xd1])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (r.ecx ^^^ r.edx) } (logicF 4 (r.ecx ^^^ r.edx)).2 (p.add 2) ic) := by
  cbv

theorem fam_8b5424dd (p : UInt32) (d : UInt8) (G : CodeMem p 4 (codeOf [0x8b, 0x54, 0x24, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.esp d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (rdRaw G.get (UInt32.add r.esp d.toUInt32) 4) } fl (p.add 4) ic) := by
  cbv

end Solutions.OpensslSha256
