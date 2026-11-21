import Solutions.OpensslSha256.Frame
/-! Instruction families of `sha256_block_data_order` (generated): each lemma is one
encoding at a symbolic address, its effect proved by `cbv`. -/
namespace Solutions.OpensslSha256
open X86 Solutions.Logic Solutions.Exec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000
set_option Elab.async false

theorem fam_8dbc05d55e1cab (p : UInt32) (G : CodeMem p 7 (codeOf [0x8d, 0xbc, 0x05, 0xd5, 0x5e, 0x1c, 0xab])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := ((r.ebp + (r.eax <<< 0)) + 2870763221) } fl (p.add 7) ic) := by
  cbv

theorem fam_31cd (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xcd])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp ^^^ r.ecx) } (logicF 4 (r.ebp ^^^ r.ecx)).2 (p.add 2) ic) := by
  cbv

theorem fam_21f5 (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xf5])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp &&& r.esi) } (logicF 4 (r.ebp &&& r.esi)).2 (p.add 2) ic) := by
  cbv

theorem fam_01c5 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xc5])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp + r.eax) } (addF 4 r.ebp r.eax 0).2 (p.add 2) ic) := by
  cbv

theorem fam_01fd (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xfd])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp + r.edi) } (addF 4 r.ebp r.edi 0).2 (p.add 2) ic) := by
  cbv

theorem fam_8b6bdd (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x8b, 0x6b, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.ebx d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (rdRaw G.get (UInt32.add r.ebx d.toUInt32) 4) } fl (p.add 3) ic) := by
  cbv

theorem fam_0fcd (p : UInt32) (G : CodeMem p 2 (codeOf [0x0f, 0xcd])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := ((((r.ebp <<< 24) ||| ((r.ebp &&& 65280) <<< 8)) ||| ((r.ebp >>> 8) &&& 65280)) ||| (r.ebp >>> 24)) } fl (p.add 2) ic) := by
  cbv

theorem fam_8b1c24 (p : UInt32) (G : CodeMem p 3 (codeOf [0x8b, 0x1c, 0x24])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.esp.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := (rdRaw G.get r.esp 4) } fl (p.add 3) ic) := by
  cbv

theorem fam_01d5 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xd5])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp + r.edx) } (addF 4 r.ebp r.edx 0).2 (p.add 2) ic) := by
  cbv

theorem fam_8dbc2898aa07d8 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8d, 0xbc, 0x28, 0x98, 0xaa, 0x07, 0xd8])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := ((r.eax + (r.ebp <<< 0)) + 3624381080) } fl (p.add 7) ic) := by
  cbv

theorem fam_c1c21e (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc2, 0x1e])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edx := (rolV r.edx 30) } (mixF fl (rolF (rolV r.edx 30)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_c1c013 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc0, 0x13])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (rolV r.eax 19) } (mixF fl (rolF (rolV r.eax 19)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_c1c50a (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc5, 0x0a])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (rolV r.ebp 10) } (mixF fl (rolF (rolV r.ebp 10)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_31c5 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xc5])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp ^^^ r.eax) } (logicF 4 (r.ebp ^^^ r.eax)).2 (p.add 2) ic) := by
  cbv

theorem fam_89d0 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xd0])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := r.edx } fl (p.add 2) ic) := by
  cbv

theorem fam_21f0 (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xf0])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with eax := (r.eax &&& r.esi) } (logicF 4 (r.eax &&& r.esi)).2 (p.add 2) ic) := by
  cbv

theorem fam_21d9 (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xd9])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (r.ecx &&& r.ebx) } (logicF 4 (r.ecx &&& r.ebx)).2 (p.add 2) ic) := by
  cbv

theorem fam_01e9 (p : UInt32) (G : CodeMem p 2 (codeOf [0x01, 0xe9])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (r.ecx + r.ebp) } (addF 4 r.ecx r.ebp 0).2 (p.add 2) ic) := by
  cbv

theorem fam_8b6add (p : UInt32) (d : UInt8) (G : CodeMem p 3 (codeOf [0x8b, 0x6a, d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hd : d.toNat < 128) (hr : (UInt32.add r.edx d.toUInt32).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (rdRaw G.get (UInt32.add r.edx d.toUInt32) 4) } fl (p.add 3) ic) := by
  cbv

theorem fam_032c24 (p : UInt32) (G : CodeMem p 3 (codeOf [0x03, 0x2c, 0x24])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.esp.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp + (rdRaw G.get r.esp 4)) } (addF 4 r.ebp (rdRaw G.get r.esp 4) 0).2 (p.add 3) ic) := by
  cbv

theorem fam_8db428015b8312 (p : UInt32) (G : CodeMem p 7 (codeOf [0x8d, 0xb4, 0x28, 0x01, 0x5b, 0x83, 0x12])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := ((r.eax + (r.ebp <<< 0)) + 310598401) } fl (p.add 7) ic) := by
  cbv

theorem fam_89c5 (p : UInt32) (G : CodeMem p 2 (codeOf [0x89, 0xc5])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := r.eax } fl (p.add 2) ic) := by
  cbv

theorem fam_c1c513 (p : UInt32) (G : CodeMem p 3 (codeOf [0xc1, 0xc5, 0x13])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (rolV r.ebp 19) } (mixF fl (rolF (rolV r.ebp 19)) 2049) (p.add 3) ic) := by
  cbv

theorem fam_31e9 (p : UInt32) (G : CodeMem p 2 (codeOf [0x31, 0xe9])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ecx := (r.ecx ^^^ r.ebp) } (logicF 4 (r.ecx ^^^ r.ebp)).2 (p.add 2) ic) := by
  cbv

theorem fam_21d5 (p : UInt32) (G : CodeMem p 2 (codeOf [0x21, 0xd5])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := (r.ebp &&& r.edx) } (logicF 4 (r.ebp &&& r.edx)).2 (p.add 2) ic) := by
  cbv

end Solutions.OpensslSha256
