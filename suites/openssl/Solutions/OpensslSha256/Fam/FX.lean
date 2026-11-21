import Solutions.OpensslSha256.Frame
/-! The stack and control-flow instructions of `SHA256_Transform` and the block function: pushes,
pops, the call and the returns, and the two branches at the flag words they meet. -/
namespace Solutions.OpensslSha256
open X86 Solutions.Logic Solutions.Exec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000
set_option Elab.async false

theorem execOp0F_x182 : execOp0F 386 = execRange 386 := by unfold execOp0F; rfl
theorem execOp0F_x185 : execOp0F 389 = execRange 389 := by unfold execOp0F; rfl

theorem efl_mix_zf (f v : UInt32) : UInt32.land (efl (mixF f v 2260)) 64 = UInt32.land v 64 := by
  show (2 ||| ((f &&& ~~~2260) ||| (v &&& 2260)) &&& 0x8D5) &&& 64 = v &&& 64
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, UInt32.toBitVec_not, BitVec.getLsbD_and,
    BitVec.getLsbD_or, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  have h64 : ∀ j, j < 32 → (UInt32.toBitVec 64).getLsbD j = decide (j = 6) := by decide
  rw [h64 i hi]
  by_cases h6 : i = 6
  · subst h6
    have : (UInt32.toBitVec 2).getLsbD 6 = false := by decide
    have : (UInt32.toBitVec 2260).getLsbD 6 = true := by decide
    have : (UInt32.toBitVec 0x8D5).getLsbD 6 = true := by decide
    simp_all
  · simp [h6]

attribute [local cbv_eval] execOp0F_x182 execOp0F_x185 efl_mix_zf

theorem famPUSH_ebp (p : UInt32) (G : CodeMem p 1 (codeOf [0x55])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (r.esp - 4).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (r.esp - 4) 4 r.ebp) { r with esp := r.esp - 4 } fl (p.add 1) ic) := by
  cbv

theorem famPUSH_ebx (p : UInt32) (G : CodeMem p 1 (codeOf [0x53])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (r.esp - 4).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (r.esp - 4) 4 r.ebx) { r with esp := r.esp - 4 } fl (p.add 1) ic) := by
  cbv

theorem famPUSH_edi (p : UInt32) (G : CodeMem p 1 (codeOf [0x57])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (r.esp - 4).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (r.esp - 4) 4 r.edi) { r with esp := r.esp - 4 } fl (p.add 1) ic) := by
  cbv

theorem famPUSH_esi (p : UInt32) (G : CodeMem p 1 (codeOf [0x56])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (r.esp - 4).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (r.esp - 4) 4 r.esi) { r with esp := r.esp - 4 } fl (p.add 1) ic) := by
  cbv

theorem famPUSHI (p : UInt32) (G : CodeMem p 2 (codeOf [0x6a, 0x01])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : (r.esp - 4).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc (wrBytes G.get (r.esp - 4) 4 1) { r with esp := r.esp - 4 } fl (p.add 2) ic) := by
  cbv

theorem famPOP_esi (p : UInt32) (G : CodeMem p 1 (codeOf [0x5e])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.esp.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := rdRaw G.get r.esp 4, esp := r.esp + 4 } fl (p.add 1) ic) := by
  cbv

theorem famPOP_edi (p : UInt32) (G : CodeMem p 1 (codeOf [0x5f])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.esp.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with edi := rdRaw G.get r.esp 4, esp := r.esp + 4 } fl (p.add 1) ic) := by
  cbv

theorem famPOP_ebx (p : UInt32) (G : CodeMem p 1 (codeOf [0x5b])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.esp.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebx := rdRaw G.get r.esp 4, esp := r.esp + 4 } fl (p.add 1) ic) := by
  cbv

theorem famPOP_ebp (p : UInt32) (G : CodeMem p 1 (codeOf [0x5d])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.esp.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with ebp := rdRaw G.get r.esp 4, esp := r.esp + 4 } fl (p.add 1) ic) := by
  cbv

theorem famRET (p : UInt32) (G : CodeMem p 1 (codeOf [0xc3])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) (hr : r.esp.toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esp := r.esp + 4 } fl (rdRaw G.get r.esp 4) ic) := by
  cbv

theorem famCMP (p : UInt32) (G : CodeMem p 3 (codeOf [0x83, 0xf8, 0x38])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) = some (conc G.get r (subF 4 r.eax 56 0).2 (p.add 3) ic) := by
  cbv

theorem famDEC (p : UInt32) (G : CodeMem p 1 (codeOf [0x4e])) (r : R) (fl : UInt32) (ic : UInt64)
    (hp : p.toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r fl p ic)) =
      some (conc G.get { r with esi := r.esi - 1 } (mixF fl (subF 4 r.esi 1 0).2 2260) (p.add 1) ic) := by
  cbv

theorem famJNE (G : CodeMem 0x101190 6 (codeOf [0x0f, 0x85, 0xfa, 0xf1, 0xff, 0xff])) (r : R) (fl : UInt32)
    (ic : UInt64) (hp : (0x101190 : UInt32).toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r (mixF fl (subF 4 1 1 0).2 2260) 0x101190 ic)) =
      some (conc G.get r (mixF fl (subF 4 1 1 0).2 2260) 0x101196 ic) := by
  cbv

theorem famCALL (G : CodeMem 0x1011ba 5 (codeOf [0xe8, 0x81, 0xf1, 0xff, 0xff])) (r : R) (fl : UInt32)
    (ic : UInt64) (hp : (0x1011ba : UInt32).toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop)
    (hr : (r.esp - 4).toNat + 4 ≤ G.get.size) :
    okState (execInstr (conc G.get r fl 0x1011ba ic)) =
      some (conc (wrBytes G.get (r.esp - 4) 4 0x1011bf) { r with esp := r.esp - 4 } fl 0x100340 ic) := by
  cbv

theorem famJB_16 (G : CodeMem 0x1010ff 6 (codeOf [0x0f, 0x82, 0xeb, 0xf9, 0xff, 0xff])) (r : R) (ic : UInt64)
    (hp : (0x1010ff : UInt32).toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r (subF 4 16 56 0).2 0x1010ff ic)) =
      some (conc G.get r (subF 4 16 56 0).2 0x100af0 ic) := by
  cbv

theorem famJB_24 (G : CodeMem 0x1010ff 6 (codeOf [0x0f, 0x82, 0xeb, 0xf9, 0xff, 0xff])) (r : R) (ic : UInt64)
    (hp : (0x1010ff : UInt32).toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r (subF 4 24 56 0).2 0x1010ff ic)) =
      some (conc G.get r (subF 4 24 56 0).2 0x100af0 ic) := by
  cbv

theorem famJB_32 (G : CodeMem 0x1010ff 6 (codeOf [0x0f, 0x82, 0xeb, 0xf9, 0xff, 0xff])) (r : R) (ic : UInt64)
    (hp : (0x1010ff : UInt32).toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r (subF 4 32 56 0).2 0x1010ff ic)) =
      some (conc G.get r (subF 4 32 56 0).2 0x100af0 ic) := by
  cbv

theorem famJB_40 (G : CodeMem 0x1010ff 6 (codeOf [0x0f, 0x82, 0xeb, 0xf9, 0xff, 0xff])) (r : R) (ic : UInt64)
    (hp : (0x1010ff : UInt32).toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r (subF 4 40 56 0).2 0x1010ff ic)) =
      some (conc G.get r (subF 4 40 56 0).2 0x100af0 ic) := by
  cbv

theorem famJB_48 (G : CodeMem 0x1010ff 6 (codeOf [0x0f, 0x82, 0xeb, 0xf9, 0xff, 0xff])) (r : R) (ic : UInt64)
    (hp : (0x1010ff : UInt32).toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r (subF 4 48 56 0).2 0x1010ff ic)) =
      some (conc G.get r (subF 4 48 56 0).2 0x100af0 ic) := by
  cbv

theorem famJB_56 (G : CodeMem 0x1010ff 6 (codeOf [0x0f, 0x82, 0xeb, 0xf9, 0xff, 0xff])) (r : R) (ic : UInt64)
    (hp : (0x1010ff : UInt32).toNat + 16 ≤ ramTop) (hsz : G.get.size ≤ ramTop) :
    okState (execInstr (conc G.get r (subF 4 56 56 0).2 0x1010ff ic)) =
      some (conc G.get r (subF 4 56 56 0).2 0x101105 ic) := by
  cbv

end Solutions.OpensslSha256
