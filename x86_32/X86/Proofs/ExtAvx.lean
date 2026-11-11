import X86.Dispatch
import X86.Proofs.Basic
/-!
# AVX (`X86/Ext/Vex.lean`, `X86/Ext/Avx.lean`)

* Checks: `vexCheck_noosxsave`, `vexCheck_xcr0` (#UD without CR4.OSXSAVE or XCR0[2:1] = 11b),
  `vexCheck_ts` (#NM with CR0.TS), all before touching any state (the machine is returned unchanged);
  `vexCheck_em` (CR0.EM does not matter); `start_enc` (an encoding violation is #UD first).
* Zeroing: `setV_vex128` (every VEX.128 destination write zeroes bits 255:128 of the register and
  leaves the other registers alone), `setV_vex256`; `setXmm_ymmh` (legacy SSE writes preserve bits
  255:128 of every register).
* VZEROUPPER/VZEROALL: `vzeroupper`, `vzeroall` (their effect, through the hook `Avx.vex?`).
* VMASKMOVPS/PD: `maskStore_none` (with no element selected the store changes nothing and raises
  nothing, whatever memory is mapped), `maskLoad_none` (the load writes zeros without accessing
  memory), `maskSel_zero`.
* Extension point: `vex?_int256` (VEX.256 of the 0F-map integer opcodes is left to `Avx2.vex?`).
-/
namespace X86
open Vex

/-! ## Checks -/

theorem vexCheck_noosxsave {m : Machine} {i : Inst} (h : m.cpu.cr4 &&& CR4.OSXSAVE = 0) :
    vexCheck i m = .error (.exc Vec.UD none 0) m := by
  simp [vexCheck, avxEnabled, cpu, h, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

theorem vexCheck_xcr0 {m : Machine} {i : Inst} (h : m.cpu.xcr0 &&& (XCR0.SSE ||| XCR0.YMM) ≠ XCR0.SSE ||| XCR0.YMM) :
    vexCheck i m = .error (.exc Vec.UD none 0) m := by
  simp [vexCheck, avxEnabled, cpu, h, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

theorem vexCheck_ts {m : Machine} {i : Inst} (hen : avxEnabled m.cpu = true) (h : m.cpu.cr0 &&& CR0.TS ≠ 0) :
    vexCheck i m = .error (.exc Vec.NM none 0) m := by
  simp [vexCheck, cpu, hen, h, bind, EStateM.bind, exc, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

/-- With AVX enabled and CR0.TS clear the checks pass without changing the state, whatever CR0.EM
and CR4.OSFXSR say. -/
theorem vexCheck_em {m : Machine} {i : Inst} (hen : avxEnabled m.cpu = true) (h : m.cpu.cr0 &&& CR0.TS = 0) :
    vexCheck i m = .ok () m := by
  simp [vexCheck, cpu, hen, h, bind, EStateM.bind, pure, EStateM.pure]

theorem start_enc {m : Machine} {i : Inst} : start i false m = .error (.exc Vec.UD none 0) m := by
  simp [start, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

theorem start_ok {m : Machine} {i : Inst} (hen : avxEnabled m.cpu = true) (h : m.cpu.cr0 &&& CR0.TS = 0) :
    start i true m = .ok () m := by
  simp [start, vexCheck, cpu, hen, h, bind, EStateM.bind, pure, EStateM.pure]

/-! ## Bits 255:128 -/

/-- A VEX.128 destination write: XMMr gets bits 127:0 of the value, bits 255:128 of YMMr become 0. -/
theorem setV_vex128 (i : Inst) (hL : i.vexL = false) (r : UInt8) (v : V256) (m : Machine) :
    ∃ m', setV i r v m = .ok () m' ∧ m'.cpu.xmm = m.cpu.xmm.set! (r &&& 7).toNat v.lo ∧
      m'.cpu.ymmh = m.cpu.ymmh.set! (r &&& 7).toNat {} := by
  refine ⟨_, rfl, ?_, ?_⟩ <;> simp [setV, setY, hL, V256.ofLo, Cpu.xmm, Cpu.ymmh]

theorem setV_vex128_upper (i : Inst) (hL : i.vexL = false) (r : UInt8) (v : V256) (m : Machine)
    (hs : (r &&& 7).toNat < m.cpu.ymmh.size) :
    ∃ m', setV i r v m = .ok () m' ∧ m'.cpu.ymmh[(r &&& 7).toNat]! = {} := by
  obtain ⟨m', h, _, hy⟩ := setV_vex128 i hL r v m
  refine ⟨m', h, ?_⟩
  rw [hy]
  have hs' : r.toNat &&& 7 < m.cpu.ymmh.size := by simpa using hs
  simp [Array.set!_eq_setIfInBounds, hs']

theorem setV_vex256 (i : Inst) (hL : i.vexL = true) (r : UInt8) (v : V256) (m : Machine) :
    ∃ m', setV i r v m = .ok () m' ∧ m'.cpu.xmm = m.cpu.xmm.set! (r &&& 7).toNat v.lo ∧
      m'.cpu.ymmh = m.cpu.ymmh.set! (r &&& 7).toNat v.hi := by
  refine ⟨_, rfl, ?_, ?_⟩ <;> simp [setV, setY, hL, Cpu.xmm, Cpu.ymmh]

/-- Legacy SSE register writes leave bits 255:128 of every YMM register unchanged. -/
theorem setXmm_ymmh (r : UInt8) (v : V128) (m : Machine) :
    ∃ m', setXmm r v m = .ok () m' ∧ m'.cpu.ymmh = m.cpu.ymmh := by
  exact ⟨_, rfl, rfl⟩

/-! ## VZEROUPPER, VZEROALL -/

/-- An instruction VEX.0F 77 with VEX.pp = 00 and VEX.vvvv = 1111b. -/
structure IsVzero (i : Inst) : Prop where
  op : i.op = 0x177
  pp : i.pp = 0
  v : i.vvvv = 0

theorem map1_vzero {i : Inst} (h : IsVzero i) :
    Avx.map1 i = some (do start i true; modCpu fun c => { c with sse := { c.sse with
      ymmh := Array.replicate 8 {}, xmm := if i.vexL then Array.replicate 8 {} else c.sse.xmm } }) := by
  have hb : i.byte = 0x77 := by simp [Inst.byte, h.op]; decide
  simp [Avx.map1, Avx.vzero, hb, h.pp, noV, h.v]

theorem vex?_vzero {i : Inst} (h : IsVzero i) :
    Avx.vex? i = Avx.map1 i := by
  have hm : i.map = 1 := by simp [Inst.map, h.op]; decide
  simp [Avx.vex?, hm, implemented]

/-- VZEROUPPER (VEX.L = 0): bits 255:128 of YMM0..7 become 0, XMM0..7 and everything else stay. -/
theorem vzeroupper {i : Inst} {m : Machine} (h : IsVzero i) (hL : i.vexL = false)
    (hen : avxEnabled m.cpu = true) (hts : m.cpu.cr0 &&& CR0.TS = 0) :
    ∃ a, Avx.vex? i = some a ∧
      a m = .ok () { m with cpu := { m.cpu with sse := { m.cpu.sse with ymmh := Array.replicate 8 {} } } } := by
  refine ⟨_, (vex?_vzero h).trans (map1_vzero h), ?_⟩
  simp [bind, EStateM.bind, start_ok hen hts, modCpu, hL]

/-- VZEROALL (VEX.L = 1): YMM0..7 become 0. -/
theorem vzeroall {i : Inst} {m : Machine} (h : IsVzero i) (hL : i.vexL = true)
    (hen : avxEnabled m.cpu = true) (hts : m.cpu.cr0 &&& CR0.TS = 0) :
    ∃ a, Avx.vex? i = some a ∧
      a m = .ok () { m with cpu := { m.cpu with sse := { m.cpu.sse with
        ymmh := Array.replicate 8 {}, xmm := Array.replicate 8 {} } } } := by
  refine ⟨_, (vex?_vzero h).trans (map1_vzero h), ?_⟩
  simp [bind, EStateM.bind, start_ok hen hts, modCpu, hL]

/-! ## VMASKMOVPS/PD -/

theorem maskSel_zero (bits n : Nat) : Avx.maskSel bits n {} = [] := by
  simp [Avx.maskSel, V256.lane, V128.lane]

/-- A VMASKMOVPS/PD store whose mask (YMM[VEX.vvvv]) selects no element changes nothing and raises
nothing, whatever the memory operand addresses (not-present or read-only pages, segment limits). -/
theorem maskStore_none {i : Inst} {m : Machine} (bits : Nat) (henc : (w0 i && i.isMem) = true)
    (hen : avxEnabled m.cpu = true) (hts : m.cpu.cr0 &&& CR0.TS = 0)
    (hsel : Avx.maskSel bits ((if i.vexL then 256 else 128) / bits)
      { lo := m.cpu.xmm[(i.vvvv &&& 7).toNat]!, hi := m.cpu.ymmh[(i.vvvv &&& 7).toNat]! } = []) :
    Avx.maskStore i bits m = .ok () m := by
  simp only [Avx.maskStore, henc, bind, EStateM.bind, start_ok hen hts]
  simp [src1, getY, Cpu.xmm, Cpu.ymmh] at hsel ⊢
  simp [hsel, getY, fpEa, forIn, pure, EStateM.pure, bind, EStateM.bind]

/-- A VMASKMOVPS/PD load whose mask selects no element writes zeros to the destination without any
memory access (so it cannot fault on the operand). -/
theorem maskLoad_none {i : Inst} {m : Machine} (bits : Nat) (henc : (w0 i && i.isMem) = true)
    (hen : avxEnabled m.cpu = true) (hts : m.cpu.cr0 &&& CR0.TS = 0)
    (hsel : Avx.maskSel bits ((if i.vexL then 256 else 128) / bits)
      { lo := m.cpu.xmm[(i.vvvv &&& 7).toNat]!, hi := m.cpu.ymmh[(i.vvvv &&& 7).toNat]! } = []) :
    Avx.maskLoad i bits m =
      setV i i.reg (V256.ofLanes bits (Array.replicate ((if i.vexL then 256 else 128) / bits) 0)) m := by
  simp only [Avx.maskLoad, henc, bind, EStateM.bind, start_ok hen hts]
  simp [src1, getY, Cpu.xmm, Cpu.ymmh] at hsel ⊢
  simp [hsel, fpEa, forIn, pure, EStateM.pure, bind, EStateM.bind]

/-! ## Extension point -/

/-- The VEX.256 forms of the 0F-map packed-integer opcodes (AVX2) are not handled by `Avx.vex?`:
`Avx2.vex?` is consulted next. -/
theorem map1_int {i : Inst} (hi : isPint i.byte = true) :
    Avx.map1 i = Avx.intMoves i i.byte i.pp.toNat := by
  unfold Avx.map1
  dsimp only
  split <;> first | rfl | (exfalso; rename_i h; rw [h] at hi; revert hi; decide)

theorem vex?_int256 {i : Inst} (hm : i.op >>> 8 = 1) (hp : i.pp = 1) (hL : i.vexL = true)
    (hi : isPint i.byte = true) : Avx.vex? i = none := by
  have hm' : i.map = 1 := hm
  simp only [Avx.vex?, hm', implemented, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [map1_int hi]
  simp [Avx.intMoves, hi, Avx.only128, hL, hp]

end X86
