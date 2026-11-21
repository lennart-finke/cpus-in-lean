import Solutions.Exec.Step
import Solutions.Exec.Dispatch
/-!
# Decoding by instruction shape

Checking a `cbv` proof of one `X86.step` cost the kernel 4–6 s and about 0.5 GB, nearly all of it in
`decode`: the kernel re-checks the unfolded body of the decoder (its prefix loop and the record
updates) for every instruction. Here the decoder is run once per *shape* — the opcode, ModRM and SIB
bytes — on a machine with a symbolic instruction pointer and symbolic displacement/immediate bytes,
giving a theorem `Solutions.Exec.Shape.dec_<hex bytes>_<length>`; executing an instruction of that
shape instantiates the theorem, with the code bytes checked by `decide`.

Measured (`lake env lean -M 4000`): a register `mov` went from 4.2 s kernel time to under 0.1 s; the
24 run pieces of `fe_add`/`fe_sub` (68 instructions, `AddSubRun`) from 243 s / 3.3 GB to 8 s wall
(26 s CPU) / 2.0 GB, plus 102 s once for their 20 shapes; 20 instructions of `fe_sq` (`imul` chains
with stores) in three pieces take 4.3 s / 1.6 GB.

## Usage

1. Generate the shapes of the code you run, in a file of your own (shapes are shared through imports;
   one costs about 5 s):
   ```
   import Solutions.Exec.Shape
   open X86 Solutions.Logic Solutions.Exec Solutions.Exec.Shape
   set_option maxRecDepth 100000
   set_option maxHeartbeats 0
   set_option cbv.maxSteps 50000000
   decode_shape [0x8B, 0x44, 0x24] 4   -- movl disp8(%esp), %eax: literal opcode/ModRM/SIB, length 4
   decode_shape [0xC3] 1               -- retl
   ```
   The literal bytes are the prefixes, the opcode (with `0F`), ModRM and SIB; the rest of the
   instruction (displacement, immediate) stays symbolic. `Solutions/Exec/shapes.py` (in
   `suites/openssl`) writes such a module for an address range of a disassembly, for any suite whose
   image module has the usual `def base`, `def chunkSize`, `def chunkN` form, e.g. from `suites/curl`:
   ```
   python3 ../openssl/Solutions/Exec/shapes.py Curl/Image.lean <image>.dis 1000a0 100340 \
     Curl/Proofs/Shapes.lean "base64 encoder"
   ```
   (paths are the suite's own; `hi` is exclusive). Build the module with `lean -M 4000` first.
2. Import that file and `open Solutions.Exec.Fast` next to `Solutions.Logic Solutions.Exec` in the
   files that run code with `cbv`; nothing else changes. The simproc `cbvDecode` fires on `decode` of
   an `St.m` machine whose memory is a `CodeMem.get` and whose `eip` is a literal, when a shape theorem
   for the bytes there exists; otherwise `cbv` decodes as before.
3. Keep pieces to about eight instructions (or four stores): in one `cbv` call, the time grows quickly
   with the number of stores (11 instructions with 5 stores: 8 s).

`open Solutions.Exec.Fast` also folds the opaque 32-bit operations on two literals (`UInt32.lor`, …),
which the instantiated shapes leave behind.

* `fetch8_St`: a code fetch from a flat `St.m` machine below `ramTop` is the memory byte.
* scoped to `Solutions.Exec.Shape` (open only to prove shape theorems): `cbv` rewrites `fetch8` at any
  address by `fetch8_St` (side condition by `exec_omega`) and a byte `rdBytes mem a 1` by a
  hypothesis `rdBytes mem a 1 = v` in context.
-/
namespace Solutions.Exec
open X86 Solutions.Logic Lean Meta

theorem flatM_St (s : St) : FlatM (St.m s) := ⟨show (17 : UInt32) &&& CR0.PG = 0 by decide, rfl, rfl, rfl, rfl, rfl⟩

theorem fetch8_St (s : St) (f : UInt32) (hfl : s.fl = efl f) {a : UInt32} (ha : a.toNat < ramTop) :
    fetch8 a (St.m s) = .ok (rdBytes s.mem a 1) (St.m s) := by
  have hc : (St.m s).cpu.cpl = 0 := cpl_zero _ f rfl hfl rfl
  have hl : ¬ (a > (St.m s).cpu.cs.limit) := by
    show ¬ (a > 4294967295)
    intro h
    rw [GT.gt, UInt32.lt_iff_toNat_lt] at h
    have := a.toNat_lt
    simp at h
    omega
  unfold fetch8
  simp only [hl, ite_false]
  simp only [bind, EStateM.bind, isUser, hc]
  rw [translate_flat (flatM_St s)]
  simp only
  rw [show (St.m s).cpu.cs.base + a = a from by
    show (0 : UInt32) + a = a
    exact UInt32.zero_add a]
  exact physRd_flat (flatM_St s) ha 1

end Solutions.Exec

namespace Solutions.Exec.Shape
open X86 Solutions.Logic Solutions.Exec Lean Meta Sym

/-- The `St` of a machine that `cbv` has unfolded from `St.m s` (its fields, read back), when its
flags are `efl f`; with `f`. -/
def stOf? (m : Expr) : MetaM (Option (Expr × Expr)) := do
  let fld (n : Name) (x : Expr) : MetaM Expr := whnfR (mkApp (mkConst n) x)
  let cpu ← fld ``Machine.cpu m
  let fl ← fld ``Cpu.eflags cpu
  unless fl.isAppOfArity ``efl 1 do return none
  let s := mkAppN (mkConst ``St.mk) #[← fld ``Machine.mem m, ← fld ``Cpu.eax cpu, ← fld ``Cpu.ecx cpu,
    ← fld ``Cpu.edx cpu, ← fld ``Cpu.ebx cpu, ← fld ``Cpu.esp cpu, ← fld ``Cpu.ebp cpu, ← fld ``Cpu.esi cpu,
    ← fld ``Cpu.edi cpu, ← fld ``Cpu.eip cpu, fl, ← fld ``Machine.icount m]
  -- the machine must be `St.m s` (its other fields are those `St.m` sets)
  unless ← withDefault (isDefEq (mkApp (mkConst ``St.m) s) m) do return none
  return some (s, fl.appArg!)

open Discharge in
/-- `fetch8 a m` at a symbolic address, `m` an unfolded `St.m s`: the memory byte, when `exec_omega`
shows the address is below `ramTop`. -/
scoped cbv_simproc cbv_eval cbvFetch8 (fetch8 _ _) := fun e => do
  let_expr fetch8 a m := e | return .rfl
  let some (s, f) ← stOf? m | return .rfl
  let goal ← mkAppM ``LT.lt #[← mkAppM ``UInt32.toNat #[a], mkConst ``ramTop]
  let some ha ← omega? goal | return .rfl
  let hfl ← Meta.mkEqRefl (mkApp (mkConst ``efl) f)
  let pf := mkAppN (mkConst ``fetch8_St) #[s, f, hfl, a, ha]
  let mem ← whnfR (mkApp (mkConst ``Machine.mem) m)
  let rhs := mkApp5 (mkConst ``EStateM.Result.ok [Level.zero]) (mkConst ``X86.Fault) (mkConst ``X86.Machine)
    (mkConst ``UInt32) (mkApp3 (mkConst ``rdBytes) mem a (toExpr (1 : UInt32))) m
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

attribute [scoped cbv_opaque] fetch8

/-- `rdBytes mem a 1` by a hypothesis `rdBytes mem a 1 = v` of the local context. -/
scoped cbv_simproc cbv_eval cbvHypByte (rdBytes _ _ _) := fun e => do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let some (_, l, r) := d.type.eq? | continue
    if l == e then
      return .step r (mkFVar d.fvarId)
  return .rfl

end Solutions.Exec.Shape

namespace Solutions.Exec.Shape
open X86 Solutions.Logic Solutions.Exec Lean Meta Elab Command

/-- The name of the shape theorem for the literal bytes `bs` and instruction length `len`. -/
def shapeName (bs : List Nat) (len : Nat) : Name :=
  let hex (n : Nat) : String :=
    let d := Nat.toDigits 16 n
    String.ofList (if d.length < 2 then '0' :: d else d)
  .str `Solutions.Exec.Shape s!"dec_{String.join (bs.map hex)}_{len}"

/-- `decode_shape [b₀, …, bₖ₋₁] len`: the theorem that `decode` of a flat `St.m` machine whose code
at the (symbolic) `eip` starts with the literal bytes `b₀ … bₖ₋₁`, followed by `len - k` arbitrary
bytes (displacement, immediate), is the instruction `cbv` computes. Needs
`open Solutions.Logic Solutions.Exec Solutions.Exec.Shape`. -/
elab "decode_shape " "[" bs:num,* "]" len:num : command => liftTermElabM do
  let bs := bs.getElems.toList.map (·.getNat)
  let len := len.getNat
  let u32 := mkConst ``UInt32
  let regNames := [`mem, `eax, `ecx, `edx, `ebx, `esp, `ebp, `esi, `edi, `e, `f]
  withLocalDeclD `mem (mkConst ``ByteArray) fun mem => do
  withLocalDeclD `eax u32 fun eax => withLocalDeclD `ecx u32 fun ecx => withLocalDeclD `edx u32 fun edx =>
  withLocalDeclD `ebx u32 fun ebx => withLocalDeclD `esp u32 fun esp => withLocalDeclD `ebp u32 fun ebp =>
  withLocalDeclD `esi u32 fun esi => withLocalDeclD `edi u32 fun edi => withLocalDeclD `e u32 fun e =>
  withLocalDeclD `f u32 fun f => withLocalDeclD `ic (mkConst ``UInt64) fun ic => do
  let _ := regNames
  -- the symbolic bytes
  let nsym := len - bs.length
  let symDecls := (List.range nsym).map fun k => (Name.mkSimple s!"b{bs.length + k}", fun (_ : Array Expr) => pure u32)
  withLocalDeclsD symDecls.toArray fun syms => do
  let addr (k : Nat) : MetaM Expr :=
    if k == 0 then pure e else pure (mkApp2 (mkConst ``UInt32.add) e (toExpr k.toUInt32))
  let byteVal (k : Nat) : Expr := if k < bs.length then toExpr (bs[k]!).toUInt32 else syms[k - bs.length]!
  let hm ← mkAppM ``LE.le #[← mkAppM ``ByteArray.size #[mem], mkConst ``ramTop]
  let he ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[← mkAppM ``UInt32.toNat #[e], toExpr len],
    ← mkAppM ``ByteArray.size #[mem]]
  let mut hyps : Array (Name × (Array Expr → TermElabM Expr)) := #[(`hm, fun _ => pure hm), (`he, fun _ => pure he)]
  for k in List.range len do
    let a ← addr k
    let t ← mkEq (mkApp3 (mkConst ``rdBytes) mem a (toExpr (1 : UInt32))) (byteVal k)
    hyps := hyps.push (Name.mkSimple s!"h{k}", fun _ => pure t)
  withLocalDeclsD hyps fun hs => do
  let s := mkAppN (mkConst ``St.mk) #[mem, eax, ecx, edx, ebx, esp, ebp, esi, edi, e,
    mkApp (mkConst ``efl) f, ic]
  let lhs := mkApp (mkConst ``decode) (mkApp (mkConst ``St.m) s)
  let r ← Lean.Meta.Tactic.Cbv.cbvEntry lhs
  let (rhs, pf) ← match r with
    | .step e' p _ _ => pure (e', p)
    | .rfl .. => throwError "decode_shape: cbv made no progress"
  let rhs ← instantiateMVars rhs
  let pf ← instantiateMVars pf
  let xs := #[mem, eax, ecx, edx, ebx, esp, ebp, esi, edi, e, f, ic] ++ syms ++ hs
  let ty ← mkForallFVars xs (← mkEq lhs rhs)
  let val ← mkLambdaFVars xs pf
  let name := shapeName bs len
  addDecl (.thmDecl { name, levelParams := [], type := ty, value := val })
  trace[Meta.Tactic.cbv] "{name} : {rhs}"

end Solutions.Exec.Shape

namespace Solutions.Exec.Fast
open X86 Solutions.Logic Solutions.Exec Solutions.Exec.Shape Lean Meta Sym

theorem rdBytes_code {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code)
    (a : UInt32) (h : base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + size) :
    rdBytes g.get a 1 = (code (a.toNat - base.toNat)).toUInt32 := by
  rw [rdBytes_codeMem]
  split
  · rfl
  · rename_i hn
    exact absurd ⟨rfl, h⟩ hn

theorem size_code {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code)
    (n : Nat) (h : n ≤ base.toNat + size) : n ≤ g.get.size :=
  Nat.le_trans h g.fits

/-- The natural-number value of a closed term (by `whnf`), if it is a literal. -/
def natVal? (e : Expr) : MetaM (Option Nat) := do
  let v ← whnfD e
  match v.rawNatLit? with
  | some n => return some n
  | none => return (Sym.getNatValue? v).run

/-- Fold a binary `UInt32` operation on two literals (the operations are opaque to `cbv`, and the
instantiated shape theorems leave them applied to literals). -/
def bin32 (f : UInt32 → UInt32 → UInt32) (e : Expr) : Sym.Simp.SimpM Sym.Simp.Result := do
  let some a := (Sym.getNatValue? e.appFn!.appArg!).run | return .rfl
  let some b := (Sym.getNatValue? e.appArg!).run | return .rfl
  let r ← share (toExpr (f a.toUInt32 b.toUInt32))
  return .step r (← Sym.mkEqRefl r)

scoped cbv_simproc cbv_eval cbvLor32 (UInt32.lor _ _) := bin32 (· ||| ·)
scoped cbv_simproc cbv_eval cbvLand32 (UInt32.land _ _) := bin32 (· &&& ·)
scoped cbv_simproc cbv_eval cbvXor32 (UInt32.xor _ _) := bin32 (· ^^^ ·)
scoped cbv_simproc cbv_eval cbvShr32 (UInt32.shiftRight _ _) := bin32 (· >>> ·)
scoped cbv_simproc cbv_eval cbvShl32 (UInt32.shiftLeft _ _) := bin32 (· <<< ·)
scoped cbv_simproc cbv_eval cbvAdd32 (UInt32.add _ _) := bin32 (· + ·)
scoped cbv_simproc cbv_eval cbvSub32 (UInt32.sub _ _) := bin32 (· - ·)
scoped cbv_simproc cbv_eval cbvMul32 (UInt32.mul _ _) := bin32 (· * ·)

open Discharge in
/-- `decode m` of an unfolded `St.m s` with a literal `eip` in a `CodeMem`: the shape theorem for
its bytes, instantiated. -/
scoped cbv_simproc cbv_eval cbvDecode (decode _) := fun e => do
  let_expr decode m := e | return .rfl
  let some (s, f) ← stOf? m | return .rfl
  let args := s.getAppArgs
  let mem := args[0]!
  let eip := args[9]!
  let some eipV := (Sym.getNatValue? eip).run | return .rfl
  unless mem.isAppOfArity ``CodeMem.get 4 do return .rfl
  let base := mem.getArg! 0
  let size := mem.getArg! 1
  let code := mem.getArg! 2
  let g := mem.getArg! 3
  let some baseV ← natVal? (mkApp (mkConst ``UInt32.toNat) base) | return .rfl
  let some sizeV ← natVal? size | return .rfl
  unless baseV ≤ eipV ∧ eipV + 15 ≤ baseV + sizeV do return .rfl
  -- the bytes at eip
  let mut bytes : Array Nat := #[]
  for k in [0:15] do
    let some b ← natVal? (mkApp (mkConst ``UInt8.toNat) (mkApp code (toExpr (eipV + k - baseV))))
      | return .rfl
    bytes := bytes.push b
  -- the shape theorem
  let env ← getEnv
  let mut found : Option (Name × Nat × Nat) := none
  for k in [1, 2, 3, 4].reverse do
    for len in [1:16] do
      if found.isNone && k ≤ len then
        let n := shapeName (bytes.toList.take k) len
        if env.contains n then found := some (n, k, len)
  let some (thm, k, len) := found | return .rfl
  let addr (j : Nat) : Expr :=
    if j == 0 then eip else mkApp2 (mkConst ``UInt32.add) eip (toExpr j.toUInt32)
  let mut syms : Array Expr := #[]
  for j in [k:len] do syms := syms.push (toExpr (bytes[j]!).toUInt32)
  let some hm ← omega? (← mkAppM ``LE.le #[← mkAppM ``ByteArray.size #[mem], mkConst ``ramTop]) | return .rfl
  let heRange ← mkDecideProof (← mkAppM ``LE.le #[toExpr (eipV + len), mkNatAdd (← mkAppM ``UInt32.toNat #[base]) size])
  let he ← mkExpectedTypeHint (mkApp5 (mkConst ``size_code) base size code g (toExpr (eipV + len)) |>.app heRange)
    (← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[← mkAppM ``UInt32.toNat #[eip], toExpr len],
      ← mkAppM ``ByteArray.size #[mem]])
  let mut hs : Array Expr := #[]
  for j in [0:len] do
    let a := addr j
    let rng ← mkDecideProof (← mkAppM ``And #[← mkAppM ``LE.le #[← mkAppM ``UInt32.toNat #[base], ← mkAppM ``UInt32.toNat #[a]],
      ← mkAppM ``LT.lt #[← mkAppM ``UInt32.toNat #[a], mkNatAdd (← mkAppM ``UInt32.toNat #[base]) size]])
    let p1 := mkAppN (mkConst ``rdBytes_code) #[base, size, code, g, a, rng]
    let lhsVal := mkApp (mkConst ``UInt8.toUInt32) (mkApp code (← mkAppM ``HSub.hSub #[← mkAppM ``UInt32.toNat #[a], ← mkAppM ``UInt32.toNat #[base]]))
    let p2 ← mkDecideProof (← mkEq lhsVal (toExpr (bytes[j]!).toUInt32))
    hs := hs.push (← mkEqTrans p1 p2)
  let pf := mkAppN (mkConst thm) (args[0:9].toArray ++ #[eip, f, args[11]!] ++ syms ++ #[hm, he] ++ hs)
  let ty ← Meta.inferType pf
  let some (_, _, rhs) := ty.eq? | return .rfl
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

end Solutions.Exec.Fast
