import Solutions.Exec.Byte
import Solutions.Exec.Shape
/-!
# Data reads at symbolic addresses of a code memory under `cbv`, inside or outside the code

`Solutions.Exec.Byte.cbvRdOut` turns a data read `rdBytes (CodeMem.get G) a n` at a symbolic address into
`rdRaw` when `exec_omega` shows `a` outside the code range; inside the code range `cbv` would evaluate
`rdBytes_codeMem`'s test and the code function at a symbolic index (recursion depth, memory). `cbvRdAny`
(scoped in `Solutions.Exec.CodeRd`) turns every such read into `rdRaw` (definitionally equal), so that a
loop over a constant table inside the image runs like one over a caller's buffer; the values of the bytes
are then facts about the code memory (`CodeMem.ok`). Use it with `Solutions.Exec.Byte.cbvRdOut` removed.
Prover P, additions only.
-/
namespace Solutions.Exec.CodeRd
open X86 Solutions.Logic Solutions.Exec Lean Meta

/-- A data read of a code memory at a symbolic address: `rdRaw`. -/
scoped cbv_simproc cbv_eval cbvRdAny (rdBytes (CodeMem.get _) _ _) := fun e => do
  let_expr rdBytes mem a n := e | return .rfl
  unless mem.isAppOfArity ``CodeMem.get 4 do return .rfl
  if (Sym.getNatValue? a).run.isSome then return .rfl
  let r ← Sym.share (mkApp3 (mkConst ``Solutions.Logic.rdRaw) mem a n)
  return .step r (← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e r))

end Solutions.Exec.CodeRd
