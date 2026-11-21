import Solutions.OpensslChacha20.Base
/-!
# Loads known from hypotheses

`cbvHypRd`: a load `rdRaw M a n` for which the context has a hypothesis `rdRaw M a n = v` (the same
memory, address and size) is `v`. With it the facts a step lemma assumes about the memory it starts
from are used by `cbv` directly.
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Lean Meta

cbv_simproc cbv_eval cbvHypRd (rdRaw _ _ _) := fun e => do
  let_expr rdRaw M a n := e | return .rfl
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, v) := ty.eq? | continue
    let_expr rdRaw M' a' n' := l | continue
    if M' == M && a' == a && n' == n then
      return .step v d.toExpr
  return .rfl

end Solutions.OpensslChacha20
