import Claims
import Lean
/-!
# Audit of the proved tasks

Run by `verify.sh` as `lake env lean Audit.lean`; elaboration fails if a claim is not acceptable.
For every task it reports `PROVED` or `OPEN`. A task is proved when

* `Claims.<task>` is a theorem whose type is syntactically the task's proposition (the constant
  defined in the pinned `Statement.lean`, not something equal to it by unfolding), and
* the axioms its proof depends on, transitively, are all in `allowedAxioms`.

`Claims.lean` may declare nothing but such theorems.

**Axiom policy.** Only Lean's three standard axioms are accepted. In particular proofs that use
`native_decide` or `bv_decide` are rejected: both add axioms that trust the Lean compiler and the
code it generates, which is a larger trusted base than the kernel. Widening the policy means
editing `allowedAxioms` below; this file is pinned by `tools/tcb.py`, so that is a visible,
separately reviewed change.

The audit is complemented by `leanchecker`, which replays the declarations of `Ssl`, `Solutions`
and `Claims` through the kernel and so detects declarations that were added without being checked.
-/
open Lean Elab Command

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Task name, and the proposition a claim of that name must have as its type. -/
def tasks : List (Name × Name) :=
  [(`sha256_streaming_correct, `Ssl.OpensslSha256.sha256_streaming_correct),
   (`sha224_streaming_correct, `Ssl.OpensslSha256.sha224_streaming_correct),
   (`SHA256_Transform_correct, `Ssl.OpensslSha256.SHA256_Transform_correct),
   (`ChaCha20_ctr32_correct, `Ssl.OpensslChacha20.ChaCha20_ctr32_correct),
   (`Poly1305_correct, `Ssl.OpensslPoly1305.Poly1305_correct),
   (`Poly1305_oneshot, `Ssl.OpensslPoly1305.Poly1305_oneshot),
   (`Poly1305_ctx_size_correct, `Ssl.OpensslPoly1305.Poly1305_ctx_size_correct),
   (`fe_mul_correct, `Ssl.OpensslX25519.fe_mul_correct),
   (`fe_sq_correct, `Ssl.OpensslX25519.fe_sq_correct),
   (`fe_add_correct, `Ssl.OpensslX25519.fe_add_correct),
   (`fe_sub_correct, `Ssl.OpensslX25519.fe_sub_correct),
   (`ossl_x25519_correct, `Ssl.OpensslX25519.ossl_x25519_correct),
   (`ossl_x25519_public_from_private_correct, `Ssl.OpensslX25519.ossl_x25519_public_from_private_correct)]

#eval show CommandElabM Unit from do
  let env ← getEnv
  -- everything `Claims.lean` declares must be one of the task theorems
  let some idx := env.getModuleIdx? `Claims | throwError "module Claims is not imported"
  for name in env.header.moduleData[idx.toNat]!.constNames do
    unless name.isInternalDetail || tasks.any (fun (t, _) => name == `Claims ++ t) do
      throwError "Claims.lean declares {name}, which is not a task"
  let mut proved := 0
  for (task, statement) in tasks do
    let some stmt := env.find? statement | throwError "the statement {statement} does not exist"
    unless stmt.type.isProp do throwError "{statement} is not a proposition"
    match env.find? (`Claims ++ task) with
    | none => IO.println s!"OPEN    {task}"
    | some claim =>
      unless claim matches .thmInfo _ do throwError "Claims.{task} is not a theorem"
      unless claim.type == mkConst statement do
        throwError "the type of Claims.{task} is not the constant {statement}"
      let axioms ← liftCoreM (collectAxioms claim.name)
      let extra := axioms.filter (!allowedAxioms.contains ·)
      unless extra.isEmpty do
        throwError "Claims.{task} depends on axioms outside the policy: {extra}"
      IO.println s!"PROVED  {task}"
      proved := proved + 1
  IO.println s!"{proved} of {tasks.length} tasks proved; axioms allowed: {allowedAxioms}"
