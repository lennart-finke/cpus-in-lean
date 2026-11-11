import Solutions
/-!
# Proved tasks

One theorem per proved task, and nothing else: the theorem is named `Claims.<task>` and its type is
the task's proposition, written as that single constant. The proof is a reference into `Solutions`.

    theorem Claims.ChaCha20_ctr32_correct : Ssl.OpensslChacha20.ChaCha20_ctr32_correct :=
      Solutions.…

`Audit.lean` reads this file: a task without a theorem here is open.
-/
