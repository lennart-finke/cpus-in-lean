import Ssl
import Solutions.Exec.Cbv
import Solutions.Exec.Mem
import Solutions.Exec.Step
import Solutions.Exec.Dispatch
import Solutions.Exec.Call
import Solutions.Exec.Alu
import Solutions.OpensslPoly1305.CtxSize
import Solutions.OpensslX25519.AddSubMath
import Solutions.OpensslX25519.Call
import Solutions.OpensslX25519.AddSub
import Solutions.OpensslX25519.Sq
import Solutions.OpensslX25519.Mul
import Solutions.OpensslX25519.X25519
import Solutions.OpensslSha256.Transform
import Solutions.OpensslSha256.Streaming
import Solutions.OpensslChacha20.Correct
import Solutions.OpensslPoly1305.Main
/-!
# Proofs of the tasks

Proofs live in this library (`Solutions/…`, imported here) and nowhere else. They may import the
statement library `Ssl` and the model `X86`, and must not change either: `tools/tcb.py` pins both.
A task counts as proved only once `Claims.lean` restates it and the audit (`Audit.lean`, run by
`verify.sh`) accepts it.
-/
