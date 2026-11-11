import Ssl
/-!
# Proofs of the tasks

Proofs live in this library (`Solutions/…`, imported here) and nowhere else. They may import the
statement library `Ssl` and the model `X86`, and must not change either: `tools/tcb.py` pins both.
A task counts as proved only once `Claims.lean` restates it and the audit (`Audit.lean`, run by
`verify.sh`) accepts it.
-/
