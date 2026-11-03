#!/bin/sh
# The IA-32 model: build the semantics and the theorems about the model, reject sorry/admit.
set -e
cd "$(dirname "$0")"
LAKE=${LAKE:-lake}
command -v $LAKE >/dev/null || LAKE=~/.elan/bin/lake
$LAKE build X86 X86Proofs
if grep -rnE "\bsorry\b|\badmit\b" X86/ >/dev/null; then echo "FAIL: sorry/admit in model sources"; exit 1; fi
echo "MODEL OK: X86 and X86Proofs built, no sorry"
