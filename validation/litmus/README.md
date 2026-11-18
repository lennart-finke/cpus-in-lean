# Litmus tests for the x86-TSO multiprocessor (`x86_32/X86/Tso.lean`)

`litmus.py` runs herd-format X86 litmus tests on the model and requires its final-state set to
**equal** herd7's `x86tso.cat` (herdtools7 7.58). Threads are assembled with clang (data at
`0x2000 + 0x40·i`, one cache line each, ending in HLT); `x86litmus` (`../LitmusMain.lean`) explores
every interleaving of steps and store-buffer commits.

```
python3 litmus.py check-expected tests diy     # against the pinned sets in expected/ (no herd7 needed)
python3 litmus.py check tests diy              # against herd7 directly
python3 litmus.py expect tests diy             # regenerate expected/ with herd7
python3 litmus.py run tests/SB.litmus          # show both sets
```

* `tests/`: SB, MP, LB, S, R, 2+2W, WRC, IRIW, n5/n6, the three fences, XCHG, LOCK INC/XADD/CMPXCHG
  and a lost unlocked INC. `expected/XADD2.states`, `CAS2.states` are hand-written from the SDM
  (herd7 lacks XADD/CMPXCHG; `# hand`, kept by `expect`).
* `diy/`: 180 tests from `diy7 -arch X86 -nprocs 4 -size 6 -safe 'PodWW PodRR PodRW PodWR Rfe Fre
  Wse Rfi Fri Wsi PosWR PosRR PosRW PosWW'`.

herdtools7 (only for `check`/`expect`):

```
brew install opam pkgconf
OPAMROOT=~/.opam-verify opam init -y --bare --disable-sandboxing --no-setup
OPAMROOT=~/.opam-verify opam switch create herd ocaml-base-compiler.5.2.1
OPAMROOT=~/.opam-verify opam install --switch herd herdtools7.7.58     # herd7 in ~/.opam-verify/herd/bin
```

Results (2026-10-26): 197/197 equal, plus 1772 diy7 size-8 tests checked once. Not covered:
mixed-size accesses (herd7's X86 is word-sized) and real hardware.
