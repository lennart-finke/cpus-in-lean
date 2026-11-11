# Litmus tests for the x86-TSO multiprocessor (`x86_32/X86/Tso.lean`)

`litmus.py` runs herd-format X86 litmus tests on the model and compares the set of final states with
herd7's `x86tso.cat` (herdtools7 7.58; Alglave and Maranget's axiomatic x86-TSO, equivalent to the
operational model of Owens, Sarkar and Sewell):

* each thread is assembled for i386 with clang (herd syntax rewritten to Intel syntax, data at
  `0x2000 + 0x40·i`, one cache line per location) and ends in HLT;
* `x86litmus` (`../LitmusMain.lean`) explores every interleaving of instruction steps and store-buffer
  commits (states deduplicated) and prints the final states over the observed locations;
* the two sets must be **equal**.

```
python3 litmus.py check-expected tests diy     # against the pinned sets in expected/ (no herd7 needed)
python3 litmus.py check tests diy              # against herd7 directly
python3 litmus.py expect tests diy             # regenerate expected/ with herd7
python3 litmus.py run tests/SB.litmus          # show both sets
```

* `tests/`: the classic shapes (SB, MP, LB, S, R, 2+2W, WRC, IRIW), the x86-TSO paper's n5/n6, and
  locked instructions (XCHG, LOCK INC, unlocked INC losing an update, LOCK XADD, LOCK CMPXCHG).
  herd7's X86 dialect has no XADD/CMPXCHG; their sets (`expected/XADD2.states`, `CAS2.states`) are
  written by hand from the SDM (`# hand` header) and kept by `expect`.
* `diy/`: 180 tests from `diy7 -arch X86 -nprocs 4 -size 6 -safe 'PodWW PodRR PodRW PodWR Rfe Fre
  Wse Rfi Fri Wsi PosWR PosRR PosRW PosWW'` (every cycle of up to 6 edges over program order,
  communication and same-location edges, including store forwarding).
* MFENCE, LFENCE and SFENCE are tested with store-buffering litmus cases against herd7.

Install herdtools7 (only needed for `check`/`expect`):

```
brew install opam pkgconf
OPAMROOT=~/.opam-verify opam init -y --bare --disable-sandboxing --no-setup
OPAMROOT=~/.opam-verify opam switch create herd ocaml-base-compiler.5.2.1
OPAMROOT=~/.opam-verify opam install --switch herd herdtools7.7.58     # herd7 in ~/.opam-verify/herd/bin
```

Results (2026-10-26): 197/197 equal (17 hand-written + 180 diy7 size 6), and 1772 diy7 tests of
size 8 checked once against herd7 (see the commit message).

Not covered here: mixed-size accesses (herd7's X86 is word-sized; rmem's mixed-size x86-TSO would
be the reference) and real hardware (litmus7 on an x86 machine; the outcomes observed there must be a
subset of the model's).
