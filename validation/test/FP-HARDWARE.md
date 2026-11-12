# IA-32 user-mode hardware campaign (the EPYC bundle)

This suite runs single 32-bit instructions natively on an x86-64 Linux machine, in **32-bit
compatibility mode**, captures the complete user-visible state (GPRs, flags, x87, MMX, XMM, YMM upper
halves, MXCSR, three memory hashes, the fault) and compares it with the **IA-32 model** run the same
way (`x86fp --compat`). It started as the x87/MMX/SSE/SSE2 campaign and now carries every user-mode
family of the Zen 2 work: the GPR extensions, SSE3..SSE4a and MisalignSse, AES/PCLMULQDQ/SHA, the
XSAVE family, AVX, AVX2/FMA/F16C, alignment checking, the instructions that differ in compatibility
mode, and the open hardware questions (`validation/README.md`, "Open questions for the EPYC"). The
older native IA-32 runner captures integer state; the older focused SSE campaign targets the
**x86-64 model**.

## Run on the Linux box

The prepared paste script is self-contained. The current one is
`validation/test/out/ia32-epyc-linux-paste.sh` (22.9 MB; seed 20261112, `--count 10000`; regenerate
with the command under "Prepare" below). Copy it to the Linux box and run:

```sh
bash ia32-epyc-linux-paste.sh
```

Alternatively, paste the entire contents of that script into a Bash terminal.
It creates a fresh directory under `/tmp`, unpacks the bundle and runs it.
The script needs **Python 3 and x86-64 Linux with IA-32 compatibility enabled**.
It does not need root, KVM, ptrace, a compiler, multilib libraries, Lean, or a
network connection. The executable is a freestanding ELF64 process that enters
32-bit mode through Linux signal return. Signal handlers use an alternate stack.

If using the smaller `.tar.gz` bundle instead:

```sh
tar -xzf ia32-epyc-linux.tar.gz
python3 ia32-epyc-linux/native_fp.py run ia32-epyc-linux
```

The runner prints the results directory and `results.tar.gz` location. Return
that archive; it includes the CPU identity/microcode information from
`/proc/cpuinfo`, kernel version, complete raw observations, calibration logs,
per-case differences and a summary. The bundle holds 189,240 cases in 66 campaigns; allow
several minutes (the earlier 120,000-case campaign took a few minutes on the 7742) and about 1 GB of
free disk space (the unpacked bundle is 402 MB, the raw results about as much again). The default timeout is 600 seconds **per batch**; override with
`--timeout 1800` if needed. A run on a VM records the guest CPU environment;
use a bare-metal host when collecting physical-CPU evidence.

Exit status:

- `0`: all compared defined fields agree exactly.
- `1`: strict mismatches, execution failure, malformed output or damaged inputs.
- `2`: only approximation/domain differences remain; review is required.

`comparison.json` summarizes results. `mismatches.jsonl` contains each differing
case's campaign name, batch-local index, opcode, family, control settings where applicable,
and hardware/model values. The matching `.bin` record contains every input bit;
the batch name identifies the corresponding input and raw output files.
No failed record is rewritten using a model answer or a QEMU deviation rule.

### Bundle format v2, CPUID dump, feature-gated families

Bundles prepared now are `ia32-fp-v2`: each 648-byte input record is followed by
YMM0..7 bits 255:128 (128 bytes), which the oracle installs in the AVX component
of the signal frame's XSAVE area (offset from CPUID leaf 0DH subleaf 2); each row
reports their final values, so legacy x87/SSE instructions are also checked to
preserve the YMM upper halves. Where the kernel's signal frame has no AVX state,
the oracle reports that (last column) and the YMM fields are not compared.
`compare` still accepts `ia32-fp-v1` bundles and results.

Before the campaigns, `run` stores every CPUID leaf and subleaf of the machine
(`oracle cpuid`) as `cpuid.txt` in the results, and the reported features in
`hardware.json`. A case family may require CPUID features (`fp_cases.FAMILIES`,
names in `native_fp.FEATURES`); its cases form their own campaigns, which are
skipped and reported when the machine lacks a feature (the base x87/SSE2 families require
none; every Zen 2 family requires its feature, e.g. `avx2`, `fma`, `f16c`, `osxsave`).

Run again with a fresh output directory:

```sh
python3 ia32-epyc-linux/native_fp.py run ia32-epyc-linux --result run-2
```

## Coverage

The bundle has 189,240 independent single-instruction cases in 76 families, split into campaigns
of at most 5,000 cases that share their CPUID requirements; 10,368 are 'observe' cases (recorded,
reported, not failed: the outcomes the manuals leave to the implementation). The base campaign
combines deterministic matrices with 10,000 seeded random x87 cases and 10,000 seeded random SSE
cases; the Zen 2 families are listed in `validation/README.md` with the layer each belongs to
(`gpr_*`, `sse3_*` .. `sse4a`, `misalign_sse`, `aes*`, `pclmulqdq*`, `sha*`, `xsave_*`, `avx_*`,
`avx2_*`, `fma_special`, `f16c`, `alignment_check`, `longmode`, `open_questions*`). Bundles prepared
after the first EPYC 7742 run (`validation/README.md`, "First run") also have `sse_rcp_sweep` (12,400
'observe' cases, `test/native_rcp.py`): the whole RCPPS/RSQRTPS tables, so that a later round can
reproduce AMD's results exactly. The base campaign covers:

- x87 arithmetic, reverse/pop forms, square root, rounding, scaling, extraction,
  remainder, comparisons, conditional moves, sign operations, stack moves,
  constants, control operations and all eight transcendental instructions.
- All three defined x87 precision controls and all four rounding modes, signed
  zero, normal/extreme values, denormals, pseudo-denormals, infinities, quiet and
  signaling NaNs, unnormals and values near rounding boundaries.
- Every x87 exception individually unmasked, all masked and all unmasked; every
  TOP position, empty operands, full stacks, and pending exceptions tested with
  WAIT, FNOP, MMX, EMMS and SSE instructions.
- x87 binary32/64/80 memory formats, signed integer conversions, packed BCD,
  read-only and absent pages, plus FXSAVE/FXRSTOR, FNSAVE/FRSTOR and FNSTENV.
- MMX and SSE2 packed-integer operations, saturation patterns, register and
  memory operands, shift boundaries through 255, all 256 immediates for the
  included shuffle/insert/extract forms, transfers and non-temporal stores.
- SSE/SSE2 packed and scalar arithmetic, comparisons, conversions, moves and
  shuffles. The directed matrix covers all 64 exception-mask settings, four
  rounding modes, DAZ/FTZ combinations, all six exception classes, mixed-lane
  priorities, sticky flags, underflow/overflow boundaries and two-NaN payloads.
- Misaligned memory operands, page faults, MXCSR reserved bits and fences.

Inputs are generated independently of both outcomes. The native oracle never
reads expected results. Each batch starts with native plumbing checks: NOP with
TF off/on, GPR/XMM preservation, nonzero x87 TOP and mixed tags, memory loads and
stores, and actual read-only/not-present faults. Checksummed bundles retain the
exact model executable identity, semantic sources, driver, generator and oracle
sources. Missing, reordered, duplicated, truncated or extra output is rejected.

## Comparison boundaries

The oracle executes each case as 32-bit code in compatibility mode under 64-bit Linux, and the model
does the same (`x86fp --compat`: EFER.LMA, 4-level paging, a 32-bit code segment with L = 0); the
`longmode` family (`native_longmode.py`) holds the user-mode instructions whose outcome differs from
legacy protected mode (SYSENTER/SYSEXIT, SWAPGS and the FSGSBASE instructions are #UD). The 116,715
cases of the earlier campaigns give identical model results in legacy and in compatibility mode.

The comparison checks exception vector/error, instruction pointer, eight GPRs,
defined arithmetic flags, all eight XMM registers, MXCSR, defined x87 control and
status bits, physical tag bits, nonempty x87 registers, and three memory hashes.
For FPREM/FPREM1, quotient bits are excluded while C2 indicates partial reduction.
Random x87 probes omit condition codes; the directed matrix checks the condition
codes defined by comparisons, remainder and FXAM, and C1 for basic arithmetic.

Undefined/reserved fields are deliberately excluded. FIP/FDP/FOP are recorded
but not used as pass/fail criteria because update policies vary by processor.
Save-image hashes zero reserved/pointer fields and MXCSR_MASK before hashing;
defined CW/SW/tags, register data, MXCSR and XMM bytes remain checked. FXSAVE's
software area remains checked. Memory outside the excluded image bytes is also
checked. Empty x87 register payloads are excluded only when **both** results
mark the corresponding register empty; TOP and tags remain checked separately.

Transcendental implementations need not match the model's correctly rounded
choice bit for bit, and some test inputs are outside defined domains. RCP/RSQRT
are approximations. Their numerical/status differences are retained as
observations, **not certified as within an accuracy bound**. Unexpected traps,
register corruption, stack/tag changes and memory differences still count as
strict mismatches. There is no hardware-specific allowlist.

This is extensive sampling, not exhaustive ISA validation. It does not test
privileged instructions, system devices, protected-mode transitions, concurrency
ordering, timing, or every encoding. A fence completing in user mode does not
establish its multiprocessor ordering semantics. A clean result is evidence
against this exact model revision and CPU, not a proof of the entire model.

## Prepare and verify locally

From `validation/`:

```sh
python3 test/native_fp.py prepare test/out/ia32-epyc-linux --seed 20261112 --count 10000
python3 -m unittest discover -s test -p 'test_native_fp.py'
python3 test/fp_model_check.py            # the model's side alone: x86fp --compat vs legacy mode
```

The first command builds `x86fp`, cross-compiles the freestanding native oracle
with the existing linker, generates inputs, and records Lean results locally.
It emits a tarball and the self-extracting paste script. Preparation never runs
physical hardware. Use another output name and seed for additional campaigns.

The optional smoke check requires the repository's existing x86-64 Linux guest
images and QEMU:

```sh
python3 test/native_fp.py prepare test/out/ia32-epyc-smoke --smoke --seed 20261112 --count 10000
python3 test/fp_smoke.py test/out/ia32-epyc-smoke test/out/ia32-epyc-smoke-tcg
```

It runs the actual oracle under Linux/TCG (`-cpu max`), every campaign in one boot (campaigns whose
CPUID features TCG lacks are skipped and listed; the cases QEMU aborts on, VEX.L = 1 of VROUNDSS/SD
and VEX.NP.0F C4, are left out), checks calibration, complete and well-formed output and that the
YMM upper halves are captured, and saves **all** TCG/model differences with a count per family.
On this commit: 2,604 cases in 26 campaigns, YMM state captured in every row, 7 campaigns skipped
(TCG lacks CLZERO, MONITORX, MCOMMIT, RDPRU, MisalignSse, XSAVEC, XSAVES), 527 differences, all in
families where TCG is known to differ. This is a runner check, not hardware evidence.
