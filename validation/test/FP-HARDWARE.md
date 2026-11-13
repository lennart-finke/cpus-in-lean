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

## The extended bundle (`ia32-epyc-ext`): one complete run against the final model

`ia32-epyc-ext` is the **whole** current bundle (seed 20261112, `--count 10000`): the 69 campaigns of the
earlier bundles (000–068: the 189,216 cases of both EPYC runs and `sse_rcp_sweep`, inputs bit-identical
to the earlier bundles, so `recompare --merge` with the earlier results stays possible) followed by
143 new campaigns (069–211) of the extended families, 863,642 cases in all. One run gives a
complete, self-consistent record against the final model.

| family | cases | what it adds | CPUID |
|---|---|---|---|
| (earlier) | 201,616 | campaigns 000–068 unchanged: the 189,216 cases of both EPYC runs and `sse_rcp_sweep` | as before |
| `enc_fuzz` | 210,930 | 069–111: encoding fuzz (`native_fuzz.py`): systematic every (map, mandatory prefix, opcode, ModRM.mod memory/register, ModRM.reg) of the one-byte, 0F, 0F 38, 0F 3A maps (65,536 slots) and every (VEX map 1..3, pp, L, W, opcode, mod, vvvv 1111b/other) (49,152 slots), 110,308 of the 114,688 slots selected; plus random prefix sequences (up to 14, repeated, any order), 2-/3-byte VEX with all fields, EVEX, XOP, 3DNow!, 16-bit addressing, encodings padded to 14..17 bytes. Every case single-steps (TF = 1) | none |
| `int_core` | 272,041 | 112–166: gen.py's random integer generator moved to the arena, defined flags per vector, undefined ones as observations, a quarter with read-only/unmapped pages | none |
| `int_directed` | 36,001 | 167–174: BCD (all AL), shifts/rotates (counts 0..33, 63, 255 at 8/16/32 bits), MUL/DIV with #DE, LOCK on every one-byte and 0F opcode, CMPXCHG/8B/XADD/XCHG, strings (REP 0..5, DF, page crossings), stack at page boundaries, every Jcc/SETcc/CMOVcc × 16 flag patterns, LOOP/JCXZ, LEA with all 32-bit ModRM/SIB and 16-bit forms, BT*/BSF/BSR, BOUND, RMW on read-only/unmapped/crossing pages, ARPL/VERR/VERW/LAR/LSL/SGDT/SIDT/SLDT/STR/SMSW (observe) | none |
| `shift16_rules` | 13,312 | 175–177: 16-bit SHLD/SHRD with every count 0..31 and nonzero operands, r16/m16, imm8/CL (G8); 8/16-bit shifts and rotates with every count 0..31 | none |
| `code16` | 6,383 | 178–179: a 16-bit code segment (LDT, `modify_ldt`): 147 directed forms × 16 and random encodings with TF | none (`modify_ldt`) |
| `fma_random` | 20,000 | 180–183: all FMA3 forms, operand classes (denormals, cancellation, near overflow/underflow, NaNs with distinct payloads in every position), every rounding mode, DAZ/FTZ, 1/6 unmasked | fma avx |
| `f16c_exhaustive` | 12,288 | 184–186: VCVTPH2PS of all 65,536 halves (8 per instruction), memory forms with random MXCSR, VCVTPS2PH in every imm8/MXCSR rounding mode to registers and memory, unmasked | f16c avx |
| `avx_unmasked` | 33,200 | 187–193: 32 AVX/AVX2/FMA FP forms × the six exceptions, one lane raising it (and a second kind in another lane), unmasked; VCVTPS2PH to memory | avx avx2 fma f16c |
| `sse_unmasked_ext` | 18,000 | 194–197: ADDSUBPS/PD, HADD/HSUB, ROUNDPS/PD/SS/SD, DPPS/DPPD likewise (CR4.OSXMMEXCPT = 0 cannot be observed natively: Linux sets it) | sse3 sse41 |
| `avx_random` | 30,375 | 198–204: every AVX/AVX2 form of gen_avx/gen_avx2 with random operands, memory at page boundaries with read-only/unmapped second pages, gathers faulting midway | avx avx2 fma f16c |
| `x87_control_load` | 2,304 | 205: FLDCW, FLDENV/FRSTOR (32/16-bit), FXRSTOR, XRSTOR with all reserved-bit classes of FCW (compared in full), FNSTCW/FNSTENV/FXSAVE stores of such a FCW (dumps) | xsave |
| `fxsave_align` | 280 | 206: FXSAVE/FXRSTOR/XSAVE/XSAVEOPT/XRSTOR, AC = 0/1, offsets mod 4/16/64, also crossing into an unmapped page | xsave xsaveopt |
| `xsave_padding` | 200 | 207: exact 64-byte dumps of FXSAVE/XSAVE/XSAVEOPT images (slot padding, reserved bytes, MXCSR_MASK, header, AVX area) over two arena fills | xsave xsaveopt |
| `x87_trans_special` | 6,400 | 208–209: FYL2XP1/FYL2X/FPATAN/F2XM1/FSCALE/FXTRACT/FPREM/FPREM1 × 20 special operands in both positions, masked/unmasked | none |
| `fenv16` | 128 | 210: 16-bit FNSTENV/FNSAVE/FLDENV/FRSTOR (and 32-bit) with dumps, TOP, ES = 0/1, nonzero input pointers | none |
| `fpu_pointers` | 184 | 211: nonzero input FIP/FDP/FOP, ES = 0/1, under non-x87, x87 non-control (with and without memory operands, unmasked exceptions), control and image-store instructions (dumps): F5, X6 | xsave |

### How to run it, what to return, how to compare

The paste script (`ia32-epyc-ext-paste.sh`, 77 MB) is copied to the machine and run as a file (it is too large to
paste into a terminal); the `.tar.gz` (57 MB) is the same bundle:

```sh
# on the EPYC (Python 3, x86-64 Linux; no root, KVM or compiler); about 4 GB of free disk
tar -xzf ia32-epyc-ext.tar.gz
python3 ia32-epyc-ext/native_fp.py run ia32-epyc-ext     # or: bash ia32-epyc-ext-paste.sh
# send back the results archive it names at the end: ia32-epyc-ext/results.tar.gz
```

The bundle's defaults are `--repeat 2 --pin auto` (below); `--repeat 1` halves the time. Expected time on
the 7742: about 10–20 minutes (1.73 million case executions at the first run's ~5,000 per second, plus the dry runs and the comparison of the passes). The bundle carries **no model results** (they would double its size): the target does
not compare; at home, after unpacking the returned archive to `test/out/epyc-ext-returned/`:

```sh
python3 test/native_fp.py recompare test/out/ia32-epyc-ext --result test/out/epyc-ext-returned/results
python3 test/native_fp.py summary test/out/epyc-ext-returned/results-recompare-<model hash>
```

`recompare` runs the current model on the stored inputs; the manifest keeps the sha256 of every
campaign's model output at prepare time (`model_output_sha256`), and the comparison lists the campaigns
whose model results changed since (`model_changed_since_prepare`), so a comparison with the prepare-time
model is `recompare --model <that x86fp>` with an empty list. (`compare`, which needs stored model
results, refuses such a bundle with that advice.)

### Format 3

The new campaigns use format 3 inside an `ia32-fp-v2` bundle (manifest entry `format: 3`, count header
bits 63 and 62): each 776-byte v2 record is followed by a 128-byte extension (`native_ext.record3`;
`FpMain.lean` and `signal_oracle.c` document it): flags (bit 0: install the x87 FOP/FIP/FDP given here in
the signal frame; bit 1: report 64 arena bytes at a given offset), the FIP/FDP/FOP inputs in the 64-bit
layout of the frame, the dump offset, up to eight dword patches of the arena (value, offset, repeat count),
and the mode (0: the 32-bit code segment; 1: the 16-bit code segment of `code16`). Native rows add the
64-bit FIP and FDP and the eight dump quadwords (110 columns), model rows FIP, FDP, CR2 of a #PF and the
dump (82); the comparison then also checks CR2 of every #PF and the dump. Per-case metadata decides what
is not strict: `flags_observe` (documented-undefined flags: compared, reported as the field
`eflags.undefined`, an observation), `observe_fields` (fields whose value depends on the OS, the machine
or time; `*` all), `compare_pointers` (FOP/FIP/FDP, otherwise excluded as before), `fcw_full` (the control
word's reserved bits). The earlier campaigns stay format 2, bit for bit.

### Safety: what can go wrong in a real user's process, and what prevents it

The extended families execute encodings nobody chose (the fuzz) and integer instructions with arbitrary
operands natively. The threats and the measures:

1. **Leaving the sandbox through the kernel.** The oracle's own validation (`native/record_check.h`,
   run before every case, by `oracle check` before every campaign and by `prepare` on every record) refuses
   INT 80h, SYSCALL, SYSENTER outside AMD, far JMP/CALL/RET, IRET, loads of DS/ES/FS/GS, and now every
   software interrupt (INT n, INT3, INTO, ICEBP: they enter the kernel's IDT, and the model has none), and
   MOV/POP SS with EFLAGS.TF (the held single-step trap would be taken on the kernel's INT3 entry, the
   CVE-2018-8897 pattern: Linux survives it but logs a warning). Privileged instructions (HLT, CLI, MOV
   CRn, IN/OUT, LGDT, WBINVD, ...) are ordinary #GP/#UD faults; SGDT/SIDT/SMSW/SLDT/STR are emulated by
   Linux under UMIP (dummy values, a rate-limited log line), observe-only.
2. **Running more than the case's instruction.** A record longer than its instruction would run the rest
   as further, unvalidated instructions. The validator decodes the instruction with the model's layout
   (`rc_decode`, checked against the model's decoded length and the Python `native_ext.layout` on 3,000
   random encodings by the unit tests) and refuses trailing bytes unless EFLAGS.TF = 1. **Every
   `enc_fuzz` case runs with TF = 1**: whatever length the processor decodes, it stops after one
   instruction (#DB, SIGTRAP), and a REP instruction after one iteration. `x86fp` reports the single-step
   trap as vector 1 (`stepInstr`'s rule) and continues REP instructions without TF to completion, as the
   processor does (both changes leave the 201,616 earlier cases' model results unchanged).
3. **Control transfers out of the code page.** A near JMP/CALL/Jcc/LOOP/JCXZ/RET or an indirect JMP/CALL
   whose target is not the INT3 filling of the code page is refused: the target is computed from the
   instruction, the GPRs or the arena (whose content follows from the record's seed and patches); a target
   in the oracle's image would execute its 64-bit code as 32-bit code (its `syscall` bytes included), a
   target inside the instruction would loop. An operand certain to fault (an unmapped arena page, below
   the arena) is accepted.
4. **Stray memory accesses.** Below 4 GiB the oracle process has only the 8 KiB arena (0x10000), the code
   page (0x20000, read/execute) and its own image (0x100000, one RWX ELF segment); its stacks, the alternate
   signal stack, the vDSO and vvar are above 4 GiB, out of reach of 32-bit addresses (checked at startup:
   the oracle audits `/proc/self/maps` and stops if anything else is mapped below 4 GiB or a stack is below
   4 GiB). The model now has exactly that address space (`FpMain.lean`): only the arena pages (with the
   record's permissions) and the read-only code page (0xCC outside the instruction, as natively) are mapped,
   so a model access anywhere else is a #PF with its CR2 (the same result as the processor's, unless the
   address is the oracle image). A case is included only if, in the model, every access is inside the low
   256 KiB (#PF CR2 < 0x40000; `native_ext.select` for the selected families, `model_problems` for every
   format-3 campaign). Since the processor may decode a fuzzed encoding differently from the model (that
   is what is being tested), the **inputs** are bounded too: in `enc_fuzz` every GPR is an arena address
   or below 0x100 (ECX ≤ 63), so base + 8 × index < 0xA2000; no four bytes of the instruction and its 0xCC
   filling form a dword in [0x50000, 0x1200000) (any displacement or immediate a decoding could use stays
   below the image); every XMM/YMM dword lies in [−0x4000, 0x4000) (gather indices). FS and GS now hold
   the flat data selector 0x2B in the oracle (as DS and ES; the freestanding oracle has no TLS), so a
   segment override addresses what the model's flat FS/GS address (checked by a calibration case).
5. **Silent corruption of the oracle.** While the instruction runs, the oracle's image is read/execute
   only (the signal handler re-enables writes as its first action and protects the image just before it
   returns into the instruction): a stray store faults, and the oracle stops with *the instruction accessed
   the oracle image*. In addition an **integrity canary**: a digest of the whole image (text, data,
   bss) is taken just before the instruction and checked just after it; a change stops the oracle with
   *the oracle image changed while the instruction ran*. A stray read of the image cannot change anything
   and shows as a difference (the model faults there). Both stops are failed cases: the runner records
   them and restarts the oracle after them. The smoke run proves both: a record storing into the middle of
   the image is stopped by the write protection, and, with the protection off (`oracle i386-unguarded`, a
   test mode), by the canary.
6. **State leaking between cases.** Each case is entered and left through rt_sigreturn with the complete
   register, x87, SSE and AVX state from the frame; MXCSR, FCW and the x87 stack are restored for the
   runner from the saved recovery frame; FXRSTOR/XRSTOR/FLDENV/LDMXCSR of random memory change only the
   case's state. Segment loads are refused (DS/ES/FS/GS) or restored by sigreturn (SS, UC_STRICT_RESTORE_SS);
   in `code16` the runner sets DS/ES around the case itself.
7. **Hangs.** With TF one instruction runs; REP counts are small (ECX ≤ 63 in the fuzz, ≤ 5 directed,
   gen.py's 0..8), and every string instruction leaves the 8 KiB arena (and faults) after at most 8,192
   iterations; MWAITX waits at most until the next interrupt or for EBX TSC ticks (EBX < 0x12000 in the
   fuzz); jumps into the instruction itself are refused. A hang would still be only a 120 s timeout of one
   case.

### Determinism: `run --repeat 2 --pin auto`

Every campaign runs twice, each pass pinned (`os.sched_setaffinity`) to its own logical CPU, chosen from
two different physical cores (`/proc/cpuinfo` physical id and core id; without them two different CPUs; on
one CPU that one twice); `hardware.json` records the CPUs (`repeat`) and per campaign and pass the CPU,
the output hash, whether the outputs are identical and every differing case with its fields. The first
pass is compared with the model, the second only with the first (byte-identical second outputs are not
kept). A difference is expected only in a case's observe fields (RDTSC, RDTSCP, RDPID, RDRAND, CPUID's
APIC IDs, ...; EFLAGS.RF and a stale CR2 are ignored); any other counts as a failure of the comparison.

### What the selection left out (the blind spots)

The model-in-the-loop selection (`native_ext.select`; counts in the manifest, `selection`) refused, of
224,687 `enc_fuzz` candidates, 13,757 (6.1%): 5,310 segment loads (LES/LDS memory forms of C4/C5, MOV/POP to
DS/ES/FS/GS, LFS/LGS), 1,568 near transfers whose target is not the INT3 filling (indirect via random memory,
relative targets inside the instruction), 1,319 software interrupts and 1 INT 80h, 745 far transfers/IRET,
147 SYSCALL, 155 MOV/POP SS with trailing bytes or TF, and 4,512 whose model access lies outside the low
256 KiB (random disp32 between 0x40000 and the forbidden window). Of `int_core`'s 279,319 candidates 7,278
(segment loads 7,176, POP/MOV SS with TF 97, trailing bytes 5); of `int_directed` 195; of `code16` 385.
So the native fuzz does **not** cover: segment-register loads of DS/ES/FS/GS (and SS only as 'observe'),
far transfers and IRET, software interrupts, SYSCALL/INT 80h, near transfers to anywhere but the code page's
INT3 filling, MOV/POP SS under TF, and memory operands outside the arena (they appear only as #PF cases
below 256 KiB). Of the remaining fuzz cases 73.4% are #UD, 17.4% execute (#DB), 5.1% #GP (the length limit
among them), 3.3% #PF, 0.6% #AC, 0.2% #XM; of `int_core` 77.5% execute, 7.0% #GP, 6.9% #PF, 6.0% #UD,
2.4% #AC. Instructions whose result depends on the OS, the machine or time get observe fields
(`native_ext.os_dependent`): CPUID (EAX..EDX), RDTSC/RDTSCP/RDPRU, RDRAND/RDSEED/RDPID, RDPMC, the SVM
instructions (EFER.SVME follows KVM), SGDT/SIDT/SMSW/SLDT/STR/VERR/VERW/LAR/LSL and SS loads (every field).

### Smoke run (QEMU/TCG, not hardware evidence)

`fp_smoke.py` on the `--smoke` bundle of the same commit (11,724 cases: 2 per family and instruction, a
hash-chosen share of the large families) with a guest kernel that has `modify_ldt` (`--kernel`: the
tinyconfig guest of `../x86_64/guest/` plus `CONFIG_MODIFY_LDT_SYSCALL=y`, `CONFIG_X86_16BIT=y`; with the
plain guest the `code16` campaign stops at `modify_ldt` and is reported as skipped): 11,674 complete
observations in 43 campaigns, YMM state in every row, 0 errors; the oracle's mapping audit passed in all 52
runs; `oracle layout` equals the ELF; the canary record is stopped by the write protection (guarded) and by
the integrity digest (unguarded); the 21 probe records are reported by the guest as by the host build; the
second passes of the 16 format-3 campaigns are identical except 1 case in its observe fields; the
16-bit code segment ran (CS 07h rows). FUZZ_TCG 1,826 TCG/model differences, all in classes where TCG is known to
differ (no #XM for unmasked SIMD exceptions, no #AC, the 16-byte limit #UD, RMW error codes, AAM bases,
3DNow!/VEX.NP forms TCG executes, x87 stack faults, the SHLD/SHRD 16-bit rule), except one model issue:
ENTER with a 16-bit operand size and a 32-bit stack writes all of EBP (README, open question G10).

## The first EPYC 7742 run, and the resume bundle

The first run of the full bundle (`ia32-epyc-linux`, seed 20261112, `--count 10000`: 189,240 cases in
66 campaigns) on a bare-metal EPYC 7742 (Linux 6.8) **executed 137,144 of the 189,240 cases**:
campaigns 000–034 completed; campaign 035 (`gpr_cache`: CLFLUSH, CLFLUSHOPT, CLWB, the prefetches)
stopped at its tenth case with `ERROR: unsupported data permission (value/negative errno:
0000000000000045)`, and campaigns 036–065 (52,096 cases: the rest of the GPR extensions, SSE3..SSE4a,
MisalignSse, XSAVE, AVX, AVX2/FMA/F16C, `longmode`, `open_questions`) never ran. The runner of that
bundle ended the whole run at the first failed batch, and its `compare` then refused the whole result.

The cause: `gpr_cases.cache_cases` gave the data page the PTE value 0x45 (present, user, read-only,
accessed bit clear) to ask whether a flush sets the accessed bit. The native oracle realises the data
page with `munmap`/`mprotect` and accepts only 0 (unmapped), 0x65 (read-only) and 0x67 (writable): a user
process can neither clear nor observe an accessed bit, and the comparison does not include page-table
entries, so natively that case was the read-only case again. The 24 PTE-0x45 cases are gone (the
accessed-bit question belongs to the QEMU/KVM tests, which compare page-table entries); campaign 035 now
has 72 cases. The TCG smoke run did not catch it because TCG lacks CLWB, so the campaign was skipped
there. What makes this class of failure impossible now (below): the oracle's own input validation runs
on every record when a bundle is prepared, a dry run of it precedes every campaign on the target, and
the runner no longer stops at a failed campaign or case.

**Results of the first run (pending triage).** The comparison of the partial result (`compare` and
`recompare` take partial results now) covers 137,153 cases: campaigns 000–034 and the 9 complete rows
campaign 035 wrote before it stopped; 717 strict mismatches and 656 observations, in `alignment_check`
(43), `gpr_bmi` (40, RORX), `sha` (28), `x87_exceptions` (223), `x87_memory` (48), `x87_random` (215),
`x87_transcendental` (120 strict, 200 observations), `x87_trans_boundary` (118 observations) and
`sse_random` (338 observations: RCP/RSQRT); every other family of those campaigns agrees exactly. These
differences are being triaged; none is classified here.

**The resume bundle** runs only what has not run: campaign 035 (fixed) and campaigns 036–065, 52,072
cases in 31 campaigns, with the campaign numbering of the first bundle. `prepare --resume` regenerated
all 66 campaigns from the same seed and count and checked that the inputs of every campaign the first
run completed (000–034) are bit-identical (their `.bin` sha256 equal the first manifest's; the inputs of
036–065 are identical too, and 035 is the first bundle's minus its 24 PTE-0x45 records), so the two
results combine into one comparison. It was prepared with

```sh
python3 test/native_fp.py prepare test/out/ia32-epyc-resume --seed 20261112 --count 10000 \
    --resume test/out/ia32-epyc-linux test/out/epyc-returned/results
```

and is `test/out/ia32-epyc-resume-paste.sh` (8.7 MB, sha256 `e7cb0ba2fedb6a6cadf8f2f211f4726519edfb16d6c9cec37db5a1314bb15719`). On the EPYC:

```sh
bash ia32-epyc-resume-paste.sh
```

and send back the `results.tar.gz` it names at the end. Then, here (after unpacking the archive to, say,
`test/out/epyc-resume-returned/`; `unpack` recreates the exact bundle from the paste script if the
`ia32-epyc-resume` directory is not at hand):

```sh
python3 test/native_fp.py unpack test/out/ia32-epyc-resume-paste.sh          # only if needed
python3 test/native_fp.py recompare test/out/ia32-epyc-resume --result test/out/epyc-resume-returned/results \
    --merge test/out/ia32-epyc-linux test/out/epyc-returned/results
```

which compares all 189,216 cases of both runs with the current model (each campaign from the run that
completed it).

## Run on the Linux box

The prepared paste script is self-contained. Copy it to the Linux box and run it, e.g.:

```sh
bash ia32-epyc-resume-paste.sh
```

Alternatively, paste the entire contents of that script into a Bash terminal.
It creates a fresh directory under `/tmp`, unpacks the bundle and runs it.
The script needs **Python 3 and x86-64 Linux with IA-32 compatibility enabled**.
It does not need root, KVM, ptrace, a compiler, multilib libraries, Lean, or a
network connection. The executable is a freestanding ELF64 process that enters
32-bit mode through Linux signal return. Signal handlers use an alternate stack.

If using the smaller `.tar.gz` bundle instead:

```sh
tar -xzf ia32-epyc-resume.tar.gz
python3 ia32-epyc-resume/native_fp.py run ia32-epyc-resume
```

The runner prints the results directory and `results.tar.gz` location. Return
that archive; it includes the CPU identity/microcode information from
`/proc/cpuinfo`, kernel version, complete raw observations, calibration logs,
per-case differences and a summary. On the 7742 a 5,000-case batch takes about 1 s (the 137,144 cases
of the first run: 29 s); allow about 1 GB of free disk space
(the unpacked full bundle is 402 MB, the raw results about as much again; the resume bundle is about a
third of that). The timeout is 120 seconds **per oracle process** (`--timeout` to change it). A run on a
VM records the guest CPU environment; use a bare-metal host when collecting physical-CPU evidence.

### Partial runs: nothing stops the run, nothing is dropped

For every campaign the runner first runs `oracle check` (the oracle's input validation alone, a dry
run on this machine: nothing executes). A record it refuses is recorded (index, value, reason) and
skipped; the other records run. If the oracle process exits or times out during a case, the rows it
wrote before are kept, that case is recorded as failed (exit status or timeout, the end of its log), and
the oracle is restarted on the remaining cases; after 50 failed cases or 3 timeouts in one campaign the
rest of it is recorded as not run. A campaign that fails before its first case (calibration), or an
error of the runner itself, is recorded and the run continues with the next campaign. `hardware.json`
holds per campaign `status` (`ok`, `partial`, `failed`, `error`), `rejected`, `failed_cases`,
`not_run` and the output hash; `<campaign>.out` holds the rows of every executed case with its
campaign index (the oracle's own outputs are kept as `<campaign>.raw` / `.partN.raw` with their logs
when a campaign needed more than one process). The run exits 1 when any campaign is not complete.

`compare` and `recompare` compare every observed case, also of partial and failed campaigns (results of
the first runner too: the complete rows a failed batch wrote before it stopped count, the case it stopped
on is reported as failed and the rest as not run), and list everything not compared, by campaign and
reason, in `comparison.json` (`not_compared`, `incomplete_campaigns`, per campaign `not_compared` with
index ranges) and in `summary.txt`. A damaged or modified result or input is still refused.

Exit status:

- `0`: all compared defined fields agree exactly, and every case of the bundle(s) was compared.
- `1`: strict mismatches, cases without a hardware observation (refused, failed, not run), malformed
  output or damaged inputs.
- `2`: only approximation/domain differences remain; review is required.

`comparison.json` summarizes results, per campaign and per family. `mismatches.jsonl` contains each
differing case's campaign name, batch-local index, opcode, family, control settings where applicable,
and hardware/model values; `summary.txt` counts them by family, by family and instruction and by
differing field, with example case ids (`campaign:index`). The matching `.bin` record contains every
input bit; the batch name identifies the corresponding input and raw output files.
No failed record is rewritten using a model answer or a QEMU deviation rule.

### Comparing again: recompare, merge, summary

```sh
python3 test/native_fp.py compare   BUNDLE --result RES [--merge BUNDLE2 RES2]... [--out OUT]
python3 test/native_fp.py recompare BUNDLE --result RES [--merge BUNDLE2 RES2]... [--out OUT] [--model X86FP]
python3 test/native_fp.py summary   OUT
python3 test/native_fp.py unpack    PASTE_SCRIPT [--out DIR]
```

`compare` uses the model results stored in the bundle (the model at `prepare` time). `recompare` runs
the **current** model (`lake build x86fp`, or `--model`) with the bundle's `model_args` (`--compat`) on
the bundle's stored `.bin` inputs, after checking every bundle file against its manifest sha256, and
compares with the stored hardware outputs: model fixes are checked against existing hardware results
without a new hardware run. It writes nothing into the bundle or the results; the comparison
(`comparison.json`, `mismatches.jsonl`, `summary.txt`) goes to `--out`, by default
`<RES>-recompare-<first 12 hex digits of the model's sha256>` next to the results. `--merge` adds further
(bundle, results) pairs, e.g. the first run to a resume run; each campaign (by name) is taken from the
run that observed most of it, its source is recorded, and campaigns no run completed are listed.
`compare` writes into the results directory for a single run (as `run` does), else to
`<RES>-combined`. `summary` prints `summary.txt` again (`--examples N`). `unpack` extracts the exact
bundle a paste script carries.

### Input validation: what the oracle accepts

`native/record_check.h` is the oracle's input validation, one source used three ways: the oracle checks
every record before it runs it (and stops with the reason if refused), `oracle check` runs it alone over
a campaign (the runner's dry run), and `prepare` compiles it for the host (`native/check_records.c`,
with the target's vendor AMD and MisalignSse only for campaigns that require it) and runs it on every
campaign it writes: **a bundle with a record the oracle would refuse is not produced**. It accepts:
instruction length 1..15; data-page PTEs 0, 0x65, 0x67 only (`fp_cases.ORACLE_PTES`; `fp_cases.record`
asserts it too); EFLAGS with exactly IF and bit 1 outside the installable CF PF AF ZF SF TF DF OF AC;
MXCSR without bits 31:16 (bit 17, MM, only with MisalignSse: rt_sigreturn's XRSTOR would fault and kill
the process); FTW 0..0xFF; memory kinds 0..4; and no instruction that would leave the process's sandbox:
INT 80h and SYSCALL (real Linux system calls with whatever is in EAX), SYSENTER unless the processor is
AMD, far JMP/CALL/RET and IRET, and loads of DS/ES/FS/GS (64-bit rt_sigreturn does not restore them,
so they would leak into the following cases). `prepare` also refuses a case whose model result the
oracle could not observe: an exception vector without a Linux signal the oracle handles
(`native_fp.VECTOR_SIGNAL`: #DE #MF #XM SIGFPE, #DB #BP SIGTRAP, #OF #BR #GP #PF SIGSEGV, #UD SIGILL,
#NP #SS #AC SIGBUS), or an instruction pointer outside the oracle's code page (`test/fp_model_check.py`
checks the same for every case). A hardware row with a signal/vector pair outside that table is a strict
mismatch (field `signal/mode`), not an error. Unit tests (`test_native_fp.py`) compile the checker and
probe each rule, check that every generated record of every family passes, and scan
`signal_oracle.c` for the include, the check before the case runs, the PTE values and the handled
signals.

### What runs natively (audit of the families of campaigns 035–065)

The TCG smoke cannot run the instructions TCG lacks (CLZERO, MONITORX/MWAITX, MCOMMIT, RDPRU,
MisalignSse, XSAVEC, XSAVES), so every family of campaigns 035–065 was audited for what the EPYC does
with it in a user process under 64-bit Linux, using the model's result for every case (vector, final
EIP) and the encodings: no case is a system call, a far transfer or a segment load; every model result
ends inside the code page with a vector in the table above; and no case touches memory outside the
model's 256 KiB identity map (the native process has nothing else mapped below 1 MiB, and the oracle
image at 1 MiB is out of reach). Per family:

- `gpr_cache` (035): CLFLUSH/CLFLUSHOPT/CLWB on writable/read-only/unmapped pages (#PF only unmapped),
  prefetches (never fault). Fixed as above.
- `gpr_clzero` (036): CLZERO zeroes the 64-byte line at EAX in the arena; #PF on the read-only and
  unmapped page.
- `gpr_monitorx` (037): MONITORX/MWAITX are allowed at CPL 3 on AMD. MWAITX without the timer waits at
  most until the next interrupt (or a store to the monitored line; the oracle writes the arena before
  every case); the timer cases use 1,000 TSC ticks; ECX bits 31:2 give #GP. A hang would be a timeout of
  one case, recorded, and the run continues.
- `gpr_system` (038): MONITOR/MWAIT #UD at CPL 3 (MSR C001_0015[MonMwaitUserEn] = 0 under Linux),
  WBNOINVD #GP at CPL 3, MCOMMIT #UD (Linux leaves EFER.MCOMMIT clear; the 7742 reports MCOMMIT), the
  RDRAND/RDSEED/RDPID #UD forms.
- `gpr_rdpru` (039): RDPRU with unsupported register numbers (CR4.TSD = 0 under Linux): EDX:EAX = 0.
- SSE3..SSE4a (040–048): ordinary data instructions on the arena.
- `misalign_sse` (049): MXCSR.MM = 1 is installed through the signal frame; the 7742 reports MisalignSse
  (MXCSR_MASK bit 17). Gated on `misalignSse`; on a processor without it `oracle check` refuses these
  records (skipped and reported, as in the TCG smoke) instead of letting rt_sigreturn fail.
- XSAVE (050–052): XSAVE/XSAVEOPT/XSAVEC images in the 8 KiB arena (at most 832 bytes with XCR0 = 7),
  XRSTOR of crafted headers (#GP), XGETBV, XSETBV and XSAVES/XRSTORS at CPL 3 (#GP).
- AVX, AVX2/FMA/F16C (053–062): data instructions, masked moves and gathers on the arena (page faults
  only on the arena's read-only/unmapped page), invalid encodings (#UD).
- `longmode` (063): SYSENTER and SYSEXIT are #UD in long mode on AMD (APM vol. 3); on a non-AMD processor
  SYSENTER from compatibility mode would be a real system call, so `oracle check` refuses it there. SYSRET
  at CPL 3 is #GP, SWAPGS and the FSGSBASE instructions are #UD outside 64-bit mode, INC/DEC 40–4F,
  LAHF/SAHF, ARPL and BOUND (#BR) execute. SYSCALL is not in the family: from compatibility mode on AMD
  it is a real Linux system call (CSTAR), with the number in EAX.
- `open_questions` (064–065): 15/16-byte encodings (#UD/#GP), EVEX/XOP-like encodings (#UD on Zen 2;
  should the 7742 execute the XOP form, it is a register-only operation), SHLD/SHRD, LOCK MOV CRn at
  CPL 3 (#GP/#UD), x87 NaN cases, XGETBV with prefixes (#UD) and with ECX = 3 (#GP).

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
python3 ia32-epyc-resume/native_fp.py run ia32-epyc-resume --result run-2
```

## Coverage

A full bundle (seed 20261112, `--count 10000`) now has 189,216 independent single-instruction cases
(the first one had 189,240, with the 24 PTE-0x45 cases) in 76 families, split into campaigns
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
with the existing linker, generates inputs, validates every record with the oracle's own check (host
build) and every model result for observability, and records Lean results locally (it stops, with the
offending cases, before producing anything the oracle could not run).
It emits a tarball and the self-extracting paste script. Preparation never runs
physical hardware. Use another output name and seed for additional campaigns.
`--only 035-065` puts only those campaigns into the bundle (all are generated, keeping the numbering;
the others are listed in the manifest with their input hash, `included: false`); `--resume BUNDLE
RESULT` includes exactly the campaigns without a complete run in RESULT and refuses to prepare anything
if a campaign that did run would not regenerate bit-identically (seed and count must be the earlier
bundle's). The run of such a bundle skips the left-out campaigns; its comparison lists them as not in
the bundle ("compare together with the earlier run") without counting them as failures.

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
It runs `oracle check` on every campaign and on 13 probe records (one per refusal rule, plus SYSENTER,
MXCSR.MM and a valid record), whose report must equal the host build's for the guest's vendor and
MisalignSse bit, and checks that `oracle i386` stops at a refused first record with its reason before
executing it. The campaigns TCG lacks features for are not compared but still executed, so the oracle
must survive them (TCG raises #UD for them).
On this commit: 2,604 cases in 26 campaigns, YMM state captured in every row, 7 campaigns skipped
(TCG lacks CLZERO, MONITORX, MCOMMIT, RDPRU, MisalignSse, XSAVEC, XSAVES; all but MisalignSse executed
anyway with the oracle surviving them; `oracle check` refuses the MisalignSse records on TCG, as it
must on a processor without MisalignSse), 527 differences, all in families where TCG is known to
differ; the probe records reported exactly as by the host build (TCG `-cpu max` reports AuthenticAMD,
so SYSENTER is accepted). This is a runner check, not hardware evidence: the runner's case-level
recovery (restarts after a failed or hanging case) needs Python on the target and is tested with a
stand-in oracle in `test_native_fp.py`.
