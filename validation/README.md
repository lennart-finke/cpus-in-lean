# Validation

Evidence that the [IA-32 model](../x86_32/README.md) behaves like 32-bit mode on an AMD EPYC 7742, plus the hardware tests for both models. `x86run` boots Linux, `x86test` replays single-instruction vectors, `x86sys` runs the system-test kernel, `x86fp` runs the native campaign's cases on the model, `x86bridge` hands the model's stops in 64-bit mode to the x86-64 model, and `x86litmus` explores concurrent executions; nothing here is imported by the model or its proofs.

```
$ lake build
$ ./verify.sh [N]          # the gate (N random QEMU vectors, default 20000): steps 1-9 below
$ ./verify.sh --full [N]   # also the whole native campaign on the model, more reference cases, SMP Linux
```

`../verify.sh` (repository root) runs `x86_32/verify.sh`, the IA-32 steps that need no Linux image and the x86-64 model's checks with separate verdicts (`--full`: everything, including both Linux boots). Each step prints one result line; the first failing step stops the run.

| step | what | current result (this commit) |
|---|---|---|
| 1 | build the runners | `x86run x86test x86sys x86litmus x86fp x86bridge` |
| 1a, 1b | x86-TSO litmus tests; TSO access log on 20,000 vectors | pinned outcome sets, 0 different; 0 failures |
| 2 | random single instructions against QEMU (`test/run.sh N SEED`) | ten seeds × 20,000 vectors (101..110): 0 mismatches; per run ≈ 1,120 QEMU deviations accepted by rule (≈ 680 the EXTRQ/INSERTQ upper-half rule, ≈ 60 the save-area #PF rule) and ≈ 470 16-byte encodings checked as #GP(0) (D1) |
| 3 | system tests against QEMU (`test/sys/run.sh`): main, 2-CPU and long-mode passes | 30,672 / 39 / 2,386 lines identical to QEMU after 124 deviation rules (+ 382 x87 transcendental rules and the RCP/RSQRT rules); 551 / 20 / 6 model-only lines as expected; all six transcripts end with `END` |
| 4 | independent references (`test/refs.py`) | 5 regenerated tables identical (xsaveref, vmeref, svmref, cryptoref, x87ref); 4 self-tests; sse_ref 2,330, avx_ref 1,503, avx2_ref 2,500 transcript lines, 0 mismatches; gpr_ref 5,400 cases, 0 differ; topo_ref for 2, 3, 4, 16 CPUs (64, 128 with `--full`), 0 differences |
| 5 | native campaign on the model (`test/fp_model_check.py`) | smoke sample 2,654 cases in 76 families, `x86fp --compat` and legacy mode complete and identical outside the `longmode` family; `--full`: the whole campaign of both bundles (863,875 cases in 93 families, 0 compat/legacy differences outside `longmode` and the 1,075 compatibility-mode-specific cases of the extended families) |
| 6 | long-mode bridge (`x86bridge --cmdline long=1`) | 1,108 stops in 64-bit mode, 1,106 continued identically by the x86-64 model, 2 differences that are the x86-64 model's (below) |
| 7 | unit tests (`python3 -m unittest discover -s test`) | 130 tests OK, including the CPUID table check (`test_cpuid_table.py`) and the LLVM cross-check of the instruction forms (`test_isa_forms.py`) |
| 8 | Linux boot | 54,168,267 instructions, ≈ 12 s |
| 9 | workload against QEMU (`guest/workload.qemu.txt`, `guest/qemu-workload.sh`) | 20 lines byte-identical; 116,169,202 instructions, ≈ 28 s |
| 10 (`--full`) | SMP Linux against QEMU (`guest/smp-check.sh`) | identical transcripts for 2 CPUs (quanta 100, 1000, 20000, 10⁶), 4 (1000, 20000), 8, and 16 (`bzImage-bigsmp`); 32 CPUs boot on the model (all 32 online, workload identical) but have no QEMU reference (SeaBIOS writes no MP table for 32 CPUs) |
| 11 (`--full`) | Linux's CPU topology against `topo_ref.py` (`guest/topo-check.sh`) | 4 CPUs, and 16 and 64 CPUs with `bzImage-bigsmp`: 0 differences |

`x86run` options: `--mem MB`, `--max N` (instruction limit), `--smp N` (N CPUs and MP tables; `--quantum Q` steps per scheduling turn), `--cpuid` (print the CPUID table, `test/cpuid_table.py`); `x86sys` also takes `--smp N`, `--quantum Q`, `--cmdline STR`, `--expect PAT --send TEXT` (scripted input; `@exit` stops) and `--trace-from N --trace-count K` (register trace on stderr).

The evidence: QEMU's TCG (an EPYC-Rome CPU, `test/qemu-cpu.sh`) where it follows the manuals, rewritten by a cited rule where it does not; independent Python references written from the manuals; Linux; and a real EPYC 7742 (Hardware tests), which takes precedence: the integer core in earlier campaigns, all 189,216 cases of the user-mode bundle and the 863,642 of the extended bundle, each at 0 strict mismatches after the fixes they prompted. The privileged open questions need the KVM harness, which has not run.

## QEMU differential tests
`test/run.sh N SEED` generates N random single instructions (random prefixes, operands, registers, flags, selectors and page-table bits, page-crossing operands, single-stepping). A small kernel (`test/harness/`) runs each under `qemu-system-i386` in ring 3; `x86test` runs it on the model and compares exception, CR2, registers, flags, selectors, a memory hash, page-table entries and (format v2) MXCSR, XMM0–7 and the YMM upper halves. Forms TCG executes that the model does not implement yet are listed in `test/isa_forms.py` and not generated. Encodings that are #UD on Zen 2 (unassigned 0F 38/0F 3A/VEX opcodes, VEX after 66/F2/F3/LOCK, unknown VEX maps, EVEX/XOP register forms) are generated, also padded to the 15-byte limit; for a 16-byte one TCG raises #UD where the model raises #GP(0) (SDM vol. 3, table 6-2), counted separately. Extending the tests: `../x86_32/EXTENDING.md`.

The ten runs of step 2 together: 11,232 QEMU deviations accepted by `qemuAsHardware` (about 6,800 of them EXTRQ/INSERTQ clearing bits 127:64) and 4,702 16-byte encodings; `SEED=7742 ./verify.sh --full`: 0 mismatches, 1,100 accepted, 476 16-byte encodings. Each run prints the distinct undefined encodings the 'ud' family emitted per map (seed 101: 0F 100, 0F 38 273, 0F 3A 264, VEX.0F 160, VEX.0F38 196, VEX.0F3A 205, unknown VEX maps 262, VEX after a legacy prefix 247, 62/8F 16, 499 of the 1,486 undefined VEX neighbours). `test_isa_forms.py` checks with LLVM (`-mcpu=znver2`) that every `IMPLEMENTED` form (135 rows, 87,834 encodings) disassembles and none of 194,300 undefined encodings does, apart from 13 listed, cited classes. `x86test` fails when not every input vector was compared.

Families beyond the base integer/x87/SSE generator (each an 'ext' family; share of the vectors in parentheses):

- **Crypto** (`test/gen_crypto.py`, about 18%): AES-NI, PCLMULQDQ, SHA with every imm8, misaligned operands (SHA executes them on the 7742 and in TCG, not the SDM's class-4 #GP), LOCK; also checked against `test/cryptoref.py`, written from FIPS-197, FIPS 180-4, the GCM specification and the SDM (`run.sh` prints how many of QEMU's results it checked).
- **GPR extensions** (`test/gen_gpr.py`, about 18%): POPCNT, LZCNT, TZCNT, BMI1/BMI2 with every encoding neighbour, ADCX/ADOX, MOVBE, CRC32, prefetches, RDPID, CLFLUSH/CLFLUSHOPT/CLWB with paging off, the #UD/#GP forms of RDRAND/RDSEED, RDPMC, MONITOR/MWAIT, MCOMMIT; also checked against `test/gpr_ref.py` (from the APM/SDM; `python3 test/gpr_ref.py check`, also a unit test). Not compared with QEMU (TCG lacks them or has no defined value): RDRAND/RDSEED/RDTSCP/RDPRU results, CLZERO, MONITORX/MWAITX, WBNOINVD at CPL 3, CLFLUSH page faults and accessed bits, RDPID/RDTSCP with 66.
- **System forms** (`test/gen_sys.py`, about 2%): SYSCALL, SYSRET, SYSENTER, SYSEXIT, CLAC, STAC, LOCK MOV CR at CPL 3 (#UD/#GP rules).
- **AVX** (`x86_32/X86/Ext/Avx.lean`, `Vex.lean`; `test/gen_avx.py`, about 10%): every form in VEX.128/256, all addressing modes, misaligned and page-crossing operands, a tenth breaking one encoding rule; YMM upper halves compared. The 'ud' family tests every undefined VEX neighbour (rows carry VEX.L and VEX.W) and walks all of `isa_forms.vex_neighbours()` in turn (kind `vexnb`, about 2.5%). VMIN/VMAX run with DAZ clear. Not generated (system tests cover them): VEX.L = 1 of VMOVSS/SD and VCVTSI2Sx (TCG keeps bits 255:128) and of VROUNDSS/SD (QEMU 11.1.2 aborts in `gen_VROUNDSx`), VEX.NP.0F C4 (aborts in `gen_pinsr`), is4 imm8[7] = 1, VRCPPS/VRSQRTPS, two NaN sources, VMASKMOVPS/PD loads with paging.
- **AVX2, FMA3, F16C** (`x86_32/X86/Ext/Avx2.lean`; `test/gen_avx2.py`, about 9%): every form of the exact `isa_forms.IMPLEMENTED` rows with their variants, a tenth breaking one encoding rule, gathers with every VSIB scale, with and without a base, data seeds chosen so selected elements address the data area; the 'ud' family tests every undefined neighbour and the FMA4 opcodes. Not generated (system tests): VPMASKMOV loads with paging, VEX.L = 1 of scalar FMA, VCVTPS2PH with FTZ (TCG flushes; AMD: no effect), binary16 denormals into VCVTPH2PS (TCG applies DAZ and reports DE; AMD: neither).

`qemuAsHardware` accepts these AVX/AVX2 TCG deviations (`tcgVexUd`, citing the manuals): TCG executes forms that are #UD on the CPU (VEX.pp = 00 MMX opcodes, SSSE3 0F 38 00..1E, PALIGNR; legacy-only 66 0F 38 10/14/15, F3/F2 0F 2B, VEX.66/F3/F2.0F 77; VEX.L = 1 of VMOVD r/m32 and VMOVLPx/VMOVHPx stores; register forms of VMOVLPD/VMOVHPD/VMOVNTDQ/VMOVNTPx); it raises #UD for VEX.L = 1 of LIG scalar forms; its masked stores (VMASKMOVPS/PD, VMASKMOVDQU, VPMASKMOVD/Q) write elements before a #PF on a later one (accepted when the model left memory unchanged); it reads past the operand (32 bytes for the m128 of VCVTDQ2PD/VCVTPS2PD ymm and of VEX.256 shift counts, 16 for scalar FMA m32/m64; accepted when the architectural operand ends at or before QEMU's page-aligned CR2).

Left out of generation where QEMU deviates from the SDM: AAM/AAD with an immediate ≥ 80h, INVD/WBINVD at CPL 3, REP INS/OUTS with a zero count, REP with TF, the read order of CMPS. Accepted as hardware and counted separately: page faults on RMW operands (QEMU drops the W bit and sets A instead of A and D), and PUSHA, which QEMU probes as a whole instead of pushing in order.

### QEMU deviations by area

Where TCG differs from the manuals, the comparison uses the manual's result: a cited rule in `test/sys/qemu-deviations.txt` (system tests; 124 rules), a rule in `TestMain.qemuAsHardware` (single instructions: only TCG's signature of a known deviation is replaced, counted as "known QEMU deviations accepted"), the per-line rules of `test/sys/x87t-deviations.txt` (`x87ref.py`) and RCP/RSQRT rules (`test/zen2_rcp.py`, every run), or the form is not generated and a model-only check covers it. By area:

| area | rules | what TCG does differently |
|---|---|---|
| paging, PAE, TLB, long mode (`pae`, `pgf`, `pgt`, `npf`, `lmf`, `lm`) | 6 + 4 + 4 + 6 + 6 + 10 | reserved-bit #PF with P = 0, PDPTEs not checked/cached, 40 physical-address bits, long-mode activation and EFER checks (MOV CR0 with LME and PAE = 0, LMA writable), LTR/LAR/LSL with 16-byte descriptors in compatibility mode, SYSENTER/SYSEXIT in long mode, non-canonical FS_BASE/KernelGSbase, L = D = 1 code entered, A bit on faulting large leaves; RMW #PF error codes (`qemuAsHardware`) |
| system A (`sysa`) | 13 | SYSCALL/SYSRET SS RPL, CR8 and EFER/PAT/MTRRdefType reserved bits, EFER.LMSLE/FFXSR/TCE/INTWB dropped, SMAP with AC for implicit accesses; SYSRET's CPL check before EFER.SCE (`qemuAsHardware`) |
| exceptions, tasks, gates, debug (`dfc`, `db`, `task`, `tsf`, `cgf`, `dbf`) | 10 + 5 + 1 + 1 + 2 + 1, and 1 for `tsf` and `cgf` | no EXT bit, #TS for a not-present SS0, MOV SS trap delay, data breakpoints in REP, faults after the task-switch commit point, #TS for TSS selectors with TI = 1, #NP/#TS for not-present stack segments, CS.RPL after a gate CALL to a conforming segment |
| SVM (`svm`, `npf`) | 12 (+ NPF above) | missing intercepts (RDTSCP, CR reads), INT3/INTO intercepts, VMEXIT_INVALID for a guest CR4 reserved bit, INVD/INTn intercept order, TR/LDTR attributes, RF kept until the end of a translation block; model-only instead: the #DF intercept of a combined double fault, the INIT intercept on the AP; not generated: NRIPS, decode assists, PAUSE filter, TSC ratio, SKINIT |
| APIC, x2APIC, I/O APIC, SMP, SMM (`apic`, `x2apic`, `ioapic`, `smp`, `smm`) | 4 + 6 + 1 + 1 + 3 | APIC version 14h (AMD: 10h), I/O APIC version 20h, no ESR error interrupt, no x2APIC #GP rules, reset FNINIT values, legacy SMM save map / revision |
| x87, MMX/SSE, XSAVE (`x87`, `simd`, `sse`, `xsave`) | 5 + 7 + 5 + 4 | FERR#/C1 details, DE for FST m32/m64 of a denormal, EXTRQ/INSERTQ keeping bits 127:64 (also `qemuAsHardware`), MXCSR_MASK FFFFh, EXTRQ/INSERTQ without OSFXSR, XSAVE #NM and MXCSR for RFBM = {AVX}, leaf 0Dh subleaves, XSETBV #GP at CPL 3; x87 transcendentals (378 per-line rules); the reserved FCW bits TCG keeps (model-only); two-NaN SSE lanes not generated |
| AVX, AVX2, FMA, F16C (`avx`) | 4 | #UD with CR0.EM, #NM before #UD, masked-out loads fault, VLDMXCSR reserved bits; `qemuAsHardware`: the deviations above, and the 7742's #UD for VEX.vvvv[3], VMOVSS/SD loads with vvvv ≠ 1111b and VPEXTRD/VPINSRD with W1, and its VPERMQ with W0 |
| GPR extensions, crypto (`gpr`, `crypto`) | 2 + 1 | RDMSR TSC_AUX reads 0, WBNOINVD at CPL 3; SHA with 66/F2/F3 executed (`qemuAsHardware` for the 'ud' vectors), RORX with VEX.vvvv ≠ 1111b executed (`qemuAsHardware`; #UD on the 7742) |
| identity (`lm.compat.cpuid`) | 1 | QEMU's EPYC-Rome reports highest standard leaf 0Dh; the 7742 reports 10h |
| EPYC 7742 extended native run (`simd`, `xsave`, `sse`) | 1 (+ 1 widened) + per-line RCP rules | EMMS keeps TOP, CVTPI2PS m64 switches to MMX; XSAVE faults at the not-present page's first byte (7742: the area's last); RCPPS/RSQRTPS give RNE(1/x) (rules from `zen2_rcp.py qemu`); `qemuAsHardware`: FXSAVE/XSAVE fault address and error code, VCVTPS2PH's MXCSR before a #PF, MASKMOVQ/MASKMOVDQU/VMASKMOVDQU's fault address, MOV CRn's #UD order; `t_xsave.c` keeps FSW.ES consistent in its random states (TCG loads ES as stored) |

## System tests
`test/sys/run.sh` builds a small multiboot test kernel (`test/sys/*.c`, clang only), runs it under `qemu-system-i386` (the long-mode pass under `qemu-system-x86_64`) and on the model (`x86sys`), and compares the serial transcripts line by line. TCG deviations are rewritten by the cited rules of `test/sys/qemu-deviations.txt` (table above; the paragraphs below name only what it does not); what TCG cannot run (e.g. the TSS T flag) follows a `MODEL-ONLY` marker and is checked against `test/sys/model-only.expected` (`model-only-smp.expected`, `model-only-long.expected`). The kernel covers paging with NX, breakpoints and RF, call gates, task switches, virtual-8086 mode, the APICs, SMM (via QEMU's i440FX/PIIX4 chipset; `x86sys` starts with the firmware's SMBASE), and the x87 FPU: 2,500 random operations over every operand class against QEMU's softfloat; stack faults, unmasked responses, #MF/FERR#, FIP/FDP/FOP and C1 round-up are model-only.

**MMX/SSE/SSE2** (`t_simd.c`, `t_simdx.c`): 6,500 random instructions (every opcode and prefix form, operands of every class, random RC/DAZ/FTZ and sticky flags, exceptions masked) against QEMU, plus #UD/#NM rules, alignment, prefix combinations and precedence, LDMXCSR/FXRSTOR reserved bits, FXSAVE/FXRSTOR. Model-only: unmasked SIMD exceptions, #MF for MMX, the MMX exponent word, the two-NaN rule (TCG returns the larger-significand NaN, so two-NaN lanes are not generated), MIN/MAX with DAZ, RCP/RSQRT special cases, FXSAVE's FIP/FDP.

**SSE3..SSE4a, MisalignSse** (`x86_32/X86/Ext/Sse.lean`) are tested in every layer: all legacy forms in the single-instruction tests (`test/gen_sse.py`, a third of the vectors, at most one NaN input); every `xops` form in `t_simd.c`; `t_sse.c` fuzzes PCMPxSTRx, EXTRQ/INSERTQ (incl. index + length > 64), PEXTR*/PINSR*, BLENDV and FISTTP against QEMU. Model-only: MisalignSse (MXCSR.MM, #AC, CPUID 8000_0001:ECX[7]), unmasked exceptions of ROUND*/DPPS/HADDPS, FISTTP stack underflow, `ssem.hnanps`/`ssem.hnanpd` (HADD/HSUB two-NaN pairs). `test/sse_ref.py check out/model.txt` recomputes the PCMPxSTRx, EXTRQ/INSERTQ, FISTTP, ROUND*, DPPS/DPPD and MPSADBW lines with exact rationals (`test_sse_ref.py`). Native: `sse3_*`, `ssse3`, `sse41_*`, `sse42_*`, `sse4a`, `misalign_sse` (`fp_cases_sse.py`).

**x87 transcendentals**: `test/sys/x87ref.py` is an exact reference independent of the model (Python's `decimal`). F2XM1, FYL2X, FYL2XP1 and FPATAN are fuzzed against QEMU's softfloat (3,000 cases); `x87ref.py qemu out/qemu.txt` decides every line where QEMU differs and writes a per-line rule with its reason to `test/sys/x87t-deviations.txt`; the model must match the corrected transcript. All 3,000 values agreed; the 378 rules are 229 #D (TCG never reports it here), 2 NaN choices (QEMU takes ST(0), SDM table 4-7 the larger significand), 135 domain cases, 11 F2XM1(±∞) and 1 exact result, where `x87ref.py` follows the 7742. FSIN, FCOS, FPTAN, FSINCOS (host doubles in QEMU) and C1, C2 and the stack effects of all eight are checked against 1,540 inputs from `x87ref.py table x87t_cases.h` (incl. arguments next to multiples of π/2 up to 2^62) in the MODEL-ONLY section. Regenerate both files with `x87ref.py` after changing `t_x87t.c`.

**XSAVE** (`t_xsave.c`) against QEMU: leaf 0xD, XSETBV/XGETBV, #UD/#NM/#GP/#PF conditions, and `xsf` (default 500) random XSAVE/XSAVEOPT/XRSTOR cases (all components in use: TCG tracks no XINUSE; FOP preset and slot padding unhashed, as TCG writes neither). Model-only (TCG has no XSAVEC/XSAVES/XRSTORS): compacted formats, XINUSE, XGETBV(1), the init and modified optimizations, error pointers, IA32_XSS, segment limits, and 600 cases from `test/sys/xsaveref.py`, written from the SDM and APM (`xsaveref.py table 600 1 > xsave_cases.h`). The single-instruction tests run with CR4.OSXSAVE and XCR0 = 7 and generate the XSAVE forms (`test/xsave_gen.py`). Native: `test/native_xsave.py` (images compared without reserved bytes and MXCSR_MASK).

**GPR extensions** (`t_gpr.c`): MONITOR/MWAIT rules and an MWAIT woken by an interrupt, TSC_AUX with RDTSCP/RDPID and CR4.TSD, RDRAND/RDSEED, RDPMC at CPL 3, WBNOINVD, prefetches, cache-line instructions. Model-only: CLZERO, MCOMMIT, RDPRU, RDPMC counters and CR4.PCE, HWCR.MonMwaitUserEn, reserved TSC_AUX bits, MWAIT corner cases, MONITORX/MWAITX, and the #PF, accessed-bit and limit checks of CLFLUSH/CLWB/MONITOR/CLZERO. Native: `test/gpr_cases.py` (in `fp_cases.FAMILIES`), all user-mode forms.

**AES-NI, PCLMULQDQ, SHA** (`t_crypto.c`) against QEMU: the #UD/#NM/#GP rules, FIPS-197 AES-128/192/256 with AESKEYGENASSIST key expansion, the FIPS 180-4 "abc" digests and GCM test case 2; the `xops` rows of `t_simd.c` fuzz all fourteen instructions; 640 random cases from `test/cryptoref.py` (`sys/crypto_cases.h`) are model-only. Native: `test/native_crypto.py` (every imm8 of PCLMULQDQ, AESKEYGENASSIST and SHA1RNDS4; misaligned and prefixed SHA forms as observations).

**AVX** (`t_avx.c`, plus 270 VEX rows in `xops`, YMM upper halves printed): the #UD/#NM matrix, alignment, VEX.128 zeroing, VZEROUPPER/VZEROALL, VMASKMOVPS/PD beside not-present and read-only pages, VLDMXCSR/VSTMXCSR, VEX in a 16-bit code segment, and 1500 `avxk` cases (shuffles, permutes, broadcasts, masked moves, blends, tests, the 32 VCMP predicates) recomputed by `test/avx_ref.py check`. Model-only (`avxm.*`): VEX.L = 1 of LIG scalar forms, is4 imm8[7], MXCSR.MM, unmasked #XM and #UD, #AC, #UD before #NM, `avxm.dpps256` (VDPPS ymm stages span both lanes), `avxm.hnan256`/`avxm.hnan256pd` (two-NaN pairs). Native: `avx_ops`, `avx_encoding`, `avx_maskmov`, `avx_alignment` (`test/native_avx.py`).

**AVX2, FMA, F16C** (`t_avx2.c` and 195 VEX rows of `xops`) against QEMU: the #UD/#NM matrix, every gather form, a gather faulting at its fourth element (state after the #PF, the restart), masked-out elements on a not-present page, VPMASKMOVD/Q stores beside a read-only page, FMA special cases in every rounding mode, 2000 random `avx2k` cases and 300 random gathers (`avx2g`). `test/avx2_ref.py check` recomputes every `avx2k`/`avx2g`/`avx2m` line (exact FMA with `fractions`; `test_avx2_ref.py` checks it against `math.fma` and `struct` over all 65,536 binary16 values). Model-only (`avx2m.*`): VEX.L = 1 of scalar FMA, F16C's FTZ/DAZ rules, unmasked #XM, gather and VPMASKMOV faults, no #AC for VPMASKMOV and gathers (as on the 7742), #UD before #NM, 200 F16C cases with denormals. Native: `avx2_*`, `fma_special`, `f16c` (`test/native_avx2.py`).

**Paging and breakpoint fuzzers** (400 cases each by default; `pgf=N`, `dbf=N`). `t_pgfuzz.c` builds fresh 32-bit or PAE tables per case with random bits and makes 3 to 8 reads, writes and fetches from rings 0 and 3, printing vector, error code, CR2, data and every entry's A/D flags. `t_dbfuzz.c` programs DR0–DR3/DR7 at random, runs one memory, stack, string or I/O instruction and prints DR6, EIP and the RF image of every #DB; it avoids the cases where TCG reports only the first matching watchpoint or splits a single-step trap and a data breakpoint, which the model-only `dbfm` checks against expectations computed in C (SDM 17.2.3, 17.3.1). The paging fuzzer found two model bugs: a PDE's accessed flag not set when the PTE then faulted (SDM 4.8), and 4 MiB PDEs without the bits 21:13 reserved check; the model now implements PSE-36 (bit 21 reserved), like TCG.

The TLB fuzzer `pgt` (`pgt=N`, 300 cases by default) enables paging once and runs 6 to 15 steps (accesses, entry upgrades and changes with or without INVLPG/MOV CR3, CR0.WP/CR4.PGE/SMEP/SMAP toggles), so later accesses hit cached translations. Only architecturally determined accesses are generated: after a change that is not an upgrade, a page is not accessed until an invalidation covers it (APM vol. 2, 5.5.3); MOV CR3 does not cover global pages; upgrades need none on AMD (5.5.3 "Invalidation of Table Entry Upgrades"). 12,000 cases (seeds 7, 99, 12345, 4,000 each; about 149,000 lines) matched QEMU; with the model's INVLPG or MOV CR3 flush made a no-op, 1,000 cases of seed 7 give 5 mismatching lines each.

**System workstream A** (`t_sysa.c`, `t_pae.c`, `t_pgfuzz.c`): SYSENTER/SYSEXIT, SYSCALL/SYSRET, CLAC/STAC, UMIP, AltMovCr8, EFER bits, MSR round trips, PSE-36 (bits 20:13 address memory above 4 GiB), SMEP/SMAP with cached translations and for implicit accesses; the paging fuzzer also randomises CR4.PGE, PSE-36 bits and, in half its cases, SMEP/SMAP/AC on a supervisor identity map (PAE reserved bits only above MAXPHYADDR = 48). Model-only: alignment checking (TCG has none; 50 operand forms incl. #AC before #PF), global pages, the TSC MSR, the MCA, MTRR, LSTAR/CSTAR, SPEC_CTRL/PRED_CMD and AMD configuration MSRs, `pgfm.pse.rsvd` (PSE-36).

**System workstream B** (`t_sysb.c`, `t_vm86.c`): `dfc.*` provokes every pair of first event class and second fault during its delivery (serial delivery or #DF through a task gate). NMIs from the APICs (`nmiq.*`): blocking until IRET, the one-entry latch, a faulting IRET keeping NMIs blocked (APM 8.1.4), NMI before INTR, HLT, gates, SMM and RSM; `smp=2` sends an NMI IPI to the AP inside its NMI handler. Model-only, through a test MSR only `x86sys` enables: MOV SS/STI shadows, SMI and NMI at one boundary, the blocked/latched bits; IRPerf; 800 random CR4.VME/PVI cases checked against `test/sys/vmeref.py`, written from the APM (`vmeref.py table 800 1 > vme_cases.h`; TCG has neither VME nor PVI).

**Review regressions** (`t_review.c`), against QEMU: INT n with short or 16-bit TSSs and an I/O map base beyond the limit, outside virtual-8086 mode or without VME: the redirection bitmap is consulted only in virtual-8086 mode with CR4.VME = 1 (APM vol. 2, 8.10.1), so every case is delivered; events from virtual-8086 mode push their frame at CPL 0 (supervisor stack, no #AC). The CR4.VME = 1 variants are model-only.

**Control transfers** (`t_xfer.c`): `tsf=N` task switches and `cgf=N` far CALL/JMP/RET, direct and through 16- and 32-bit call gates, with random descriptors, selectors and stacks (300 cases each by default); every exception and case end goes through IDT task gates to recovery tasks, so outcomes are observed from a clean task. Six model bugs found: JMP/CALL to an LDT TSS descriptor switched tasks instead of #GP; an IRET to the current task loaded TSS contents from before the switch saved the state; null selectors with RPL > 0 survived returns to outer levels; RETF to a 16-bit stack cleared ESP[31:16]; an inner-stack selector beyond the table limit raised #GP instead of #TS; a call gate with no room for the frame raised #SS(0) after the offset check instead of #SS(new SS) before it. Excluded, with model-only checks: conforming task CS with DPL < RPL, far CALL/RET offset checks, JMP through a gate to a not-present segment, 16-bit inner stacks, null FS/GS on returns, RF in the image of faults through task gates, faults after the task-switch commit point.

**Multiprocessor platform** (`t_apic.c`, `t_ioapic.c`, `t_x2apic.c`, `t_smp.c`), against QEMU: ESR, the I/O APIC (edge PIT, level UART with remote IRR, destinations, TMR), x2APIC (`-cpu ...,+x2apic`); a second pass with two CPUs (`smp=2`; QEMU `-smp 2,sockets=2`, `x86sys --smp 2`) compares AP startup, IPIs of every mode and shorthand, a TLB shootdown, I/O APIC routing, MWAIT ended by the other CPU's store, LOCKed counters, TSCs and the AP's state after RESET+INIT. Model-only: APR, remote read, SAE, SIV/RIV, SEOI, IER, extended LVTs, I/O APIC polarity and ExtINT, AMD's x2APIC ICR rules and lowest-priority arbitration (TCG takes the lowest APIC ID), INIT keeping CR0.CD/NW. `x86sys --quantum Q`: the SMP transcript is identical for Q = 1, 3, 7, 100, 1000, 10^4, 10^6. `x86sys --smp N --cmdline smpn=N` (N ≤ 128) dumps each CPU's CPUID topology for `test/topo_ref.py check N`, a reference from the APM and a 7742 dump (checked for N = 2, 3, 4, 16, 128); `guest/topo-check.sh N` checks Linux's topology against it (N = 3, 4).

**Long mode** (`t_long.c`) is a pass with `long=1` under `qemu-system-x86_64`: activation rules, then compatibility-mode code at CPL 0 and 3 with 4-level paging (A/D, large pages, NX, reserved bits, WP, SMEP/SMAP), 64-bit gates, #UD of SYSENTER/SYSEXIT/SWAPGS/RDFSBASE, FS_BASE/KernelGSbase, descriptor instructions, 16-bit code and every transfer into 64-bit code. The 64-bit targets are tiny hand-assembled stubs that record the frame and return with IRETQ; QEMU executes them, the model stops before them and `x86sys` applies the stub's exact effect (`LongStub.lean`, recognised by its bytes). A 4-level paging fuzzer, `lmf=N` (300 by default; 1,500 cases each with seeds 7 and 99 checked), randomises every level. Model-only: enabling paging with CS.L = 1, clearing CR4.PAE in long mode, RSM recomputing LMA, the L = D = 1 far-JMP target (#GP, the Intel rule). Review additions against QEMU: outer-level IRET/RETF to 64-bit code, a 64-bit call gate with a based SS, breakpoints above 4 GiB, an SMI in compatibility mode (AMD64 save map; rules for QEMU's revisions 20064h and, in the main pass, 20000h).

### x86bridge

`x86bridge` (`BridgeMain.lean`, the only target depending on both Lake packages) hands every stop of the IA-32 model in 64-bit mode to the `x86_64` model: it converts the machine state (mapping documented in the file) and runs the x86-64 model, which stops at the first transfer back to compatibility mode (it has none). On `t_long` (`x86bridge --cmdline long=1 test/sys/out/systest.elf`, step 6) the IA-32 side reaches all 1,108 stops and `END`; 1,106 stops run the stub in the x86-64 model up to its IRETQ with exactly the memory writes and registers of `LongStub.lean`'s emulation. The X64 machine starts with `icount + tscOff`, so its TSC equals the IA-32 model's; state X64 cannot hold is listed in the file header.

### x86-64 model: known issues

Found in the separate `x86_64/` model and left unfixed there (out of this work's scope); the root `verify.sh` reports the x86-64 checks with their own verdict (exit status 2 when only they fail), never as an IA-32 failure:
- **RF in the RFLAGS image of a #GP**: the x86-64 model does not set RF in the RFLAGS it pushes for a fault. 2 of the 1,108 bridge hand-offs differ for this reason (stops 55 and 56 of `t_long`: an IRETQ / far RET stub after a #GP; 2 differing bytes, registers equal). `validation/verify.sh` fails if more than these 2 differ.
- **Two-NaN SUBPS against QEMU**: the random x86-64 test has a seed-dependent mismatch on SUBPS with two NaN lanes, e.g. `python3 x86_64/test/run.py 2000 1794432498`: vector 1771 (`0F 5C`), XMM2 bits 127:64: QEMU `ffc302ca7fc00123`, model `7fc001237fc00123` (1 of 2,000 vectors). Which side follows the SDM's two-NaN rule there is undecided.

### SVM

`t_svm.c` is a small hypervisor in the test kernel, compared with QEMU (`-cpu ...,+svm,+npt`): instruction rules, VMRUN/#VMEXIT state, 50 instruction intercepts, IOIO and MSR maps, exception intercepts, #DF and shutdown, intercept priority, event injection, consistency checks, VMSAVE/VMLOAD, GIF, virtual interrupts, real-mode, virtual-8086, 16-bit and paged guests, nested paging with a PAE host, and the interrupt shadow and RF saved by intercepts; fuzzers `svf=N` (300 by default; 3,000 cases identical: random intercepts × guest state × a 44-instruction pool) and `npf=N` (300 by default; 3,000 cases with seed 3 identical: random nested and guest tables). The `smp=2` pass sends a guest on the AP an IPI, an NMI and an INIT (identical for quanta 1 to 10^6); the `long=1` pass runs VMRUN from a compatibility-mode host (`test_svm_long`). Avoided by the generators: what TCG lacks (NRIPS, decode assists, PAUSE filter, TSC ratio, VM_CR/SVM_KEY, SKINIT, nested walks for a non-PAE host) and where it differs (unknown MSRs, XSETBV with OSXSAVE = 0, WBINVD at CPL 3, RF = 0 at a VMMCALL exit). Model-only (`svmm.*`, `svmr.*`): the #DF intercept of a combined double fault and the INIT intercept on the AP, CPUID 8000_000A, the SVM MSRs, nRIP and decode assists, TSC_RATIO/OFFSET, virtual GIF, TLB_CONTROL and INVLPGA, INIT and SMI around guests, SMM_CTL, SKINIT, gPAT, a 32-bit nested-paging host, and two tables from `test/sys/svmref.py`, written from the APM (`svmref.py table 400 400 1 > svm_cases.h`): 400 SVM-fuzzer cases without the TCG restrictions and 400 nested-paging cases (32-bit and PAE hosts, every guest mode). The two points the APM leaves open (V17) are not derived from it: the dependent cases (138 of 400 with seed 1) are counted separately. The SVM instructions are also 'ext' cases of `test/gen_svm.py`. Not tested: 64-bit guests. No native family: SVM is ring 0.

## TSO memory-model tests

`lake build x86litmus` builds the concurrent execution explorer; `python3 litmus/litmus.py check-expected litmus/tests litmus/diy` compares all final states with the pinned expected sets ([provenance and herd7 comparison](litmus/README.md)). `verify.sh` also checks on 20,000 generated vectors (those with paging off) that the TSO access log preserves single-CPU execution and records all stores.

## Hardware tests

### The EPYC bundle (user mode, no root)

`test/native_fp.py prepare` builds a self-contained paste script that runs every native case family on an x86-64 Linux machine in 32-bit compatibility mode and captures the full state with signal handlers; the target needs only Python 3 (no root, KVM, compiler or Lean). Details of the bundle, its runner and comparison: [`test/FP-HARDWARE.md`](test/FP-HARDWARE.md).

```
$ python3 test/native_fp.py prepare test/out/ia32-epyc-linux --seed 20261112 --count 10000
  -> test/out/ia32-epyc-linux-paste.sh (22.9 MB), test/out/ia32-epyc-linux.tar.gz (17.0 MB)
$ bash ia32-epyc-linux-paste.sh          # on the EPYC; prints the results archive to send back
$ python3 test/native_fp.py compare test/out/ia32-epyc-linux --result <returned results dir>
$ python3 test/native_fp.py recompare test/out/ia32-epyc-linux --result <returned results dir>   # the current model
```

The bundle holds 189,216 cases (the first one: 189,240) in 66 campaigns of 76 families (10,368 of them 'observe'), each with the model's result in compatibility mode (`x86fp --compat`); it records the machine's CPUID dump (`cpuid.txt`) and skips campaigns whose features the machine lacks. Send back the `results.tar.gz` the script names at the end. A TCG smoke run (`test/fp_smoke.py`, `--smoke` bundle, 2,654 cases, guest of `../x86_64/guest/`) checks the runner only: 2,604 cases in 26 campaigns complete; 7 campaigns skipped (CLZERO, MONITORX, MCOMMIT, RDPRU, MisalignSse, XSAVEC, XSAVES); 2 cases left out (QEMU aborts); 527 TCG/model differences, all where TCG is known to differ.

**EPYC 7742 runs: all 189,216 cases have hardware results** (the first run 000–034, the resumed run 035–065; triage below). The first run stopped at campaign 035 (`gpr_cache`, a data-page PTE 0x45 that a user-mode oracle cannot realise), so 036–065 (52,096 cases) never ran. Since then `prepare` runs the oracle's input validation (`native/record_check.h`) on every record, the target dry-runs it (`oracle check`) before every campaign, and a refused, failing or hanging case is recorded and skipped. `recompare` runs the current model on stored results, `summary` counts differences by family, instruction and field, and `prepare --resume` built the rest (`test/out/ia32-epyc-resume-paste.sh`, 8.7 MB: 035 fixed and 036–065, 52,072 cases), merged with `--merge`. Details: [`test/FP-HARDWARE.md`](test/FP-HARDWARE.md).

**The extended bundle** (`test/out/ia32-epyc-ext`; families, format 3 and the safety design in [`test/FP-HARDWARE.md`](test/FP-HARDWARE.md), "The extended bundle"): campaigns 000–068 with bit-identical inputs plus 143 new campaigns (069–211), 863,642 cases in all: `enc_fuzz` (210,930, every legacy and VEX opcode slot plus random encodings, single-stepped), the integer core (`int_core` 272,041, `int_directed` 36,001, `shift16_rules` 13,312, `code16` 6,383 in a 16-bit code segment), FP depth (`fma_random` 20,000, `f16c_exhaustive` 12,288, `avx_unmasked` 33,200, `sse_unmasked_ext` 18,000, `avx_random` 30,375) and the open rules (`x87_control_load`, `fxsave_align`, `xsave_padding`, `x87_trans_special`, `fenv16`, `fpu_pointers`). `x86fp` runs each case in the oracle's exact address space (the 201,616 earlier cases give bit-identical results); `run` executes every campaign twice on two physical cores (`--repeat 2 --pin auto`) and reports every case observed differently.

```
$ python3 test/native_fp.py prepare test/out/ia32-epyc-ext --seed 20261112 --count 10000 --no-model-files --repeat 2 --pin auto
$ tar -xzf ia32-epyc-ext.tar.gz && python3 ia32-epyc-ext/native_fp.py run ia32-epyc-ext      # on the EPYC
$ python3 test/native_fp.py recompare test/out/ia32-epyc-ext --result test/out/epyc-ext-returned/results   # here
```

#### The EPYC 7742 runs: triage of every difference (campaigns 000–065, 189,216 cases)

Machine: a bare-metal AMD EPYC 7742 (microcode 0x830107c, Linux 6.8, IA-32 compatibility mode). **First run** (campaigns 000–034, 137,144 cases: x87, MMX/SSE/SSE2, `alignment_check`, AES/PCLMULQDQ/SHA, five `gpr_*` families) against the model as it was: 717 strict mismatches and 656 observations; the resumed bundle (`test/out/ia32-epyc-resume`) ran 035–065 (52,072 cases). Every difference, masked ones included, was traced to a root cause and decided by the hardware. `test/epyc_regression.py` replays the cases the model got wrong (`test/fixtures/native_epyc_fixes.json`, up to 12 per root cause, 207 cases, unmasked); `Proofs/EpycHw.lean` has a theorem or `#guard` per rule.

| root cause | families | cases | kind | resolution |
|---|---|---|---|---|
| FCOMI/FCOMIP/FUCOMI/FUCOMIP with IE or DE unmasked: ZF, PF, CF written as when masked, no pop (the model left EFLAGS unchanged) | `x87_exceptions` 208, `x87_random` 200 | 408 strict | model bug (the SDM sets 111 "if IM = 1" only) | `Fpu.fpCompare`; TCG already did so |
| the same for FCOM/FUCOM/FCOMPP/FUCOMPP/FTST: C3, C2, C0 written | `x87_exceptions`, `x87_random` | 487 (masked by `sw_mask`) | model bug | same fix |
| FLD ST(i) with ST(i) empty and ST(7) in use: underflow (C1 = 0) wins over overflow | `x87_exceptions`, `x87_random` | 77 (C1 masked) | model bug | `Fpu.x87D9reg` |
| FXTRACT: the push's stack overflow (ST(7) in use) before the operand's IE/DE/ZE | `x87_exceptions` 10, `x87_random` 12 | 22 strict | model bug | `Fpu.x87D9reg` |
| FSCALE with OE/UE unmasked beyond the wrapped range: ±∞ (OE, PE, C1) or ±0 (UE, PE) (SDM vol. 1, 8.5.4/8.5.5) | `x87_exceptions` 1, `x87_random` 3 | 4 strict | model bug | `round80`; TCG agrees |
| FPREM/FPREM1, denormal remainder, UE unmasked: UE, the remainder wrapped by 24576 | `x87_exceptions` | 4 strict | model bug | `F80.prem` rounds with `round80` |
| FST/FSTP m32/m64 of a denormal ST(0): no DE (the SDM lists no #D for FST) | `x87_memory` | 48 strict | model bug | `F80.toIeee`; QEMU rule (TCG sets DE) |
| F2XM1 outside [-1, 1] and at ±1, FYL2X of 2^k, FYL2XP1 outside √2/2 − 1 ≤ x ≤ √2 − 1: the model raised QEMU's invalid operation and gave exact results without PE | `x87_transcendental` 120 strict + 200, `x87_trans_boundary` 110 | 120 strict, 310 observations | undefined in the SDM, defined by the hardware | F2XM1: x with PE for finite \|x\| > 1, +∞/−1 for ±∞, −0.5 with PE for −1, the rounding of 1 − ε for +1; FYL2XP1: y·log2(1 + x) for x > −1, x with PE for x ≤ −1; PE for every finite nonzero result (`Trans.forcePE`); `x87ref.py` regenerated |
| transcendental results 1 ulp from the correctly rounded value | `x87_trans_boundary` | 8 observations (+2 differing only in C1) | implementation approximation | kept; hardware error ≤ 0.58 ulp (F2XM1 0.505, FYL2X 0.520, FYL2XP1 0.581, FPATAN 0.507); FSIN/FCOS/FPTAN/FSINCOS agreed bit for bit on all 1,688 cases (422 each) |
| RCPPS/RSQRTPS/RCPSS/RSQRTSS: AMD's table results (12 fraction bits) | `sse_random` | 338 observations | implementation specific | relative error ≤ 1.0·2⁻¹² (RCP), 0.83·2⁻¹² (RSQRT); a midpoint-and-round rule on the top 12 fraction bits fits only 210/314 and 259/287 lanes, hence `sse_rcp_sweep` (12,400 cases, `test/native_rcp.py`) and the 7742's tables (below) |
| x87 control word loaded by FRSTOR: bits 7, 13..15 read 0, bit 6 reads 1 | `alignment_check` | 12 strict | model bug (reset value 0040h; Bochs agrees) | `fcwLoad` for FLDCW, FLDENV, FRSTOR, FXRSTOR, XRSTOR; `xsaveref.py` follows |
| FNSTENV/FNSAVE, 32-bit protected-mode format: the reserved upper halves of the CW, SW, TW and FDS dwords are FFFFh | `alignment_check` | 24 strict | model bug | `fpEnvBytes` (real-mode format not observed, kept 0) |
| FXSAVE writes bytes 10..15 of each register slot as zero | `alignment_check` | 2 strict | model bug | `fxsaveRegs (pad := true)` |
| FXSAVE with EFLAGS.AC = 1: #AC for an operand not 4-byte aligned, before the 16-byte #GP | `alignment_check` | 4 strict | open question | `vecAddr (acFirst := 4)` |
| MASKMOVDQU (and MASKMOVQ): #AC for DS:EDI not 8-byte aligned, not 16 | `alignment_check` | 1 strict | open question S7 | `Simd.maskMov` (also VMASKMOVDQU) |
| SHA with a misaligned m128 operand executes (the SDM says exception class 4) | `sha` | 28 strict (observe rows with a vector difference) | open question C2 | `Crypto.shaOp`; the QEMU rule removed (TCG agrees), `gen_crypto.py` generates misaligned SHA operands |
| RORX with VEX.vvvv ≠ 1111b is #UD (SDM; the APM lists none) | `gpr_bmi` | 40 strict | open question G3 | `Gpr`; `qemuAsHardware` (TCG executes) |
| undefined flags: LZCNT/TZCNT keep OF and clear SF, AF, PF; BEXTR sets AF, clears SF, PF = parity; ANDN/BLSx/BZHI as the model had (AF = 0, PF = parity) | `gpr_bitcount`, `gpr_bmi` | 148 (masked by `flags_mask`) | undefined, adopted | `Gpr.bitCount`, BEXTR |
| EFLAGS.RF in faulting cases | all faulting cases | (masked) | oracle artifact: a fault's pushed EFLAGS image has RF = 1 (SDM 17.3.1.1) | the comparison's flag mask |
| FIP/FDP/FOP: the signal frames show the error pointers only with FSW.ES = 1 (4,335 cases, all equal to the model's), otherwise the input's 0 (30,754 cases) | x87 families | (excluded) | open (F5) | settled by the extended run (X6); compared since |
| *resumed run, 035–065:* EXTRQ/INSERTQ (all four forms) clear bits 127:64 of the destination | `sse4a` | 288 strict | undefined (APM), defined by the hardware | `Sse` clears them; QEMU rules (TCG keeps them); `sse_ref.py` |
| HADDPS/HADDPD/VHADDPS/VHADDPD with two NaNs in a pair: the lower element's NaN (an SNaN in the higher element loses to a QNaN in the lower) | `sse3_hadd_nan` 48, `sse3_arith` 5, `avx_ops` 11, `avx_observe` 4 | 68 strict | open question S2/A6 (the manuals write the higher element first) | `Sse.hop` adds `x[2j] + x[2j+1]`; HSUB already matched; `sse_ref.py` |
| FSW.B after the oracle's XRSTOR of a status word with ES = 1, B = 0: B = 1 | `xsave_save` 24, `xsave_compacted` 12 | 36 strict | model bug (SDM 8.1.3.1: B reflects ES) | `fswLoad` for XRSTOR/FXRSTOR/FLDENV/FRSTOR and `x86fp`'s input state |
| no #AC for misaligned VPMASKMOVD/Q (load and store, 128/256) and gather elements | `avx2_alignment` | 17 strict | open questions A8, A9 | `maskAc` no-op, no element #AC (VMASKMOVPS/PD already matched) |
| VEX.vvvv[3] alone wrong on a form that needs 1111b: #UD (VMOVAPS, VCVTPS2PH) | `avx_encoding` 2, `avx2_encoding` 1 | 3 strict | open question A4 (SDM 2.3.5.6: ignored) | `Inst.vvvv3`, `Vex.noV` (as a register number bit 3 stays ignored) |
| VMOVSS/VMOVSD load with VEX.vvvv ≠ 1111b: #UD | `avx_encoding` | 4 strict | open question A3 | `Avx` |
| VPEXTRD/VPINSRD with VEX.W1 outside 64-bit mode: #UD | `avx_encoding` | 4 strict | open question A4 | `Avx`; `isa_forms` rows, LLVM cross-check entry |
| VPERMQ with VEX.W0 executes as VPERMQ | `avx2_encoding` | 1 strict | the APM requires W1 | `Avx2` ignores W; LLVM cross-check entry |
| RDPRU with an unsupported ECX leaves every flag unchanged | `gpr_rdpru` | 4 strict | open question G6 | `Gpr.rdpru` |
| 16-bit SHLD/SHRD with a count of 17..31: result 0 with source 0, AF = 1 | `open_questions` | 5 strict | open question G8 (undefined) | superseded by the extended run's 48-bit rule (below); TCG's dst:src:dst no longer generated |
| SNaN m32/m64 operand of x87 arithmetic and a QNaN ST(0): ST(0)'s QNaN (the SNaN is not quieted before the NaN choice) | `open_questions` | 3 strict | open question F1 | `fpMemOperand` |
| VRCPPS/VRSQRTPS/VRCPSS/VRSQRTSS: the same table as the legacy forms | `avx_ops` | 146 observations | implementation specific | 350 + 350 VEX lanes agree with the legacy lanes at all 9 shared entries (977 lanes); now the 7742's tables |

After these fixes, `native_fp.py recompare` of all 189,216 cases (both runs, `--merge`): **0 strict mismatches, 492 observations** (338 RCPPS/RSQRTPS in `sse_random`, 146 VRCPPS/VRSQRTPS in `avx_ops`, 8 transcendental results), and no difference in any unmasked column (all FSW bits, all EFLAGS bits but RF, undefined flags) beyond those 492 rows and the 2 C1-only rows. Families without any difference: `avx2_ops` 8,050, `avx2_gather` 412, `avx2_maskmov` 128, `avx_maskmov` 128, `avx_alignment` 192, `f16c` 68, `fma_special` 264, `sse42_strings` 16,384, the `sse41_*` families 5,045, `ssse3` 3,074, `sse3_fisttp` 534, `misalign_sse` 99, `gpr_cache`/`gpr_clzero`/`gpr_monitorx`/`gpr_system`, `longmode` 37, `xsave_restore`/`xsave_fault`/`xsave_xcr`/`xsave_privileged`, `open_questions_xsave`, `aes` 6,292, `pclmulqdq` 1,262, `sha_prefix` 21, and the base families above.

CPUID ([`../x86_32/CPUID.md`](../x86_32/CPUID.md)): the machine's dump (`test/fixtures/epyc7742-native-cpuid.txt`, logical CPU 155) equals InstLatx64's (`test/fixtures/epyc7742-cpuid.txt`) except per-CPU topology, the subleaves of 8000_0020h (subleaf 1 EAX = 0Bh, EDX = 0Fh) and 8000_0008h EBX[17] StibpAlwaysOn, clear here and now masked (124 of the 162 feature bits reported, each in both dumps: `dumps_feature_diff`, `test/cpuid_table.py`). Both list XCR0 bit 9 (PKRU) in leaf 0Dh without PKU.

#### The extended run (campaigns 000–211, 863,642 cases)

The extended bundle ran on the same machine, every campaign twice on two physical cores: all 863,642 cases have hardware results. Against the model of the bundle: **3,999 strict mismatches and 46,162 observations**, all in the new families; each traced to a root cause of kind (a) model bug, (b) harness or comparison artifact, (c) left undefined or implementation specific by the manuals, now the 7742's, or (d) an open question answered. `test/epyc_regression.py` replays a sample (`test/fixtures/native_epyc_ext_fixes.json`: up to 6 cases per root cause, one per undefined-flag instruction, RCP/RSQRT lanes; 363 cases, unmasked, 351 of which fail with the model of the bundle); `Proofs/EpycHw.lean` has `#guard`s for the cheap rules.

| root cause | families (strict cases) | cases | kind | resolution |
|---|---|---|---|---|
| 16-bit SHLD/SHRD: the 48-bit dst:src:src (SHLD) / src:src:dst (SHRD) is shifted, so counts 17..31 rotate the source by count − 16; CF = 0 above 16; OF, AF as in the flag table | `shift16_rules` 1,160, `enc_fuzz` 14, `code16` 1 | 1,175 | (c), G8 | `Alu.shiftDouble` (was: 32-bit dst:src, inferred from 5 cases with source 0) |
| PUSHF stores EFLAGS.ID/NT set by an earlier POPF case of the same oracle process (rt_sigreturn takes only FIX_EFLAGS from the frame) | `int_core` 431, `enc_fuzz` 26 | 457 | (b) | the model runs on the start state the oracle really had (`native_fp.oracle_start_flags`); the oracle clears ID/NT before every case (`signal_oracle.c`) for later bundles |
| XOP layout (8F with ModRM.reg ≠ 0, every map): 3 bytes, opcode, ModRM/SIB/disp, imm32 in map 0Ah only; the 15-byte #GP(0) before the #UD | `enc_fuzz` 342, `code16` 13 | 355 | (a) | `Decode.lean` (was: POP r/m layout); all 8,664 XOP encodings agree |
| an unknown VEX map has a ModRM byte | `enc_fuzz` 259, `code16` 6 | 265 | (a) | `Decode.lean`; all 15,923 such cases agree |
| 0F 0F (3DNow!): ModRM and imm8 | `enc_fuzz` 193, `code16` 11 | 204 | (a) | `opInfo`; all 8,728 cases agree |
| 0F 78: two imm8 whatever the prefix; 0F B9 (UD1), 0F FF (UD0, also VEX): no ModRM; VEX.0F 0F: ModRM (+ imm8, inferred); VEX.0F 80–8F: 4 immediate bytes whatever 66 says | `enc_fuzz` 21, `code16` 1 | 22 | (a) | `Decode.lean` |
| CMPS reads ES:(E)DI before DS:(E)SI | `int_core` 197, `enc_fuzz` 65, `int_directed` 2, `code16` 2 | 266 | (a) (manuals: no order) | `Exec.strIter`; TCG agrees: `x86test` now compares CMPS's CR2 |
| BSWAP r16 clears bits 15:0 (keeps 31:16) | `enc_fuzz` 186, `code16` 36, `int_directed` 9 | 231 | (c) | `Exec`; all 234 cases |
| FLDENV/FRSTOR/FXRSTOR/XRSTOR: FSW.ES = B = an unmasked flag is set, whatever the image's ES | `x87_control_load` 198, `code16` 8, `enc_fuzz` 1 | 207 | (a) | `fswLoad`; all 1,660 loads agree |
| XSAVE/XSAVEOPT write the x87 slots' padding (bytes 10..15) as zeros | `xsave_padding` 132, `fxsave_align` 4 | 136 | (a) | `Xsave.saveX87` |
| ARPL reads its operand and writes only when it adjusts the RPL | `int_core` 100, `enc_fuzz` 22, `code16` 1 | 123 | (a) | `Exec` (SDM pseudocode; was: RMW write-back) |
| MOV to/from CR1, CR5–CR7 at CPL 3: #UD before #GP(0) | `enc_fuzz` 123 | 123 | (a) (no order in the APM) | `Exec` 0F 20/22; `qemuAsHardware` (TCG: #GP) |
| ENTER with alignment checking: #AC for a final ESP not aligned to the operand size (before its #PF; frame stores kept) | `int_core` 96, `enc_fuzz` 3 | 99 | (a) | `Exec` ENTER |
| ENTER with a 16-bit operand size on a 32-bit stack writes BP only | `code16` 29 | 29 | (d) G10 | `Exec` |
| EMMS sets TOP = 0 | `enc_fuzz` 41, `code16` 4, `fpu_pointers` 4 | 49 | (a) (SDM vol. 1, table 9-2) | `Simd.emms`; QEMU rule |
| MMX transition: none for CVTPI2PS m64; kept when MASKMOVQ faults and when CVTPI2PS/PD mm or CVT(T)PS2PI/PD2PI raise #XM; MASKMOVQ/MASKMOVDQU fault at DS:(E)DI | `enc_fuzz` 45, `code16` 3 | 48 | (a)/(c) | `Simd.sseCvt`, `Step.mmxFaultKeeps`, `Simd.maskMov`; QEMU rule |
| LOOPE/LOOPNE with F2/F3: the last of them selects the condition (F3: ZF = 1, F2: ZF = 0) | `enc_fuzz` 34, `code16` 1 | 35 | (c) undocumented | `Exec` E0/E1; all 83 cases agree |
| x87 stores check their destination (#PF, #GP, #AC) even when an unmasked exception suppresses the store | `enc_fuzz` 35 | 35 | (a) | `Fpu.fpStore` |
| FSTP/FIST with an unmasked OE/UE: no PE; FSTP1 (D9 D8+i) with an empty ST(0) only pops | `enc_fuzz` 1 + 3 | 4 | (c) | `Fpu.fpStore` (OE inferred by symmetry), `Fpu.x87D9reg` |
| FNSTENV clears ES and B | `fenv16` 16, `fpu_pointers` 4 | 20 | (a) | `Fpu` |
| FLDCW, FLDENV, FRSTOR raise #MF for a pending exception | `fenv16` 16, `fpu_pointers` 4 | 20 | (a) | `Fpu.fpWaitingControl` |
| FXSAVE/XSAVE write FOP/FIP/FCS/FDP/FDS only with FSW.ES = 1 (zeros otherwise), despite XSaveErPtr; restores always load them | `fpu_pointers` 12 | 12 | (d) F5, X6 | `Simd.fxsaveEnv`; `x86fp` reports the pointers as the signal frame's XSAVE stores them, compared in every case now (all 858,603 agree) |
| FXSAVE/FXRSTOR/XSAVE/XSAVEOPT fault first at the last byte of the area, XRSTOR at its header; FXRSTOR's #AC (4-byte) precedes its 16-byte #GP | `fxsave_align` 32, `enc_fuzz` 1 | 33 | (d) S8 | `Simd.fxsave/fxrstor`, `Xsave.area`; QEMU rules |
| RCPPS/RSQRTPS table results in a strict family | `enc_fuzz` 17 | 17 | (c) | the 7742's tables (below) |
| FYL2XP1(+∞, y) = ±∞ by the sign of y; FYL2XP1(−1, ±0 or ±∞) = ∓0, ∓∞, no exception | `x87_trans_special` 15 | 15 | (c) F3 | `Trans.fyl2xp1`, `x87ref.py` |
| REP INS/OUTS check the I/O permission with a zero count (#GP(0) at CPL 3) | `enc_fuzz` 11, `code16` 1 | 12 | (a) | `Exec.stringOp` (TCG agrees) |
| VCVTPS2PH m: destination checked (#AC, #PF) before the MXCSR flags and #XM | `avx_random` 4, `enc_fuzz` 1 | 5 | (a) | `Avx2.cvtps2ph`; QEMU rule |
| a 16-byte-aligned SSE/XSAVE operand: the alignment #GP(0) before the segment-limit #SS(0) of an access wrapping past 4 GiB | `enc_fuzz` 2 | 2 | (a) | `Simd.vecAddr`, `Xsave.area` (theorem `area_misaligned` restated) |

**Undefined flags.** The new families recorded every documented-undefined arithmetic flag (`flags_observe`, `eflags.undefined`: 30,551 observations). Each rule below predicts the 7742's value in 100% of the completed cases of all integer families (77,275; the 10,667 faulting cases, incl. DIV #DE, leave every flag unchanged). The model computes them, the comparison checks them strictly (`native_fp.PINNED_UNDEFINED`) and the generators no longer mark them (`native_flags.observed_flags`); the QEMU tests keep masking them (`fmask` in `gen.py`).

| instruction | the EPYC 7742's value of the formerly undefined flags | cases | model before |
|---|---|---|---|
| AND, OR, XOR, TEST (all forms) | AF = 0 | 19,789 | agreed |
| SHL/SAL | AF = 1; OF = MSB(r) XOR CF for every count (CF = 0 for a count above the width) | 7,638 | AF wrong |
| SHR | AF = 1; OF = bit w−1 XOR bit w−2 of r (MSB(dst) for a count of 1, 0 above) | 3,791 | AF, OF wrong |
| SAR | AF = 1; OF = 0 | 3,789 | AF wrong |
| ROL, ROR (count mod w) | CF and OF from the result as for a count of 1 (ROL: CF = r[0], OF = MSB XOR CF; ROR: CF = MSB, OF = bit w−1 XOR bit w−2) | 6,848 | agreed |
| RCL | OF = MSB(r) XOR CF | 3,404 | agreed |
| RCR | OF = bit w−1 XOR bit w−2 of r | 3,430 | OF wrong (MSB(dst) XOR CF-in) |
| SHLD/SHRD r/m32 | AF = 1; SHLD OF = MSB(r) XOR CF, SHRD OF = bit 31 XOR bit 30 of r | 1,694 | AF, OF wrong |
| SHLD/SHRD r/m16 | AF = 1; CF = 0 above 16; SHLD OF = MSB(r) XOR CF below 16, CF at 16, 0 above; SHRD OF = bit 15 XOR bit 14 | 3,551 | wrong |
| MUL, IMUL (F6/F7 /4 /5, 69, 6B, 0F AF) | SF, ZF, AF, PF unchanged | 4,526 | wrong (SZP of the low half, AF = 0) |
| DIV, IDIV (completed) | AF = 1, SF = ZF = PF = 0, CF and OF unchanged | 1,075 | wrong (all unchanged) |
| AAA, AAS | from the 16-bit AX ± 0106h when adjusting (SF = bit 15, ZF of 16 bits, PF of its low byte, OF its signed overflow), from AX otherwise (OF = 0) | 3,903 | wrong (unchanged) |
| DAA, DAS | OF = the signed overflow of AL ± the correction (DAA: AL[7] 0 → 1, DAS: 1 → 0) | 3,925 | OF wrong (0) |
| AAM | OF = AF = CF = 0 | 2,711 | agreed |
| AAD | CF, AF, OF of the 8-bit addition AL + (AH·imm8)[7:0] | 2,767 | wrong (0) |
| BT, BTS, BTR, BTC | OF, SF, ZF, AF, PF unchanged | 3,031 | agreed |
| BSF, BSR | source 0: ZF = 1, the destination and CF, OF, SF, AF, PF unchanged; else ZF = 0, the others unchanged | 1,403 | agreed |
| LZCNT/TZCNT, ANDN/BLSx/BZHI, BEXTR | (first run, G1) | — | agreed |

**RCPPS/RSQRTPS.** The sweep (`sse_rcp_sweep`, campaigns 066–068) determines the function: the result depends only on the exponent and fraction bits 22..11; RCP uses one 4096-entry table of 12-bit result fractions (biased exponent 253 − E, ±0 for E ≥ 253 whatever FTZ), RSQRT two by exponent parity (exponent (379 − E)/2 or (380 − E)/2); no interpolation, no MXCSR effect, no flag; NaNs are quieted, ±0 and denormals give ±∞, RCP(±∞) = ±0, RSQRT(+∞) = +0, RSQRT of another negative operand FFC00000h; RCP(1.0) = 3F7FF000h. The tables (`x86_32/X86/Zen2Rcp.lean`, from `test/zen2_rcp.py tables`) reproduce all 52,794 RCP/RSQRT lanes of the run, every entry pinned by at least 4 observations; maximum relative error 1.29·2⁻¹² (RCP), 0.94·2⁻¹² and 1.06·2⁻¹² (RSQRT, odd and even exponent), within AMD's 1.5·2⁻¹² (`zen2_rcp.py bound`; a `#guard` over all entries in `Proofs/EpycHw.lean`). The model computes them (`FP.rcp`, `FP.rsqrt`). TCG computes RNE(1/x): `test/sys/run.sh` replaces its `t_simd.c` results by `zen2_rcp.py`'s (rules generated on every run); the single-instruction tests do not generate RCP/RSQRT. Not observed: RSQRT of a negative SNaN and a few negative denormals.

**Determinism.** 187 of 212 campaign passes were byte-identical; 141 cases differed between the two cores, all in observe fields and all machine or time dependent: RDTSC (130), RDRAND/RDSEED (8; also RDPID's CPU number), CPUID (1, EDX of a CPU-specific leaf), RDPRU (1, APERF/MPERF).

**After the fixes**, `native_fp.py recompare` of all 863,642 cases: **0 strict mismatches, 2,375 observations**: results that depend on the OS, the machine or time (`native_ext.os_dependent`: SS loads 1,380, UMIP-emulated SGDT/SIDT/SMSW 388 and SLDT/STR/VERR/VERW 318, LAR/LSL 71, RDTSC 130, RDRAND/RDSEED/RDPID 8, RDPRU 1), transcendental results within 1 ulp (`x87_trans_special` 35, `x87_trans_boundary` 8), and 36 `fpu_pointers` cases whose input FIP/FDP have bits above 31 (kept by the 64-bit signal frame). The inputs were selected with the model of that time, so a future `prepare` selects somewhat different `enc_fuzz`/`int_core`/`code16` cases; this run is always evaluated on the stored bundle.

**The x86-64 model** (`../x86_64/`, unchanged) probably keeps the old behaviour of these rules; to check: undefined-encoding lengths, MOV CRn, BSWAP r16 (and r64 with 66), CMPS, LOOPcc, REP INS/OUTS, ENTER, the undefined flags, EMMS and MMX transitions, the x87 rows (FSW.ES, FNSTENV, #MF, store checks, FSTP1, FYL2XP1), FXSAVE/XSAVE pointers, padding and fault address, VCVTPS2PH, alignment before limit, RCPPS/RSQRTPS.

### KVM: privileged behaviour

Privileged behaviour cannot be observed from user mode. `test/hardware.py` prepares a bundle to run on the EPYC with `/dev/kvm` (QEMU `-accel kvm -cpu host`), then compares locally:

```
$ python3 test/hardware.py prepare test/out/kvm --count 10000          # --arch i386 x86_64 sys (default: all)
$ python3 hardware.py run kvm                                            # on the EPYC, in the copied bundle
$ python3 test/hardware.py compare test/out/kvm-returned                 # here
```

`i386`/`x86_64` run random single instructions in the ring-3 harness; `sys` runs the system-test kernel's three passes (MODEL-ONLY parts included, no QEMU rule) and lists every line where `x86sys` differs (`sys/<pass>.diff`). Under KVM the processor executes instructions, paging, gates, task switches and mode transitions; the APICs, PIC/PIT, SMM chipset, NMI delivery and nested SVM are KVM's (no hardware evidence). The `sys` path has run with TCG in place of KVM, not yet under KVM.

### Earlier native campaigns (integer core, x86-64)

These run on an x86-64 Linux server without root or KVM; each instruction executes in user mode and signal handlers capture the result, for both models:

```
$ python3 test/native.py prepare test/out/run --count 20000 --seed 1    # or --memory, --hunt, --focused-sse
$ bash test/native_remote.sh test/out/run.tar.gz user@host
$ python3 test/native.py compare test/out/run-returned --prepared test/out/run
```

`--memory` adds memory operands on writable, read-only or unmapped pages; `--hunt` targets areas earlier runs missed (`test/native_hunt.py` groups its mismatches). On an AMD EPYC 7742, about 475,000 observations across four campaigns (before the Zen 2 work) all match. Bugs found this way and by the Linux boot (regression tests: `python3 test/rmw_regression.py`, `python3 test/stack_regression.py`):
- AAS ignored the borrow out of AL.
- LOCK on non-lockable instructions did not raise #UD.
- Read-modify-write instructions skipped the write-back for a zero shift count and for an unchanged ARPL.
- Read-modify-write operands were translated as reads, giving the wrong page-fault error code.
- PUSHA and POPA restored the wrong state after a fault, and ENTER did not check its final stack byte.
- The second immediate of far pointers and ENTER re-read the first (found by the Linux boot).
- x86-64 SSE: wrong MXCSR flags with unmasked exceptions, and flush-to-zero at the underflow boundary.

The native oracle runs each case as 32-bit code in compatibility mode under 64-bit Linux; `x86fp --compat` does the same on the model (EFER, CR4 and 4-level identity-mapped tables as Linux sets them on a 7742, CS 0x23 with L = 0), plain `x86fp` legacy protected mode. Both give identical output outside the `longmode` family (`test/fp_model_check.py`; also on the 116,715 cases of the earlier `ia32-fp-hardware` campaigns, including 3,034 page faults).

## Open questions for the EPYC

Every place where the model's behaviour is a choice the manuals do not settle for Zen 2, or a value not yet confirmed. "native `family`": a family of the user-mode bundle ('observe' cases are recorded, not failed); "KVM sys": `test/hardware.py --arch sys` (no hardware evidence for what KVM emulates: APICs, PIC/PIT, SMM chipset, NMI delivery, nested SVM). U = observable from a ring-3 32-bit program under 64-bit Linux, S = needs ring 0, U* = observable but no native case (reason given). "**EPYC 7742:**" is the answer of the runs above; rows without it are privileged (the KVM harness has not run) or have no native case. Behaviour adopted from a triage table is not restated.

**Decoder**

| # | question | model | source | observed by |
|---|---|---|---|---|
| D1 | U: a 16-byte encoding of an undefined opcode (prefix-padded): #UD or #GP(0)? | decode the whole instruction, then #GP(0) for length > 15 (`Decode.lean`); QEMU raises #UD (`x86test` counts these) | SDM vol. 3, table 6-2 | native `open_questions` `len_*_16` (observe), `enc_fuzz` pad14..17. **EPYC 7742:** matches (3 + 3 cases; `enc_fuzz` with the lengths of D4) |
| D2 | U: are the ModRM/SIB/disp/imm8 of an *undefined* 0F 38, 0F 3A or VEX opcode fetched before the #UD? | yes: 0F 38 ModRM, 0F 3A ModRM + imm8, VEX the legacy layout (`opInfo`) | none (QEMU's layout) | native `open_questions` `len_0f38/0f3a/vex0f38_16` (observe; no page-end case). **EPYC 7742:** yes, with the layouts of D4 |
| D3 | U: 62 with mod = 11 and 8F with reg ≠ 0 (EVEX/XOP elsewhere) | #UD | APM vol. 3: Zen 2 has no EVEX/XOP | native `open_questions` `evex_xop`, `enc_fuzz`. **EPYC 7742:** #UD (5 cases); 62 mod = 11 is the 2-byte BOUND form (419 over-long EVEX encodings: #UD); 8F has the XOP layout (D4) |
| D4 | U: the length of undefined encodings (visible through the 15-byte limit) | the 7742's (extended-run triage: XOP, unknown VEX maps, 0F 0F, 0F 78, UD0/UD1, VEX.0F 0F and 8x) | none | native `enc_fuzz`, `code16`. **EPYC 7742:** answered; model fixed |

**General-purpose extensions and core integer**

| # | question | model | source | observed by |
|---|---|---|---|---|
| G1 | U: undefined flags of LZCNT/TZCNT, ANDN/BLSx/BZHI, BEXTR | the 7742's (first-run triage) | APM: undefined | native `gpr_bitcount`, `gpr_bmi` (raw values recorded). **EPYC 7742:** LZCNT/TZCNT (102 cases) and BEXTR (46) differed, adopted; ANDN/BLSx/BZHI matched |
| G2 | U: BZHI with index ≥ 32 | source unchanged, CF = 1 | SDM pseudocode, APM prose | native `gpr_bmi` (strict). **EPYC 7742:** matches (46 cases) |
| G3 | U: RORX with VEX.vvvv ≠ 1111b | #UD | SDM (the APM lists no #UD) | native `gpr_bmi`, vvvv 0..2 (strict). **EPYC 7742:** #UD (40 cases), model fixed; TCG executes (`qemuAsHardware`) |
| G4 | U*: do CLFLUSH/CLFLUSHOPT/CLWB trigger data breakpoints? | never | APM silent (UNCONFIRMED in `Gpr.lean`) | no native case (needs DR7: ptrace); KVM sys has no case |
| G5 | U*: CLZERO alignment of the offset or of the linear address | linear address | APM silent | no native case (needs a DS base not 64-byte aligned, i.e. an LDT segment) |
| G6 | U: RDPRU CF for an unsupported ECX | EDX:EAX = 0, flags unchanged | APM: "CF modified" (UNCONFIRMED) | native `gpr_rdpru` (strict). **EPYC 7742:** flags unchanged (4 cases); model fixed |
| G7 | U: MONITOR/MWAIT(X) wake-up corner cases (silent stores, far transfers, masked timer) | documented in `Gpr.lean` | SDM MWAIT, APM | timing only; native `gpr_monitorx` records register and fault outcome |
| G8 | U: SHLD/SHRD r16 with a count of 17..31 | the 48-bit rule (extended-run triage) | undefined (SDM, APM) | native `open_questions` `shld_shrd_r16_count`, `shift16_rules`. **EPYC 7742:** 5 first-run cases (source 0), then 3,551 (100%); model fixed |
| G9 | U: AF after AND/OR/XOR/TEST | 0 | undefined | integer campaigns. **EPYC 7742:** AF = 0 (19,789 cases), compared strictly now |
| G10 | U: ENTER with a 16-bit operand size and a 32-bit stack: all of EBP written? | BP only | APM `rBP.v = temp_RBP`, SDM `BP ← FrameTemp`; TCG keeps EBP[31:16] | native `int_directed` (`66c80400`), `code16`. **EPYC 7742:** BP only (29 cases); model fixed |
| G11 | U: undefined results and flags of the integer set | the 7742's (undefined-flag table; BSWAP r16) | undefined (SDM, APM) | native `int_core`, `int_directed`, `shift16_rules`, `code16`, `enc_fuzz` (strict now). **EPYC 7742:** deterministic (77,275 cases, 100%; BSWAP r16 234); model fixed |
| G12 | U: LOOPE/LOOPNE with F2/F3 | the last prefix selects the condition | the manuals give none | native `enc_fuzz`, `code16`. **EPYC 7742:** so (83 cases; LOOP and JCXZ ignore them); model fixed (TCG ignores them) |
| G13 | U: ARPL's memory access; MOV CRn with an unimplemented n at CPL 3; CMPS's read order; REP INS/OUTS with a zero count | the 7742's (extended-run triage) | SDM ARPL pseudocode; APM MOV CRn lists both; no order stated | native `int_core`, `enc_fuzz`, `code16`. **EPYC 7742:** 123, 123, 266, 12 cases; model fixed |

**SSE (SSE..SSE4a, MisalignSse)**

| # | question | model | source | observed by |
|---|---|---|---|---|
| S1 | U: EXTRQ/INSERTQ bits 127:64 and index + length > 64 | bits 127:64 cleared (QEMU and Bochs keep them), bits above 63 read as 0 | APM vol. 4: undefined | native `sse4a` (observe). **EPYC 7742:** cleared by all four forms (288 cases), model fixed; index + length > 64 matches |
| S2 | U: HADDPx/HSUBPx with two NaNs in a pair | the lower element's NaN for both | SDM/APM table 4-7 with the instruction text | native `sse3_hadd_nan`, two-NaN rows of `sse3_arith` (observe). **EPYC 7742:** lower for HADD as for HSUB (68 HADD cases differed); model fixed |
| S3 | U: DPPS/DPPD exception staging | per stage; masked-out products +0 | SDM DPPS | native `sse41_dp`. **EPYC 7742:** matches (1,000 cases, 113 observe) |
| S4 | U: PCMPxSTRx equal-ordered with an empty prototype / partial match at the end | SDM, where AMD's pseudocode differs | APM vol. 4 1.5.3 vs SDM | native `sse42_strings` imm8 & 0Ch = 0Ch (observe). **EPYC 7742:** matches (16,384 cases, 4,096 observe) |
| S5 | U: RCPPS/RSQRTPS result bits | the 7742's tables (`X86/Zen2Rcp.lean`; the former correctly rounded results kept as `FP.rcpSpec`/`FP.rsqrtSpec`) | implementation specific (≤ 1.5·2⁻¹²) | native `sse_random` 52h/53h, `avx_ops`, `avx_random`, `sse_rcp_sweep` (strict now). **EPYC 7742:** reconstructed from the sweep ("RCPPS/RSQRTPS" above); all 52,794 lanes; model fixed |
| S6 | U: #AC for misaligned MOVUPS/MOVDQU with EFLAGS.AC = 1 | #AC (16 bytes) | APM vol. 2, table 8-7 | native `alignment_check` (observe). **EPYC 7742:** matches (offsets 1..12, 14 cases) |
| S7 | U: #AC for MASKMOVQ/MASKMOVDQU | 8-byte alignment for both, whatever the mask | APM table 8-7 does not single them out | native `alignment_check` (strict). **EPYC 7742:** MASKMOVDQU at offset 8 stores without #AC (1 case), model fixed; MASKMOVQ matched |
| S8 | U: #AC or #PF first for a misaligned access to an unmapped page | #AC (before paging, as Bochs) | APM 8.2.17 silent | native `alignment_check` `unmapped_load`, `fxsave_align`. **EPYC 7742:** matches (3 cases); the FXSAVE family's #AC, #GP-before-#SS and fault-address order in the triage tables (both pages faulting not observed) |
| S9 | U*: MXCSR_MASK | 0x2FFFF (MisalignSse) | APM vol. 1, 4.2.2 | no native case (image hashes leave MXCSR_MASK out, the oracle returns no image bytes); KVM sys: `simd` FXSAVE lines |
| S10 | S: FXSAVE/FXRSTOR with CR4.OSFXSR = 0 | MXCSR/XMM neither saved nor restored | SDM: implementation dependent | KVM sys (`t_simdx.c`) |
| S11 | U: MMX/x87 transitions: EMMS's TOP, CVTPI2PS m64, a fault after the transition, MASKMOVQ's fault address | the 7742's (extended-run triage; no #MF for CVTPI2PS m64, inferred like CVTPI2PD m64) | SDM vol. 1, table 9-2 (EMMS); CVTPI2PS pages differ | native `enc_fuzz`, `code16`, `fpu_pointers`. **EPYC 7742:** 49, 8, 40, 19 cases; model fixed |
| S12 | U: VCVTPS2PH to memory: destination checks vs MXCSR flags/#XM | destination first | none | native `enc_fuzz`, `avx_random`. **EPYC 7742:** so (5 cases); model fixed |

**Crypto**

| # | question | model | source | observed by |
|---|---|---|---|---|
| C1 | U: "NP" SHA instructions with 66/F2/F3 | #UD (Bochs; TCG executes them) | SDM 3.1.1.1 | native `sha_prefix` (observe). **EPYC 7742:** matches |
| C2 | U: misaligned SHA memory operand | executes | SDM table 2-21: class 4; TCG does not check | native `sha` offset rows (observe). **EPYC 7742:** executes (28 cases), model fixed |

**AVX, AVX2, FMA3, F16C**

| # | question | model | source | observed by |
|---|---|---|---|---|
| A1 | U: VMASKMOVPS/PD masked-out elements: accesses, faults, #AC | never accessed; stores check every selected element first | SDM (APM: implementation dependent) | native `avx_maskmov` (observe), `avx_alignment`. **EPYC 7742:** matches (128; no #AC for VMASKMOVPS) |
| A2 | U: VZEROALL with VEX.W = 1 | W ignored | APM exception table: #UD; its encoding table: WIG | native `avx_encoding` `vzeroall_w1` (observe). **EPYC 7742:** executes (matches) |
| A3 | U: VMOVSS/VMOVSD load with VEX.vvvv ≠ 1111b | #UD | SDM note, APM exception table (store only) | native `avx_encoding` (strict). **EPYC 7742:** #UD for the load too (4 cases); model fixed |
| A4 | U: VEX.W/is4[7]/vvvv[3]/VEX.L of LIG forms outside 64-bit mode | ignored, except vvvv[3] where 1111b is required and W1 of VPEXTRD/VPINSRD (#UD); VPERMQ/VPERMPD ignore W | SDM 2.3.5.6, 2.3.9; APM "x" encodings | native `avx_encoding`, `avx2_encoding`. **EPYC 7742:** W1 of VMOVD, VCVTSI2SS, VCVTSS2SI, is4[7], L of LIG forms ignored (matches); the exceptions found by the triage; model fixed |
| A5 | U: VDPPS ymm exception stages across the lanes | stages span both lanes | SDM ("order of execution") | native `avx_observe`. **EPYC 7742:** matches (12 cases) |
| A6 | U: VHADD/VHSUB ymm two-NaN pairs | as S2 | as S2 | native `avx_observe`. **EPYC 7742:** as S2; model fixed |
| A7 | U: VPMASKMOVD/Q masked-out elements | never accessed; stores checked first | APM implementation dependent vs SDM | native `avx2_maskmov`. **EPYC 7742:** matches (128, 72 observe) |
| A8 | U: #AC alignment of VPMASKMOV | none | APM vol. 4 page (32) vs vol. 2 table 8-7 (16) | native `avx2_alignment`. **EPYC 7742:** no #AC (12 cases); model fixed |
| A9 | U: #AC for gather elements | none | model choice | native `avx2_alignment` gathers. **EPYC 7742:** no #AC (5 cases); model fixed |
| A10 | U: gather mask and destination after a fault | mask elements not normalized; upper bits unchanged | SDM normalizes, APM silent | native `avx2_gather` `pf_*`. **EPYC 7742:** matches (412, 6 observe) |
| A11 | U*: data breakpoint of a loaded gather element vs a later fault | the fault wins, the trap is dropped | SDM gather text | no native case (needs DR7: ptrace) |
| A12 | U: FMA 0·∞ + QNaN | QNaN, no IE | SDM vol. 1 table 14-17, IEEE 754-2008 7.2; AMD silent | native `fma_special`. **EPYC 7742:** matches (264, 72 observe) |
| A13 | U: FMA NaN choice with several NaN operands | first of x, y, z in x·y + z | SDM table 14-17; AMD silent | native `fma_special`, `avx2_ops`. **EPYC 7742:** matches |
| A14 | U: F16C with DAZ/FTZ | VCVTPH2PS ignores DAZ (no DE), VCVTPS2PH ignores FTZ | APM vol. 4 (TCG differs) | native `f16c` (strict). **EPYC 7742:** matches (68) |

**XSAVE**

| # | question | model | source | observed by |
|---|---|---|---|---|
| X1 | U*: XINUSE/XMODIFIED (init and modified optimizations) | exact tracking (`Xsave.lean`) | SDM vol. 1 13.6, 13.8.3 (latitude) | no discriminating native case (the oracle loads every component from the signal frame, XINUSE = 7); KVM sys: `xsave` lines |
| X2 | U: MXCSR saved/restored for RFBM[1] or RFBM[2] | either bit (Intel) | APM vol. 4 ("bits 0 or 1") vs vol. 2 11.5.9 / SDM | native `xsave_save`, `xsave_restore` (strict). **EPYC 7742:** matches |
| X3 | U*: XRSTOR header bytes checked | 8..23 standard, 16..63 compacted | APM vol. 4 vs SDM 13.8.1 | no discriminating native case (random headers fail both rules); KVM sys: `xsave` header cases |
| X4 | S: XRSTORS #GP rule for XSTATE_BV & ~IA32_XSS | SDM | APM vs SDM | KVM sys |
| X5 | U*: faults on pages of components not touched | not probed | undocumented | no native case (the data area is one mapping) |
| X6 | U: XSaveErPtr | FXSAVE/XSAVE write FOP/FIP/FCS/FDP/FDS only with FSW.ES = 1; restores always load them | APM vol. 3 E, 8000_0008:EBX[2]: "always save" | native `fpu_pointers`, `xsave_padding`. **EPYC 7742:** images with ES = 0 hold zeros although FNSTENV of the same state stores the pointers; model fixed |
| X7 | U: XGETBV with 66/F2/F3 | #UD | SDM "NP" | native `open_questions_xsave` (observe). **EPYC 7742:** matches (4 cases) |

**x87**

| # | question | model | source | observed by |
|---|---|---|---|---|
| F1 | U: SNaN m32/m64 operand of D8/DC arithmetic: quieted before the NaN choice? | no (QEMU and Bochs: yes) | SDM silent | native `open_questions` `x87_snan_memory` (observe). **EPYC 7742:** no, ST(0)'s QNaN is returned (3 cases); model fixed |
| F2 | U: transcendental result bits, Pi/2 reduction, FPTAN/FSINCOS NaN, FSINCOS C1 | correctly rounded, 66-bit Pi; PE for every finite nonzero F2XM1/FYL2X/FYL2XP1 result | SDM vol. 1 8.3.8, 8.3.10 | native `x87_transcendental`, `x87_trans_boundary`. **EPYC 7742:** FSIN/FCOS/FPTAN/FSINCOS identical (1,688 cases); 8 results 1 ulp off; PE for exact results (model fixed) |
| F3 | U: F2XM1 with abs(x) > 1, FYL2XP1 outside its range | the 7742's (both triage tables) | SDM undefined; AMD's range | native `x87_transcendental`, `x87_trans_special`. **EPYC 7742:** answered (430 + 52 cases); model and `x87ref.py` fixed |
| F4 | U: FYL2X/FPATAN with two NaNs | larger significand (SDM table 4-7); QEMU takes ST(0) | SDM vol. 1 table 4-7 | native `open_questions` `x87_trans_two_nan` (observe). **EPYC 7742:** matches (4 cases) |
| F5 | U: FIP/FDP/FOP update policy | every non-control instruction updates FIP/FOP; FDP with a memory operand | SDM | native `fpu_pointers`. **EPYC 7742:** visible only with ES = 1 (X6): 4,335 first-run and 7,401 extended-run cases agree; compared in every case now (858,603 agree) |
| F6 | U: FSW loaded by FLDENV/FRSTOR/FXRSTOR/XRSTOR with an unmasked flag and ES = 0; FNSTENV's ES; #MF before FLDCW/FLDENV/FRSTOR; x87 stores with an unmasked exception and an inaccessible destination; FSTP1 with an empty ST(0) | the 7742's (extended-run triage) | SDM (FLDENV etc. list #MF) | native `x87_control_load`, `fenv16`, `fpu_pointers`, `enc_fuzz`. **EPYC 7742:** 207, 20, 20, 35 + 1, 3 cases; model fixed (FSTP1 with IE unmasked and DD D8+i/DF D0+i not observed) |

**System (paging, SYSCALL/SYSENTER, MSRs)**

| # | question | model | source | observed by |
|---|---|---|---|---|
| SA1 | S: SMAP on implicit supervisor accesses at CPL 0 with EFLAGS.AC = 1 | checked regardless of AC | SDM 4.6.1 vs APM vol. 2 5.6.6 | KVM sys `sysa.smap.implicit` |
| SA2 | S: call-gate parameters read at the caller's or the new CPL | caller's (QEMU) | neither manual's CALL pseudocode | KVM sys (`t_callgate.c`, with SMAP) |
| SA3 | S: SYSENTER in real mode | #UD | APM vol. 3 exception table vs its text and the SDM (#GP) | KVM sys |
| SA4 | S: legacy SYSRET keeps SS's cache and RPL; SYSCALL keeps SS.RPL | as stated | APM SYSRET/SYSCALL pseudocode | KVM sys `sysa.*` |
| SA5 | U: LOCK MOV CRn (n ≠ 0) at CPL 3 | #UD before the CPL check (LOCK MOV CR0 = CR8: #GP) | APM defines LOCK only for CR0 | native `open_questions` `lock_mov_cr` (observe). **EPYC 7742:** matches (5 cases) |
| SA6 | S: #PF I/D bit for a SMEP fetch without NXE | set (Intel, QEMU) | APM 8.4.2 vs SDM 4.7 | KVM sys `pgf` |
| SA7 | S: global pages across MOV CR3 and task switches | kept | implementation defined | KVM sys `sysa.pge*`, `pgt` |
| SA8 | S: A bit of a long-mode 1 GiB/2 MiB leaf with a reserved bit | not set | APM 5.4.2 silent | KVM sys `lmf` |
| SA9 | S: WRMSR of a reserved MTRR memory type | #GP(0) | SDM 11.11.2 (APM silent) | KVM sys `sysa.msr*` |

**System B (NMI, VME, IRPerf, SMM, INIT)**

| # | question | model | source | observed by |
|---|---|---|---|---|
| SB1 | S: does a faulting IRET end NMI blocking? | no | APM vol. 2 8.1.4 vs SDM 7.7.2 | KVM sys `nmiq.*` (KVM's NMI blocking: no hardware evidence) |
| SB2 | S: does INIT end NMI blocking? | unchanged | neither manual | none |
| SB3 | S: armed MONITOR across INIT | kept | not specified | none |
| SB4 | S: GIF after INIT | 1 | no row in APM table 14-1 | none |
| SB5 | S: IRPerf retirement corner cases | rules in `SysB.lean` | APM 13.2.1 silent | KVM sys `irperf.*` (if KVM passes IRPerf through) |
| SB6 | S: VME redirection bitmap beyond the TSS limit | #GP(0) | AMD silent | KVM sys `vme.irb.limit` |
| SB7 | S: task switch into a 16-bit TSS: upper register halves | kept (QEMU) | none | KVM sys `tsf` |
| SB8 | S: SMM save-state attribute layout, GPR high halves | QEMU's layout, zero-extended | APM does not define the layout | KVM sys `smm.*` (SMM emulated) |
| SB9 | S: which CPU an APM-port (B2h) SMI goes to | the CPU executing the OUT | chipset dependent | none (chipset) |

**Long mode**

| # | question | model | source | observed by |
|---|---|---|---|---|
| L1 | S: far transfer to a code descriptor with L = D = 1 | #GP(selector) (Intel) | APM 4.8.1 "reserved", no AMD rule | KVM sys model-only `lmm.jmp.rsvdcode` |
| L2 | S: error code when a 64-bit IDT gate's target is not 64-bit code | the selector | APM READ_DESCRIPTOR vs 4.8.4 prose | KVM sys `lm.*` gate cases |
| L3 | U*: GPR bits 63:32 when compatibility code enters 64-bit mode | zero (the bridge zero-extends) | APM: undefined outside 64-bit mode | no native case (the oracle must not run 64-bit code) |
| L4 | S: same-privilege CALL through a 64-bit call gate | flat 64-bit pushes (QEMU) | APM CALLF pseudocode | KVM sys `lm.*` |
| L5 | S: RSM with LME/LMA and PG = 0 | LMA = LME ∧ PG ∧ PAE | APM 10.4 | KVM sys `lmm.*` (SMM emulated) |

**Multiprocessor platform** (all S; the KVM run gives none of these hardware evidence: its APICs are KVM's)

| # | question | model | source |
|---|---|---|---|
| P1 | lowest-priority ties among focus processors; APR bits compared | highest APIC ID; APR bits 7:4 | APM 16.6.2 leaves it open |
| P2 | polarity of SVR.FCC | set = focus checking disabled | APM 16.4.7 vs 16.6.2 |
| P3 | XAIDN (4/8-bit APIC ID matching) | always 8-bit | APM |
| P4 | IER writes | only with IERN = 1 | APM 16.3.6 |
| P5 | what a disabled APIC accepts | AE = 0 nothing; ASE = 0 SMI/NMI/INIT/STARTUP/remote read/ExtINT | APM 16.5 |
| P6 | illegal vectors 0..15, SIV/RIV/SAE/RAE | sender SIV, receivers drop and set RIV, SAE when nobody accepts, RAE never | APM |
| P7 | timer divide sampling, delivery status | divide sampled at the initial-count write; status always 0 | APM |
| P8 | APIC version register | 10h (UNCONFIRMED for the 7742) | APM 16.3.4 "1Xh" |
| P9 | I/O APIC version, level-programmed NMI/INIT/SMI/ExtINT entries | 11h; edge-triggered | 82093AA datasheet (the 7742's I/O APIC is not an 82093AA) |
| P10 | x2APIC IER reserved bits | not checked | APM 16.11.3 |
| P11 | I/O APIC ID | N for N ≤ 14 CPUs, else 0 | platform choice |

**SVM** (all S; KVM runs a nested guest with its own emulation, so the KVM run is no hardware evidence)

| # | question | model | source |
|---|---|---|---|
| V1 | host state at VMRUN | kept on chip; VM_HSAVE_PA page not written; #VMEXIT restores DR6/DR7 with breakpoints off, CR2 keeps the guest's | APM 15.5.1, 15.6 |
| V2 | VMCB clean bits | ignored: every field reloaded | APM 15.15.1 |
| V3 | TLB across VMRUN; reserved TLB_CONTROL | guest starts empty, host entries set aside; VMEXIT_INVALID (as KVM) | APM reserved |
| V4 | VMCB register loading | CR0 reserved bits read 0, LMA recomputed, CR3[63:48] MBZ for long-mode guests | model choice |
| V5 | VMCB CPL ≠ CS.RPL | the simulation stops (unsupported) | model limitation |
| V6 | event injection details | error code only with EV; type 3/4 push nRIP; type 3 with another vector VMEXIT_INVALID | APM 15.20 |
| V7 | SKINIT | CPU-state effects only | APM vol. 3 SKINIT |
| V8 | VMSAVE/VMLOAD virtualization | never recognized (no 64-bit host) | APM 15.33.1 |
| V9 | SMI in a guest | SMM in the guest's context (no intercepts, no nested paging); RSM does not re-read the save map's SVM fields (FF38h written as the host's CR3, "SVM Host CR3"; KVM's `svm_host_cr3`); SMM_CTL ENTER/EXIT hold SMIs and block NMIs without entering SMM, locked by HWCR.SmmLock | APM 15.22, 15.30.3, table 10-1 |
| V10 | LbrVirt, AVIC, GMET | not reported | APM |
| V11 | guest-physical address ≥ 4 GiB with a 32-bit or PAE host | not-present NPF | APM silent (UNCONFIRMED) |
| V12 | VMRUN in SMM | unsupported (stops) | APM: undefined |
| V13 | RFLAGS.RF and the interrupt shadow saved by a #VMEXIT | those the intercepted instruction started with (also for an intercepted exception it raises) | APM 15.7.1 "as of the moment the intercept triggers"; TCG agrees |
| V14 | intercepted INTR/NMI/SMI in the guest's interrupt shadow | exit at once (the VMCB records the shadow) | KVM: "vmexits aren't blocked by the interrupt shadow"; TCG holds them; APM silent |
| V15 | FERR_FREEZE | never freezes (CR0.NE = 0: FERR# raises IRQ13 and execution continues); the intercept exits (7Eh) where the freeze would be, unless the IGNNE MSR asserts IGNNE | APM table 15-7, appendix C (exit 7Eh); x87 legacy FERR handling |
| V16 | INIT in a guest without the INIT intercept | GIF = 1 (as QEMU), VM_CR.SVMDIS cleared unless LOCK, host PAT/SPEC_CTRL restored, the guest's TLB entries dropped | APM 15.30.1, table 14-1 (no SVM rows) |
| V17 | nested walk: leaf A/D bits on a refused access; a PAE guest's PDPTEs under nested paging | A/D not set; PDPTEs read at each walk through the nested tables | APM silent; `svmref.py` marks the dependent cases |
| V18 | long-mode guest CR3/GDTR/IDTR, VMLOAD TR/LDTR base above 4 GiB | unsupported (the model's CR3 and table bases have 32 bits) | model limitation |

**CPUID and MSR values**

| # | question | model | source | observed by |
|---|---|---|---|---|
| M1 | U: unnamed dump bits (8000_0007:EBX[4], 8000_0008:EBX[6, 10]) | masked | no name in APM rev. 3.33 | the bundle's `cpuid.txt`. **EPYC 7742:** set on this machine too (still masked); StibpAlwaysOn (8000_0008:EBX[17]) clear on it, now masked |
| M2 | U/S: PKRU in leaf 0xD without PKU; XSETBV with XCR0[9] | not reported; #GP(0) | APM 11.5.2, 5.6.7 | `cpuid.txt`; XSETBV: none. **EPYC 7742:** leaf 0Dh lists XCR0 bit 9 without PKU here too |
| M3 | S: MCG_CAP bank count | 23 (UNCONFIRMED) | family 17h PPR not available | KVM sys (KVM's value) |
| M4 | S: width of SYSENTER_CS/ESP/EIP | upper bits ignored (UNCONFIRMED) | none | KVM sys `sysa.msr*` |
| M5 | S: LS_CFG/DE_CFG reserved bits; CPUID override MSRs C001_1004/5 | UNCONFIRMED; stored without changing CPUID | PPR not available | KVM sys (KVM's) |
| M6 | S: PATCH_LEVEL (8Bh) | reads 0, WRMSR #GP(0) (Linux guest below) | AMD OSRR 56255 | KVM sys `msr8b.amd` |
| M7 | S: Intel MSRs 17h, C1h/C2h, 186h/187h | #GP(0) with the AMD identity | not in APM vol. 2 appendix A | KVM sys `msr.intel` |

## Bugs found during the Zen 2 work

Found by reviews (a second agent reading a diff against the APM/SDM), fuzzers, Linux and integration checks; each fixed, with a regression test or theorem:
- VEX.256.NP.0F 70 executed as VPSHUFLW instead of #UD (review; hence the `vexnb` walk; theorem `vexExec_np70`).
- INT n read the TSS redirection bitmap outside virtual-8086 mode with CR4.VME, raising #GP(0) with short TSS limits; events from virtual-8086 mode pushed their ring-0 frame at CPL 3 (review; `t_review.c`, theorems `intN_noVme`, `leaveV86_cpl`).
- XSAVE/XSAVEC/XSAVES wrote zero x87 error pointers unless FSW.ES = 1 (review; `xsaveref.py` found 27 of 600 cases); the 7742 later showed exactly that behaviour (X6).
- VDPPS ymm staged exceptions per lane; HADDPx returned the lower element's NaN of a two-NaN pair (review; the 7742 later showed lower-first, S2).
- A STARTUP accepted while an INIT was pending was lost, so Linux started its AP only at some quanta; APIC timers and MWAIT wake-ups of CPUs not running depended on the quantum (SMP Linux checks, platform review).
- SMM used the legacy 32-bit save map and stopped in long mode; RETF/IRET to 64-bit code at an outer level and same-privilege 64-bit call-gate CALLs used the wrong stack pointer; INIT and RESET states corrected against APM table 14-1; I/O APIC NMI/INIT/SMI/ExtINT entries could be level-triggered; EOI cleared TMR (platform review).
- An unassigned VEX.0F 8x encoding was decoded with the wrong length (the 15-byte-limit tests).
- Integration: the Intel MSRs 17h, C1h/C2h, 186h/187h existed with the AMD identity (now #GP(0)); the native comparison rejected the `longmode` BOUND #BR (SIGSEGV under Linux) as an "unexpected signal"; the TCG smoke check ran only single-campaign bundles; `isa_forms.py` rows were broader than Zen 2, so the 'ud' family never tested those forms (found by the LLVM cross-check).
- The EPYC 7742 runs: every model bug of the two triage tables above and the CPUID bit StibpAlwaysOn, which the machine lacks; each with hardware regression cases in `test/epyc_regression.py`.

## Linux guest
`guest/build.sh` builds Linux 6.12.111 from `tinyconfig` plus `guest/kernel.fragment` (a 486SX-class kernel with math emulation compiled in but unused, since CPUID reports the FPU; an 8250 console; no SMP, APIC, PCI or ACPI) and an initramfs with Debian's static i386 BusyBox. Run it in a Linux VM, e.g. on macOS:

```
$ limactl start --name=kbuild template:debian
$ limactl shell kbuild -- sudo apt-get install -y build-essential flex bison bc libelf-dev cpio lz4 gcc-i686-linux-gnu
$ limactl shell kbuild -- bash guest/build.sh          # also: build.sh smp, build.sh bigsmp
```

With the AMD identity Linux takes its AMD paths. What it prints about the CPU (the SMP kernels print the same):
- `CPU: AMD EPYC 7742 64-Core Processor (family: 0x17, model: 0x31, stepping: 0x0)`; `/proc/cpuinfo`: `vendor_id AuthenticAMD`, `cpu family 23`, `model 49`, `cpuid level 16`, `cache size 512 KB`, `address sizes 48 bits physical, 48 bits virtual`, the reported features (no `xsaves`: Linux clears it for AMD erratum 1386, hence `x86/fpu: Enabled xstate features 0x7, context size is 832 bytes, using 'compacted' format` with XSAVEC; no `ht` with one CPU).
- `microcode: Current revision: 0x00000000` and `Zenbleed: please update your microcode for the most optimal fix`: PATCH_LEVEL reads 0, as on a 7742 without a loaded patch (M6); Linux then sets the Zenbleed chicken bit in DE_CFG, which the model stores.
- `bugs: sysret_ss_attrs spectre_v1 spectre_v2 spec_store_bypass retbleed smt_rsb srso ibpb_no_ret vmscape` (Linux's list for Zen 2; mitigations off: `CPU_MITIGATIONS=n`).
- `Performance Events: AMD PMU driver` with 4 generic counters (PerfCtrExtCore is masked; a real 7742 reports "Fam17h+ core perfctr" with 6).
- `Last level iTLB entries: 4KB 1024, 2MB 1024, 4MB 512`, `dTLB ... 1GB 0` (leaves 8000_0005/6); `tsc: Detected 99.996 MHz processor` (the virtual 100M instructions per second); `process: using mwait in idle threads`; system calls via SYSENTER (`do_SYSENTER_32`).
- No warning, `BUG`, `Oops` or call trace; the boot takes 54,168,236 instructions (52,180,389 with the former Intel identity at the same commit).

`guest/workload.sh` runs hashing, sort, a gzip round trip, shell arithmetic, floating-point awk, tmpfs I/O and `/proc` reads (the transcendentals were checked in the guest with a small static program: bit-identical to `test/sys/x87ref.py`). Its output on the model is byte-identical to `guest/workload.qemu.txt`, which `guest/qemu-workload.sh` regenerates (qemu-system-i386, EPYC-Rome CPU of `test/qemu-cpu.sh`, 128 MiB; `-cpu pentium2` gives the same bytes).

`guest/build.sh smp` builds `bzImage-smp` (`kernel-smp.fragment`: SMP, APIC, I/O APIC, MP tables, NR_CPUS = 8; `initramfs-smp.cpio` adds `smp.sh`), `guest/build.sh bigsmp` `bzImage-bigsmp` (`kernel-bigsmp.fragment`: X86_BIGSMP, NR_CPUS = 64). `guest/smp-check.sh N` (`KERNEL=guest/bzImage-bigsmp` for N > 8) boots it with `x86run --smp N` (the loader writes MP tables) and under QEMU `-smp N,sockets=N`, runs `smp.sh` (CPU counts, IO-APIC interrupts, per-CPU pinned jobs) and `workload.sh`, and compares the transcripts (steps 10 and 11 at the top). Linux takes the topology from CPUID, runs its timer through the I/O APIC (`..TIMER: vector=0x30 apic1=0 pin1=2`) and, as an AMD system, does not require unique I/O APIC IDs (no 14-CPU limit as with the Intel identity).

DOOM ([`doom/`](doom/README.md), `doom/test.sh 100`): the first 100 demo frames are identical on QEMU and on the model with the AMD identity (2,236,019,717 instructions, ≈ 9 min).
