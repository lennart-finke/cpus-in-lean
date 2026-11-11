# Extending the IA-32 model to Zen 2

How to add an ISA or system feature without editing the lines other workstreams edit. Read the
module documentation of `X86/Decode.lean`, `X86/Cpuid.lean`, `X86/Dispatch.lean` and of your
`X86/Ext/*.lean` file as well.

## Opcode numbering and `Inst`

`Inst.op = map * 0x100 + opcode byte`: 0x000–0x0FF one-byte, 0x100–0x1FF `0F xx`, 0x200–0x2FF
`0F 38 xx` (always ModRM), 0x300–0x3FF `0F 3A xx` (always ModRM + imm8 in `imm`). VEX instructions
use the same numbering with `vex = true` (VEX.mmmmm 1/2/3; other maps give `op < 0x100` and #UD).
Their ModRM/SIB/displacement/immediates are laid out as in the legacy map with the same opcode
(`opInfo`): VEX.0F 77 has no ModRM, VEX.0F 70–73/C2/C4–C6 and VEX.0F3A have an imm8.

| field | meaning |
|---|---|
| `pp` | mandatory prefix, legacy and VEX alike: 0 none, 1 = 66, 2 = F3, 3 = F2 (legacy: the last F2/F3 wins over 66) — `Simd.pfx i = i.pp.toNat` |
| `vex`, `vvvv`, `vexL`, `vexW` | VEX prefix; `vvvv` is the register number (bit 3 ignored in 32-bit mode) |
| `rep`, `p66`, `lock`, `opsz`, `adsz`, `segOvr` | raw prefixes, as before (66 still sets `opsz`, e.g. for 66 F2 0F 38 F1 CRC32 r16) |
| `imm`, `imm2` | immediates; 66/F2 0F 78 (EXTRQ/INSERTQ) put their two imm8 in `imm` and `imm2` |
| `map`, `byte` | `op >>> 8`, `op &&& 0xFF` |

C4/C5 are VEX only if the next byte has bits 7:6 = 11 (else LES/LDS). 62 and 8F are not decoded as
EVEX/XOP: on Zen 2 their mod=11 / reg≠0 forms stay the #UD forms of BOUND and POP. `decode_len`
(`Proofs/State.lean`) depends on `decode`'s final `if n > 15 then gp 0`; keep it.

## Hooks: who owns what

`X86/Dispatch.lean` is fixed: it calls each module's hooks at the places below. A hook returns
`none` for forms it does not implement; then the next hook or the fallback runs. Implement only
your forms, return `none` for everything else, and never edit another module or `Dispatch.lean`.

| hook | called for (fallback) | owners |
|---|---|---|
| `Gpr.op0F?` | F3 0F B8 (#UD), F3 0F BC/BD (BSF/BSR), 0F 0D, 0F 18 (NOP), 0F 33 (#UD), F3 0F 09 (WBINVD) | Gpr |
| `Sse.op0F?` | F2/F3 0F 12, 0F 16, 0F 2B; 0F 78, 79, 7C, 7D, D0; F2 0F F0 (#UD) | Sse |
| `Sys.op0F?` | 0F 05, 07, 34, 35 (#UD); LOCK 0F 20/22 = AltMovCr8 (core) | Sys |
| 0F 01 register forms except SMSW/LMSW (#UD): `Gpr`, `Sys`, `Xsave`, `Svm`, `LongMode` `.op0F?` in that order | C8/C9 MONITOR/MWAIT, F9 RDTSCP, FA/FB MONITORX/MWAITX, FC CLZERO, FD RDPRU → Gpr; CA/CB CLAC/STAC → Sys; D0/D1 XGETBV/XSETBV → Xsave; D8–DF → Svm; F8 SWAPGS → LongMode | |
| 0F AE except FXSAVE/FXRSTOR/LDMXCSR/STMXCSR (memory /0–/3) and fences (register /5–/7), no prefix (#UD): `Xsave`, `Gpr`, `LongMode` | memory /4 /5 /6 XSAVE/XRSTOR/XSAVEOPT → Xsave; memory /7 CLFLUSH, 66 memory /6 /7 CLWB/CLFLUSHOPT → Gpr; F3 register /0–/3 → LongMode | |
| 0F C7 except /1 (#UD): `Xsave`, `Gpr` | memory /3 /4 /5 XRSTORS/XSAVEC/XSAVES → Xsave; register /6 /7 RDRAND/RDSEED, F3 /7 RDPID → Gpr | |
| `map2?` (0F 38, #UD): `Sse`, `Crypto`, `Gpr` | SSSE3/SSE4.x → Sse; 66 DB–DF AES, C8–CD SHA → Crypto; F0/F1 MOVBE/CRC32, F6 ADCX/ADOX → Gpr | |
| `map3?` (0F 3A, #UD): `Sse`, `Crypto` | SSSE3 PALIGNR/SSE4.x/PCMPxSTRx → Sse; 44 PCLMULQDQ, DF AESKEYGENASSIST, CC SHA1RNDS4 → Crypto | |
| `vex?` (#UD): `Gpr`, `Avx`, `Avx2` | VEX.0F38 F2–F7, VEX.0F3A F0 (BMI1/2) → Gpr; AVX (incl. VEX AES/PCLMUL, VZEROUPPER, VLDMXCSR) → Avx; AVX2, FMA3, F16C → Avx2 | |
| `msr?` (#GP): core (`Exec.coreMsr?`: EFER, APIC_BASE, 0x17, 0x8B, 0xC1/C2, 0x186/187, 0x1D9), then `Gpr`, `Sys`, `Xsave`, `Svm`, `LongMode`, `Smp` | return an `MsrImpl` (`rd`, `wr`; `MsrImpl.stored n mask` keeps it in `Cpu.msrs`) | |

`Dispatch.vexExec` raises #UD for every VEX instruction in real/virtual-8086 mode, after
66/F2/F3/LOCK and for unknown maps before calling `vex?` (theorems `vexExec_*`). The SSE/AVX
checks (CR4.OSXSAVE, XCR0[2:1], CR0.TS) are `Vex.vexCheck` in `X86/Ext/Vex.lean` (with `Vex.start` for the
per-instruction encoding rules and the 256-bit operand helpers; see its documentation), owned
by Avx; BMI does not use it.

Changes outside your module that are expected (and owned): Sys A — `X86/Machine.lean` paging
(SMEP/SMAP, PSE-36, global pages); Sys B (VME/PVI, NMI, exception classes) — `popf`/`iret` in
`X86/Exec.lean`, `X86/Sys.lean`, `X86/Step.lean`, `Flag.valid` (VIF/VIP are named in `Word.lean`);
LongMode — paging/translation; Smp — `X86/Dev.lean`, `X86/Machine.lean`; Sse — `Simd.vecAddr`
(MisalignSse), `Float.lean`; Avx2 — `Float.lean` (fma, binary16); Xsave — `Cpuid.leafD`.
Leave existing core code alone otherwise; reuse its helpers (`V128.lane/map2`, `pint`, `sseCheck`,
`sseStatus`, `vecAddr`, `rdXE`, `FP.cmp`, `Float.*`, `deliver`, `sysRd/sysWr`, `eaOff`, `rmwE`).

State: `SseState.ymmh` (YMM bits 255:128; legacy SSE keeps it, VEX.128 zeroes it), `CpuExt.xcr0`
(reset 1), `CpuExt.xss`, and one structure per owner in `X86/State.lean` (`GprState`, `SysState`,
`SvmState`, `LongModeState`) — add your fields only to yours. Bit names: `CR0.*`, `CR4.*`
(UMIP, FSGSBASE, OSXSAVE, SMEP, SMAP, ...), `EFER.*` (SCE, LME, LMA, SVME, LMSLE, FFXSR, TCE),
`XCR0.*`, `Flag.VIF/VIP` in `X86/Word.lean`.

## Adding a feature bit

`X86/Cpuid.lean`: flip your feature's line in `implemented` to `true` (one line per feature,
grouped by owner — do not reorder or touch other groups) once the feature is complete and tested.
CPUID then reports it (at its `Feature.loc`), and MOV CR4 / WRMSR EFER accept its control bit
(`Cpuid.cr4Writable`, `Cpuid.eferWritable`: VME/PVI, UMIP, FSGSBASE, OSXSAVE, SMEP, SMAP; SCE, LME,
SVME, FFXSR, TCE). `cpuid_former`, `cr4Writable_former` and `eferWritable_former`
(`Proofs/Ext.lean`) pin today's values: restate them for the new feature set (do not delete them;
e.g. `cpuid c 1 sub` with the new bit). The identity stays `.legacy` ("GenuineIntel" 0x619) until
the integration step flips `identity` to `.epyc7742`; with `.legacy`, an implemented feature in leaf
7/0xD/0x8000000x raises the reported maximum leaves automatically.

## Tests

1. **Random single instructions** (`validation/test/gen.py`, run by `test/run.sh`, format v2):
   remove your rows from `NOT_YET_IMPLEMENTED` in `validation/test/isa_forms.py` (one row per
   line; the list must end empty) and add rows to `IMPLEMENTED` plus a generator for them in
   gen.py (`gen_v2_family`, an 'ext' family; vector state XMM0–7/YMM-high/MXCSR is compared).
   Never generate a form still listed in `NOT_YET_IMPLEMENTED`: QEMU (EPYC-Rome, `test/qemu-cpu.sh`)
   executes it. The 'ud' family generates encodings outside both lists and expects #UD, so a new
   row also stops the #UD tests for its form. QEMU deviations: as in `TestMain.qemuAsHardware`
   (rewrite only the TCG signature, cite the manual) or not generated, documented.
2. **System tests** (`validation/test/sys/`): SIMD rows go into `xops` in `t_simd.c`
   (`{pfx, op, flags, map, vex, l, w}`, flags `ALLX`/`YMMD`); other features get their own `t_*.c`
   or lines. Probes of optional features follow CPUID (`has_feature`, `feat()` in `t_simdx.c`).
   TCG bugs: a rule in `qemu-deviations.txt` citing the manual; what TCG cannot run goes after
   `MODEL-ONLY` with `model-only.expected`. Tests pinning old behaviour owned by Sys:
   `t_pae.c:61` (`pae.efer.rsvd`, the reserved EFER bit) and `pgfm.pse.rsvd` (`t_pgfuzz.c`,
   no PSE-36).
3. **Native hardware campaign** (`validation/test/fp_cases.py`): add a family to `FAMILIES` with
   the CPUID features it needs (names in `native_fp.FEATURES`); records carry YMM upper halves.
4. **Theorems** in `X86/Proofs/` for your feature's key properties.
5. Anything computed (crypto, FMA, F16C, PCMPxSTRx): an independent reference in Python.

## Gate (all green before handing back)

```
x86_32/verify.sh                                      # model + proofs, no sorry
cd validation && lake build x86run x86test x86sys x86litmus x86fp
validation/test/run.sh 20000 <seed>                   # ", 0 mismatches", several seeds
validation/test/sys/run.sh                            # both diffs empty
python3 validation/litmus/litmus.py check-expected validation/litmus/tests validation/litmus/diy
python3 -m unittest discover -s validation/test -p 'test_*.py'
validation/verify.sh steps 3-4                        # Linux boot + workload identical; < 10% slower
./verify.sh 2000                                      # also builds x86_64 (do not change it)
```

Boot baseline (before the foundation work, this machine): 62,400,204 instructions in ≈13.5 s;
workload 131,401,245 instructions in ≈30 s.

## Conventions

No `sorry`/`admit`/new axioms; do not weaken theorems or tests; cite SDM/APM sections in comments;
where CPUID values or behaviour cannot be confirmed from a source, say so in a comment. Commit on
your branch with plain messages, no AI attribution, never push.
