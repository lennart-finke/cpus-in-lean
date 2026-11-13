# Maintaining the IA-32 model

How the model is organised for changes: where an instruction is decoded and dispatched, which module
owns which feature, how CPUID follows the implemented features, which tests a change needs, and the
gate every change must pass. The Zen 2 work was done this way by several parallel workstreams (one
module each); the structure stays useful for fixes, because a change to one feature touches one
module, its proofs file and its tests. Read the module documentation of `X86/Decode.lean`,
`X86/Cpuid.lean`, `X86/Dispatch.lean` and of the `X86/Ext/*.lean` file concerned as well.

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

C4/C5 are VEX only if the next byte has bits 7:6 = 11 (else LES/LDS). 62 is not decoded as EVEX: on
Zen 2 its mod=11 form stays the #UD form of BOUND. 8F with ModRM.reg ≠ 0 is decoded with the XOP layout
the EPYC 7742 uses for its length (an unknown VEX map, #UD), and the other undefined encodings have the
layouts of `Decode.lean`'s "Lengths of undefined encodings" (hardware-established; keep `opInfo`,
`validation/test/native/record_check.h`, `native_ext.layout` and `gen.py`'s layouts in step). `decode_len`
(`Proofs/State.lean`) depends on `decode`'s final `if n > 15 then gp 0`; keep it.

## Hooks: who owns what

`X86/Dispatch.lean` calls each module's hooks at the places below. A hook returns `none` for forms it
does not implement; then the next hook or the fallback runs. A module implements only its forms and
returns `none` for everything else; a fix belongs in the module that owns the form.

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
| `msr?` (#GP): core (`Exec.coreMsr?`: EFER, APIC_BASE, 0x8B, 0x1D9; 0x17, 0xC1/C2, 0x186/187 only with the legacy identity), then `Gpr`, `Sys`, `Xsave`, `Svm`, `LongMode`, `Smp` | return an `MsrImpl` (`rd`, `wr`; `MsrImpl.stored n mask` keeps it in `Cpu.msrs`) | |

`Dispatch.vexExec` raises #UD for every VEX instruction in real/virtual-8086 mode, after
66/F2/F3/LOCK and for unknown maps before calling `vex?` (theorems `vexExec_*`). The SSE/AVX
checks (CR4.OSXSAVE, XCR0[2:1], CR0.TS) are `Vex.vexCheck` in `X86/Ext/Vex.lean` (with `Vex.start` for the
per-instruction encoding rules and the 256-bit operand helpers; see its documentation), owned
by Avx; BMI does not use it.

Code outside the extension modules that belongs to a feature: Sys A — `X86/Machine.lean` paging
(SMEP/SMAP, PSE-36, global pages); Sys B (VME/PVI, NMI, exception classes) — `popf`/`iret` in
`X86/Exec.lean`, `X86/Sys.lean`, `X86/Step.lean`, `Flag.valid` (VIF/VIP are named in `Word.lean`);
LongMode — paging/translation; Smp — `X86/Dev.lean`, `X86/Machine.lean`; Sse — `Simd.vecAddr`
(MisalignSse), `Float.lean`; Avx2 — `Float.lean` (fma, binary16); Xsave — `Cpuid.leafD`.
Leave existing core code alone otherwise; reuse its helpers (`V128.lane/map2`, `pint`, `sseCheck`,
`sseStatus`, `vecAddr`, `rdXE`, `FP.cmp`, `Float.*`, `deliver`, `sysRd/sysWr`, `eaOff`, `rmwE`).

State: `SseState.ymmh` (YMM bits 255:128; legacy SSE keeps it, VEX.128 zeroes it), `CpuExt.xcr0`
(reset 1), `CpuExt.xss`, and one structure per owner in `X86/State.lean` (`GprState`, `SysState`,
`SvmState`, `LongModeState`, `SmpState`, `SysBState`, `XsaveState`) — a feature's state goes into its
owner's structure. Bit names: `CR0.*`, `CR4.*`
(UMIP, FSGSBASE, OSXSAVE, SMEP, SMAP, ...), `EFER.*` (SCE, LME, LMA, SVME, LMSLE, FFXSR, TCE),
`XCR0.*`, `Flag.VIF/VIP` in `X86/Word.lean`.

## CPUID

`X86/Cpuid.lean` reports the identity of an AMD EPYC 7742 (`identity = .epyc7742`: "AuthenticAMD",
00830F10h, the dump's leaves) and, of the dump's feature bits, exactly those of `implemented`
features. Every `false` line of `implemented` says why the feature is masked. MOV CR4 and WRMSR EFER
accept a control bit only with its feature (`Cpuid.cr4Writable`, `Cpuid.eferWritable`).

Changing a feature bit (`implemented f`): `x86_32/CPUID.md` must be regenerated
(`python3 validation/test/cpuid_table.py write`, after `lake build x86run`; the unit test
`test_cpuid_table.py` fails otherwise, and also if a masked feature has no reason in `REASONS` there or
a native-campaign feature (`native_fp.FEATURES`) is not reported), and the closed forms in
`Proofs/Ext.lean` must be restated: `amdTable` (`cpuid_epyc`, `cpuid_epyc_dump`, `cpuid_epyc_descr`),
`presentCpuid` (`legacyLeaf_former`: the former identity, kept for reference) and, for a control bit,
`cr4Writable_former`/`eferWritable_former`. Restate, never delete. Software that keys on the identity:
MSR 8Bh (`patchLevelMsr`) and the Intel MSRs of `Exec.msrInfo`; Linux's vendor paths (see
`validation/README.md`, Linux guest).

## Tests

1. **Random single instructions** (`validation/test/gen.py`, run by `test/run.sh`, format v2):
   add rows to `IMPLEMENTED` in `validation/test/isa_forms.py` (one row per line) plus a
   generator for them in gen.py (`gen_v2_family`, an 'ext' family; vector state
   XMM0–7/YMM-high/MXCSR is compared). The 'ud' family generates encodings outside `IMPLEMENTED`
   and expects #UD (QEMU runs EPYC-Rome, `test/qemu-cpu.sh`), so a new row also stops the #UD
   tests for its form; gen.py prints how many distinct undefined encodings per map a run emitted.
   `test_isa_forms.py` checks every row against LLVM's disassembler (`-mcpu=znver2`). QEMU
   deviations: as in `TestMain.qemuAsHardware` (rewrite only the TCG signature, cite the manual)
   or not generated, documented.
2. **System tests** (`validation/test/sys/`): SIMD rows go into `xops` in `t_simd.c`
   (`{pfx, op, flags, map, vex, l, w}`, flags `ALLX`/`YMMD`); other features get their own `t_*.c`
   or lines. Probes of optional features follow CPUID (`has_feature`, `feat()` in `t_simdx.c`).
   TCG bugs: a rule in `qemu-deviations.txt` citing the manual; what TCG cannot run goes after
   `MODEL-ONLY` with `model-only.expected` (QEMU stops at the marker, `qemu=1`; every transcript
   must end with `END`).
3. **Native hardware campaign** (`validation/test/fp_cases.py`): user-mode-visible behaviour gets a
   family in `FAMILIES` with the CPUID features it needs (names in `native_fp.FEATURES`); records
   carry YMM upper halves; cases whose hardware outcome the manuals leave open are `policy='observe'`
   and get an entry in "Open questions for the EPYC" (`validation/README.md`). Records must be ones
   the native oracle can run as the model does (`validation/test/native/record_check.h`: data-page
   PTEs 0/0x65/0x67 only, no system calls, far transfers or DS/ES/FS/GS loads, ...); `native_fp.py
   prepare` and `test_native_fp.py` refuse anything else (`validation/test/FP-HARDWARE.md`).
4. **Theorems** in `X86/Proofs/` (one file per module, `Ext<Owner>.lean`) for the key properties.
5. Anything computed (crypto, FMA, F16C, PCMPxSTRx, topology, ...): an independent reference in
   Python, run by `validation/test/refs.py` or a unit test.

## Gate (all green before a change is merged)

```
x86_32/verify.sh                                      # model + proofs, no sorry
cd validation && lake build x86run x86test x86sys x86litmus x86fp x86bridge
validation/test/run.sh 20000 <seed>                   # ", 0 mismatches", several seeds
validation/test/sys/run.sh                            # all diffs empty, every transcript ends with END
python3 validation/litmus/litmus.py check-expected validation/litmus/tests validation/litmus/diy
python3 -m unittest discover -s validation/test -p 'test_*.py'
python3 validation/test/refs.py                       # independent references (after sys/run.sh)
validation/verify.sh steps 8-9                        # Linux boot + workload identical; < 10% slower
./verify.sh 2000                                      # both models; ./verify.sh --full for everything
```

`./verify.sh --full` runs `x86_32/verify.sh`, `validation/verify.sh --full` (adds the bridge, the whole
x86fp campaign, SMP Linux at several quanta and the Linux topology checks) and `x86_64/verify.sh`.

Boot: 62,400,204 instructions in ≈13.5 s before the Zen 2 work; 52,180,389 with all workstreams and the
former (Intel) identity; 54,168,236 with the EPYC identity (≈12.7 s on a loaded machine; Linux takes
its AMD paths, e.g. the Zenbleed and erratum-1386 checks). Workload: 117,169,217 instructions (≈29 s).

## Conventions

No `sorry`/`admit`/new axioms; do not weaken theorems or tests; cite SDM/APM sections in comments;
where CPUID values or behaviour cannot be confirmed from a source, say so in a comment and add the
question to "Open questions for the EPYC" (`validation/README.md`) with a native case or the KVM
harness that observes it. Commit with plain messages, no AI attribution, never push.
