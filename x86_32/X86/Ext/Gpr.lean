import X86.Ext.Vex
/-!
# General-purpose instruction extensions of Zen 2

Owner: the GPR-extension workstream. POPCNT, LZCNT/TZCNT (ABM/BMI1), BMI1, BMI2, ADX, MOVBE,
CRC32, RDRAND/RDSEED, RDPID/RDTSCP, RDPMC, RDPRU, CLFLUSH/CLFLUSHOPT/CLWB/CLZERO, WBNOINVD,
MONITOR/MWAIT/MONITORX/MWAITX, PREFETCH/PREFETCHW memory forms.

Hooks (called by `X86/Dispatch.lean`; `none` = not handled here, see `EXTENDING.md`). CPUID reports
a feature only once its line in `Cpuid.implemented` is `true`.

* `op0F?` is called for
  - F3 0F B8 (POPCNT; fallback #UD) and F3 0F BC / F3 0F BD (TZCNT / LZCNT; fallback BSF / BSR,
    which is what a CPU without BMI1/ABM executes: return `none` unless the feature is implemented);
  - 0F 0D (PREFETCH/PREFETCHW), 0F 18 (prefetch hints), 0F 33 (RDPMC), F3 0F 09 (WBNOINVD)
    (fallback: the core behaviour: NOP, NOP, #UD, WBINVD);
  - 0F 01 register forms other than SMSW/LMSW (fallback #UD; shared with Sys, Xsave, Svm,
    LongMode): this module owns C8 MONITOR, C9 MWAIT, F9 RDTSCP, FA MONITORX, FB MWAITX,
    FC CLZERO, FD RDPRU;
  - 0F AE forms other than FXSAVE/FXRSTOR/LDMXCSR/STMXCSR and the fences (fallback #UD; shared
    with Xsave, LongMode): this module owns memory /7 without prefix (CLFLUSH), 66 memory /6
    (CLWB) and 66 memory /7 (CLFLUSHOPT);
  - 0F C7 forms other than /1 (fallback #UD; shared with Xsave): this module owns register /6
    (RDRAND), register /7 (RDSEED) and F3 register /7 (RDPID).
* `map2?` (legacy 0F 38): F0/F1 (MOVBE; F2: CRC32), F6 (66: ADCX, F3: ADOX). Fallback #UD.
* `vex?`: VEX.0F38 F2 (ANDN), F3 (BLSR/BLSMSK/BLSI), F5 (BZHI, PDEP, PEXT), F6 (MULX), F7 (BEXTR,
  SHLX, SARX, SHRX) and VEX.0F3A F0 (RORX). Fallback: `Avx.vex?`, then #UD.
* `msr?`: e.g. TSC_AUX (0xC0000103) for RDTSCP/RDPID.
-/
namespace X86
namespace Gpr

def op0F? (_i : Inst) : Option (M Unit) := none
def map2? (_i : Inst) : Option (M Unit) := none
def vex? (_i : Inst) : Option (M Unit) := none
def msr? (_n : UInt32) : Option MsrImpl := none

end Gpr
end X86
