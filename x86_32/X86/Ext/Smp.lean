import X86.Exec
/-!
# Multiprocessor platform

Owner: the SMP workstream (I/O APIC, x2APIC, IPIs, several CPUs). Device and machine changes live in
`X86/Dev.lean`, `X86/Machine.lean` and new files of this workstream.

Hook (called by `X86/Dispatch.lean`; `none` = not handled here):

* `msr?`: x2APIC registers (0x800..0x8FF).
-/
namespace X86
namespace Smp

def msr? (_n : UInt32) : Option MsrImpl := none

end Smp
end X86
