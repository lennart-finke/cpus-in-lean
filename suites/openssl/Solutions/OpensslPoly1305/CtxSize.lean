import Solutions.Exec.Step
import Solutions.Exec.Dispatch
import Solutions.Exec.Call
import Ssl.OpensslPoly1305.Statement
/-!
# `Poly1305_ctx_size` returns 236

The function is `movl $0xec, %eax; retl` at `0x100000`: two steps, after which the call has returned
to the sentinel with `eax = 0xEC` and nothing written.
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305

abbrev PMem := CodeMem Image.base Image.size Image.byte

set_option maxRecDepth 100000 in
theorem step_mov (g : PMem) (eax ecx edx ebx esp ebp esi edi f : UInt32) :
    X86.step (St.m ⟨g.get, eax, ecx, edx, ebx, esp, ebp, esi, edi, 0x100000, efl f, 0⟩) =
      St.m ⟨g.get, 0xEC, ecx, edx, ebx, esp, ebp, esi, edi, 0x100005, efl f, 1⟩ := by
  cbv

set_option maxRecDepth 100000 in
theorem step_ret (g : PMem) (eax ecx edx ebx esp ebp esi edi f : UInt32)
    (hsz : g.get.size ≤ ramTop) (h1 : esp.toNat + 4 ≤ g.get.size) :
    X86.step (St.m ⟨g.get, eax, ecx, edx, ebx, esp, ebp, esi, edi, 0x100005, efl f, 1⟩) =
      St.m ⟨g.get, eax, ecx, edx, ebx, UInt32.add esp 4, ebp, esi, edi, rdRaw g.get esp 4, efl f, 2⟩ := by
  cbv

/-- The task, for a call whose memory ends below the I/O APIC page (every call does). -/
theorem ctx_size_correct_of_ramTop :
    ∀ (c : Caller), Calls img c stackBound [] → c.mem.size ≤ ramTop →
      Returns img (c.enter Image.sym_Poly1305_ctx_size) stackBound NoWrites fun m =>
        m.cpu.eax = ctxSize.toUInt32 := by
  intro c hc hram
  let g : PMem := callMem (byte := Image.byte) rfl hc
  have hg : g.get = c.mem := rfl
  have hsp : c.sp.toNat + 4 ≤ g.get.size := by
    have := hc.2.2.2.2.2.1; simp at this; rw [hg]; omega
  have hret : rdRaw g.get c.sp 4 = Image.sym_halt := calls_ret hc
  have e0 : c.enter Image.sym_Poly1305_ctx_size =
      St.m ⟨g.get, c.regs.eax, c.regs.ecx, c.regs.edx, c.regs.ebx, c.sp, c.regs.ebp, c.regs.esi,
        c.regs.edi, 0x100000, efl c.regs.flags, 0⟩ := rfl
  have e1 := step_mov g c.regs.eax c.regs.ecx c.regs.edx c.regs.ebx c.sp c.regs.ebp c.regs.esi
    c.regs.edi c.regs.flags
  have e2 := step_ret g 0xEC c.regs.ecx c.regs.edx c.regs.ebx c.sp c.regs.ebp c.regs.esi
    c.regs.edi c.regs.flags (by rw [hg]; exact hram) hsp
  rw [hret] at e2
  rw [e0]
  refine Returns.intro (Run.step rfl e1 (Run.step rfl e2 (Run.refl img _))) ?_ ?_ ?_ ?_
  · refine ⟨rfl, rfl, ?_⟩
    show efl c.regs.flags &&& 1024 = 0
    exact efl_DF _
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, fun _ _ _ _ => rfl⟩
  · rfl

theorem ctx_size_correct : Poly1305_ctx_size_correct :=
  fun c hc => ctx_size_correct_of_ramTop c hc (ramTop_of_calls hc)

end Solutions.OpensslPoly1305
