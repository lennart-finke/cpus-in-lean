import X86.Tso
import Std.Tactic.BVDecide
import X86.Proofs.Basic
/-!
# Facts about the TSO hook and the multiprocessor (`X86.Tso`)

* With `Machine.tso = none` (every single-CPU machine) `physRd`/`physWr` are plain RAM accesses outside the APIC page,
  so the access log changes nothing about the single-CPU semantics.
* Committing a CPU's oldest buffered store does not change that CPU's own view of memory.

That a step with the log on records every store it makes (so that the buffered stores are exactly
the step's memory effect) is checked by running, not proved: `x86test --tso-log` (validation/).
-/
namespace X86

theorem physRd_none (p n : UInt32) (m : Machine) (h : m.tso = none) (hap : isApic m p = false) :
    physRd p.toUInt64 n m = .ok (rdBytes m.mem p n) m := by
  have hi : (p.toUInt64 >>> 32 != 0) = false := by
    have : p.toUInt64 >>> 32 = 0 := by simp only [X86.shr64]; bv_decide
    simp [this]
  have lo : p.toUInt64.toUInt32 = p := by bv_decide
  simp only [physRd, hi, lo, hap, Bool.false_eq_true, ite_false, h]

theorem physWr_none (p n v : UInt32) (m : Machine) (h : m.tso = none) (hap : isApic m p = false) :
    physWr p.toUInt64 n v m = .ok () { m with mem := wrBytes m.mem p n v } := by
  have hi : (p.toUInt64 >>> 32 != 0) = false := by
    have : p.toUInt64 >>> 32 = 0 := by simp only [X86.shr64]; bv_decide
    simp [this]
  have lo : p.toUInt64.toUInt32 = p := by bv_decide
  simp only [physWr, hi, lo, hap, Bool.false_eq_true, ite_false, h]

namespace Tso

theorem overlay_push (mem : ByteArray) (buf : Array Store) (s : Store) :
    overlay mem (buf.push s) = commit (overlay mem buf) s := by
  simp [overlay]

/-- Committing the oldest store of a buffer does not change the memory seen through it. -/
theorem overlay_commit_head (mem : ByteArray) (buf : Array Store) (h : 0 < buf.size) :
    overlay (commit mem buf[0]) (buf.extract 1 buf.size) = overlay mem buf := by
  obtain ⟨l⟩ := buf
  cases l with
  | nil => simp at h
  | cons s l => simp [overlay, List.foldl]

end Tso

/-- `TMachine.flush` of CPU `k` leaves CPU `k`'s view of memory unchanged. -/
theorem flush_view_self (t t' : TMachine) (k : Nat) (h : t.flush k = some t') :
    ∃ c c', t.cores[k]? = some c ∧ t'.cores[k]? = some c' ∧ c'.m = c.m ∧
      t'.view c' = t.view c := by
  simp only [TMachine.flush, bind, Option.bind] at h
  cases hc : t.cores[k]? with
  | none => simp [hc] at h
  | some c =>
    simp only [hc] at h
    cases hs : c.sb[0]? with
    | none => simp [hs] at h
    | some s =>
      simp only [hs, Option.some.injEq, pure] at h
      subst h
      have hk : k < t.cores.size := by
        rcases Array.getElem?_eq_some_iff.mp hc with ⟨hk, _⟩; exact hk
      have h0 : 0 < c.sb.size := by
        rcases Array.getElem?_eq_some_iff.mp hs with ⟨h0, _⟩; exact h0
      have hs' : c.sb[0] = s := by
        rcases Array.getElem?_eq_some_iff.mp hs with ⟨_, e⟩; exact e
      refine ⟨c, { c with sb := c.sb.extract 1 c.sb.size }, rfl, ?_, rfl, ?_⟩
      · simp [Array.set!, hk]
      · simp only [TMachine.view]
        rw [← hs', Tso.overlay_commit_head _ _ h0]

end X86
