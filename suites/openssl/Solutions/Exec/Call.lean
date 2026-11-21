import Solutions.Exec.Mem
import Solutions.Logic.Decode
import Solutions.Logic.Run
/-!
# The machine of a well-formed call

`Ssl.Calls` puts the image at its link address; `callMem` packages the caller's memory with that
fact as a `CodeMem` (for decoding by `cbv`), for any image whose bytes are given by a byte function
(as every `Image.lean` of the suite defines them). The rest are the facts of a call that the step
proofs use: the stack word at the stack pointer, and the bounds of the stack.

Memory ends below the I/O APIC page (`Ssl.Calls` bounds it by `Ssl.ramLimit = ramTop`,
`ramTop_of_calls`), so every access inside memory reaches `Machine.mem`.
-/
namespace Solutions.Exec
open X86 Ssl Solutions.Logic

/-- The memory of a call, with the image in it. -/
def callMem {base halt : UInt32} {size : Nat} {byte : Nat → UInt8} {bytes : ByteArray}
    (hb : bytes = ⟨Array.ofFn (n := size) fun i => byte i.val⟩)
    {c : Caller} {stack : Nat} {args : List UInt32} (h : Calls ⟨base, bytes, halt⟩ c stack args) :
    CodeMem base size byte :=
  have hs : bytes.size = size := by subst hb; simp [ByteArray.size]
  have h1 : c.mem.size ≤ 2 ^ 32 := Nat.le_trans h.1 (by decide)
  let g := CodeMem.ofMemBytes c.mem base bytes h.2.1 h1 h.2.2.1
  { mem := c.mem
    fits := by rw [← hs]; exact h.2.1
    ok := fun i hi => by
      have : c.mem.get! (base.toNat + i) = bytes.get! i := g.ok i (by rw [hs]; exact hi)
      rw [this]
      subst hb
      simp [ByteArray.get!, getElem!_pos, hi] }

theorem callMem_get {base halt : UInt32} {size : Nat} {byte : Nat → UInt8} {bytes : ByteArray}
    (hb : bytes = ⟨Array.ofFn (n := size) fun i => byte i.val⟩)
    {c : Caller} {stack : Nat} {args : List UInt32} (h : Calls ⟨base, bytes, halt⟩ c stack args) :
    (callMem hb h).get = c.mem := rfl

theorem ramLimit_eq_ramTop : ramLimit = ramTop := rfl

/-- The memory of a call ends below the I/O APIC page. -/
theorem ramTop_of_calls {img : Img} {c : Caller} {stack : Nat} {args : List UInt32}
    (h : Calls img c stack args) : c.mem.size ≤ ramTop := h.1

/-- The word at the stack pointer of a call is the return address. -/
theorem calls_ret {img : Img} {c : Caller} {stack : Nat} {args : List UInt32} (h : Calls img c stack args) :
    rdBytes c.mem c.sp 4 = img.halt := by
  have h4 := h.2.2.2.1
  have := congrArg (fun a => a[0]!) h4
  simp only [memWords] at this
  simpa [memWord] using this

/-- The `i`-th stack argument of a call. -/
theorem calls_arg {img : Img} {c : Caller} {stack : Nat} {args : List UInt32} (h : Calls img c stack args)
    (i : Nat) (hi : i < args.length) :
    rdBytes c.mem (c.sp + 4 * (i + 1).toUInt32) 4 = args[i] := by
  have h4 := h.2.2.2.1
  have := congrArg (fun a => a[i + 1]!) h4
  simp only [memWords] at this
  simpa [memWord, hi] using this

/-! ## Running straight-line code with `cbv`

`runOk img k m` takes `k` steps from `m`, checking before each that the machine is running; `cbv`
evaluates it in one call, one step at a time (`run_of_runOk` turns the result into a `Run`). -/

/-- `Running` as a `Bool`. -/
def runningB (img : Img) (m : Machine) : Bool := !(returned img m || m.fatal.isSome || m.cpu.halted)

/-- `k` steps from `m` through running states, or `none`. -/
def runOk (img : Img) : Nat → Machine → Option Machine
  | 0, m => some m
  | k + 1, m => if runningB img m then runOk img k (X86.step m) else none

theorem run_of_runOk {img : Img} : ∀ {k : Nat} {m m' : Machine}, runOk img k m = some m' → Run img m m'
  | 0, m, m', h => by
    simp only [runOk, Option.some.injEq] at h; subst h; exact Run.refl img m
  | k + 1, m, m', h => by
    simp only [runOk] at h
    split at h
    · rename_i hr
      refine Run.step ?_ rfl (run_of_runOk h)
      unfold Running; unfold runningB at hr; simpa using hr
    · exact absurd h (by simp)

end Solutions.Exec
