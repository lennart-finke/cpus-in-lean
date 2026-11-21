import Solutions.OpensslSha256.X.Init
import Solutions.OpensslSha256.X.FinContract
/-!
# The streaming tasks: `SHA256_Init`/`Update`/`Final` and the SHA-224 functions

The context after `Init` and after every `Update` is `Good` for the bytes hashed so far (the Init,
Update and Final contracts in `X/`); `Final` from a `Good` context writes the digest. An induction
over the chunks gives `Stream`.
-/
namespace Solutions.OpensslSha256
open X86 Ssl Solutions.Logic Ssl.OpensslSha256

theorem returns_mono {m0 : Machine} {W : UInt32 → Prop} {Q Q' : Machine → Prop}
    (h : Returns img m0 stackBound W Q) (hq : ∀ m, Q m → Q' m) : Returns img m0 stackBound W Q' :=
  Reaches.mono h fun m ⟨a, b, c, d⟩ => ⟨a, b, c, hq m d⟩

/-- The `Final` part of `Stream` for the digest `d`. -/
def FinOk (fin : UInt32) (n : Nat) (d : List UInt8) (st : List UInt8) : Prop :=
  ∀ (c : Caller) (out ctx : UInt32), FinalPre n c out ctx st →
    Returns img (c.enter fin) stackBound (fun a => InRange ctx ctxSize a ∨ InRange out n a) fun m3 =>
      m3.cpu.eax = 1 ∧ bytesAt m3 out n = d ∧ bytesAt m3 (ctx + dataOff) 68 = List.replicate 68 0

theorem updates_good (H0 : Array UInt32) (mdN n : Nat) (upd fin : UInt32) (digestOf : List UInt8 → List UInt8)
    (hupd : ∀ (msg st chunk : List UInt8), Good H0 mdN msg st → (msg ++ chunk).length < Spec.Sha256.lenBound →
      ∀ (c : Caller) (ctx msgp : UInt32), UpdatePre c ctx msgp st chunk →
        Returns img (c.enter upd) stackBound (InRange ctx ctxSize) fun m =>
          m.cpu.eax = 1 ∧ Good H0 mdN (msg ++ chunk) (bytesAt m ctx ctxSize))
    (hfin : ∀ (msg st : List UInt8), Good H0 mdN msg st → FinOk fin n (digestOf msg) st) :
    ∀ (rest : List (List UInt8)) (msg st : List UInt8), Good H0 mdN msg st →
      (msg ++ rest.flatten).length < Spec.Sha256.lenBound →
      UpdatesThen upd rest st (FinOk fin n (digestOf (msg ++ rest.flatten))) := by
  intro rest
  induction rest with
  | nil =>
    intro msg st hG _
    show FinOk fin n (digestOf (msg ++ [])) st
    rw [List.append_nil]; exact hfin msg st hG
  | cons chunk rest ih =>
    intro msg st hG hl
    intro c ctx msgp hpre
    have e : msg ++ (chunk :: rest).flatten = (msg ++ chunk) ++ rest.flatten := by
      simp [List.flatten_cons, List.append_assoc]
    rw [e] at hl ⊢
    refine returns_mono (hupd msg st chunk hG (by simp at hl ⊢; omega) c ctx msgp hpre) fun m ⟨h1, hg⟩ => ⟨h1, ?_⟩
    exact ih (msg ++ chunk) _ hg hl

theorem stream_of (H0 : Array UInt32) (mdN n : Nat) (ini upd fin : UInt32) (digestOf : List UInt8 → List UInt8)
    (hini : ∀ (c : Caller) (ctx : UInt32), InitPre c ctx →
      Returns img (c.enter ini) stackBound (InRange ctx ctxSize) fun m =>
        m.cpu.eax = 1 ∧ Good H0 mdN [] (bytesAt m ctx ctxSize))
    (hupd : ∀ (msg st chunk : List UInt8), Good H0 mdN msg st → (msg ++ chunk).length < Spec.Sha256.lenBound →
      ∀ (c : Caller) (ctx msgp : UInt32), UpdatePre c ctx msgp st chunk →
        Returns img (c.enter upd) stackBound (InRange ctx ctxSize) fun m =>
          m.cpu.eax = 1 ∧ Good H0 mdN (msg ++ chunk) (bytesAt m ctx ctxSize))
    (hfin : ∀ (msg st : List UInt8), Good H0 mdN msg st → FinOk fin n (digestOf msg) st)
    (chunks : List (List UInt8)) (hlen : chunks.flatten.length < Spec.Sha256.lenBound) :
    Stream ini upd fin n (digestOf chunks.flatten) chunks := by
  intro c ctx hpre
  refine returns_mono (hini c ctx hpre) fun m ⟨h1, hg⟩ => ⟨h1, ?_⟩
  have := updates_good H0 mdN n upd fin digestOf hupd hfin chunks [] _ hg (by rw [List.nil_append]; exact hlen)
  rw [List.nil_append] at this
  exact this

theorem sha256_streaming_ok : Ssl.OpensslSha256.sha256_streaming_correct := fun chunks hlen =>
  stream_of Spec.Sha256.H0_256 32 32 _ _ _ Spec.Sha256.sha256 Solutions.ShaX.init256_ok
    (fun msg st chunk hG hl c ctx msgp hp => Solutions.ShaX.upd256_ok _ 32 msg st chunk hG hl c ctx msgp hp)
    (fun msg st hG c out ctx hp => Solutions.ShaX.fin256_ok _ msg st hG c out ctx hp) chunks hlen

theorem sha224_streaming_ok : Ssl.OpensslSha256.sha224_streaming_correct := fun chunks hlen =>
  stream_of Spec.Sha256.H0_224 28 28 _ _ _ Spec.Sha256.sha224 Solutions.ShaX.init224_ok
    (fun msg st chunk hG hl c ctx msgp hp => Solutions.ShaX.upd224_ok _ 28 msg st chunk hG hl c ctx msgp hp)
    (fun msg st hG c out ctx hp => Solutions.ShaX.fin224_ok _ msg st hG c out ctx hp) chunks hlen

end Solutions.OpensslSha256
