import Solutions.OpensslPoly1305.InitOk
import Ssl.OpensslPoly1305.Statement
/-!
# `Poly1305_correct` from the contracts of `Poly1305_Update` and `Poly1305_Final`

`init_ok` (proved) leaves `GoodB key []`; `UpdSpec` (each `Update` call extends the message of a
`GoodB` context by its chunk) and `FinSpec` (`Final` from a `GoodB key msg` context writes the tag of
`msg` and wipes the context) give the streaming statement by induction on the chunks (`correct_of`).
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305 Ssl.Spec.Poly1305

set_option autoImplicit false

theorem Returns.mono' {m : Machine} {stack : Nat} {W : UInt32 → Prop} {P Q : Machine → Prop}
    (h : Returns img m stack W P) (hPQ : ∀ m', P m' → Q m') : Returns img m stack W Q :=
  Reaches.mono h (fun _ ⟨a, b, c, d⟩ => ⟨a, b, c, hPQ _ d⟩)

/-- `Poly1305_Update` extends the message of a good context by its chunk. -/
def UpdSpec : Prop :=
  ∀ (key msg st chunk : List UInt8) (c : Caller) (ctx msgp : UInt32), key.length = 32 → GoodB key msg st →
    UpdatePre c ctx msgp st chunk →
    Returns img (c.enter Image.sym_Poly1305_Update) stackBound (InRange ctx ctxSize)
      (fun m => GoodB key (msg ++ chunk) (bytesAt m ctx ctxSize))

/-- `Poly1305_Final` from a good context writes the tag of its message and wipes the context. -/
def FinSpec : Prop :=
  ∀ (key msg st : List UInt8) (c : Caller) (ctx mac : UInt32), key.length = 32 → GoodB key msg st →
    FinalPre c ctx mac st →
    Returns img (c.enter Image.sym_Poly1305_Final) stackBound (fun a => InRange ctx ctxSize a ∨ InRange mac 16 a)
      (fun m3 => bytesAt m3 mac 16 = poly1305 key msg ∧ bytesAt m3 ctx ctxSize = List.replicate ctxSize 0)

theorem updates_of (hu : UpdSpec) (hf : FinSpec) (key : List UInt8) (hk : key.length = 32) :
    ∀ (chunks : List (List UInt8)) (msg st : List UInt8), GoodB key msg st →
      UpdatesThen chunks st (fun st' => ∀ (c : Caller) (ctx mac : UInt32), FinalPre c ctx mac st' →
        Returns img (c.enter Image.sym_Poly1305_Final) stackBound
          (fun a => InRange ctx ctxSize a ∨ InRange mac 16 a) fun m3 =>
            bytesAt m3 mac 16 = poly1305 key (msg ++ chunks.flatten) ∧
            bytesAt m3 ctx ctxSize = List.replicate ctxSize 0)
  | [], msg, st, hg => by
    intro c ctx mac hp
    simpa using hf key msg st c ctx mac hk hg hp
  | chunk :: rest, msg, st, hg => by
    intro c ctx msgp hp
    refine Returns.mono' (hu key msg st chunk c ctx msgp hk hg hp) (fun m h => ?_)
    have e : msg ++ (chunk :: rest).flatten = msg ++ chunk ++ rest.flatten := by
      simp [List.flatten_cons, List.append_assoc]
    rw [e]
    exact updates_of hu hf key hk rest (msg ++ chunk) _ h

theorem correct_of (hu : UpdSpec) (hf : FinSpec) : Poly1305_correct := by
  intro key chunks hk c ctx keyp hp
  refine Returns.mono' (init_ok c ctx keyp key hk hp) (fun m h => ?_)
  have := updates_of hu hf key hk chunks [] _ h
  rwa [List.nil_append] at this

theorem oneshot_of (hu : UpdSpec) (hf : FinSpec) : Poly1305_oneshot :=
  Poly1305_oneshot_of_correct (correct_of hu hf)

end Solutions.OpensslPoly1305
