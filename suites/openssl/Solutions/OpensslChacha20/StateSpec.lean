import Solutions.OpensslChacha20.Spec
import Solutions.OpensslChacha20.Rounds
import Ssl.OpensslChacha20.Statement
/-!
# The state matrix as sixteen words

`w0 key ctr`: the state matrix `state key ctr` as a `V16`; `wJ key ctr j`: after `j` blocks (the block
counter incremented `j` times), which is `advance (state key ctr) j` (`wJ_toArr`).
-/
namespace Solutions.OpensslChacha20
open Ssl Ssl.Spec.Chacha Ssl.OpensslChacha20

/-- The state matrix with the block counter incremented. -/
def V16.next (w : V16) : V16 := { w with x12 := w.x12 + 1 }

def w0 (key ctr : Array UInt32) : V16 := V16.ofArr (state key ctr)

def wJ (key ctr : Array UInt32) (j : Nat) : V16 := Nat.repeat V16.next j (w0 key ctr)

theorem state_size {key ctr : Array UInt32} (hk : key.size = 8) (hc : ctr.size = 4) :
    (state key ctr).size = 16 := by
  simp [state, sigma, hk, hc]

theorem state_get {key ctr : Array UInt32} (hk : key.size = 8) (hc : ctr.size = 4) (i : Nat) (hi : i < 16) :
    (state key ctr)[i]! = if i < 4 then sigma[i]! else if i < 12 then key[i - 4]! else ctr[i - 12]! := by
  have hs := state_size hk hc
  rw [getElem!_pos _ _ (by rw [hs]; exact hi)]
  simp only [state]
  by_cases h4 : i < 4
  · rw [if_pos h4, Array.getElem_append_left (by simp [sigma, hk]; omega), Array.getElem_append_left (by simp [sigma]; omega),
      getElem!_pos _ _ (by simp [sigma]; omega)]
  · rw [if_neg h4]
    by_cases h12 : i < 12
    · rw [if_pos h12, Array.getElem_append_left (by simp [sigma, hk]; omega), Array.getElem_append_right (by simp [sigma]; omega),
        getElem!_pos _ _ (by rw [hk]; omega)]
      simp [sigma]
    · rw [if_neg h12, Array.getElem_append_right (by simp [sigma, hk]; omega), getElem!_pos _ _ (by rw [hc]; omega)]
      simp [sigma, hk]

theorem w0_toArr {key ctr : Array UInt32} (hk : key.size = 8) (hc : ctr.size = 4) :
    (w0 key ctr).toArr = state key ctr :=
  V16.toArr_ofArr _ (state_size hk hc)

theorem next_toArr (w : V16) : (V16.next w).toArr = advance w.toArr 1 := by
  rcases w with ⟨⟩
  rfl

theorem advance_size' (s : Array UInt32) (n : Nat) : (advance s n).size = s.size := advance_size s n

theorem wJ_toArr {key ctr : Array UInt32} (hk : key.size = 8) (hc : ctr.size = 4) :
    ∀ j, (wJ key ctr j).toArr = advance (state key ctr) j
  | 0 => by
    rw [advance_zero _ (by rw [state_size hk hc]; decide)]
    exact w0_toArr hk hc
  | j + 1 => by
    show (V16.next (wJ key ctr j)).toArr = _
    rw [next_toArr, wJ_toArr hk hc j, advance_advance _ _ _ (by rw [state_size hk hc]; decide)]

end Solutions.OpensslChacha20
