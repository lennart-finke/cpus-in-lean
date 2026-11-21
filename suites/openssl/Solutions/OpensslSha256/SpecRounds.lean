import Ssl.Spec.Sha256
/-!
# The compression function round by round

`rs H W t` is the working state `(a, …, h)` after `t` rounds of `Spec.Sha256.compress` with message
schedule `W` (`compress_eq`); `Ws block t` is word `t` of the schedule, which for `t ≥ 16` follows
the recurrence (`Ws_rec`) and below 16 is the big-endian word of the block (`Ws_lt`).
-/
namespace Solutions.OpensslSha256
open Ssl Ssl.Spec.Sha256

abbrev S8 := UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32

/-- One round, as `compress` writes it. -/
def rstep (W : Array UInt32) : S8 → Nat → S8 :=
  fun (a, b, c, d, e, f, g, h) t =>
    let T1 := h + Sigma1 e + Ch e f g + K[t]! + W[t]!
    let T2 := Sigma0 a + Maj a b c
    (T1 + T2, a, b, c, d + T1, e, f, g)

def init8 (H : Array UInt32) : S8 := (H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!)

/-- The state after `t` rounds. -/
def rs (H W : Array UInt32) (t : Nat) : S8 := (List.range t).foldl (rstep W) (init8 H)

def fin8 (H : Array UInt32) (s : S8) : Array UInt32 :=
  #[H[0]! + s.1, H[1]! + s.2.1, H[2]! + s.2.2.1, H[3]! + s.2.2.2.1, H[4]! + s.2.2.2.2.1,
    H[5]! + s.2.2.2.2.2.1, H[6]! + s.2.2.2.2.2.2.1, H[7]! + s.2.2.2.2.2.2.2]

theorem compress_eq (H : Array UInt32) (block : List UInt8) :
    compress H block = fin8 H (rs H (schedule block) 64) := rfl

theorem rs_zero (H W : Array UInt32) : rs H W 0 = init8 H := rfl

theorem rs_succ (H W : Array UInt32) (t : Nat) : rs H W (t + 1) = rstep W (rs H W t) t := by
  unfold rs
  rw [List.range_succ, List.foldl_append]
  rfl

/-! ## Components -/

def A (H W : Array UInt32) (t : Nat) : UInt32 := (rs H W t).1
def B (H W : Array UInt32) (t : Nat) : UInt32 := (rs H W t).2.1
def C (H W : Array UInt32) (t : Nat) : UInt32 := (rs H W t).2.2.1
def D (H W : Array UInt32) (t : Nat) : UInt32 := (rs H W t).2.2.2.1
def E (H W : Array UInt32) (t : Nat) : UInt32 := (rs H W t).2.2.2.2.1
def F (H W : Array UInt32) (t : Nat) : UInt32 := (rs H W t).2.2.2.2.2.1
def G (H W : Array UInt32) (t : Nat) : UInt32 := (rs H W t).2.2.2.2.2.2.1
def Hh (H W : Array UInt32) (t : Nat) : UInt32 := (rs H W t).2.2.2.2.2.2.2

/-- The first summand of round `t`. -/
def T1 (H W : Array UInt32) (t : Nat) : UInt32 :=
  Hh H W t + Sigma1 (E H W t) + Ch (E H W t) (F H W t) (G H W t) + K[t]! + W[t]!

theorem A_succ (H W : Array UInt32) (t : Nat) :
    A H W (t + 1) = T1 H W t + (Sigma0 (A H W t) + Maj (A H W t) (B H W t) (C H W t)) := by
  simp only [A, B, C, T1, Hh, E, F, G, rs_succ]; rfl
theorem E_succ (H W : Array UInt32) (t : Nat) : E H W (t + 1) = D H W t + T1 H W t := by
  simp only [E, D, T1, Hh, F, G, rs_succ]; rfl
theorem B_succ (H W : Array UInt32) (t : Nat) : B H W (t + 1) = A H W t := by
  simp only [A, B, rs_succ]; rfl
theorem C_succ (H W : Array UInt32) (t : Nat) : C H W (t + 1) = B H W t := by
  simp only [B, C, rs_succ]; rfl
theorem D_succ (H W : Array UInt32) (t : Nat) : D H W (t + 1) = C H W t := by
  simp only [C, D, rs_succ]; rfl
theorem F_succ (H W : Array UInt32) (t : Nat) : F H W (t + 1) = E H W t := by
  simp only [E, F, rs_succ]; rfl
theorem G_succ (H W : Array UInt32) (t : Nat) : G H W (t + 1) = F H W t := by
  simp only [F, G, rs_succ]; rfl
theorem Hh_succ (H W : Array UInt32) (t : Nat) : Hh H W (t + 1) = G H W t := by
  simp only [G, Hh, rs_succ]; rfl

theorem fin8_eq (H W : Array UInt32) :
    fin8 H (rs H W 64) = #[H[0]! + A H W 64, H[1]! + B H W 64, H[2]! + C H W 64, H[3]! + D H W 64,
      H[4]! + E H W 64, H[5]! + F H W 64, H[6]! + G H W 64, H[7]! + Hh H W 64] := rfl

theorem A_zero (H W : Array UInt32) : A H W 0 = H[0]! := rfl
theorem B_zero (H W : Array UInt32) : B H W 0 = H[1]! := rfl
theorem C_zero (H W : Array UInt32) : C H W 0 = H[2]! := rfl
theorem D_zero (H W : Array UInt32) : D H W 0 = H[3]! := rfl
theorem E_zero (H W : Array UInt32) : E H W 0 = H[4]! := rfl
theorem F_zero (H W : Array UInt32) : F H W 0 = H[5]! := rfl
theorem G_zero (H W : Array UInt32) : G H W 0 = H[6]! := rfl
theorem Hh_zero (H W : Array UInt32) : Hh H W 0 = H[7]! := rfl

/-! ## The message schedule -/

/-- The first 16 words. -/
def sched16 (block : List UInt8) (n : Nat) : Array UInt32 :=
  (List.range n).foldl (fun W i => W.push (be32At block i)) #[]

/-- The schedule after pushing `n` of the 48 computed words. -/
def schedN (block : List UInt8) (n : Nat) : Array UInt32 :=
  (List.range n).foldl (fun W t => W.push (sigma1 W[t + 14]! + W[t + 9]! + sigma0 W[t + 1]! + W[t]!))
    (sched16 block 16)

theorem schedule_eq (block : List UInt8) : schedule block = schedN block 48 := by
  unfold schedule schedN sched16; rfl

theorem sched16_succ (block : List UInt8) (n : Nat) :
    sched16 block (n + 1) = (sched16 block n).push (be32At block n) := by
  unfold sched16; rw [List.range_succ, List.foldl_append]; rfl

theorem sched16_size (block : List UInt8) (n : Nat) : (sched16 block n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sched16_succ]; simp [ih]

theorem sched16_get (block : List UInt8) (n i : Nat) (hi : i < n) :
    (sched16 block n)[i]! = be32At block i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sched16_succ]
    by_cases h : i < n
    · rw [getElem!_pos _ _ (by simp [sched16_size]; omega), Array.getElem_push_lt (by simp [sched16_size]; omega),
        ← getElem!_pos _ _ (by simp [sched16_size]; omega)]
      exact ih h
    · have : i = n := by omega
      subst this
      rw [getElem!_pos _ _ (by simp [sched16_size]), Array.getElem_push]
      simp [sched16_size]

theorem schedN_succ (block : List UInt8) (n : Nat) :
    schedN block (n + 1) = (schedN block n).push (sigma1 (schedN block n)[n + 14]! + (schedN block n)[n + 9]! +
      sigma0 (schedN block n)[n + 1]! + (schedN block n)[n]!) := by
  unfold schedN; rw [List.range_succ, List.foldl_append]; rfl

theorem schedN_zero (block : List UInt8) : schedN block 0 = sched16 block 16 := by
  unfold schedN; simp only [List.range_zero, List.foldl_nil]

theorem schedN_size (block : List UInt8) (n : Nat) : (schedN block n).size = 16 + n := by
  induction n with
  | zero => rw [schedN_zero, sched16_size]
  | succ n ih => rw [schedN_succ]; simp [ih]; omega

theorem schedN_mono (block : List UInt8) (n m i : Nat) (hi : i < 16 + n) :
    (schedN block (n + m))[i]! = (schedN block n)[i]! := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← Nat.add_assoc, schedN_succ, getElem!_pos _ _ (by simp [schedN_size]; omega),
      Array.getElem_push_lt (by simp [schedN_size]; omega), ← getElem!_pos _ _ (by simp [schedN_size]; omega), ih]

/-- Word `t` of the schedule. -/
def Ws (block : List UInt8) (t : Nat) : UInt32 := (schedule block)[t]!

theorem Ws_lt (block : List UInt8) (t : Nat) (ht : t < 16) : Ws block t = be32At block t := by
  unfold Ws
  rw [schedule_eq, show 48 = 0 + 48 from rfl, schedN_mono block 0 48 t (by omega), schedN_zero]
  exact sched16_get block 16 t ht

theorem Ws_rec (block : List UInt8) (t : Nat) (ht : t < 48) :
    Ws block (t + 16) = sigma1 (Ws block (t + 14)) + Ws block (t + 9) + sigma0 (Ws block (t + 1)) + Ws block t := by
  unfold Ws
  have key : ∀ i, i < 16 + t → (schedule block)[i]! = (schedN block t)[i]! := by
    intro i hi
    rw [schedule_eq, show 48 = t + (48 - t) by omega, schedN_mono block t (48 - t) i hi]
  rw [key (t + 14) (by omega), key (t + 9) (by omega), key (t + 1) (by omega), key t (by omega)]
  rw [schedule_eq, show 48 = (t + 1) + (47 - t) by omega, schedN_mono block (t + 1) (47 - t) (t + 16) (by omega),
    schedN_succ, getElem!_pos _ _ (by simp [schedN_size]; omega)]
  have hs : t + 16 = (schedN block t).size := by rw [schedN_size]; omega
  simp only [hs, Array.getElem_push_eq]

end Solutions.OpensslSha256
