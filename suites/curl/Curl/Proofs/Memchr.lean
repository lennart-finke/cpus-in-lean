import Curl.Proofs.Xrun
/-!
# `memchr` (`0x100730`)

```
100730 push %ebx                 100750 cmpb %bl,(%edx)
100731 mov 0x10(%esp),%ecx       100752 je 10075a
100735 xor %eax,%eax             100754 inc %edx
100737 test %ecx,%ecx            100755 dec %ecx
100739 je 100758                 100756 jne 100750
10073b mov 0xc(%esp),%ebx        100758 pop %ebx; ret
10073f mov 0x8(%esp),%edx        10075a mov %edx,%eax; pop %ebx; ret
100743 … 10074f nop × 13
```

The run in pieces of a few instructions (each executed by `xrun`), the loop by induction on the
bytes left, and the contract `memchr_spec`: the call returns the first byte equal to `c` among the
`n` bytes at `s` (or 0), restores `ebx`, writes only its stack slot below the return address, and
takes at most `5 n + 40` instructions.
-/
namespace Curl.Proofs.Memchr
open X86 Ssl Solutions.Logic Solutions.Exec Curl.Proofs Curl.Proofs.Sym Curl.Hostcheck

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000

/-- `memchr` found the byte: `mov %edx,%eax; pop %ebx; ret`. -/
theorem memchr_found (G : CMem) (ebx0 t : UInt32) (ok : StOk G.mem (t.sub 4) 4)
    (e cnt p b ebp esi edi f : UInt32) (x : UInt64) (Q : Machine → Prop)
    (hsz : G.get.size ≤ ramTop) (ht : 4 ≤ t.toNat) (hts : t.toNat + 16 ≤ G.get.size)
    (hx : x.toNat + 10 < 2 ^ 64)
    (k : Reaches img (St.m ⟨(G.wr (t.sub 4) 4 ebx0 ok).get, p, cnt, p, ebx0, t.add 4, ebp, esi, edi,
      rdRaw G.get t 4, efl f, x + 3⟩) Q) :
    Reaches img (St.m ⟨(G.wr (t.sub 4) 4 ebx0 ok).get, e, cnt, p, b, t.sub 4, ebp, esi, edi, 0x10075a,
      efl f, x⟩) Q := by
  xrun []
  exact k

/-- `memchr` did not find the byte: `pop %ebx; ret`. -/
theorem memchr_none (G : CMem) (ebx0 t : UInt32) (ok : StOk G.mem (t.sub 4) 4)
    (e cnt p b ebp esi edi f : UInt32) (x : UInt64) (Q : Machine → Prop)
    (hsz : G.get.size ≤ ramTop) (ht : 4 ≤ t.toNat) (hts : t.toNat + 16 ≤ G.get.size)
    (hx : x.toNat + 10 < 2 ^ 64)
    (k : Reaches img (St.m ⟨(G.wr (t.sub 4) 4 ebx0 ok).get, e, cnt, p, ebx0, t.add 4, ebp, esi, edi,
      rdRaw G.get t 4, efl f, x + 2⟩) Q) :
    Reaches img (St.m ⟨(G.wr (t.sub 4) 4 ebx0 ok).get, e, cnt, p, b, t.sub 4, ebp, esi, edi, 0x100758,
      efl f, x⟩) Q := by
  xrun []
  exact k

/-- Seven `nop`s. -/
theorem memchr_nops1 (G : CMem) (eax ecx edx ebx esp ebp esi edi f : UInt32) (x : UInt64) (Q : Machine → Prop)
    (hsz : G.get.size ≤ ramTop) (hx : x.toNat + 10 < 2 ^ 64)
    (k : Reaches img (St.m ⟨G.get, eax, ecx, edx, ebx, esp, ebp, esi, edi, 0x10074a, efl f, x + 7⟩) Q) :
    Reaches img (St.m ⟨G.get, eax, ecx, edx, ebx, esp, ebp, esi, edi, 0x100743, efl f, x⟩) Q := by
  xrun [0x10074a]
  exact k

/-- Six `nop`s. -/
theorem memchr_nops2 (G : CMem) (eax ecx edx ebx esp ebp esi edi f : UInt32) (x : UInt64) (Q : Machine → Prop)
    (hsz : G.get.size ≤ ramTop) (hx : x.toNat + 10 < 2 ^ 64)
    (k : Reaches img (St.m ⟨G.get, eax, ecx, edx, ebx, esp, ebp, esi, edi, 0x100750, efl f, x + 6⟩) Q) :
    Reaches img (St.m ⟨G.get, eax, ecx, edx, ebx, esp, ebp, esi, edi, 0x10074a, efl f, x⟩) Q := by
  xrun [0x100750]
  exact k

/-- One iteration of the loop of `memchr` at `0x100750`. -/
theorem memchr_iter (M : CMem) (e cnt p b sp4 ebp esi edi f : UInt32) (x : UInt64) (Q : Machine → Prop)
    (hsz : M.get.size ≤ ramTop) (hp : p.toNat + cnt.toNat ≤ M.get.size) (hc : 1 ≤ cnt.toNat)
    (hx : x.toNat + 10 < 2 ^ 64) (hby : (rdRaw M.get p 1).toNat < 256)
    (k1 : (rdRaw M.get p 1).toNat = b.toNat % 256 → ∀ (f' : UInt32) (x' : UInt64), x'.toNat ≤ x.toNat + 2 →
      Reaches img (St.m ⟨M.get, e, cnt, p, b, sp4, ebp, esi, edi, 0x10075a, efl f', x'⟩) Q)
    (k2 : (rdRaw M.get p 1).toNat ≠ b.toNat % 256 → cnt.toNat = 1 → ∀ (c' p' f' : UInt32) (x' : UInt64),
      x'.toNat ≤ x.toNat + 5 →
      Reaches img (St.m ⟨M.get, e, c', p', b, sp4, ebp, esi, edi, 0x100758, efl f', x'⟩) Q)
    (k3 : (rdRaw M.get p 1).toNat ≠ b.toNat % 256 → cnt.toNat ≠ 1 → ∀ (f' : UInt32) (x' : UInt64),
      x'.toNat ≤ x.toNat + 5 →
      Reaches img (St.m ⟨M.get, e, cnt.sub 1, p.add 1, b, sp4, ebp, esi, edi, 0x100750, efl f', x'⟩) Q) :
    Reaches img (St.m ⟨M.get, e, cnt, p, b, sp4, ebp, esi, edi, 0x100750, efl f, x⟩) Q := by
  xrun [] 1
  xrun [0x100750, 0x100758, 0x10075a]
  all_goals first
    | exact k1 (by xomega) _ _ (by xomega)
    | exact k2 (by xomega) (by xomega) _ _ _ _ (by xomega)
    | exact k3 (by xomega) (by xomega) _ _ (by xomega)

/-- The entry of `memchr` up to the `nop`s, or to the return for `n = 0`. -/
theorem memchr_pro (G : CMem) (eax ecx edx ebx t ebp esi edi f : UInt32) (x : UInt64) (Q : Machine → Prop)
    (ok : StOk G.mem (t.sub 4) 4)
    (hsz : G.get.size ≤ ramTop) (ht : 4 ≤ t.toNat) (hts : t.toNat + 16 ≤ G.get.size)
    (hx : x.toNat + 10 < 2 ^ 64)
    (kz : (rdRaw G.get (t.add 12) 4).toNat = 0 → ∀ (e c' f' : UInt32) (x' : UInt64), e.toNat = 0 →
      x'.toNat ≤ x.toNat + 5 →
      Reaches img (St.m ⟨(G.wr (t.sub 4) 4 ebx ok).get, e, c', edx, ebx, t.sub 4, ebp, esi, edi, 0x100758,
        efl f', x'⟩) Q)
    (kn : (rdRaw G.get (t.add 12) 4).toNat ≠ 0 → ∀ (e f' : UInt32) (x' : UInt64), e.toNat = 0 →
      x'.toNat ≤ x.toNat + 7 →
      Reaches img (St.m ⟨(G.wr (t.sub 4) 4 ebx ok).get, e, rdRaw G.get (t.add 12) 4, rdRaw G.get (t.add 4) 4,
        rdRaw G.get (t.add 8) 4, t.sub 4, ebp, esi, edi, 0x100743, efl f', x'⟩) Q) :
    Reaches img (St.m ⟨G.get, eax, ecx, edx, ebx, t, ebp, esi, edi, 0x100730, efl f, x⟩) Q := by
  xrun [0x100743, 0x100758]
  · exact kz (by xomega) _ _ _ _ (by xomega) (by xomega)
  · exact kn (by xomega) _ _ _ (by xomega) (by xomega)

/-! ## The loop and the contract -/

/-- The byte at `a`, as a number. -/
def byt (G : CMem) (a : UInt32) : Nat := (rdRaw G.get a 1).toNat

/-- `r` is what `memchr(s, c, n)` returns on memory `G`. -/
def Res (G : CMem) (s c n r : UInt32) : Prop :=
  (r = 0 ∧ ∀ i, i < n.toNat → ∀ a : UInt32, a.toNat = s.toNat + i → byt G a ≠ c.toNat % 256) ∨
  (∃ i, i < n.toNat ∧ r.toNat = s.toNat + i ∧ byt G r = c.toNat % 256 ∧
    ∀ j, j < i → ∀ a : UInt32, a.toNat = s.toNat + j → byt G a ≠ c.toNat % 256)

/-- What the caller does with the return: continue from the returned state. -/
def Cont (G : CMem) (ebx t ebp esi edi s c n : UInt32) (x0 : UInt64) (Q : Machine → Prop) : Prop :=
  ∀ (G' : CMem) (r ecx' edx' f' : UInt32) (x' : UInt64), Frame G G' (t.toNat - 4) t.toNat →
    Res G s c n r → x'.toNat ≤ x0.toNat + 5 * n.toNat + 40 →
    Reaches img (St.m ⟨G'.get, r, ecx', edx', ebx, t.add 4, ebp, esi, edi, rdRaw G.get t 4, efl f', x'⟩) Q

theorem byt_wr (G : CMem) (t ebx0 : UInt32) (ok : StOk G.mem (t.sub 4) 4) (p : UInt32)
    (hp : p.toNat + 1 ≤ G.get.size) (ht : 4 ≤ t.toNat) (hd : p.toNat + 1 ≤ t.toNat - 4 ∨ t.toNat ≤ p.toNat) :
    rdRaw (G.wr (t.sub 4) 4 ebx0 ok).get p 1 = rdRaw G.get p 1 :=
  rdRaw_wr_other G (t.sub 4) 4 ebx0 ok (Or.inl rfl) hp (by
    have : (t.sub 4).toNat = t.toNat - 4 := by xomega
    rw [this]; simp; omega)

theorem frame_push (G : CMem) (t ebx0 : UInt32) (ok : StOk G.mem (t.sub 4) 4) (ht : 4 ≤ t.toNat) :
    Frame G (G.wr (t.sub 4) 4 ebx0 ok) (t.toNat - 4) t.toNat := by
  have : (t.sub 4).toNat = t.toNat - 4 := by xomega
  exact Frame.wr G _ 4 ebx0 ok (by omega) (by simp; omega)

theorem memchr_loop (G : CMem) (ebx0 t : UInt32) (ok : StOk G.mem (t.sub 4) 4) (ebp esi edi s c n : UInt32)
    (x0 : UInt64) (Q : Machine → Prop)
    (hsz : G.get.size ≤ ramTop) (ht : 4 ≤ t.toNat) (hts : t.toNat + 16 ≤ G.get.size)
    (hbuf : s.toNat + n.toNat ≤ G.get.size) (hap : s.toNat + n.toNat ≤ t.toNat - 4 ∨ t.toNat ≤ s.toNat)
    (hx0 : x0.toNat + 5 * n.toNat + 100 < 2 ^ 64) (K : Cont G ebx0 t ebp esi edi s c n x0 Q) :
    ∀ (m i : Nat) (cnt p e f : UInt32) (x : UInt64), n.toNat - i = m → i < n.toNat → cnt.toNat = n.toNat - i →
      p.toNat = s.toNat + i → e.toNat = 0 → x.toNat ≤ x0.toNat + 20 + 5 * i →
      (∀ j, j < i → ∀ a : UInt32, a.toNat = s.toNat + j → byt G a ≠ c.toNat % 256) →
      Reaches img (St.m ⟨(G.wr (t.sub 4) 4 ebx0 ok).get, e, cnt, p, c, t.sub 4, ebp, esi, edi, 0x100750,
        efl f, x⟩) Q := by
  have hsz' : (G.wr (t.sub 4) 4 ebx0 ok).get.size = G.get.size := CMem.wr_size _ _ _ _ _
  intro m
  induction m with
  | zero => intro i cnt p e f x hm hi; omega
  | succ m ih =>
    intro i cnt p e f x hm hi hcnt hpi he hx hprev
    have hbyte : rdRaw (G.wr (t.sub 4) 4 ebx0 ok).get p 1 = rdRaw G.get p 1 :=
      byt_wr G t ebx0 ok p (by omega) ht (by omega)
    apply memchr_iter _ e cnt p c (t.sub 4) ebp esi edi f x Q (by rw [hsz']; exact hsz) (by rw [hsz']; omega)
      (by omega) (by omega) (rdRaw1_lt _ _)
    · intro hf f' x' hx'
      apply memchr_found G ebx0 t ok e cnt p c ebp esi edi f' x' Q hsz ht hts (by omega)
      refine K _ p cnt p f' (x' + 3) (frame_push G t ebx0 ok ht) (Or.inr ⟨i, hi, hpi, ?_, hprev⟩) ?_
      · unfold byt; rw [← hbyte]; exact hf
      · xomega
    · intro hf hc1 c' p' f' x' hx'
      apply memchr_none G ebx0 t ok e c' p' c ebp esi edi f' x' Q hsz ht hts (by omega)
      refine K _ e c' p' f' (x' + 2) (frame_push G t ebx0 ok ht) (Or.inl ⟨?_, ?_⟩) ?_
      · exact UInt32.toNat_inj.mp (by simpa using he)
      · intro j hj a ha
        by_cases hji : j < i
        · exact hprev j hji a ha
        · have hj' : j = i := by omega
          subst hj'
          have hap' : a = p := UInt32.toNat_inj.mp (by omega)
          subst hap'
          unfold byt; rw [← hbyte]; exact hf
      · xomega
    · intro hf hc1 f' x' hx'
      refine ih (i + 1) _ _ e f' x' (by omega) (by omega) ?_ ?_ he (by omega) ?_
      · xomega
      · xomega
      · intro j hj a ha
        by_cases hji : j < i
        · exact hprev j hji a ha
        · have hj' : j = i := by omega
          subst hj'
          have hap' : a = p := UInt32.toNat_inj.mp (by omega)
          subst hap'
          unfold byt; rw [← hbyte]; exact hf

/-- **The contract of `memchr`.** -/
theorem memchr_spec (G : CMem) (eax ecx edx ebx t ebp esi edi f s c n : UInt32) (x0 : UInt64)
    (Q : Machine → Prop)
    (hsz : G.get.size ≤ ramTop) (ht : 4 ≤ t.toNat) (hts : t.toNat + 16 ≤ G.get.size)
    (hcode : t.toNat ≤ 0x100000 ∨ 0x100000 + 3971 + 4 ≤ t.toNat)
    (hs : rdRaw G.get (t.add 4) 4 = s) (hc : rdRaw G.get (t.add 8) 4 = c) (hn : rdRaw G.get (t.add 12) 4 = n)
    (hbuf : s.toNat + n.toNat ≤ G.get.size) (hap : s.toNat + n.toNat ≤ t.toNat - 4 ∨ t.toNat ≤ s.toNat)
    (hx0 : x0.toNat + 5 * n.toNat + 100 < 2 ^ 64) (K : Cont G ebx t ebp esi edi s c n x0 Q) :
    Reaches img (St.m ⟨G.get, eax, ecx, edx, ebx, t, ebp, esi, edi, 0x100730, efl f, x0⟩) Q := by
  have ok : StOk G.mem (t.sub 4) 4 := by
    refine ⟨Or.inr (Or.inr rfl), ?_, ?_⟩
    · show (t.sub 4).toNat + (4 : UInt32).toNat ≤ G.get.size
      xomega
    · xomega
  apply memchr_pro G eax ecx edx ebx t ebp esi edi f x0 Q ok hsz ht hts (by omega)
  · intro hz e c' f' x' he hx'
    apply memchr_none G ebx t ok e c' edx ebx ebp esi edi f' x' Q hsz ht hts (by omega)
    refine K _ e c' edx f' (x' + 2) (frame_push G t ebx ok ht) (Or.inl ⟨?_, ?_⟩) (by xomega)
    · exact UInt32.toNat_inj.mp (by simpa using he)
    · rw [hn] at hz; intro i hi; omega
  · intro hnz e f' x' he hx'
    refine memchr_nops1 _ _ _ _ _ _ _ _ _ _ _ Q (by rw [CMem.wr_size]; exact hsz) (by omega) ?_
    refine memchr_nops2 _ _ _ _ _ _ _ _ _ _ _ Q (by rw [CMem.wr_size]; exact hsz) (by xomega) ?_
    rw [hs, hc, hn]
    rw [hn] at hnz
    exact memchr_loop G ebx t ok ebp esi edi s c n x0 Q hsz ht hts hbuf hap hx0 K (n.toNat - 0) 0 n s e f'
      (x' + 7 + 6) rfl (by omega) (by omega) (by omega) he (by xomega) (fun j hj => absurd hj (Nat.not_lt_zero _))

end Curl.Proofs.Memchr
