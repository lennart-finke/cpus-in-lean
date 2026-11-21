import Solutions.OpensslChacha20.Block
/-!
# `ChaCha20_ctr32_correct`

The run of a call: the entry (`entry_run`), then for an empty input the epilogue, otherwise the
blocks (`block_run`), each producing 64 bytes of `Spec.Chacha.crypt` (fewer for the last), and the
epilogue. The invariant of the block loop (`Outer`) says which bytes are written so far and that
the state matrix in the frame has the block counter advanced by the number of blocks.
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20 Ssl.Spec.Chacha

/-- The facts of the call kept by the block loop after `j` blocks. -/
structure Outer (M0 : ByteArray) (C out inp : UInt32) (key ctr : Array UInt32) (src : List UInt8)
    (sesi sedi sebx sebp : UInt32) (j : Nat) (M : ByteArray) : Prop where
  agree : AgreeOn (fun a => (C.toNat - 224 ≤ a ∧ a < C.toNat + 288) ∨
    (out.toNat ≤ a ∧ a < out.toNat + min (64 * j) src.length)) M0 M
  words : InAt M C (wJ key ctr j)
  saved : rdRaw M (C.add 272) 4 = sesi ∧ rdRaw M (C.add 276) 4 = sedi ∧ rdRaw M (C.add 280) 4 = sebx ∧
    rdRaw M (C.add 284) 4 = sebp
  bytes : ∀ i (hi : i < 64 * j) (hl : i < src.length),
    M.get! (out.toNat + i) = (crypt 20 (state key ctr) src)[i]'(by rw [crypt_length]; exact hl)

/-- The address facts of a call, in `toNat` form. -/
structure Facts (size : Nat) (C out inp : UInt32) (len : Nat) : Prop where
  sz : size ≤ 4273995776
  clo : 224 ≤ C.toNat
  cfit : C.toNat + 312 ≤ size
  ccode : 1049648 + 224 ≤ C.toNat ∨ C.toNat + 312 ≤ 1048576
  len31 : len < 2 ^ 31
  ofit : out.toNat + len ≤ size
  ifit : inp.toNat + len ≤ size
  ocode : out.toNat + len ≤ 1048576 ∨ 1049648 ≤ out.toNat
  icode : inp.toNat + len ≤ 1048576 ∨ 1049648 ≤ inp.toNat
  ostack : out.toNat + len ≤ C.toNat - 224 ∨ C.toNat + 312 ≤ out.toNat
  istack : inp.toNat + len ≤ C.toNat - 224 ∨ C.toNat + 312 ≤ inp.toNat
  io : inp = out ∨ inp.toNat + len ≤ out.toNat ∨ out.toNat + len ≤ inp.toNat

theorem ptr_toNat {p : UInt32} {k : Nat} (h : p.toNat + k < 2 ^ 32) : (p + k.toUInt32).toNat = p.toNat + k :=
  toNat_natAdd h

/-- The input byte `k` is the caller's. -/
theorem inp_byte {M0 M : ByteArray} {C out inp : UInt32} {key ctr : Array UInt32} {src : List UInt8}
    {sesi sedi sebx sebp : UInt32} {j : Nat} (hF : Facts M0.size C out inp src.length)
    (hO : Outer M0 C out inp key ctr src sesi sedi sebx sebp j M) (hsrc : memBytes M0 inp src.length = src)
    (k : Nat) (hk : k < src.length) (hkj : 64 * j ≤ k) :
    M.get! (inp.toNat + k) = src[k] := by
  have hpos : inp.toNat + k < M0.size := by have := hF.ifit; omega
  rw [hO.agree.2 _ hpos (by
    intro h
    rcases h with h | h
    · have := hF.istack; omega
    · rcases hF.io with e | e | e
      · subst e; omega
      · omega
      · omega)]
  have := (memBytes_eq_iff.1 hsrc).2 k hk
  rw [memByte_def (by rw [ptr_toNat (by have := hF.sz; omega)]; exact hpos),
    ptr_toNat (by have := hF.sz; omega)] at this
  exact this

set_option maxHeartbeats 4000000 in
/-- One block, at the level of the call. -/
theorem outer_step {M0 : ByteArray} {C out inp : UInt32} {key ctr : Array UInt32} {src : List UInt8}
    {sesi sedi sebx sebp : UInt32} (hk : key.size = 8) (hc : ctr.size = 4)
    (hF : Facts M0.size C out inp src.length) (hsrc : memBytes M0 inp src.length = src)
    (H : CMem) (hsz : H.get.size = M0.size) (j : Nat) (hj : 64 * j < src.length)
    (hO : Outer M0 C out inp key ctr src sesi sedi sebx sebp j H.get)
    (eax ecx edx edi f : UInt32) (ic : UInt64) (hic : ic.toNat + 4096 < 2 ^ 64) :
    ∃ (H' : CMem) (f' eax' ecx' edx' : UInt32) (ic' : UInt64),
      Run img (St.m ⟨H.get, eax, ecx, edx, (src.length - 64 * j).toUInt32, C.add 144, inp + (64 * j).toUInt32,
          out + (64 * j).toUInt32, edi, 0x1000b0, efl f, ic⟩)
        (St.m ⟨H'.get, eax', ecx', edx', UInt32.sub (src.length - 64 * j).toUInt32 (blockN (src.length - 64 * j).toUInt32),
          C.add 144, UInt32.add (inp + (64 * j).toUInt32) (blockN (src.length - 64 * j).toUInt32),
          UInt32.add (out + (64 * j).toUInt32) (blockN (src.length - 64 * j).toUInt32),
          blockN (src.length - 64 * j).toUInt32,
          if (src.length - 64 * j).toUInt32.toNat ≤ 64 then 0x1000ed else 0x1000b0, efl f', ic'⟩) ∧
      ic'.toNat ≤ ic.toNat + 4096 ∧ H'.get.size = M0.size ∧
      Outer M0 C out inp key ctr src sesi sedi sebx sebp (j + 1) H'.get := by
  obtain ⟨hsz0, hclo, hcfit, hccode, hlen, hofit, hifit, hocode, hicode, hostack, histack, hio⟩ := hF
  have hF : Facts M0.size C out inp src.length :=
    ⟨hsz0, hclo, hcfit, hccode, hlen, hofit, hifit, hocode, hicode, hostack, histack, hio⟩
  have hremN : (src.length - 64 * j).toUInt32.toNat = src.length - 64 * j := toUInt32_toNat (by omega)
  have hnN : (blockN (src.length - 64 * j).toUInt32).toNat = min (src.length - 64 * j) 64 := by rw [blockN_toNat, hremN]
  have hip : (inp + (64 * j).toUInt32).toNat = inp.toNat + 64 * j := ptr_toNat (by omega)
  have hop : (out + (64 * j).toUInt32).toNat = out.toNat + 64 * j := ptr_toNat (by omega)
  have hB : BlockOk H.get.size C (inp + (64 * j).toUInt32) (out + (64 * j).toUInt32) (blockN (src.length - 64 * j).toUInt32).toNat := by
    refine ⟨⟨by rw [hsz]; exact hsz0, by omega, by rw [hsz]; omega, by omega⟩, by omega, by omega,
      ⟨by rw [hip, hsz]; omega, by rw [hip]; omega⟩, ⟨by rw [hop, hsz]; omega, by rw [hop]; omega⟩, ?_,
      by rw [hip]; omega, by rw [hop]; omega⟩
    rcases hio with e | e | e
    · left; rw [e]
    · right; left; rw [hip, hop]; omega
    · right; right; rw [hip, hop]; omega
  obtain ⟨H', f', eax', ecx', edx', ic', hr, hic', ha, hw, hb⟩ :=
    block_run H C eax ecx edx edi (src.length - 64 * j).toUInt32 (inp + (64 * j).toUInt32) (out + (64 * j).toUInt32) f (wJ key ctr j) ic hB
      hO.words hic
  have hs' : H'.get.size = M0.size := ha.1.trans hsz
  refine ⟨H', f', eax', ecx', edx', ic', ?_, hic', hs', ?_⟩
  · exact hr
  · have notS : ∀ a, (out.toNat ≤ a ∧ a < out.toNat + src.length) → ¬ (C.toNat - 24 ≤ a ∧ a < C.toNat + 272) := by
      intro a h1 h2; omega
    refine ⟨?_, hw, ?_, ?_⟩
    · refine (hO.agree.mono (fun a h => by (try simp only at h ⊢) <;> omega)).trans (ha.mono ?_)
      intro a h
      unfold BlockRegion at h
      rw [hop] at h
      omega
    · have e : ∀ (k : Nat) (v : UInt32), 272 ≤ k → k ≤ 284 → rdRaw H.get (C.add (OfNat.ofNat k)) 4 = v →
          rdRaw H'.get (C.add (OfNat.ofNat k)) 4 = v := by
        intro k v hk1 hk2 hv
        have hk : (C.add (OfNat.ofNat k)).toNat = C.toNat + k := caddv (by omega) (by omega)
        rw [ha.rdRaw4 (by rw [hk, hsz]; omega) (fun q hq h => by unfold BlockRegion at h; rw [hk, hop] at h; omega)]
        exact hv
      obtain ⟨s1, s2, s3, s4⟩ := hO.saved
      exact ⟨e 272 _ (by omega) (by omega) s1, e 276 _ (by omega) (by omega) s2, e 280 _ (by omega) (by omega) s3,
        e 284 _ (by omega) (by omega) s4⟩
    · intro i hi hl
      by_cases hij : i < 64 * j
      · rw [ha.2 _ (by rw [hsz]; omega) (by unfold BlockRegion; rw [hop]; omega)]
        exact hO.bytes i hij hl
      · have hi' : i - 64 * j < (blockN (src.length - 64 * j).toUInt32).toNat := by rw [hnN]; omega
        have h1 := hb (i - 64 * j) hi'
        rw [hop, hip, show out.toNat + 64 * j + (i - 64 * j) = out.toNat + i by omega,
          show inp.toNat + 64 * j + (i - 64 * j) = inp.toNat + i by omega, inp_byte hF hO hsrc i hl (by omega)] at h1
        rw [h1, crypt_getElem _ _ (by rw [state_size hk hc]; decide)]
        have hdiv : i / 64 = j := by omega
        have hmod : i % 64 = i - 64 * j := by omega
        refine congrArg (fun x => _ ^^^ x) ?_
        simp only [wJ_toArr hk hc, hdiv, hmod]

end Solutions.OpensslChacha20
