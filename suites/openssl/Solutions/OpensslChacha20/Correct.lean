import Solutions.OpensslChacha20.Final
import Solutions.OpensslChacha20.Entry
/-!
# `ChaCha20_ctr32` is RFC 8439 ChaCha20

`Solutions.OpensslChacha20.ChaCha20_ctr32_correct : Ssl.OpensslChacha20.ChaCha20_ctr32_correct`.
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20 Ssl.Spec.Chacha

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ChaCha20_ctr32_correct : Ssl.OpensslChacha20.ChaCha20_ctr32_correct := by
  intro c out inp keyp ctrp key ctr src hpre
  have hpre0 := hpre
  obtain ⟨hcalls, hks, hcs, hbo, hbi, hbk, hbc, hio, hok, hoc, hkey, hctr, hsrc⟩ := hpre
  have hsz : c.mem.size ≤ 4273995776 := hcalls.1
  have hsp : 512 ≤ c.sp.toNat := hcalls.2.2.2.2.1
  have hspfit : c.sp.toNat + 24 ≤ c.mem.size := by
    have := hcalls.2.2.2.2.2.1; simpa [args] using this
  have hlo : (c.stackLo stackBound).toNat = c.sp.toNat - 512 := by
    unfold Caller.stackLo stackBound
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    simp
  have himg := apart_nat hcalls.2.2.2.2.2.2 (by simp [stackSize]) (by rw [img_bytes_size]; decide)
  rw [hlo, img_bytes_size, img_base_toNat] at himg
  simp only [stackSize, stackBound, args, List.length] at himg
  -- the frame base `C`: the caller's stack pointer is `C + 288`
  let C : UInt32 := c.sp - 288
  have hC : C.toNat = c.sp.toNat - 288 := by
    show (c.sp - 288).toNat = _
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; show 288 ≤ c.sp.toNat; omega)]
    rfl
  have hspC : c.sp = C.add 288 := by
    apply UInt32.toNat_inj.1
    rw [cadd (by omega) (by decide), hC]; omega
  have hS : StackOk c.mem.size C := ⟨hsz, by omega, by omega, by omega⟩
  let G : CMem := callMem (byte := Image.byte) rfl hcalls
  have hG : G.get = c.mem := rfl
  have hGs : G.get.size = c.mem.size := rfl
  -- the arguments and the return address
  have harg : ∀ (i : Nat) (hi : i < 5) (k : Nat), k = 292 + 4 * i →
      rdRaw c.mem (C.add (OfNat.ofNat k)) 4 = (args out inp keyp ctrp src)[i]'(by simp [args]; omega) := by
    intro i hi k hk
    have := calls_arg hcalls i (by simp [args]; omega)
    unfold rdRaw
    rw [← this]
    congr 1
    apply UInt32.toNat_inj.1
    subst hk
    have : c.sp.toNat < 2 ^ 32 := c.sp.toNat_lt
    rw [caddv (by omega) (by omega), UInt32.toNat_add, UInt32.toNat_mul, show (4 : UInt32).toNat = 4 from rfl,
      toUInt32_toNat (by omega)]
    omega
  have hret : rdRaw c.mem (C.add 288) 4 = 0x10042F := by rw [← hspC]; exact calls_ret hcalls
  -- the key and the counter
  have hkp : keyp.toNat + 32 ≤ c.mem.size := by rcases hbk.1 with h | h <;> omega
  have hcp : ctrp.toNat + 16 ≤ c.mem.size := by rcases hbc.1 with h | h <;> omega
  have hksA : keyp.toNat + 32 ≤ C.toNat ∨ C.toNat + 312 ≤ keyp.toNat := by
    have := apart_nat hbk.2.2.2 (by decide) (by simp [stackSize])
    rw [hlo] at this; simp only [stackSize, stackBound] at this; omega
  have hcsA : ctrp.toNat + 16 ≤ C.toNat ∨ C.toNat + 312 ≤ ctrp.toNat := by
    have := apart_nat hbc.2.2.2 (by decide) (by simp [stackSize])
    rw [hlo] at this; simp only [stackSize, stackBound] at this; omega
  have kw : ∀ i, i < 8 → ∀ k, k = 4 * i → rdRaw c.mem (keyp.add (OfNat.ofNat k)) 4 = key[i]! :=
    fun i hi k hk => word_at hkey i hi (by rw [hks]; exact hi) k hk (by omega)
  have cw : ∀ i, i < 4 → ∀ k, k = 4 * i → rdRaw c.mem (ctrp.add (OfNat.ofNat k)) 4 = ctr[i]! :=
    fun i hi k hk => word_at hctr i hi (by rw [hcs]; exact hi) k hk (by omega)
  -- the entry
  have e0 : c.enter Image.sym_ChaCha20_ctr32 = St.m ⟨G.get, c.regs.eax, c.regs.ecx, c.regs.edx, c.regs.ebx,
      C.add 288, c.regs.ebp, c.regs.esi, c.regs.edi, 0x100000, efl c.regs.flags, 0⟩ := by
    rw [← hspC]; rfl
  obtain ⟨H1, f1, e1, hsv4, hsv3, hsv2, hsv1, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12,
      hw13, hw14, hw15, ha1⟩ :=
    entry_run G C c.regs.flags c.regs.eax c.regs.ecx c.regs.edx c.regs.ebx c.regs.ebp c.regs.esi c.regs.edi
      src.length.toUInt32 ctrp keyp key[0]! key[1]! key[2]! key[3]! key[4]! key[5]! key[6]! key[7]!
      ctr[0]! ctr[1]! ctr[2]! ctr[3]! 0 hS hkp hksA hcp hcsA (harg 2 (by omega) 300 rfl) (harg 4 (by omega) 308 rfl)
      (harg 3 (by omega) 304 rfl) (word_at0 hkey (by omega) (by rw [hks]; omega))
      (kw 1 (by omega) 4 rfl) (kw 2 (by omega) 8 rfl) (kw 3 (by omega) 12 rfl) (kw 4 (by omega) 16 rfl)
      (kw 5 (by omega) 20 rfl) (kw 6 (by omega) 24 rfl) (kw 7 (by omega) 28 rfl)
      (word_at0 hctr (by omega) (by rw [hcs]; omega)) (cw 1 (by omega) 4 rfl) (cw 2 (by omega) 8 rfl)
      (cw 3 (by omega) 12 rfl)
  have r1 := run_of_exN e1 (by show (0 : UInt64).toNat + 36 < 2 ^ 64; decide)
  have hs1 : H1.get.size = c.mem.size := ha1.1
  have hS1 : StackOk H1.get.size C := by rw [hs1]; exact hS
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15⟩ := w0_x hks hcs
  have hwords : InAt H1.get C (wJ key ctr 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [x0]; exact hw0
    · rw [x1]; exact hw1
    · rw [x2]; exact hw2
    · rw [x3]; exact hw3
    · rw [x4]; exact hw4
    · rw [x5]; exact hw5
    · rw [x6]; exact hw6
    · rw [x7]; exact hw7
    · rw [x8]; exact hw8
    · rw [x9]; exact hw9
    · rw [x10]; exact hw10
    · rw [x11]; exact hw11
    · rw [x12]; exact hw12
    · rw [x13]; exact hw13
    · rw [x14]; exact hw14
    · rw [x15]; exact hw15
  have hret1 : rdRaw H1.get (C.add 288) 4 = 0x10042F := by
    rw [ha1.rdRaw4 (by rw [cadd (by omega) (by decide)]; omega)
      (fun k hk h => by rw [cadd (by omega) (by decide)] at h; omega)]
    exact hret
  have hesp : C.add 292 = c.sp + 4 := by
    apply UInt32.toNat_inj.1
    rw [cadd (by omega) (by decide), UInt32.toNat_add]
    show _ = (c.sp.toNat + 4) % 2 ^ 32
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hstk : ∀ a : UInt32, ¬ InRange (c.sp - (stackBound : Nat).toUInt32) stackBound a →
      ¬ (C.toNat - 224 ≤ a.toNat ∧ a.toNat < C.toNat + 288) := by
    intro a ha h
    apply ha
    rw [inRange_iff, show (c.sp - (stackBound : Nat).toUInt32) = c.stackLo stackBound from rfl, hlo]
    simp only [stackBound]; omega
  rw [e0]
  by_cases hl : src.length = 0
  · -- an empty input
    obtain ⟨f2, e2⟩ := empty_run H1 C ctr[3]! ctr[2]! key[6]! src.length.toUInt32 c.regs.ebp c.regs.esi c.regs.edi
      f1 (0 + 36) hS1 (by rw [hl]; rfl)
    have r2 := run_of_exN e2 (by show (0 + 36 : UInt64).toNat + 2 < 2 ^ 64; decide)
    obtain ⟨f3, e3⟩ := epilogue_run H1 C ctr[3]! ctr[2]! key[6]! src.length.toUInt32 c.regs.ebp c.regs.esi
      c.regs.edi f2 c.regs.esi c.regs.edi c.regs.ebx c.regs.ebp (0 + 36 + 2) hS1 hsv1 hsv2 hsv3 hsv4 hret1
    have r3 := run_of_exN e3 (by show (0 + 36 + 2 : UInt64).toNat + 6 < 2 ^ 64; decide)
    refine Returns.intro (r1.trans (r2.trans r3)) ⟨rfl, ?_, efl_DF _⟩ ⟨rfl, rfl, rfl, rfl⟩ ⟨hs1, ?_⟩ ?_
    · show C.add 292 = C.add 288 + 4
      rw [← hspC]; exact hesp
    · intro a ha _ hs
      show memByte H1.get a = memByte c.mem a
      rw [← hspC] at hs
      exact ha1.memByte ha (fun h => hstk a hs ⟨by omega, by omega⟩)
    · show memBytes H1.get out src.length = crypt 20 (state key ctr) src
      have : src = [] := List.eq_nil_of_length_eq_zero hl
      subst this
      simp [memBytes, crypt]
  · -- the blocks
    have hF := facts_of_pre hpre0 hl C (by omega)
    obtain ⟨f2, e2⟩ := nonempty_run H1 C ctr[3]! ctr[2]! key[6]! src.length.toUInt32 c.regs.ebp c.regs.esi c.regs.edi
      f1 out inp (0 + 36) hS1 (by rw [toUInt32_toNat (by have := hF.len31; omega)]; exact hl)
      (by rw [ha1.rdRaw4 (by rw [cadd (by omega) (by decide)]; omega)
        (fun k hk h => by rw [cadd (by omega) (by decide)] at h; omega)]; exact harg 0 (by omega) 292 rfl)
      (by rw [ha1.rdRaw4 (by rw [cadd (by omega) (by decide)]; omega)
        (fun k hk h => by rw [cadd (by omega) (by decide)] at h; omega)]; exact harg 1 (by omega) 296 rfl)
    have r2 := run_of_exN e2 (by show (0 + 36 : UInt64).toNat + 18 < 2 ^ 64; decide)
    have hlen := hF.len31
    -- the head of the block loop after `j` blocks
    have loop : ∀ j, 64 * j < src.length → ∃ (H : CMem) (f eax ecx edx edi : UInt32) (ic : UInt64),
        Run img (St.m ⟨G.get, c.regs.eax, c.regs.ecx, c.regs.edx, c.regs.ebx, C.add 288, c.regs.ebp, c.regs.esi,
            c.regs.edi, 0x100000, efl c.regs.flags, 0⟩)
          (St.m ⟨H.get, eax, ecx, edx, (src.length - 64 * j).toUInt32, C.add 144, inp + (64 * j).toUInt32,
            out + (64 * j).toUInt32, edi, 0x1000b0, efl f, ic⟩) ∧
        ic.toNat ≤ 54 + 4096 * j ∧ H.get.size = c.mem.size ∧
        Outer c.mem C out inp key ctr src c.regs.esi c.regs.edi c.regs.ebx c.regs.ebp j H.get := by
      intro j
      induction j with
      | zero =>
        intro _
        refine ⟨H1, f2, ctr[3]!, ctr[2]!, key[6]!, c.regs.edi, 0 + 36 + 18, ?_, by decide, hs1, ?_⟩
        · have h0 : (src.length - 64 * 0).toUInt32 = src.length.toUInt32 := by simp
          have h1 : ∀ p : UInt32, p + (64 * 0 : Nat).toUInt32 = p := fun p => by simp
          rw [h0, h1, h1]
          exact r1.trans r2
        · refine ⟨ha1.mono (fun a h => Or.inl ⟨by omega, by omega⟩), hwords,
            ⟨hsv1, hsv2, hsv3, hsv4⟩, fun i hi _ => absurd hi (by omega)⟩
      | succ j ih =>
        intro hj
        obtain ⟨H, f, eax, ecx, edx, edi, ic, hr, hic, hsH, hO⟩ := ih (by omega)
        obtain ⟨H', f', eax', ecx', edx', ic', hr', hic', hs', hO'⟩ :=
          outer_step hks hcs hF hsrc H hsH j (by omega) hO eax ecx edx edi f ic (by omega)
        have hremN : (src.length - 64 * j).toUInt32.toNat = src.length - 64 * j := toUInt32_toNat (by omega)
        have hrem : ¬ ((src.length - 64 * j).toUInt32.toNat ≤ 64) := by rw [hremN]; omega
        have hb64 : blockN (src.length - 64 * j).toUInt32 = 64 := by
          unfold blockN; rw [if_neg (by rw [hremN]; omega)]
        rw [if_neg hrem, hb64] at hr'
        have esub : UInt32.sub (src.length - 64 * j).toUInt32 64 = (src.length - 64 * (j + 1)).toUInt32 := by
          apply UInt32.toNat_inj.1
          show ((src.length - 64 * j).toUInt32 - 64).toNat = _
          rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hremN]; simp; omega), hremN,
            toUInt32_toNat (by omega)]
          simp; omega
        have eadd : ∀ p : UInt32, p.toNat + src.length ≤ c.mem.size →
            UInt32.add (p + (64 * j).toUInt32) 64 = p + (64 * (j + 1)).toUInt32 := by
          intro p hp
          apply UInt32.toNat_inj.1
          show (p + (64 * j).toUInt32 + 64).toNat = _
          rw [UInt32.toNat_add, ptr_toNat (by omega), ptr_toNat (by omega)]
          simp; omega
        rw [esub, eadd inp hF.ifit, eadd out hF.ofit] at hr'
        exact ⟨H', f', eax', ecx', edx', 64, ic', hr.trans hr', by omega, hs', hO'⟩
    -- the last block
    obtain ⟨H, f, eax, ecx, edx, edi, ic, hr, hic, hsH, hO⟩ := loop ((src.length - 1) / 64) (by omega)
    obtain ⟨H', f', eax', ecx', edx', ic', hr', hic', hs', hO'⟩ :=
      outer_step hks hcs hF hsrc H hsH ((src.length - 1) / 64) (by omega) hO eax ecx edx edi f ic (by omega)
    have hlast : (src.length - 64 * ((src.length - 1) / 64)).toUInt32.toNat ≤ 64 := by
      rw [toUInt32_toNat (by omega)]; omega
    rw [if_pos hlast] at hr'
    have hS' : StackOk H'.get.size C := by rw [hs']; exact hS
    have hret' : rdRaw H'.get (C.add 288) 4 = 0x10042F := by
      rw [hO'.agree.rdRaw4 (by rw [cadd (by omega) (by decide)]; omega) (fun k hk h => by
        rw [cadd (by omega) (by decide)] at h
        rcases h with h | h
        · omega
        · have := hF.ostack; omega)]
      exact hret
    obtain ⟨s1, s2, s3, s4⟩ := hO'.saved
    obtain ⟨f3, e3⟩ := epilogue_run H' C eax' ecx' edx' _ _ _ _ f' c.regs.esi c.regs.edi c.regs.ebx c.regs.ebp ic'
      hS' s1 s2 s3 s4 hret'
    have r3 := run_of_exN e3 (by show ic'.toNat + 6 < 2 ^ 64; omega)
    refine Returns.intro (hr.trans (hr'.trans r3)) ⟨rfl, ?_, efl_DF _⟩ ⟨rfl, rfl, rfl, rfl⟩ ⟨by show H'.get.size = c.mem.size; exact hs', ?_⟩ ?_
    · show C.add 292 = C.add 288 + 4
      rw [← hspC]; exact hesp
    · intro a ha hw hs
      show memByte H'.get a = memByte c.mem a
      rw [← hspC] at hs
      apply hO'.agree.memByte ha
      intro h
      rcases h with h | h
      · exact hstk a hs h
      · exact hw (inRange_iff.2 ⟨by omega, by omega⟩)
    · show memBytes H'.get out src.length = crypt 20 (state key ctr) src
      apply memBytes_eq_iff.2
      refine ⟨crypt_length _ _ _, fun i hi => ?_⟩
      rw [crypt_length] at hi
      have hpos : (out + i.toUInt32).toNat = out.toNat + i := ptr_toNat (by have := hF.ofit; omega)
      rw [memByte_def (by rw [hpos, hs']; have := hF.ofit; omega), hpos]
      exact hO'.bytes i (by omega) hi

end Solutions.OpensslChacha20
