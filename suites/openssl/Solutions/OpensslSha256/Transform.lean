import Solutions.OpensslSha256.Run
/-!
# `SHA256_Transform_correct`

The run of `run_all` from the caller's machine: the call returns to the sentinel with the stack
pointer popped, the callee-saved registers restored, memory changed only in the context and the
call's stack, and the eight hash words in the context replaced by `Spec.Sha256.compress H block`.
-/
namespace Solutions.OpensslSha256
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslSha256 Ssl.Spec.Sha256

theorem u32_add_sub (x : UInt32) (a : UInt32) : x - a + a = x := by
  apply UInt32.toNat_inj.1
  simp only [UInt32.toNat_add, UInt32.toNat_sub]
  have := x.toNat_lt; have := a.toNat_lt
  omega

theorem u32_sub_add (x : UInt32) (a b c : UInt32) (h : b - a = c) : x - a + b = x + c := by
  subst h
  apply UInt32.toNat_inj.1
  simp only [UInt32.toNat_add, UInt32.toNat_sub]
  have := x.toNat_lt; have := a.toNat_lt; have := b.toNat_lt
  omega

/-- The block's words, big-endian, are the byte-swapped words of memory. -/
theorem block_words (V : Env) (block : List UInt8) (hb : memBytes V.M0 V.blk 64 = block) (k : Nat)
    (hk : k < 16) :
    ((((blkWord V k <<< 24) ||| ((blkWord V k &&& 65280) <<< 8)) |||
      ((blkWord V k >>> 8) &&& 65280)) ||| (blkWord V k >>> 24)) = (schedule block)[k]! := by
  have h1 := V.hblk; have h2 := V.hsz
  have hbl := blk_toNat V k hk
  have hw : blkWord V k = (V.M0.get! (V.blk.toNat + 4 * k)).toUInt32 |||
      ((V.M0.get! (V.blk.toNat + 4 * k + 1)).toUInt32 <<< 8) |||
      ((V.M0.get! (V.blk.toNat + 4 * k + 2)).toUInt32 <<< 16) |||
      ((V.M0.get! (V.blk.toNat + 4 * k + 3)).toUInt32 <<< 24) := by
    unfold blkWord
    rw [rdBytes4_eq (by rw [hbl]; omega), hbl]
  rw [hw, bswap_join]
  show _ = Ws block k
  rw [Ws_lt block k hk]
  have hlen : block.length = 64 := by rw [← hb]; exact memBytes_length _ _ _
  have byte : ∀ i, i < 64 → block[i]! = V.M0.get! (V.blk.toNat + i) := by
    intro i hi
    rw [getElem!_pos block i (by omega)]
    have := memBytes_getElem V.M0 V.blk 64 i (by rw [memBytes_length]; omega)
    simp only [hb] at this
    rw [this, memByte_def (by rw [toNat_add_of_lt (by unfold ramTop at h2; omega)]; omega),
      toNat_add_of_lt (by unfold ramTop at h2; omega)]
  unfold be32At
  rw [byte (4 * k) (by omega), byte (4 * k + 1) (by omega), byte (4 * k + 2) (by omega),
    byte (4 * k + 3) (by omega)]
  simp only [Nat.add_assoc, shl32]

theorem ctx_word (V : Env) (H : Array UInt32) (hH : H.size = 8) (hw : memWords V.M0 V.ctx 8 = H) (k : Nat)
    (hk : k < 8) : rdBytes V.M0 (slotAddr V (48 + k)) 4 = H[k]! := by
  have := memWords_get hw k hk (by omega)
  rw [getElem!_pos H k (by omega), ← this]
  unfold memWord slotAddr
  rw [if_neg (by omega), show 48 + k - 48 = k by omega]
  congr 2
  apply UInt32.toNat_inj.1
  simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat', UInt32.toNat_mul, UInt32.reduceToNat]
  have : k < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt this]

set_option maxRecDepth 100000 in
theorem transform_correct : SHA256_Transform_correct := by
  intro c ctx blockp H block hpre
  have hF := callFacts hpre
  obtain ⟨hc, hH, hlen, -, -, -, hwords, hbytes⟩ := hpre
  let V := envOf c ctx blockp hF (calls_code hc)
  have hspV : V.sp + 192 = c.sp := u32_add_sub c.sp 192
  have hret : rdBytes V.M0 (V.sp + 192) 4 = 0x101248 := by
    rw [hspV]; exact calls_ret hc
  have harg1 : rdBytes V.M0 (UInt32.add (V.sp + 192) (UInt8.toUInt32 4)) 4 = V.ctx := by
    have := calls_arg hc 0 (by simp)
    show rdBytes c.mem (V.sp + 192 + 4) 4 = ctx
    rw [hspV]; simpa using this
  have harg2 : rdBytes V.M0 (UInt32.add (V.sp + 192) (UInt8.toUInt32 8)) 4 = V.blk := by
    have := calls_arg hc 1 (by simp)
    show rdBytes c.mem (V.sp + 192 + 8) 4 = blockp
    rw [hspV]; simpa using this
  have hblk := block_words V block hbytes
  have hseg := run_all V H block c.regs.ebp c.regs.ebx c.regs.edi c.regs.esi hblk harg1 harg2 hret
  let r0 : R := ⟨c.regs.eax, c.regs.ecx, c.regs.edx, c.regs.ebx, c.sp, c.regs.ebp, c.regs.esi, c.regs.edi⟩
  let F0 : Nat → UInt32 := fun j => rdBytes c.mem (slotAddr V j) 4
  obtain ⟨r1, F1, hs⟩ := hseg r0 F0
  have hall : AllEq F0 [(48, H[0]!), (49, H[1]!), (50, H[2]!), (51, H[3]!), (52, H[4]!), (53, H[5]!),
      (54, H[6]!), (55, H[7]!)] :=
    ⟨ctx_word V H hH hwords 0 (by decide), ctx_word V H hH hwords 1 (by decide),
      ctx_word V H hH hwords 2 (by decide), ctx_word V H hH hwords 3 (by decide),
      ctx_word V H hH hwords 4 (by decide), ctx_word V H hH hwords 5 (by decide),
      ctx_word V H hH hwords 6 (by decide), ctx_word V H hH hwords 7 (by decide), trivial⟩
  have hI : Inv V c.mem (updL F0 [(48, H[0]!), (49, H[1]!), (50, H[2]!), (51, H[3]!), (52, H[4]!), (53, H[5]!),
      (54, H[6]!), (55, H[7]!)]) :=
    ⟨rfl, fun _ _ _ => rfl, fun j _ => by rw [updL_self F0 _ hall j]⟩
  obtain ⟨M', fl', hrun, hI'⟩ := hs c.mem c.regs.flags 0 hI (by decide)
  let rP : R := ⟨c.regs.eax, c.regs.ecx, c.regs.edx, c.regs.ebx, V.sp + 192, c.regs.ebp, c.regs.esi, c.regs.edi⟩
  have he : conc c.mem rP c.regs.flags 0x1011b0 0 = c.enter Image.sym_SHA256_Transform := by
    show St.m ⟨c.mem, c.regs.eax, c.regs.ecx, c.regs.edx, c.regs.ebx, V.sp + 192, c.regs.ebp, c.regs.esi,
      c.regs.edi, 0x1011b0, efl c.regs.flags, 0⟩ = _
    rw [hspV]; rfl
  rw [← he]
  have hsz' := hI'.size
  refine Returns.intro hrun ⟨?_, ?_, ?_⟩ ⟨rfl, rfl, rfl, rfl⟩ ⟨hsz', fun a ha hw hs' => ?_⟩ ?_
  · rfl
  · show V.sp + 196 = V.sp + 192 + 4
    exact (add_norm V.sp 192 4 196 (by decide)).symm
  · exact efl_DF fl'
  · have hsp := hF.sp_lo
    change a.toNat < c.mem.size at ha
    show memByte M' a = memByte c.mem a
    rw [memByte_def (by rw [hsz']; exact ha), memByte_def ha]
    refine hI'.out a.toNat ha fun hin => ?_
    rw [inRange_iff] at hw hs'
    have hv : V.sp.toNat = c.sp.toNat - 192 := sp192_toNat hsp
    have hcx : V.ctx.toNat = ctx.toNat := rfl
    have hlo : (c.sp - stackBound.toUInt32).toNat = c.sp.toNat - 512 := by
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp [stackBound]; omega)]
      simp [stackBound]
    rw [show (conc c.mem rP c.regs.flags 0x1011b0 0).cpu.esp = c.sp from hspV, hlo] at hs'
    unfold InSlots at hin
    simp only [stackBound] at hs'
    omega
  · show wordsAt (conc M' _ fl' 0x101248 _) ctx 8 = compress H block
    have hw : ∀ k, k < 8 → rdBytes M' (slotAddr V (48 + k)) 4 = _ := fun k hk => hI'.slot (48 + k) (by omega)
    rw [compress_eq, fin8_eq]
    simp only [B_succ H (schedule block) 63, C_succ H (schedule block) 63, B_succ H (schedule block) 62,
      D_succ H (schedule block) 63, C_succ H (schedule block) 62, B_succ H (schedule block) 61,
      F_succ H (schedule block) 63, G_succ H (schedule block) 63, F_succ H (schedule block) 62,
      Hh_succ H (schedule block) 63, G_succ H (schedule block) 62, F_succ H (schedule block) 61]
    apply Array.ext
    · simp [wordsAt, memWords]
    · intro i h1 h2
      simp only [wordsAt, memWords, Array.getElem_ofFn]
      have hi : i < 8 := by simpa [wordsAt, memWords] using h1
      have hk := hw i hi
      simp only [updL, upd] at hk
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hk

end Solutions.OpensslSha256
