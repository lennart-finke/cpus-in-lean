import Solutions.OpensslSha256.Chain
import Solutions.OpensslSha256.Alg
import Solutions.OpensslSha256.ChainF
import Solutions.OpensslSha256.FJ
import Solutions.OpensslSha256.Fam.F00
import Solutions.OpensslSha256.Fam.F01
import Solutions.OpensslSha256.Fam.F02
import Solutions.OpensslSha256.Fam.F03
import Solutions.OpensslSha256.Fam.F04
import Solutions.OpensslSha256.Fam.F13
import Solutions.OpensslSha256.Fam.FX
/-! The end of a block of the block function (generated): the additions into the hash words up to
`decl %esi` (`segn_epiA`), then the stores of the hash words into the context and the loop branch,
taken for a count other than 1 (`segn_next`) or not taken, followed by the return (`segn_ret`). -/
namespace Solutions.OpensslSha256
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.Spec.Sha256
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem segn_epiA (V : Env) (H : Array UInt32) (blk : List UInt8) (sv0 sv1 sv2 sv3 cnt ra : UInt32) :
    Seg V 24 0x1010f5
      (fun r => { r with esp := V.sp, ecx := A H (schedule blk) 63, edi := A H (schedule blk) 64 })
      (fun F => updL F ([(0, E H (schedule blk) 64), (1, E H (schedule blk) 62), (2, (56 : UInt32)), (3, E H (schedule blk) 61), (4, A H (schedule blk) 62), (5, E H (schedule blk) 63), (6, A H (schedule blk) 61), (8, V.blk), (10, H[2]!), (11, H[1]!), (12, H[0]!), (13, H[5]!), (14, H[3]!), (15, H[6]!), (16, H[4]!), (38, V.ctx), (39, H[7]!), (40, cnt), (42, sv3), (43, sv2), (44, sv1), (45, sv0), (46, ra)] : List (Nat × UInt32)))
      0x101159
      (fun r => { r with esp := V.sp, ecx := H[4]! + E H (schedule blk) 64, edx := V.blk + 64, ebp := H[5]! + E H (schedule blk) 63, esi := cnt, edi := H[7]! + E H (schedule blk) 61 })
      (fun F => updL F ([(10, H[2]! + A H (schedule blk) 62), (11, H[1]! + A H (schedule blk) 63), (12, H[0]! + A H (schedule blk) 64), (14, H[3]! + A H (schedule blk) 61), (15, H[6]! + E H (schedule blk) 62), (38, V.ctx), (42, sv3), (43, sv2), (44, sv1), (45, sv0), (46, ra)] : List (Nat × UInt32))) := by
  apply Seg.ofL
  intro r0 F0
  apply Exists.intro
  apply Exists.intro
  refine ⟨?_, ?_, ?_⟩
  · apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((56)) (A H (schedule blk) 63) (r0.edx) (r0.ebx) (V.sp) (r0.ebp) (r0.esi) (A H (schedule blk) 64)) (Steps.load' (fun r v => { r with eax := v }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 8))) 2 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_8b4424dd 0x1010f5 8 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 3
    · apply Steps.ofF; intro fl0; apply Exists.intro
      apply StepsF.consK 1
      · exact (StepsF.reg (by decide) (by decide) (fun G ic hsz => famCMP 0x1010f9 G _ fl0 ic (by decide) hsz))
      apply StepsF.consK 1
      · exact (StepsF.reg (by decide) (by decide) (fun G ic hsz => fam_8d40dd 0x1010fc 8 G _ _ ic (by decide) hsz (by decide)))
      apply StepsF.consK 1
      · exact (StepsF.reg (by decide) (by decide) (fun G ic hsz => famJB_56 G _ ic (by decide) hsz))
      exact StepsF.refl _ _ _ _ _
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((((56)) + (UInt8.toUInt32 8))) (A H (schedule blk) 63) (r0.edx) (r0.ebx) (V.sp) (r0.ebp) (r0.esi) (A H (schedule blk) 64)) (Steps.rmw' (fun r => (UInt32.add r.esp (UInt8.toUInt32 48))) (fun r v => (v + r.edi)) 12 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_017c24dd 0x101105 48 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((((56)) + (UInt8.toUInt32 8))) (A H (schedule blk) 63) (r0.edx) (r0.ebx) (V.sp) (r0.ebp) (r0.esi) (A H (schedule blk) 64)) (Steps.rmw' (fun r => (UInt32.add r.esp (UInt8.toUInt32 44))) (fun r v => (v + r.ecx)) 11 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_014c24dd 0x101109 44 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[2]!)) (A H (schedule blk) 63) (r0.edx) (r0.ebx) (V.sp) (r0.ebp) (r0.esi) (A H (schedule blk) 64)) (Steps.load' (fun r v => { r with eax := v }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 40))) 10 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_8b4424dd 0x10110d 40 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((((H[2]!)) + (A H (schedule blk) 62))) (A H (schedule blk) 63) (r0.edx) (r0.ebx) (V.sp) (r0.ebp) (r0.esi) (A H (schedule blk) 64)) (Steps.load' (fun r v => { r with eax := (r.eax + v) }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 16))) 4 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_034424dd 0x101111 16 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((((H[2]!)) + (A H (schedule blk) 62))) (A H (schedule blk) 63) (r0.edx) (r0.ebx) (V.sp) (r0.ebp) (r0.esi) (A H (schedule blk) 64)) (Steps.store' (fun r => r) (fun r => (UInt32.add r.esp (UInt8.toUInt32 40))) (fun r => r.eax) 10 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_894424dd 0x101115 40 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[3]!)) (A H (schedule blk) 63) (r0.edx) (r0.ebx) (V.sp) (r0.ebp) (r0.esi) (A H (schedule blk) 64)) (Steps.load' (fun r v => { r with eax := v }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 56))) 14 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_8b4424dd 0x101119 56 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((((H[3]!)) + (A H (schedule blk) 61))) (A H (schedule blk) 63) (r0.edx) (r0.ebx) (V.sp) (r0.ebp) (r0.esi) (A H (schedule blk) 64)) (Steps.load' (fun r v => { r with eax := (r.eax + v) }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 24))) 6 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_034424dd 0x10111d 24 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((((H[3]!)) + (A H (schedule blk) 61))) (A H (schedule blk) 63) (r0.edx) (r0.ebx) (V.sp) (r0.ebp) (r0.esi) (A H (schedule blk) 64)) (Steps.store' (fun r => r) (fun r => (UInt32.add r.esp (UInt8.toUInt32 56))) (fun r => r.eax) 14 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_894424dd 0x101121 56 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((((H[3]!)) + (A H (schedule blk) 61))) ((H[4]!)) (r0.edx) (r0.ebx) (V.sp) (r0.ebp) (r0.esi) (A H (schedule blk) 64)) (Steps.load' (fun r v => { r with ecx := v }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 64))) 16 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_8b4c24dd 0x101125 64 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((((H[3]!)) + (A H (schedule blk) 61))) ((((H[4]!)) + (E H (schedule blk) 64))) (r0.edx) (r0.ebx) (V.sp) (r0.ebp) (r0.esi) (A H (schedule blk) 64)) (Steps.load' (fun r v => { r with ecx := (r.ecx + v) }) (fun r => r.esp) 0 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_030c24 0x101129 G _ fl ic (by decide) hsz hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((((H[3]!)) + (A H (schedule blk) 61))) ((((H[4]!)) + (E H (schedule blk) 64))) (r0.edx) (r0.ebx) (V.sp) ((H[5]!)) (r0.esi) (A H (schedule blk) 64)) (Steps.load' (fun r v => { r with ebp := v }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 52))) 13 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_8b6c24dd 0x10112c 52 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((((H[3]!)) + (A H (schedule blk) 61))) ((((H[4]!)) + (E H (schedule blk) 64))) (r0.edx) (r0.ebx) (V.sp) ((((H[5]!)) + (E H (schedule blk) 63))) (r0.esi) (A H (schedule blk) 64)) (Steps.load' (fun r v => { r with ebp := (r.ebp + v) }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 20))) 5 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_036c24dd 0x101130 20 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[6]!)) ((((H[4]!)) + (E H (schedule blk) 64))) (r0.edx) (r0.ebx) (V.sp) ((((H[5]!)) + (E H (schedule blk) 63))) (r0.esi) (A H (schedule blk) 64)) (Steps.load' (fun r v => { r with eax := v }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 60))) 15 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_8b4424dd 0x101134 60 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((((H[6]!)) + (E H (schedule blk) 62))) ((((H[4]!)) + (E H (schedule blk) 64))) (r0.edx) (r0.ebx) (V.sp) ((((H[5]!)) + (E H (schedule blk) 63))) (r0.esi) (A H (schedule blk) 64)) (Steps.load' (fun r v => { r with eax := (r.eax + v) }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 4))) 1 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_034424dd 0x101138 4 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((((H[6]!)) + (E H (schedule blk) 62))) ((((H[4]!)) + (E H (schedule blk) 64))) (r0.edx) (r0.ebx) (V.sp) ((((H[5]!)) + (E H (schedule blk) 63))) (r0.esi) (A H (schedule blk) 64)) (Steps.store' (fun r => r) (fun r => (UInt32.add r.esp (UInt8.toUInt32 60))) (fun r => r.eax) 15 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_894424dd 0x10113c 60 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((((H[6]!)) + (E H (schedule blk) 62))) ((((H[4]!)) + (E H (schedule blk) 64))) (r0.edx) (r0.ebx) (V.sp) ((((H[5]!)) + (E H (schedule blk) 63))) (r0.esi) ((H[7]!))) (Steps.load' (fun r v => { r with edi := v }) (fun r => (UInt32.add r.esp 156)) 39 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_8bbc249c000000 0x101140 G _ fl ic (by decide) hsz hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((((H[6]!)) + (E H (schedule blk) 62))) ((((H[4]!)) + (E H (schedule blk) 64))) (r0.edx) (r0.ebx) (V.sp) ((((H[5]!)) + (E H (schedule blk) 63))) (r0.esi) ((((H[7]!)) + (E H (schedule blk) 61)))) (Steps.load' (fun r v => { r with edi := (r.edi + v) }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 12))) 3 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_037c24dd 0x101147 12 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((((H[6]!)) + (E H (schedule blk) 62))) ((((H[4]!)) + (E H (schedule blk) 64))) ((V.blk)) (r0.ebx) (V.sp) ((((H[5]!)) + (E H (schedule blk) 63))) (r0.esi) ((((H[7]!)) + (E H (schedule blk) 61)))) (Steps.load' (fun r v => { r with edx := v }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 32))) 8 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_8b5424dd 0x10114b 32 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((((H[6]!)) + (E H (schedule blk) 62))) ((((H[4]!)) + (E H (schedule blk) 64))) ((((V.blk)) + (64 : UInt32))) (r0.ebx) (V.sp) ((((H[5]!)) + (E H (schedule blk) 63))) (r0.esi) ((((H[7]!)) + (E H (schedule blk) 61)))) (Steps.reg (by decide) (by decide) (fun G fl ic hsz => ⟨_, fam_83c240 0x10114f G _ fl ic (by decide) hsz⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((((H[6]!)) + (E H (schedule blk) 62))) ((((H[4]!)) + (E H (schedule blk) 64))) ((((V.blk)) + (64 : UInt32))) (r0.ebx) (V.sp) ((((H[5]!)) + (E H (schedule blk) 63))) ((cnt)) ((((H[7]!)) + (E H (schedule blk) 61)))) (Steps.load' (fun r v => { r with esi := v }) (fun r => (UInt32.add r.esp 160)) 40 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_8bb424a0000000 0x101152 G _ fl ic (by decide) hsz hr⟩)) rfl)
    exact Steps.refl _ _ _ _
  · exact R.ext' (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  · exact ⟨(by (simp only [upd, updL, ↓reduceIte, Nat.reduceEqDiff]) <;> first | rfl | ac_rfl), (by (simp only [upd, updL, ↓reduceIte, Nat.reduceEqDiff]) <;> first | rfl | ac_rfl), (by (simp only [upd, updL, ↓reduceIte, Nat.reduceEqDiff]) <;> first | rfl | ac_rfl), (by (simp only [upd, updL, ↓reduceIte, Nat.reduceEqDiff]) <;> first | rfl | ac_rfl), (by (simp only [upd, updL, ↓reduceIte, Nat.reduceEqDiff]) <;> first | rfl | ac_rfl), (by (simp only [upd, updL, ↓reduceIte, Nat.reduceEqDiff]) <;> first | rfl | ac_rfl), (by (simp only [upd, updL, ↓reduceIte, Nat.reduceEqDiff]) <;> first | rfl | ac_rfl), (by (simp only [upd, updL, ↓reduceIte, Nat.reduceEqDiff]) <;> first | rfl | ac_rfl), (by (simp only [upd, updL, ↓reduceIte, Nat.reduceEqDiff]) <;> first | rfl | ac_rfl), (by (simp only [upd, updL, ↓reduceIte, Nat.reduceEqDiff]) <;> first | rfl | ac_rfl), (by (simp only [upd, updL, ↓reduceIte, Nat.reduceEqDiff]) <;> first | rfl | ac_rfl), trivial⟩

theorem segn_next (V : Env) (h0 h1 h2 h3 h4 h5 h6 h7 d c sv0 sv1 sv2 sv3 ra : UInt32) (hc : c.toNat ≠ 1) :
    Seg V 17 0x101159
      (fun r => { r with esp := V.sp, ecx := h4, edx := d, ebp := h5, esi := c, edi := h7 })
      (fun F => updL F ([(10, h2), (11, h1), (12, h0), (14, h3), (15, h6), (38, V.ctx), (42, sv3), (43, sv2), (44, sv1), (45, sv0), (46, ra)] : List (Nat × UInt32)))
      0x100390
      (fun r => { r with esp := V.sp, ecx := h4, edx := d, ebx := h6, esi := c - 1, edi := h7 })
      (fun F => updL F ([(10, h2), (11, h1), (12, h0), (13, h5), (14, h3), (38, V.ctx), (42, sv3), (43, sv2), (44, sv1), (45, sv0), (46, ra)] : List (Nat × UInt32))) := by
  apply Seg.ofL
  intro r0 F0
  apply Exists.intro
  apply Exists.intro
  refine ⟨?_, ?_, ?_⟩
  · apply Steps.consK 17
    · apply Steps.ofF; intro fl0; apply Exists.intro
      apply StepsF.consK 1
      · exact (StepsF.reg (by decide) (by decide) (fun G ic hsz => famDEC 0x101159 G _ fl0 ic (by decide) hsz))
      apply StepsF.consK 1
      · exact (StepsF.load' (fun r v => { r with eax := v }) (fun r => (UInt32.add r.esp 152)) 38 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8b842498000000 0x10115a G _ _ ic (by decide) hsz hr)))
      apply StepsF.consK 1
      · exact (StepsF.load' (fun r v => { r with ebx := v }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 48))) 12 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8b5c24dd 0x101161 48 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.store' (fun r => r) (fun r => r.eax) (fun r => r.ebx) 48 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8918 0x101165 G _ _ ic (by decide) hsz hr)))
      apply StepsF.consK 1
      · exact (StepsF.load' (fun r v => { r with ebx := v }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 44))) 11 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8b5c24dd 0x101167 44 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.store' (fun r => r) (fun r => (UInt32.add r.eax (UInt8.toUInt32 4))) (fun r => r.ebx) 49 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8958dd 0x10116b 4 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.load' (fun r v => { r with ebx := v }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 40))) 10 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8b5c24dd 0x10116e 40 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.store' (fun r => r) (fun r => (UInt32.add r.eax (UInt8.toUInt32 8))) (fun r => r.ebx) 50 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8958dd 0x101172 8 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.load' (fun r v => { r with ebx := v }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 56))) 14 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8b5c24dd 0x101175 56 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.store' (fun r => r) (fun r => (UInt32.add r.eax (UInt8.toUInt32 12))) (fun r => r.ebx) 51 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8958dd 0x101179 12 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.store' (fun r => r) (fun r => (UInt32.add r.eax (UInt8.toUInt32 16))) (fun r => r.ecx) 52 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8948dd 0x10117c 16 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.store' (fun r => r) (fun r => (UInt32.add r.esp (UInt8.toUInt32 52))) (fun r => r.ebp) 13 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_896c24dd 0x10117f 52 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.store' (fun r => r) (fun r => (UInt32.add r.eax (UInt8.toUInt32 20))) (fun r => r.ebp) 53 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8968dd 0x101183 20 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.load' (fun r v => { r with ebx := v }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 60))) 15 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8b5c24dd 0x101186 60 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.store' (fun r => r) (fun r => (UInt32.add r.eax (UInt8.toUInt32 24))) (fun r => r.ebx) 54 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8958dd 0x10118a 24 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.store' (fun r => r) (fun r => (UInt32.add r.eax (UInt8.toUInt32 28))) (fun r => r.edi) 55 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8978dd 0x10118d 28 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.reg (by decide) (by decide) (fun G ic hsz => famJNE_T G _ _ _ ic hc (by decide) hsz))
      exact StepsF.refl _ _ _ _ _
    exact Steps.refl _ _ _ _
  · exact R.ext' (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  · exact ⟨(by rfl), (by rfl), (by rfl), (by rfl), (by rfl), (by rfl), (by rfl), (by rfl), (by rfl), (by rfl), (by rfl), trivial⟩

theorem segn_ret (V : Env) (h0 h1 h2 h3 h4 h5 h6 h7 d c sv0 sv1 sv2 sv3 ra : UInt32) :
    Seg V 23 0x101159
      (fun r => { r with esp := V.sp, ecx := h4, edx := d, ebp := h5, esi := 1, edi := h7 })
      (fun F => updL F ([(10, h2), (11, h1), (12, h0), (14, h3), (15, h6), (38, V.ctx), (42, sv3), (43, sv2), (44, sv1), (45, sv0), (46, ra)] : List (Nat × UInt32)))
      ra
      (fun r => { r with esp := V.sp + 188, ebp := sv0, ebx := sv1, edi := sv2, esi := sv3 })
      (fun F => updL F ([(48, h0), (49, h1), (50, h2), (51, h3), (52, h4), (53, h5), (54, h6), (55, h7)] : List (Nat × UInt32))) := by
  apply Seg.ofL
  intro r0 F0
  apply Exists.intro
  apply Exists.intro
  refine ⟨?_, ?_, ?_⟩
  · apply Steps.consK 17
    · apply Steps.ofF; intro fl0; apply Exists.intro
      apply StepsF.consK 1
      · exact (StepsF.reg (by decide) (by decide) (fun G ic hsz => famDEC 0x101159 G _ fl0 ic (by decide) hsz))
      apply StepsF.consK 1
      · exact (StepsF.load' (fun r v => { r with eax := v }) (fun r => (UInt32.add r.esp 152)) 38 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8b842498000000 0x10115a G _ _ ic (by decide) hsz hr)))
      apply StepsF.consK 1
      · exact (StepsF.load' (fun r v => { r with ebx := v }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 48))) 12 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8b5c24dd 0x101161 48 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.store' (fun r => r) (fun r => r.eax) (fun r => r.ebx) 48 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8918 0x101165 G _ _ ic (by decide) hsz hr)))
      apply StepsF.consK 1
      · exact (StepsF.load' (fun r v => { r with ebx := v }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 44))) 11 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8b5c24dd 0x101167 44 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.store' (fun r => r) (fun r => (UInt32.add r.eax (UInt8.toUInt32 4))) (fun r => r.ebx) 49 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8958dd 0x10116b 4 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.load' (fun r v => { r with ebx := v }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 40))) 10 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8b5c24dd 0x10116e 40 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.store' (fun r => r) (fun r => (UInt32.add r.eax (UInt8.toUInt32 8))) (fun r => r.ebx) 50 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8958dd 0x101172 8 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.load' (fun r v => { r with ebx := v }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 56))) 14 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8b5c24dd 0x101175 56 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.store' (fun r => r) (fun r => (UInt32.add r.eax (UInt8.toUInt32 12))) (fun r => r.ebx) 51 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8958dd 0x101179 12 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.store' (fun r => r) (fun r => (UInt32.add r.eax (UInt8.toUInt32 16))) (fun r => r.ecx) 52 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8948dd 0x10117c 16 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.store' (fun r => r) (fun r => (UInt32.add r.esp (UInt8.toUInt32 52))) (fun r => r.ebp) 13 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_896c24dd 0x10117f 52 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.store' (fun r => r) (fun r => (UInt32.add r.eax (UInt8.toUInt32 20))) (fun r => r.ebp) 53 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8968dd 0x101183 20 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.load' (fun r v => { r with ebx := v }) (fun r => (UInt32.add r.esp (UInt8.toUInt32 60))) 15 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8b5c24dd 0x101186 60 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.store' (fun r => r) (fun r => (UInt32.add r.eax (UInt8.toUInt32 24))) (fun r => r.ebx) 54 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8958dd 0x10118a 24 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.store' (fun r => r) (fun r => (UInt32.add r.eax (UInt8.toUInt32 28))) (fun r => r.edi) 55 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
                (fun G ic hsz hr => (fam_8978dd 0x10118d 28 G _ _ ic (by decide) hsz (by decide) hr)))
      apply StepsF.consK 1
      · exact (StepsF.reg (by decide) (by decide) (fun G ic hsz => famJNE G _ _ ic (by decide) hsz))
      exact StepsF.refl _ _ _ _ _
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk (V.ctx) (h4) (d) (h6) (V.sp + (168 : UInt32)) (h5) ((1 : UInt32) - (1 : UInt32)) (h7)) (Steps.reg (by decide) (by decide) (fun G fl ic hsz => ⟨_, fam_81c4a8000000 0x101196 G _ fl ic (by decide) hsz⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk (V.ctx) (h4) (d) (h6) (V.sp + (172 : UInt32)) (h5) (sv3) (h7)) (Steps.congrEsp (Steps.load' (fun r v => { r with esi := v, esp := r.esp + 4 }) (fun r => r.esp) 42 (by decide) (by rfl) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, famPOP_esi 0x10119c G _ fl ic (by decide) hsz hr⟩)) (V.sp + 172) (by exact add_norm V.sp 168 4 172 (by decide))) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk (V.ctx) (h4) (d) (h6) (V.sp + (176 : UInt32)) (h5) (sv3) (sv2)) (Steps.congrEsp (Steps.load' (fun r v => { r with edi := v, esp := r.esp + 4 }) (fun r => r.esp) 43 (by decide) (by rfl) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, famPOP_edi 0x10119d G _ fl ic (by decide) hsz hr⟩)) (V.sp + 176) (by exact add_norm V.sp 172 4 176 (by decide))) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk (V.ctx) (h4) (d) (sv1) (V.sp + (180 : UInt32)) (h5) (sv3) (sv2)) (Steps.congrEsp (Steps.load' (fun r v => { r with ebx := v, esp := r.esp + 4 }) (fun r => r.esp) 44 (by decide) (by rfl) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, famPOP_ebx 0x10119e G _ fl ic (by decide) hsz hr⟩)) (V.sp + 180) (by exact add_norm V.sp 176 4 180 (by decide))) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk (V.ctx) (h4) (d) (sv1) (V.sp + (184 : UInt32)) (sv0) (sv3) (sv2)) (Steps.congrEsp (Steps.load' (fun r v => { r with ebp := v, esp := r.esp + 4 }) (fun r => r.esp) 45 (by decide) (by rfl) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, famPOP_ebp 0x10119f G _ fl ic (by decide) hsz hr⟩)) (V.sp + 184) (by exact add_norm V.sp 180 4 184 (by decide))) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk (V.ctx) (h4) (d) (sv1) (V.sp + (188 : UInt32)) (sv0) (sv3) (sv2)) (Steps.congrEsp (Steps.ret (fun r => { r with esp := r.esp + 4 }) (fun r => r.esp) 46 (by decide) (by rfl) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, famRET 0x1011a0 G _ fl ic (by decide) hsz hr⟩)) (V.sp + 188) (by exact add_norm V.sp 184 4 188 (by decide))) rfl)
    exact Steps.refl _ _ _ _
  · exact R.ext' (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  · exact ⟨(by rfl), (by rfl), (by rfl), (by rfl), (by rfl), (by rfl), (by rfl), (by rfl), trivial⟩

end Solutions.OpensslSha256
