import Solutions.OpensslSha256.Chain
import Solutions.OpensslSha256.Alg
import Solutions.OpensslSha256.Fam.F00
import Solutions.OpensslSha256.Fam.F03
import Solutions.OpensslSha256.Fam.FX
/-! The prologue of the block function `sha256_block_data_order` from its entry, for any block count
`cnt` (the stack argument) and return address `ra` (generated from `Seg/SPro`). -/
namespace Solutions.OpensslSha256
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.Spec.Sha256
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem segn_pro (V : Env) (H : Array UInt32) (sv0 sv1 sv2 sv3 cnt ra : UInt32) :
    Seg V 32 0x100340
      (fun r => { r with esp := V.sp + 184, ecx := V.ctx, edx := V.blk, ebp := sv0, ebx := sv1, edi := sv2, esi := sv3 })
      (fun F => updL F ([(46, ra), (47, cnt), (48, H[0]!), (49, H[1]!), (50, H[2]!), (51, H[3]!), (52, H[4]!), (53, H[5]!), (54, H[6]!), (55, H[7]!)] : List (Nat × UInt32)))
      0x100390
      (fun r => { r with esp := V.sp, ecx := H[4]!, edx := V.blk, ebx := H[6]!, esi := cnt, edi := H[7]! })
      (fun F => updL F ([(10, H[2]!), (11, H[1]!), (12, H[0]!), (13, H[5]!), (14, H[3]!), (38, V.ctx), (42, sv3), (43, sv2), (44, sv1), (45, sv0), (46, ra)] : List (Nat × UInt32))) := by
  apply Seg.ofL
  intro r0 F0
  apply Exists.intro
  apply Exists.intro
  refine ⟨?_, ?_, ?_⟩
  · apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk (r0.eax) (V.ctx) (V.blk) (sv1) (V.sp + (180 : UInt32)) (sv0) (sv3) (sv2)) (Steps.congrEsp (Steps.store' (fun r => { r with esp := r.esp - 4 }) (fun r => r.esp - 4) (fun r => r.ebp) 45 (by decide)
              (by exact (sub_norm V.sp 184 4 180 (by decide)).trans rfl) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, famPUSH_ebp 0x100340 G _ fl ic (by decide) hsz hr⟩)) (V.sp + 180) (by exact sub_norm V.sp 184 4 180 (by decide))) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk (r0.eax) (V.ctx) (V.blk) (sv1) (V.sp + (176 : UInt32)) (sv0) (sv3) (sv2)) (Steps.congrEsp (Steps.store' (fun r => { r with esp := r.esp - 4 }) (fun r => r.esp - 4) (fun r => r.ebx) 44 (by decide)
              (by exact (sub_norm V.sp 180 4 176 (by decide)).trans rfl) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, famPUSH_ebx 0x100341 G _ fl ic (by decide) hsz hr⟩)) (V.sp + 176) (by exact sub_norm V.sp 180 4 176 (by decide))) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk (r0.eax) (V.ctx) (V.blk) (sv1) (V.sp + (172 : UInt32)) (sv0) (sv3) (sv2)) (Steps.congrEsp (Steps.store' (fun r => { r with esp := r.esp - 4 }) (fun r => r.esp - 4) (fun r => r.edi) 43 (by decide)
              (by exact (sub_norm V.sp 176 4 172 (by decide)).trans rfl) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, famPUSH_edi 0x100342 G _ fl ic (by decide) hsz hr⟩)) (V.sp + 172) (by exact sub_norm V.sp 176 4 172 (by decide))) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk (r0.eax) (V.ctx) (V.blk) (sv1) (V.sp + (168 : UInt32)) (sv0) (sv3) (sv2)) (Steps.congrEsp (Steps.store' (fun r => { r with esp := r.esp - 4 }) (fun r => r.esp - 4) (fun r => r.esi) 42 (by decide)
              (by exact (sub_norm V.sp 172 4 168 (by decide)).trans rfl) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, famPUSH_esi 0x100343 G _ fl ic (by decide) hsz hr⟩)) (V.sp + 168) (by exact sub_norm V.sp 172 4 168 (by decide))) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk (r0.eax) (V.ctx) (V.blk) (sv1) (V.sp) (sv0) (sv3) (sv2)) (Steps.congrEsp (Steps.reg (by decide) (by decide) (fun G fl ic hsz => ⟨_, fam_81eca8000000 0x100344 G _ fl ic (by decide) hsz⟩)) V.sp (by exact (sub_norm V.sp 168 168 0 (by decide)).trans (UInt32.add_zero _))) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk (r0.eax) (V.ctx) (V.blk) (sv1) (V.sp) (sv0) ((cnt)) (sv2)) (Steps.load' (fun r v => { r with esi := v }) (fun r => (UInt32.add r.esp 188)) 47 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_8bb424bc000000 0x10034a G _ fl ic (by decide) hsz hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[0]!)) (V.ctx) (V.blk) (sv1) (V.sp) (sv0) ((cnt)) (sv2)) (Steps.load' (fun r v => { r with eax := v }) (fun r => r.ecx) 48 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_8b01 0x100351 G _ fl ic (by decide) hsz hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[0]!)) (V.ctx) (V.blk) (sv1) (V.sp) (sv0) ((cnt)) (sv2)) (Steps.store' (fun r => r) (fun r => (UInt32.add r.esp (UInt8.toUInt32 48))) (fun r => r.eax) 12 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_894424dd 0x100353 48 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[1]!)) (V.ctx) (V.blk) (sv1) (V.sp) (sv0) ((cnt)) (sv2)) (Steps.load' (fun r v => { r with eax := v }) (fun r => (UInt32.add r.ecx (UInt8.toUInt32 4))) 49 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_8b41dd 0x100357 4 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[1]!)) (V.ctx) (V.blk) (sv1) (V.sp) (sv0) ((cnt)) (sv2)) (Steps.store' (fun r => r) (fun r => (UInt32.add r.esp (UInt8.toUInt32 44))) (fun r => r.eax) 11 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_894424dd 0x10035a 44 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[2]!)) (V.ctx) (V.blk) (sv1) (V.sp) (sv0) ((cnt)) (sv2)) (Steps.load' (fun r v => { r with eax := v }) (fun r => (UInt32.add r.ecx (UInt8.toUInt32 8))) 50 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_8b41dd 0x10035e 8 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[2]!)) (V.ctx) (V.blk) (sv1) (V.sp) (sv0) ((cnt)) (sv2)) (Steps.store' (fun r => r) (fun r => (UInt32.add r.esp (UInt8.toUInt32 40))) (fun r => r.eax) 10 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_894424dd 0x100361 40 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[3]!)) (V.ctx) (V.blk) (sv1) (V.sp) (sv0) ((cnt)) (sv2)) (Steps.load' (fun r v => { r with eax := v }) (fun r => (UInt32.add r.ecx (UInt8.toUInt32 12))) 51 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_8b41dd 0x100365 12 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[3]!)) (V.ctx) (V.blk) (sv1) (V.sp) (sv0) ((cnt)) (sv2)) (Steps.store' (fun r => r) (fun r => (UInt32.add r.esp (UInt8.toUInt32 56))) (fun r => r.eax) 14 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_894424dd 0x100368 56 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[4]!)) (V.ctx) (V.blk) (sv1) (V.sp) (sv0) ((cnt)) (sv2)) (Steps.load' (fun r v => { r with eax := v }) (fun r => (UInt32.add r.ecx (UInt8.toUInt32 16))) 52 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_8b41dd 0x10036c 16 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[4]!)) (V.ctx) (V.blk) (sv1) (V.sp) (sv0) ((cnt)) ((H[5]!))) (Steps.load' (fun r v => { r with edi := v }) (fun r => (UInt32.add r.ecx (UInt8.toUInt32 20))) 53 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_8b79dd 0x10036f 20 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[4]!)) (V.ctx) (V.blk) (sv1) (V.sp) (sv0) ((cnt)) ((H[5]!))) (Steps.store' (fun r => r) (fun r => (UInt32.add r.esp (UInt8.toUInt32 52))) (fun r => r.edi) 13 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_897c24dd 0x100372 52 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[4]!)) (V.ctx) (V.blk) ((H[6]!)) (V.sp) (sv0) ((cnt)) ((H[5]!))) (Steps.load' (fun r v => { r with ebx := v }) (fun r => (UInt32.add r.ecx (UInt8.toUInt32 24))) 54 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_8b59dd 0x100376 24 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[4]!)) (V.ctx) (V.blk) ((H[6]!)) (V.sp) (sv0) ((cnt)) ((H[5]!))) (Steps.store' (fun r => r) (fun r => (UInt32.add r.esp 152)) (fun r => r.ecx) 38 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_898c2498000000 0x100379 G _ fl ic (by decide) hsz hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[4]!)) (V.ctx) (V.blk) ((H[6]!)) (V.sp) (sv0) ((cnt)) ((H[7]!))) (Steps.load' (fun r v => { r with edi := v }) (fun r => (UInt32.add r.ecx (UInt8.toUInt32 28))) 55 (by decide) (by first | rfl | exact (UInt32.add_zero _).symm | (rw [uadd_assoc]; rfl)) (by decide) (by decide)
              (fun G fl ic hsz hr => ⟨_, fam_8b79dd 0x100380 28 G _ fl ic (by decide) hsz (by decide) hr⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[4]!)) (((H[4]!))) (V.blk) ((H[6]!)) (V.sp) (sv0) ((cnt)) ((H[7]!))) (Steps.reg (by decide) (by decide) (fun G fl ic hsz => ⟨_, fam_89c1 0x100383 G _ fl ic (by decide) hsz⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[4]!)) (((H[4]!))) (V.blk) ((H[6]!)) (V.sp) (sv0) ((cnt)) ((H[7]!))) (Steps.reg (by decide) (by decide) (fun G fl ic hsz => ⟨_, fam_90 0x100385 G _ fl ic (by decide) hsz⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[4]!)) (((H[4]!))) (V.blk) ((H[6]!)) (V.sp) (sv0) ((cnt)) ((H[7]!))) (Steps.reg (by decide) (by decide) (fun G fl ic hsz => ⟨_, fam_90 0x100386 G _ fl ic (by decide) hsz⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[4]!)) (((H[4]!))) (V.blk) ((H[6]!)) (V.sp) (sv0) ((cnt)) ((H[7]!))) (Steps.reg (by decide) (by decide) (fun G fl ic hsz => ⟨_, fam_90 0x100387 G _ fl ic (by decide) hsz⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[4]!)) (((H[4]!))) (V.blk) ((H[6]!)) (V.sp) (sv0) ((cnt)) ((H[7]!))) (Steps.reg (by decide) (by decide) (fun G fl ic hsz => ⟨_, fam_90 0x100388 G _ fl ic (by decide) hsz⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[4]!)) (((H[4]!))) (V.blk) ((H[6]!)) (V.sp) (sv0) ((cnt)) ((H[7]!))) (Steps.reg (by decide) (by decide) (fun G fl ic hsz => ⟨_, fam_90 0x100389 G _ fl ic (by decide) hsz⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[4]!)) (((H[4]!))) (V.blk) ((H[6]!)) (V.sp) (sv0) ((cnt)) ((H[7]!))) (Steps.reg (by decide) (by decide) (fun G fl ic hsz => ⟨_, fam_90 0x10038a G _ fl ic (by decide) hsz⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[4]!)) (((H[4]!))) (V.blk) ((H[6]!)) (V.sp) (sv0) ((cnt)) ((H[7]!))) (Steps.reg (by decide) (by decide) (fun G fl ic hsz => ⟨_, fam_90 0x10038b G _ fl ic (by decide) hsz⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[4]!)) (((H[4]!))) (V.blk) ((H[6]!)) (V.sp) (sv0) ((cnt)) ((H[7]!))) (Steps.reg (by decide) (by decide) (fun G fl ic hsz => ⟨_, fam_90 0x10038c G _ fl ic (by decide) hsz⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[4]!)) (((H[4]!))) (V.blk) ((H[6]!)) (V.sp) (sv0) ((cnt)) ((H[7]!))) (Steps.reg (by decide) (by decide) (fun G fl ic hsz => ⟨_, fam_90 0x10038d G _ fl ic (by decide) hsz⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[4]!)) (((H[4]!))) (V.blk) ((H[6]!)) (V.sp) (sv0) ((cnt)) ((H[7]!))) (Steps.reg (by decide) (by decide) (fun G fl ic hsz => ⟨_, fam_90 0x10038e G _ fl ic (by decide) hsz⟩)) rfl)
    apply Steps.consK 1
    · exact (Steps.congrR (r'' := R.mk ((H[4]!)) (((H[4]!))) (V.blk) ((H[6]!)) (V.sp) (sv0) ((cnt)) ((H[7]!))) (Steps.reg (by decide) (by decide) (fun G fl ic hsz => ⟨_, fam_90 0x10038f G _ fl ic (by decide) hsz⟩)) rfl)
    exact Steps.refl _ _ _ _
  · exact R.ext' (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  · exact ⟨(by rfl), (by rfl), (by rfl), (by rfl), (by rfl), (by rfl), (by rfl), (by rfl), (by rfl), (by rfl), (by rfl), trivial⟩

end Solutions.OpensslSha256
