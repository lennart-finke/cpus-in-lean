import Solutions.OpensslSha256.BlockBody
import Solutions.OpensslSha256.SegN.SPro
import Solutions.OpensslSha256.Transform
/-!
# `sha256_block_data_order` over any number of blocks

The block function compresses `n ≥ 1` consecutive 64-byte blocks at `V.blk`. One block (`block_body`)
is run in the environment of that block (`envAt`); runs only depend on the memory, the stack pointer
and the context of an environment (`Steps.env`), so all blocks are composed in the environment `V`
of the first. The loop (`bdo_loop`) is by induction on the number of blocks left; `bdo_seg` adds the
prologue: from the entry of the function (the return address `ra` and the count in slots 46, 47)
to the return, with the context slots holding the hash words compressed over the blocks.
-/
namespace Solutions.OpensslSha256
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.Spec.Sha256

theorem Inv.env {E E' : Env} (h1 : E'.M0 = E.M0) (h2 : E'.sp = E.sp) (h3 : E'.ctx = E.ctx) {M : ByteArray}
    {F : Nat → UInt32} (h : Inv E M F) : Inv E' M F := by
  have hs : InSlots E' = InSlots E := by funext a; unfold InSlots; rw [h2, h3]
  have ha : slotAddr E' = slotAddr E := by funext j; unfold slotAddr; rw [h2, h3]
  refine ⟨by rw [h1]; exact h.size, fun a ha' hn => ?_, fun j hj => by rw [ha]; exact h.slot j hj⟩
  rw [h1] at ha' ⊢; rw [hs] at hn; exact h.out a ha' hn

theorem Steps.env {E E' : Env} (h1 : E'.M0 = E.M0) (h2 : E'.sp = E.sp) (h3 : E'.ctx = E.ctx) {n : Nat}
    {p p' : UInt32} {r r' : R} {F F' : Nat → UInt32} (h : Steps E n p r F p' r' F') : Steps E' n p r F p' r' F' := by
  intro M fl ic hI hic
  obtain ⟨M', fl', hr, hI'⟩ := h M fl ic (hI.env h1.symm h2.symm h3.symm) hic
  exact ⟨M', fl', hr, hI'.env h1 h2 h3⟩

theorem Seg.env {E E' : Env} (h1 : E'.M0 = E.M0) (h2 : E'.sp = E.sp) (h3 : E'.ctx = E.ctx) {n : Nat}
    {p p' : UInt32} {Pr Qr : R → R} {Pf Qf : (Nat → UInt32) → Nat → UInt32} (h : Seg E n p Pr Pf p' Qr Qf) :
    Seg E' n p Pr Pf p' Qr Qf := fun r0 F0 =>
  let ⟨r1, F1, hs⟩ := h r0 F0
  ⟨r1, F1, hs.env h1 h2 h3⟩

theorem Seg.congrN {E : Env} {n n' : Nat} {p p' : UInt32} {Pr Qr : R → R} {Pf Qf : (Nat → UInt32) → Nat → UInt32}
    (h : Seg E n p Pr Pf p' Qr Qf) (e : n = n') : Seg E n' p Pr Pf p' Qr Qf := e ▸ h

/-! ## The blocks -/

/-- `n` blocks at `V.blk`: inside memory, apart from the image, the frame and the context words. -/
structure DataOk (V : Env) (n : Nat) : Prop where
  fit : V.blk.toNat + 64 * n ≤ V.M0.size
  img : V.blk.toNat + 64 * n ≤ imgBase ∨ imgBase + imgSize ≤ V.blk.toNat
  sp : V.blk.toNat + 64 * n ≤ V.sp.toNat ∨ V.sp.toNat + 204 ≤ V.blk.toNat
  ctx : V.blk.toNat + 64 * n ≤ V.ctx.toNat ∨ V.ctx.toNat + 32 ≤ V.blk.toNat

/-- The address of block `i`. -/
def bAddr (d : UInt32) (i : Nat) : UInt32 := d + (64 * i).toUInt32

/-- The bytes of block `i`. -/
def blkAt (M : ByteArray) (d : UInt32) (i : Nat) : List UInt8 := memBytes M (bAddr d i) 64

/-- The `k` blocks from block `i`. -/
def blks (M : ByteArray) (d : UInt32) : Nat → Nat → List (List UInt8)
  | _, 0 => []
  | i, k + 1 => blkAt M d i :: blks M d (i + 1) k

theorem bAddr_toNat {V : Env} {n : Nat} (hD : DataOk V n) {i : Nat} (hi : i < n) :
    (bAddr V.blk i).toNat = V.blk.toNat + 64 * i := by
  have h1 := hD.fit; have h2 := V.hsz
  unfold bAddr ramTop at *
  rw [UInt32.toNat_add]
  simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (a := 64 * i) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem bAddr_zero (d : UInt32) : bAddr d 0 = d := by
  unfold bAddr; exact UInt32.add_zero d

theorem bAddr_succ (d : UInt32) (i : Nat) : bAddr d (i + 1) = bAddr d i + 64 := by
  unfold bAddr
  rw [UInt32.add_assoc]
  congr 1
  apply UInt32.toNat_inj.1
  simp only [Nat.toUInt32_eq, UInt32.toNat_add, UInt32.toNat_ofNat']
  show (64 * (i + 1)) % 2 ^ 32 = ((64 * i) % 2 ^ 32 + 64 % 2 ^ 32) % 2 ^ 32
  omega

/-- The environment of block `i`. -/
def envAt (V : Env) {n : Nat} (hD : DataOk V n) (i : Nat) (hi : i < n) : Env :=
  { V with
    blk := bAddr V.blk i
    hblk := by rw [bAddr_toNat hD hi]; have := hD.fit; omega
    blk_img := by rw [bAddr_toNat hD hi]; have := hD.img; omega
    blk_sp := by rw [bAddr_toNat hD hi]; have := hD.sp; omega
    blk_ctx := by rw [bAddr_toNat hD hi]; have := hD.ctx; omega }

/-! ## The hash words of a compression -/

theorem compress_0 (H : Array UInt32) (b : List UInt8) : (compress H b)[0]! = H[0]! + A H (schedule b) 64 := rfl
theorem compress_1 (H : Array UInt32) (b : List UInt8) : (compress H b)[1]! = H[1]! + A H (schedule b) 63 := by
  rw [compress_eq, fin8_eq]; show H[1]! + B H (schedule b) 64 = _; rw [B_succ]
theorem compress_2 (H : Array UInt32) (b : List UInt8) : (compress H b)[2]! = H[2]! + A H (schedule b) 62 := by
  rw [compress_eq, fin8_eq]; show H[2]! + C H (schedule b) 64 = _; rw [C_succ, B_succ]
theorem compress_3 (H : Array UInt32) (b : List UInt8) : (compress H b)[3]! = H[3]! + A H (schedule b) 61 := by
  rw [compress_eq, fin8_eq]; show H[3]! + D H (schedule b) 64 = _; rw [D_succ, C_succ, B_succ]
theorem compress_4 (H : Array UInt32) (b : List UInt8) : (compress H b)[4]! = H[4]! + E H (schedule b) 64 := by
  rw [compress_eq, fin8_eq]; rfl
theorem compress_5 (H : Array UInt32) (b : List UInt8) : (compress H b)[5]! = H[5]! + E H (schedule b) 63 := by
  rw [compress_eq, fin8_eq]; show H[5]! + F H (schedule b) 64 = _; rw [F_succ]
theorem compress_6 (H : Array UInt32) (b : List UInt8) : (compress H b)[6]! = H[6]! + E H (schedule b) 62 := by
  rw [compress_eq, fin8_eq]; show H[6]! + G H (schedule b) 64 = _; rw [G_succ, F_succ]
theorem compress_7 (H : Array UInt32) (b : List UInt8) : (compress H b)[7]! = H[7]! + E H (schedule b) 61 := by
  rw [compress_eq, fin8_eq]; show H[7]! + Hh H (schedule b) 64 = _; rw [Hh_succ, G_succ, F_succ]

theorem toUInt32_sub1 (k : Nat) (hk : k + 2 < 2 ^ 32) : (k + 1).toUInt32 = (k + 1 + 1).toUInt32 - 1 := by
  apply UInt32.toNat_inj.1
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']; simp; omega)]
  simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']
  simp
  omega

/-! ## The loop -/

set_option maxRecDepth 100000 in
theorem bdo_loop (V : Env) (n : Nat) (hD : DataOk V n) (hn : n < 2 ^ 26) (sv0 sv1 sv2 sv3 ra : UInt32) :
    ∀ k i (H : Array UInt32), i + k = n → 0 < k →
      Seg V (4029 * k + 6) 0x100390
        (fun r => { r with esp := V.sp, ecx := H[4]!, edx := bAddr V.blk i, ebx := H[6]!, esi := k.toUInt32, edi := H[7]! })
        (fun F => updL F ([(10, H[2]!), (11, H[1]!), (12, H[0]!), (13, H[5]!), (14, H[3]!), (38, V.ctx), (42, sv3), (43, sv2), (44, sv1), (45, sv0), (46, ra)] : List (Nat × UInt32)))
        ra
        (fun r => { r with esp := V.sp + 188, ebp := sv0, ebx := sv1, edi := sv2, esi := sv3 })
        (fun F => updL F ([(48, ((blks V.M0 V.blk i k).foldl compress H)[0]!), (49, ((blks V.M0 V.blk i k).foldl compress H)[1]!),
          (50, ((blks V.M0 V.blk i k).foldl compress H)[2]!), (51, ((blks V.M0 V.blk i k).foldl compress H)[3]!),
          (52, ((blks V.M0 V.blk i k).foldl compress H)[4]!), (53, ((blks V.M0 V.blk i k).foldl compress H)[5]!),
          (54, ((blks V.M0 V.blk i k).foldl compress H)[6]!), (55, ((blks V.M0 V.blk i k).foldl compress H)[7]!)] :
          List (Nat × UInt32))) := by
  intro k
  induction k with
  | zero => intro _ _ _ h; omega
  | succ k ih =>
    intro i H hik _
    have hi : i < n := by omega
    have hb : Seg V 4012 0x100390
        (fun r => { r with esp := V.sp, ecx := H[4]!, edx := bAddr V.blk i, ebx := H[6]!, esi := (k + 1).toUInt32, edi := H[7]! })
        (fun F => updL F ([(10, H[2]!), (11, H[1]!), (12, H[0]!), (13, H[5]!), (14, H[3]!), (38, V.ctx), (42, sv3), (43, sv2), (44, sv1), (45, sv0), (46, ra)] : List (Nat × UInt32)))
        0x101159
        (fun r => { r with esp := V.sp, ecx := H[4]! + E H (schedule (blkAt V.M0 V.blk i)) 64, edx := bAddr V.blk i + 64, ebp := H[5]! + E H (schedule (blkAt V.M0 V.blk i)) 63, esi := (k + 1).toUInt32, edi := H[7]! + E H (schedule (blkAt V.M0 V.blk i)) 61 })
        (fun F => updL F ([(10, H[2]! + A H (schedule (blkAt V.M0 V.blk i)) 62), (11, H[1]! + A H (schedule (blkAt V.M0 V.blk i)) 63),
          (12, H[0]! + A H (schedule (blkAt V.M0 V.blk i)) 64), (14, H[3]! + A H (schedule (blkAt V.M0 V.blk i)) 61),
          (15, H[6]! + E H (schedule (blkAt V.M0 V.blk i)) 62), (38, V.ctx), (42, sv3), (43, sv2), (44, sv1), (45, sv0), (46, ra)] :
          List (Nat × UInt32))) :=
      Seg.env (E := envAt V hD i hi) (E' := V) rfl rfl rfl (block_body (envAt V hD i hi) H (blkAt V.M0 V.blk i) sv0 sv1 sv2 sv3
        (block_words (envAt V hD i hi) _ rfl) (k + 1).toUInt32 ra)
    cases k with
    | zero =>
      have hr := segn_ret V (H[0]! + A H (schedule (blkAt V.M0 V.blk i)) 64) (H[1]! + A H (schedule (blkAt V.M0 V.blk i)) 63)
        (H[2]! + A H (schedule (blkAt V.M0 V.blk i)) 62) (H[3]! + A H (schedule (blkAt V.M0 V.blk i)) 61)
        (H[4]! + E H (schedule (blkAt V.M0 V.blk i)) 64) (H[5]! + E H (schedule (blkAt V.M0 V.blk i)) 63)
        (H[6]! + E H (schedule (blkAt V.M0 V.blk i)) 62) (H[7]! + E H (schedule (blkAt V.M0 V.blk i)) 61)
        (bAddr V.blk i + 64) 1 sv0 sv1 sv2 sv3 ra
      have h := hb.trans hr
      simp only [blks, List.foldl_cons, List.foldl_nil, compress_0, compress_1, compress_2, compress_3, compress_4,
        compress_5, compress_6, compress_7]
      exact h.congrN rfl
    | succ k =>
      have hc : ((k + 1 + 1).toUInt32).toNat ≠ 1 := by
        simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']; rw [Nat.mod_eq_of_lt (by omega)]; omega
      have hx := segn_next V (H[0]! + A H (schedule (blkAt V.M0 V.blk i)) 64) (H[1]! + A H (schedule (blkAt V.M0 V.blk i)) 63)
        (H[2]! + A H (schedule (blkAt V.M0 V.blk i)) 62) (H[3]! + A H (schedule (blkAt V.M0 V.blk i)) 61)
        (H[4]! + E H (schedule (blkAt V.M0 V.blk i)) 64) (H[5]! + E H (schedule (blkAt V.M0 V.blk i)) 63)
        (H[6]! + E H (schedule (blkAt V.M0 V.blk i)) 62) (H[7]! + E H (schedule (blkAt V.M0 V.blk i)) 61)
        (bAddr V.blk i + 64) (k + 1 + 1).toUInt32 sv0 sv1 sv2 sv3 ra hc
      have ih' := ih (i + 1) (compress H (blkAt V.M0 V.blk i)) (by omega) (by omega)
      rw [compress_0, compress_1, compress_2, compress_3, compress_4, compress_5, compress_6, compress_7,
        bAddr_succ, toUInt32_sub1 k (by omega)] at ih'
      exact ((hb.trans hx).trans ih').congrN (by omega)

/-- The block function from its entry: `n` blocks at `V.blk`, the hash words `H` in the context. -/
theorem bdo_seg (V : Env) (n : Nat) (hD : DataOk V n) (hn0 : 0 < n) (hn : n < 2 ^ 26) (H : Array UInt32)
    (sv0 sv1 sv2 sv3 ra : UInt32) :
    Seg V (4029 * n + 38) 0x100340
      (fun r => { r with esp := V.sp + 184, ecx := V.ctx, edx := V.blk, ebp := sv0, ebx := sv1, edi := sv2, esi := sv3 })
      (fun F => updL F ([(46, ra), (47, n.toUInt32), (48, H[0]!), (49, H[1]!), (50, H[2]!), (51, H[3]!), (52, H[4]!), (53, H[5]!), (54, H[6]!), (55, H[7]!)] : List (Nat × UInt32)))
      ra
      (fun r => { r with esp := V.sp + 188, ebp := sv0, ebx := sv1, edi := sv2, esi := sv3 })
      (fun F => updL F ([(48, ((blks V.M0 V.blk 0 n).foldl compress H)[0]!), (49, ((blks V.M0 V.blk 0 n).foldl compress H)[1]!),
        (50, ((blks V.M0 V.blk 0 n).foldl compress H)[2]!), (51, ((blks V.M0 V.blk 0 n).foldl compress H)[3]!),
        (52, ((blks V.M0 V.blk 0 n).foldl compress H)[4]!), (53, ((blks V.M0 V.blk 0 n).foldl compress H)[5]!),
        (54, ((blks V.M0 V.blk 0 n).foldl compress H)[6]!), (55, ((blks V.M0 V.blk 0 n).foldl compress H)[7]!)] :
        List (Nat × UInt32))) := by
  have hl := bdo_loop V n hD hn sv0 sv1 sv2 sv3 ra n 0 H (by omega) hn0
  rw [bAddr_zero] at hl
  exact ((segn_pro V H sv0 sv1 sv2 sv3 n.toUInt32 ra).trans hl).congrN (by omega)

end Solutions.OpensslSha256
