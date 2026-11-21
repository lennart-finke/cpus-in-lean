import Solutions.OpensslSha256.SegN.S00
import Solutions.OpensslSha256.SegN.S01
import Solutions.OpensslSha256.SegN.S02
import Solutions.OpensslSha256.SegN.S03
import Solutions.OpensslSha256.SegN.S04
import Solutions.OpensslSha256.SegN.S05
import Solutions.OpensslSha256.SegN.S06
import Solutions.OpensslSha256.SegN.S07
import Solutions.OpensslSha256.SegN.S08
import Solutions.OpensslSha256.SegN.S09
import Solutions.OpensslSha256.SegN.S10
import Solutions.OpensslSha256.SegN.S11
import Solutions.OpensslSha256.SegN.S12
import Solutions.OpensslSha256.SegN.S13
import Solutions.OpensslSha256.SegN.S14
import Solutions.OpensslSha256.SegN.S15
import Solutions.OpensslSha256.SegN.S16
import Solutions.OpensslSha256.SegN.S17
import Solutions.OpensslSha256.SegN.S18
import Solutions.OpensslSha256.SegN.S19
import Solutions.OpensslSha256.SegN.S20
import Solutions.OpensslSha256.SegN.S21
import Solutions.OpensslSha256.SegN.S22
import Solutions.OpensslSha256.SegN.S23
import Solutions.OpensslSha256.SegN.S24
import Solutions.OpensslSha256.SegN.S25
import Solutions.OpensslSha256.SegN.S26
import Solutions.OpensslSha256.SegN.S27
import Solutions.OpensslSha256.SegN.S28
import Solutions.OpensslSha256.SegN.S29
import Solutions.OpensslSha256.SegN.S30
import Solutions.OpensslSha256.SegN.S31
import Solutions.OpensslSha256.SegN.S32
import Solutions.OpensslSha256.SegN.S33
import Solutions.OpensslSha256.SegN.S34
import Solutions.OpensslSha256.SegN.S35
import Solutions.OpensslSha256.SegN.S36
import Solutions.OpensslSha256.SegN.S37
import Solutions.OpensslSha256.SegN.S38
import Solutions.OpensslSha256.SegN.S39
import Solutions.OpensslSha256.SegN.S40
import Solutions.OpensslSha256.SegN.S41
import Solutions.OpensslSha256.SegN.S42
import Solutions.OpensslSha256.SegN.S43
import Solutions.OpensslSha256.SegN.S44
import Solutions.OpensslSha256.SegN.S45
import Solutions.OpensslSha256.SegN.S46
import Solutions.OpensslSha256.SegN.S47
import Solutions.OpensslSha256.SegN.S48
import Solutions.OpensslSha256.SegN.S49
import Solutions.OpensslSha256.SegN.S50
import Solutions.OpensslSha256.SegN.S51
import Solutions.OpensslSha256.SegN.S52
import Solutions.OpensslSha256.SegN.S53
import Solutions.OpensslSha256.SegN.S54
import Solutions.OpensslSha256.SegN.S55
import Solutions.OpensslSha256.SegN.S56
import Solutions.OpensslSha256.SegN.S57
import Solutions.OpensslSha256.SegN.S58
import Solutions.OpensslSha256.SegN.S59
import Solutions.OpensslSha256.SegN.S60
import Solutions.OpensslSha256.SegN.S61
import Solutions.OpensslSha256.SegN.S62
import Solutions.OpensslSha256.SegN.S63
import Solutions.OpensslSha256.SegN.SEpi
/-!
# One block of `sha256_block_data_order`

From the loop head `0x100390` (the hash words in registers and slots, `V.blk` the block, `cnt` the
blocks left) to `decl %esi`: the 64 rounds (`SegN.S00`..`S63`) and the additions into the hash words.
-/
namespace Solutions.OpensslSha256
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.Spec.Sha256

set_option maxRecDepth 100000 in
theorem block_body (V : Env) (H : Array UInt32) (blk : List UInt8) (sv0 sv1 sv2 sv3 : UInt32)
    (hblk : ∀ k, k < 16 → ((((blkWord V k <<< 24) ||| ((blkWord V k &&& 65280) <<< 8)) |||
      ((blkWord V k >>> 8) &&& 65280)) ||| (blkWord V k >>> 24)) = (schedule blk)[k]!) (cnt ra : UInt32) :
    Seg V 4012 0x100390
      (fun r => { r with esp := V.sp, ecx := H[4]!, edx := V.blk, ebx := H[6]!, esi := cnt, edi := H[7]! })
      (fun F => updL F ([(10, H[2]!), (11, H[1]!), (12, H[0]!), (13, H[5]!), (14, H[3]!), (38, V.ctx), (42, sv3), (43, sv2), (44, sv1), (45, sv0), (46, ra)] : List (Nat × UInt32)))
      0x101159
      (fun r => { r with esp := V.sp, ecx := H[4]! + E H (schedule blk) 64, edx := V.blk + 64, ebp := H[5]! + E H (schedule blk) 63, esi := cnt, edi := H[7]! + E H (schedule blk) 61 })
      (fun F => updL F ([(10, H[2]! + A H (schedule blk) 62), (11, H[1]! + A H (schedule blk) 63), (12, H[0]! + A H (schedule blk) 64), (14, H[3]! + A H (schedule blk) 61), (15, H[6]! + E H (schedule blk) 62), (38, V.ctx), (42, sv3), (43, sv2), (44, sv1), (45, sv0), (46, ra)] : List (Nat × UInt32))) :=
    ((segn_00 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_01 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_02 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_03 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_04 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_05 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_06 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_07 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_08 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_09 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_10 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_11 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_12 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_13 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_14 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_15 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_16 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_17 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_18 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_19 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_20 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_21 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_22 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_23 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_24 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_25 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_26 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_27 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_28 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_29 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_30 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_31 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_32 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_33 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_34 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_35 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_36 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_37 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_38 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_39 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_40 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_41 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_42 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_43 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_44 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_45 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_46 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_47 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_48 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_49 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_50 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_51 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_52 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_53 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_54 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_55 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_56 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_57 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_58 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_59 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_60 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_61 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_62 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    ((segn_63 V H blk sv0 sv1 sv2 sv3 hblk cnt ra).trans
    (segn_epiA V H blk sv0 sv1 sv2 sv3 cnt ra)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Solutions.OpensslSha256
