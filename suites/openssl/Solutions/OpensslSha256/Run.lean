import Solutions.OpensslSha256.Facts
import Solutions.OpensslSha256.Seg.SPro
import Solutions.OpensslSha256.Seg.S00
import Solutions.OpensslSha256.Seg.S01
import Solutions.OpensslSha256.Seg.S02
import Solutions.OpensslSha256.Seg.S03
import Solutions.OpensslSha256.Seg.S04
import Solutions.OpensslSha256.Seg.S05
import Solutions.OpensslSha256.Seg.S06
import Solutions.OpensslSha256.Seg.S07
import Solutions.OpensslSha256.Seg.S08
import Solutions.OpensslSha256.Seg.S09
import Solutions.OpensslSha256.Seg.S10
import Solutions.OpensslSha256.Seg.S11
import Solutions.OpensslSha256.Seg.S12
import Solutions.OpensslSha256.Seg.S13
import Solutions.OpensslSha256.Seg.S14
import Solutions.OpensslSha256.Seg.S15
import Solutions.OpensslSha256.Seg.S16
import Solutions.OpensslSha256.Seg.S17
import Solutions.OpensslSha256.Seg.S18
import Solutions.OpensslSha256.Seg.S19
import Solutions.OpensslSha256.Seg.S20
import Solutions.OpensslSha256.Seg.S21
import Solutions.OpensslSha256.Seg.S22
import Solutions.OpensslSha256.Seg.S23
import Solutions.OpensslSha256.Seg.S24
import Solutions.OpensslSha256.Seg.S25
import Solutions.OpensslSha256.Seg.S26
import Solutions.OpensslSha256.Seg.S27
import Solutions.OpensslSha256.Seg.S28
import Solutions.OpensslSha256.Seg.S29
import Solutions.OpensslSha256.Seg.S30
import Solutions.OpensslSha256.Seg.S31
import Solutions.OpensslSha256.Seg.S32
import Solutions.OpensslSha256.Seg.S33
import Solutions.OpensslSha256.Seg.S34
import Solutions.OpensslSha256.Seg.S35
import Solutions.OpensslSha256.Seg.S36
import Solutions.OpensslSha256.Seg.S37
import Solutions.OpensslSha256.Seg.S38
import Solutions.OpensslSha256.Seg.S39
import Solutions.OpensslSha256.Seg.S40
import Solutions.OpensslSha256.Seg.S41
import Solutions.OpensslSha256.Seg.S42
import Solutions.OpensslSha256.Seg.S43
import Solutions.OpensslSha256.Seg.S44
import Solutions.OpensslSha256.Seg.S45
import Solutions.OpensslSha256.Seg.S46
import Solutions.OpensslSha256.Seg.S47
import Solutions.OpensslSha256.Seg.S48
import Solutions.OpensslSha256.Seg.S49
import Solutions.OpensslSha256.Seg.S50
import Solutions.OpensslSha256.Seg.S51
import Solutions.OpensslSha256.Seg.S52
import Solutions.OpensslSha256.Seg.S53
import Solutions.OpensslSha256.Seg.S54
import Solutions.OpensslSha256.Seg.S55
import Solutions.OpensslSha256.Seg.S56
import Solutions.OpensslSha256.Seg.S57
import Solutions.OpensslSha256.Seg.S58
import Solutions.OpensslSha256.Seg.S59
import Solutions.OpensslSha256.Seg.S60
import Solutions.OpensslSha256.Seg.S61
import Solutions.OpensslSha256.Seg.S62
import Solutions.OpensslSha256.Seg.S63
import Solutions.OpensslSha256.Seg.SEpi
/-!
# `SHA256_Transform`: the whole run

The segments of the run composed (`run_all`): from the entry of `SHA256_Transform` with the
hash words in the context slots to the return, with the context slots holding the compressed hash.
-/
namespace Solutions.OpensslSha256
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.Spec.Sha256

set_option maxRecDepth 100000 in
theorem run_all (V : Env) (H : Array UInt32) (blk : List UInt8) (sv0 sv1 sv2 sv3 : UInt32)
    (hblk : ∀ k, k < 16 → ((((blkWord V k <<< 24) ||| ((blkWord V k &&& 65280) <<< 8)) |||
      ((blkWord V k >>> 8) &&& 65280)) ||| (blkWord V k >>> 24)) = (schedule blk)[k]!)
    (harg1 : rdBytes V.M0 (UInt32.add (V.sp + 192) (UInt8.toUInt32 4)) 4 = V.ctx)
    (harg2 : rdBytes V.M0 (UInt32.add (V.sp + 192) (UInt8.toUInt32 8)) 4 = V.blk)
    (hret : rdBytes V.M0 (V.sp + 192) 4 = 0x101248) :
    Seg V 4073 0x1011b0
      (fun r => { r with esp := V.sp + 192, ebp := sv0, ebx := sv1, edi := sv2, esi := sv3 })
      (fun F => updL F [(48, H[0]!), (49, H[1]!), (50, H[2]!), (51, H[3]!), (52, H[4]!), (53, H[5]!), (54, H[6]!), (55, H[7]!)])
      0x101248
      (fun r => { r with esp := V.sp + 196, ebp := sv0, ebx := sv1, edi := sv2, esi := sv3 })
      (fun F => updL F [(48, H[0]! + A H (schedule blk) 64), (49, H[1]! + A H (schedule blk) 63), (50, H[2]! + A H (schedule blk) 62), (51, H[3]! + A H (schedule blk) 61), (52, H[4]! + E H (schedule blk) 64), (53, H[5]! + E H (schedule blk) 63), (54, H[6]! + E H (schedule blk) 62), (55, H[7]! + E H (schedule blk) 61)]) :=
  (seg_pro V H blk sv0 sv1 sv2 sv3 hblk harg1 harg2).trans
    ((seg_00 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_01 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_02 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_03 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_04 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_05 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_06 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_07 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_08 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_09 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_10 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_11 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_12 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_13 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_14 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_15 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_16 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_17 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_18 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_19 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_20 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_21 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_22 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_23 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_24 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_25 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_26 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_27 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_28 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_29 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_30 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_31 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_32 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_33 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_34 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_35 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_36 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_37 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_38 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_39 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_40 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_41 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_42 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_43 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_44 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_45 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_46 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_47 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_48 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_49 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_50 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_51 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_52 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_53 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_54 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_55 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_56 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_57 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_58 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_59 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_60 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_61 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_62 V H blk sv0 sv1 sv2 sv3 hblk).trans
    ((seg_63 V H blk sv0 sv1 sv2 sv3 hblk).trans
    (seg_epi V H blk sv0 sv1 sv2 sv3 hblk hret)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Solutions.OpensslSha256
