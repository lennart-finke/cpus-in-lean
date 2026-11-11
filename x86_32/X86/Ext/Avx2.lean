import X86.Ext.Avx
/-!
# AVX2, FMA3, F16C

Owner: the AVX2 workstream. 256-bit integer instructions (VEX.256 forms of the packed-integer
instructions, VPERMD/VPERMQ/VPERM2I128, VPBROADCAST*, VPMASKMOV*, VPSLLV*/VPSRLV*/VPSRAVD,
VINSERTI128/VEXTRACTI128, VPBLENDD), gathers (VEX.0F38 90..93), FMA3 (VEX.0F38 96..BF), F16C
(VEX.0F38 13 VCVTPH2PS, VEX.0F3A 1D VCVTPS2PH).

Hook (called by `X86/Dispatch.lean` after `Avx.vex?`; `none` = not handled here):

* `vex?`: the instructions above.
-/
namespace X86
namespace Avx2

def vex? (_i : Inst) : Option (M Unit) := none

end Avx2
end X86
