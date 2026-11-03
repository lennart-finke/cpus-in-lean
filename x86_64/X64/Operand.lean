import X64.Decode
import X64.Alu
import X64.Sys
namespace X64
@[inline] def eaOff (i : Inst) : M UInt64 := do
  let c ← cpu
  let base := if i.ripRelative then c.rip else if i.base < 16 then c.getReg i.base else 0
  let index := if i.index < 16 then c.getReg i.index <<< i.scale.toUInt64 else 0
  let addr := base + index + i.disp
  return if i.adsz == 4 then addr &&& 0xFFFFFFFF else addr
@[inline] def rdG (i : Inst) (sz : Sz) : M UInt64 := rdReg sz i.reg (i.rex != 0)
@[inline] def wrG (i : Inst) (sz : Sz) (v : UInt64) : M Unit := wrReg sz i.reg v (i.rex != 0)
@[inline] def rdE (i : Inst) (sz : Sz) (write : Bool := false) : M UInt64 := do
  if i.isMem then rdMem i.seg (← eaOff i) sz.toUInt64 write else rdReg sz i.rm (i.rex != 0)
@[inline] def wrE (i : Inst) (sz : Sz) (v : UInt64) : M Unit := do
  if i.isMem then wrMem i.seg (← eaOff i) sz.toUInt64 v else wrReg sz i.rm v (i.rex != 0)
@[inline] def bsz (i : Inst) : Sz := if i.op &&& 1 == 0 then 1 else i.opsz
@[inline] def needMem (i : Inst) : M Unit := if i.isMem then pure () else ud


end X64
