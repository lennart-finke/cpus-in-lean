import X64
open X64

def check (name : String) (condition : Bool) : IO Unit := do
  if !condition then throw (IO.userError s!"FAIL: {name}")
  IO.println s!"PASS: {name}"

def baseMachine : Machine := {
  cpu := { rip := 0x10000, rsp := 0x18000,
           cs := flatSeg 8 0xA09B, ss := flatSeg 16 0xC093,
           cr0 := 0x80010011, cr3 := 0x3000, cr4 := 0x20, efer := 0xD01 },
  mem := identityMap (zeroMem 0x20000) }

def runBytes (code : List UInt8) (m : Machine := baseMachine) : EStateM.Result Fault Machine Inst :=
  let mem := code.toArray.foldl (fun (s : Nat × ByteArray) b => (s.1+1, s.2.set! s.1 b)) (m.cpu.rip.toNat,m.mem)
  instruction { m with mem := mem.2 }

def completed (r : EStateM.Result Fault Machine Inst) (f : Machine → Bool) : Bool :=
  match r with | .ok _ m => f m | _ => false

def faults (r : EStateM.Result Fault Machine α) (vec : UInt8) (err addr : UInt64) : Bool :=
  match r with | .error (.exc v e a) _ => v == vec && e == some err && a == addr | _ => false

def main : IO UInt32 := do
  check "32-bit destination clears high half" (completed
    (runBytes [0xB8,1,0,0,0] { baseMachine with cpu := { baseMachine.cpu with rax := 0xFFFFFFFFFFFFFFFF } })
    (fun m => m.cpu.rax == 1))
  check "REX selects SPL, not AH" (completed (runBytes [0x40,0xB4,0x55]) (fun m => m.cpu.rsp == 0x18055 && m.cpu.rax == 0))
  check "legacy byte write selects AH" (completed (runBytes [0xB4,0x55]) (fun m => m.cpu.rax == 0x5500 && m.cpu.rsp == 0x18000))
  check "legacy prefix cancels earlier REX" (completed (runBytes [0x48,0x66,0xB8,0x34,0x12])
    (fun m => m.cpu.rax == 0x1234 && m.cpu.rip == 0x10005))
  check "REX.W wins over earlier operand override" (completed
    (runBytes [0x66,0x48,0xB8,1,2,3,4,5,6,7,8]) (fun m => m.cpu.rax == 0x0807060504030201))
  check "RIP-relative LEA uses end of instruction" (completed (runBytes [0x48,0x8D,0x05,0xFC,0xFF,0xFF,0xFF])
    (fun m => m.cpu.rax == 0x10003))
  check "address override truncates effective address" (completed
    (runBytes [0x67,0x48,0x8B,0x03] { baseMachine with cpu := { baseMachine.cpu with rbx := 0xFFFF000000001000 } })
    (fun m => m.cpu.rax == 0))
  check "noncanonical stack address raises SS" (faults
    ((rdMem SegN.SS 0x800000000000 8) baseMachine) Vec.SS 0 0)
  check "noncanonical data address raises GP" (faults
    ((rdMem SegN.DS 0x800000000000 8) baseMachine) Vec.GP 0 0)
  check "supervisor page rejects user read" (faults (translate 0x1000 .read true baseMachine) Vec.PF 5 0x1000)
  let nx := { baseMachine with mem := wrBytes baseMachine.mem 0x5000 8 0x8000000000000083 }
  check "NX rejects instruction fetch" (faults (translate 0x10000 .fetch false nx) Vec.PF 17 0x10000)
  let noNx := { nx with cpu := { nx.cpu with efer := 0x501 } }
  check "NX bit is reserved when NXE is clear" (faults (translate 0x1000 .read false noNx) Vec.PF 9 0x1000)
  let ro := { baseMachine with mem := wrBytes baseMachine.mem 0x5000 8 0x81 }
  check "CR0.WP protects supervisor stores" (faults (translate 0x1000 .write false ro) Vec.PF 3 0x1000)
  let writable := { ro with cpu := { ro.cpu with cr0 := 0x80000011 } }
  check "CR0.WP clear permits supervisor store" (match translate 0x1000 .write false writable with
    | .ok addr m => addr == 0x1000 && rdBytes m.mem 0x5000 8 &&& 0x60 == 0x60 | _ => false)
  let crossing := { baseMachine with mem := wrBytes (wrBytes baseMachine.mem 0x5000 8 0x6003) 0x6040 8 0x8003 }
  check "cross-page store faults before writing data" (match linWr 0x8FFF 8 0xFEDCBA9876543210 false crossing with
    | .error (.exc 14 (some 2) 0x9000) m => m.mem.get! 0x8FFF == 0 | _ => false)
  let reserved := { baseMachine with mem := wrBytes baseMachine.mem 0x5000 8 0x2083 }
  check "reserved large-page address bits raise PF" (faults (translate 0 .read false reserved) Vec.PF 9 0)
  let fs := { baseMachine with cpu := { baseMachine.cpu with fsBase := 0x1000 }, mem := wrBytes baseMachine.mem 0x1020 8 42 }
  check "FS base participates in addressing" (completed (runBytes [0x64,0x48,0x8B,0x04,0x25,0x20,0,0,0] fs) (fun m => m.cpu.rax == 42))
  let user := { baseMachine with
    cpu := { baseMachine.cpu with cs := flatSeg 0x1B 0xA0FB, ss := flatSeg 0x23 0xC0F3 },
    mem := wrBytes (wrBytes (wrBytes baseMachine.mem 0x3000 8 0x4007) 0x4000 8 0x5007) 0x5000 8 0x87 }
  check "SWAPGS is privileged" (faults (runBytes [0x0F,0x01,0xF8] user) Vec.GP 0 0)
  let sys := { user with cpu := { user.cpu with
    star := 0x0010000800000000, lstar := 0x12000, sfmask := Flag.IF,
    rflags := 0x202, gsBase := 0x1000, kernelGsBase := 0x2000 } }
  check "SYSCALL saves RIP/RFLAGS and retains RSP" (completed (runBytes [0x0F,0x05] sys)
    (fun m => m.cpu.rip == 0x12000 && m.cpu.rcx == 0x10002 && m.cpu.r11 == 0x202 &&
      m.cpu.rflags == 2 && m.cpu.rsp == sys.cpu.rsp && m.cpu.cs.sel == 8 && m.cpu.ss.sel == 16))
  let ret := { baseMachine with cpu := { baseMachine.cpu with star := 0x0010000800000000, rcx := 0x16000, r11 := 0x202 } }
  check "SYSRETQ returns to ring 3" (completed (runBytes [0x48,0x0F,0x07] ret)
    (fun m => m.cpu.rip == 0x16000 && m.cpu.cpl == 3 && m.cpu.cs.sel == 0x23 && m.cpu.ss.sel == 0x1B))
  let badRet := { ret with cpu := { ret.cpu with rcx := 0x800000000000 } }
  check "SYSRET canonical check occurs before privilege change" (match runBytes [0x48,0x0F,0x07] badRet with
    | .error (.exc 13 (some 0) 0) m => m.cpu.cs.sel == badRet.cpu.cs.sel && m.cpu.rip == badRet.cpu.rip | _ => false)
  check "reject truncated bzImage" (match loadLinux (32*1024*1024) ByteArray.empty ByteArray.empty "" with | .error _ => true | .ok _ => false)
  let mut gateMem := user.mem
  gateMem := wrBytes gateMem 0x9008 8 0x00AF9B000000FFFF
  gateMem := wrBytes gateMem 0x9010 8 0x00CF93000000FFFF
  gateMem := wrBytes gateMem 0x9018 8 0x00AFFB000000FFFF
  gateMem := wrBytes gateMem 0x9020 8 0x00CFF3000000FFFF
  -- Vector 32 -> CS 8:RIP 0x12000, interrupt gate, IST 0.
  gateMem := wrBytes gateMem 0xA200 8 0x00018E0000082000
  gateMem := wrBytes gateMem 0xB004 8 0x1A008
  let gates : Machine := { user with
    cpu := { user.cpu with
      gdtBase := 0x9000, gdtLimit := 39, idtBase := 0xA000, idtLimit := 4095,
      tr := { sel := 0x28, base := 0xB000, limit := 103, attr := 0x89 }, rflags := 0x202 },
    mem := gateMem }
  let entered := deliver 32 none false true gates
  check "interrupt switches to TSS stack and pushes 64-bit frame" (match entered with
    | .ok _ m => m.cpu.rsp == 0x19FD8 && m.cpu.cs.sel == 8 && m.cpu.rip == 0x12000 &&
      m.cpu.rflags &&& Flag.IF == 0 && rdBytes m.mem 0x19FD8 8 == 0x10000 &&
      rdBytes m.mem 0x19FE0 8 == 0x1B && rdBytes m.mem 0x19FF0 8 == 0x18000
    | _ => false)
  check "IRETQ restores ring-3 stack and flags" (match entered with
    | .ok _ m => match iret m with
      | .ok _ r => r.cpu.rip == gates.cpu.rip && r.cpu.rsp == gates.cpu.rsp &&
        r.cpu.cs.sel == 0x1B && r.cpu.ss.sel == 0x23 && r.cpu.rflags == gates.cpu.rflags
      | _ => false
    | _ => false)
  let same := { gates with cpu := { gates.cpu with cs := flatSeg 8 0xA09B, ss := flatSeg 16 0xC093 } }
  check "same-ring interrupt also pushes SS:RSP" (match deliver 32 none false true same with
    | .ok _ m => m.cpu.rsp == same.cpu.rsp - 40 && match iret m with
      | .ok _ r => r.cpu.rsp == same.cpu.rsp && r.cpu.rip == same.cpu.rip && r.cpu.cs.sel == 8
      | _ => false
    | _ => false)
  check "software INT obeys gate DPL" (faults (deliver 32 none true false gates) Vec.GP 0x102 0)
  let ist := { gates with mem := wrBytes (wrBytes gateMem 0xA200 8 0x00018E0100082000) 0xB024 8 0x1C008 }
  check "IST chooses its own TSS stack" (match deliver 32 none false true ist with
    | .ok _ m => m.cpu.rsp == 0x1BFD8 | _ => false)
  -- Synthetic boot image checks loader+runner plumbing, not Linux bootability.
  let mut kernel := zeroMem 0x1000
  for (off,n,v) in [(0x1FE,2,0xAA55),(0x202,4,0x53726448),(0x206,2,0x20C),
    (0x236,2,1),(0x1F1,1,1),(0x201,1,0x6A),(0x214,4,0x100000),
    (0x260,4,4096),(0x238,4,256),(0x22C,4,0x3FFFFFFF)] do
    kernel := wrBytes kernel off n v
  let payload : List UInt8 := [0xBA,0xF8,3,0,0,0xB0,0x4B,0xEE,0xF4]
  for k in [0:payload.length] do kernel := kernel.set! (0x600+k) payload[k]!
  check "64-bit boot entry executes guest bytes and writes serial" (match loadLinux (32*1024*1024) kernel ByteArray.empty "console=ttyS0" with
    | .ok m => let r := m.runUntil 100
               r.fatal.isNone && r.cpu.halted && r.uart.tx.toList == [0x4B]
    | .error _ => false)
  let badImage := wrBytes kernel 0x236 2 0
  check "loader rejects a 32-bit image" (match loadLinux (32*1024*1024) badImage ByteArray.empty "" with
    | .error _ => true | .ok _ => false)
  let sse := { baseMachine with cpu := { baseMachine.cpu with cr4 := 0x620 } }
  let a : Xmm := { lo := 0x3FF0000000000000, hi := 0x1234 }
  let divZero := { sse with cpu := { sse.cpu with mxcsr := 0x1D80, xmm := sse.cpu.xmm.set! 0 a } }
  check "unmasked SIMD divide-by-zero keeps destination and sets sticky ZE" (match runBytes [0xF2,0x0F,0x5E,0xC1] divZero with
    | .error (.exc 19 none 0) m => m.cpu.rip == divZero.cpu.rip && m.cpu.xmm[0]! == a && m.cpu.mxcsr == 0x1D84
    | _ => false)
  -- Eight counterexamples captured on AMD EPYC 7742, plus masked/sticky controls.
  for (pfx, bits) in [([],32), ([0x66],64), ([0xF3],32), ([0xF2],64)] do
    let one : UInt64 := if bits == 32 then 0x3F800000 else 0x3FF0000000000000
    let normal : UInt64 := if bits == 32 then 0x00800000 else 0x0010000000000000
    let splat := fun value => (List.range (128/bits)).foldl
      (fun (v : Xmm) k => v.setLane bits k value) {}
    for (op, lhs, rhs, mxcsr, expected) in
        ([(0x58, 1, one, 0x1E80, 0x1E82),
         (0x58, 1, one, 0x1EA0, 0x1EA2),
         (0x59, normal, normal, 0x1780, 0x1790),
         (0x59, normal, normal, 0x9780, 0x9790)] : List (UInt8 × UInt64 × UInt64 × UInt64 × UInt64)) do
      let m := { sse with cpu := { sse.cpu with
        mxcsr := mxcsr, xmm := (sse.cpu.xmm.set! 0 (splat lhs)).set! 1 (splat rhs) } }
      check s!"SIMD hardware regression {pfx}/{op}, MXCSR={mxcsr}" (match runBytes (pfx ++ [0x0F,op,0xC1]) m with
        | .error (.exc 19 none 0) r => r.cpu.rip == m.cpu.rip && r.cpu.xmm == m.cpu.xmm && r.cpu.mxcsr == expected
        | _ => false)
    for (op, lhs, rhs, expected) in
        ([(0x58, 1, one, 0x1FA2), (0x59, normal, normal, 0x1FB0)] : List (UInt8 × UInt64 × UInt64 × UInt64)) do
      let m := { sse with cpu := { sse.cpu with
        mxcsr := 0x1F80, xmm := (sse.cpu.xmm.set! 0 (splat lhs)).set! 1 (splat rhs) } }
      check s!"masked SIMD control {pfx}/{op}" (completed (runBytes (pfx ++ [0x0F,op,0xC1]) m)
        (fun r => r.cpu.mxcsr == expected))
  let mixed := { sse with cpu := { sse.cpu with
    mxcsr := 0x1F00, xmm := (sse.cpu.xmm.set! 0 { lo := 0x000000017F800001, hi := 0x3F8000003F800000 }).set! 1
      { lo := 0x3F8000003F800000, hi := 0x000000013F800000 } } }
  check "packed input exception suppresses output flags across all lanes" (match runBytes [0x0F,0x58,0xC1] mixed with
    | .error (.exc 19 none 0) m => m.cpu.mxcsr == 0x1F03 && m.cpu.xmm == mixed.cpu.xmm
    | _ => false)
  for f in [FP.binary32, FP.binary64] do
    let emin := 1 - f.bias
    let emax := (f.exponentMax : Int) - 1 - f.bias
    check "exact representable subnormal still traps with UM clear"
      ((FP.pack f false 1 1 (emin-1) 0x1780).2 == 0x10)
    check "inexact unbounded underflow retains PE"
      ((FP.pack f false 1 3 (emin-1) 0x1780).2 == 0x30)
    check "exact unbounded overflow omits PE with OM clear"
      ((FP.pack f false 1 1 (emax+1) 0x1B80).2 == 8)
    check "masked overflow sets PE even for an exact unbounded result"
      ((FP.pack f false 1 1 (emax+1) 0x1F80).2 == 0x28)
    check "inexact unbounded overflow retains PE"
      ((FP.pack f false 1 3 (emax+3) 0x1B80).2 == 0x28)
  -- EPYC hardware: minNormal * predecessor(1) is tiny before denormalization,
  -- even when gradual underflow rounds it back up to minNormal. FTZ must flush.
  for (pfx, bits) in ([([],32), ([0x66],64), ([0xF3],32), ([0xF2],64)] : List (List UInt8 × Nat)) do
    let normal : UInt64 := if bits == 32 then 0x00800000 else 0x0010000000000000
    let one : UInt64 := if bits == 32 then 0x3F800000 else 0x3FF0000000000000
    let signBit : UInt64 := if bits == 32 then 0x80000000 else 0x8000000000000000
    let splat := fun value => (List.range (128/bits)).foldl
      (fun (v : Xmm) k => v.setLane bits k value) {}
    for negative in [false, true] do
      let sign := if negative then signBit else 0
      for rounding in ([0,1,2,3] : List UInt64) do
        for dazBit in ([0,0x40] : List UInt64) do
          for ftz in [false,true] do
            for masked in [false,true] do
              let mxcsr := (if masked then 0x1F80 else 0x1780) ||| (rounding <<< 13) |||
                dazBit ||| (if ftz then 0x8000 else 0)
              let m := { sse with cpu := { sse.cpu with
                mxcsr := mxcsr, xmm := (sse.cpu.xmm.set! 0 (splat (normal ||| sign))).set! 1 (splat (one-1)) } }
              let up := rounding == 0 || (rounding == 1 && negative) || (rounding == 2 && !negative)
              let value := sign ||| (if ftz then 0 else if up then normal else normal-1)
              let lanes := if pfx == [0xF2] || pfx == [0xF3] then 1 else 128/bits
              let expected := (List.range lanes).foldl (fun (v : Xmm) k => v.setLane bits k value) m.cpu.xmm[0]!
              check s!"FTZ normal-boundary {pfx}, sign={negative}, MXCSR={mxcsr}" (match runBytes (pfx ++ [0x0F,0x59,0xC1]) m with
                | .ok _ r => masked && r.cpu.xmm[0]! == expected && r.cpu.mxcsr == (mxcsr ||| 0x30)
                | .error (.exc 19 none 0) r => !masked && r.cpu.xmm == m.cpu.xmm &&
                    r.cpu.rip == m.cpu.rip && r.cpu.mxcsr == (mxcsr ||| 0x10)
                | _ => false)
  let daz := { sse with cpu := { sse.cpu with mxcsr := 0x1FC0, xmm := sse.cpu.xmm.set! 0 { lo := 1, hi := 1 } } }
  check "MINPD applies DAZ to denormal results" (completed (runBytes [0x66,0x0F,0x5D,0xC0] daz)
    (fun m => m.cpu.xmm[0]! == {} && m.cpu.mxcsr == 0x1FC0))
  check "SSE disabled raises UD" (match runBytes [0x0F,0x57,0xC0] baseMachine with
    | .error (.exc 6 none 0) _ => true | _ => false)
  check "task-switched SSE raises NM" (match runBytes [0x0F,0x57,0xC0] { sse with cpu := { sse.cpu with cr0 := sse.cpu.cr0 ||| CR0.TS } } with
    | .error (.exc 7 none 0) _ => true | _ => false)
  let farMem := wrBytes (wrBytes (wrBytes baseMachine.mem 0x9008 8 0x00AF9B000000FFFF) 0x18000 8 0x12000) 0x18008 8 8
  let far := { baseMachine with cpu := { baseMachine.cpu with gdtBase := 0x9000, gdtLimit := 15 }, mem := farMem }
  check "RETFQ reloads CS and consumes two 64-bit slots" (completed (runBytes [0x48,0xCB] far)
    (fun m => m.cpu.rip == 0x12000 && m.cpu.rsp == 0x18010 && m.cpu.cs.sel == 8))
  let fx := { sse with cpu := { sse.cpu with
    rbx := 0x12000, fpStatus := 0x2800, fpTag := 0xF3FF, fpIp := 0xFFFF800012345678,
    fp := sse.cpu.fp.set! 5 ⟨0x8000000000000000, 0x3FFF⟩,
    xmm := sse.cpu.xmm.set! 15 ⟨0x1122334455667788, 0x99AABBCCDDEEFF00⟩ } }
  check "FXSAVE64 layout and FXRSTOR64 preserve x87 and high XMM registers" (match runBytes [0x48,0x0F,0xAE,0x03] fx with
    | .ok _ saved =>
      rdBytes saved.mem 0x12004 1 == 0x20 && rdBytes saved.mem 0x12008 8 == fx.cpu.fpIp &&
      rdBytes saved.mem 0x12020 8 == 0x8000000000000000 &&
      completed (runBytes [0x48,0x0F,0xAE,0x0B] { saved with cpu := { sse.cpu with rbx := 0x12000 } })
        (fun m => m.cpu.fpStatus == fx.cpu.fpStatus && m.cpu.fpTag == fx.cpu.fpTag &&
          m.cpu.fpIp == fx.cpu.fpIp && m.cpu.fp[5]! == fx.cpu.fp[5]! && m.cpu.xmm[15]! == fx.cpu.xmm[15]!)
    | _ => false)
  let badMx := { sse with cpu := { sse.cpu with rbx := 0x12000 }, mem := wrBytes sse.mem 0x12000 4 0x10000 }
  check "LDMXCSR rejects reserved bits" (faults (runBytes [0x0F,0xAE,0x13] badMx) Vec.GP 0 0)
  let sseCross := { crossing with mem := wrBytes crossing.mem 0x6080 8 0x10003, cpu := { sse.cpu with rbx := 0x8FF8, xmm := sse.cpu.xmm.set! 0 ⟨1,2⟩ } }
  check "cross-page MOVUPS store probes before committing either half" (match runBytes [0x0F,0x11,0x03] sseCross with
    | .error (.exc 14 (some 2) 0x9000) m => rdBytes m.mem 0x8FF8 8 == 0 | _ => false)
  let integerFp := { sse with cpu := { sse.cpu with rbx := 0x12000 }, mem := wrBytes sse.mem 0x12000 4 0xFFFFFFD6 }
  check "FILD32 pushes exact negative extended value and tracks operand address" (completed
    (runBytes [0xDB,0x03] integerFp) (fun m => m.cpu.fpStatus == 0x3800 && m.cpu.fpTag == 0x3FFF &&
      m.cpu.fp[7]! == ⟨0xA800000000000000, 0xC004⟩ && m.cpu.fpIp == 0x10000 && m.cpu.fpDp == 0x12000))
  let gd := { baseMachine with cpu := { baseMachine.cpu with dr7 := 0x2400 } }
  check "MOV DR general detect faults and clears GD without committing the destination" (match runBytes [0x0F,0x21,0xF8] gd with
    | .error (.exc 1 none 0) m => m.cpu.dr7 == 0x400 && m.cpu.dr6 &&& 0x2000 != 0 && m.cpu.rax == gd.cpu.rax
    | _ => false)
  IO.println "All targeted checks passed"
  return 0
