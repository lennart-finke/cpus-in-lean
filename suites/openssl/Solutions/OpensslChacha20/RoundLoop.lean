import Solutions.OpensslChacha20.RB1
import Solutions.OpensslChacha20.RB2
import Solutions.OpensslChacha20.RB3
import Solutions.OpensslChacha20.RB4
import Solutions.OpensslChacha20.RT
/-!
# The round loop of `chacha20_core`

The loop body (`rbAll`, the composition of the generated pieces `rb0` … `rb22`) is the double round
on the state words (`rbAll_toV`); with the counter update it runs ten times.
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20

def rbAll (r : RS) : RS :=
  rb22 ( rb21 ( rb20 ( rb19 ( rb18 ( rb17 ( rb16 ( rb15 ( rb14 ( rb13 ( rb12 ( rb11 ( rb10 ( rb9 ( rb8 ( rb7 ( rb6 ( rb5 ( rb4 ( rb3 ( rb2 ( rb1 ( rb0 (r)))))))))))))))))))))))

theorem rbAll_run (t : UInt32) : RunR t 133 0x100190 0x10032a (fun _ => True) rbAll := by
  have c0 : RunR t 6 0x100190 0x1001a5 (fun _ => True) rb0 :=
    fun H f r ic hF hC _ => rb0_run H t f r ic hF.sz hF.fit hF.code hC
  have c1 : RunR t 6 0x1001a5 0x1001b9 (fun _ => True) rb1 :=
    fun H f r ic hF hC _ => rb1_run H t f r ic hF.sz hF.fit hF.code hC
  have c2 : RunR t 6 0x1001b9 0x1001cd (fun _ => True) rb2 :=
    fun H f r ic hF hC _ => rb2_run H t f r ic hF.sz hF.fit hF.code hC
  have c3 : RunR t 6 0x1001cd 0x1001df (fun _ => True) rb3 :=
    fun H f r ic hF hC _ => rb3_run H t f r ic hF.sz hF.fit hF.code hC
  have c4 : RunR t 6 0x1001df 0x1001f2 (fun _ => True) rb4 :=
    fun H f r ic hF hC _ => rb4_run H t f r ic hF.sz hF.fit hF.code hC
  have c5 : RunR t 6 0x1001f2 0x100204 (fun _ => True) rb5 :=
    fun H f r ic hF hC _ => rb5_run H t f r ic hF.sz hF.fit hF.code hC
  have c6 : RunR t 6 0x100204 0x100217 (fun _ => True) rb6 :=
    fun H f r ic hF hC _ => rb6_run H t f r ic hF.sz hF.fit hF.code hC
  have c7 : RunR t 6 0x100217 0x10022a (fun _ => True) rb7 :=
    fun H f r ic hF hC _ => rb7_run H t f r ic hF.sz hF.fit hF.code hC
  have c8 : RunR t 6 0x10022a 0x10023c (fun _ => True) rb8 :=
    fun H f r ic hF hC _ => rb8_run H t f r ic hF.sz hF.fit hF.code hC
  have c9 : RunR t 6 0x10023c 0x10024d (fun _ => True) rb9 :=
    fun H f r ic hF hC _ => rb9_run H t f r ic hF.sz hF.fit hF.code hC
  have c10 : RunR t 6 0x10024d 0x10025f (fun _ => True) rb10 :=
    fun H f r ic hF hC _ => rb10_run H t f r ic hF.sz hF.fit hF.code hC
  have c11 : RunR t 6 0x10025f 0x100271 (fun _ => True) rb11 :=
    fun H f r ic hF hC _ => rb11_run H t f r ic hF.sz hF.fit hF.code hC
  have c12 : RunR t 6 0x100271 0x100285 (fun _ => True) rb12 :=
    fun H f r ic hF hC _ => rb12_run H t f r ic hF.sz hF.fit hF.code hC
  have c13 : RunR t 6 0x100285 0x100298 (fun _ => True) rb13 :=
    fun H f r ic hF hC _ => rb13_run H t f r ic hF.sz hF.fit hF.code hC
  have c14 : RunR t 6 0x100298 0x1002a9 (fun _ => True) rb14 :=
    fun H f r ic hF hC _ => rb14_run H t f r ic hF.sz hF.fit hF.code hC
  have c15 : RunR t 6 0x1002a9 0x1002bd (fun _ => True) rb15 :=
    fun H f r ic hF hC _ => rb15_run H t f r ic hF.sz hF.fit hF.code hC
  have c16 : RunR t 6 0x1002bd 0x1002cd (fun _ => True) rb16 :=
    fun H f r ic hF hC _ => rb16_run H t f r ic hF.sz hF.fit hF.code hC
  have c17 : RunR t 6 0x1002cd 0x1002de (fun _ => True) rb17 :=
    fun H f r ic hF hC _ => rb17_run H t f r ic hF.sz hF.fit hF.code hC
  have c18 : RunR t 6 0x1002de 0x1002ee (fun _ => True) rb18 :=
    fun H f r ic hF hC _ => rb18_run H t f r ic hF.sz hF.fit hF.code hC
  have c19 : RunR t 6 0x1002ee 0x100301 (fun _ => True) rb19 :=
    fun H f r ic hF hC _ => rb19_run H t f r ic hF.sz hF.fit hF.code hC
  have c20 : RunR t 6 0x100301 0x100314 (fun _ => True) rb20 :=
    fun H f r ic hF hC _ => rb20_run H t f r ic hF.sz hF.fit hF.code hC
  have c21 : RunR t 6 0x100314 0x100327 (fun _ => True) rb21 :=
    fun H f r ic hF hC _ => rb21_run H t f r ic hF.sz hF.fit hF.code hC
  have c22 : RunR t 1 0x100327 0x10032a (fun _ => True) rb22 :=
    fun H f r ic hF hC _ => rb22_run H t f r ic hF.sz hF.fit hF.code hC
  exact ((((((((((((((((((((((c0.trans (fun _ _ => trivial) c1).trans (fun _ _ => trivial) c2).trans (fun _ _ => trivial) c3).trans (fun _ _ => trivial) c4).trans (fun _ _ => trivial) c5).trans (fun _ _ => trivial) c6).trans (fun _ _ => trivial) c7).trans (fun _ _ => trivial) c8).trans (fun _ _ => trivial) c9).trans (fun _ _ => trivial) c10).trans (fun _ _ => trivial) c11).trans (fun _ _ => trivial) c12).trans (fun _ _ => trivial) c13).trans (fun _ _ => trivial) c14).trans (fun _ _ => trivial) c15).trans (fun _ _ => trivial) c16).trans (fun _ _ => trivial) c17).trans (fun _ _ => trivial) c18).trans (fun _ _ => trivial) c19).trans (fun _ _ => trivial) c20).trans (fun _ _ => trivial) c21).trans (fun _ _ => trivial) c22)

/-- The state words of a round state at the loop head. -/
def RS.toV (r : RS) : V16 :=
  ⟨r.s8, r.s10, r.sc, r.s4, r.ebp, r.edi, r.esi, r.eax, r.s20, r.s1c, r.s34, r.s30, r.s0, r.ecx, r.s18, r.ebx⟩

theorem rbAll_toV (r : RS) : (rbAll r).toV = dround r.toV := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30,
    s34, s38⟩
  rfl

theorem rbAll_s28 (r : RS) : (rbAll r).s28 = r.s28 := rfl
theorem rbAll_s14 (r : RS) : (rbAll r).s14 = r.s14 := rfl
theorem rbAll_s24 (r : RS) : (rbAll r).s24 = r.s24 := rfl

end Solutions.OpensslChacha20
