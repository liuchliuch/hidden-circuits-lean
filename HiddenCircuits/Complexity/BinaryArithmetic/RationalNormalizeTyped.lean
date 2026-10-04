import HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalizeRegisters
import HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalizeModel

/-! Canonical rational output, with every arithmetic side condition obtained
from the input integers rather than supplied by the caller. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalize
open OracleBlock Polynomial

lemma quotient_negative_iff (u v : ℤ) (hv : v≠0) : v/divisor u v<0 ↔ v<0 := by
  have hp:=divisor_positive u v hv
  have he:=Int.ediv_mul_cancel (divisor_dvd_right u v)
  constructor <;> intro h <;> nlinarith

lemma canonical_num (u v : ℤ) (hv : v≠0) :
    signNumerator (u/divisor u v) (v/divisor u v)=((u:ℚ)/(v:ℚ)).num := by
  rw [numerator_eq u v hv]
  simp only [signNumerator,quotient_negative_iff u v hv]
lemma canonical_den (u v : ℤ) (hv : v≠0) :
    ((v/divisor u v).natAbs:ℤ)=(((u:ℚ)/(v:ℚ)).den:ℤ) := by
  rw [denominator_eq u v hv]
  by_cases hn:v<0
  · rw [if_pos hn,Int.ofNat_natAbs_of_nonpos ((quotient_negative_iff u v hv).mpr hn).le]
  · have h : ¬v/divisor u v<0 := by rwa [quotient_negative_iff u v hv]
    rw [if_neg hn,Int.natAbs_of_nonneg (by omega)]

/-- Clean canonical rational output from canonical signed registers. -/
theorem program_executes (g : BitString → ℕ) (u v : ℤ) (hv : v≠0) :
    ∃c,program.Executes g (regState (signedBits u) (signedBits v) [])
      (Function.update (fun _=>[]) 0 (RationalOracleEncoding.bits ((u:ℚ)/(v:ℚ)))) c ∧
      c≤time.eval ((signedBits u).length+(signedBits v).length) := by
  let L := (signedBits u).length+(signedBits v).length
  have hd : (signedBits (divisor u v)).length≤L := (divisor_bits_le u v hv).trans (by dsimp [L];omega)
  have hu : (signedBits (u/divisor u v)).length≤L := (quotient_bits_le u _).trans (by dsimp [L];omega)
  have hv' : (signedBits (v/divisor u v)).length≤L := (quotient_bits_le v _).trans (by dsimp [L];omega)
  obtain ⟨ca,ha,hab⟩:=arithmetic_executes g u v (divisor u v) rfl
    (divisor_ne_zero u v hv) (divisor_dvd_left u v) (divisor_dvd_right u v) L
    (by dsimp [L];omega) (by dsimp [L];omega) hd hu hv'
  obtain ⟨cf,hf,hfb⟩:=finish_executes g (u/divisor u v) (v/divisor u v) (divisor u v) L hu hv' hd
  rw [canonical_num u v hv,canonical_den u v hv] at hf
  refine ⟨_,seq_executes _ _ g ha hf,?_⟩
  change ca+cf+2≤time.eval L
  simp only [time,eval_add,eval_mul,eval_ofNat,eval_X]
  omega

noncomputable def prepareBinary : OracleBlock 15 :=
  seq (moveOn 0 9 2 (by decide) (by decide) (by decide))
    (moveOn 1 10 2 (by decide) (by decide) (by decide))
noncomputable def binaryProgram : OracleBlock 15 := seq prepareBinary program
noncomputable def binaryTime : Polynomial ℕ := time+6*X+14

lemma prepareBinary_executes (g : BitString → ℕ) (u v : BitString) :
    prepareBinary.Executes g (binaryStore u v) (regState u v []) (6*u.length+6*v.length+12) := by
  have h1 : (moveOn (0:Fin 16) 9 2 (by decide) (by decide) (by decide)).Executes g
      (binaryStore u v) (Function.update (Function.update (binaryStore u v) 9 u) 0 []) (6*u.length+5) := by
    convert moveOn_executes g (0:Fin 16) 9 2 (by decide) (by decide) (by decide) (binaryStore u v) rfl using 1
    simp [binaryStore]
  have h2 : (moveOn (1:Fin 16) 10 2 (by decide) (by decide) (by decide)).Executes g
      (Function.update (Function.update (binaryStore u v) 9 u) 0 []) (regState u v []) (6*v.length+5) := by
    convert moveOn_executes g (1:Fin 16) 10 2 (by decide) (by decide) (by decide)
      (Function.update (Function.update (binaryStore u v) 9 u) 0 []) rfl using 1
    · funext i;fin_cases i <;> simp [binaryStore,regState,RegisterMachine.store,regs]
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

theorem binaryProgram_executes (g : BitString → ℕ) (u v : ℤ) (hv : v≠0) :
    ∃c,binaryProgram.Executes g (binaryStore (signedBits u) (signedBits v))
      (Function.update (fun _=>[]) 0 (RationalOracleEncoding.bits ((u:ℚ)/(v:ℚ)))) c ∧
      c≤binaryTime.eval ((signedBits u).length+(signedBits v).length) := by
  obtain ⟨c,hc,hcb⟩:=program_executes g u v hv
  refine ⟨_,seq_executes _ _ g (prepareBinary_executes g (signedBits u) (signedBits v)) hc,?_⟩
  simp only [binaryTime,eval_add,eval_mul,eval_ofNat,eval_X]
  omega
lemma prepareBinary_queryFree : prepareBinary.QueryFree :=
  seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (moveOn_queryFree _ _ _ _ _ _)
lemma binaryProgram_queryFree : binaryProgram.QueryFree :=
  seq_queryFree _ _ prepareBinary_queryFree program_queryFree

end HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalize
