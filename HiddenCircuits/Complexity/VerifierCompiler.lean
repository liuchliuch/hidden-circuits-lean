import HiddenCircuits.Complexity.NegativeCompiler
import HiddenCircuits.Complexity.OracleCleanup

/-! A uniform, parsimonious Cook compiler from an arbitrary genuine polynomial
TM2 verifier. The choice of finite code depends only on the fixed verifier and
witness polynomial. Every variable input is processed by the proved bit-stack
instructions, including initial, transition, accepting and rejecting clauses. -/
namespace HiddenCircuits.Complexity.VerifierCompiler
open OracleBlock
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v) (p : Polynomial ℕ)

noncomputable def program : OracleBlock 17 := by
  classical
  exact if ht : VerifierTableau.HasTrueSymbol M then PositiveCompiler.program M p ht
    else NegativeCompiler.program M p

noncomputable def time : Polynomial ℕ := by
  classical
  exact if ht : VerifierTableau.HasTrueSymbol M then PositiveCompiler.time M p ht
    else NegativeCompiler.time M p

noncomputable def emit (x : BitString) : BitString :=
  CNFInput.encode (VerifierTableau.uniformFormula M x (p.eval x.length))

theorem program_executes (g : BitString → ℕ) (x : BitString) :
    ∃ s : Store 17, ∃ cost, (program M p).Executes g
      (Function.update (fun _ => []) 0 x) s cost ∧
      s 0 = emit M p x ∧ cost ≤ (time M p).eval x.length := by
  classical
  by_cases ht : VerifierTableau.HasTrueSymbol M
  · simp only [program,time,dif_pos ht,emit]
    rw [VerifierTableau.uniformFormula_pos M x (p.eval x.length) ht]
    exact PositiveCompiler.program_executes M p g ht x
  · simp only [program,time,dif_neg ht,emit]
    rw [VerifierTableau.uniformFormula_neg M x (p.eval x.length) ht]
    exact NegativeCompiler.program_executes M p g x

lemma program_queryFree : (program M p).QueryFree := by
  classical
  by_cases ht : VerifierTableau.HasTrueSymbol M
  · simpa only [program,dif_pos ht] using PositiveCompiler.program_queryFree M p ht
  · simpa only [program,dif_neg ht] using NegativeCompiler.program_queryFree M p

/-- The compiler is polynomial time in the actual mathlib machine model. -/
theorem emit_polyTime : PolyTime (emit M p) :=
  polyTime_of_block (program M p) (program_queryFree M p) (time M p)
    (program_executes M p (fun _ => 0))

/-- Every accepting certificate extends uniquely to its full computation
assignment; there is no auxiliary-assignment multiplicity. -/
theorem emit_count (x : BitString) :
    CNFInput.satProblem (emit M p x) = certificateCount v x (p.eval x.length) := by
  rw [emit,CNFInput.satProblem_encode,VerifierTableau.uniformFormula_count]

lemma emit_length (x : BitString) :
    (emit M p x).length ≤ (VerifierTableau.formulaSizePolynomial M p).eval x.length :=
  VerifierTableau.uniformFormula_polynomial_size M p x

end HiddenCircuits.Complexity.VerifierCompiler
