import HiddenCircuits.Circuit.Runtime.SpectralConstraintDriver
import HiddenCircuits.Complexity.NativeValidation.Guard

/-! Independent Lemma 7.2 as a total natural-function polynomial Turing
reduction. A physical validator sends malformed bytes to literal natural zero. -/
namespace HiddenCircuits.Circuit.Runtime.ConstraintRawReduction
open Complexity OracleBlock Polynomial
noncomputable def program : OracleBlock 98:=NativeValidation.Guard.constraintProgram SpectralConstraintEvaluation.program
noncomputable def time : Polynomial ℕ:=NativeValidation.Guard.time SpectralConstraintEvaluation.time
lemma solverSpec (g : BitString→ℕ) (hg : DeltaOracle g) :
    RawValidationGuard.SolverSpec NativeValidation.Guard.constraintInput SpectralConstraintEvaluation.program SpectralConstraintEvaluation.time g :=
  SpectralConstraintEvaluation.native_executes g hg

theorem program_executes (g : BitString→ℕ) (hg : DeltaOracle g) (xs : BitString) :
    ∃c,program.Executes g (Function.update (fun _=>[]) 0 xs)
      (Function.update (fun _=>[]) 0 (Computability.encodeNat (constraintProblem xs))) c ∧ c ≤ time.eval xs.length :=
  NativeValidation.Guard.constraint_executes _ _ g (solverSpec g hg) xs

theorem reduction_of_oracle (g : BitString→ℕ) (hg : DeltaOracle g) : PolyTuringReduction constraintProblem g :=
  NativeValidation.Guard.constraint_reduction _ _ g (solverSpec g hg)
theorem constraintEval_le_deltaEval : PolyTuringReduction constraintProblem deltaProblem :=
  reduction_of_oracle deltaProblem deltaProblem_oracle
end HiddenCircuits.Circuit.Runtime.ConstraintRawReduction
