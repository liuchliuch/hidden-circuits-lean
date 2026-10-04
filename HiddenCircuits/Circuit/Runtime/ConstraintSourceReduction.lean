import HiddenCircuits.Circuit.Runtime.ConstraintSourceDriver

/-! The total natural-coded CircuitEval problem is genuinely #P-hard. The
canonical graph compiler is direct; the existing machine-grounded #P foundation
also supplies the all-raw #IS function-level Turing-reduction statement. -/
namespace HiddenCircuits.Circuit.Runtime.ConstraintSource
open Complexity

theorem independentSet_to_constraintOracle (g : BitString→ℕ) (hg : ConstraintOracle g) :
    PolyTuringReduction GraphInput.independentSetProblem g :=
  sharpPHard_of_oracle g hg _ GraphVerifier.Runtime.independentSet_sharpP

theorem independentSet_to_constraintEval : PolyTuringReduction GraphInput.independentSetProblem constraintProblem :=
  independentSet_to_constraintOracle constraintProblem constraintProblem_oracle
end HiddenCircuits.Circuit.Runtime.ConstraintSource
