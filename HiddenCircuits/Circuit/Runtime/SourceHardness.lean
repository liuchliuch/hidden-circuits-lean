import HiddenCircuits.Circuit.Runtime.SourceReductionProgram
import HiddenCircuits.Complexity.CanonicalSubstitution.Program

/-! The closed #P-to-WordEval operational reduction. Target instantiation only
requires the actual signed-word program contract, never a hardness assumption. -/
namespace HiddenCircuits.Circuit.Runtime.SourceReduction
open HiddenCircuits.Complexity OracleBlock Polynomial

theorem sharpPHard {k : ℕ} (W : OracleBlock k) (g : BitString → ℕ) (p : Polynomial ℕ)
    (hW : SourceWordCall.WordSolverSpec W g p) : SharpPHard g := by
  apply sharpPHard_of_canonical_independent_block g (program W) (time k p)
  intro G
  obtain ⟨c,hc,hb⟩ := program_executes W g p hW G
  exact ⟨_,c,hc,Function.update_self _ _ _,hb⟩
end HiddenCircuits.Circuit.Runtime.SourceReduction
