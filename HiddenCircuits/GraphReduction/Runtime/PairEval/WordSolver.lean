import HiddenCircuits.GraphReduction.Runtime.PairEval.WordCell
import HiddenCircuits.Circuit.Runtime.SourceHardness

/-! The standalone PairEval oracle is #P-hard by a concrete finite signed
WordEval solver, with every frontend, arithmetic cell and bit bound discharged. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.WordSolver
open Complexity OracleBlock BinaryArithmetic Polynomial WordGraph

noncomputable def program : OracleBlock 97 := GenericDriver.program WordCell.program
noncomputable def time : Polynomial ℕ := GenericDriver.time Driver.accumulatorP WordCell.time

lemma modelSpec (g : BitString→ℕ) (hg : WordCell.oracleSpec g) (w : WordInstance) (hw : w.word≠[]) :
    GenericDriver.ModelSpec WordCell.program g w (WordRecovery.term w) Driver.accumulatorP WordCell.time :=
  ⟨WordCell.program_spec g hg w hw,WordRecovery.initialBitBound w hw,
    WordRecovery.term_nonzero w,WordRecovery.terms_value w⟩

theorem program_executes (g : BitString→ℕ) (hg : WordCell.oracleSpec g) (w : WordInstance) :
    ∃z : ℤ,∃c,program.Executes g (Function.update (fun _=>[]) 0 (wordBits w))
      (Function.update (fun _=>[]) 0 (signedBits z)) c ∧ w.value=(z:ℚ) ∧ c≤time.eval (wordBits w).length :=
  GenericDriver.program_executes WordCell.program g w (WordRecovery.term w) Driver.accumulatorP WordCell.time (modelSpec g hg w)

lemma solverSpec (g : BitString→ℕ) (hg : WordCell.oracleSpec g) :
    Circuit.Runtime.SourceWordCall.WordSolverSpec program g time := program_executes g hg

/-- Lemma 3.3: the finite program works for every WordEval input, including
empty words, and its polynomial is measured in the canonical input bytes. -/
theorem wordEval_to_pairEval :
    Circuit.Runtime.SourceWordCall.WordSolverSpec program pairEval time := solverSpec pairEval WordCell.problem_spec

/-- Theorem 8.2, standalone natural-valued PairEval target. -/
theorem sharpPHard_of_oracle (g : BitString→ℕ) (hg : WordCell.oracleSpec g) : SharpPHard g :=
  Circuit.Runtime.SourceReduction.sharpPHard program g time (solverSpec g hg)
theorem pairEval_sharpPHard : SharpPHard pairEval := sharpPHard_of_oracle pairEval WordCell.problem_spec

/-- Exactly the nonnegative pair instances scheduled by the outer interpolation.
The finite cell queries only when its physical inner counter is empty. -/
def samples (w : WordInstance) (hw : w.word≠[]) : List PairInput :=
  (List.finRange (Recovery.degree w+1)).map (fun t=>WordQuery.sampleInput w hw t.val)
lemma samples_length (w : WordInstance) (hw : w.word≠[]) :
    (samples w hw).length=w.word.length*w.particles^2+1 := by simp [samples,Recovery.degree]
lemma sample_pairs (w : WordInstance) (hw : w.word≠[]) (t : Fin (Recovery.degree w+1)) :
    (WordQuery.sampleInput w hw t.val).pairs.length=w.word.length*(t.val+1) := sampleWord_length _ _
end HiddenCircuits.GraphReduction.Runtime.PairEval.WordSolver
