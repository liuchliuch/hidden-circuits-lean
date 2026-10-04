import HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueWordSolver
import HiddenCircuits.GraphReduction.Runtime.WordGraph.PrivateBothQueryAnswer

/-! A genuine signed word solver using the simultaneously supplied representations. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.PrivateBothDriver
open Complexity OracleBlock BinaryArithmetic Polynomial

noncomputable def program : OracleBlock 97 :=
  GenericDriver.program (CliqueDriver.cell PrivateBothQueryAnswer.program true)
noncomputable def time : Polynomial ℕ :=
  GenericDriver.time CliqueDriver.accumulatorP (CliqueDriver.cellTime PrivateBothQueryAnswer.time)

theorem program_executes (g : BitString → ℕ) (w : WordInstance)
    (hg : w.word ≠ [] → CliqueDriver.CorrectOracle g PrivateBothWordQuery.queryBits true w) :
    ∃ z : ℤ, ∃ c, program.Executes g (Function.update (fun _ => []) 0 (wordBits w))
      (Function.update (fun _ => []) 0 (signedBits z)) c ∧ w.value=(z:ℚ) ∧
      c ≤ time.eval (wordBits w).length := by
  apply GenericDriver.program_executes (CliqueDriver.cell PrivateBothQueryAnswer.program true) g w
    (CliqueDriver.term true w) CliqueDriver.accumulatorP (CliqueDriver.cellTime PrivateBothQueryAnswer.time)
  intro hw
  exact CliqueDriver.modelSpec PrivateBothQueryAnswer.program g PrivateBothWordQuery.queryBits
    PrivateBothQueryAnswer.time (PrivateBothQueryAnswer.program_polynomial g) true w hw (hg hw)

end HiddenCircuits.GraphReduction.Runtime.WordGraph.PrivateBothDriver
