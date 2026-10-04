import HiddenCircuits.GraphReduction.Runtime.WordGraph.EndpointDriverModel
import HiddenCircuits.GraphReduction.Runtime.WordGraph.MonotonePermutationAnswer

/-! A fixed 136-port supplied-permutation-diagram oracle solver. Its actual query wrapper
constructs and emits the two endpoint-rank vectors, then ordinary signed interpolation
recovers WordEval; no graph oracle or arithmetic certificate is substituted. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.MonotonePermutationDriver
open Complexity OracleBlock BinaryArithmetic Polynomial
noncomputable def program : OracleBlock 135 := EndpointDriver.program MonotonePermutationAnswer.program
noncomputable def time : Polynomial ℕ := EndpointDriver.time MonotonePermutationAnswer.time

theorem program_executes (g : BitString → ℕ) (w : WordInstance)
    (hg : w.word≠[] → EndpointDriver.CorrectOracle g MonotonePermutationAnswer.queryBits w) :
    ∃z : ℤ, ∃c, program.Executes g (Function.update (fun _ => []) 0 (wordBits w))
      (Function.update (fun _ => []) 0 (signedBits z)) c ∧ w.value=(z:ℚ) ∧ c ≤ time.eval (wordBits w).length :=
  EndpointDriver.program_executes MonotonePermutationAnswer.program g MonotonePermutationAnswer.queryBits
    MonotonePermutationAnswer.time (MonotonePermutationAnswer.program_polynomial g) w hg
end HiddenCircuits.GraphReduction.Runtime.WordGraph.MonotonePermutationDriver
