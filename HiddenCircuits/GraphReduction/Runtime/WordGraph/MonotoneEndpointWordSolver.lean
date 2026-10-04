import HiddenCircuits.GraphReduction.Runtime.WordGraph.EndpointDriverModel
import HiddenCircuits.GraphReduction.Runtime.WordGraph.MonotoneEndpointAnswer

/-! A fixed136-port native endpoint oracle solver. Its actual query wrapper
constructs and emits the endpoint arrays, then ordinary signed interpolation
recovers WordEval; no graph oracle or arithmetic certificate is substituted. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.MonotoneEndpointDriver
open Complexity OracleBlock BinaryArithmetic Polynomial
noncomputable def program : OracleBlock 135 := EndpointDriver.program MonotoneEndpointAnswer.program
noncomputable def time : Polynomial ℕ := EndpointDriver.time MonotoneEndpointAnswer.time

theorem program_executes (g : BitString → ℕ) (w : WordInstance)
    (hg : w.word≠[] → EndpointDriver.CorrectOracle g MonotoneEndpointAnswer.queryBits w) :
    ∃z : ℤ, ∃c, program.Executes g (Function.update (fun _ => []) 0 (wordBits w))
      (Function.update (fun _ => []) 0 (signedBits z)) c ∧ w.value=(z:ℚ) ∧ c ≤ time.eval (wordBits w).length :=
  EndpointDriver.program_executes MonotoneEndpointAnswer.program g MonotoneEndpointAnswer.queryBits
    MonotoneEndpointAnswer.time (MonotoneEndpointAnswer.program_polynomial g) w hg
end HiddenCircuits.GraphReduction.Runtime.WordGraph.MonotoneEndpointDriver
