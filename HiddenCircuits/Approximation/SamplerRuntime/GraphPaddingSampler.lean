import HiddenCircuits.Approximation.SamplerRuntime.GraphPadding
import HiddenCircuits.Approximation.SamplerRuntime.GraphSampler

/-! Canonical budget and padded law of the compiled raw graph random program. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.GraphPadding
open Complexity GraphReduction FiniteChains
attribute [local instance] Classical.propDecidable

lemma randomProgram_bits (G : GraphInput) (k : ℕ) :
    GraphSampler.randomProgram.bits (sampleInput G.encode k)=
      3*((sampleInput G.encode k).length+1)^4+
        PartnerBudget.bits ((sampleInput G.encode k).length+1) :=
  GraphFunctional.bits_eq GraphSampler.evaluate_polyTime _

/-- Polynomial notation for the literal sufficient random prefix. -/
theorem core_event_error_polynomial {n : ℕ} (G : MatrixGraph n) (hG : Quasimonotone G.graph)
    (N k m : ℕ) (hn : n≤N) (hk : k+1≤N)
    (h : 3*N^4+PartnerBudget.bitsPolynomial.eval N ≤ m) (A : Option BitString → Prop) :
    |coinProbability m (fun r => A (decodeSample (GraphFunctional.core G N (List.ofFn r))))-
      uniformProbability (PartnerOutput.witnesses G) A|≤1/(2^k:ℚ) :=
  core_event_error G hG N k m hn hk (by simpa only [PartnerBudget.bits_eval] using h) A

/-- Fair tapes of any dominating length satisfy the actual random program's law. -/
theorem randomProgram_event_error (G : GraphInput) (hG : Quasimonotone G.2.graph) (k m : ℕ)
    (h : GraphSampler.randomProgram.bits (sampleInput G.encode k) ≤ m) (A : Option BitString → Prop) :
    |coinProbability m (fun r => A (decodeSample (GraphSampler.randomProgram.evaluate
      (pairBits (sampleInput G.encode k) (List.ofFn r)))))-
      uniformProbability (GraphFunctional.solutions G.encode) A|≤1/(2^k:ℚ) := by
  exact event_error G hG k m (by simpa only [randomProgram_bits] using h) A

end HiddenCircuits.Approximation.SamplerRuntime.GraphPadding
