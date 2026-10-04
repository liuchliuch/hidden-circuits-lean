import HiddenCircuits.Approximation.SamplerRuntime.MonotoneSampler
import HiddenCircuits.Approximation.SamplerRuntime.CorePadding

/-! Finite-tape padding for the monotone sampler. -/

/-! Finite-tape padding for the monotone sampler. -/
namespace HiddenCircuits.Approximation.SamplerRuntime
open Complexity GraphReduction.MonotoneEndpointEncoding FiniteChains
attribute [local instance] Classical.propDecidable

namespace MonotonePadding

lemma size_bounds (E : Input) (k : ℕ) : E.1≤(sampleInput (encode E) k).length ∧ k≤(sampleInput (encode E) k).length := by
  have hn := Functional.size_le_encode E
  rw [sampleInput_length]
  omega

/-- Extra coins do not change the actual canonical sampler output. -/
theorem evaluate_append (E : Input) (k : ℕ) (coins padding : BitString)
    (h : Budget.bits (sampleInput (encode E) k).length≤coins.length) :
    Functional.evaluate (pairBits (sampleInput (encode E) k) (coins++padding))=
      Functional.evaluate (pairBits (sampleInput (encode E) k) coins) := by
  rw [Functional.evaluate_canonical,Functional.evaluate_canonical]
  apply Core.evaluate_append
  exact (Budget.tape_budget (size_bounds E k).1).trans h

/-- Exact identification with the prefix of an arbitrarily larger fair tape. -/
theorem evaluate_ofFn_restrict (E : Input) (k m : ℕ)
    (h : Budget.bits (sampleInput (encode E) k).length≤m) (r : CoinTape m) :
    Functional.evaluate (pairBits (sampleInput (encode E) k) (List.ofFn r))=
      Functional.evaluate (pairBits (sampleInput (encode E) k) (List.ofFn (CoinLists.restrictTape h r))) := by
  let need := Budget.bits (sampleInput (encode E) k).length
  have he : List.ofFn r=List.ofFn (CoinLists.restrictTape h r)++(List.ofFn r).drop need := by
    rw [CoinLists.restrict_ofFn]
    exact (List.take_append_drop need (List.ofFn r)).symm
  rw [he]
  exact evaluate_append E k (List.ofFn (CoinLists.restrictTape h r)) ((List.ofFn r).drop need)
    (by simp only [List.length_ofFn];exact le_rfl)

/-- Fixed globally padded independent fair tapes retain the same unconditional
sampling guarantee on every canonical residual endpoint instance. -/
theorem event_error (E : Input) (k m : ℕ)
    (h : Budget.bits (sampleInput (encode E) k).length≤m) (A : Option BitString → Prop) :
    |coinProbability m (fun r => A (decodeSample (Functional.evaluate
      (pairBits (sampleInput (encode E) k) (List.ofFn r)))))-
      uniformProbability (Output.solutions (encode E)) A|≤1/(2^k:ℚ) := by
  simp_rw [evaluate_ofFn_restrict E k m h]
  rw [CoinLists.probability_restrict h (fun r => A (decodeSample (Functional.evaluate
    (pairBits (sampleInput (encode E) k) (List.ofFn r)))))]
  simp only [Functional.evaluate_canonical,Output.solutions_encode]
  exact Core.evaluate_event_error E.2 _ k (size_bounds E k).1 (size_bounds E k).2 A

lemma randomProgram_bits (E : Input) (k : ℕ) :
    MonotoneSampler.randomProgram.bits (sampleInput (encode E) k)=Budget.bits (sampleInput (encode E) k).length :=
  Functional.bits_eq MonotoneSampler.evaluate_polyTime _

end MonotonePadding
end HiddenCircuits.Approximation.SamplerRuntime
