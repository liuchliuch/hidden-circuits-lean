import HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidualSampler

/-! Explicit single global fair-tape size for every canonical residual whose
dimension is bounded by the original candidate cap. -/
namespace HiddenCircuits.Approximation.SelfReduction.EndpointResidual
open Complexity GraphReduction SamplerRuntime GraphReduction.MonotoneEndpointEncoding

def inputBound (b k : ℕ) : ℕ := 16*(b+1)^2+20*(b+1)+k+13
def sampleBits (b k : ℕ) : ℕ := Budget.bits (inputBound b k)

lemma sampleInput_bound {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1 ≤ b+1) (k : ℕ) :
    (sampleInput (encode ⟨d+1,E⟩) k).length ≤  inputBound b k := by
  have henc := encode_length ⟨d+1,E⟩
  have hpow := Nat.pow_le_pow_left hE 2
  rw [sampleInput_length]
  dsimp only at henc
  unfold inputBound
  nlinarith

lemma sampleBits_bound {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1 ≤ b+1) (k : ℕ) :
    Budget.bits (sampleInput (encode ⟨d+1,E⟩) k).length ≤ sampleBits b k := by
  unfold sampleBits
  rw [←Budget.bits_eval,←Budget.bits_eval]
  exact polynomial_nat_eval_mono Budget.bitsPolynomial (sampleInput_bound E hE k)

/-- Closed bias theorem for the concrete globally padded sampler: no residual
budget or sampling correctness hypothesis is supplied by the caller. -/
theorem padded_sample_bias {b : ℕ} (k : ℕ) (s : State b) (hc : 0<count s) (hr : 0<rank s)
    (j : Fin (b+1)) :
    |coinProbability (sampleBits b k) (fun r => sample k (sampleBits b k) s r=some j)-
      (reduction b).branchProbability s j| ≤ 1/(2^k:ℚ) :=
  sample_bias k (sampleBits b k) (fun _ E hE => sampleBits_bound E hE k) s hc hr j
end HiddenCircuits.Approximation.SelfReduction.EndpointResidual
