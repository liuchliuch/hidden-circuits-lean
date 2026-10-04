import HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidualUniform

/-! Closed one-variable polynomial clocks for globally padded endpoint sampling
and the full uniform finite counting experiment. -/
namespace HiddenCircuits.Approximation.SelfReduction.EndpointResidual
open Complexity SamplerRuntime Polynomial

noncomputable def uniformSampleInputPolynomial : Polynomial ℕ :=
  16*(X+1)^2+20*(X+1)+24*(X+1)^3+13
noncomputable def uniformSampleBitsPolynomial : Polynomial ℕ :=
  Budget.bitsPolynomial.comp uniformSampleInputPolynomial

@[simp] lemma uniformSampleBits_eval (N : ℕ) :
    uniformSampleBitsPolynomial.eval N=sampleBits N (uniformAccuracy N) := by
  simp [uniformSampleBitsPolynomial,uniformSampleInputPolynomial,sampleBits,inputBound,uniformAccuracy]

lemma sampleBits_mono_cap {b N : ℕ} (hb : b ≤ N) (k : ℕ) : sampleBits b k ≤ sampleBits N k := by
  unfold sampleBits
  rw [←Budget.bits_eval,←Budget.bits_eval]
  apply polynomial_nat_eval_mono Budget.bitsPolynomial
  unfold inputBound
  gcongr

/-- A single polynomially evaluated random-block length dominates every active
residual, independently of which previous sampled branches were selected. -/
theorem uniformSampleBits_sufficient {b : ℕ} (N : ℕ) (hb : b ≤ N) :
    sampleBits b (uniformAccuracy N) ≤ uniformSampleBitsPolynomial.eval N := by
  rw [uniformSampleBits_eval]
  exact sampleBits_mono_cap hb _

noncomputable def randomBitsPolynomial : Polynomial ℕ := uniformCountingBitsPolynomial uniformSampleBitsPolynomial

lemma countingBits_polynomial_bound (N d : ℕ) (hd : d ≤ N) :
    countingBits (uniformSampleBitsPolynomial.eval N) (uniformAccuracy N) (uniformConfidence N) d ≤ 
      randomBitsPolynomial.eval N := countingBits_le_uniform uniformSampleBitsPolynomial N d hd

/-- The oversized endpoint estimator therefore has a closed fair-bit success
statement with an explicitly polynomial global sample-block budget. -/
theorem polynomial_uniform_guarantee {b : ℕ} (N d r k : ℕ)
    (hb : b ≤ N) (hd : d ≤ N) (hr : r ≤ N) (hk : k ≤ N) (s : State b) (hrank : rank s=d) :
    (count s=0 → ∀tape,decodeEstimate (uniformOutput N (uniformSampleBitsPolynomial.eval N) d s tape)=some 0) ∧
    1-1/(2^k:ℚ) ≤ coinProbability
      (countingBits (uniformSampleBitsPolynomial.eval N) (uniformAccuracy N) (uniformConfidence N) d)
      (fun tape => ∃z,decodeEstimate (uniformOutput N (uniformSampleBitsPolynomial.eval N) d s tape)=some z ∧
        RelativeEstimate (count s) r z) :=
  uniformOutput_guarantee N _ d r k hb hd hr hk (uniformSampleBits_sufficient N hb) s hrank
end HiddenCircuits.Approximation.SelfReduction.EndpointResidual
