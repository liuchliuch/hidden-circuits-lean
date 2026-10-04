import HiddenCircuits.Complexity.PolynomialBounds
import HiddenCircuits.Approximation.SamplerRuntime.GraphFunctional
import HiddenCircuits.Approximation.SelfReduction.UniformParameters

/-! Fixed original-input random budgets for every dense induced graph.
Neither random-bit generation nor runtime parameters depend on random outcomes. -/
namespace HiddenCircuits.Approximation.SelfReduction.GraphCount
open Complexity SamplerRuntime Polynomial

def inputBound (b k : ℕ) : ℕ := 2*(b+1)^2+4*(b+1)+k+3
noncomputable def sampleBits (b k : ℕ) : ℕ := GraphFunctional.bitsPolynomial.eval (inputBound b k)

lemma sampleInput_bound {b n : ℕ} (G : MatrixGraph n) (hn:n ≤ b+1) (k : ℕ) :
    (sampleInput (GraphInput.encode ⟨n,G⟩) k).length ≤ inputBound b k := by
  simp only [sampleInput_length,GraphInput.encode,pairBits_length,List.length_replicate,MatrixGraph.bits_length]
  unfold inputBound
  have hh:=Nat.pow_le_pow_left hn 2
  nlinarith

lemma sampleBits_bound {b n : ℕ} (G : MatrixGraph n) (hn:n ≤ b+1) (k : ℕ) :
    3*((sampleInput (GraphInput.encode ⟨n,G⟩) k).length+1)^4+
      PartnerBudget.bits ((sampleInput (GraphInput.encode ⟨n,G⟩) k).length+1) ≤ sampleBits b k := by
  rw [←GraphFunctional.bits_eval]
  exact polynomial_nat_eval_mono GraphFunctional.bitsPolynomial (sampleInput_bound G hn k)

noncomputable def uniformSampleInputPolynomial : Polynomial ℕ :=
  2*(X+1)^2+4*(X+1)+24*(X+1)^3+3
noncomputable def uniformSampleBitsPolynomial : Polynomial ℕ :=
  GraphFunctional.bitsPolynomial.comp uniformSampleInputPolynomial
@[simp] lemma uniformSampleBits_eval (N : ℕ) :
    uniformSampleBitsPolynomial.eval N=sampleBits N (uniformAccuracy N) := by
  simp [uniformSampleBitsPolynomial,uniformSampleInputPolynomial,sampleBits,inputBound,uniformAccuracy]
lemma sampleBits_mono_cap {b N : ℕ} (hb:b ≤ N) (k : ℕ) : sampleBits b k ≤ sampleBits N k := by
  unfold sampleBits
  apply polynomial_nat_eval_mono GraphFunctional.bitsPolynomial
  unfold inputBound
  gcongr
lemma uniformSampleBits_sufficient {b : ℕ} (N : ℕ) (hb:b ≤ N) :
    sampleBits b (uniformAccuracy N) ≤ uniformSampleBitsPolynomial.eval N := by
  rw [uniformSampleBits_eval]
  exact sampleBits_mono_cap hb _

noncomputable def randomBitsPolynomial : Polynomial ℕ := uniformCountingBitsPolynomial uniformSampleBitsPolynomial
lemma countingBits_polynomial_bound (N d : ℕ) (hd:d ≤ N) :
    countingBits (uniformSampleBitsPolynomial.eval N) (uniformAccuracy N) (uniformConfidence N) d ≤
      randomBitsPolynomial.eval N := countingBits_le_uniform uniformSampleBitsPolynomial N d hd
end HiddenCircuits.Approximation.SelfReduction.GraphCount
