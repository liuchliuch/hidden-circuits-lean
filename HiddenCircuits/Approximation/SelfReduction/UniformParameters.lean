import HiddenCircuits.Approximation.SelfReduction.CoinExperiment

/-! Global input-length caps for the actual compiler. All loop budgets can be
computed once from unary input size, then reused on every induced instance. -/
namespace HiddenCircuits.Approximation.SelfReduction

def uniformAccuracy (N : ℕ) : ℕ := 24*(N+1)^3
def uniformConfidence (N : ℕ) : ℕ := 3*N

 theorem accuracyBudget_le_uniform (b d r N : ℕ) (hb : b ≤ N) (hd : d ≤ N) (hr : r ≤ N) :
    accuracyBudget b d r ≤ uniformAccuracy N := by
  unfold accuracyBudget uniformAccuracy
  calc
    _ ≤ 24*(N+1)*(N+1)*(N+1) := by gcongr
    _ = _ := by ring

 theorem confidenceBudget_le_uniform (b d k N : ℕ) (hb : b ≤ N) (hd : d ≤ N) (hk : k ≤ N) :
    confidenceBudget b d k ≤ uniformConfidence N := by unfold confidenceBudget uniformConfidence; omega

/-- Increasing either runtime budget preserves the complete derived guarantee. -/
theorem counting_oversized_dyadic_failure {S α : Type*} [Fintype α] [Nonempty α] {b : ℕ}
    (R : CountReduction S b) (sampler : S → α → Option (Fin (b+1))) (d r k T h : ℕ)
    (hT : accuracyBudget b d r ≤ T) (hh : confidenceBudget b d k ≤ h)
    (hbias : ∀ s, 0 < R.count s → 0 < R.rank s → ∀ i,
      |probability (fun a => sampler s a=some i)-R.branchProbability s i| ≤ 1/(2^T : ℚ))
    (s : S) (hc : 0 < R.count s) (hrank : R.rank s=d) :
    probability (fun tape => ¬RelativeEstimate (R.count s) r (countingEstimate R sampler T h d s tape)) ≤
      1/(2^k : ℚ) := by
  have hT0 : 0 < T := (accuracyBudget_pos b d r).trans_le hT
  have hTq : (accuracyBudget b d r : ℚ) ≤ T := by exact_mod_cast hT
  have hη : 12*(b+1 : ℚ)/T ≤ 12*(b+1 : ℚ)/(accuracyBudget b d r : ℚ) :=
    div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast accuracyBudget_pos b d r) hTq
  have hbias' : ∀ s, 0 < R.count s → 0 < R.rank s → ∀ i,
      |probability (fun a => sampler s a=some i)-R.branchProbability s i| ≤ 1/(T : ℚ) := by
    intro s hs hsr i
    exact (hbias s hs hsr i).trans (dyadic_le_reciprocal T hT0)
  have hs := counting_failure_bound R sampler T h d r hT0 ((accuracyBudget_large b d r).trans hTq)
    (hη.trans (localTolerance_le_one b d r))
    ((mul_le_mul_of_nonneg_left hη (Nat.cast_nonneg _)).trans (accumulatedTolerance_small b d r))
    ((mul_le_mul_of_nonneg_left hη (by positivity)).trans (accumulatedTolerance_accuracy b d r)) hbias' s hc hrank
  apply hs.trans
  apply le_trans _ (confidence_union_bound b d k)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right hh 1)

 theorem counting_uniform_dyadic_failure {S α : Type*} [Fintype α] [Nonempty α] {b : ℕ}
    (R : CountReduction S b) (sampler : S → α → Option (Fin (b+1))) (d r k N : ℕ)
    (hb : b ≤ N) (hd : d ≤ N) (hr : r ≤ N) (hk : k ≤ N)
    (hbias : ∀ s, 0 < R.count s → 0 < R.rank s → ∀ i,
      |probability (fun a => sampler s a=some i)-R.branchProbability s i| ≤ 1/(2^(uniformAccuracy N) : ℚ))
    (s : S) (hc : 0 < R.count s) (hrank : R.rank s=d) :
    probability (fun tape => ¬RelativeEstimate (R.count s) r
      (countingEstimate R sampler (uniformAccuracy N) (uniformConfidence N) d s tape)) ≤ 1/(2^k : ℚ) :=
  counting_oversized_dyadic_failure R sampler d r k _ _ (accuracyBudget_le_uniform b d r N hb hd hr)
    (confidenceBudget_le_uniform b d k N hb hd hk) hbias s hc hrank

/-- The global tape budget is polynomial even after paying for every requested
sampler bit in every sample, confidence repetition and deletion stage. -/
noncomputable def uniformCountingBitsPolynomial (samplerBits : Polynomial ℕ) : Polynomial ℕ :=
  2304*Polynomial.X*(3*Polynomial.X+1)*(Polynomial.X+1)^6*samplerBits

 theorem countingBits_le_uniform (samplerBits : Polynomial ℕ) (N d : ℕ) (hd : d ≤ N) :
    countingBits (samplerBits.eval N) (uniformAccuracy N) (uniformConfidence N) d ≤
      (uniformCountingBitsPolynomial samplerBits).eval N := by
  unfold countingBits uniformAccuracy uniformConfidence batchSize uniformCountingBitsPolynomial
  simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_add,
    Polynomial.eval_one,Polynomial.eval_pow]
  calc
    d*(2*(3*N+1)*(2*(24*(N+1)^3)^2*samplerBits.eval N)) ≤
        N*(2*(3*N+1)*(2*(24*(N+1)^3)^2*samplerBits.eval N)) := by gcongr
    _ = _ := by ring

end HiddenCircuits.Approximation.SelfReduction
