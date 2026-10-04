import HiddenCircuits.Approximation.SelfReduction.Counting

/-! Explicit polynomial accuracy
and confidence budgets and their statistical counting specialization. -/
namespace HiddenCircuits.Approximation.SelfReduction

def accuracyBudget (b d r : ℕ) : ℕ := 24*(b+1)*(d+1)*(r+1)
def confidenceBudget (b d k : ℕ) : ℕ := k+d+b

theorem accuracyBudget_pos (b d r : ℕ) : 0 < accuracyBudget b d r := by
  unfold accuracyBudget; positivity

private theorem accuracy_cast (b d r : ℕ) :
    (accuracyBudget b d r : ℚ)=24*(b+1)*(d+1)*(r+1) := by simp [accuracyBudget]

theorem accuracyBudget_large (b d r : ℕ) : (24 : ℚ)*(b+1) ≤ accuracyBudget b d r := by
  rw [accuracy_cast]
  have h1 : (24 : ℚ)*(b+1) ≤ 24*(b+1)*(d+1) := le_mul_of_one_le_right (by positivity) (by norm_cast; omega)
  exact h1.trans (le_mul_of_one_le_right (by positivity) (by norm_cast; omega))

theorem localTolerance_le_one (b d r : ℕ) :
    12*(b+1 : ℚ)/(accuracyBudget b d r : ℚ) ≤ 1 := by
  apply (div_le_iff₀ (by exact_mod_cast accuracyBudget_pos b d r)).2
  have h := accuracyBudget_large b d r
  nlinarith

theorem accumulatedTolerance_small (b d r : ℕ) :
    (d : ℚ)*(12*(b+1 : ℚ)/(accuracyBudget b d r : ℚ)) ≤ 1/2 := by
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by exact_mod_cast accuracyBudget_pos b d r)).2
  rw [accuracy_cast]
  have hd : (d : ℚ) ≤ d+1 := by linarith
  have hp : (24 : ℚ)*(b+1)*(d+1) ≤ 24*(b+1)*(d+1)*(r+1) :=
    le_mul_of_one_le_right (by positivity) (by norm_cast; omega)
  have hmul := mul_le_mul_of_nonneg_left hd (show (0 : ℚ) ≤ 24*(b+1) by positivity)
  nlinarith

theorem accumulatedTolerance_accuracy (b d r : ℕ) :
    2*d*(12*(b+1 : ℚ)/(accuracyBudget b d r : ℚ)) ≤ 1/(r+1 : ℚ) := by
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by exact_mod_cast accuracyBudget_pos b d r) (by positivity)).2
  rw [accuracy_cast]
  have h := mul_le_mul_of_nonneg_left (show (d : ℚ) ≤ d+1 by linarith)
    (show (0 : ℚ) ≤ 24*(b+1)*(r+1) by positivity)
  nlinarith

theorem nat_le_two_pow (n : ℕ) : n ≤ 2^n := (Nat.lt_two_pow_self (n := n)).le

theorem dyadic_le_reciprocal (T : ℕ) (hT : 0 < T) : 1/(2^T : ℚ) ≤ 1/(T : ℚ) := by
  apply div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hT)
  exact_mod_cast (Nat.lt_two_pow_self (n := T)).le

theorem confidence_union_bound (b d k : ℕ) :
    (d : ℚ)*(b+1)/(2^(confidenceBudget b d k+1) : ℚ) ≤ 1/(2^k : ℚ) := by
  have hd : (d : ℚ) ≤ 2^d := by exact_mod_cast (Nat.lt_two_pow_self (n := d)).le
  have hb : (b+1 : ℚ) ≤ 2^b := by exact_mod_cast (Nat.lt_two_pow_self (n := b))
  have hh : (d : ℚ)*(b+1) ≤ 2^(d+b) := by
    rw [pow_add]
    exact mul_le_mul hd hb (by positivity) (by positivity)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  unfold confidenceBudget
  rw [show k+d+b+1=k+(d+b)+1 by omega, pow_succ, pow_add]
  have hmul := mul_le_mul_of_nonneg_right hh (show (0 : ℚ) ≤ 2^k by positivity)
  have hp : (0 : ℚ) ≤ 2^k*2^(d+b) := by positivity
  nlinarith

/-- The explicit polynomial budgets give the requested relative accuracy and
failure probability. Concentration and adaptive error bounds are proved by
`counting_failure_bound`; no statistical conclusion is an input assumption. -/
theorem counting_dyadic_failure {S α : Type*} [Fintype α] [Nonempty α] {b : ℕ}
    (R : CountReduction S b) (sampler : S → α → Option (Fin (b+1))) (d r k : ℕ)
    (hbias : ∀ s, 0 < R.count s → 0 < R.rank s → ∀ i,
      |probability (fun a => sampler s a=some i)-R.branchProbability s i| ≤
        1/(2^(accuracyBudget b d r) : ℚ))
    (s : S) (hc : 0 < R.count s) (hrank : R.rank s=d) :
    probability (fun tape => ¬RelativeEstimate (R.count s) r
      (countingEstimate R sampler (accuracyBudget b d r) (confidenceBudget b d k) d s tape)) ≤
      1/(2^k : ℚ) := by
  have hbias' : ∀ s, 0 < R.count s → 0 < R.rank s → ∀ i,
      |probability (fun a => sampler s a=some i)-R.branchProbability s i| ≤
        1/(accuracyBudget b d r : ℚ) := by
    intro t ht htr i
    exact (hbias t ht htr i).trans (dyadic_le_reciprocal _ (accuracyBudget_pos b d r))
  exact (counting_failure_bound R sampler (accuracyBudget b d r) (confidenceBudget b d k) d r
    (accuracyBudget_pos b d r) (accuracyBudget_large b d r) (localTolerance_le_one b d r)
    (accumulatedTolerance_small b d r) (accumulatedTolerance_accuracy b d r) hbias' s hc hrank).trans
    (confidence_union_bound b d k)

end HiddenCircuits.Approximation.SelfReduction
