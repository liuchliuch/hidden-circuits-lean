import HiddenCircuits.Approximation.SelfReduction.Parameters

/-! Flattening the independent experiments into a literal bounded fair-bit tape.
No ideal independent random oracle or rejection-until-success loop is used. -/
namespace HiddenCircuits.Approximation.SelfReduction

/-- A computable bijection from one fixed tape to n independent fixed-size blocks. -/
def splitBlocks (n m : ℕ) : CoinTape (n*m) ≃ (Fin n → CoinTape m) :=
  (Equiv.arrowCongr (finProdFinEquiv : Fin n × Fin m ≃ Fin (n*m)).symm
    (Equiv.refl Bool)).trans (Equiv.curry (Fin n) (Fin m) Bool)

def countingBits (m T h d : ℕ) : ℕ := d*(2*(h+1)*(batchSize T*m))

/-- All stage, confidence-batch and single-sample coordinates are disjoint slices. -/
def countingTapes (m T h d : ℕ) :
    CoinTape (countingBits m T h d) ≃ (Fin d → StageTape (CoinTape m) T h) :=
  (splitBlocks d (2*(h+1)*(batchSize T*m))).trans
    (Equiv.piCongrRight fun _ => (splitBlocks (2*(h+1)) (batchSize T*m)).trans
      (Equiv.piCongrRight fun _ => splitBlocks (batchSize T) m))

theorem probability_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (E : β → Prop) : probability (fun a => E (e a)) = probability E := by
  classical
  unfold probability
  exact mean_equiv e (fun b => if E b then 1 else 0)

/-- Literal finite-coin implementation of the typed counting estimator. -/
def runCountingCoins {S : Type*} {b : ℕ} (R : CountReduction S b)
    (m : ℕ) (sampler : S → CoinTape m → Option (Fin (b+1))) (T h d : ℕ) (s : S)
    (tape : CoinTape (countingBits m T h d)) : ℚ :=
  countingEstimate R sampler T h d s (countingTapes m T h d tape)

/-- The finite-product proof is exactly the law of the concrete bit-tape program. -/
theorem counting_coins_dyadic_failure {S : Type*} {b : ℕ}
    (R : CountReduction S b) (m : ℕ) (sampler : S → CoinTape m → Option (Fin (b+1)))
    (d r k : ℕ)
    (hbias : ∀ s, 0 < R.count s → 0 < R.rank s → ∀ i,
      |coinProbability m (fun a => sampler s a=some i)-R.branchProbability s i| ≤
        1/(2^(accuracyBudget b d r) : ℚ))
    (s : S) (hc : 0 < R.count s) (hr : R.rank s=d) :
    coinProbability (countingBits m (accuracyBudget b d r) (confidenceBudget b d k) d)
      (fun tape => ¬RelativeEstimate (R.count s) r
        (runCountingCoins R m sampler (accuracyBudget b d r) (confidenceBudget b d k) d s tape)) ≤
      1/(2^k : ℚ) := by
  rw [← probability_coinTape]
  unfold runCountingCoins
  rw [probability_equiv (countingTapes m (accuracyBudget b d r) (confidenceBudget b d k) d)
    (fun tape => ¬RelativeEstimate (R.count s) r
      (countingEstimate R sampler (accuracyBudget b d r) (confidenceBudget b d k) d s tape))]
  apply counting_dyadic_failure R sampler d r k _ s hc hr
  intro t ht htr i
  rw [probability_coinTape]
  exact hbias t ht htr i

/-- The exact bit use is a multivariate polynomial in sampler bits, graph depth,
branch count, inverse relative accuracy and confidence precision. -/
theorem countingBits_formula (m b d r k : ℕ) :
    countingBits m (accuracyBudget b d r) (confidenceBudget b d k) d =
      2304*d*(k+d+b+1)*(b+1)^2*(d+1)^2*(r+1)^2*m := by
  unfold countingBits accuracyBudget confidenceBudget batchSize
  ring

/-- A univariate polynomial envelope, suitable for composition with the supplied
sampler's polynomial random-bit budget. -/
theorem countingBits_polynomial (m b d r k N : ℕ)
    (hm : m ≤ N) (hb : b ≤ N) (hd : d ≤ N) (hr : r ≤ N) (hk : k ≤ N) :
    countingBits m (accuracyBudget b d r) (confidenceBudget b d k) d ≤
      2304*N*(3*N+1)*(N+1)^6*N := by
  rw [countingBits_formula]
  calc
    _ ≤ 2304*N*(3*N+1)*(N+1)^2*(N+1)^2*(N+1)^2*N := by gcongr <;> omega
    _ = _ := by ring

end HiddenCircuits.Approximation.SelfReduction
