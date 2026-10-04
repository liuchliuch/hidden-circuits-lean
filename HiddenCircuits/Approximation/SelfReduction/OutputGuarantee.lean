import HiddenCircuits.Approximation.SelfReduction.EncodedOutput

/-! Exact zero handling and the complete finite-coin encoded-output guarantee.
This theorem does not claim TM2 polynomial time for the orchestration: that
separate implementation obligation is deliberately not hidden in the statement. -/
namespace HiddenCircuits.Approximation.SelfReduction
open HiddenCircuits.Complexity

/-- Binary output of the actual bounded fair-bit self-reduction, with a supplied
correct emptiness decision procedure. -/
def runCountingOutput {S : Type*} {b : ℕ} (R : CountReduction S b)
    (isEmpty : S → Bool) (m : ℕ) (sampler : S → CoinTape m → Option (Fin (b+1)))
    (d r k : ℕ) (s : S)
    (tape : CoinTape (countingBits m (accuracyBudget b d r) (confidenceBudget b d k) d)) : BitString :=
  countingOutputWithZero R isEmpty sampler (accuracyBudget b d r) (confidenceBudget b d k) d s
    (countingTapes m (accuracyBudget b d r) (confidenceBudget b d k) d tape)

/-- Exact finite-coin approximation semantics, including zero-count instances.
All concentration, amplification and adaptive error accumulation are proved in
this subtree. The only probabilistic input is the sampler's near-uniformity. -/
theorem runCountingOutput_guarantee {S : Type*} {b : ℕ}
    (R : CountReduction S b) (isEmpty : S → Bool)
    (hempty : ∀ s, isEmpty s=true ↔ R.count s=0)
    (m : ℕ) (sampler : S → CoinTape m → Option (Fin (b+1))) (d r k : ℕ)
    (hbias : ∀ s, 0 < R.count s → 0 < R.rank s → ∀ i,
      |coinProbability m (fun a => sampler s a=some i)-R.branchProbability s i| ≤
        1/(2^(accuracyBudget b d r) : ℚ))
    (s : S) (hr : R.rank s=d) :
    (R.count s=0 → ∀ tape, decodeEstimate (runCountingOutput R isEmpty m sampler d r k s tape)=some 0) ∧
    1-1/(2^k : ℚ) ≤
      coinProbability (countingBits m (accuracyBudget b d r) (confidenceBudget b d k) d)
        (fun tape => ∃ z, decodeEstimate (runCountingOutput R isEmpty m sampler d r k s tape)=some z ∧
          RelativeEstimate (R.count s) r z) := by
  classical
  constructor
  · intro hc tape
    exact countingOutputWithZero_zero R isEmpty hempty sampler _ _ _ s hc _
  · by_cases hc : R.count s=0
    · have hdecode (tape) : decodeEstimate (runCountingOutput R isEmpty m sampler d r k s tape)=some 0 :=
        countingOutputWithZero_zero R isEmpty hempty sampler _ _ _ s hc _
      have hevent : coinProbability (countingBits m (accuracyBudget b d r) (confidenceBudget b d k) d)
          (fun tape => ∃ z, decodeEstimate (runCountingOutput R isEmpty m sampler d r k s tape)=some z ∧
            RelativeEstimate (R.count s) r z) = 1 := by
        apply (coinProbability_congr (fun tape => ?_)).trans (coinProbability_true _)
        simp [hdecode, hc]
      rw [hevent]
      have hnonneg : (0 : ℚ) ≤ 1/2^k := by positivity
      linarith
    · have hc' : 0 < R.count s := by omega
      have hempty' : isEmpty s=false := by
        cases he : isEmpty s
        · rfl
        · exact False.elim (hc ((hempty s).1 he))
      have hf := counting_coins_dyadic_failure R m sampler d r k hbias s hc' hr
      have hevent : coinProbability (countingBits m (accuracyBudget b d r) (confidenceBudget b d k) d)
          (fun tape => ∃ z, decodeEstimate (runCountingOutput R isEmpty m sampler d r k s tape)=some z ∧
            RelativeEstimate (R.count s) r z) =
          probability (fun tape => RelativeEstimate (R.count s) r
            (runCountingCoins R m sampler (accuracyBudget b d r) (confidenceBudget b d k) d s tape)) := by
        rw [probability_coinTape]
        apply coinProbability_congr
        intro tape
        simp [runCountingOutput, countingOutputWithZero, hempty', countingOutput_decode, runCountingCoins]
      rw [hevent]
      rw [← probability_coinTape, probability_compl] at hf
      linarith

end HiddenCircuits.Approximation.SelfReduction
