import HiddenCircuits.Approximation.SelfReduction.NaturalSelection

/-! Integer-only matching estimator, pointwise equal to the analyzed estimator.
Only final binary numerator/denominator products can grow beyond polynomial
magnitude; their bit lengths and real accumulator executions are already proved. -/
namespace HiddenCircuits.Approximation.SelfReduction
open HiddenCircuits.Complexity

def naturalSelectedBranch {S α : Type*} (b T k : ℕ) (sampler : S → α → Option (Fin (b+1)))
    (s : S) (r : StageTape α T k) : Fin (b+1) :=
  chooseMax b (fun i => naturalAmplifiedCount (fun a => sampler s a=some i) T k r)

theorem naturalSelectedBranch_eq {S α : Type*} (b T k : ℕ) (hT : 0 < T)
    (sampler : S → α → Option (Fin (b+1))) (s : S) (r : StageTape α T k) :
    naturalSelectedBranch b T k sampler s r = selectedBranch b T k sampler s r := by
  unfold naturalSelectedBranch selectedBranch
  have hfun : branchFrequencies b T k sampler s r =
      (fun i => (naturalAmplifiedCount (fun a => sampler s a=some i) T k r : ℚ)/batchSize T) := by
    funext i
    rw [naturalAmplifiedCount_eq _ _ _ hT]
    exact amplifiedFrequency_eq_count _ _ _ _
  rw [hfun]
  exact (chooseMax_natural_div b (batchSize T) (by unfold batchSize; positivity) _).symm

def naturalMatchingCounts {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (m : ℕ) (sample : ResidualSampler G m) (T h : ℕ) :
    (d : ℕ) → MatchingState b → (Fin d → StageTape (CoinTape m) T h) → List ℕ
  | 0, _, _ => []
  | d+1, s, tapes =>
      let sampler := matchingBranchSampler G m sample
      let j := naturalSelectedBranch b T h sampler s (tapes 0)
      naturalAmplifiedCount (fun a => sampler s a=some j) T h (tapes 0) ::
        naturalMatchingCounts G m sample T h d (matchingChild G s j) (fun i => tapes i.succ)

theorem naturalMatchingCounts_eq {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (m : ℕ) (sample : ResidualSampler G m) (T h d : ℕ) (hT : 0 < T) (s : MatchingState b)
    (tapes : Fin d → StageTape (CoinTape m) T h) :
    naturalMatchingCounts G m sample T h d s tapes = matchingObservedCounts G m sample T h d s tapes := by
  induction d generalizing s with
  | zero => rfl
  | succ d ih =>
    simp only [naturalMatchingCounts, matchingObservedCounts,
      naturalSelectedBranch_eq b T h hT, naturalAmplifiedCount_eq _ _ _ hT, ih]
    rfl

/-- The final executable functional algorithm contains only natural counts,
integer comparisons, finite graph deletion, binary encoding and sampled bits. -/
def naturalMatchingOutput {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (isEmpty : MatchingState b → Bool) (m : ℕ) (sample : ResidualSampler G m)
    (d r k : ℕ) (s : MatchingState b)
    (tape : CoinTape (countingBits m (accuracyBudget b d r) (confidenceBudget b d k) d)) : BitString :=
  if isEmpty s then encodeRatio 0 1 else
    reciprocalProductOutput (batchSize (accuracyBudget b d r))
      (naturalMatchingCounts G m sample (accuracyBudget b d r) (confidenceBudget b d k) d s
        (countingTapes m (accuracyBudget b d r) (confidenceBudget b d k) d tape))

theorem naturalMatchingOutput_eq {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (isEmpty : MatchingState b → Bool) (m : ℕ) (sample : ResidualSampler G m)
    (d r k : ℕ) (s : MatchingState b)
    (tape : CoinTape (countingBits m (accuracyBudget b d r) (confidenceBudget b d k) d)) :
    naturalMatchingOutput G isEmpty m sample d r k s tape =
      matchingCountingOutput G isEmpty m sample d r k s tape := by
  simp only [naturalMatchingOutput, matchingCountingOutput,
    naturalMatchingCounts_eq G m sample _ _ _ (accuracyBudget_pos b d r)]

/-- Complete finite-coin correctness of the bounded-integer matching algorithm,
including exact zero. This still deliberately makes no unproved TM runtime claim. -/
theorem naturalMatchingOutput_guarantee {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (isEmpty : MatchingState b → Bool)
    (hempty : ∀ s, isEmpty s=true ↔ matchingStateCount G s=0)
    (m : ℕ) (sample : ResidualSampler G m) (d r k : ℕ)
    (hsample : ResidualSamplingGuarantee G m sample (1/(2^(accuracyBudget b d r) : ℚ)))
    (s : MatchingState b) (hr : matchingRank s=d) :
    (matchingStateCount G s=0 → ∀ tape,
      decodeEstimate (naturalMatchingOutput G isEmpty m sample d r k s tape)=some 0) ∧
    1-1/(2^k : ℚ) ≤
      coinProbability (countingBits m (accuracyBudget b d r) (confidenceBudget b d k) d)
        (fun tape => ∃ z, decodeEstimate (naturalMatchingOutput G isEmpty m sample d r k s tape)=some z ∧
          RelativeEstimate (matchingStateCount G s) r z) := by
  simp_rw [naturalMatchingOutput_eq]
  exact matchingCountingOutput_guarantee G isEmpty hempty m sample d r k hsample s hr

end HiddenCircuits.Approximation.SelfReduction
