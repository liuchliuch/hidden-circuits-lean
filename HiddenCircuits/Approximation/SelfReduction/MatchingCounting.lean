import HiddenCircuits.Approximation.SelfReduction.MatchingSampler
import HiddenCircuits.Approximation.SelfReduction.OutputBounds

/-! Concrete matching counting code, separated from every analysis-only count
field. This is a bounded-bit functional algorithm, not a count-oracle call. -/
namespace HiddenCircuits.Approximation.SelfReduction
open HiddenCircuits.Complexity

/-- Collect exactly the empirical counts used along successive actual vertex
pair deletions. The program reads neither exact counts nor a recurrence certificate. -/
def matchingObservedCounts {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (m : ℕ) (sample : ResidualSampler G m) (T h : ℕ) :
    (d : ℕ) → MatchingState b → (Fin d → StageTape (CoinTape m) T h) → List ℕ
  | 0, _, _ => []
  | d+1, s, tapes =>
      let sampler := matchingBranchSampler G m sample
      let j := selectedBranch b T h sampler s (tapes 0)
      selectedCount sampler T h s (tapes 0) ::
        matchingObservedCounts G m sample T h d (matchingChild G s j) (fun i => tapes i.succ)

/-- Equality to the abstract analysis, proved for all tapes, including bad ones. -/
theorem matchingObservedCounts_eq {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (m : ℕ) (sample : ResidualSampler G m) (T h d : ℕ) (s : MatchingState b)
    (tapes : Fin d → StageTape (CoinTape m) T h) :
    matchingObservedCounts G m sample T h d s tapes =
      selectedCounts (matchingReduction G) (matchingBranchSampler G m sample) T h d s tapes := by
  induction d generalizing s with
  | zero => rfl
  | succ d ih => simp only [matchingObservedCounts, selectedCounts, ih]; rfl

/-- A computable binary-output matching estimator driven by one fixed fair-bit
tape. `isEmpty` is the separately supplied matching-existence decision routine. -/
def matchingCountingOutput {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (isEmpty : MatchingState b → Bool) (m : ℕ) (sample : ResidualSampler G m)
    (d r k : ℕ) (s : MatchingState b)
    (tape : CoinTape (countingBits m (accuracyBudget b d r) (confidenceBudget b d k) d)) : BitString :=
  if isEmpty s then encodeRatio 0 1 else
    reciprocalProductOutput (batchSize (accuracyBudget b d r))
      (matchingObservedCounts G m sample (accuracyBudget b d r) (confidenceBudget b d k) d s
        (countingTapes m (accuracyBudget b d r) (confidenceBudget b d k) d tape))

 theorem matchingCountingOutput_eq {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (isEmpty : MatchingState b → Bool) (m : ℕ) (sample : ResidualSampler G m)
    (d r k : ℕ) (s : MatchingState b)
    (tape : CoinTape (countingBits m (accuracyBudget b d r) (confidenceBudget b d k) d)) :
    matchingCountingOutput G isEmpty m sample d r k s tape =
      runCountingOutput (matchingReduction G) isEmpty m (matchingBranchSampler G m sample) d r k s tape := by
  simp only [matchingCountingOutput, matchingObservedCounts_eq, runCountingOutput,
    countingOutputWithZero, countingOutput]

/-- Matching-specific exact-zero and dyadic-success theorem. The only supplied
algorithmic components are residual near-uniform samplers and an empty-instance
decider; all counting statistics and actual graph deletions are derived here. -/
theorem matchingCountingOutput_guarantee {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (isEmpty : MatchingState b → Bool)
    (hempty : ∀ s, isEmpty s=true ↔ matchingStateCount G s=0)
    (m : ℕ) (sample : ResidualSampler G m) (d r k : ℕ)
    (hsample : ResidualSamplingGuarantee G m sample (1/(2^(accuracyBudget b d r) : ℚ)))
    (s : MatchingState b) (hr : matchingRank s=d) :
    (matchingStateCount G s=0 → ∀ tape,
      decodeEstimate (matchingCountingOutput G isEmpty m sample d r k s tape)=some 0) ∧
    1-1/(2^k : ℚ) ≤
      coinProbability (countingBits m (accuracyBudget b d r) (confidenceBudget b d k) d)
        (fun tape => ∃ z, decodeEstimate (matchingCountingOutput G isEmpty m sample d r k s tape)=some z ∧
          RelativeEstimate (matchingStateCount G s) r z) := by
  simp_rw [matchingCountingOutput_eq]
  exact runCountingOutput_guarantee (matchingReduction G) isEmpty hempty m (matchingBranchSampler G m sample)
    d r k (fun s hs hsr i => matchingBranchSampler_bias G m sample _ (by positivity) hsample s hs hsr i) s hr

/-- All output words have a polynomial bound on every random tape. -/
theorem matchingCountingOutput_length {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (isEmpty : MatchingState b → Bool) (m : ℕ) (sample : ResidualSampler G m)
    (d r k : ℕ) (s : MatchingState b)
    (tape : CoinTape (countingBits m (accuracyBudget b d r) (confidenceBudget b d k) d)) :
    (matchingCountingOutput G isEmpty m sample d r k s tape).length ≤
      3*batchSize (accuracyBudget b d r)*d+4 := by
  rw [matchingCountingOutput_eq]
  unfold runCountingOutput countingOutputWithZero
  split_ifs
  · simp [encodeRatio, encodeNat_length]
  · exact countingOutput_length _ _ _ _ _ _ _

end HiddenCircuits.Approximation.SelfReduction
