import HiddenCircuits.Approximation.SelfReduction.NaturalCounting

/-! Zero counts are handled without an existence oracle. Sound typed samplers
return `none` on every zero-count instance, forcing an exact zero numerator-free
failure output through the observed zero denominator. -/
namespace HiddenCircuits.Approximation.SelfReduction
open HiddenCircuits.Complexity

def isRejected {b : ℕ} (s : MatchingState b) : Bool := s.2.isNone

theorem residualSampler_zero {b : ℕ} (G : SimpleGraph (Fin (b+1))) (m : ℕ)
    (sample : ResidualSampler G m) (d : ℕ) (U : {U : Finset (Fin (b+1)) // U.card=2*d})
    (hc : perfectMatchingCount (G.induce (U.val : Set (Fin (b+1))))=0) :
    ∀ r, sample d U r=none := by
  classical
  intro r
  cases hs : sample d U r with
  | none => rfl
  | some p =>
    have hp : 0 < Fintype.card (PerfectPartner (G.induce (U.val : Set (Fin (b+1)))) ) :=
      Fintype.card_pos_iff.mpr ⟨p⟩
    rw [← perfectMatchingCount_eq_partners, hc] at hp
    omega

 theorem naturalAmplifiedCount_false {α : Type*} (E : α → Prop) [DecidablePred E]
    (hE : ∀ a, ¬E a) (T k : ℕ) (r : StageTape α T k) : naturalAmplifiedCount E T k r=0 := by
  simp [naturalAmplifiedCount, eventCount, hE]

 theorem naturalMatchingCounts_zero_product {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (m : ℕ) (sample : ResidualSampler G m) (T k d : ℕ)
    (U : {U : Finset (Fin (b+1)) // U.card=2*(d+1)})
    (hc : perfectMatchingCount (G.induce (U.val : Set (Fin (b+1))))=0)
    (tapes : Fin (d+1) → StageTape (CoinTape m) T k) :
    (naturalMatchingCounts G m sample T k (d+1) ⟨d+1,some U⟩ tapes).prod=0 := by
  have hs := residualSampler_zero G m sample (d+1) U hc
  have hb (r) : matchingBranchSampler G m sample ⟨d+1,some U⟩ r=none := by
    simp [matchingBranchSampler, hs]
  unfold naturalMatchingCounts
  dsimp only
  rw [naturalAmplifiedCount_false _ (fun a => by rw [hb]; simp)]
  simp

/-- No matching-existence decision routine is called: rejected markers are
visible input data; active zero-count graphs force a zero empirical denominator. -/
def soundMatchingOutput {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (m : ℕ) (sample : ResidualSampler G m) (d r k : ℕ) (s : MatchingState b)
    (tape : CoinTape (countingBits m (accuracyBudget b d r) (confidenceBudget b d k) d)) : BitString :=
  naturalMatchingOutput G isRejected m sample d r k s tape

/-- Exact zero on every tape follows solely from soundness of the sampler's
witness type, including zero-count active states and rejected states. -/
theorem soundMatchingOutput_zero {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (m : ℕ) (sample : ResidualSampler G m) (d r k : ℕ) (s : MatchingState b)
    (hr : matchingRank s=d) (hc : matchingStateCount G s=0)
    (tape : CoinTape (countingBits m (accuracyBudget b d r) (confidenceBudget b d k) d)) :
    decodeEstimate (soundMatchingOutput G m sample d r k s tape)=some 0 := by
  rcases s with ⟨d',U⟩
  change d'=d at hr
  subst d'
  cases U with
  | none => simp [soundMatchingOutput, naturalMatchingOutput, isRejected]
  | some U =>
    cases d with
    | zero =>
      have he : U.val=∅ := Finset.card_eq_zero.mp (by simpa using U.property)
      have hi : IsEmpty {x // x ∈ U.val} := ⟨fun x => by simpa [he] using x.property⟩
      letI := hi
      have hh := perfectMatchingCount_empty_vertices (G.induce (U.val : Set (Fin (b+1))))
      change perfectMatchingCount _=0 at hc
      omega
    | succ d =>
      have hz := naturalMatchingCounts_zero_product G m sample (accuracyBudget b (d+1) r)
        (confidenceBudget b (d+1) k) d U hc
        (countingTapes m (accuracyBudget b (d+1) r) (confidenceBudget b (d+1) k) (d+1) tape)
      simp only [soundMatchingOutput, naturalMatchingOutput, isRejected, Option.isNone_some,
        Bool.false_eq_true, if_false, reciprocalProductOutput, hz, decodeEstimate_encodeRatio, Nat.cast_zero, div_zero]

/-- Full finite statistical guarantee with no supplied empty-instance decider. -/
theorem soundMatchingOutput_guarantee {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (m : ℕ) (sample : ResidualSampler G m) (d r k : ℕ)
    (hsample : ResidualSamplingGuarantee G m sample (1/(2^(accuracyBudget b d r) : ℚ)))
    (s : MatchingState b) (hr : matchingRank s=d) :
    (matchingStateCount G s=0 → ∀ tape, decodeEstimate (soundMatchingOutput G m sample d r k s tape)=some 0) ∧
    1-1/(2^k : ℚ) ≤
      coinProbability (countingBits m (accuracyBudget b d r) (confidenceBudget b d k) d)
        (fun tape => ∃ z, decodeEstimate (soundMatchingOutput G m sample d r k s tape)=some z ∧
          RelativeEstimate (matchingStateCount G s) r z) := by
  classical
  constructor
  · exact fun hc tape => soundMatchingOutput_zero G m sample d r k s hr hc tape
  · by_cases hc : matchingStateCount G s=0
    · have hz := soundMatchingOutput_zero G m sample d r k s hr hc
      have hevent : coinProbability (countingBits m (accuracyBudget b d r) (confidenceBudget b d k) d)
          (fun tape => ∃ z, decodeEstimate (soundMatchingOutput G m sample d r k s tape)=some z ∧
            RelativeEstimate (matchingStateCount G s) r z)=1 := by
        apply (coinProbability_congr (fun tape => ?_)).trans (coinProbability_true _)
        simp [hz, hc]
      rw [hevent]
      have hn : (0 : ℚ)≤1/2^k := by positivity
      linarith
    · have hc' : 0 < matchingStateCount G s := by omega
      have hrejected : isRejected s=false := by
        rcases s with ⟨sd,U⟩
        cases U with
        | none => exact False.elim (hc rfl)
        | some U => rfl
      have h := counting_coins_dyadic_failure (matchingReduction G) m (matchingBranchSampler G m sample)
        d r k (fun s hs hsr i => matchingBranchSampler_bias G m sample _ (by positivity) hsample s hs hsr i) s hc' hr
      have hevent : coinProbability (countingBits m (accuracyBudget b d r) (confidenceBudget b d k) d)
          (fun tape => ∃ z, decodeEstimate (soundMatchingOutput G m sample d r k s tape)=some z ∧
            RelativeEstimate (matchingStateCount G s) r z) =
          probability (fun tape => RelativeEstimate (matchingStateCount G s) r
            (runCountingCoins (matchingReduction G) m (matchingBranchSampler G m sample)
              (accuracyBudget b d r) (confidenceBudget b d k) d s tape)) := by
        rw [probability_coinTape]
        apply coinProbability_congr
        intro tape
        simp [soundMatchingOutput, naturalMatchingOutput_eq, matchingCountingOutput_eq,
          runCountingOutput, countingOutputWithZero, hrejected, runCountingCoins]
      rw [hevent]
      rw [← probability_coinTape, probability_compl] at h
      rw [show (matchingReduction G).count s=matchingStateCount G s from rfl] at h
      linarith

end HiddenCircuits.Approximation.SelfReduction
