import HiddenCircuits.Approximation.SelfReduction.MatchingDeletion
import HiddenCircuits.Approximation.SelfReduction.OutputGuarantee

/-! Unconditional near-uniform samplers on induced matching instances supply
all probabilistic inputs of the actual matching counting reduction. -/
namespace HiddenCircuits.Approximation.SelfReduction

/-- An actual finite-tape sampler for each active residual induced graph. -/
abbrev ResidualSampler {b : ℕ} (G : SimpleGraph (Fin (b+1))) (m : ℕ) :=
  ∀ (d : ℕ) (U : {U : Finset (Fin (b+1)) // U.card=2*d}),
    CoinTape m → Option (PerfectPartner (G.induce (U.val : Set (Fin (b+1)))))

/-- Read the pivot's actual sampled partner; failure remains the distinct `none`.
Rejected and terminal states are never sampled by the counting proof. -/
def matchingBranchSampler {b : ℕ} (G : SimpleGraph (Fin (b+1))) (m : ℕ)
    (sample : ResidualSampler G m) : MatchingState b → CoinTape m → Option (Fin (b+1))
  | ⟨0,_⟩, _ => none
  | ⟨d+1,none⟩, _ => none
  | ⟨d+1,some U⟩, r => (sample (d+1) U r).map (fun p => (p.val (matchingPivot U)).val)

/-- Typed unconditional near-uniformity; nothing is conditioned on successful
sampling and every event, including failure, is included. -/
def ResidualSamplingGuarantee {b : ℕ} (G : SimpleGraph (Fin (b+1))) (m : ℕ)
    (sample : ResidualSampler G m) (δ : ℚ) : Prop :=
  ∀ (d : ℕ) (U : {U : Finset (Fin (b+1)) // U.card=2*d}),
    0 < perfectMatchingCount (G.induce (U.val : Set (Fin (b+1)))) →
    ∀ E : Option (PerfectPartner (G.induce (U.val : Set (Fin (b+1))))) → Prop,
      |coinProbability m (fun r => E (sample d U r)) - probability (fun p => E (some p))| ≤ δ

/-- Exact branch probabilities are inherited from the supplied matching sampler
on each genuine induced residual instance. -/
theorem matchingBranchSampler_bias {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (m : ℕ) (sample : ResidualSampler G m) (δ : ℚ) (hδ : 0 ≤ δ)
    (h : ResidualSamplingGuarantee G m sample δ)
    (s : MatchingState b) (hc : 0 < matchingStateCount G s) (hr : 0 < matchingRank s)
    (v : Fin (b+1)) :
    |coinProbability m (fun r => matchingBranchSampler G m sample s r=some v) -
      (matchingReduction G).branchProbability s v| ≤ δ := by
  classical
  rcases s with ⟨d,U⟩
  cases d with
  | zero => exact False.elim (Nat.lt_irrefl 0 hr)
  | succ d =>
    cases U with
    | none => exact False.elim (Nat.lt_irrefl 0 hc)
    | some U =>
      by_cases hv : v ∈ U.val
      · let w : U.val := ⟨v,hv⟩
        have hh := sampledPartner_error (G.induce (U.val : Set (Fin (b+1))))
          (matchingPivot U) w m (sample (d+1) U) δ (h (d+1) U hc)
        have he : coinProbability m (fun r => matchingBranchSampler G m sample ⟨d+1,some U⟩ r=some v) =
            coinProbability m (fun r => sampledPartner (matchingPivot U) (sample (d+1) U r)=some w) := by
          apply coinProbability_congr
          intro r
          cases hs : sample (d+1) U r with
          | none => simp [matchingBranchSampler, sampledPartner, hs]
          | some p => simp [matchingBranchSampler, sampledPartner, hs, w, Subtype.ext_iff]
        rw [he]
        simp only [CountReduction.branchProbability, matchingReduction]
        rw [show v=w.val from rfl, matchingChild_count_retained G U w]
        exact hh
      · have he : coinProbability m (fun r => matchingBranchSampler G m sample ⟨d+1,some U⟩ r=some v)=0 := by
          apply (coinProbability_eq_zero_iff m _).mpr
          intro r he
          cases hs : sample (d+1) U r with
          | none => simp [matchingBranchSampler, hs] at he
          | some p =>
            have he' : (p.val (matchingPivot U)).val=v := by simpa [matchingBranchSampler,hs] using he
            exact hv (he' ▸ (p.val (matchingPivot U)).property)
        rw [he]
        have hz := matchingChild_count_outside G U v hv
        simp only [CountReduction.branchProbability, matchingReduction]
        rw [hz]
        simpa using hδ

end HiddenCircuits.Approximation.SelfReduction
