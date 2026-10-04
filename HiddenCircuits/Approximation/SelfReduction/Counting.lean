import HiddenCircuits.Approximation.SelfReduction.Branches
import HiddenCircuits.Approximation.SelfReduction.Estimator

/-! A finite sampling-to-counting reduction with a proved unconditional success
bound. The algorithm uses only samples, empirical frequencies and child instances. -/
namespace HiddenCircuits.Approximation.SelfReduction

abbrev StageTape (α : Type*) (T k : ℕ) := Fin (2*(k+1)) → Fin (batchSize T) → α

def countingStep {S α : Type*} {b : ℕ} (R : CountReduction S b)
    (sampler : S → α → Option (Fin (b+1))) (T k : ℕ) (s : S) (r : StageTape α T k) : S :=
  R.child s (selectedBranch b T k sampler s r)

def countingFrequency {S α : Type*} {b : ℕ} (sampler : S → α → Option (Fin (b+1)))
    (T k : ℕ) (s : S) (r : StageTape α T k) : ℚ :=
  branchFrequencies b T k sampler s r (selectedBranch b T k sampler s r)

def countingEstimate {S α : Type*} {b : ℕ} (R : CountReduction S b)
    (sampler : S → α → Option (Fin (b+1))) (T k d : ℕ) (s : S)
    (r : Fin d → StageTape α T k) : ℚ :=
  estimate (countingStep R sampler T k) (countingFrequency sampler T k) d s r

/-- Local correctness is derived from near-uniform sampling and the proved
concentration/selection lemmas. It is not an input certificate. -/
theorem counting_local_failure {S α : Type*} [Fintype α] [Nonempty α] {b : ℕ}
    (R : CountReduction S b) (sampler : S → α → Option (Fin (b+1)))
    (T k : ℕ) (hT : 0 < T) (hsize : (24 : ℚ)*(b+1) ≤ T)
    (s : S) (hc : 0 < R.count s) (hr : 0 < R.rank s)
    (hbias : ∀ i, |probability (fun a => sampler s a=some i)-R.branchProbability s i| ≤ 1/(T : ℚ)) :
    probability (fun r => ¬stepAccurate (countingStep R sampler T k) (countingFrequency sampler T k)
      R.count R.rank (12*(b+1 : ℚ)/T) s r) ≤ (b+1 : ℚ)/(2^(k+1) : ℚ) := by
  classical
  apply le_trans ?_ (branchFrequencies_failure b T k hT sampler s (R.branchProbability s) hbias)
  apply probability_mono
  intro r hbad
  by_contra hn
  push_neg at hn
  have hh := selectedBranch_correct b T k hT R sampler s hr hc r hsize hn
  apply hbad
  exact ⟨hh.1, hh.2.1, R.child_rank s _ hr, hh.2.2⟩

/-- Statistical counting theorem on a genuine finite product of independent
sampler tapes. Accuracy and confidence are quantitative, not asymptotic. -/
theorem counting_failure_bound {S α : Type*} [Fintype α] [Nonempty α] {b : ℕ}
    (R : CountReduction S b) (sampler : S → α → Option (Fin (b+1)))
    (T k d r : ℕ) (hT : 0 < T) (hsize : (24 : ℚ)*(b+1) ≤ T)
    (hη1 : 12*(b+1 : ℚ)/T ≤ 1)
    (hsmall : (d : ℚ)*(12*(b+1 : ℚ)/T) ≤ 1/2)
    (haccuracy : 2*d*(12*(b+1 : ℚ)/T) ≤ 1/(r+1 : ℚ))
    (hbias : ∀ s, 0 < R.count s → 0 < R.rank s → ∀ i,
      |probability (fun a => sampler s a=some i)-R.branchProbability s i| ≤ 1/(T : ℚ))
    (s : S) (hc : 0 < R.count s) (hr : R.rank s=d) :
    probability (fun tape => ¬RelativeEstimate (R.count s) r
      (countingEstimate R sampler T k d s tape)) ≤ (d : ℚ)*(b+1)/(2^(k+1) : ℚ) := by
  classical
  let step := countingStep R sampler T k
  let freq := countingFrequency sampler T k
  let η : ℚ := 12*(b+1 : ℚ)/T
  let good := stepAccurate step freq R.count R.rank η
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have ha := adaptive_rank_failure_bound step good (fun s => 0 < R.count s) R.rank
    ((b+1 : ℚ)/(2^(k+1) : ℚ)) (by positivity)
    (fun s hs hsr => counting_local_failure R sampler T k hT hsize s hs hsr (hbias s hs hsr))
    (fun _ _ _ hg => hg.1) (fun _ _ _ hg => hg.2.2.1) d s hc hr
  have hmono : probability (fun tape => ¬RelativeEstimate (R.count s) r
      (countingEstimate R sampler T k d s tape)) ≤
      probability (fun tape => ¬goodRun step good d s tape) := by
    apply probability_mono
    intro tape hbad hgood
    apply hbad
    have he := estimate_relative_error step freq R.count R.rank R.leaf_count η hη hη1 d hsmall
      s hr hc tape hgood
    unfold RelativeEstimate countingEstimate
    apply he.trans
    calc
      (2*d*η)*(R.count s : ℚ) ≤ (1/(r+1 : ℚ))*(R.count s : ℚ) :=
        mul_le_mul_of_nonneg_right haccuracy (Nat.cast_nonneg _)
      _ = (R.count s : ℚ)/(r+1) := by ring
  exact hmono.trans (by simpa [div_eq_mul_inv, mul_assoc] using ha)

end HiddenCircuits.Approximation.SelfReduction
