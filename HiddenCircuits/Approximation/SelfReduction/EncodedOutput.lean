import HiddenCircuits.Approximation.SelfReduction.CoinExperiment
import HiddenCircuits.Approximation.SelfReduction.Arithmetic

/-! Exact bounded natural numerator/denominator outputs for the statistical
estimator, including an explicit zero-count decision wrapper. -/
namespace HiddenCircuits.Approximation.SelfReduction
open HiddenCircuits.Complexity

/-- The amplifier selects one observed batch; its numerator remains a bounded
natural frequency count, even on a statistically bad outcome. -/
def amplifiedCount {α : Type*} (E : α → Prop) [DecidablePred E] (T k : ℕ)
    (r : StageTape α T k) : ℕ :=
  let z : Fin (2*k+1+1) → ℚ :=
    fun i => eventFrequency (batchSize T) E (r (Fin.cast (by omega) i))
  let i := chooseMax (2*k+1) (fun j => (cluster (2*k+1) z (2/(T : ℚ)) j).card)
  (Finset.univ.filter fun j => E (r (Fin.cast (by omega) i) j)).card

theorem amplifiedFrequency_eq_count {α : Type*} (E : α → Prop) [DecidablePred E]
    (T k : ℕ) (r : StageTape α T k) :
    amplifiedFrequency E T k r = (amplifiedCount E T k r : ℚ)/batchSize T := by
  rfl

theorem amplifiedCount_le {α : Type*} (E : α → Prop) [DecidablePred E]
    (T k : ℕ) (r : StageTape α T k) : amplifiedCount E T k r ≤ batchSize T := by
  unfold amplifiedCount
  exact (Finset.card_filter_le _ _).trans (by simp)

def selectedCount {S α : Type*} {b : ℕ} (sampler : S → α → Option (Fin (b+1)))
    (T k : ℕ) (s : S) (r : StageTape α T k) : ℕ :=
  amplifiedCount (fun a => sampler s a=some (selectedBranch b T k sampler s r)) T k r

theorem countingFrequency_eq_count {S α : Type*} {b : ℕ}
    (sampler : S → α → Option (Fin (b+1))) (T k : ℕ) (s : S) (r : StageTape α T k) :
    countingFrequency sampler T k s r = (selectedCount sampler T k s r : ℚ)/batchSize T := by
  exact amplifiedFrequency_eq_count
    (fun a => sampler s a=some (selectedBranch b T k sampler s r)) T k r

/-- Actual empirical counts along the chosen path; no exact count oracle occurs. -/
def selectedCounts {S α : Type*} {b : ℕ} (R : CountReduction S b)
    (sampler : S → α → Option (Fin (b+1))) (T k : ℕ) :
    (d : ℕ) → S → (Fin d → StageTape α T k) → List ℕ
  | 0, _, _ => []
  | d+1, s, r => selectedCount sampler T k s (r 0) ::
      selectedCounts R sampler T k d (countingStep R sampler T k s (r 0)) (fun i => r i.succ)

@[simp] theorem selectedCounts_length {S α : Type*} {b : ℕ} (R : CountReduction S b)
    (sampler : S → α → Option (Fin (b+1))) (T k d : ℕ) (s : S) (r : Fin d → StageTape α T k) :
    (selectedCounts R sampler T k d s r).length=d := by
  induction d generalizing s with
  | zero => rfl
  | succ d ih => simp [selectedCounts, ih]

theorem selectedCounts_bound {S α : Type*} {b : ℕ} (R : CountReduction S b)
    (sampler : S → α → Option (Fin (b+1))) (T k d : ℕ) (s : S) (r : Fin d → StageTape α T k) :
    ∀ c ∈ selectedCounts R sampler T k d s r, c ≤ batchSize T := by
  induction d generalizing s with
  | zero => simp [selectedCounts]
  | succ d ih =>
    intro c hc
    simp only [selectedCounts, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact amplifiedCount_le _ _ _ _
    · exact ih _ _ _ hc

/-- The rational estimator equals the exact unreduced quotient of bounded
natural products, so no ideal rational-output operation is needed. -/
theorem countingEstimate_eq_fraction {S α : Type*} {b : ℕ} (R : CountReduction S b)
    (sampler : S → α → Option (Fin (b+1))) (T k d : ℕ) (s : S) (r : Fin d → StageTape α T k) :
    countingEstimate R sampler T k d s r =
      (batchSize T : ℚ)^d/((selectedCounts R sampler T k d s r).prod : ℚ) := by
  induction d generalizing s with
  | zero => simp [countingEstimate, estimate, selectedCounts]
  | succ d ih =>
    change countingEstimate R sampler T k d (countingStep R sampler T k s (r 0))
      (fun i => r i.succ) / countingFrequency sampler T k s (r 0) = _
    rw [ih, countingFrequency_eq_count]
    simp only [selectedCounts, List.prod_cons, Nat.cast_mul, pow_succ, div_div_div_eq]
    rw [mul_comm (selectedCount sampler T k s (r 0) : ℚ)]

/-- Concrete binary output, using the project's rational decoding convention. -/
def countingOutput {S α : Type*} {b : ℕ} (R : CountReduction S b)
    (sampler : S → α → Option (Fin (b+1))) (T k d : ℕ) (s : S) (r : Fin d → StageTape α T k) : BitString :=
  reciprocalProductOutput (batchSize T) (selectedCounts R sampler T k d s r)

@[simp] theorem countingOutput_decode {S α : Type*} {b : ℕ} (R : CountReduction S b)
    (sampler : S → α → Option (Fin (b+1))) (T k d : ℕ) (s : S) (r : Fin d → StageTape α T k) :
    decodeEstimate (countingOutput R sampler T k d s r) = some (countingEstimate R sampler T k d s r) := by
  rw [countingOutput, reciprocalProductOutput_value, selectedCounts_length, countingEstimate_eq_fraction]

/-- A supplied actual empty-instance decision procedure controls exact zero
output. The algorithm does not inspect `R.count`; correctness is proved below. -/
def countingOutputWithZero {S α : Type*} {b : ℕ} (R : CountReduction S b)
    (isEmpty : S → Bool) (sampler : S → α → Option (Fin (b+1))) (T k d : ℕ) (s : S)
    (r : Fin d → StageTape α T k) : BitString :=
  if isEmpty s then encodeRatio 0 1 else countingOutput R sampler T k d s r

@[simp] theorem countingOutputWithZero_zero {S α : Type*} {b : ℕ} (R : CountReduction S b)
    (isEmpty : S → Bool) (hzero : ∀ s, isEmpty s=true ↔ R.count s=0)
    (sampler : S → α → Option (Fin (b+1))) (T k d : ℕ) (s : S) (hc : R.count s=0)
    (r : Fin d → StageTape α T k) :
    decodeEstimate (countingOutputWithZero R isEmpty sampler T k d s r)=some 0 := by
  simp [countingOutputWithZero, (hzero s).2 hc]

end HiddenCircuits.Approximation.SelfReduction
