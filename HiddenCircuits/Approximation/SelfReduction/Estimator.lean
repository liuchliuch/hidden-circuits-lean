import HiddenCircuits.Approximation.SelfReduction.Adaptive
import HiddenCircuits.Approximation.SelfReduction.ProductError
import HiddenCircuits.Approximation.Schemes

/-! An executable ratio-product counting algorithm and its pathwise correctness.
True counts occur only in its analysis, never in the estimator definition. -/
namespace HiddenCircuits.Approximation.SelfReduction

/-- The actual estimator successively divides by empirical branch frequencies. -/
def estimate {S α : Type*} (step : S → α → S) (frequency : S → α → ℚ) :
    (d : ℕ) → S → (Fin d → α) → ℚ
  | 0, _, _ => 1
  | d+1, s, r => estimate step frequency d (step s (r 0)) (fun i => r i.succ) / frequency s (r 0)

/-- Relative factors are an analysis-only expression for the actual output. -/
def relativeFactors {S α : Type*} (step : S → α → S) (frequency : S → α → ℚ)
    (count : S → ℕ) : (d : ℕ) → S → (Fin d → α) → List ℚ
  | 0, _, _ => []
  | d+1, s, r => ((count (step s (r 0)) : ℚ)/count s/frequency s (r 0)) ::
      relativeFactors step frequency count d (step s (r 0)) (fun i => r i.succ)

@[simp] theorem relativeFactors_length {S α : Type*} (step : S → α → S)
    (frequency : S → α → ℚ) (count : S → ℕ) (d : ℕ) (s : S) (r : Fin d → α) :
    (relativeFactors step frequency count d s r).length = d := by
  induction d generalizing s with
  | zero => rfl
  | succ d ih => simp [relativeFactors, ih]

/-- Conditions proved from accurate heavy-branch selection, not assumed
concentration or an assumed FPRAS output guarantee. -/
def stepAccurate {S α : Type*} (step : S → α → S) (frequency : S → α → ℚ)
    (count rank : S → ℕ) (η : ℚ) (s : S) (a : α) : Prop :=
  0 < count (step s a) ∧ 0 < frequency s a ∧ rank (step s a)+1=rank s ∧
    |(count (step s a) : ℚ)/count s/frequency s a-1| ≤ η

/-- Telescoping is proved for the actual adaptively chosen path, including the
one empty matching at depth zero. -/
theorem estimate_factorization {S α : Type*} (step : S → α → S) (frequency : S → α → ℚ)
    (count rank : S → ℕ) (hleaf : ∀ s, rank s=0 → count s ≤ 1) (η : ℚ)
    (d : ℕ) (s : S) (hrank : rank s=d) (hcount : 0 < count s) (r : Fin d → α)
    (hgood : goodRun step (stepAccurate step frequency count rank η) d s r) :
    estimate step frequency d s r / (count s : ℚ) =
      (relativeFactors step frequency count d s r).prod := by
  induction d generalizing s with
  | zero =>
    have hc : count s=1 := by have hh := hleaf s hrank; omega
    simp [estimate, relativeFactors, hc]
  | succ d ih =>
    obtain ⟨hl,ht⟩ := hgood
    obtain ⟨hc,hq,hr,he⟩ := hl
    have hr' : rank (step s (r 0))=d := by omega
    have hc' : (count s : ℚ) ≠ 0 := by exact_mod_cast hcount.ne'
    have hcn : (count (step s (r 0)) : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
    have hq' : frequency s (r 0) ≠ 0 := ne_of_gt hq
    have hi := ih (step s (r 0)) hr' hc (fun i => r i.succ) ht
    simp only [estimate, relativeFactors, List.prod_cons]
    calc
      _ = ((count (step s (r 0)) : ℚ)/count s/frequency s (r 0)) *
          (estimate step frequency d (step s (r 0)) (fun i => r i.succ) /
            (count (step s (r 0)) : ℚ)) := by field_simp <;> ring
      _ = _ := by rw [hi]

theorem relativeFactors_accurate {S α : Type*} (step : S → α → S) (frequency : S → α → ℚ)
    (count rank : S → ℕ) (η : ℚ) (d : ℕ) (s : S) (r : Fin d → α)
    (hgood : goodRun step (stepAccurate step frequency count rank η) d s r) :
    ∀ x ∈ relativeFactors step frequency count d s r, |x-1| ≤ η := by
  induction d generalizing s with
  | zero => simp [relativeFactors]
  | succ d ih =>
    obtain ⟨hl,ht⟩ := hgood
    intro x hx
    simp only [relativeFactors, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hl.2.2.2
    · exact ih _ _ ht _ hx

/-- The actual estimator is relatively accurate whenever all local steps are
accurate; the error budget is linear in deletion depth. -/
theorem estimate_relative_error {S α : Type*} (step : S → α → S) (frequency : S → α → ℚ)
    (count rank : S → ℕ) (hleaf : ∀ s, rank s=0 → count s ≤ 1)
    (η : ℚ) (hη : 0 ≤ η) (hη1 : η ≤ 1) (d : ℕ) (hsmall : (d : ℚ)*η ≤ 1/2)
    (s : S) (hrank : rank s=d) (hcount : 0 < count s) (r : Fin d → α)
    (hgood : goodRun step (stepAccurate step frequency count rank η) d s r) :
    |estimate step frequency d s r - count s| ≤ (2*d*η)*(count s : ℚ) := by
  have hf := estimate_factorization step frequency count rank hleaf η d s hrank hcount r hgood
  have hp := product_relative_error (relativeFactors step frequency count d s r) η hη hη1
    (relativeFactors_accurate step frequency count rank η d s r hgood)
    (by simpa using hsmall)
  rw [relativeFactors_length, ← hf] at hp
  have hc : (0 : ℚ) < count s := by exact_mod_cast hcount
  have he : estimate step frequency d s r-count s =
      (estimate step frequency d s r/(count s : ℚ)-1)*(count s : ℚ) := by field_simp <;> ring
  rw [he, abs_mul, abs_of_pos hc]
  exact mul_le_mul_of_nonneg_right hp hc.le

end HiddenCircuits.Approximation.SelfReduction
