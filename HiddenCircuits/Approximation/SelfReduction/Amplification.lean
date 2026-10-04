import HiddenCircuits.Approximation.SelfReduction.FiniteMean

/-! Independent confidence amplification. An exponential finite moment bounds
a majority of bad groups; each group's probability is at most one eighth. -/
namespace HiddenCircuits.Approximation.SelfReduction
open scoped BigOperators

 theorem majority_failure_bound {α : Type*} [Fintype α] [Nonempty α]
    (E : α → Prop) [DecidablePred E] (hE : probability E ≤ 1/8) (m : ℕ) :
    probability (fun r : Fin (2*m) → α =>
      m ≤ (Finset.univ.filter (fun i => E (r i))).card) ≤ 1/(2^m : ℚ) := by
  classical
  let W : (Fin (2*m) → α) → ℚ := fun r => ∏ i, if E (r i) then 8 else 1
  have hw (r : Fin (2*m) → α) : W r=(8 : ℚ)^(Finset.univ.filter (fun i => E (r i))).card := by
    simp [W, Finset.prod_ite]
  have he : mean (fun a : α => if E a then (8 : ℚ) else 1) ≤ 2 := by
    have hh : mean (fun a : α => if E a then (8 : ℚ) else 1)=1+7*probability E := by
      calc
        _ = mean (fun a : α => 1+7*(if E a then 1 else 0)) :=
          mean_congr (fun a => by by_cases h : E a <;> norm_num [h])
        _ = _ := by rw [mean_add, mean_const, mean_const_mul, mean_indicator]
    rw [hh]
    linarith
  have hm : mean W ≤ (2 : ℚ)^(2*m) := by
    rw [show mean W=∏ _ : Fin (2*m), mean (fun a : α => if E a then (8 : ℚ) else 1) from
      mean_pi_prod (fun _ : Fin (2*m) => fun a : α => if E a then (8 : ℚ) else 1)]
    calc
      _ ≤ ∏ _ : Fin (2*m), (2 : ℚ) := Finset.prod_le_prod
        (fun i _ => mean_nonneg (fun a => by split_ifs <;> norm_num)) (fun i _ => he)
      _ = _ := by simp
  have hmark := probability_markov W (fun r => by rw [hw]; positivity) ((8 : ℚ)^m) (by positivity)
  calc
    _ ≤ probability (fun r => (8 : ℚ)^m ≤ W r) := by
      apply probability_mono
      intro r hr
      rw [hw]
      exact pow_le_pow_right₀ (by norm_num) hr
    _ ≤ mean W/(8 : ℚ)^m := hmark
    _ ≤ (2 : ℚ)^(2*m)/(8 : ℚ)^m := div_le_div_of_nonneg_right hm (by positivity)
    _ = 1/(2^m : ℚ) := by
      rw [pow_mul, ← div_pow]
      norm_num
      simp [one_div_pow, one_div]

end HiddenCircuits.Approximation.SelfReduction
