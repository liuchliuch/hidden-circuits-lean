import HiddenCircuits.Approximation.FiniteChains.Basic

/-! Elementary quadratic estimates for a finite lazy reversible chain. -/
namespace HiddenCircuits.Approximation.FiniteChains
open scoped BigOperators
variable {α : Type*} [Fintype α]

/-- Weighted Cauchy–Schwarz, with no square roots or measure theory. -/
theorem weighted_sum_sq_le (w g : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x, w x * g x)^2 ≤ (∑ x, w x) * ∑ x, w x * (g x)^2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro i _; exact hw i
  · intro i _; exact mul_nonneg (hw i) (sq_nonneg _)
  · intro i _; ring

namespace LazyChain
variable (P : LazyChain α)

/-- The squared norm of the one-step displacement uses only off-diagonal
transitions. Laziness bounds their total mass by one half. -/
theorem displacement_sq_le (f : α → ℝ) (x : α) :
    (P.act f x - f x)^2 ≤ (1:ℝ)/2 * ∑ y, P.weight x y * (f x-f y)^2 := by
  classical
  let w : α → ℝ := fun y => if y=x then 0 else P.weight x y
  have hw : ∀ y, 0 ≤ w y := by
    intro y; dsimp [w]; split_ifs
    · exact le_rfl
    · exact P.nonneg x y
  have hws : ∑ y, w y = 1-P.weight x x := by
    calc
      _ = ∑ y, (P.weight x y - if y=x then P.weight x x else 0) := by
        apply Finset.sum_congr rfl
        intro y _; by_cases h : y=x <;> simp [w,h]
      _ = _ := by rw [Finset.sum_sub_distrib]; simp [P.row_sum]
  have hsum : ∑ y, w y * (f y-f x) = P.act f x-f x := by
    calc
      _ = ∑ y, P.weight x y * (f y-f x) := by
        apply Finset.sum_congr rfl
        intro y _; by_cases h : y=x <;> simp [w,h]
      _ = _ := by simp_rw [mul_sub]; rw [Finset.sum_sub_distrib,← Finset.sum_mul,
        P.row_sum,one_mul]; rfl
  have henergy : ∑ y, w y * (f y-f x)^2 =
      ∑ y, P.weight x y * (f x-f y)^2 := by
    apply Finset.sum_congr rfl
    intro y _
    by_cases h : y=x
    · simp [w,h]
    · simp only [w,if_neg h]; ring
  have h := weighted_sum_sq_le w (fun y => f y-f x) hw
  rw [hsum,henergy,hws] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · linarith [P.lazy x]
  · exact Finset.sum_nonneg fun y _ => mul_nonneg (P.nonneg x y) (sq_nonneg _)

/-- Symmetry converts the two squared endpoint terms into the same norm. -/
theorem energy_identity (f : α → ℝ) :
    P.energy f = 2 * P.sqNorm f - 2 * ∑ x, f x * P.act f x := by
  unfold energy sqNorm act
  have hrow : ∀ x, (∑ y, P.weight x y * f x^2) = f x^2 := by
    intro x; rw [← Finset.sum_mul,P.row_sum,one_mul]
  have hcol : (∑ x, ∑ y, P.weight x y * f y^2) = ∑ y, f y^2 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,P.column_sum,one_mul]
  calc
    _ = (∑ x, ∑ y, P.weight x y * f x^2) +
        (∑ x, ∑ y, P.weight x y * f y^2) -
        2 * ∑ x, f x * ∑ y, P.weight x y * f y := by
      simp_rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _; ring
    _ = _ := by simp_rw [hrow,hcol]; ring

/-- A genuine one-step energy decay, proved directly from lazy transitions. -/
theorem sqNorm_act_le (f : α → ℝ) :
    P.sqNorm (P.act f) ≤ P.sqNorm f - P.energy f / 2 := by
  have hd := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset α)) =>
    P.displacement_sq_le f x)
  have hid : (∑ x, (P.act f x-f x)^2) =
      P.sqNorm (P.act f) + P.sqNorm f - 2 * ∑ x, f x * P.act f x := by
    unfold sqNorm
    simp_rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _; ring
  rw [hid,← Finset.mul_sum] at hd
  change P.sqNorm (P.act f) + P.sqNorm f - 2 * ∑ x, f x * P.act f x ≤
    (1:ℝ)/2 * P.energy f at hd
  have he := P.energy_identity f
  linarith

/-- Pairwise differences exactly recover the centered quadratic norm. -/
theorem pair_difference_identity (f : α → ℝ) (hf : ∑ x, f x = 0) :
    (∑ x, ∑ y, (f x-f y)^2) = 2 * Fintype.card α * P.sqNorm f := by
  unfold sqNorm
  have hx : ∀ x, (∑ y, (f x-f y)^2) =
      Fintype.card α * f x^2 + ∑ y, f y^2 := by
    intro x
    calc
      _ = (∑ _y : α, f x^2) + (∑ y, f y^2) - 2*f x*∑ y, f y := by
        simp_rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro y _; ring
      _ = _ := by simp [hf]
  simp_rw [hx,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  ring

end LazyChain
end HiddenCircuits.Approximation.FiniteChains
