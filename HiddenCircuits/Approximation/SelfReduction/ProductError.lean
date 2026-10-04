import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

/-! Finite rational product
bounds, with no asymptotic or analytic approximation premise. -/
namespace HiddenCircuits.Approximation.SelfReduction

private theorem product_envelope (xs : List ℚ) (η : ℚ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hx : ∀ x ∈ xs, |x-1| ≤ η) (hsmall : (xs.length : ℚ)*η ≤ 1/2) :
    1-(xs.length : ℚ)*η ≤ xs.prod ∧ xs.prod ≤ 1+2*(xs.length : ℚ)*η := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hl : (0 : ℚ) ≤ xs.length := Nat.cast_nonneg _
    have hst : (xs.length : ℚ)*η ≤ 1/2 := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hsmall
      nlinarith
    have ht := ih (fun y hy => hx y (List.mem_cons_of_mem _ hy)) hst
    have he := abs_le.mp (hx x (List.mem_cons_self))
    have hp0 : 0 ≤ xs.prod := by linarith
    have hx0 : 0 ≤ x := by linarith
    have hlow := mul_le_mul (show 1-η ≤ x by linarith) ht.1 (by linarith : 0 ≤ 1-(xs.length : ℚ)*η) hx0
    have hupp := mul_le_mul (show x ≤ 1+η by linarith) ht.2 hp0 (by linarith : 0 ≤ 1+η)
    have hnn : 0 ≤ (xs.length : ℚ)*η*η := by positivity
    have hcap : 2*(xs.length : ℚ)*η*η ≤ η := by nlinarith [mul_nonneg hη (by linarith : 0 ≤ 1-2*(xs.length : ℚ)*η)]
    simp only [List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith

theorem product_relative_error (xs : List ℚ) (η : ℚ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hx : ∀ x ∈ xs, |x-1| ≤ η) (hsmall : (xs.length : ℚ)*η ≤ 1/2) :
    |xs.prod-1| ≤ 2*(xs.length : ℚ)*η := by
  have h := product_envelope xs η hη hη1 hx hsmall
  rw [abs_le]
  have hn : 0 ≤ (xs.length : ℚ)*η := by positivity
  constructor <;> linarith

end HiddenCircuits.Approximation.SelfReduction
