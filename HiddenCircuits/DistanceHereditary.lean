import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! Integer-polynomial normal-ordered matching columns.
The connection to bag matching counts and the full graph algorithm is separate. -/
namespace HiddenCircuits.DH
open Polynomial
open scoped BigOperators

/-- Normal ordering: multiplication by X acts on the output, differentiation on the input. -/
noncomputable def matchingColumn (F : ℤ[X]) : ℕ → ℤ[X]
  | 0 => F
  | n+1 => X * matchingColumn F n + matchingColumn (derivative F) n

@[simp] theorem matchingColumn_zero (F : ℤ[X]) : matchingColumn F 0 = F := rfl
@[simp] theorem matchingColumn_one (F : ℤ[X]) : matchingColumn F 1 = X*F + derivative F := rfl

/-- Differentiating a normal-ordered column creates the exact lower-column correction. -/
theorem derivative_matchingColumn_succ (F : ℤ[X]) (n : ℕ) :
    derivative (matchingColumn F (n+1)) =
      matchingColumn (derivative F) (n+1) + (n+1 : ℤ[X]) * matchingColumn F n := by
  induction n generalizing F with
  | zero => simp [matchingColumn, derivative_mul]; ring
  | succ n ih =>
    change derivative (X * matchingColumn F (n+1) + matchingColumn (derivative F) (n+1)) = _
    rw [derivative_add, derivative_mul, derivative_X, one_mul, ih F, ih (derivative F)]
    change _ = X * matchingColumn (derivative F) (n+1) +
      matchingColumn (derivative (derivative F)) (n+1) +
      ((n+1 : ℕ)+1 : ℤ[X]) * matchingColumn F (n+1)
    rw [show matchingColumn F (n+1) = X*matchingColumn F n + matchingColumn (derivative F) n from rfl]
    push_cast
    ring

/-- Division-free three-term recurrence over actual integer polynomials. -/
theorem matchingColumn_recurrence (F : ℤ[X]) (n : ℕ) :
    matchingColumn F (n+2) = X * matchingColumn F (n+1) +
      derivative (matchingColumn F (n+1)) - (n+1 : ℤ[X]) * matchingColumn F n := by
  rw [derivative_matchingColumn_succ]
  change X * matchingColumn F (n+1) + matchingColumn (derivative F) (n+1) = _
  ring

/-- Exact finite-sum identification with the paper's Q_j; no recurrence is assumed. -/
theorem matchingColumn_eq_sum (F : ℤ[X]) (n : ℕ) :
    matchingColumn F n = ∑ r ∈ Finset.range (n+1),
      (n.choose r : ℤ[X]) * (X^(n-r) * derivative^[r] F) := by
  induction n generalizing F with
  | zero => simp [matchingColumn]
  | succ n ih =>
    rw [matchingColumn, ih F, ih (derivative F)]
    rw [Finset.sum_choose_succ_mul (fun r j => (X : ℤ[X])^j * derivative^[r] F) n]
    rw [Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro r hr
      have hrn : r ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
      have he : n+1-r = (n-r)+1 := by omega
      rw [he, pow_succ]
      ring

/-- The recurrence never needs coefficients beyond the combined bag-size bound. -/
theorem matchingColumn_natDegree_le (F : ℤ[X]) (n : ℕ) :
    (matchingColumn F n).natDegree ≤ F.natDegree + n := by
  induction n generalizing F with
  | zero => simp
  | succ n ih =>
    change (X * matchingColumn F n + matchingColumn (derivative F) n).natDegree ≤ _
    apply (natDegree_add_le _ _).trans
    apply max_le
    · have hm : (X * matchingColumn F n).natDegree ≤ (X : ℤ[X]).natDegree + (matchingColumn F n).natDegree := natDegree_mul_le
      have hx := natDegree_X_le (R := ℤ)
      have hf := ih F
      omega
    · have hd := natDegree_derivative_le F
      have hf := ih (derivative F)
      omega

end HiddenCircuits.DH
