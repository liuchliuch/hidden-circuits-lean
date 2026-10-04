import HiddenCircuits.Complexity.InterpolationWeights
import HiddenCircuits.Complexity.CNFQueryEncoding

/-! Division-free accumulation followed by one proved-exact integer division.
This avoids treating arbitrary-precision rational arithmetic as a free operation. -/
namespace HiddenCircuits.Complexity
open scoped BigOperators

def gridDenominator (dx dy : ℕ) : ℤ :=
  (∏ i : Fin (dx+1), interpolationDenominator dx i) *
  (∏ j : Fin (dy+1), interpolationDenominator dy j)

def gridNumerator (dx dy : ℕ) (values : Fin (dx+1) → Fin (dy+1) → ℤ) : ℤ :=
  ∑ i : Fin (dx+1), ∑ j : Fin (dy+1),
    values i j * interpolationNegativeNumerator dy j *
    (∏ k ∈ Finset.univ.erase i, interpolationDenominator dx k) *
    (∏ l ∈ Finset.univ.erase j, interpolationDenominator dy l)

/-- Executable integer-only postprocessing of the oracle values. -/
def recoverIntegerGrid (dx dy : ℕ) (values : Fin (dx+1) → Fin (dy+1) → ℤ) : ℕ :=
  (gridNumerator dx dy values / gridDenominator dx dy).toNat

theorem gridDenominator_ne_zero (dx dy : ℕ) : gridDenominator dx dy ≠ 0 := by
  unfold gridDenominator
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => interpolationDenominator_ne_zero dx i)
  · exact Finset.prod_ne_zero_iff.mpr (fun j _ => interpolationDenominator_ne_zero dy j)

theorem grid_ratio_eq (dx dy : ℕ) (values : Fin (dx+1) → Fin (dy+1) → ℤ) :
    (gridNumerator dx dy values : ℚ) / (gridDenominator dx dy : ℚ) =
      ∑ i : Fin (dx+1), ∑ j : Fin (dy+1),
        (values i j : ℚ) * (interpolationNegativeNumerator dy j : ℚ) /
          ((interpolationDenominator dx i : ℚ) * (interpolationDenominator dy j : ℚ)) := by
  unfold gridNumerator gridDenominator
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have hx : (∏ k : Fin (dx+1), (interpolationDenominator dx k : ℚ)) =
      (interpolationDenominator dx i : ℚ) *
        (∏ k ∈ Finset.univ.erase i, (interpolationDenominator dx k : ℚ)) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hy : (∏ l : Fin (dy+1), (interpolationDenominator dy l : ℚ)) =
      (interpolationDenominator dy j : ℚ) *
        (∏ l ∈ Finset.univ.erase j, (interpolationDenominator dy l : ℚ)) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
  have hnX (k : Fin (dx+1)) : (interpolationDenominator dx k : ℚ) ≠ 0 := by
    exact_mod_cast interpolationDenominator_ne_zero dx k
  have hnY (l : Fin (dy+1)) : (interpolationDenominator dy l : ℚ) ≠ 0 := by
    exact_mod_cast interpolationDenominator_ne_zero dy l
  have hpx : (∏ k ∈ Finset.univ.erase i, (interpolationDenominator dx k : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => hnX k)
  have hpy : (∏ l ∈ Finset.univ.erase j, (interpolationDenominator dy l : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun l _ => hnY l)
  rw [hx,hy]
  field_simp [hnX i,hnY j,hpx,hpy]
  <;> ring

namespace CNF
variable {n m : ℕ} (F : CNF n m)

/-- Explicit bounded-integer coefficients for the graph-oracle interpolation. -/
theorem satCount_integer_weights :
    (F.satCount : ℚ) = ∑ i : Fin (n+1), ∑ j : Fin (m+1),
      (F.cloneCount i.val j.val : ℚ) * (interpolationNegativeNumerator m j : ℚ) /
        ((interpolationDenominator n i : ℚ) * (interpolationDenominator m j : ℚ)) := by
  rw [← F.column_minus_one_coeff,
    top_coefficient_integer_weights n _ (F.columnPolynomial_degree (-1))]
  simp_rw [← F.polynomial_cross,negative_value_integer_weights m _ (F.rowPolynomial_degree _),
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [interpolationNode,F.rowPolynomial_eval_cloneCount,div_div]
  congr 1
  exact mul_comm _ _

/-- The accumulated numerator is exactly the wanted count times the known,
nonzero common denominator. Thus the final division has no rounding or remainder. -/
theorem gridNumerator_exact :
    gridNumerator n m (fun i j => (F.cloneCount i.val j.val : ℤ)) =
      (F.satCount : ℤ) * gridDenominator n m := by
  have h := grid_ratio_eq n m (fun i j => (F.cloneCount i.val j.val : ℤ))
  simp only [Int.cast_natCast] at h
  rw [← F.satCount_integer_weights] at h
  have hd : (gridDenominator n m : ℚ) ≠ 0 := by exact_mod_cast gridDenominator_ne_zero n m
  have he := (div_eq_iff hd).mp h
  exact_mod_cast he

/-- An executable integer-only recovery function returns the exact #SAT count. -/
theorem recoverIntegerGrid_correct :
    recoverIntegerGrid n m (fun i j => (F.cloneCount i.val j.val : ℤ)) = F.satCount := by
  unfold recoverIntegerGrid
  rw [F.gridNumerator_exact]
  simp [gridDenominator_ne_zero]

/-- The same executable recovery consumes the answers to actual encoded graph queries. -/
theorem recoverIntegerGrid_encoded_correct :
    recoverIntegerGrid n m (fun i j =>
      (GraphInput.independentSetProblem (F.encodedCloneQuery i.val j.val) : ℤ)) = F.satCount := by
  simp only [F.encodedCloneQuery_correct]
  exact F.recoverIntegerGrid_correct

end CNF
end HiddenCircuits.Complexity
