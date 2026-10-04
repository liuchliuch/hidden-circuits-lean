import HiddenCircuits.Complexity.Interpolation
import HiddenCircuits.BitBounds
import Mathlib.Data.Int.NatAbs

/-! Explicit integer Lagrange weights at consecutive nodes. Their denominators
and the numerators for evaluation at `-1` have proved polynomial bit bounds. -/
namespace HiddenCircuits.Complexity
open scoped BigOperators
open Polynomial

/-- Integer denominator of the i-th Lagrange basis polynomial. -/
def interpolationDenominator (d : ℕ) (i : Fin (d+1)) : ℤ :=
  ∏ j ∈ Finset.univ.erase i, ((i.val : ℤ)-j.val)

/-- Integer numerator when the i-th basis polynomial is evaluated at `-1`. -/
def interpolationNegativeNumerator (d : ℕ) (i : Fin (d+1)) : ℤ :=
  ∏ j ∈ Finset.univ.erase i, ((-1 : ℤ)-j.val)

theorem interpolationDenominator_ne_zero (d : ℕ) (i : Fin (d+1)) :
    interpolationDenominator d i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro h
  have he : i = j := Fin.ext (by exact_mod_cast h)
  exact (Finset.mem_erase.mp hj).1 he.symm

theorem interpolationDenominator_natAbs (d : ℕ) (i : Fin (d+1)) :
    (interpolationDenominator d i).natAbs ≤ d^d := by
  unfold interpolationDenominator
  change Int.natAbsHom (∏ j ∈ Finset.univ.erase i, ((i.val : ℤ)-j.val)) ≤ d^d
  rw [map_prod]
  calc
    _ ≤ ∏ _j ∈ Finset.univ.erase i, d := by
      apply Finset.prod_le_prod'
      intro j _
      change ((i.val : ℤ)-j.val).natAbs ≤ d
      rcases le_total i.val j.val with h | h
      · rw [Int.natAbs_natCast_sub_natCast_of_le h]
        omega
      · rw [Int.natAbs_natCast_sub_natCast_of_ge h]
        omega
    _ = d^d := by simp

theorem interpolationNegativeNumerator_natAbs (d : ℕ) (i : Fin (d+1)) :
    (interpolationNegativeNumerator d i).natAbs ≤ (d+1)^d := by
  unfold interpolationNegativeNumerator
  change Int.natAbsHom (∏ j ∈ Finset.univ.erase i, ((-1 : ℤ)-j.val)) ≤ (d+1)^d
  rw [map_prod]
  calc
    _ ≤ ∏ _j ∈ Finset.univ.erase i, (d+1) := by
      apply Finset.prod_le_prod'
      intro j _
      change ((-1 : ℤ)-j.val).natAbs ≤ d+1
      have he : (-1 : ℤ)-j.val = -((j.val+1 : ℕ) : ℤ) := by push_cast; ring
      rw [he]
      simp only [Int.natAbs_neg,Int.natAbs_natCast]
      omega
    _ = (d+1)^d := by simp

/-- Both denominator and negative-evaluation numerator have at most d²+1 bits. -/
theorem interpolation_weights_bit_bound (d : ℕ) (i : Fin (d+1)) :
    (interpolationDenominator d i).natAbs.size ≤ d^2+1 ∧
    (interpolationNegativeNumerator d i).natAbs.size ≤ d^2+1 := by
  have hp : (d+1)^d ≤ 2^(d^2) := by
    have h := Nat.pow_le_pow_left (HiddenCircuits.succ_le_two_pow d) d
    simpa [← pow_mul,pow_two] using h
  have hd : (interpolationDenominator d i).natAbs ≤ 2^(d^2) :=
    (interpolationDenominator_natAbs d i).trans
      ((Nat.pow_le_pow_left (Nat.le_succ d) d).trans hp)
  have hn := (interpolationNegativeNumerator_natAbs d i).trans hp
  constructor
  · have h := Nat.size_le_size hd
    simpa [Nat.size_pow] using h
  · have h := Nat.size_le_size hn
    simpa [Nat.size_pow] using h

@[simp] theorem interpolationDenominator_cast (d : ℕ) (i : Fin (d+1)) :
    (interpolationDenominator d i : ℚ) =
      ∏ j ∈ Finset.univ.erase i, (interpolationNode i-interpolationNode j) := by
  simp [interpolationDenominator,interpolationNode]

@[simp] theorem interpolationNegativeNumerator_cast (d : ℕ) (i : Fin (d+1)) :
    (interpolationNegativeNumerator d i : ℚ) =
      ∏ j ∈ Finset.univ.erase i, ((-1 : ℚ)-interpolationNode j) := by
  simp [interpolationNegativeNumerator,interpolationNode]

/-- The leading coefficient requires only the integer denominators. -/
theorem top_coefficient_integer_weights (d : ℕ) (p : ℚ[X]) (hp : p.natDegree ≤ d) :
    p.coeff d = ∑ i : Fin (d+1), p.eval (interpolationNode i) /
      (interpolationDenominator d i : ℚ) := by
  have hdeg : p.degree < ((Finset.univ : Finset (Fin (d+1))).card : WithBot ℕ) := by
    simp only [Finset.card_univ,Fintype.card_fin]
    exact lt_of_le_of_lt p.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hp)
  simpa using (Lagrange.coeff_eq_sum (s := Finset.univ)
    (v := @interpolationNode d) (interpolationNode_injective d).injOn hdeg)

/-- The negative-evaluation weights are explicit ratios of bounded integers. -/
theorem basis_negative_integer_weight (d : ℕ) (i : Fin (d+1)) :
    (Lagrange.basis Finset.univ interpolationNode i).eval (-1) =
      (interpolationNegativeNumerator d i : ℚ) / (interpolationDenominator d i : ℚ) := by
  simp only [Lagrange.basis,Lagrange.basisDivisor,eval_prod,eval_mul,eval_C,eval_sub,eval_X,
    Finset.prod_mul_distrib,Finset.prod_inv_distrib,interpolationNegativeNumerator_cast,
    interpolationDenominator_cast,div_eq_mul_inv]
  exact mul_comm _ _

/-- Evaluation at `-1` from d+1 nonnegative integer oracle nodes. -/
theorem negative_value_integer_weights (d : ℕ) (p : ℚ[X]) (hp : p.natDegree ≤ d) :
    p.eval (-1) = ∑ i : Fin (d+1), p.eval (interpolationNode i) *
      (interpolationNegativeNumerator d i : ℚ) / (interpolationDenominator d i : ℚ) := by
  conv_lhs => rw [← interpolateValues_correct d p hp]
  simp only [interpolateValues,Lagrange.interpolate_apply,eval_finset_sum,eval_mul,eval_C,
    basis_negative_integer_weight,div_eq_mul_inv,mul_assoc]

end HiddenCircuits.Complexity
