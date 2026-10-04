import HiddenCircuits.DH.JoinCounts
import HiddenCircuits.DistanceHereditary
import HiddenCircuits.DH.ArrayColumn
import HiddenCircuits.DH.Transport

/-! Identification of the integer-polynomial recurrence with the concrete crossing counts. -/
namespace HiddenCircuits.DH
open Polynomial
open scoped BigOperators

lemma iterate_derivative_monomial_formula (a : ℤ) (i r : ℕ) :
    derivative^[r] (monomial i a) = monomial (i-r) (a*(i.descFactorial r : ℤ)) := by
  rw [← C_mul_X_pow_eq_monomial,iterate_derivative_C_mul,iterate_derivative_X_pow_eq_C_mul,
    ← mul_assoc,← C_mul,C_mul_X_pow_eq_monomial]

/-- One column on a monomial counts the same endpoint choices as a complete cross block. -/
lemma matchingColumn_monomial (a : ℤ) (i j : ℕ) :
    matchingColumn (monomial i a) j =
      ∑ r ∈ Finset.range (j+1), monomial (i+j-2*r)
        (a*((i.choose r * j.choose r * r.factorial : ℕ) : ℤ)) := by
  rw [matchingColumn_eq_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrj : r ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  rw [iterate_derivative_monomial_formula,X_pow_mul_monomial]
  change C (j.choose r : ℤ) * monomial (i-r+(j-r)) (a*(i.descFactorial r : ℤ)) = _
  rw [C_mul_monomial]
  by_cases hri : r ≤ i
  · have he : i-r+(j-r) = i+j-2*r := by omega
    rw [he,Nat.descFactorial_eq_factorial_mul_choose]
    congr 1
    push_cast
    ring
  · have hir : i < r := by omega
    simp [Nat.descFactorial_of_lt hir,Nat.choose_eq_zero_of_lt hir]

lemma matchingColumn_monomial_coeff (a : ℤ) (i j k : ℕ) :
    (matchingColumn (monomial i a) j).coeff k =
      ∑ r ∈ Finset.range (j+1), if i+j = k+2*r then
        a*((i.choose r * j.choose r * r.factorial : ℕ) : ℤ) else 0 := by
  rw [matchingColumn_monomial]
  simp only [finset_sum_coeff,coeff_monomial]
  apply Finset.sum_congr rfl
  intro r hr
  have hrj : r ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  by_cases hri : r ≤ i
  · have he : i+j-2*r = k ↔ i+j = k+2*r := by omega
    simp only [he]
  · have hir : i < r := by omega
    simp [Nat.choose_eq_zero_of_lt hir]

lemma matchingColumn_sum {I : Type*} (s : Finset I) (f : I → ℤ[X]) (j : ℕ) :
    matchingColumn (∑ i ∈ s, f i) j = ∑ i ∈ s, matchingColumn (f i) j := by
  induction j generalizing f with
  | zero => rfl
  | succ j ih =>
    simp only [matchingColumn,derivative_sum,ih,Finset.mul_sum,Finset.sum_add_distrib]

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
variable {T : Set V} {U : Set W}

/-- Coefficients are cardinalities of actual graph boundary states. -/
noncomputable def bagPolynomial [Fintype V] (G : SimpleGraph V) (T : Set V) : ℤ[X] :=
  ∑ i ∈ Finset.range (Fintype.card V+1), monomial i (Fintype.card (BagState G T i) : ℤ)

@[simp] lemma bagPolynomial_coeff [Fintype V] (k : ℕ) :
    (bagPolynomial G T).coeff k = (Fintype.card (BagState G T k) : ℤ) := by
  classical
  simp only [bagPolynomial,finset_sum_coeff,coeff_monomial]
  by_cases hk : k < Fintype.card V+1
  · simp [Finset.mem_range,hk]
  · have hz := bagState_card_eq_zero_of_lt (G := G) T (show Fintype.card V < k by omega)
    simp [Finset.mem_range,hk,hz]

lemma bagPolynomial_natDegree_le [Fintype V] :
    (bagPolynomial G T).natDegree ≤ Fintype.card V := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [bagPolynomial_coeff,bagState_card_eq_zero_of_lt T hk,Nat.cast_zero]

/-- Finite integer formula for Q_j's actual boundary-state coefficients. -/
lemma matchingColumn_bag_coeff [Fintype V] (j k : ℕ) :
    (matchingColumn (bagPolynomial G T) j).coeff k =
      ∑ i ∈ Finset.range (Fintype.card V+1), ∑ r ∈ Finset.range (j+1),
        if i+j = k+2*r then
          ((Fintype.card (BagState G T i) * (i.choose r * j.choose r * r.factorial) : ℕ) : ℤ)
        else 0 := by
  rw [bagPolynomial,matchingColumn_sum]
  simp only [finset_sum_coeff,matchingColumn_monomial_coeff,Nat.cast_mul]

/-- The division-free integer operation is exactly the true-twin graph-state polynomial. -/
theorem trueTwinProduct_bag [Fintype V] [Fintype W] :
    ArrayColumn.trueTwinProduct (bagPolynomial G T) (bagPolynomial H U) =
      bagPolynomial (joinGraph G H T U) {x | Sum.elim T U x} := by
  classical
  ext k
  rw [ArrayColumn.trueTwinProduct_eq_weightedSum _ _ (Fintype.card W) bagPolynomial_natDegree_le]
  simp only [ArrayColumn.weightedSum,finset_sum_coeff,coeff_C_mul,bagPolynomial_coeff,
    matchingColumn_bag_coeff]
  rw [trueTwin_count_rightRange]
  simp only [Nat.cast_sum,← Fin.sum_univ_eq_sum_range,Nat.cast_ite,Nat.cast_zero,Nat.cast_mul]
  simp_rw [Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs <;> ring

/-- The implemented true-twin coefficient loop computes the genuine merged graph states. -/
theorem runWeighted_bag [Fintype V] [Fintype W] (input weights : Array ℤ)
    (hp : ArrayColumn.Represents input (bagPolynomial G T))
    (hq : ArrayColumn.Represents weights (bagPolynomial H U)) :
    ArrayColumn.polynomial
      (ArrayColumn.runWeighted (Fintype.card V+Fintype.card W+1)
        input weights (Fintype.card W)).value.total =
      bagPolynomial (joinGraph G H T U) {x | Sum.elim T U x} := by
  rw [ArrayColumn.runWeighted_product _ _ _ _ _ _ hp hq
    bagPolynomial_natDegree_le bagPolynomial_natDegree_le]
  exact trueTwinProduct_bag

/-- Exchanging true-twin operands is a graph isomorphism; it does not exchange pendant roles. -/
def joinSwapIso : joinGraph G H T U ≃g joinGraph H G U T where
  toEquiv := Equiv.sumComm V W
  map_rel_iff' := by
    rintro (v | w) (v' | w') <;> simp [joinGraph,and_comm]

lemma joinSwapIso_active :
    joinSwapIso (G := G) (H := H) (T := T) (U := U) '' {x | Sum.elim T U x} =
      {x | Sum.elim U T x} := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    cases y <;> exact hy
  · intro hx
    refine ⟨Sum.swap x,?_,?_⟩
    · cases x <;> exact hx
    · cases x <;> rfl

/-- Valid bag polynomials can safely be oriented with the smaller true-twin bag second. -/
theorem trueTwinProduct_bag_comm [Fintype V] [Fintype W] :
    ArrayColumn.trueTwinProduct (bagPolynomial G T) (bagPolynomial H U) =
      ArrayColumn.trueTwinProduct (bagPolynomial H U) (bagPolynomial G T) := by
  rw [trueTwinProduct_bag,trueTwinProduct_bag]
  ext k
  simp only [bagPolynomial_coeff]
  congr 1
  have h := transport_bag_count (joinSwapIso (G := G) (H := H) (T := T) (U := U))
    {x | Sum.elim T U x} k
  rw [joinSwapIso_active] at h
  exact h

end HiddenCircuits.DH
