import HiddenCircuits.Complexity.IntegerRecovery

/-! Explicit bit bounds for the actual integer interpolation accumulators. -/
namespace HiddenCircuits.Complexity
open scoped BigOperators

lemma int_prod_envelope {ι : Type*} (s : Finset ι) (f : ι → ℤ) (B : ℕ)
    (h : ∀ i ∈ s, (f i).natAbs ≤ 2^B) :
    (∏ i ∈ s, f i).natAbs ≤ 2^(B*s.card) := by
  change Int.natAbsHom (∏ i ∈ s, f i) ≤ _
  rw [map_prod]
  calc
    _ ≤ ∏ _i ∈ s, 2^B := Finset.prod_le_prod' h
    _ = _ := by rw [Finset.prod_const,← pow_mul]

lemma int_sum_envelope {ι : Type*} (s : Finset ι) (f : ι → ℤ) (B : ℕ)
    (h : ∀ i ∈ s, (f i).natAbs ≤ 2^B) :
    (∑ i ∈ s, f i).natAbs ≤ 2^(B+s.card) := by
  calc
    _ ≤ ∑ i ∈ s, (f i).natAbs := Int.natAbs_sum_le s f
    _ ≤ ∑ _i ∈ s, 2^B := Finset.sum_le_sum h
    _ = s.card * 2^B := by simp
    _ ≤ 2^s.card * 2^B := Nat.mul_le_mul_right _
      ((Nat.le_succ s.card).trans (HiddenCircuits.succ_le_two_pow s.card))
    _ = _ := by rw [← pow_add,Nat.add_comm]

lemma interpolationDenominator_envelope (d : ℕ) (i : Fin (d+1)) :
    (interpolationDenominator d i).natAbs ≤ 2^(d^2+1) := by
  exact (Nat.le_of_lt (Nat.lt_size_self _)).trans
    (Nat.pow_le_pow_right (by decide) (interpolation_weights_bit_bound d i).1)

lemma interpolationNegativeNumerator_envelope (d : ℕ) (i : Fin (d+1)) :
    (interpolationNegativeNumerator d i).natAbs ≤ 2^(d^2+1) := by
  exact (Nat.le_of_lt (Nat.lt_size_self _)).trans
    (Nat.pow_le_pow_right (by decide) (interpolation_weights_bit_bound d i).2)

/-- Common-denominator exponent, cubic in the interpolation degrees. -/
def denominatorExponent (dx dy : ℕ) : ℕ :=
  (dx^2+1)*(dx+1)+(dy^2+1)*(dy+1)

theorem gridDenominator_envelope (dx dy : ℕ) :
    (gridDenominator dx dy).natAbs ≤ 2^(denominatorExponent dx dy) := by
  unfold gridDenominator denominatorExponent
  rw [Int.natAbs_mul,pow_add]
  apply Nat.mul_le_mul
  · simpa using int_prod_envelope Finset.univ (interpolationDenominator dx) (dx^2+1)
      (fun i _ => interpolationDenominator_envelope dx i)
  · simpa using int_prod_envelope Finset.univ (interpolationDenominator dy) (dy^2+1)
      (fun j _ => interpolationDenominator_envelope dy j)

lemma denominator_erase_envelope (d : ℕ) (i : Fin (d+1)) :
    (∏ j ∈ Finset.univ.erase i, interpolationDenominator d j).natAbs ≤
      2^((d^2+1)*(d+1)) := by
  have h := int_prod_envelope (Finset.univ.erase i) (interpolationDenominator d) (d^2+1)
    (fun j _ => interpolationDenominator_envelope d j)
  exact h.trans (Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_left _ (by simp)))

/-- Includes the input answer bound, all interpolation weights, and both sums. -/
def numeratorExponent (dx dy B : ℕ) : ℕ :=
  B+(dy^2+1)+denominatorExponent dx dy+(dx+1)*(dy+1)

lemma grid_term_envelope (dx dy B : ℕ)
    (values : Fin (dx+1) → Fin (dy+1) → ℤ)
    (hv : ∀ i j, (values i j).natAbs ≤ 2^B) (i : Fin (dx+1)) (j : Fin (dy+1)) :
    (values i j * interpolationNegativeNumerator dy j *
      (∏ k ∈ Finset.univ.erase i, interpolationDenominator dx k) *
      (∏ l ∈ Finset.univ.erase j, interpolationDenominator dy l)).natAbs ≤
        2^(B+(dy^2+1)+denominatorExponent dx dy) := by
  have h := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.mul_le_mul (hv i j) (interpolationNegativeNumerator_envelope dy j))
      (denominator_erase_envelope dx i)) (denominator_erase_envelope dy j)
  simpa only [Int.natAbs_mul,← pow_add,denominatorExponent,Nat.add_assoc] using h

theorem gridNumerator_envelope (dx dy B : ℕ)
    (values : Fin (dx+1) → Fin (dy+1) → ℤ)
    (hv : ∀ i j, (values i j).natAbs ≤ 2^B) :
    (gridNumerator dx dy values).natAbs ≤ 2^(numeratorExponent dx dy B) := by
  let f : Fin (dx+1) × Fin (dy+1) → ℤ := fun ij =>
    values ij.1 ij.2 * interpolationNegativeNumerator dy ij.2 *
      (∏ k ∈ Finset.univ.erase ij.1, interpolationDenominator dx k) *
      (∏ l ∈ Finset.univ.erase ij.2, interpolationDenominator dy l)
  have h := int_sum_envelope Finset.univ f (B+(dy^2+1)+denominatorExponent dx dy)
    (fun ij _ => grid_term_envelope dx dy B values hv ij.1 ij.2)
  simpa only [gridNumerator,numeratorExponent,Fintype.sum_prod_type,f,Finset.card_univ,
    Fintype.card_prod,Fintype.card_fin] using h

theorem recovery_accumulator_bits (dx dy B : ℕ)
    (values : Fin (dx+1) → Fin (dy+1) → ℤ)
    (hv : ∀ i j, (values i j).natAbs ≤ 2^B) :
    (gridDenominator dx dy).natAbs.size ≤ denominatorExponent dx dy+1 ∧
    (gridNumerator dx dy values).natAbs.size ≤ numeratorExponent dx dy B+1 := by
  constructor
  · have h := Nat.size_le_size (gridDenominator_envelope dx dy)
    simpa [Nat.size_pow] using h
  · have h := Nat.size_le_size (gridNumerator_envelope dx dy B values hv)
    simpa [Nat.size_pow] using h

namespace CNF
variable {n m : ℕ} (F : CNF n m)

theorem cloneCount_grid_envelope (i : Fin (n+1)) (j : Fin (m+1)) :
    F.cloneCount i.val j.val ≤ 2^((2*n+m)^2+1) := by
  have h := F.encodedCloneAnswer_grid_length i j
  rw [encodedCloneQuery_correct,encodeNat_length] at h
  exact (Nat.le_of_lt (Nat.lt_size_self _)).trans (Nat.pow_le_pow_right (by decide) h)

/-- Every actual interpolation accumulator for the source reduction has an
explicit polynomial signed-magnitude bit bound. -/
theorem source_recovery_accumulator_bits :
    (gridDenominator n m).natAbs.size ≤ denominatorExponent n m+1 ∧
    (gridNumerator n m (fun i j => (F.cloneCount i.val j.val : ℤ))).natAbs.size ≤
      numeratorExponent n m ((2*n+m)^2+1)+1 := by
  apply recovery_accumulator_bits
  intro i j
  simpa using F.cloneCount_grid_envelope i j

end CNF
end HiddenCircuits.Complexity
