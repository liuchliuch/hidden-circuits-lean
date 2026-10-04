import HiddenCircuits.Complexity.RecoveryBitBounds

/-! Exact shared-denominator grid weights in the order used by the real
arithmetic program: multiply two node denominators, divide the common product,
then multiply the negative-evaluation numerator and oracle answer. -/
namespace HiddenCircuits.Complexity
open scoped BigOperators

def gridDivisor (dx dy : ℕ) (i : Fin (dx+1)) (j : Fin (dy+1)) : ℤ :=
  interpolationDenominator dx i * interpolationDenominator dy j

def gridCofactor (dx dy : ℕ) (i : Fin (dx+1)) (j : Fin (dy+1)) : ℤ :=
  (∏ k ∈ Finset.univ.erase i, interpolationDenominator dx k) *
  (∏ l ∈ Finset.univ.erase j, interpolationDenominator dy l)

lemma gridDivisor_ne_zero (dx dy : ℕ) (i : Fin (dx+1)) (j : Fin (dy+1)) :
    gridDivisor dx dy i j ≠ 0 :=
  mul_ne_zero (interpolationDenominator_ne_zero dx i) (interpolationDenominator_ne_zero dy j)

lemma gridDenominator_factor (dx dy : ℕ) (i : Fin (dx+1)) (j : Fin (dy+1)) :
    gridDenominator dx dy = gridCofactor dx dy i j * gridDivisor dx dy i j := by
  have hx : (∏ k : Fin (dx+1), interpolationDenominator dx k) =
      interpolationDenominator dx i * (∏ k ∈ Finset.univ.erase i, interpolationDenominator dx k) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hy : (∏ k : Fin (dy+1), interpolationDenominator dy k) =
      interpolationDenominator dy j * (∏ k ∈ Finset.univ.erase j, interpolationDenominator dy k) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
  unfold gridDenominator gridCofactor gridDivisor
  rw [hx,hy]
  ring

lemma gridDivisor_dvd (dx dy : ℕ) (i : Fin (dx+1)) (j : Fin (dy+1)) :
    gridDivisor dx dy i j ∣ gridDenominator dx dy :=
  ⟨gridCofactor dx dy i j,by rw [gridDenominator_factor];ring⟩

lemma gridDenominator_div (dx dy : ℕ) (i : Fin (dx+1)) (j : Fin (dy+1)) :
    gridDenominator dx dy / gridDivisor dx dy i j = gridCofactor dx dy i j := by
  rw [gridDenominator_factor dx dy i j]
  exact Int.mul_ediv_cancel _ (gridDivisor_ne_zero dx dy i j)

def gridTerm (dx dy : ℕ) (i : Fin (dx+1)) (j : Fin (dy+1)) (value : ℤ) : ℤ :=
  (gridDenominator dx dy / gridDivisor dx dy i j) * interpolationNegativeNumerator dy j * value

lemma gridTerm_eq (dx dy : ℕ) (i : Fin (dx+1)) (j : Fin (dy+1)) (value : ℤ) :
    gridTerm dx dy i j value = value * interpolationNegativeNumerator dy j *
      (∏ k ∈ Finset.univ.erase i, interpolationDenominator dx k) *
      (∏ l ∈ Finset.univ.erase j, interpolationDenominator dy l) := by
  rw [gridTerm,gridDenominator_div,gridCofactor]
  ring

lemma gridNumerator_eq_sum_gridTerm (dx dy : ℕ) (values : Fin (dx+1) → Fin (dy+1) → ℤ) :
    gridNumerator dx dy values = ∑ i, ∑ j, gridTerm dx dy i j (values i j) := by
  simp only [gridTerm_eq,gridNumerator]

lemma gridCofactor_envelope (dx dy : ℕ) (i : Fin (dx+1)) (j : Fin (dy+1)) :
    (gridCofactor dx dy i j).natAbs ≤ 2^(denominatorExponent dx dy) := by
  simpa only [gridCofactor,Int.natAbs_mul,←pow_add,denominatorExponent] using
    Nat.mul_le_mul (denominator_erase_envelope dx i) (denominator_erase_envelope dy j)

lemma gridTerm_envelope (dx dy B : ℕ) (i : Fin (dx+1)) (j : Fin (dy+1)) (value : ℤ)
    (hv : value.natAbs≤2^B) :
    (gridTerm dx dy i j value).natAbs ≤ 2^(B+(dy^2+1)+denominatorExponent dx dy) := by
  rw [gridTerm_eq]
  exact grid_term_envelope dx dy B (fun _ _ => value) (fun _ _ => hv) i j

end HiddenCircuits.Complexity
