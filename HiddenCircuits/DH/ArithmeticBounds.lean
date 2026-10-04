import HiddenCircuits.DH.ColumnBounds

/-! Bounds on the actual integer expressions evaluated inside the array scans. -/
namespace HiddenCircuits.DH
open Polynomial
open scoped BigOperators

/-- A uniform envelope for state products, falling factors, finite sums and recurrence transients. -/
def arithmeticEnvelope (n : ℕ) : ℕ := 2*(n+1)^(3*n+3)

lemma arithmeticEnvelope_binary (n : ℕ) :
    arithmeticEnvelope n ≤ 2^(1+(3*n+3)*(n+1).size) := by
  unfold arithmeticEnvelope
  calc
    2*(n+1)^(3*n+3) ≤ 2*(2^((n+1).size))^(3*n+3) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_size_self (n+1))) _)
    _ = _ := by rw [← pow_mul,pow_add]; simp only [pow_one]; congr 2; ring

lemma arithmeticEnvelope_bits (n : ℕ) {z : ℤ} (hz : z.natAbs ≤ arithmeticEnvelope n) :
    z.natAbs.size ≤ (3*n+3)*(n+1).size+2 := by
  have h := Nat.size_le_size (hz.trans (arithmeticEnvelope_binary n))
  rw [Nat.size_pow] at h
  omega

/-- All four primitive recurrence expressions are bounded, including the temporary sum
before subtraction. Bounds are attached to the expressions in `ArrayColumn.entry`. -/
theorem entry_intermediate_bounds (n j k : ℕ) (previous current : Array ℤ) (B : ℤ)
    (hB : 0 ≤ B) (hj : j ≤ n) (hk : k ≤ n)
    (hp : ∀ l, |ArrayColumn.read previous l| ≤ B)
    (hc : ∀ l, |ArrayColumn.read current l| ≤ B) :
    |(k+1 : ℤ)*ArrayColumn.read current (k+1)| ≤ (n+1)*B ∧
    |(j : ℤ)*ArrayColumn.read previous k| ≤ n*B ∧
    |(if k=0 then 0 else ArrayColumn.read current (k-1)) +
      (k+1 : ℤ)*ArrayColumn.read current (k+1)| ≤ (n+2)*B ∧
    |(ArrayColumn.entry j previous current k).value| ≤ (2*n+2)*B := by
  have hj' : (j : ℤ) ≤ n := by exact_mod_cast hj
  have hk' : (k : ℤ) ≤ n := by exact_mod_cast hk
  have hd : |(k+1 : ℤ)*ArrayColumn.read current (k+1)| ≤ (n+1)*B := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (k+1 : ℤ))]
    exact (mul_le_mul_of_nonneg_left (hc (k+1)) (by positivity)).trans
      (mul_le_mul_of_nonneg_right (by omega) hB)
  have hs : |(j : ℤ)*ArrayColumn.read previous k| ≤ n*B := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (j : ℤ))]
    exact (mul_le_mul_of_nonneg_left (hp k) (by positivity)).trans
      (mul_le_mul_of_nonneg_right hj' hB)
  have hx : |(if k=0 then 0 else ArrayColumn.read current (k-1))| ≤ B := by
    split_ifs
    · simpa using hB
    · exact hc _
  have hadd : |(if k=0 then 0 else ArrayColumn.read current (k-1)) +
      (k+1 : ℤ)*ArrayColumn.read current (k+1)| ≤ (n+2)*B := by
    exact (abs_add_le _ _).trans (by nlinarith)
  refine ⟨hd,hs,hadd,?_⟩
  change |((if k=0 then 0 else ArrayColumn.read current (k-1)) +
      (k+1 : ℤ)*ArrayColumn.read current (k+1)) -
      (j : ℤ)*ArrayColumn.read previous k| ≤ _
  exact (abs_sub _ _).trans (by nlinarith)

variable {V : Type*} {G : SimpleGraph V} {T : Set V}

/-- Every retained coefficient in the real recurrence loop inherits the matching bound. -/
theorem run_columns_abs_bound [Fintype V] (b j n : ℕ) (input : Array ℤ)
    (hinput : ArrayColumn.Represents input (bagPolynomial G T))
    (hj : j ≤ b) (hn : Fintype.card V+b ≤ n) (k : ℕ) :
    |ArrayColumn.read (ArrayColumn.run (Fintype.card V+b+1) input j).value.1 k| ≤ ((n+1)^n : ℕ) ∧
    |ArrayColumn.read (ArrayColumn.run (Fintype.card V+b+1) input j).value.2 k| ≤ ((n+1)^n : ℕ) := by
  obtain ⟨hp,hc⟩ := ArrayColumn.run_represents (Fintype.card V) b input
    (bagPolynomial G T) hinput bagPolynomial_natDegree_le j hj
  constructor
  · rw [hp k]
    cases j with
    | zero => simp only [ArrayColumn.previousColumn,coeff_zero,abs_zero]; positivity
    | succ j =>
      change |(matchingColumn (bagPolynomial G T) j).coeff k| ≤ _
      obtain ⟨h0,hb⟩ := matchingColumn_bag_coeff_bound (G := G) (T := T) j k n (by omega)
      rwa [abs_of_nonneg h0]
  · rw [hc k]
    obtain ⟨h0,hb⟩ := matchingColumn_bag_coeff_bound (G := G) (T := T) j k n (by omega)
    rwa [abs_of_nonneg h0]

/-- The generic transient estimate applies to every actual scanned recurrence entry. -/
theorem run_entry_transient_bound [Fintype V] (b j n k : ℕ) (input : Array ℤ)
    (hinput : ArrayColumn.Represents input (bagPolynomial G T))
    (hj : j ≤ b) (hn : Fintype.card V+b ≤ n) (hk : k ≤ n) :
    |(ArrayColumn.entry j
      (ArrayColumn.run (Fintype.card V+b+1) input j).value.1
      (ArrayColumn.run (Fintype.card V+b+1) input j).value.2 k).value| ≤
        (2*n+2)*((n+1)^n : ℕ) := by
  apply (entry_intermediate_bounds n j k _ _ ((n+1)^n : ℕ)
    (by positivity) (by omega) hk
    (fun l => (run_columns_abs_bound b j n input hinput hj hn l).1)
    (fun l => (run_columns_abs_bound b j n input hinput hj hn l).2)).2.2.2

lemma recurrenceEnvelope_le_arithmetic (n : ℕ) :
    (2*n+2)*(n+1)^n ≤ arithmeticEnvelope n := by
  unfold arithmeticEnvelope
  calc
    (2*n+2)*(n+1)^n = 2*(n+1)^(n+1) := by rw [pow_succ]; ring
    _ ≤ 2*(n+1)^(3*n+3) := Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by omega) (by omega))

/-- Every actual recurrence scan result has O(n log n) magnitude bits. -/
theorem run_entry_bits [Fintype V] (b j n k : ℕ) (input : Array ℤ)
    (hinput : ArrayColumn.Represents input (bagPolynomial G T))
    (hj : j ≤ b) (hn : Fintype.card V+b ≤ n) (hk : k ≤ n) :
    ((ArrayColumn.entry j
      (ArrayColumn.run (Fintype.card V+b+1) input j).value.1
      (ArrayColumn.run (Fintype.card V+b+1) input j).value.2 k).value).natAbs.size ≤
        (3*n+3)*(n+1).size+2 := by
  apply arithmeticEnvelope_bits n
  apply le_trans _ (recurrenceEnvelope_le_arithmetic n)
  have h := run_entry_transient_bound b j n k input hinput hj hn hk
  rw [← Int.natCast_natAbs] at h
  exact_mod_cast h

variable {W : Type*} {H : SimpleGraph W} {U : Set W}

/-- Each accumulator prefix is a nonnegative sum of at most n+1 products of matching counts. -/
theorem weightedSum_bag_coeff_bound [Fintype V] [Fintype W] (j k n : ℕ)
    (hj : j ≤ Fintype.card W) (hn : Fintype.card V+Fintype.card W ≤ n) :
    0 ≤ (ArrayColumn.weightedSum (bagPolynomial G T) (bagPolynomial H U) j).coeff k ∧
    (ArrayColumn.weightedSum (bagPolynomial G T) (bagPolynomial H U) j).coeff k ≤
      ((n+1)*((n+1)^n)^2 : ℕ) := by
  classical
  simp only [ArrayColumn.weightedSum,finset_sum_coeff,coeff_C_mul,bagPolynomial_coeff]
  have hg (l : ℕ) :
      0 ≤ (Fintype.card (BagState H U l) : ℤ) ∧
        (Fintype.card (BagState H U l) : ℤ) ≤ ((n+1)^n : ℕ) := by
    constructor
    · positivity
    · exact_mod_cast (bagState_card_bound_of_card_le (G := H) (T := U) n l (by omega))
  have hterm (l : ℕ) (hl : l ∈ Finset.range (j+1)) :
      0 ≤ (Fintype.card (BagState H U l) : ℤ) *
        (matchingColumn (bagPolynomial G T) l).coeff k ∧
      (Fintype.card (BagState H U l) : ℤ) *
        (matchingColumn (bagPolynomial G T) l).coeff k ≤ (((n+1)^n)^2 : ℕ) := by
    have hlj := Finset.mem_range.mp hl
    obtain ⟨hq0,hqb⟩ := matchingColumn_bag_coeff_bound (G := G) (T := T) l k n (by omega)
    constructor
    · exact mul_nonneg (hg l).1 hq0
    · have hm := mul_le_mul (hg l).2 hqb hq0 (by positivity : (0 : ℤ) ≤ ((n+1)^n : ℕ))
      simpa only [Nat.cast_pow,pow_two] using hm
  constructor
  · exact Finset.sum_nonneg (fun l hl => (hterm l hl).1)
  · calc
      _ ≤ ∑ _l ∈ Finset.range (j+1), ((((n+1)^n)^2 : ℕ) : ℤ) :=
        Finset.sum_le_sum (fun l hl => (hterm l hl).2)
      _ = (j+1)*((((n+1)^n)^2 : ℕ) : ℤ) := by simp
      _ ≤ _ := by
        have hjn : (j+1 : ℤ) ≤ n+1 := by exact_mod_cast (show j+1 ≤ n+1 by omega)
        exact_mod_cast (mul_le_mul_of_nonneg_right hjn
          (by positivity : (0 : ℤ) ≤ (((n+1)^n)^2 : ℕ)))

lemma accumulationEnvelope_le_arithmetic (n : ℕ) :
    (n+1)*((n+1)^n)^2 ≤ arithmeticEnvelope n := by
  unfold arithmeticEnvelope
  calc
    (n+1)*((n+1)^n)^2 = (n+1)^(2*n+1) := by rw [← pow_mul,pow_succ,Nat.mul_comm n 2]; ring
    _ ≤ (n+1)^(3*n+3) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ 2*(n+1)^(3*n+3) := by omega

/-- Materialized accumulator prefixes, rather than just the final answer, obey the bit bound. -/
theorem runWeighted_total_bits [Fintype V] [Fintype W] (j k n : ℕ)
    (input weights : Array ℤ)
    (hinput : ArrayColumn.Represents input (bagPolynomial G T))
    (hweights : ArrayColumn.Represents weights (bagPolynomial H U))
    (hj : j ≤ Fintype.card W) (hn : Fintype.card V+Fintype.card W ≤ n) :
    (ArrayColumn.read (ArrayColumn.runWeighted
      (Fintype.card V+Fintype.card W+1) input weights j).value.total k).natAbs.size ≤
        (3*n+3)*(n+1).size+2 := by
  have hr := ArrayColumn.runWeighted_represents (Fintype.card V) (Fintype.card W)
    input weights (bagPolynomial G T) (bagPolynomial H U)
    hinput hweights bagPolynomial_natDegree_le j hj
  rw [hr k]
  obtain ⟨h0,hb⟩ := weightedSum_bag_coeff_bound (G := G) (H := H) (T := T) (U := U) j k n hj hn
  apply arithmeticEnvelope_bits n
  apply le_trans _ (accumulationEnvelope_le_arithmetic n)
  have he := hb
  rw [← abs_of_nonneg h0,← Int.natCast_natAbs] at he
  exact_mod_cast he

end HiddenCircuits.DH
