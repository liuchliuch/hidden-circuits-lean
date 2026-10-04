import HiddenCircuits.Circuit.LagrangeIntegerArrays
import HiddenCircuits.Complexity.RecoveryBitBounds

/-! Executable common-denominator accumulation of bounded integer ratios. -/
namespace HiddenCircuits.Circuit.IntegerRatioAccumulator
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def commonDenominator (l : List ι) (d : ι → ℤ) : ℤ := (l.map d).prod

def commonNumerator (l : List ι) (n d : ι → ℤ) : ℤ :=
  (l.map (fun i => n i*((l.filter (fun j => j≠i)).map d).prod)).sum

 theorem list_prod_univ {R : Type*} [CommMonoid R] (l : List ι) (hl : l.Nodup)
    (hall : ∀ i, i∈l) (f : ι → R) : (l.map f).prod=∏ i, f i := by
  rw [← List.prod_toFinset f hl]
  congr 1
  ext i
  simp [hall i]

 theorem list_sum_univ {R : Type*} [AddCommMonoid R] (l : List ι) (hl : l.Nodup)
    (hall : ∀ i, i∈l) (f : ι → R) : (l.map f).sum=∑ i, f i := by
  rw [← List.sum_toFinset f hl]
  congr 1
  ext i
  simp [hall i]

 theorem list_prod_except {R : Type*} [CommMonoid R] (l : List ι) (hl : l.Nodup)
    (hall : ∀ i, i∈l) (f : ι → R) (i : ι) :
    ((l.filter (fun j => j≠i)).map f).prod=∏ j ∈ Finset.univ.erase i, f j := by
  rw [← List.prod_toFinset f (hl.filter _)]
  congr 1
  ext j
  simp [hall j]

 theorem commonDenominator_eq (l : List ι) (hl : l.Nodup) (hall : ∀ i, i∈l) (d : ι → ℤ) :
    commonDenominator l d=∏ i, d i := list_prod_univ l hl hall d

 theorem commonNumerator_eq (l : List ι) (hl : l.Nodup) (hall : ∀ i, i∈l) (n d : ι → ℤ) :
    commonNumerator l n d=∑ i, n i*∏ j ∈ Finset.univ.erase i, d j := by
  unfold commonNumerator
  rw [list_sum_univ l hl hall]
  simp_rw [list_prod_except l hl hall]

 theorem commonDenominator_ne_zero (l : List ι) (d : ι → ℤ) (hd : ∀ i, d i≠0) :
    commonDenominator l d≠0 := by
  unfold commonDenominator
  apply List.prod_ne_zero
  intro hz
  obtain ⟨i,_,hi⟩ := List.mem_map.mp hz
  exact hd i hi

/-- The explicitly accumulated numerator and denominator represent the exact rational sum. -/
theorem ratio_correct (l : List ι) (hl : l.Nodup) (hall : ∀ i, i∈l) (n d : ι → ℤ)
    (hd : ∀ i, d i≠0) :
    (commonNumerator l n d:ℚ)/(commonDenominator l d:ℚ)=∑ i, (n i:ℚ)/(d i:ℚ) := by
  rw [commonNumerator_eq l hl hall,commonDenominator_eq l hl hall]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have hdi (i : ι) : (d i:ℚ)≠0 := by exact_mod_cast hd i
  have he : (∏ j : ι, (d j:ℚ))=(d i:ℚ)*(∏ j ∈ Finset.univ.erase i, (d j:ℚ)) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hp : (∏ j ∈ Finset.univ.erase i, (d j:ℚ))≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hdi j)
  rw [he]
  field_simp [hdi i,hp]

/-- If the desired sum is integral, one actual signed division is exact. -/
theorem exact_division (l : List ι) (hl : l.Nodup) (hall : ∀ i, i∈l) (n d : ι → ℤ)
    (hd : ∀ i, d i≠0) (z : ℤ) (hz : (∑ i, (n i:ℚ)/(d i:ℚ))=(z:ℚ)) :
    commonNumerator l n d/commonDenominator l d=z := by
  have hh := (ratio_correct l hl hall n d hd).trans hz
  have hm := (div_eq_iff (show (commonDenominator l d:ℚ)≠0 by exact_mod_cast commonDenominator_ne_zero l d hd)).mp hh
  have hi : commonNumerator l n d=z*commonDenominator l d := by exact_mod_cast hm
  rw [hi]
  simp [commonDenominator_ne_zero l d hd]

/-- All denominator factors and accumulator terms are covered by an explicit polynomial exponent. -/
theorem accumulator_bits (l : List ι) (hl : l.Nodup) (hall : ∀ i, i∈l) (n d : ι → ℤ)
    (B C : ℕ) (hn : ∀ i, (n i).natAbs ≤ 2^B) (hd : ∀ i, (d i).natAbs ≤ 2^C) :
    (commonDenominator l d).natAbs.size ≤ C*Fintype.card ι+1 ∧
      (commonNumerator l n d).natAbs.size ≤ B+C*Fintype.card ι+Fintype.card ι+1 := by
  have hp := Complexity.int_prod_envelope Finset.univ d C (fun i _ => hd i)
  have hp' (i : ι) : (∏ j ∈ Finset.univ.erase i, d j).natAbs ≤ 2^(C*Fintype.card ι) := by
    apply (Complexity.int_prod_envelope (Finset.univ.erase i) d C (fun j _ => hd j)).trans
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (by simp))
  have hs := Complexity.int_sum_envelope Finset.univ
    (fun i => n i*∏ j ∈ Finset.univ.erase i, d j) (B+C*Fintype.card ι) (fun i _ => by
      simpa only [Int.natAbs_mul,pow_add] using Nat.mul_le_mul (hn i) (hp' i))
  rw [commonDenominator_eq l hl hall,commonNumerator_eq l hl hall]
  constructor
  · have h := Nat.size_le_size hp
    simpa [Nat.size_pow] using h
  · have h := Nat.size_le_size hs
    simpa [Nat.size_pow] using h

end HiddenCircuits.Circuit.IntegerRatioAccumulator
